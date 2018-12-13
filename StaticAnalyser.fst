(*
This module implements the core functions (leveraging AbstractDomain & GaloisConnection module's definitions) of a tiny WIP static analyser
@summary: Toy static analyser's core
*)
module StaticAnalyser

open FStar.GSet
module CS = CSet
open FStar.Tactics.Typeclasses

open GaloisConnection
open ToyLanguageDef
open EnumerableMap
open AbstractDomain
open ZeroOrLess

module Parser = ToyParser

type mem a = enumerableMap a 

class hasToList a b = {
  toList: a -> list b 
}
instance constHasToList #a: hasToList a a = { toList = fun v -> [v] }

//type isAbstractDomain = (x:Type {exists (d: hasAbstractDomain x). True})
//open Interval
// need to express type with behaviour, i.e. existentials types
//instance tup2HasToList #a: hasToList (a, b) a = { toList = fun v -> [v] }


let rec findInTupList #a key (l:list (string * a)): a = admitP (~ (l == [])); match l with
  | (s,h)::t -> if key = s then h else findInTupList key t  

(* Compute the (abstract) result of an expression *)
let rec static_analysis_aexp #a [| hasGaloisConnection int a |] [| hasAbstractOperators a |]
                    (st:enumerableMap a)
                    (exp:   lAExp      )
                    //(progs: list (string * list lAExp -> enumerableMap a -> list funDef -> a))
                    : a
  = let rec h (exp:lAExp): a = admitP (~(LAExpCall? exp));
         match exp with
       | LAExpLitt  n       -> alpha' n
       | LAExpVar   varName -> em_get st varName
       | LAExpPlus  a b     -> (h a) `a_op_plus` (h b)
       | LAExpMinus a b     -> (h a) `a_op_minus` (h b)
       | LAExpMult  a b     -> (h a) `a_op_times` (h b)
       | LAExpDiv   a b     -> (h a) `a_op_div` (h b)
       //| LAExpCall  v a     -> (let x = findInTupList v )
    in h exp

(* Given an aim and an expression, the following function constraints 
   the variable abstract values present in the expression, using generically
   defined backward operators (see AbstractDomain module) *)
let rec backward_analysis_aexp #a [| hasGaloisConnection int a |] [| hasAbstractOperators a |]
                                  [| hasAbstractDomain a |] [| hasZeroOrLess a |]
                    (st:enumerableMap a)
                    (exp:lAExp)
                    (aim:a)
                    : Tot (enumerableMap a) (decreases exp)
= let f exp = static_analysis_aexp st exp in
  let op2 bop (e1 e2: (x: lAExp{x << exp})) =
                  (let (aim1, aim2):(tuple2 a a) = bop (f e1) (f e2) aim in (* e1 + e2 should fit in aim *)
                   let st' = backward_analysis_aexp st e1 aim1 in
                   backward_analysis_aexp st' e2 aim2)
  in admitP (~(LAExpCall? exp)); match exp with
  | LAExpLitt n       -> st (* a constant cannot be refined *)
  | LAExpVar  varName -> em_set st varName aim (* TODO: why do I set the value directly? should do some inter or smth *)
  | LAExpPlus  e1 e2  -> op2 backward_aop_plus  e1 e2
  | LAExpMinus e1 e2  -> op2 backward_aop_minus e1 e2
  | LAExpMult  e1 e2  -> op2 backward_aop_mul   e1 e2
  | LAExpDiv   e1 e2  -> op2 backward_aop_div   e1 e2
//  | LAExpMult a b    ->  st (*todo*)//(h a) `a_op_times` (h b)

open PartialOrder

let all_bottom #a [| hasAbstractDomain a |] (st: enumerableMap a) = {_em_data = (fun _ -> bottom); _em_keys = st._em_keys}

let is_bottom #a [| hasPartialOrder a |] [| hasAbstractDomain a |] (st: enumerableMap a) =
    List.Tot.Base.existsb (fun k -> isBottom (em_get st k)) st._em_keys

let spread_bottom #a [| hasPartialOrder a |] [| hasAbstractDomain a |] (st: enumerableMap a) =
    if is_bottom st
    then all_bottom st
    else st
    
(* Given an boolean expression `bexp` and a state, `analyse_bexp` returns a state satisfying `bexp` *)
let rec analyse_bexp #a [| hasAbstractOperators a |] [| hasAbstractDomain a |] [| hasGaloisConnection int a |] [| hasZeroOrLess a |]
                     (st:enumerableMap a)
                     (exp:lBExp): Tot (enumerableMap a)
                                  (* either the number of non-terminal `not` is decreasing, either
                                     the size of exp (i.e. the deepness of the AST) is decreasing *)
                                  (decreases %[bexp_count_not exp; exp])
  =
  spread_bottom #a #a_po (match exp with
  | LBExpLitt b -> if b then st (* supposing true doesn't bring anything new *)
                       else all_bottom st (* variables should all be bottom *)
  (* if `not` is terminal (i.e. `! (3 <= 45)`) *)
  | LBExpNot (LBExpEq a b) -> backward_analysis_aexp st (a -. b) (alpha' 0)
  (* otherwise, we apply demorgan and `a <= b ==> b <= a && !(a==b)` *)
  | LBExpNot  b -> let rec apply_not (e:lBExp): (r:lBExp{bexp_count_not e >= bexp_count_not r}) = (match e with
                          | LBExpNot e1    -> e1
                          | LBExpAnd e1 e2 -> LBExpOr  (apply_not e1) (apply_not e2)
                          | LBExpOr  e1 e2 -> LBExpAnd (apply_not e1) (apply_not e2)
                          | LBExpLe  e1 e2 -> ((e2 +. (v 1)) <=. e1) // for now we discard this &&. (!. (e1 ==. e2))
                          | LBExpEq  e1 e2 -> LBExpNot e
                          | LBExpLitt   _  -> e
                          ) in 
                            let nexp = apply_not b in
                               analyse_bexp st nexp
                     (* `em_combine` takes two states and apply a function for 
                        each pairs of values that share a same key *)
  | LBExpAnd  a b -> em_combine (analyse_bexp st a) (analyse_bexp st b) inter
  | LBExpOr   a b -> em_combine (analyse_bexp st a) (analyse_bexp st b) union
  | LBExpEq   a b -> backward_analysis_aexp st (a -. b) (alpha' 0)//lessThanZero
  | LBExpLe   a b -> backward_analysis_aexp st (a -. b) zeroOrLess
  )


open MyIO
open ToString

let prt str = mi_debug_print_string str

//let _ = assert (Prims.Tot = Tot)

(* This functions perform static analysis on instructions, i.e. on full programs *)
let rec static_analysis_instr #a [| hasToString a |] [| hasAbstractOperators a |] [| hasAbstractDomain a |] [| hasGaloisConnection int a |] [| hasZeroOrLess a |]
                    (st:enumerableMap a)
                    (instr: lInstr)
                    : Tot (enumerableMap a) (decreases instr)
  = let f = static_analysis_instr in
    let cs (x:enumerableMap a) = emHasToString.toString x in
    let printCond st c = prt ("\n Cond '" ^ toString c ^ "' gives: \n" ^ cs (analyse_bexp st c)) in
    match instr with
  | LInstrAssign name v -> em_set st name (static_analysis_aexp st v)
  | LInstrSkip          -> st
  | LInstrSeq b1 b2     -> static_analysis_instr (f st b1) b2 
  | LInstrIf c b1 b2    -> let r1 = f (analyse_bexp st     c ) b1 in
                          let r2 = f (analyse_bexp st (!. c)) b2 in
                          let _ = prt ("\n [IF] Previous state is\n" ^ cs st) in
                          let _ = printCond st c in
                          let _ = printCond st (!. c) in
                          em_combine r1 r2 union
  | LInstrWhile cond body -> let apply_cond st = analyse_bexp st cond in 
                          let _ = prt ("\n [WHILE] Previous state is\n" ^ cs st) in
                          //let _ = printCond st c in
                          (* apply_cond takes a state: at each iterations, inveriants 
                             might change, so we need to recompute the condition *)
                          (* TODO: remove that stop parameter *)
                          let rec unroll (n:nat) st = if n = 0 then st else
                            (let st = unroll (n-1) st in 
                             let ifexp = iF cond Then body Else LInstrSkip End in
                              admitP (ifexp << instr);
                              static_analysis_instr st ifexp
                            )
                          in
                          let rec findFixPoint state1
                                               (f: enumerableMap a -> enumerableMap a)
                                               (stop: option nat)
                                               : (enumerableMap a) =
                              let state2 = f state1 in
                              if em_equal aeq state1 state2 || stop = Some 0
                              then state2
                              else (admitP (%[state2] << %[state1]);
                                    findFixPoint state2 f (match stop with | Some n -> Some (n - 1) | x -> x)) in
                          
                          (*
                          let rec lookForFixPoint current_st (stop: nat): Tot (enumerableMap a) = if stop=0 then current_st else
                              let _ = prt ("\n [WHILE:LookForFixPoint] state is\n" ^ cs current_st) in
                              let _ = printCond st cond in
                              let new_st  = static_analysis_instr (apply_cond current_st) body in (* compute while's body once *)
                              let widened = em_combine new_st (apply_cond (em_combine current_st new_st widen)) union in (* widen the new state *)
                                if   em_equal aeq current_st widened then widened (* we reached a fixpoint, we're done *)
                                else lookForFixPoint (admitP (%[widened] << %[current_st]); widened) (stop - 1) in (* TODO: prove some lemma saying widening is ensures termination *)
                          (* we combine the fixpoint state with the old state constrained with the negated condition *)
                          *)
                          let st = unroll 0 st in
                          let _ = printCond st (!. cond) in
                          let unify z = em_combine z (analyse_bexp st (!. cond)) union in
                          let st' = findFixPoint st (fun x ->
                              let x' = static_analysis_instr (apply_cond x) body in
                              em_combine x' (apply_cond (em_combine x x' widen)) union
                            ) None in
                          //st'
                          let st'' = findFixPoint st'
                                       (fun x -> let y = static_analysis_instr (apply_cond x) body in
                                              if is_bottom #a #ab_dom_po y then x else y
                                       )
                                       (Some 20) in
                          let _ =  prt ("\n [HEY] st'\n" ^ cs st') in
                          let _ =  prt ("\n [HEY] st''\n" ^ cs st'') in
                          let _ =  prt ("\n [HEY] (st'' inter st')\n" ^ cs (em_combine st'' st' inter)) in
                          //let _ =  prt ("\n [XX] (st'' inter st')\n" ^ cs (em_combine st'' st' inter)) in
                          unify (em_combine st'' st' inter)
                          //em_combine (analyse_bexp st (!. cond)) (lookForFixPoint st 4) union



