(*
This module implements the core functions (leveraging AbstractDomain & GaloisConnection module's definitions) of a tiny WIP static analyser
@summary: Toy static analyser's core
*)
module StaticAnalyser

open FStar.GSet
module CS = Data.Set.Computable.NonOrdered
open FStar.Tactics.Typeclasses

open GaloisConnection
open ToyLanguageDef
open Data.Map.Enumerable.NonOrdered
open AbstractDomain
open ZeroOrLess
open PartialOrder

module Parser = ToyParser
module L = FStar.List.Tot

type mem a = enumerableMap a 

class hasToList a b = {
  toList: a -> list b 
}
instance constHasToList #a: hasToList a a = { toList = fun v -> [v] }

let rec findInTupList #a key (l:list (string * a)): a = admitP (~ (l == [])); match l with
  | (s,h)::t -> if key = s then h else findInTupList key t  

(* Compute the (abstract) result of an expression *)
let rec static_analysis_aexp #a [| hasGaloisConnection int a |] [| hasAbstractOperators a |]
                    (st:enumerableMap a)
                    (exp:   lAExp      )
                    //(progs: list (string * list lAExp -> enumerableMap a -> list funDef -> a))
                    : a
  = let rec h (exp:lAExp): a =
         match exp with
       | LAExpLitt  n       -> alpha' n
       | LAExpVar   varName -> em_get st varName
       | LAExpPlus  a b     -> (h a) `a_op_plus` (h b)
       | LAExpMinus a b     -> (h a) `a_op_minus` (h b)
       | LAExpMult  a b     -> (h a) `a_op_times` (h b)
       | LAExpDiv   a b     -> (h a) `a_op_div` (h b)
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
  in match exp with
  | LAExpLitt n       -> st (* a constant cannot be refined *)
  | LAExpVar  varName -> em_set st varName aim (* TODO: why do I set the value directly? should do some inter or smth *)
  | LAExpPlus  e1 e2  -> op2 backward_aop_plus  e1 e2
  | LAExpMinus e1 e2  -> op2 backward_aop_minus e1 e2
  | LAExpMult  e1 e2  -> op2 backward_aop_mul   e1 e2
  | LAExpDiv   e1 e2  -> op2 backward_aop_div   e1 e2


let all_bottom #a [| hasAbstractDomain a |] (st: enumerableMap a)
  : enumerableMap a
  = {_em_data = (fun _ -> bottom); _em_keys = st._em_keys}

let is_bottom #a [| hasAbstractDomain a |] (st: enumerableMap a) =
    List.Tot.Base.existsb (fun k -> isBottom (em_get st k)) st._em_keys

let spread_bottom #a [| hasAbstractDomain a |] (st: enumerableMap a) =
    if is_bottom st
    then all_bottom st
    else st

let lemma_bexp_count_not_or a b
  : Lemma (bexp_count_not (LBExpOr a b) == bexp_count_not a + bexp_count_not b) = ()

(* Given an boolean expression `bexp` and a state, `analyse_bexp` returns a state satisfying `bexp` *)
let rec analyse_bexp #a [| hasAbstractOperators a |] [| hasAbstractDomain a |] [| hasGaloisConnection int a |] [| hasZeroOrLess a |]
                     (st:enumerableMap a)
                     (exp:lBExp): Tot (enumerableMap a)
                                  (* either the number of non-terminal `not` is decreasing, either
                                     the size of exp (i.e. the deepness of the AST) is decreasing *)
                                  (decreases %[bexp_count_not exp; exp])
  =
  spread_bottom #a (match exp with
  | LBExpLitt b -> if b then st (* supposing true doesn't bring anything new *)
                       else all_bottom st (* variables should all be bottom *)
  (* if `not` is terminal (i.e. `! (3 <= 45)`) *)
  | LBExpNot (LBExpEq a b) -> backward_analysis_aexp st (a -. b) (alpha' 0)
  (* otherwise, we apply demorgan and `a <= b ==> b <= a && !(a==b)` *)
  | LBExpNot  b -> analyse_bexp st (apply_de_morgan b)
                     (* `em_combine` takes two states and apply a function for 
                        each pairs of values that share a same key *)
  | LBExpAnd  a b -> admit(); em_combine (analyse_bexp st a) (analyse_bexp st b) inter
  | LBExpOr   a b -> admit(); em_combine (analyse_bexp st a) (analyse_bexp st b) union
  | LBExpEq   a b -> backward_analysis_aexp st (a -. b) (alpha' 0)//lessThanZero
  | LBExpLe   a b -> backward_analysis_aexp st (a -. b) zeroOrLess
  | _ -> st
  )

open ToString
open MyIO

let prt str = mi_debug_print_string str

// let fail #a (reason:string): a = let x = MyIO.mi_fail ("ERROR: "^reason) in magic ()

let lookupFun funDefs funName = 
  let rec h funs = (match funs with
      | [] -> None
      | (FunDef fn args instr)::t -> if funName = fn then Some (args, instr) else h t
  ) in h funDefs

let rec check_calls funDefs body: option string  =
    let bind v f = (match v with | None -> f () | _ -> v) in
    match body with
    | LInstrAssign _ (AssignCall fname args) -> (
      let x = "In assignment \"" ^ toString body ^ "\": the function " ^ toString fname in
      match lookupFun funDefs fname with
      | Some (args_name, _) -> 
                              if L.length args_name = L.length args then
                                 None
                              else Some (x ^ " was given " ^ toString (L.length args) ^ " arguments, instead of " ^ toString (L.length args_name))
      | None -> Some (x ^ " was not found")
    )          
    | LInstrSeq a b -> _ <-- check_calls funDefs a; check_calls funDefs b
    | LInstrWhile _ a -> check_calls funDefs a
    | LInstrIf _ a b -> _ <-- check_calls funDefs a; check_calls funDefs b
    | _ -> None

let rec function_call_safe funDefs instr: option string = 
  let bind v f = (match v with | None -> f () | _ -> v) in
  _ <-- check_calls funDefs instr;
  L.fold_left (fun x (FunDef _ _ b) -> _ <-- x; check_calls funDefs b) None funDefs

let ( @$ ) f x = f x

let rec lst_contains (#a:eqtype) (x:a) (l: list a) = match l with
  | [] -> false
  | h::t -> if h = x then true else lst_contains x t 

// private
// let assign_variable (LInstrAssign name v) = 

let rec zip #a #b (l1: list a) (l2: list b): list (a * b) =
    match l1,l2 with
    | [], [] -> []
    | hd1::tl1, hd2::tl2 -> (hd1,hd2)::(zip tl1 tl2)
    | _, _ -> []

(* This functions perform static analysis on instructions, i.e. on full programs *)
let rec static_analysis_instr #a [| hasToString a |] [| hasAbstractOperators a |] [| hasAbstractDomain a |] [| hasGaloisConnection int a |] [| hasZeroOrLess a |]
                    (funs: list funDef)
                    (st:enumerableMap a)
                    (instr: lInstr {None? (function_call_safe funs instr)})
                    : Tot (enumerableMap a) (decreases instr)
  = let f = admit(); static_analysis_instr funs in
    let cs (x:enumerableMap a) = emHasToString.toString x in
    let printCond st c = prt ("\n Cond '" ^ toString c ^ "' gives: \n" ^ cs (analyse_bexp st c)) in
    match (assert (None? (check_calls funs instr)); instr) with
  | LInstrAssign name v -> (
     (match v with
       | AssignLAExp v -> em_set st name @$ static_analysis_aexp st v
       | AssignCall funName args ->
           let Some (args_name, fun_body) = lookupFun funs funName in
           let l = zip args_name args in
           let toExec: lInstr = (L.fold_left LInstrSeq LInstrSkip (
                       ( L.map (fun (name, value) -> name =. (AssignLAExp value)) l
                     @ [ fun_body ])
                )) in
           let st' = (
             admitP (None? (function_call_safe funs fun_body));
             admitP (%[toExec] << %[instr]);
             let _ = prt (toString toExec) in
             static_analysis_instr funs st (admit();toExec)
           ) in
           { _em_data = (fun var -> if lst_contains var args_name
                                 then st._em_data var
                                 else st'._em_data var)
           ; _em_keys = st'._em_keys}
       )
   )
  | LInstrSkip          -> st
  | LInstrSeq b1 b2     -> f
        (f st (admitP (None? (function_call_safe funs b1));
               admitP (b1 << instr);
               admit (); b1))
              b2
  | LInstrIf c b1 b2    -> let r1 = admit(); f (admit(); analyse_bexp st     c ) b1 in
                          let r2 = admit(); f (admit(); analyse_bexp st (!. c)) b2 in
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
                              f st ifexp
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
                          let st = unroll 0 st in
                          let _ = printCond st (!. cond) in
                          let unify z = em_combine z (analyse_bexp st (!. cond)) union in
                          let invariant: enumerableMap a = findFixPoint st (fun x ->
                              let x' = f (apply_cond x) body in
                              em_combine x' (apply_cond (em_combine x x' widen)) union
                            ) None in
                          let shouldNarrow = false in
                          let invariant = (match shouldNarrow with
                              | true -> findFixPoint invariant
                                       (fun x -> let y = f (apply_cond x) body in
                                              if is_bottom #a y then x else y
                                       ) (Some 3)
                              | false -> invariant) in
                          //              (Some 20) in
                          //let _ =  prt ("\n [WHILE] st = \n" ^ cs st) in
                          //let _ =  prt ("\n [WHILE] inv = \n" ^ cs inv) in
                          //let _ =  prt ("\n [WHILE] analyse_bexp inv (!. cond) = \n" ^ cs (analyse_bexp inv (!. cond))) in
                          // let _ =  prt ("\n [WHILE] st''\n" ^ cs st'') in
                          // let _ =  prt ("\n [WHILE] (st'' inter st')\n" ^ cs (em_combine st'' st' inter)) in
                          //let _ =  prt ("\n [XX] (st'' inter st')\n" ^ cs (em_combine st'' st' inter)) in
                          //em_combine (analyse_bexp st (!. cond)) (lookForFixPoint st 4) union
                          let after = analyse_bexp invariant (!. cond) in // after loop, filter
                          unify after
                          
let static_analysis_fullProg #a [| hasToString a |] [| hasAbstractOperators a |] [| hasAbstractDomain a |] [| hasGaloisConnection int a |] [| hasZeroOrLess a |]
                             state (FullProg funs prog) = 
                               match function_call_safe funs prog with
                               | None -> Inl (static_analysis_instr #a funs state prog)
                               | Some x -> Inr x 

