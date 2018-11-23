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

(* Compute the (abstract) result of an expression *)
let rec static_analysis_aexp #a [| hasGaloisConnection int a |] [| hasAbstractOperators a |]
                    (st:enumerableMap a)
                    (exp:lAExp)
                    : a
  = let rec h (exp:lAExp): a = 
         match exp with
       | LAExpLitt  n       -> alpha' n
       | LAExpVar   varName -> em_get st varName
       | LAExpPlus  a b     -> (h a) `a_op_plus` (h b)
       | LAExpMinus a b     -> (h a) `a_op_minus` (h b)
       | LAExpMult  a b     ->  (h a) `a_op_times` (h b)
    in h exp

(* Given an aim and an expression, the following function constraints 
   the variable abstract values present in the expression, using generically
   defined backward operators (see AbstractDomain module) *)
let rec backward_analysis_aexp #a [| hasGaloisConnection int a |] [| hasAbstractOperators a |]
                                  [| hasAbstractDomain a |]
                    (st:enumerableMap a)
                    (exp:lAExp)
                    (aim:a)
                    : Tot (enumerableMap a) (decreases exp)
= let f exp = static_analysis_aexp st exp in
  match exp with
  | LAExpLitt n       -> st (* a constant cannot be refined *)
  | LAExpVar  varName -> em_set st varName aim (* TODO: why do I set the value directly? should do some inter or smth *)
  | LAExpPlus e1 e2   -> let (aim1, aim2):(tuple2 a a) = backward_aop_plus (f e1) (f e2) aim in (* e1 + e2 should fit in aim *)
                        let st' = backward_analysis_aexp st e1 aim1 in
                        backward_analysis_aexp st' e2 aim2
  | LAExpMinus e1 e2  -> let (aim1, aim2):(tuple2 a a) = backward_aop_minus (f e1) (f e2) aim in (* e1 - e1 should fit in aim *)
                        let st' = backward_analysis_aexp st e1 aim1 in
                        backward_analysis_aexp st' e2 aim2
  | LAExpMult a b    ->  st (*todo*)//(h a) `a_op_times` (h b)

(* Given an boolean expression `bexp` and a state, `analyse_bexp` returns a state satisfying `bexp` *)
let rec analyse_bexp #a [| hasAbstractOperators a |] [| hasAbstractDomain a |] [| hasGaloisConnection int a |] [| hasZeroOrLess a |]
                     (st:enumerableMap a)
                     (exp:lBExp): Tot (enumerableMap a)
                                  (* either the number of non-terminal `not` is decreasing, either
                                     the size of exp (i.e. the deepness of the AST) is decreasing *)
                                  (decreases %[bexp_count_not exp; exp])
  = match exp with
  | LBExpLitt b -> if b then st (* supposing true doesn't bring anything new *)
                       else {_em_data = (fun _ -> bottom); _em_keys = st._em_keys} (* variables should all be bottom *)
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


open MyIO
open ToString

(* This functions perform static analysis on instructions, i.e. on full programs *)
let rec static_analysis_instr #a [| hasToString a |] [| hasAbstractOperators a |] [| hasAbstractDomain a |] [| hasGaloisConnection int a |] [| hasZeroOrLess a |]
                    (st:enumerableMap a)
                    (instr:lInstr)
                    : Tot (enumerableMap a) (decreases instr)
  = let f = static_analysis_instr in
    match instr with
  | LInstrAssign name v -> em_set st name (static_analysis_aexp st v)
  | LInstrSkip          -> st
  | LInstrSeq b1 b2     -> static_analysis_instr (f st b1) b2 
  | LInstrIf c b1 b2    -> let r1 = f (analyse_bexp st     c ) b1 in
                          let r2 = f (analyse_bexp st (!. c)) b2 in
                          let _ = mi_debug_print_string ("\n Previous state is\n" ^ emHasToString.toString st) in
                          let _ = mi_debug_print_string ("\n Cond '" ^ toString c ^ "' gives: \n" ^ emHasToString.toString (analyse_bexp st c)) in
                          let _ = mi_debug_print_string ("\n Cond '" ^ toString (!. c) ^ "' gives: \n" ^ emHasToString.toString (analyse_bexp st (!. c))) in
                          em_combine r1 r2 union
  | LInstrWhile cond b1 -> let apply_cond st = analyse_bexp st cond in 
                          (* apply_cond takes a state: at each iterations, inveriants 
                             might change, so we need to recompute the condition *)
                          (* TODO: remove that stop parameter *)
                          

                          let rec lookForFixPoint current_st (stop: nat): Tot (enumerableMap a) = if stop=0 then current_st else
                              let new_st  = static_analysis_instr (apply_cond current_st) b1 in (* compute while's body once *)
                              let widened = em_combine new_st (apply_cond (em_combine current_st new_st widen)) union in (* widen the new state *)
                                if   em_equal aeq current_st widened then widened (* we reached a fixpoint, we're done *)
                                else lookForFixPoint (admitP (%[widened] << %[current_st]); widened) (stop - 1) in (* TODO: prove some lemma saying widening is ensures termination *)
                          (* we combine the fixpoint state with the old state constrained with the negated condition *)
                          em_combine (analyse_bexp st (!. cond)) (lookForFixPoint st 4) union


