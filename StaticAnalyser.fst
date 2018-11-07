module StaticAnalyser

open FStar.GSet
module CS = CSet
open FStar.Tactics
open FStar.Tactics.Typeclasses

open PartialOrder
open GaloisConnection
open DefaultValue
open ToyLanguageDef
open EnumerableMap
open AbstractDomain
open ZeroOrLess

let rec static_analysis_aexp #a [| hasGaloisConnection int a |] [| hasAbstractOperators a |]
                    (st:enumerableMap a)
                    (exp:lAExp)
                    : a
  = let rec h (exp:lAExp): a = 
         match exp with
       | LAExpLitt n       -> alpha' n
       | LAExpVar  varName -> em_get st varName
       | LAExpPlus a b     -> (h a) `a_op_plus` (h b)
       | LAExpMinus a b    -> (h a) `a_op_minus` (h b)
       | LAExpMult a b    ->  (h a) `a_op_times` (h b)
    in h exp

let rec backward_analysis_aexp #a [| hasGaloisConnection int a |] [| hasAbstractOperators a |]
                                  [| hasAbstractDomain a |]
                    (st:enumerableMap a)
                    (exp:lAExp)
                    (aim:a)
                    : Tot (enumerableMap a) (decreases exp)
= let f exp = static_analysis_aexp st exp in
  match exp with
  | LAExpLitt n       -> st //(alpha' n) `inter` aim
  | LAExpVar  varName -> em_set st varName aim//(st varName) ``
  | LAExpPlus e1 e2   -> let (aim1, aim2):(tuple2 a a) = backward_aop_plus (f e1) (f e2) aim in (* e1 + e1 should fit in aim *)
                        let st' = backward_analysis_aexp st e1 aim1 in
                        backward_analysis_aexp st' e2 aim2
  | LAExpMinus e1 e2  -> let (aim1, aim2):(tuple2 a a) = backward_aop_minus (f e1) (f e2) aim in (* e1 + e1 should fit in aim *)
                        let st' = backward_analysis_aexp st e1 aim1 in
                        backward_analysis_aexp st' e2 aim2
  | LAExpMult a b    ->  st (*todo*)//(h a) `a_op_times` (h b)

let rec analyse_bexp #a [| hasAbstractOperators a |] [| hasAbstractDomain a |] [| hasGaloisConnection int a |] [| hasZeroOrLess a |]
                     (st:enumerableMap a)
                     (exp:lBExp): Tot (enumerableMap a)
                                  (decreases %[bexp_count_not exp; exp])
  = match exp with
  | LBExpLitt b -> if b then st (* supposing true doesn't bring anything new *)
                       else {_em_data = (fun _ -> bottom); _em_keys = st._em_keys} (* variables should all be bottom *)
  | LBExpNot (LBExpEq a b) -> backward_analysis_aexp st (a -. b) (alpha' 0)
  | LBExpNot  b -> let rec apply_not (e:lBExp): (r:lBExp{bexp_count_not e >= bexp_count_not r}) = (match e with
                          | LBExpNot e1    -> e1
                          | LBExpAnd e1 e2 -> LBExpOr  (apply_not e1) (apply_not e2)
                          | LBExpOr  e1 e2 -> LBExpAnd (apply_not e1) (apply_not e2)
                          | LBExpLe  e1 e2 -> (e2 <=. e1) &&. (!. (e1 ==. e2))
                          | LBExpEq  e1 e2 -> LBExpNot e
                          | LBExpLitt   _  -> e
                          ) in 
                            let nexp = apply_not b in
                               analyse_bexp st nexp
  | LBExpAnd  a b -> em_combine (analyse_bexp st a) (analyse_bexp st b) inter
  | LBExpOr   a b -> em_combine (analyse_bexp st a) (analyse_bexp st b) union
  | LBExpEq   a b -> backward_analysis_aexp st (a -. b) (alpha' 0)//lessThanZero
  | LBExpLe   a b -> backward_analysis_aexp st (a -. b) zeroOrLess

let rec static_analysis_instr #a [| hasAbstractOperators a |] [| hasAbstractDomain a |] [| hasGaloisConnection int a |] [| hasZeroOrLess a |]
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
                          em_combine r1 r2 union
  | LInstrWhile cond b1 -> let apply_cond st = analyse_bexp st cond in
                          let rec lookForFixPoint current_st (stop: nat): Tot (enumerableMap a) = if stop=0 then current_st else
                              let new_st  = static_analysis_instr (apply_cond current_st) b1 in
                              let widened = em_combine new_st (apply_cond (em_combine current_st new_st widen)) union in 
                                if   em_equal aeq current_st widened then widened
                                else lookForFixPoint (admitP (%[widened] << %[current_st]); widened) (stop - 1) in
                          em_combine (analyse_bexp st (!. cond)) (lookForFixPoint st 4) union