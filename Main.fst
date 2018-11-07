module Main

open FStar.FunctionalExtensionality
open FStar.GSet
module CS = CSet
open Interval
open FStar.Tactics.Typeclasses
open ExtInt

module OS = FStar.OrdSet

type lAExp =
  | LAExpLitt : int -> lAExp
  | LAExpVar  : string -> lAExp
  | LAExpPlus : lAExp -> lAExp -> lAExp 
  | LAExpMinus: lAExp -> lAExp -> lAExp 
  | LAExpMult : lAExp -> lAExp -> lAExp

let ( +. ) = LAExpPlus
let ( -. ) = LAExpMinus
let ( *. ) = LAExpMult

type lBExp =
  | LBExpLitt: bool -> lBExp
  | LBExpNot : lBExp -> lBExp
  | LBExpAnd : lBExp -> lBExp -> lBExp
  | LBExpOr  : lBExp -> lBExp -> lBExp
  | LBExpEq  : lAExp -> lAExp -> lBExp
  | LBExpLe  : lAExp -> lAExp -> lBExp

let ( !.  ) = LBExpNot
let ( &&. ) = LBExpAnd
let ( ||. ) = LBExpOr
let ( ==. ) = LBExpEq
let ( <=. ) = LBExpLe

class litteral_lift a b = {
  v : a -> b
}
instance _ : litteral_lift int    lAExp = { v = LAExpLitt }
instance _ : litteral_lift bool lBExp = { v = LBExpLitt }

let ( !! ) = LAExpVar
 
type lInstr =
  | LInstrAssign : string -> lAExp -> lInstr
  | LInstrSkip   : lInstr
  | LInstrSeq    : lInstr -> lInstr -> lInstr
  | LInstrIf     : lBExp -> lInstr -> lInstr -> lInstr
  | LInstrWhile  : lBExp -> lInstr -> lInstr

let ( =. ) = LInstrAssign
let Skip = LInstrSkip
let ( >> ) = LInstrSeq 

type thenTag = | Then
type elseTag = | Else
type endTag  = | End
type doTag   = | Do

let iF (cond:lBExp) (_:thenTag) (b1:lInstr) (_:elseTag) (b2:lInstr) (_:endTag) : lInstr = LInstrIf cond b1 b2

val while : lBExp -> doTag -> lInstr -> endTag -> lInstr
let while cond _ body _ = LInstrWhile cond body

let a = "a"
let b = "b"
let c = "c"
let d = "d"
let i = "i"
let tmp = "tmp"

let fib (max:int) =
  (a =. (v 1)) >>
  (b =. (v 1)) >>
  (i =. (v 0)) >>
  (while (!! i <=. (LAExpLitt max)) Do (
    (tmp =. (!! a)) >>
    (a =. (!! b)) >>
    (b =. (!! tmp) +. (!! b)) >>
    (i =. (!! i) +. (v 1))
  ) End)

type state (a:Type) = string -> a

class hasDefaultValue a = {
  def: a
}
instance _ : hasDefaultValue int = {def = 0}

let emptyState #a [| hasDefaultValue a |] () : state a =
  fun _ -> def

open FStar.Mul


// interface _ : run_c = {} 
val norm_lAExp : state int -> lAExp -> int
let rec norm_lAExp state exp =
  let fA a b g = g (norm_lAExp state a) (norm_lAExp state b) in
  match exp with 
  | LAExpLitt v -> v
  | LAExpMinus a b -> fA a b ( fun x y -> x - y )
  | LAExpMult a b -> fA a b  ( * )
  | LAExpPlus a b -> fA a b  ( + )
  | LAExpVar v -> state v

val norm_lBExp : state int -> lBExp -> bool
let rec norm_lBExp state exp =
  let fA a b g = g (norm_lAExp state a) (norm_lAExp state b) in
  let fB a b g = g (norm_lBExp state a) (norm_lBExp state b) in
  match exp with
  | LBExpLitt v -> v
  | LBExpEq a b -> fA a b ( fun a b -> a = b )
  | LBExpLe a b -> fA a b (<=)
  | LBExpAnd a b-> fB a b (&&)
  | LBExpOr a b -> fB a b ( || )
  | LBExpNot a -> norm_lBExp state a

class run_c a b = {
  run : state int -> a -> b
}
instance _ : run_c lAExp int = { run = norm_lAExp }
instance _ : run_c lBExp bool = { run = norm_lBExp }

val norm_lInstr : state int -> lInstr -> (fuel:nat) -> Tot (state int) (decreases fuel)
let rec norm_lInstr state instr n = if n = 0 then state else
  let f = norm_lInstr in
  match instr with
  | LInstrAssign name v -> (fun q -> if q = name then run state v else state q)
  | LInstrIf cond b1 b2 -> norm_lInstr state (if run state cond then b1 else b2) (n - 1)
  | LInstrSkip          -> state
  | LInstrSeq a b       -> f (f state a (n - 1)) b (n - 1)
  | LInstrWhile cond b  -> if run state cond then
				f state (b >> (while cond Do b End)) (n - 1)
			  else  state

instance _ : run_c lInstr (state int) = { run = fun s a -> norm_lInstr s a 100 }

val execFib : int -> state int
let execFib n = (run (emptyState ()) (fib n))

let xx n = execFib n "a"

let test = norm_lBExp (emptyState ()) (LBExpLitt true)


let xxx = run (emptyState ()) (v 2 +. v 3)

// let main = 
//   let i = FStar.IO.input_int () in
//   FStar.IO.print_string (string_of_int (xx i))

let isPartialOrder #a (f:(a -> a -> bool)) =
    (forall a    . f a a)
  /\ (forall a b  . f a b /\ f b a ==> a == b)
  /\ (forall a b c. f a b /\ f b c ==> f a c)

class hasPartialOrder a = {
   po : (f:(a -> a -> bool){isPartialOrder f})
}

let isPartialOrderL #a (cmp:a->a->Type0) (f:(a -> a -> Type0)) =
    (forall a    . f a a)
  /\ (forall a b  . f a b /\ f b a ==> cmp a b)
  /\ (forall a b c. f a b /\ f b c ==> f a c)
  
class hasLPartialOrder (a:Type) = {
  l_po_cmp : a -> a -> Type;
  l_po : (f:(a -> a -> Type){isPartialOrderL l_po_cmp f})
}

instance derivedLPO (someInstance : hasPartialOrder 'a) : hasLPartialOrder 'a = {
  l_po_cmp = (fun x y -> x == y);
  l_po = fun x y -> po x y == true
}
instance _ : hasPartialOrder int = { po = fun a b -> a <= b } 

let isMonotonic #a #b [| hasLPartialOrder a |] [| hasLPartialOrder b |] (f:(a -> b)) =
  forall a b. a `l_po` b ==> f(a) `l_po` f(b)

instance csetLPO #c : hasLPartialOrder (CSet.set c) = {
 	  l_po_cmp = CSet.equal;
	  l_po = let h = (fun (a b: CSet.set c) -> true == CSet.subset a b) in admitP (isPartialOrderL CSet.equal h); h
 	}

instance gsetLPO #c : hasLPartialOrder (GSet.set c) = {
 	  l_po_cmp = GSet.equal;
	  l_po = GSet.subset
 	}

// instance ordsetLPO (t:eqtype) (cmp:(t->t->bool){total_order t cmp}) : 
// 	 hasLPartialOrder (ordset t cmp) = {
//     l_po_cmp = equal
//   ; l_po = fun a b -> subset a b
// }

let cset_to_set (#t:eqtype) (s:CSet.set t) =
   GSet.as_set' (CSet.set_to_list s)

// class hasTotalOrder (a:eqtype) = {
//   to : (to:(a->a->bool){ total_order a to })
// }
// instance totImpPartial (a:eqtype) (_:hasTotalOrder a) : hasPartialOrder a = { po = to } 

class hasGaloisConnection (c:eqtype) a = {
     c_po  : hasPartialOrder c
   ; a_po  : hasPartialOrder a
   ; gamma : (f:(a -> set c){ isMonotonic f })
   ; alpha : (f:(CSet.set c -> a){ isMonotonic f })
   ; galois_wf : (sa:a) -> (sc:CSet.set c) ->
		 Lemma (cset_to_set sc `l_po` (gamma sa) /\ sa `l_po` (alpha sc))
   ; alpha': c -> a
}

let mkGaloisConnection (#c:eqtype) #a
			     [| hasPartialOrder c   |]
			     [| hasPartialOrder a |]
			     (gamma:(a -> set c){ isMonotonic gamma })
			     (alpha:(CSet.set c -> a){ isMonotonic alpha })
			     (galois_wf : (sa:a) -> (sc:CSet.set c) -> 
					Lemma (cset_to_set sc `l_po` (gamma sa) /\ sa `l_po` (alpha sc))
			     )
  = {
	c_po      = solve
      ; a_po      = solve
      ; gamma     = gamma
      ; alpha     = alpha
      ; galois_wf = galois_wf
      ; alpha'    = (fun c -> alpha (CSet.singleton c))
    }

instance _ : hasPartialOrder interval = { po = includes }

let interval_alpha set = Interval.values_to_interval (CSet.set_to_list set)
let h l1 l2 = (l1 `l_po` l2 ==> interval_alpha l1 `po` interval_alpha l2)
let _ = assert ( h [1;2;3] [1;3] )

open FStar.Tactics

let rec lemma_intervalAlpha_eq_modulo_order (a:CSet.set int) (b:CSet.set int{CSet.equal a b})
    : Lemma (interval_alpha a == interval_alpha b) = admit ()

let rec inteval_alpha_behead_both (hd:int)
                  (l1:CSet.set int{CSet.no_dup (hd::l1)})
                  (l2:CSet.set int{CSet.no_dup (hd::l2)})
      : Lemma (interval_alpha l1 `po` interval_alpha l2 == interval_alpha (hd::l1) `po` interval_alpha (hd::l2))
      = match l1 with
      | [] -> (match l2 with
        | [] -> ()
        | h2::t2 -> admit () 
        )
      | _ -> admit ()

let rec lemma_intervalAlpha_ind (hd:int) (l1:CSet.set int{CSet.no_dup (hd::l1)})
                  (l2:CSet.set int{CSet.mem hd l2 /\ interval_alpha l1 `po` interval_alpha (CSet.remove l2 hd)})
    : Lemma (interval_alpha (hd::l1) `po` interval_alpha l2) = 
            assert (CSet.no_dup (CSet.remove l2 hd));
              
            admitP (CSet.no_dup (hd::(CSet.remove l2 hd)));
            admitP (CSet.equal l2 (hd::(CSet.remove l2 hd)));
            assert (CSet.mem hd l2);
            lemma_intervalAlpha_eq_modulo_order l2 (hd::(CSet.remove l2 hd));
            inteval_alpha_behead_both hd l1 (CSet.remove l2 hd)

let rec interval_alpha_monotonicy' (l1:CSet.set int) (l2:CSet.set int{l1 `l_po` l2})
  : Lemma (interval_alpha l1 `po` interval_alpha l2)
  = match l1 with
  | [] -> ()
  | hd::tl -> CSet.lemma_subset_remove tl l2 hd;
            assert (CSet.subset tl (CSet.remove l2 hd));
            assert (CSet.mem hd l2);
            interval_alpha_monotonicy' tl (CSet.remove l2 hd);
            assert (interval_alpha tl `po` interval_alpha (CSet.remove l2 hd));
            lemma_intervalAlpha_ind hd tl l2

let _ = assert (isMonotonic (Interval.gamma))

instance _ : hasGaloisConnection int interval = mkGaloisConnection
                                 Interval.gamma
                                 (admitP (isMonotonic interval_alpha); interval_alpha)
                                 (magic ())

class hasAbstractDomain a = {
  union : a -> a -> a;
  inter : a -> a -> a;
  bottom: a;
  top   : a;
  widen : a -> a -> a;
  assign: string -> a -> a;
  aeq : a -> a -> bool;
}

let mkAbstractDomain union inter bottom top widen assign aeq
    = {
        union = union
      ; inter = inter
      ; bottom = bottom
      ; top = top
      ; widen = widen
      ; assign = assign
      ; aeq = aeq
    }

class hasAbstractOperators a = {
    abstract_domain:  hasAbstractDomain a
  ; default_value:    hasDefaultValue a
  ; a_op_unary_minus: a -> a
  ; a_op_plus:        a -> a -> a
  ; a_op_minus:       a -> a -> a
  ; a_op_times:       a -> a -> a
}

let backward_aop_le0         #a [| hasAbstractOperators a |] [| hasAbstractDomain a |] (x r  :a) (lessThanZero:a)
    = x `inter` lessThanZero
let backward_aop_unary_minus #a [| hasAbstractOperators a |] [| hasAbstractDomain a |] (x r  :a)
    = x `inter` (a_op_unary_minus r)
let backward_aop_plus        #a [| hasAbstractOperators a |] [| hasAbstractDomain a |] (x y r:a)
    = (x `inter` (r `a_op_minus` y), y `inter` (r `a_op_minus` r)) 
let backward_aop_minus       #a [| hasAbstractOperators a |] [| hasAbstractDomain a |] (x y r:a)
    = (x `inter` (r `a_op_plus` y), y `inter` (x `a_op_minus` r)) 
// let backward_aop_mul #a [| hasAbstractOperators a |] [| hasAbstractDomain a |] (x y r:a)
//     = (x `inter` (r `a_op` y), y `inter` (r `a_op_minus` r))

// let backward_aop_lt #a [| hasAbstractOperators a |] = 

let mkAbstractOperators #a [| hasAbstractDomain a |] [| hasDefaultValue a |]
  a_op_unary_minus a_op_plus a_op_minus a_op_times
  = {
    abstract_domain  = solve
  ; default_value    = solve
  ; a_op_unary_minus = a_op_unary_minus
  ; a_op_plus        = a_op_plus
  ; a_op_minus       = a_op_minus
  ; a_op_times       = a_op_times
  }

let rec interval_widen (i j:interval) = match (i, j) with
  | (SomeInterval a b, SomeInterval c d) -> SomeInterval (if ExtInt.le a c then a else ExtInt.minusInfty)
                                                        (if ExtInt.ge b d then b else ExtInt.plusInfty)
  | (EmptyInterval, EmptyInterval) -> i
  | (a, EmptyInterval) -> a
  | (EmptyInterval, a) -> a

instance intervalDomain : hasAbstractDomain interval = mkAbstractDomain #interval
                          Interval.union
                          Interval.inter
           (*bottom*)     Interval.EmptyInterval
           (*top*)        (Interval.SomeInterval ExtInt.minusInfty ExtInt.plusInfty)
           (*widen*)      interval_widen
           (*assign*)     (fun _ (i: interval) -> i)
                          Interval.equal

instance _ : hasDefaultValue interval = {def = (SomeInterval (SomeInt 0) (SomeInt 0))}

instance intervalOperators : hasAbstractOperators interval = mkAbstractOperators
                          Interval.unaryMinus
                          Interval.plus
                          Interval.minus
                          Interval.times

let rec static_analysis_aexp #a [| hasGaloisConnection int a |] [| hasAbstractOperators a |]
                    (st:state a)
                    (exp:lAExp)
                    : a
  = let rec h (exp:lAExp): a = 
         match exp with
       | LAExpLitt n       -> alpha' n
       | LAExpVar  varName -> st varName
       | LAExpPlus a b     -> (h a) `a_op_plus` (h b)
       | LAExpMinus a b    -> (h a) `a_op_minus` (h b)
       | LAExpMult a b    ->  (h a) `a_op_times` (h b)
    in h exp

noeq
type enumerableMap a = {
   _em_data: string -> a
 ; _em_keys: CSet.set string
}
let state_to_em s = {_em_data = s;_em_keys = []}
let em_get (m:enumerableMap 'a) (k:string): 'a = m._em_data k
let em_set (m:enumerableMap 'a) (k:string) (v:'a) = let data = fun q -> if q = k then v else m._em_data q in {
   _em_data = data
 ; _em_keys = CSet.add_in_set k m._em_keys
}
let em_combine (m1 m2:enumerableMap 'a) (f:'a -> 'a -> 'a) = {
   _em_data = (fun key -> f (em_get m1 key) (em_get m2 key))
 ; _em_keys = CSet.union m2._em_keys m1._em_keys
}

let em_equal #a (myEq:a->a->bool) (m1 m2:enumerableMap a) =
    let f1 = em_get m1 in
    let f2 = em_get m2 in
    let rec h l = (match l with
      | [] -> true
      | hd::tl -> if f1 hd `myEq` f2 hd then h tl else false
    ) in h (CSet.union m2._em_keys m1._em_keys)

// let rec is_bexp_normalized (e:lBExp) = match e with
//   | LBExpLitt  _ -> False
//   | LBExpNot   b -> is_bexp_normalized b
//   | LBExpAnd a b -> is_bexp_normalized a /\ is_bexp_normalized b
//   | LBExpOr  a b -> is_bexp_normalized a /\ is_bexp_normalized b
//   | LBExpEq  a b -> is_bexp_normalized a /\ is_bexp_normalized b
//   | LBExpLe  a b -> is_bexp_normalized a /\ b == (v 0)
let rec backward_analysis_aexp #a [| hasGaloisConnection int a |] [| hasAbstractOperators a |]
                                  [| hasAbstractDomain a |]
                    (st:enumerableMap a)
                    (exp:lAExp)
                    (aim:a)
                    : Tot (enumerableMap a) (decreases exp)
= let f exp = static_analysis_aexp (em_get st) exp in
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

class hasLessOrZero a = {
   lessOrZero: a
}
instance _ : hasLessOrZero interval = { lessOrZero = SomeInterval minusInfty (SomeInt 0) }


let rec bexp_count_not (e:lBExp): nat = match e with
  | LBExpNot (LBExpEq _ _) -> 0
  | LBExpNot x -> 1 + bexp_count_not x
  | LBExpAnd x y -> bexp_count_not x + bexp_count_not y
  | LBExpOr x y -> bexp_count_not x + bexp_count_not y
  | _ -> 0

let sad = let v = v 3 in (v <=. v) &&. (!. (v ==. v))
//let _ = assert ((bexp_count_not sad, sad) == magic ()) by (compute (); qed ())

let rec analyse_bexp #a [| hasAbstractOperators a |] [| hasAbstractDomain a |] [| hasGaloisConnection int a |] [| hasLessOrZero a |]
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
  | LBExpLe   a b -> backward_analysis_aexp st (a -. b) lessOrZero

//let rec em_bigger
let rec static_analysis_instr #a [| hasAbstractOperators a |] [| hasAbstractDomain a |] [| hasGaloisConnection int a |] [| hasLessOrZero a |]
                    (st:enumerableMap a)
                    (instr:lInstr)
                    : Tot (enumerableMap a) (decreases instr)
  = let f = static_analysis_instr in
    match instr with
  | LInstrAssign name v -> em_set st name (static_analysis_aexp (em_get st) v)
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

let myProg = (
  (a =. (v 23)) >>
  (a =. (!! a) +. (!! b))
  )
let myState : enumerableMap interval = 
  em_set (
    state_to_em (emptyState ())
  ) "a" (SomeInterval (SomeInt 23) (SomeInt 23))




open FStar.String

class hasToString t = {
  toString: t -> string
}
instance _ : hasToString extInt =  { toString = fun i -> match i with
    | SomeInt n -> string_of_int n
    | _ -> if i = plusInfty then "+inf" else "-inf"}

let join sep l = List.Tot.Base.fold_right (fun a b -> (if a = "" then sep else "") `strcat` (a `strcat` b)) l ""

instance _ : hasToString interval =  { toString = fun i ->  match i with
  | EmptyInterval -> "[]"
  | SomeInterval l (r:extInt) -> join "" ["[";toString l;" ; ";toString r;"]"]}

instance emHasToString #a [| hasToString a |] : hasToString (enumerableMap a) =  { toString = fun i -> 
  "{" `strcat`
         join ", " (List.Tot.Base.map (fun s -> s `strcat` " = " `strcat` toString (em_get i s)) i._em_keys)
      `strcat` "}"
}

let fib' (max:int) =
  (a =. (v 1)) >>
  (b =. (v 1)) >>
  (i =. (v 0)) >>
  (while (!! i <=. (v max)) Do (
    (tmp =. (!! a)) >>
    (a =. (!! b)) >>
    (b =. (!! tmp) +. (!! b)) >>
    (i =. (!! i) +. (v 1))
  ) End)

let prog2 = (
  (a =. (v 0)) >>
  (b =. (v 0)) >>
  (while ((!! a) <=. (v 10)) Do (
    (a =. (!! a) +. (v 1)) >>
    (b =. (!! b) +. (!! a))
  ) End)
)
let prog3 = (a =. (v 28))

let hey  = static_analysis_instr myState prog2
let hey2 = static_analysis_instr myState prog3
let hey3 = analyse_bexp myState ((!! a) <=. (v 4))
let hey4 = static_analysis_instr myState (fib 0)


//let _ = assert (em_get hey3 "a"  == magic ()) by (compute(); qed ())
//let _ = assert (em_equal aeq (hey) (hey2)) by (compute (); qed ())
let _ = assert (emHasToString.toString hey == magic()) by (compute (); qed ())



let main = 
  let i = FStar.IO.input_int () in
  FStar.IO.print_string (emHasToString.toString hey4)


let rec listToState (#a:Type) [| hasDefaultValue a |] (lst:list (tuple2 string a))
  = fun (query:string) -> match lst with
  | [] -> def
  | (name, value)::tl -> if name = query then value else listToState tl query

let test0 = static_analysis_aexp (listToState [
  ("hey", SomeInterval (SomeInt 2) (SomeInt 4))
]) (v 10 *. !! "hey")
 
//let _ = assert (test0 == magic ()) by (compute ();qed ())

//let verif_test0 = assert (test0 == SomeInterval (SomeInt 4) (SomeInt 4))

//let hey =  static_analysis_aexp (emptyState ()) 
//hey
