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
  | LBExpLt  : lAExp -> lAExp -> lBExp

let ( !.  ) = LBExpNot
let ( &&. ) = LBExpAnd
let ( ||. ) = LBExpOr
let ( ==. ) = LBExpEq
let ( <.  ) = LBExpLt

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

val iF : int -> int
let iF v = v

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
  (while (!! i <. (LAExpLitt max)) Do (
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
  | LBExpLt a b -> fA a b (<)
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

let main = 
  let i = FStar.IO.input_int () in
  FStar.IO.print_string (string_of_int (xx i))

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

class hasAbstractDomain (c:eqtype) a = {
  galois_connection : hasGaloisConnection c a;
  union : a -> a -> a;
  inter : a -> a -> a;
  bottom: a;
  top   : a;
  widen : a -> a -> a;
  assign: string -> a -> a;
  op_eq : a -> a -> a;
}

let mkAbstractDomain (#c:eqtype) #a
                                  [| hasGaloisConnection c a |]
                                  union inter bottom top widen assign op_eq
    = {
        galois_connection = solve
      ; union = union
      ; inter = inter
      ; bottom = bottom
      ; top = top
      ; widen = widen
      ; assign = assign
      ; op_eq = op_eq
    }

class hasAbstractOperators (c:eqtype) a = {
    abstract_domain:  hasAbstractDomain c a
  ; default_value:    hasDefaultValue a
  ; a_op_unary_minus: a -> a
  ; a_op_unary_lift:  c -> a
  ; a_op_plus:        a -> a -> a
  ; a_op_minus:       a -> a -> a
  ; a_op_times:       a -> a -> a
}

let mkAbstractOperators (#c:eqtype) #a [| hasAbstractDomain c a |] [| hasDefaultValue a |]
  a_op_unary_minus a_op_plus a_op_minus a_op_times
  = {
    abstract_domain  = solve
  ; default_value    = solve
  ; a_op_unary_lift  = (fun c -> galois_connection.alpha (CSet.singleton c))
  ; a_op_unary_minus = a_op_unary_minus
  ; a_op_plus        = a_op_plus
  ; a_op_minus       = a_op_minus
  ; a_op_times       = a_op_times
  }

instance intervalDomain : hasAbstractDomain int interval = mkAbstractDomain
                          Interval.union
                          Interval.inter
           (*bottom*)     Interval.EmptyInterval
           (*top*)        (Interval.SomeInterval ExtInt.minusInfty ExtInt.plusInfty)
           (*widen*)      Interval.union
           (*assign*)     (fun _ i -> i)
                          Interval.union

instance _ : hasDefaultValue interval = {def = (SomeInterval (SomeInt 0) (SomeInt 0))}

instance intervalOperators : hasAbstractOperators int interval = mkAbstractOperators
                          Interval.unaryMinus
                          Interval.plus
                          Interval.minus
                          Interval.times
                          
noeq
type ctx (#c:eqtype) #a = {
  memory: string -> state a
}


//let static_analysis_aexp (#c:eqtype{c==int}) #a [| hasAbstractOperators c a |]
let rec static_analysis_aexp #a [| hasAbstractOperators int a |]
                    (st:state a)
                    (exp:lAExp)
                    : a
  = let rec h (exp:lAExp): a = 
         match exp with
       | LAExpLitt n       -> a_op_unary_lift n
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

let rec interval_widen (i j:interval) = match (i, j) with
  | (SomeInterval a b, SomeInterval c d) -> SomeInterval (if ExtInt.le a c then a else ExtInt.minusInfty)
                                                        (if ExtInt.ge b d then b else ExtInt.plusInfty)
  | (EmptyInterval, EmptyInterval) -> i
  | (a, EmptyInterval) -> a
  | (EmptyInterval, a) -> a

//let rec em_bigger  

let rec static_analysis_instr #a [| hasAbstractOperators int a |]// (#ad:hasAbstractDomain int a)
                    (_inter: a -> a -> a) (*dirty hack*)
                    (_eq: a -> a -> bool)
                    (_w:  a -> a -> a)
                    (st:enumerableMap a)
                    (instr:lInstr)
                    : Tot (enumerableMap a) (decreases instr)
  = match instr with
  | LInstrAssign name v -> em_set st name (static_analysis_aexp (em_get st) v)
  | LInstrSkip -> st
  | LInstrSeq b1 b2 -> static_analysis_instr _inter _eq _w (static_analysis_instr _inter _eq _w st b1) b2 
  | LInstrIf c b1 b2 -> let r1 = static_analysis_instr _inter _eq _w st b1 in
                       let r2 = static_analysis_instr _inter _eq _w st b2 in
                       em_combine r1 r2 _inter
  | LInstrWhile c b1 -> let execOnce st = static_analysis_instr _inter _eq _w st b1 in
                       let rec lookForFixPoint st: Tot (enumerableMap a) = // (decreases (admitP (False))) = 
                         let new_st  = execOnce st in
                         let widened = em_combine st new_st _w in 
                         if   em_equal _eq st widened
                         then widened // new_st
                         else lookForFixPoint new_st//(admitP (%[new_st] << %[st]); new_st)
                       in execOnce st

let myProg = (
  (a =. (v 23)) >>
  (a =. (!! a) +. (!! b))
  )
let myState : enumerableMap interval = 
  em_set (state_to_em (emptyState ())) "b" (SomeInterval (SomeInt 2) (SomeInt 9))



let hey = static_analysis_instr Interval.inter (fun x y -> x = y) interval_widen myState myProg

let _ = assert (em_get hey "a" == magic()) by (compute (); qed ())


let rec listToState (#a:Type) [| hasDefaultValue a |] (lst:list (tuple2 string a))
  = fun (query:string) -> match lst with
  | [] -> def
  | (name, value)::tl -> if name = query then value else listToState tl query

let test0 = static_analysis_aexp (listToState [
  ("hey", SomeInterval (SomeInt 2) (SomeInt 4))
]) (v 10 *. !! "hey")

let _ = assert (test0 == magic ()) by (compute ();qed ())

let verif_test0 = assert (test0 == SomeInterval (SomeInt 4) (SomeInt 4))

//let hey =  static_analysis_aexp (emptyState ()) 
//hey
