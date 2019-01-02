(*
@summary: Integer intervals (possibly infinite)
*)
module Interval

open ExtInt
open PartialOrder
open FStar.List.Tot
open FStar.Tactics.Typeclasses
open ToString

open AbstractDomain
open GaloisConnection
open DefaultValue

open ZeroOrLess

module G = FStar.GSet

type interval = | EmptyInterval : interval
		| SomeInterval  : (l:extInt) -> (r:extInt{l `le` r}) -> interval

let mkExtInterval (l:extInt) (r:extInt{l `lt` r}) = SomeInterval l r
let mkInterval (l:int) (r:int{l <= r}) = SomeInterval (SomeInt l) (SomeInt r)

let union (a b:interval) = match a with
  | EmptyInterval -> b
  | SomeInterval l1 r1 -> match b with
		 | EmptyInterval -> a
		 | SomeInterval l2 r2 ->
                                 assert (l1 `le` r1);
                                assert (l2 `le` r2);
                                assert (min l1 l2 `le` max r1 r2);
                                SomeInterval (min l1 l2) (max r1 r2) 

let inter (a b:interval) = match a with
  | SomeInterval l1 r1 -> 
        (match b with
	| SomeInterval l2 r2 -> let l3 = max l1 l2 in
	 		       let r3 = min r1 r2 in
				   if l3 `gt` r3 then EmptyInterval
						 else SomeInterval l3 r3
	| _ -> b) // empty
  | _ -> a // if empty

// let x = (SomeInterval (SomeInt 23) (SomeInt 23))
// let y = inter x (SomeInterval minusInfty plusInfty)

// let _ = assert (y == magic()) by (compute (); qed ()) 

let includes (a b:interval) = match a with
  | EmptyInterval -> true
  | SomeInterval l1 r1 -> match b with
    | EmptyInterval -> false
    | SomeInterval l2 r2 -> (l1 `ge` l2) && (r1 `le` r2)

let gamma (i: interval): GSet.set int = match i with
  | EmptyInterval -> GSet.empty
  | SomeInterval l r -> GSet.comprehend (fun v' -> let v = SomeInt v' in (v `ge` l) || (v `le` r))


let lemma_includes_trans' (a:interval)
                         (b:interval{includes a b})
                         (c:interval{includes b c})
                       : Lemma (includes a c) = ()
                             
let lemma_includes_trans (a:interval)
                         (b:interval)
                         (c: interval)
                         : Lemma (includes a b ==> includes b c ==> includes a c) = ()
                         // if includes a b && includes b c then (
                         //   lemma_includes_trans' a b c
                         // ) else ()


let _ = assert (forall (a b c:interval). includes a b ==> includes b c ==> includes a c)
let _ = assert (forall a b c. includes a b ==> includes b c ==> includes a c)

let values_to_interval (l: list int) =
  // let f #t (g:t->t->bool) (a:t) (b:t) : t = if a `g` b then a else b in
  // let l = List.Tot.Base.map SomeInt lInt in
  //             SomeInterval 
  //                 (min minusInfty (fold_left (f lt) plusInfty l))
  //                 (max plusInfty (fold_left (f gt) minusInfty l))
  let enlarge (tup:extInt * extInt) (current':int) = (
              let (l, r) = tup in
              let current = SomeInt current' in
              (min l current, max r current)
            ) in
  let (l, r) = fold_left enlarge (plusInfty, minusInfty) l in
  if r `lt` l then EmptyInterval
              else SomeInterval l r 

let nonEmptyInterval = x:interval{SomeInterval? x}

(* those are just helpers *)
private
let h1 (f:nonEmptyInterval -> nonEmptyInterval) (a:interval): interval = match a with
  | EmptyInterval -> EmptyInterval
  | _ -> f a

private
let h2 (f:nonEmptyInterval -> nonEmptyInterval -> nonEmptyInterval)
       (a b:interval): interval = match a with
  | EmptyInterval -> EmptyInterval
  | _ -> match b with
    | EmptyInterval -> EmptyInterval
    | _ -> f a b

let plus = h2 (fun a b ->
    let (SomeInterval a1 a2) = a in
    let (SomeInterval b1 b2) = b in
    SomeInterval (a1 `plus` b1) (a2 `plus` b2)
  )

 
private
let lift_cst x = mkInterval x x
//let lemma_plus (a: int) (b: int): Lemma (plus (lift_cst a) (lift_cst b) = lift_cst (a + b)) = () 

let correct_bin_op_abstraction
    #a #c
    (c_op: c -> c -> c)
    (a_op: a -> a -> a)
    (lift: c -> a)
    (le: a -> a -> bool)
    a0 a1 (c0: c {lift c0 `le` a0})
          (c1: c {lift c1 `le` a1})
  = (lift (c_op c0 c1) `le` a_op a0 a1)

let correct_bin_op_abstraction'
    #a #c
    (c_op: c -> c -> c)
    (a_op: a -> a -> a)
    (lift: c -> a)
    (le: a -> a -> bool)
    a0 a1 c0 c1
  = ((lift c0 `le` a0 && lift c1 `le` a1) ==> lift (c_op c0 c1) `le` a_op a0 a1)

let lemma_add_correct x y x' y': Lemma (correct_bin_op_abstraction (+) plus lift_cst includes x y x' y') = ()

let minus = h2 (fun a b ->
    let (SomeInterval a1 a2) = a in
    let (SomeInterval b1 b2) = b in
    SomeInterval (a1 `minus` b2) (a2 `minus` b1)
  )

let lemma_minus_correct x y x' y': Lemma (correct_bin_op_abstraction (fun a b -> a - b) minus lift_cst includes x y x' y') = ()

let unaryMinus = h1 (fun a -> let (SomeInterval a1 a2) = a in
                            SomeInterval (unaryMinus a2) (unaryMinus a1))

let min4 (a, b, c, d) = min (min a b) (min c d) 
let max4 (a, b, c, d) = max (max a b) (max c d) 
let times = h2 (fun l r ->
    let (SomeInterval a b) = l in
    let (SomeInterval c d) = r in
    let choices = (a `times` c, a `times` d, b `times` c, b `times` d) in
    SomeInterval (min4 choices) (max4 choices)
  )

type si = x: interval {SomeInterval? x /\ (let SomeInterval l r = x
             in l `gt` SomeInt 0 && r `gt` SomeInt 0)}

type int' = n : int {n > 0}
type eint' = n : extInt {SomeInt? n /\ (let SomeInt i = n in i > 0)}

let intervalP n = SomeInt? n && (let SomeInt i = n in i > 0)

let lemma_simplify_for_int' a c b d: Lemma (
   (intervalP a && intervalP b && intervalP c && intervalP d && b `gt` a && d `gt` c) ==> (
     let ( * ) = ExtInt.times in
     let choices = (a * c, a * d, b * c, b * d) in
     (min4 choices) = a * c /\ (max4 choices) = b * d
   )
) = if (intervalP a && intervalP b && intervalP c && intervalP d && b `gt` a && d `gt` c) then () else ()

let lemma_mult_correct (l0:int{l0 > 0 }) (r0:int{r0 >= l0})
                       (l1:int{l1 > 0 }) (r1:int{r1 >= l1})
                       (c0:int{c0 >= l0 /\ c0 <= r0})
                       (c1:int{c1 >= l1 /\ c1 <= r1})
                       : Lemma (correct_bin_op_abstraction Mul.op_Star times lift_cst includes (mkInterval l0 r0) (mkInterval l1 r1) c0 c1) =
  assert_norm (c0 `Mul.op_Star` c1 >= l0 `Mul.op_Star` l1);
  assert_norm (c0 `Mul.op_Star` c1 <= r0 `Mul.op_Star` r1);
  let SomeInterval (SomeInt r_l) (SomeInt r_r) = times (mkInterval l0 r0) (mkInterval l1 r1) in
  assert_norm (r_l == l0 `Mul.op_Star` l1);
  assert_norm (c0 `Mul.op_Star` c1 >= r_l);
  assert (r_r == r0 `Mul.op_Star` r1);
  assert (c0 `Mul.op_Star` c1 <= r_r);
  assert (includes
            (lift_cst (c0 `Mul.op_Star` c1))
            (SomeInterval (SomeInt r_l) (SomeInt r_r))
         );
  ()

private
let div = divide
let rec int_divide (l' r': interval): Tot interval (*decreases
    %[
      SomeInterval? r' && (let SomeInterval c d = r' in (SomeInt 1) `le` c),
      SomeInterval? r' && (let SomeInterval c d = r' in d `le` (SomeInt (-1)))
    ]
  *) = h2 (fun l r -> 
    let SomeInterval a b = l in
    let SomeInterval c d = r in
    if SomeInt 1 `le` c then (
      let nl = (min (a `div` c)
                    (a `div` d)) in
      let nr = (max (b `div` c)
                    (b `div` d)) in
      admitP (nl `le` nr);
      SomeInterval nl nr
    ) else if d `le` SomeInt (-1) then (
      let nl = (min (b `div` c)
                    (b `div` d)) in
      let nr = (max (a `div` c)
                    (a `div` d)) in
      admitP (nl `le` nr);
      SomeInterval nl nr
    ) else (
      admitP (l << l); // todo, show (r `inter` wr*) "widen" second argument, then it goes in the two first cases 
      let wrr = SomeInterval (SomeInt 1) plusInfty in
      let wrl = SomeInterval minusInfty (SomeInt (-1)) in
        (l `int_divide` (r `inter` wrr))
      `union`
        (l `int_divide` (r `inter` wrl))
    )
) l' r'

let divide = int_divide

type maybe a = | Just : a -> maybe a | Nothing : maybe a

let basic_le_interval_int (i:interval) (v':int) = match i with
  | EmptyInterval -> Nothing
  | SomeInterval a b -> let v = SomeInt v' in
                       if a `le` v then Just (SomeInterval a (min b v))
                       else             Nothing

let basic_le_intervals (i j:interval) = match i with
  | EmptyInterval -> Nothing
  | SomeInterval a b -> match j with
                       | EmptyInterval -> Nothing
                       | SomeInterval c d -> if a `le` d then
                                               Just (
                                                 SomeInterval a (min b d),
                                                 SomeInterval (max a c) d
                                               )
                                            else Nothing

let equal (a b:interval) = match (a, b) with
  | (EmptyInterval, EmptyInterval) -> true
  | (SomeInterval a b, SomeInterval c d) -> a=c && b=d
  | _ -> false

instance _ : hasPartialOrder interval = { po = includes }

//Lemma (values_to_interval )

// let rec lemma_includes_wide 
//      (al ar bl br : extInt)
//      (SomeInterval al ar:interval) (SomeInterval bl br:interval{includes a b})
//      : Lemma (al `ge` )

instance _ : hasToString interval =  { toString = fun i ->  match i with
  | EmptyInterval -> "┴"
  | SomeInterval l (r:extInt) -> join "" ["[";toString l;" ; ";toString r;"]"]}

let interval_alpha set = values_to_interval (CSet.set_to_list set)

let rec lemma_intervalAlpha_eq_modulo_order (a:CSet.set int) (b:CSet.set int{CSet.equal a b})
    : Lemma (interval_alpha a == interval_alpha b) = admit () (*TODO*)

let rec inteval_alpha_behead_both (hd:int)
                  (l1:CSet.set int{CSet.no_dup (hd::l1)})
                  (l2:CSet.set int{CSet.no_dup (hd::l2)})
      : Lemma (interval_alpha l1 `po` interval_alpha l2 == interval_alpha (hd::l1) `po` interval_alpha (hd::l2))
      = match l1 with
      | [] -> (match l2 with
        | [] -> ()
        | h2::t2 -> admit ()  (*TODO*)
        )
      | _ -> admit () (*TODO*)

let rec lemma_intervalAlpha_ind (hd:int) (l1:CSet.set int{CSet.no_dup (hd::l1)})
                  (l2:CSet.set int{CSet.mem hd l2 /\ interval_alpha l1 `po` interval_alpha (CSet.remove l2 hd)})
    : Lemma (interval_alpha (hd::l1) `po` interval_alpha l2) = 
            assert (CSet.no_dup (CSet.remove l2 hd));
              
            admitP (CSet.no_dup (hd::(CSet.remove l2 hd))); (*TODO*)
            admitP (CSet.equal l2 (hd::(CSet.remove l2 hd))); (*TODO*)
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

let _ = assert (isMonotonic gamma)

instance _ : hasGaloisConnection int interval = mkGaloisConnection
                                 gamma
                                 (admitP (isMonotonic interval_alpha); interval_alpha) (*TODO*)
                                 (magic ()) 

let rec interval_widen (i j:interval) = match (i, j) with
  | (SomeInterval a b, SomeInterval c d) -> SomeInterval (if ExtInt.le a c then a else ExtInt.minusInfty)
                                                        (if ExtInt.ge b d then b else ExtInt.plusInfty)
  | (EmptyInterval, EmptyInterval) -> i
  | (a, EmptyInterval) -> a
  | (EmptyInterval, a) -> a

private
let bind (x: interval) (f: (extInt * extInt) -> interval) = match x with
  | SomeInterval b0 b1 -> f (b0, b1)
  | EmptyInterval    -> EmptyInterval
  
let interval_narrow l (r:interval{r `includes` l}) =
  match l with
    | EmptyInterval -> EmptyInterval
    | SomeInterval a b -> (match r with
      | EmptyInterval -> EmptyInterval
      | SomeInterval c d -> 
        SomeInterval
          (if a = minusInfty then c else a)
          (if b = plusInfty  then d else b)
      )

// soo bad/let interval_narrow_protected 

instance intervalDomain : hasAbstractDomain interval = mkAbstractDomain #interval
                          union
                          inter
           (*bottom*)     EmptyInterval
           (*top*)        (SomeInterval ExtInt.minusInfty ExtInt.plusInfty)
           (*widen*)      interval_widen
           (*narrow*)     interval_narrow
           (*assign*)     (fun _ (i: interval) -> i)
                          equal
                          (fun x -> EmptyInterval = x)


instance _ : hasDefaultValue interval = {def = (SomeInterval (SomeInt 0) (SomeInt 0))}
instance _ : hasZeroOrLess interval = { zeroOrLess = SomeInterval minusInfty (SomeInt 0); zeroOnly = mkInterval 0 0; aroundZero = mkInterval (-1) (1) }
instance intervalOperators : hasAbstractOperators interval = mkAbstractOperators unaryMinus plus minus times divide
