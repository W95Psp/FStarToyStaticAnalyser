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
let mkInterval (l:int) (r:int{l < r}) = SomeInterval (SomeInt l) (SomeInt r)

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

let minus = h2 (fun a b ->
    let (SomeInterval a1 a2) = a in
    let (SomeInterval b1 b2) = b in
    SomeInterval (a1 `minus` b2) (a2 `minus` b1)
  )

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

instance intervalDomain : hasAbstractDomain interval = mkAbstractDomain #interval
                          union
                          inter
           (*bottom*)     EmptyInterval
           (*top*)        (SomeInterval ExtInt.minusInfty ExtInt.plusInfty)
           (*widen*)      interval_widen
           (*assign*)     (fun _ (i: interval) -> i)
                          equal
instance _ : hasDefaultValue interval = {def = (SomeInterval (SomeInt 0) (SomeInt 0))}
instance _ : hasZeroOrLess interval = { zeroOrLess = SomeInterval minusInfty (SomeInt 0) }
instance intervalOperators : hasAbstractOperators interval = mkAbstractOperators unaryMinus plus minus times
