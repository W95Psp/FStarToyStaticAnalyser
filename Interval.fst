module Interval

open ExtInt
open FStar.List.Tot
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

// [1; 3] is included in [0;4]
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

//Lemma (values_to_interval )

// let rec lemma_includes_wide 
//      (al ar bl br : extInt)
//      (SomeInterval al ar:interval) (SomeInterval bl br:interval{includes a b})
//      : Lemma (al `ge` )

