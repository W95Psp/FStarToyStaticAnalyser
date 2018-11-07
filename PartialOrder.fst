module PartialOrder
open FStar.Tactics.Typeclasses

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

(* generic instance *)
instance derivedLPO (someInstance : hasPartialOrder 'a) : hasLPartialOrder 'a = {
  l_po_cmp = (fun x y -> x == y);
  l_po = fun x y -> po x y == true
}
(* int instance *)
instance _ : hasPartialOrder int = { po = fun a b -> a <= b } 

(* isMonotonic *)
let isMonotonic #a #b [| hasLPartialOrder a |] [| hasLPartialOrder b |] (f:(a -> b)) =
  forall a b. a `l_po` b ==> f(a) `l_po` f(b)
