module CartProdAbs

open AbstractDomain
open PartialOrder
open FStar.Tactics.Typeclasses
open DefaultValue
open ToString
open ZeroOrLess
open GaloisConnection

private
let (<*>) #ta #tb #ra #rb ((f1, f2): (ta -> ra) * (tb -> rb)) (a, b): (ra * rb) = (f1 a, f2 b)

private
let (<$>) #ta #tb #ra #rb ((fl, fr): ((ta -> ra) * (tb -> rb))) (a, b): (ra * rb) = (fl a, fr b)


let lt (#ta #tb: Type) [| hasPartialOrder ta |] [| hasPartialOrder tb |]
                     ((a, b): (ta*tb)) ((a', b'): (ta*tb))
                     = a `po` a' && b `po` b'

// let _ = assert (isPartialOrder lt)


instance tupAbsDomHasPartialOrder (a b: Type) [| hasPartialOrder a |] [| hasPartialOrder b |]: hasPartialOrder (a * b) = { po = lt }

let union #ta #tb [| hasAbstractDomain ta |] [| hasAbstractDomain tb |]
          (a: (ta * tb)) b = (union, union) <*> a <$> b

let inter #ta #tb [| hasAbstractDomain ta |] [| hasAbstractDomain tb |]
          (a: (ta * tb)) b = (inter, inter) <*> a <$> b
          
let bottom #ta #tb [| hasAbstractDomain ta |] [| hasAbstractDomain tb |]
           : (ta * tb) = (bottom, bottom)
let top #ta #tb [| hasAbstractDomain ta |] [| hasAbstractDomain tb |]
           : (ta * tb) = (top, top)

let widen #ta #tb [| hasAbstractDomain ta |] [| hasAbstractDomain tb |]
          (a: (ta * tb)) b = (widen, widen) <*> a <$> b

let narrow #ta #tb [| hasAbstractDomain ta |] [| hasAbstractDomain tb |]
          (a: (ta * tb)) (b: (ta * tb){lt #ta #tb #ab_dom_po #ab_dom_po b a}) =
          (admit(); narrow, narrow) <*> a <$> b // TODO Remove admit ! should be "easy"

let assign #ta #tb [| hasAbstractDomain ta |] [| hasAbstractDomain tb |]
          a (b: (ta * tb)) = (assign, assign) <*> (a,a) <$> b

let aeq #ta #tb [| hasAbstractDomain ta |] [| hasAbstractDomain tb |]
          (a: (ta * tb)) b = let (r1, r2) = (aeq, aeq) <*> a <$> b in r1 && r2

//let _gamma #ta #tb [| hasGaloisConnection ta |] [| hasGaloisConnection tb |]   = 

module G = FStar.GSet
module C = CSet

instance tupAbsDomHasGaloisConnection (#c: eqtype) (#a #b:Type) [| hasPartialOrder c |] [| hasPartialOrder a |] [| hasPartialOrder b |] [| hasGaloisConnection c a |] [| hasGaloisConnection c b |]  = mkGaloisConnection #c #(a*b) #solve #(tupAbsDomHasPartialOrder a b)
                                    (admit (); fun (a, b) ->  G.union (gamma a) (gamma b))
                                    (admit (); fun a -> (alpha a, alpha a)) (magic ())

let isBottomCart  (#a #b:Type) [| hasAbstractDomain a |] [| hasAbstractDomain b |] ((x, y):(a*b)) = isBottom x || isBottom y

instance tupAbsDomHasAbstractDomain (#a #b:Type) [| hasAbstractDomain a |] [| hasAbstractDomain b |]: hasAbstractDomain (a * b) = mkAbstractDomain #(a * b) #(tupAbsDomHasPartialOrder a b #ab_dom_po #ab_dom_po) union inter bottom top widen narrow assign aeq isBottomCart

let a_op_unary_minus #a #b [| hasAbstractOperators a |] [| hasAbstractOperators b |] (x: a*b)  = 
  (a_op_unary_minus, a_op_unary_minus) <$> x
let a_op_plus #a #b [| hasAbstractOperators a |] [| hasAbstractOperators b |] (x: a*b) y  = 
  (a_op_plus, a_op_plus) <$> x <*> y
let a_op_minus #a #b [| hasAbstractOperators a |] [| hasAbstractOperators b |] (x: a*b) y  = 
  (a_op_minus, a_op_minus) <$> x <*> y
let a_op_times #a #b [| hasAbstractOperators a |] [| hasAbstractOperators b |] (x: a*b) y  = 
  (a_op_times, a_op_times) <$> x <*> y
let a_op_div #a #b [| hasAbstractOperators a |] [| hasAbstractOperators b |] (x: a*b) y  = 
  (a_op_div, a_op_div) <$> x <*> y

instance tupAbsDomHasDefaultValue #a #b [| hasDefaultValue a |] [| hasDefaultValue b |] : hasDefaultValue (a * b) = { def = (def, def) }

instance tupAbsDomHasToString #a #b [| hasToString a |] [| hasToString b |]: hasToString (a * b) = {
  toString = fun (a, b) -> "(" ^ toString a ^ ", " ^ toString b ^ ")"
}

instance tupAbsDomHasZeroOrLess (#a #b:Type) [| hasZeroOrLess a |] [| hasZeroOrLess b |]: hasZeroOrLess (a * b) = {
  zeroOnly = (zeroOnly, zeroOnly);
  zeroOrLess = (zeroOrLess, zeroOrLess);
  aroundZero = (aroundZero, aroundZero)
}

instance tupAbsDomHasAbstractOperators (#a #b:Type) [| hasDefaultValue (a * b) |] [| hasAbstractOperators a |] [| hasAbstractOperators b |] [| hasAbstractDomain (a * b) |] = 
  mkAbstractOperators #(a*b) a_op_unary_minus a_op_plus a_op_minus a_op_times a_op_div

