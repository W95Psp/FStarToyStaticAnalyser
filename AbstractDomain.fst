(*
@summary: Specify what is an abstract domain and what should be abstract operators. Also derive generic backward operators.
*)
module AbstractDomain

open PartialOrder
open DefaultValue
open FStar.Tactics.Typeclasses

class hasAbstractDomain a = {
  ab_dom_po: hasPartialOrder a;
  union : a -> a -> a;
  inter : a -> a -> a;
  bottom: a;
  top   : a;
  widen : a -> a -> a;
  narrow : (l:a) -> (r: a{ab_dom_po.po r l}) -> a;
  assign: string -> a -> a;
  aeq : a -> a -> bool;
  isBottom : a -> bool;
  // representableType: Type;
  // enc_RepresentableType: a -> representableType;
  // dec_RepresentableType: representableType -> a;
}

let mkAbstractDomain #a [| hasPartialOrder a |] union inter bottom top widen narrow assign aeq isBottom //rep eRep dRep
    : hasAbstractDomain a
    = {
        ab_dom_po = solve
      ; union = union
      ; inter = inter
      ; bottom = bottom
      ; top = top
      ; widen = widen
      ; narrow = narrow
      ; assign = assign
      ; aeq = aeq
      ; isBottom = isBottom
      // ; representableType = rep
      // ; enc_RepresentableType = eRep
      // ; dec_RepresentableType = dRep
    }

class hasAbstractOperators a = {
    abstract_domain:  hasAbstractDomain a
  ; default_value:    hasDefaultValue a
  ; a_op_unary_minus: a -> a
  ; a_op_plus:        a -> a -> a
  ; a_op_minus:       a -> a -> a
  ; a_op_times:       a -> a -> a
  ; a_op_div:         a -> a -> a
}
let mkAbstractOperators #a [| hasAbstractDomain a |] [| hasDefaultValue a |]
  a_op_unary_minus a_op_plus a_op_minus a_op_times a_op_div
  : hasAbstractOperators a
  = {
    abstract_domain  = solve
  ; default_value    = solve
  ; a_op_unary_minus = a_op_unary_minus
  ; a_op_plus        = a_op_plus
  ; a_op_minus       = a_op_minus
  ; a_op_times       = a_op_times
  ; a_op_div         = a_op_div
  }

// let areAbstractOperatorsWellFounded #c #a [| hasAbstractOperators a |] [| hasGaloisConnection c a |]
//   = (forall (x y: a) . gamma (a_op_plus x y) == gamma ())
//   /\ 


(* TODO/idea: Use meta-F* to generate those function *)
let backward_aop_le0         #a [| hasAbstractOperators a |] [| hasAbstractDomain a |] (x r  :a) (lessThanZero:a)
    = x `inter` lessThanZero
let backward_aop_unary_minus #a [| hasAbstractOperators a |] [| hasAbstractDomain a |] (x r  :a)
    = x `inter` (a_op_unary_minus r)
let backward_aop_plus        #a [| hasAbstractOperators a |] [| hasAbstractDomain a |] (x y r:a)
    = (x `inter` (r `a_op_minus` y), y `inter` (r `a_op_minus` x)) 
let backward_aop_minus       #a [| hasAbstractOperators a |] [| hasAbstractDomain a |] (x y r:a)
    = (x `inter` (r `a_op_plus` y), y `inter` (x `a_op_minus` r)) 
let backward_aop_mul #a [| hasAbstractOperators a |] [| hasAbstractDomain a |] (x y r:a)
     = (x `inter` (r `a_op_div` y), y `inter` (r `a_op_div` x))

open ZeroOrLess

let backward_aop_div #a [| hasZeroOrLess a |] [| hasAbstractOperators a |] [| hasAbstractDomain a |] (x y r:a) =
    let s = r `a_op_plus` aroundZero
    in
     (x `inter` (s `a_op_times` y), y `inter` ((x `a_op_div` s) `union` zeroOnly))

//let backward_aop_lt #a [| hasAbstractOperators a |] = 
