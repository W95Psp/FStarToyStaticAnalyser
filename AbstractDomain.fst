(*
@summary: Specify what is an abstract domain and what should be abstract operators. Also derive generic backward operators.
*)
module AbstractDomain

open DefaultValue
open FStar.Tactics.Typeclasses

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


(* TODO/idea: Use meta-F* to generate those function *)
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
