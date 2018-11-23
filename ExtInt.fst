(*
@summary: integer extended with infinities
*)
module ExtInt

open FStar.Mul
open ToString

(* an extended int is either an int, either some infinite *)
type extInt = | Infty : bool -> extInt
              | SomeInt : int -> extInt
let plusInfty = Infty true
let minusInfty = Infty false
let zero = SomeInt 0

let eq (a:extInt) (b:extInt) = match a with
  | Infty a_sign -> (match b with
	    | Infty b_sign -> a_sign = b_sign
	    | _     -> false)
  | SomeInt a -> (match b with
		| Infty b -> b 
		| SomeInt v -> a = v)

let example_eq1 = assert (minusInfty `eq` minusInfty)
let example_eq2 = assert (~(minusInfty `eq` plusInfty))
let example_eq3 = assert (SomeInt 3 `eq` SomeInt 3)

let lt (a:extInt) (b:extInt) = match a with
  | Infty _ -> (match b with
              | Infty _   -> a = minusInfty && b = plusInfty
              | SomeInt _ -> a = minusInfty)
  | SomeInt v -> (match b with
		| Infty _ -> b = plusInfty 
		| SomeInt w -> v < w)

let le a b : bool = (eq a b) || (lt a b)
let ge a b : bool = not (lt a b)
let gt a b : bool = (ge a b) && (not (eq a b))

let min a b = if lt a b then a else b
let max a b = if lt a b then b else a


let plus (a b:extInt) = match a with
  | Infty _ -> a
  | SomeInt a' -> match b with
                 | Infty _ -> b
                 | SomeInt b' -> SomeInt (a'+b')
let unaryMinus (a:extInt) = match a with
  | Infty sign -> Infty (not sign)
  | SomeInt a' -> SomeInt (- a')
let minus (a b:extInt) = a `plus` unaryMinus b


let rec times (a b:extInt): Tot extInt (decreases (match b with | Infty _ -> 0 | _ -> 1)) = match b with
  | Infty sb -> if a `gt` zero then (Infty sb)
          else if a `lt` zero then (Infty (not sb))
          else                     (SomeInt 0)
  | SomeInt vb -> match a with
                 | Infty _ -> times b a
                 | SomeInt va -> SomeInt (vb * va)
    

let _ = assert (forall (a b:int). a < b ==> (SomeInt a) `lt` (SomeInt b))
let _ = assert (forall (a:int). (SomeInt a) `lt` plusInfty)

let lemma_minmax (a b:extInt) : Lemma (min a b `le` max a b) = ()
let _ = assert (forall (a b:extInt). min a b `le` max a b)

instance _ : hasToString extInt =  { toString = fun i -> match i with
    | SomeInt n -> string_of_int n
    | _ -> if i = plusInfty then "∞" else "-∞"}
