module ExtInt

type extInt = | Infty : bool -> extInt
              | SomeInt : int -> extInt
let plusInfty = Infty true
let minusInfty = Infty false

let eq (a:extInt) (b:extInt) = match a with
  | Infty a_sign -> (match b with
	    | Infty b_sign -> a_sign = b_sign
	    | _     -> false)
  | SomeInt a -> (match b with
		| Infty _ -> false 
		| SomeInt v -> a = v)

let example_eq1 = assert (minusInfty `eq` minusInfty)
let example_eq2 = assert (~(minusInfty `eq` plusInfty))
let example_eq3 = assert (SomeInt 3 `eq` SomeInt 3)

let lt (a:extInt) (b:extInt) = match a with
  | Infty _ -> (match b with
              | Infty _ -> a = minusInfty && b = plusInfty
              | _ -> false)
  | SomeInt v -> (match b with
		| Infty _ -> b = plusInfty 
		| SomeInt w -> v < w)

let le a b = (eq a b) || (lt a b)
let ge a b = not (lt a b)
let gt a b = (ge a b) && (not (eq a b))

let min a b = if le a b then a else b
let max a b = if le a b then b else a

//let _ = assume (Infty)
