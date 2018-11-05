module ExtInt

type extInt = | Infty : extInt
              | SomeInt : int -> extInt

let eq (a:extInt) (b:extInt) = match a with
  | Infty -> (match b with
	    | Infty -> true
	    | _     -> false)
  | SomeInt a -> (match b with
		| Infty -> false 
		| SomeInt v -> a = v)

let lt (a:extInt) (b:extInt) = match a with
  | Infty -> false
  | SomeInt v -> (match b with
		| Infty -> true
		| SomeInt w -> v < w)

let le a b = (eq a b) || (lt a b)
let ge a b = not (lt a b)
let gt a b = (ge a b) && (not (eq a b))

let min a b = if le a b then a else b
let max a b = if le a b then b else a

