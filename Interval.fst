module Interval

open ExtInt

type interval = | EmptyInterval : interval
		| SomeInterval  : (l:extInt) -> (r:extInt{l `lt` r}) -> interval

let mkExtInterval (l:extInt) (r:extInt{l `lt` r}) = SomeInterval l r
let mkInterval (l:int) (r:int{l < r}) = SomeInterval (SomeInt l) (SomeInt r)

let union (a b:interval) = match a with
  | EmptyInterval -> b
  | SomeInterval l1 r1 -> match b with
		 | EmptyInterval -> a
		 | SomeInterval l2 r2 -> SomeInterval (min l1 l2) (max r1 r2) 

let inter (a b:interval) = match a with
  | SomeInterval l1 r1 -> 
        (match b with
	| SomeInterval l2 r2 -> let l3 = max l1 l2 in
	 		       let r3 = min r1 r2 in
				   if l3 `ge` r3 then EmptyInterval
						 else SomeInterval l3 r3
	| _ -> b) // empty
  | _ -> a // if empty

let includes (a b:interval) = match a with
  | EmptyInterval -> true
  | SomeInterval l1 r1 -> match b with
    | EmptyInterval -> false
    | SomeInterval l2 r2 -> (l1 `ge` l2) && (r1 `le` r2)

let gamma (i: interval) = match i with
  | EmptyInterval -> fun _ -> False
  | SomeInterval l r -> fun v' -> true == (let v = SomeInt v' in (v `ge` l) || (v `le` r))
  
