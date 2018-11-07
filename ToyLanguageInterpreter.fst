module ToyLanguageInterpreter

open ToyLanguageDef
open DefaultValue

open FStar.Mul
open FStar.Tactics.Typeclasses

let a = "a"
let b = "b"
let c = "c"
let d = "d"
let i = "i"
let tmp = "tmp"

let fib (max:int) =
  (a =. (v 1)) >>
  (b =. (v 1)) >>
  (i =. (v 0)) >>
  (while (!! i <=. (LAExpLitt max)) Do (
    (tmp =. (!! a)) >>
    (a =. (!! b)) >>
    (b =. (!! tmp) +. (!! b)) >>
    (i =. (!! i) +. (v 1))
  ) End)


type state (a:Type) = string -> a

let emptyState #a [| hasDefaultValue a |] () : state a =
  fun _ -> def

val norm_lAExp : state int -> lAExp -> int
let rec norm_lAExp state exp =
  let fA a b g = g (norm_lAExp state a) (norm_lAExp state b) in
  match exp with 
  | LAExpLitt v -> v
  | LAExpMinus a b -> fA a b ( fun x y -> x - y )
  | LAExpMult a b -> fA a b  ( * )
  | LAExpPlus a b -> fA a b  ( + )
  | LAExpVar v -> state v

val norm_lBExp : state int -> lBExp -> bool
let rec norm_lBExp state exp =
  let fA a b g = g (norm_lAExp state a) (norm_lAExp state b) in
  let fB a b g = g (norm_lBExp state a) (norm_lBExp state b) in
  match exp with
  | LBExpLitt v -> v
  | LBExpEq a b -> fA a b ( fun a b -> a = b )
  | LBExpLe a b -> fA a b (<=)
  | LBExpAnd a b-> fB a b (&&)
  | LBExpOr a b -> fB a b ( || )
  | LBExpNot a -> norm_lBExp state a

class run_c a b = {
  run : state int -> a -> b
}
instance _ : run_c lAExp int = { run = norm_lAExp }
instance _ : run_c lBExp bool = { run = norm_lBExp }

val norm_lInstr : state int -> lInstr -> (fuel:nat) -> Tot (state int) (decreases fuel)
let rec norm_lInstr state instr n = if n = 0 then state else
  let f = norm_lInstr in
  match instr with
  | LInstrAssign name v -> (fun q -> if q = name then run state v else state q)
  | LInstrIf cond b1 b2 -> norm_lInstr state (if run state cond then b1 else b2) (n - 1)
  | LInstrSkip          -> state
  | LInstrSeq a b       -> f (f state a (n - 1)) b (n - 1)
  | LInstrWhile cond b  -> if run state cond then
				f state (b >> (while cond Do b End)) (n - 1)
			  else  state

instance _ : run_c lInstr (state int) = { run = fun s a -> norm_lInstr s a 100 }

val execFib : int -> state int
let execFib n = (run (emptyState ()) (fib n))

let xx n = execFib n "a"

let test = norm_lBExp (emptyState ()) (LBExpLitt true)


let xxx = run (emptyState ()) (v 2 +. v 3)

// let main = 
//   let i = FStar.IO.input_int () in
//   FStar.IO.print_string (string_of_int (xx i))