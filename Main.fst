module Main

open FStar.FunctionalExtensionality
open FStar.GSet
module CS = CSet
open Interval
open FStar.Tactics
open FStar.Tactics.Typeclasses
open ExtInt
open FStar.Mul

open PartialOrder
open GaloisConnection
open DefaultValue
open ToyLanguageDef
open ToyLanguageInterpreter
open ToString
open EnumerableMap
open AbstractDomain
open ZeroOrLess

open StaticAnalyser

module OS = FStar.OrdSet

let sad = let v = v 3 in (v <=. v) &&. (!. (v ==. v))
//let _ = assert ((bexp_count_not sad, sad) == magic ()) by (compute (); qed ())

let myProg = (
  (a =. (v 23)) >>
  (a =. (!! a) +. (!! b))
  )
let myState : enumerableMap interval = 
  em_set (
    state_to_em (emptyState ())
  ) "a" (SomeInterval (SomeInt 23) (SomeInt 23))


let fib' (max:int) =
  (a =. (v 1)) >>
  (b =. (v 1)) >>
  (i =. (v 0)) >>
  (while (!! i <=. (v max)) Do (
    (tmp =. (!! a)) >>
    (a =. (!! b)) >>
    (b =. (!! tmp) +. (!! b)) >>
    (i =. (!! i) +. (v 1))
  ) End)

let prog2 = (
  (a =. (v 0)) >>
  (b =. (v 0)) >>
  (while ((!! a) <=. (v 10)) Do (
    (a =. (!! a) +. (v 1)) >>
    (b =. (!! b) +. (!! a))
  ) End)
)
let prog3 = (a =. (v 28))

let hey  = static_analysis_instr myState prog2
let hey2 = static_analysis_instr myState prog3
let hey3 = analyse_bexp myState ((!! a) <=. (v 4))
let hey4 = static_analysis_instr myState (fib 0)


//let _ = assert (em_get hey3 "a"  == magic ()) by (compute(); qed ())
//let _ = assert (em_equal aeq (hey) (hey2)) by (compute (); qed ())
//let _ = assert (emHasToString.toString hey == magic()) by (compute (); qed ())



let main = 
  let i = FStar.IO.input_int () in
  FStar.IO.print_string (emHasToString.toString hey4)


(* 
let test0 = static_analysis_aexp (listToState [
  ("hey", SomeInterval (SomeInt 2) (SomeInt 4))
]) (v 10 *. !! "hey") *)
 
//let _ = assert (test0 == magic ()) by (compute ();qed ())

//let verif_test0 = assert (test0 == SomeInterval (SomeInt 4) (SomeInt 4))

//let hey =  static_analysis_aexp (emptyState ()) 
//hey
