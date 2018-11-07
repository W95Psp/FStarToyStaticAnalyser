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

(*
  Here are some testṡ.
  Variables `a`, `b`, `c`, `d`, `i`, `tmp` are strings and are declared in ToyLanguageInterpreter module

  NOTICE: I use `let _ = assert (something == magic()) by (compute (); qed ())` to ask F* to normalize as much as it can a term.
          `magic ()` fit any type.
          Therfore this assertion always fail, but F* opens a `goals` buffer where we can observe the normalized term.
          One can also use `C-C C-S C-E` command in emacs, but it looks like it has some kind of timeout.
*)

let state0 : enumerableMap interval = 
  em_set (
    state_to_em (emptyState ())
  ) "a" (mkInterval 12 23)
  
(* helper function that run a static analysis using defined state0 *)
let guessInvariants prog = emHasToString.toString (static_analysis_instr state0 prog)

(* simple program summing two numbers *)
let prog0 = (
  (a =. (v 23)) >>
  (b =. (v 12)) >>
  (a =. (!! a) +. (!! b))
  )

// let _ = assert (guessInvariants prog0 == "") by (compute (); qed ())
// -> gives "{b = [12 ; 12], a = [35 ; 35]}"

(* simple program with a while *)
let prog1 = (
  (a =. (v 0)) >>
  (b =. (v 0)) >>
  (while ((!! a) <=. (v 10)) Do (
    (a =. (!! a) +. (v 1)) >>
    (b =. (!! b) +. (!! a))
  ) End)
)

// let _ = assert (guessInvariants prog1 == "") by (compute (); qed ())
// -> gives "{b = [0 ; +inf], a = [0 ; 11]}" (after a while, like 3 minutes!)

(* simple program incremening a value till a upper bound with a while *)
let prog2 = (
  (while ((!! a) <=. (v 40)) Do (
    (a =. (!! a) +. (v 5))
  ) End)
)

// let _ = assert (guessInvariants prog2 == "") by (compute (); qed ())
// -> gives "{a = [12 ; 45]}"


(* max-th number of fibonnacci *)
let prog3 (max:int) =
  (a =. (v 1)) >>
  (b =. (v 1)) >>
  (i =. (v 0)) >>
  (while (!! i <=. (v max)) Do (
    (tmp =. (!! a)) >>
    (a =. (!! b)) >>
    (b =. (!! tmp) +. (!! b)) >>
    (i =. (!! i) +. (v 1))
  ) End)

// let _ = assert (guessInvariants prog3) by (compute (); qed ())
// take too long (I need to export to ML to actually compute it)

(*
  **This is intended for ML extraction, but the extraction doesn't work for me**
*)
let main = 
  //let i = FStar.IO.input_int () in
  FStar.IO.print_string (guessInvariants (prog3 2))
