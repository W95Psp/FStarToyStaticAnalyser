module Main

open FStar.FunctionalExtensionality
open FStar.GSet
module CS = CSet
open Interval
open FStar.Tactics
open FStar.Tactics.Typeclasses
open ExtInt
module Mul = FStar.Mul

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
open Congruence
open Interval
open CartProdAbs

module Parser = ToyParser

module OS = FStar.OrdSet

open MyIO

(*
  Here are some testṡ.
  Variables `a`, `b`, `c`, `d`, `i`, `tmp` are strings and are declared in ToyLanguageInterpreter module

  NOTICE: I use `let _ = assert (something == magic()) by (compute (); qed ())` to ask F* to normalize as much as it can a term.
          `magic ()` fit any type.
          Therfore this assertion always fail, but F* opens a `goals` buffer where we can observe the normalized term.
          One can also use `C-C C-S C-E` command in emacs, but it looks like it has some kind of timeout.
*)

type dom = interval * congruence 

let domDV: hasDefaultValue dom = tupAbsDomHasDefaultValue

let state0 : enumerableMap dom = state_to_em (emptyState #dom #domDV ())

(*let state0 : enumerableMap interval = 
  //em_set (
    state_to_em (emptyState ())
  //) "a" (mkInterval 12 23)
  *)
(* helper function that run a static analysis using defined state0 *)
let domAD = tupAbsDomHasAbstractDomain #interval #congruence
let domAO = tupAbsDomHasAbstractOperators #interval #congruence #domDV #solve #solve #domAD
let domGC = tupAbsDomHasGaloisConnection #int #interval #congruence 

let domToStr = emHasToString #dom #tupAbsDomHasToString

let static_analysis_fullProg' = static_analysis_fullProg
    #dom
    #tupAbsDomHasToString
    #domAO
    #domAD
    #domGC
    #(tupAbsDomHasZeroOrLess #interval #congruence)
    

let guessInvariants prog = (* domToStr.toString *)  (static_analysis_fullProg' state0 prog)


open FStar.String
open FStar.Char
module U32 = FStar.UInt32

//let x = u32_of_char 'a'
open ToyParser

// let getStr progStr i = match parse_toy_language progStr with
//                        | Just prog -> guessInvariants prog
//                        | Nothing   -> "Error parsing input"

//let getdir unit = mi_readdir "../prog-

open FStar.All

let mi_get_file_contents (path: string): ML string =
  let r = mi_open_read_file path in
  let rec h unit: ML string = match (try Some (mi_read_line r) with | _ -> None) with // we parse *one* line
          | Some l  -> let next = h () in
                      l `strcat` "\n" `strcat` next
          | None -> ""    
  in
  let contents = h () in
  mi_close_read_file r; contents

let rec _last (l: list string) = match l with
  | [] -> ""
  | [x] -> x
  | hd::tl -> _last tl

let get_ext name = let chunks = split ['.'] name in
                   if FStar.List.Tot.Base.length chunks > 1 then _last chunks
                                                            else ""
let filter_ext ext name = get_ext name = ext

//let ff (): ML (list unit) = []

let main_h (): ML (list unit) =
  let basedir = "./prog-example/" in
  let app = strcat basedir in
  let l = mi_readdir basedir in
  mi_print_string (anyListHasToString.toString l);
  let l = List.filter (fun p -> mi_file_exists (app p)) l in
  let l = List.filter (fun p -> get_ext p = "c") l in
  mi_print_string (anyListHasToString.toString (FStar.List.Tot.Base.map get_ext l));
  let f (x: string): ML unit = 
                  let _ = mi_debug_print_string ("\n# Process file " ^ x) in
                  let content = mi_get_file_contents (app x) in
                  let (ast, pp, invariants) = (match admit(); parse_toy_language content with
                       | Inl prog -> let invs = admit(); guessInvariants prog in
                                     ( (admit (); print_AST_fullProg prog)
                                     , (admit (); toString prog)
                                     , (match invs with
                                       | Inl x -> domToStr.toString x
                                       | Inr x -> x
                                       )
                                     )
                       | Inr m -> let _ = mi_print_string m in (m,m,m)
                       ) in
                  let file_result = mi_open_write_file (app x `strcat` ".result") in
                  mi_write_string file_result invariants;
                  mi_close_write_file file_result;
                  let file_pp     = mi_open_write_file (app x `strcat` ".pp") in
                  mi_write_string file_pp     pp;
                  mi_close_write_file file_pp;
                  let file_ast    = mi_open_write_file (app x `strcat` ".ast") in
                  mi_write_string file_ast    ast;
                  mi_close_write_file file_ast;
                  () in
  List.map f l

let main = main_h ()

