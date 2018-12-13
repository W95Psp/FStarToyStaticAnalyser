(*
@summary: a -> string interface
*)
module ToString

open FStar.Tactics.Typeclasses
open FStar.String
open FStar.List.Tot.Base

class hasToString t = {
  toString: t -> string
}

let join sep l = fold_right
					(fun (a, i) b -> (if i then sep else "") `strcat` (a `strcat` b))
					(mapi (fun i x -> (x, i > 0)) l)
					""


instance tupleHasToString #t1 #t2 [| hasToString t1 |] [| hasToString t2 |] = {
	toString = fun (a,b) -> join "" ["("; toString a; ", "; toString b; ")"]
}
private
let nat_to_int (i:nat): int = i


instance stringHasToString : hasToString string = {toString = fun x -> x}
instance charHasToString   : hasToString char = {toString = fun ch -> String.make 1 ch}
instance natHasToString    : hasToString nat = {toString = fun ch -> string_of_int (nat_to_int ch)}
instance intHasToString    : hasToString int = {toString = string_of_int}
instance boolHasToString   : hasToString bool = {toString = fun v -> if v then "true" else "false"}

instance anyListHasToString #a [| hasToString a |] : hasToString (list a) = {toString = fun x -> "[" ^ join ", " (map toString x) ^ "]"}

let (^-) #t0 #t1 [| hasToString t0 |] [| hasToString t1 |] (s0: t0) (s1: t1) = toString s0 ^ toString s1

//instance anyRefinedStringHasToString #pred : hasToString (s:string{pred s}) = {toString = id }
