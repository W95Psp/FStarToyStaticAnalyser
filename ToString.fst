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
private
let example = join "," ["A";"B";"C";"D"]
