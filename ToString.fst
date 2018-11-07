module ToString

open FStar.Tactics.Typeclasses
open FStar.String

class hasToString t = {
  toString: t -> string
}

let join sep l = List.Tot.Base.fold_right (fun a b -> (if a = "" then sep else "") `strcat` (a `strcat` b)) l ""