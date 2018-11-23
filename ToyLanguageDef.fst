module ToyLanguageDef
open FStar.Tactics.Typeclasses
open ToString
module L = FStar.List.Tot.Base

type lAExp =
  | LAExpLitt : int -> lAExp
  | LAExpVar  : string -> lAExp
  | LAExpPlus : lAExp -> lAExp -> lAExp 
  | LAExpMinus: lAExp -> lAExp -> lAExp 
  | LAExpMult : lAExp -> lAExp -> lAExp


let ( +. ) = LAExpPlus
let ( -. ) = LAExpMinus
let ( *. ) = LAExpMult

type lBExp =
  | LBExpLitt: bool -> lBExp
  | LBExpNot : lBExp -> lBExp
  | LBExpAnd : lBExp -> lBExp -> lBExp
  | LBExpOr  : lBExp -> lBExp -> lBExp
  | LBExpEq  : lAExp -> lAExp -> lBExp
  | LBExpLe  : lAExp -> lAExp -> lBExp

let ( !.  ) = LBExpNot
let ( &&. ) = LBExpAnd
let ( ||. ) = LBExpOr
let ( ==. ) = LBExpEq
let ( <=. ) = LBExpLe

(* Class for lifting bools and ints into our language *)
class litteral_lift a b = { v : a -> b }
instance _ : litteral_lift int    lAExp = { v = LAExpLitt }
instance _ : litteral_lift bool lBExp = { v = LBExpLitt }

let ( !! ) = LAExpVar

type lInstr =
  | LInstrAssign : string -> lAExp -> lInstr
  | LInstrSkip   : lInstr
  | LInstrSeq    : lInstr -> lInstr -> lInstr
  | LInstrIf     : lBExp -> lInstr -> lInstr -> lInstr
  | LInstrWhile  : lBExp -> lInstr -> lInstr

let ( =. ) = LInstrAssign
let Skip = LInstrSkip
let ( >> ) = LInstrSeq 

type thenTag = | Then
type elseTag = | Else
type endTag  = | End
type doTag   = | Do

let iF (cond:lBExp) (_:thenTag) (b1:lInstr) (_:elseTag) (b2:lInstr) (_:endTag) : lInstr = LInstrIf cond b1 b2

val while : lBExp -> doTag -> lInstr -> endTag -> lInstr
let while cond _ body _ = LInstrWhile cond body

let rec bexp_count_not (e:lBExp): nat = match e with
  | LBExpNot (LBExpEq _ _) -> 0
  | LBExpNot x -> 1 + bexp_count_not x
  | LBExpAnd x y -> bexp_count_not x + bexp_count_not y
  | LBExpOr x y -> bexp_count_not x + bexp_count_not y
  | _ -> 0


private
let rec ntabs (n:nat): string = if n=0 then "" else strcat "    " (ntabs (n-1))
private
let apptabs (n:nat): string -> string = strcat (ntabs n)
let rec lAExpToString exp = match exp with 
         | LAExpLitt z -> toString z
         | LAExpVar s -> s
         | LAExpPlus  a b -> join " + " (L.map lAExpToString [a;b])
         | LAExpMinus a b -> join " - " (L.map lAExpToString [a;b])
         | LAExpMult  a b -> join " * " (L.map lAExpToString [a;b])
instance lAExpHasToString : hasToString lAExp = { toString = lAExpToString }
let rec lBExpToString exp = match exp with
  | LBExpLitt b -> toString b
  | LBExpNot e -> strcat "~" (lBExpToString e)
  | LBExpAnd a b -> join " && " (L.map lBExpToString [a;b])
  | LBExpOr  a b -> join " || " (L.map lBExpToString [a;b])
  | LBExpEq  a b -> join " == " (L.map toString [a;b])
  | LBExpLe  a b -> join " <= " (L.map toString [a;b])
instance lBExpHasToString : hasToString lBExp = { toString = lBExpToString }
let rec lInstrToString (n:nat) exp: Tot string (decreases exp) = match exp with
  | LInstrAssign name v -> apptabs n (join " = " [name; toString v])
  | LInstrSkip -> apptabs n "SKIP"
  | LInstrSeq a b -> join "; \n" [lInstrToString n a; lInstrToString n b]
  | LInstrIf c a b -> join "" [apptabs n "if ("; toString c; ") {\n"; lInstrToString (n+1) a; "\n" `strcat` apptabs n "} else {\n"; lInstrToString (n+1) b; "\n" `strcat` apptabs n "}"]
  | LInstrWhile c a -> join "" [apptabs n "while ("; toString c; ") {\n"; lInstrToString (n+1) a; "\n" `strcat` apptabs n "}" ]
instance lInstrHasToString : hasToString lInstr = { toString = lInstrToString 0 }
