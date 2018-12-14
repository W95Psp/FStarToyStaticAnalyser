module ToyLanguageDef
open FStar.Tactics.Typeclasses
open ToString

open EnumerableMap

module L = FStar.List.Tot.Base

type lAExp =
  | LAExpLitt : int -> lAExp
  | LAExpVar  : string -> lAExp
  | LAExpPlus : lAExp  -> lAExp -> lAExp 
  | LAExpMinus: lAExp  -> lAExp -> lAExp 
  | LAExpMult : lAExp  -> lAExp -> lAExp
  | LAExpDiv  : lAExp  -> lAExp -> lAExp
  //| LAExpCall : string -> list lAExp -> lAExp 

let ( +. ) = LAExpPlus
let ( -. ) = LAExpMinus
let ( *. ) = LAExpMult
let ( /. ) = LAExpDiv

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

type lInstrAssignable = | AssignLAExp : lAExp -> lInstrAssignable
                        | AssignCall  : string -> list lAExp -> lInstrAssignable

type lInstr =
  | LInstrAssign : string -> lInstrAssignable -> lInstr
  | LInstrSkip   : lInstr
  | LInstrSeq    : lInstr -> lInstr -> lInstr
  | LInstrIf     : lBExp -> lInstr -> lInstr -> lInstr
  | LInstrWhile  : lBExp -> lInstr -> lInstr
//  | LInstrStoCall: string -> string -> list lAExp -> lAExp 
  
type funDef = | FunDef : string -> list string -> lInstr -> funDef

type fullProg = | FullProg : (list funDef) -> lInstr -> fullProg

// let rec getFunDefs prog = match prog with
//   | LInstrSeq    a b -> getFunDefs a @ getFunDefs b
//   | LInstrIf   _ a b -> getFunDefs a @ getFunDefs b
//   | LInstrWhile  _ a -> getFunDefs a
//   | LInstrFun    a b -> getFunDefs a @ getFunDefs b
//   | _ -> []

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
         | LAExpDiv  a b  -> join " / " (L.map lAExpToString [a;b])
         //| LAExpCall name args -> name ^ "(" ^ (join ", " (L.map (admit (); lAExpToString) args)) ^ ")"
         
instance lAExpHasToString : hasToString lAExp = { toString = lAExpToString }
let rec lBExpToString exp = match exp with
  | LBExpLitt b  -> toString b
  | LBExpNot e   -> strcat "~" (lBExpToString e)
  | LBExpAnd a b -> join " && " (L.map lBExpToString [a;b])
  | LBExpOr  a b -> join " || " (L.map lBExpToString [a;b])
  | LBExpEq  a b -> join " == " (L.map toString [a;b])
  | LBExpLe  a b -> join " <= " (L.map toString [a;b])
instance lBExpHasToString : hasToString lBExp = { toString = lBExpToString }
let rec lInstrToString (n:nat) exp: Tot string (decreases exp) = match exp with
  | LInstrAssign name v -> (match v with
    | (AssignLAExp v) -> apptabs n (name ^ " = " ^ toString v)
    | (AssignCall funName args) -> apptabs n (name ^ " = " ^ funName ^ "("
                                  ^ join ", " (L.map toString args) ^ ")")
    )
  | LInstrSkip -> apptabs n "SKIP"
  | LInstrSeq a b -> join "; \n" [lInstrToString n a; lInstrToString n b]
  | LInstrIf c a b -> join "" [apptabs n "if ("; toString c; ") {\n"; lInstrToString (n+1) a; "\n" `strcat` apptabs n "} else {\n"; lInstrToString (n+1) b; "\n" `strcat` apptabs n "}"]
  | LInstrWhile c a -> join "" [apptabs n "while ("; toString c; ") {\n"; lInstrToString (n+1) a; "\n" `strcat` apptabs n "}" ]
instance lInstrHasToString : hasToString lInstr = { toString = lInstrToString 0 }

private
let g t n (a: nat -> string)
  = let t' = t + 1 in ntabs t ^ n ^ " (\n" ^ a t' ^ "\n" ^ ntabs t ^ ")" 
private
let g' t n m (a: nat -> string)
  = let t' = t + 1 in ntabs t ^ n ^ " (" ^ m ^ " ,\n" ^ a t' ^ "\n" ^ ntabs t ^ ")" 
private
let h t n (a: nat -> string) (b: nat -> string)
  = let t' = t + 1 in ntabs t ^ n ^ " (\n" ^ a t' ^ ", \n" ^ b t' ^ "\n" ^ ntabs t ^ ")" 
private
let i t n (a: nat -> string) (b: nat -> string) (c: nat -> string)
  = let t' = t + 1 in ntabs t ^ n ^ " (\n" ^ a t' ^ ", \n" ^ b t' ^ ", \n" ^ c t' ^ "\n" ^ ntabs t ^ ")" 
private
let hh (t:nat) n (l: list (nat -> string))
  = ntabs t ^ n ^ " (\n"
    ^ join ", \n" (L.map (fun (f: nat -> string) -> f (t + 1)) l)
    ^ "\n" ^ ntabs t ^ ")" 

let rec print_AST_lAExp v (t: nat) = match v with
    | LAExpLitt n ->  ntabs t ^ toString n
    | LAExpVar var -> ntabs t ^ "\"" ^ var ^ "\""
    | LAExpPlus a b -> h t "LAExpPlus" (print_AST_lAExp a) (print_AST_lAExp b)
    | LAExpMinus a b -> h t "LAExpMinus" (print_AST_lAExp a) (print_AST_lAExp b)
    | LAExpMult a b -> h t "LAExpMult" (print_AST_lAExp a) (print_AST_lAExp b)
    | LAExpDiv a b -> h t "LAExpDiv" (print_AST_lAExp a) (print_AST_lAExp b)
    //| LAExpCall name string -> "TODO"//h t "LAExpDiv" (print_AST_lAExp a) (print_AST_lAExp b)

let rec print_AST_lBExp v (t: nat) = match v with
  | LBExpLitt n -> toString n
  | LBExpNot e -> g t "LBExpNot" (print_AST_lBExp e)
  | LBExpAnd a b -> h t "LBExpAnd" (print_AST_lBExp a) (print_AST_lBExp b)
  | LBExpOr  a b -> h t "LBExpOr" (print_AST_lBExp a) (print_AST_lBExp b)  
  | LBExpEq  a b -> h t "LBExpEq" (print_AST_lAExp a) (print_AST_lAExp b)  
  | LBExpLe  a b -> h t "LBExpLe" (print_AST_lAExp a) (print_AST_lAExp b)  

let rec print_AST_lInstr' v (t: nat) = match v with  
  | LInstrAssign var value  -> (match value with
    | AssignLAExp value -> g' t "LInstrAssign.Exp" var (print_AST_lAExp value)
    | AssignCall funName args -> hh t ("LInstrAssign.Call["^var^" <- "^funName^"(..)]") (L.map print_AST_lAExp args)
    )
  | LInstrSkip              -> "LInstrSkip"
  | LInstrSeq    a   b      -> 
    let rec collect x = match x with | LInstrSeq a b -> collect a @ collect b
                                     | _ -> [x] in
    hh t "LInstrSeq" (L.map (admit();print_AST_lInstr') (collect v))
  | LInstrIf c btrue bfalse -> h t "LInstrIf" (print_AST_lBExp c) (print_AST_lInstr' btrue) 
  | LInstrWhile  c   body   -> h t "LInstrWhile" (print_AST_lBExp c) (print_AST_lInstr' body)
 
let print_AST_lInstr v = print_AST_lInstr' v 0 


let print_AST_fullProg (FullProg funs prog) = 
  let h = join "\n" in
  h [h (L.map 
    (fun (FunDef name args body) -> "\n\n# Function " ^ name ^ " (" ^ join ", " args ^ "):\n"
      ^ print_AST_lInstr body ^ "\n"
    ) funs)
  ; "\n\n # Main prog:" ^ print_AST_lInstr prog]

private
let rec print_tup_fullProg (FullProg funs prog): string =
  let h = join "\n" in
  h [h (L.map 
    (fun (FunDef name args body) -> "function "
       ^ name ^ " (" ^ join ", " args ^ ") {\n" ^ toString body ^ "\n}"
    ) funs)
  ; toString prog]
  
instance fullProgHasToString : hasToString fullProg 
         = { toString = print_tup_fullProg }

