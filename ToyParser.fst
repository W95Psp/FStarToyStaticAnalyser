module ToyParser

open FStar.String
open FStar.Char
module L = FStar.List.Tot.Base
open ToyLanguageDef

open ParserCombinators

open ToString


private
let uncurry f x = let (l,r) = x in f l r
private
let uncurry3 f x = let ((a,b),c) = x in f a b c

let aexp_parser: parser lAExp =
  let rec no_rec (): parser lAExp = fp LAExpLitt match_nat <|> fp LAExpVar match_word
                   <|> (match_keyword "(" <*>> (admitP (() << ()); delayMe h') <<*> match_keyword ")")
  and h' (): parser lAExp = admitP (() << ()); let h = delayMe h' in
         no_rec () <|> fp (uncurry LAExpPlus)  (no_rec () <<*> opc '+' <*> h)
                   <|> fp (uncurry LAExpMinus) (no_rec () <<*> opc '-' <*> h)
                   <|> fp (uncurry LAExpMult)  (no_rec () <<*> opc '*' <*> h)
                   <|> fp (uncurry LAExpDiv)  (no_rec () <<*> opc '/' <*> h)
  in wrapspace (h' ())

let bexp_parser: parser lBExp =
  let rec no_rec (): parser lBExp = fp LBExpLitt match_boolean_litterate
           <|> fp (uncurry LBExpEq) (aexp_parser <<*> match_string "==" () <*> aexp_parser)
           <|> fp (uncurry LBExpLe) (aexp_parser <<*> match_string "<=" () <*> aexp_parser)
           <|> fp LBExpNot (match_char () '~' <*>> (admitP (() << ()); delayMe no_rec))
           <|> (match_keyword "(" <*>> delayMe h' <<*> match_keyword ")")
  and h' (): parser lBExp = admitP (() << ()); let h = delayMe h' in
    no_rec () <|> fp (uncurry LBExpAnd) (no_rec () <<*> match_string "&&" () <*> h)
              <|> fp (uncurry LBExpOr)  (no_rec () <<*> match_string "||" () <*> h)
  in wrapspace (h' ())


private
type lFakeInstr =
  | LFakeInstrAssign : string -> lInstrAssignable -> lFakeInstr
  | LFakeInstrSkip   : lFakeInstr
  | LFakeInstrSeq    : lFakeInstr -> lFakeInstr -> lFakeInstr
  | LFakeInstrIf     : lBExp -> lFakeInstr -> lFakeInstr -> lFakeInstr
  | LFakeInstrWhile  : lBExp -> lFakeInstr -> lFakeInstr
  | LFakeInstrFunDef : funFakeDef -> lFakeInstr
and funFakeDef = | FunFakeDef : string -> list string -> lFakeInstr -> funFakeDef



instance pr_ts #a [| hasToString a |] : hasToString (parserResult a) = { 
   toString = fun v -> match v with
    | ParserRes pos somevalue -> join "" ["{pos:"; string_of_int pos ; "} "; toString somevalue]
    | NoRes -> "NoRes"
}

private
let rec lFakeInstrIsWF prog toplevel = match prog with 
  | LFakeInstrSeq a b -> lFakeInstrIsWF a toplevel && lFakeInstrIsWF b toplevel 
  | LFakeInstrIf  _ a b -> lFakeInstrIsWF a false && lFakeInstrIsWF b false 
  | LFakeInstrWhile _ a -> lFakeInstrIsWF a false
  | LFakeInstrFunDef (FunFakeDef _ _ a) -> if toplevel then lFakeInstrIsWF a false else false 
  | _ -> true
private
type lFakeInstrWF = r:lFakeInstr {lFakeInstrIsWF r true}

private
let hAssignCall var fName args = LFakeInstrAssign var (AssignCall fName args)
private
let hAssignExp var exp = LFakeInstrAssign var (AssignLAExp exp) 

private
let lFakeInstr_parser: parser (r:lFakeInstr {lFakeInstrIsWF r true}) =
   let z #a (arg:parser a) = arg <<*> match_comments in
   let rec no_rec (tl:bool): parser (r:lFakeInstr {lFakeInstrIsWF r tl}) = admitP (() << ()); z (
           fp (uncurry hAssignExp) (match_word <<*> match_keyword "=" <*> aexp_parser)
       <|> fp (uncurry3 hAssignCall) (match_word <<*> match_keyword "="
              <*> match_word <*> match_list "(" ")" aexp_parser)
       <|> match_string "SKIP" LFakeInstrSkip
       <|> fp (uncurry3 LFakeInstrIf) (
                  ((match_keywords ["if"; "("] <*>> bexp_parser) <<*> match_keywords [")"; "{"])
              <*> ((delayMe (h' false)) <<*> match_keywords ["}";"else";"{"])
              <*> ((delayMe (h' false)) <<*> match_keyword "}")
           )
       <|> fp (fun ((str,args),body) -> LFakeInstrFunDef (FunFakeDef str args body)) (
                  (match_keyword "function" <*>> match_word <*> 
                    (match_list "(" ")" match_word)
                    <<*> match_keyword "{")
              <*> (delayMe (h' false) <<*> match_keyword "}")
           )       
       <|> fp (uncurry LFakeInstrWhile) (
                  ((match_keywords ["while";"("] <*>> bexp_parser) <<*> match_keywords [")";"{"])
              <*> ((delayMe (h' false)) <<*> match_keyword "}")
           ))
   and h' (tl:bool) (): parser (r:lFakeInstr {lFakeInstrIsWF r tl}) = admitP (() << ()); let h = delayMe (h' tl) in
     z (
       no_rec tl <|> fp (uncurry LFakeInstrSeq) (no_rec tl <<*> match_keyword ";" <*> (match_comments <*>> h))
                 <|> (no_rec tl <<*> match_keyword ";")
     )
   in wrapspace (h' true ())

private
let wfFakeConv (r:lFakeInstr {lFakeInstrIsWF r true}): (list funDef * lInstr) =
  let rec h (tl:bool) (r:lFakeInstr {lFakeInstrIsWF r tl})
      : Tot (list funDef * lInstr) (decreases r)
= (match r with
  | LFakeInstrAssign n v -> ([], LInstrAssign n v)
  | LFakeInstrSkip -> ([], LInstrSkip)
  | LFakeInstrSeq   a b -> let (la, a) = h tl a in
                          let (lb, b) = h tl b in
                          (List.append la lb, LInstrSeq a b)
  | LFakeInstrIf  c a b -> let (la, a) = h false a in
                          let (lb, b) = h false b in
                          (List.append la lb, LInstrIf c a b)
  | LFakeInstrWhile c a -> let (la, a) = h false a in
                          (la, LInstrWhile c a)
  | LFakeInstrFunDef (FunFakeDef name args body) -> ([FunDef name args (let (_,b) = h false body in b)], LInstrSkip)
  ) in h true r
  
let fullProg_parser: parser fullProg =
  fp (fun x -> let (a, b) = wfFakeConv x in FullProg a b) lFakeInstr_parser


let parse_toy_language src = match (fullProg_parser <<*> match_eof) src 0 with
  | ParserRes _ res -> Some res
  | NoRes -> None

