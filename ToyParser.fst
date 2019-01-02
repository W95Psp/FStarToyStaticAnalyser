module ToyParser

open FStar.String
open FStar.Char
module L = FStar.List.Tot.Base
open ToyLanguageDef

open StarCombinator

open ToString

private
let uncurry f x = let (l,r) = x in f l r
private
let uncurry3 f x = let ((a,b),c) = x in f a b c

let op_apply = (fun (l, mb) -> match mb with
          | None -> l
          | Some (op, r) -> op l r
          )


let aexp_parser: parser lAExp =
  let rec no_rec (): parser lAExp =
          between_kwd "(" ")" (admitP (()<<()); delayMe h')
      <|> fp LAExpLitt number
      <|> fp LAExpVar word
      
  and h' (): parser lAExp = admitP (() << ()); let h = delayMe h' in
      op_apply @<< (
            no_rec ()
          <*> maybe ((
                (ptry (LAExpPlus *<< operator "+")) <|> (ptry (LAExpMinus *<< operator "-"))
            <|> (ptry (LAExpMult *<< operator "*")) <|> (ptry (LAExpDiv *<< operator "/"))
          ) <*> h)
        )      
  in wrapspace (h' ())

let bexp_parser: parser lBExp =
  let rec no_rec (): parser lBExp = admitP (() << ()); let nr = delayMe no_rec in
          (LBExpNot @<< (operator "~" <*>> nr))
      <|> ptry (LBExpLitt true  *<< keyword "true" <|> LBExpLitt false *<< keyword "false")
      <|> ptry (between (operator "(") (operator ")") (delayMe h'))
      <|> ptry (fp (fun ((l, op), r) -> op l r)
        (aexp_parser <*> (
           (LBExpEq *<< operator "==") <|> (LBExpLe *<< operator "<=")
        ) <*> aexp_parser))
  and h' (): parser lBExp =   admitP (() << ()); let h = delayMe h' in
          op_apply @<<
          (no_rec () <*> maybe (
                ((LBExpAnd *<< operator "&&") <|> (LBExpOr *<< operator "||"))
            <*> h
          ))
  in wrapspace (h' ())
  
type lFakeInstr =
  | LFakeInstrAssign : string -> lInstrAssignable -> lFakeInstr
  | LFakeInstrSkip   : lFakeInstr
  | LFakeInstrSeq    : lFakeInstr -> lFakeInstr -> lFakeInstr
  | LFakeInstrIf     : lBExp -> lFakeInstr -> lFakeInstr -> lFakeInstr
  | LFakeInstrWhile  : lBExp -> lFakeInstr -> lFakeInstr
  | LFakeInstrFunDef : funFakeDef -> lFakeInstr
and funFakeDef = | FunFakeDef : string -> list string -> lFakeInstr -> funFakeDef

let rec lFakeInstrIsWF prog toplevel = match prog with 
  | LFakeInstrSeq a b -> lFakeInstrIsWF a toplevel && lFakeInstrIsWF b toplevel 
  | LFakeInstrIf  _ a b -> lFakeInstrIsWF a false && lFakeInstrIsWF b false 
  | LFakeInstrWhile _ a -> lFakeInstrIsWF a false
  | LFakeInstrFunDef (FunFakeDef _ _ a) -> if toplevel then lFakeInstrIsWF a false else false 
  | _ -> true

type lFakeInstrWF = r:lFakeInstr {lFakeInstrIsWF r true}

let hAssign (var, eith) = match eith with
    | Inl (fName, args) -> LFakeInstrAssign var (AssignCall fName args)
    | Inr exp -> LFakeInstrAssign var (AssignLAExp exp) 

let match_comment: parser string = spaces <*>> keyword "//" <*>> string_satisfy (fun x -> x <> '\n')
let match_comments: parser (list string) = fp (fun x -> match x with | Some x -> x | None -> []) (maybe (many match_comment))

let hIf ((cond, body0), body1) = LFakeInstrIf cond body0 body1
let hWhile (cond, body) = LFakeInstrWhile cond body
let hFunction ((str,args),body) = LFakeInstrFunDef (FunFakeDef str args body)
 
let lFakeInstr_parser: parser (r:lFakeInstr {lFakeInstrIsWF r true}) =
   let z #a (arg:parser a) = arg  in
   let rec no_rec (tl:bool): parser (r:lFakeInstr {lFakeInstrIsWF r tl}) =
       admitP (() << ()); let nr = delayMe (h' false) in
   z (
       ( hIf @<<
         (((keyword "if" <*> operator "(") <*>> bexp_parser <<*> (operator ")" <*> operator "{")) <*>
           (nr <<*> (operator "}" <*> keyword "else" <*> operator "{")) <*>
           (nr <<*> operator "}"))
       )
   <|> ( hWhile @<< (
                ((keyword "while" <*> operator "(") <*>> bexp_parser <<*> (operator ")" <*> operator "{"))
            <*> (nr <<*> operator "}")
            )
       )
   <|> ( hFunction @<< (
                   (operator "function" <*>> word)
               <*> (match_list "(" ")" (operator ",") word <<*> operator "{")
               <*> (nr <<*> operator "}")
               )
       )
   <|> (LFakeInstrSkip *<< operator "SKIP")
   <|> (hAssign @<< (word <<*> operator "=" <*> (
             ptry (word <*> match_list "(" ")" (operator ",") aexp_parser)
         </> aexp_parser
       )))
   )
   and h' (tl:bool) (): parser (r:lFakeInstr {lFakeInstrIsWF r tl}) = admitP (() << ()); let h = delayMe (h' tl) in z (
       (fun (s1, s2) -> match s2 with
                     | None    -> s1
                     | Some s2 -> LFakeInstrSeq s1 s2
       ) @<< (no_rec tl <*> maybe (operator ";" <*>> h))//(match_comments <*>> h)))
     )
   in wrapspace (h' true ())

// instance pr_ts #a [| hasToString a |] : hasToString (parserResult a) = { 
//    toString = fun v -> match v with
//     | ParserRes pos somevalue -> join "" ["{pos:"; string_of_int pos ; "} "; toString somevalue]
//     | NoRes _ _ -> "NoRes"
// }

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


let parse_toy_language: string -> (either fullProg string) = make (fullProg_parser <<*> eof)

