module ToyParser

open FStar.String
open FStar.Char
module U32 = FStar.UInt32
module L = FStar.List.Tot.Base
open ToyLanguageDef

module T = FStar.Tactics
open ToString
open MiscStuff
module M = FStar.Mul

let lowerCaseCharList = list_of_string "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
let upperCaseCharList = list_of_string "abcdefghijklmnopqrstuvwxyz"
let digitList = list_of_string "1234567890"
let isSpecialChar = list_of_string "~@#$%^?!+-*<>\\/|&=:"

//type regexpSpecial = 

type regexp a = | RegExpLit : a -> regexp a
                | RegExpClassRange : (list a) -> regexp a
                | RegExpAny : regexp a -> regexp a
                | RegExpOr : regexp a -> regexp a -> regexp a
                | RegExpSeq : regexp a -> regexp a -> regexp a
                | RegExpEmpty : regexp a 

type maybe a = | Nothing : maybe a | Just : a -> maybe a

let op m1 m2 f1 f2 = match m1 with
               | Just m1 -> (match m2 with
                      | Just m2 -> Just (if f2 m1 m2 then f1 m1 else f1 m2)
                      | Nothing -> Just (f1 m1))
               | Nothing -> (match m2 with
                      | Just m2 -> Just (f1 m2)
                      | Nothing -> Nothing)

let id x = x 

// let bind x f = match x with | Nothing -> Nothing | Just v -> f v


// let regexp_parse (#a:eqtype) (lst: list a) (re: regexp a) =
//   let rec h (l acc: list a) (re: regexp a) : Tot (maybe (list a * list a)) (decreases re) = 
//     let cmb left right = op (h l acc left) (h l acc right) id (fun (_,x) (_,y) -> L.length x < L.length y) in
//     match l with
//     | [] -> (match re with
//            | RegExpLit _ -> Nothing
//            | RegExpClassRange _ -> Nothing
//            | RegExpAny _ -> Just (l, acc)
//            | RegExpOr left right -> cmb left right
//            | RegExpSeq e1 e2 -> r1 <-- h l acc e1; h (fst r1) (snd r1) e2 
//            | RegExpEmpty -> Just (l, acc)
//            )
//     | hd::tl -> (match re with
//            | RegExpLit a -> if a = hd then Just (tl, hd::acc) else Nothing
//            | RegExpClassRange range -> if L.mem hd range then Just (tl, hd::acc) else Nothing
//            | RegExpAny re' -> (match h l acc re' with
//                              | Just (l', acc') -> h l' acc' re'
//                              | Nothing -> Just (l, acc)
//                              )
//            | RegExpOr left right -> cmb left right
//            | RegExpSeq e1 e2 -> r1 <-- h l acc e1; h (fst r1) (snd r1) e2
//            | RegExpEmpty -> Just (l, acc)
//            )
//     in
//   h lst [] re

type parserResult a = | ParserRes : nat -> a -> parserResult a | NoRes

type parser a = string -> nat -> parserResult a

let empty #a (symb: a) : parser a = fun _ pos -> ParserRes pos symb
let match_char #a (symb: a) (ch: char) : parser a = fun src pos -> if pos >= FStar.String.length src then NoRes
                                                                else (
                                                                  if get src pos = ch then ParserRes (pos+1) symb
                                                                  else                     NoRes
                                                                )
                                                                
let match_charf (f: char -> bool) : parser char = fun src pos -> if pos >= FStar.String.length src then NoRes
                                                                else (let ch = get src pos in
                                                                  if f ch then  ParserRes (pos+1) ch 
                                                                  else    NoRes
                                                                )

type either a b = | Left : a -> either a b | Right : b -> either a b 

let bind x f = match x with | ParserRes a b -> f (a, b) | _ -> NoRes

let map_pr x f = x <-- x; ParserRes (fst x) (f (snd x))

let fst' #a (x: parserResult a{ParserRes? x}) = match x with | ParserRes a _ -> a

let comb_or #a #b #c (p_a: parser a) (p_b: parser b) (f: (either a b) -> c) : parser c = fun src pos -> 
  let r_a = p_a src pos in
  let r_b = p_b src pos in
  match (r_a, r_b) with
    | (NoRes, NoRes) -> NoRes
    | (value, NoRes) -> map_pr value (f @ Left)
    | (NoRes, value) -> map_pr value (f @ Right)
    | (val0 , val1 ) -> if (fst' val0) > (fst' val1) then
                            map_pr val0 (f @ Left)           
                       else map_pr val1 (f @ Right)

let rec repeat' #a (p_a: parser a) (acc:list a) src pos = 
  match p_a src pos with
    | ParserRes p v -> admitP (p << p); repeat' p_a (L.append acc [v]) src p
    | NoRes -> ParserRes pos acc

let repeat #a #b (p_a: parser a) (f: list a -> b) : parser b = fun src pos -> match repeat' p_a [] src pos with
    | ParserRes p v -> ParserRes p (f v)
    | NoRes -> NoRes

let match_stringf (f: char -> bool) : parser string = repeat (match_charf f) string_of_list

let sequence #a #b #c (p_a: parser a) (p_b: parser b) (f: a -> b -> c) : parser c = fun src pos ->
  r_a <-- p_a src pos;
  r_b <-- p_b src (fst r_a);
  ParserRes (fst r_b) (f (snd r_a) (snd r_b))

let match_string #a (str: string) (symb: a): parser a = fun src pos -> (L.fold_left (fun c char -> sequence c (match_char () char) (fun _ _ -> symb)) (empty symb) (list_of_string str)) src pos

let (<*>) #t1 #t2 (a:parser t1) (b:parser t2): parser (t1*t2) = sequence a b (fun a b -> (a, b))
let (<|>) = fun a b -> comb_or a b (fun e -> match e with | Left x -> x | Right x -> x)


//let match_class #a (choices: list char) (symb: char -> a): parser a = fun src pos ->
//  let p = (L.fold_left (fun c char -> comb_or c (match_char () char) (fun _ -> (Just char))) (empty Nothing) choices) src pos in
//  match p with
//  | ParserRes pos v -> (match v with | Just v -> ParserRes pos (symb v) | Nothing -> NoRes)
//  | NoRes -> NoRes

let match_class #a (choices: list char) (symb: char -> a): parser a = fun src pos ->
  let p = L.fold_left (fun c char -> c <|> (match_char (Just char) char)) (empty Nothing) choices in
  p <-- p src pos;
  (match snd p with
  | Just v -> ParserRes (fst p) (symb v)
  | Nothing -> NoRes)

let match_digit : parser (n: nat{n <= 9}) = 
  let convert (c:char): (n: nat{n <= 9}) = match c with
              | '1' -> 1 | '2' -> 2 | '3' -> 3 | '4' -> 4 | '5' -> 5
              | '6' -> 6 | '7' -> 7 | '8' -> 8 | '9' -> 9 |  _  -> 0 in
  match_class digitList convert

let match_nat : parser nat =
  let rec convert (c:list (n: nat{n <= 9})): nat = match c with
    | [] -> 0
    | hd::tl -> hd + (M.op_Star 10 (convert tl))
  in
  repeat match_digit (convert @ L.rev)

let fp #a #b (f: a -> b) (p:parser a): parser b = fun src pos -> map_pr (p src pos) f

let letterList = upperCaseCharList `L.append` lowerCaseCharList
let match_word = repeat (match_class letterList id) string_of_list

let uncurry f x = let (l,r) = x in f l r

let delayMe #a (p: unit -> parser a): parser a = fun a b -> (p ()) a b

let (<*>>) a b = sequence a b (fun _ b -> b)
let (<<*>) a b = sequence a b (fun a _ -> a)

let match_space = match_class [' ';'\t';'\n';'\r'] (fun _ -> ())
let any_space = repeat match_space (fun _ -> ())

let match_eof: parser unit = fun src pos -> if pos >= String.length src then ParserRes pos () else NoRes 
let match_eol: parser unit = match_char () '\n'

let match_comment: parser string = any_space <*>> match_string "//" () <*>> match_stringf (fun x -> x <> '\n')

let wrapspace #a (p: parser a): parser a = any_space <*>> p <<*> any_space 

let opc ch: parser unit = wrapspace (match_char () ch)

let uncurry3 f x = let ((a,b),c) = x in f a b c

let match_keyword str: parser unit = wrapspace (match_string str ())
let match_kwds (strs:list string{L.length strs > 0}): parser unit = 
  let hd::tl = strs in
    L.fold_left (fun c kw -> c <*>> match_keyword kw) (match_keyword hd) tl 

let match_maybe #a (p:parser a): parser (maybe a) = fun src pos -> match p src pos with
                | ParserRes x y -> ParserRes x (Just y)
                | NoRes -> ParserRes pos Nothing
                
let aexp_parser: parser lAExp =
  let rec no_rec (): parser lAExp = fp LAExpLitt match_nat <|> fp LAExpVar match_word
                   <|> (match_keyword "(" <*>> (admitP (() << ()); delayMe h') <<*> match_keyword ")")
  and h' (): parser lAExp = admitP (() << ()); let h = delayMe h' in
         no_rec () <|> fp (uncurry LAExpPlus)  (no_rec () <<*> opc '+' <*> h)
                   <|> fp (uncurry LAExpMinus) (no_rec () <<*> opc '-' <*> h)
                   <|> fp (uncurry LAExpMult)  (no_rec () <<*> opc '*' <*> h)
  in wrapspace (h' ())

let bool_litt_parser: parser bool = any_space <*>> match_string "true" true <|> match_string "false" false <<*> any_space

let bexp_parser: parser lBExp =
  let rec no_rec (): parser lBExp = fp LBExpLitt bool_litt_parser
           <|> fp (uncurry LBExpEq) (aexp_parser <<*> match_string "==" () <*> aexp_parser)
           <|> fp (uncurry LBExpLe) (aexp_parser <<*> match_string "<=" () <*> aexp_parser)
           <|> fp LBExpNot (match_char () '~' <*>> (admitP (() << ()); delayMe no_rec))
           <|> (match_keyword "(" <*>> delayMe h' <<*> match_keyword ")")
  and h' (): parser lBExp = admitP (() << ()); let h = delayMe h' in
    no_rec () <|> fp (uncurry LBExpAnd) (no_rec () <<*> match_string "&&" () <*> h)
              <|> fp (uncurry LBExpOr)  (no_rec () <<*> match_string "||" () <*> h)
  in wrapspace (h' ())


let lInstr_parser: parser lInstr =
   let z #a (arg:parser a) = arg <<*> match_maybe match_comment in
   let rec no_rec (nothing:unit): parser lInstr = admitP (() << ()); z (
           fp (uncurry LInstrAssign) (match_word <<*> match_keyword "=" <*> aexp_parser)
       <|> match_string "SKIP" LInstrSkip
       <|> fp (uncurry3 LInstrIf) (
                  ((match_kwds ["if"; "("] <*>> bexp_parser) <<*> match_kwds [")"; "{"])
              <*> ((delayMe h') <<*> match_kwds ["}";"else";"{"])
              <*> ((delayMe h') <<*> match_keyword "}")
           )
       <|> fp (uncurry LInstrWhile) (
                  ((match_kwds ["while";"("] <*>> bexp_parser) <<*> match_kwds [")";"{"])
              <*> ((delayMe h') <<*> match_keyword "}")
           ))
   and h' (): parser lInstr = admitP (() << ()); let h = delayMe h' in
     z (no_rec () <|> fp (uncurry LInstrSeq) (no_rec () <<*> match_keyword ";" <*> ((match_maybe match_comment) <*>> h)))
   in wrapspace (h' ())
   
instance pr_ts #a [| hasToString a |] : hasToString (parserResult a) = { 
   toString = fun v -> match v with
    | ParserRes pos somevalue -> join "" ["{pos:"; string_of_int pos ; "} "; toString somevalue]
    | NoRes -> "NoRes"
}

let parse_toy_language src = match (lInstr_parser <<*> match_eof) src 0 with
  | ParserRes _ res -> Just res
  | NoRes -> Nothing
  
//let ttt = lInstr_parser//match_class ['a';'b'] id //(match_char "GOT A" 'a') <|> (match_char "GOT B" 'b')

//let sss = ttt ()

//let xxx = String.strcat (pr_ts.toString (ttt "if     (6+54+hey<=8) {a=3} else {b=2}" 0)) "\n"
//let xxx s = String.strcat (pr_ts.toString (ttt s 0)) "\n"

//let _ = assert (xxx = magic ()) by (T.compute (); T.qed ())

// let lexer (input: string) =
//   let h (list:list char) = match list with
//     []    -> []
//     hd::tl -> (match hd with
//       'a' -> )
  
