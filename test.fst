module Test

open Interval
open FStar.Tactics.Typeclasses
open ExtInt

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
  | LBExpLt  : lAExp -> lAExp -> lBExp

let ( !.  ) = LBExpNot
let ( &&. ) = LBExpAnd
let ( ||. ) = LBExpOr
let ( ==. ) = LBExpEq
let ( <.  ) = LBExpLt

class litteral_lift a b = {
  v : a -> b
}
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

val iF : int -> int
let iF v = v

val while : lBExp -> doTag -> lInstr -> endTag -> lInstr
let while cond _ body _ = LInstrWhile cond body

let a = "a"
let b = "b"
let c = "c"
let d = "d"
let i = "i"
let tmp = "tmp"

let fib (max:int) =
  (a =. (v 1)) >>
  (b =. (v 1)) >>
  (i =. (v 0)) >>
  (while (!! i <. (LAExpLitt max)) Do (
    (tmp =. (!! a)) >>
    (a =. (!! b)) >>
    (b =. (!! tmp) +. (!! b)) >>
    (i =. (!! i) +. (v 1))
  ) End)

type state = string -> int

val emptyState : state
let emptyState _ = 0

open FStar.Mul


// interface _ : run_c = {} 
val norm_lAExp : state -> lAExp -> int
let rec norm_lAExp state exp =
  let fA a b g = g (norm_lAExp state a) (norm_lAExp state b) in
  match exp with 
  | LAExpLitt v -> v
  | LAExpMinus a b -> fA a b ( fun x y -> x - y )
  | LAExpMult a b -> fA a b  ( * )
  | LAExpPlus a b -> fA a b  ( + )
  | LAExpVar v -> state v

val norm_lBExp : state -> lBExp -> bool
let rec norm_lBExp state exp =
  let fA a b g = g (norm_lAExp state a) (norm_lAExp state b) in
  let fB a b g = g (norm_lBExp state a) (norm_lBExp state b) in
  match exp with
  | LBExpLitt v -> v
  | LBExpEq a b -> fA a b ( fun a b -> a = b )
  | LBExpLt a b -> fA a b (<)
  | LBExpAnd a b-> fB a b (&&)
  | LBExpOr a b -> fB a b ( || )
  | LBExpNot a -> norm_lBExp state a


class run_c a b = {
  run : state -> a -> b
}
instance _ : run_c lAExp int = { run = norm_lAExp }
instance _ : run_c lBExp bool = { run = norm_lBExp }

val norm_lInstr : state -> lInstr -> (fuel:nat) -> Tot state (decreases fuel)
let rec norm_lInstr state instr n = if n = 0 then state else
  let f = norm_lInstr in
  match instr with
  | LInstrAssign name v -> (fun q -> if q = name then run state v else state q)
  | LInstrIf cond b1 b2 -> norm_lInstr state (if run state cond then b1 else b2) (n - 1)
  | LInstrSkip          -> state
  | LInstrSeq a b       -> f (f state a (n - 1)) b (n - 1)
  | LInstrWhile cond b  -> if run state cond then
				f state (b >> (while cond Do b End)) (n - 1)
			  else  state

instance _ : run_c lInstr state = { run = fun s a -> norm_lInstr s a 100 }

val execFib : int -> state
let execFib n = (run emptyState (fib n))

let xx n = execFib n "a"

let test = norm_lBExp emptyState (LBExpLitt true)


let xxx = run emptyState (v 2 +. v 3)

let main = 
  let i = FStar.IO.input_int () in
  FStar.IO.print_string (string_of_int (xx i))

let isPartialOrder #a (f:(a -> a -> bool)) =
    (forall a    . f a a)
  /\ (forall a b  . f a b /\ f b a ==> a == b)
  /\ (forall a b c. f a b /\ f b c ==> f a c)

let isPartialOrderL #a (f:(a -> a -> Type)) =
    (forall a    . f a a)
  /\ (forall a b  . f a b /\ f b a ==> a == b)
  /\ (forall a b c. f a b /\ f b c ==> f a c)

class hasPartialOrder a = {
   po : (f:(a -> a -> bool){isPartialOrder f})
}

class hasLPartialOrder a = {
  l_po : (f:(a -> a -> Type){isPartialOrderL f})
}

instance _ : hasLPartialOrder (x:Type{hasPartialOrder x}) = {
  l_po = let myPo = solve in let h = fun a b -> True in assert (isPartialOrderL h); h
}

instance _ : hasPartialOrder int = { po = fun a b -> a <= b } 

let isMonotonic #a #b [| hasPartialOrder a |] [| hasPartialOrder b |] (f:(a -> b)) =
  forall a b. a `po` b ==> f(a) `po` f(b)

type set = | EmptySet  

instance _ : hasPartialOrder (int -> bool) = {
  po = fun a b -> 
}

instance _ : hasPartialOrder ((c:Type{hasPartialOrder c}) -> bool) = {
  po = fun a b -> true
}

class hasGaloisConnection c a = {
   c_po  : hasPartialOrder c;
   a_po  : hasPartialOrder a;
   gamma : (f:(a -> (c -> Type0)){ });
   alpha : c -> (x:a{a_po.po x x})
}

let wfGaloisConnection #c #a (gc : hasGaloisConnection c a) =
  isMonotonic 

let mkGaloisConnection #c #a [| hasPartialOrder c |] [| hasPartialOrder a |]
			  (gamma : a -> (c -> bool)) (alpha : c -> a) =
			 {
			   c_po = solve;
			   a_po = solve;
			   gamma = gamma;
			   alpha = alpha;
			 }



class abstractDomain c a = {
  order : a -> a -> bool;
  gamma : a -> (c -> Type0);
  alpha : c -> a;
  union : a -> a -> a;
  inter : a -> a -> a;
  bottom: a;
  top   : a;
  widen : a -> a -> a;
  assign: string -> a -> a;
  op_eq : a -> a -> a
}

class test0 a = {
  get0 : a -> int
}

instance test0_int : test0 int = {get0 = (fun _ -> 10) }

class test2 a = {
  test0_super: test0 a;
  get2: a -> int
}

instance test0_eq (d : test2 'a) : test0 'a = d.test0_super

let mktest2 (#a:Type) [| test0 a |] (f : a -> int)  = {
  test0_super = solve;
  get2 = f
}

instance _ : test2 int = mktest2 (fun z -> z * get0 z)

let x = get2 22

class test1 a (i:test0 a) = {
  get1 : a -> int
}

instance hey (i:test0 'a) : test1 'a i = {
  get1 = fun (x:'a) -> (get0 x) * 10
}

let asd = get1 1


// interface _ : testx c a (abstractDomain) 

let _ = mkabstractDomain


let aaa a b = a \/ b

let asdasdxx = aaa True False


let wellfounded #c #a (dom:abstractDomain c a) =
  isPartialOrder dom.order


