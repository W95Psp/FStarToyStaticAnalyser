(*
@summary: Congruence domain
*)
module Congruence

open ExtInt
open PartialOrder
open FStar.List.Tot
open FStar.Tactics.Typeclasses
open ToString

open AbstractDomain
open GaloisConnection
open DefaultValue

open ZeroOrLess

module G = FStar.GSet
module CSet = Data.Set.Computable.NonOrdered

type congruence = | SomeCongruence : (a:nat) -> (b:int{if a = 0 then True else (b < a /\ b >= 0)}) -> congruence
                  | EmptyCongruence : congruence


private
let gbind #a (d:a) (x: congruence) (f: (ne: congruence{SomeCongruence? ne}) -> a) =
  if SomeCongruence? x then f x else d

module Mul = FStar.Mul

let ( |. ) (x d:int) = if d = 0 then true else let k = x / d in d `Mul.op_Star` k = x

// "a ≡ b [c]" is "a =~ b %% c"
//let ( %% ) = SomeCongruence
// is y === x [x']?

let is_in_congruence (x a y: int): bool =
  if a = 0 then x = y else x % a = y % a
  //if x = 0 then x' = 1 || x = x' else y % x' = x % x' //y |. abs (x - x')
// is_in_congruence  0 1 0 (0 === 0 [1] ?) should be true

let lift_const c = SomeCongruence 0 c

let natstar = (x:nat{x > 0})

private
let test (m:natstar) (x y c:nat) = (
  is_in_congruence (m `Mul.op_Star` x + c)
                   m
                   (m `Mul.op_Star` y + c)
        )

let ( =~ ) (x: int) (c: congruence) = 
  match c with
  | SomeCongruence x' y -> is_in_congruence x x' y
  | _ -> false

let std_gcd (a: int{a <> 0}) (b: int): Tot (n:nat{n <> 0}) =
  let rec h (a': natstar) (b': nat): Tot (n:natstar) (decreases %[a' + b'; if a' > b' then 0 else 1]) = 
    if b' = 0 then a'
    else h b' (a' % b')
  in h (abs a) (abs b)

let std_lcm (a: int{a <> 0}) (b: int): nat = abs (a `Mul.op_Star` b) / std_gcd a b

let extendZero (f: (v:int{v <> 0}) -> int -> nat) (x y: int) = if x = 0 || y = 0 then 0 else f x y

let gcd (x y:int): nat = if x = 0 then abs y
                else if y = 0 then abs x
                else               std_gcd x y
let lcm = extendZero std_lcm

let includes c1 c2 =
  let bind = gbind false in
  c1 <-- c1; c2 <-- c2; let SomeCongruence a b = c1 in let SomeCongruence a' _ = c2 in
  (a' |. a) && (b =~ c2)

let union' c1 c2 =
  match c1 with
    | EmptyCongruence -> c2
    | SomeCongruence a b -> 
    ( match c2 with
      | EmptyCongruence -> c1
      | SomeCongruence a' b' -> 
                       let coef = a `gcd` a' `gcd` abs (b - b') in
                       SomeCongruence
                                   coef
                                   (if coef = 0 then 0 else b % coef)
    )

let union = union'


instance _ : hasToString congruence =  { toString = fun i ->  match i with
  | EmptyCongruence -> "┴"
  | SomeCongruence a b -> intHasToString.toString b ^ "[" ^ toString a ^ "]"
}


//let x = toString (union' (lift_const 2) (lift_const 18))
//module Tactics = FStar.Tactics
//let _ = assert (x == magic ()) by (Tactics.compute (); Tactics.qed ())

let extended_euclidean (a b: int) =
  let rec h (a b: nat) = 
	if b = 0 then (a, 1, 0)
	else match admitP (b << a); (h b (a % b)) with
		(d, x, y) -> (d, y, x - (a / b) `Mul.op_Star` y)
  in h (abs a) (abs b)

private
type neCongr = c:congruence {SomeCongruence? c}

private
let ( ** ) = Mul.op_Star

private
let testEGCD x y = let (r,a,b) = extended_euclidean x y in 
                   (a `Mul.op_Star` x) + (b `Mul.op_Star` y) = r


// returns x such that "x = a [a']" and "x = b [b']"
let solve_two_mod_eq (a a' b b': int) =
    let (_, a'', b'') = extended_euclidean a' b' in
    a ** b' ** b'' + b ** a' ** a''

let test_solve_mod a ma b mb = let x = solve_two_mod_eq a ma b mb in
                                         is_in_congruence x ma a
                                      && is_in_congruence x mb b

//let _ = assert (test_solve_mod 6 18 2 18) by (Tactics.compute (); Tactics.qed ())

//let solve_two_mod_eq (ac: neCongr) (bc: neCongr) =
//    let SomeCongruence a a' = ac in let SomeCongruence b b' = bc in
//    let (_, a'', b'') = extended_euclidean a' b' in
//    a ** b' ** b'' + b ** a' ** a''


//instance congruenceHasPartialOrder : hasPartialOrder congruence = { po = (admit(isPartialOrder gcd); gcd) }

private
let inter_cong a1 m1 a2 (m2:nat{m1 <> 0 \/ m2 <> 0}) =
  let g = m1 `gcd` m2 in
  if is_in_congruence a1 g a2 then (
    let (_, p, q) = extended_euclidean m1 m2 in
    let ( * ) = Mul.op_Star in 
    let x = a1 * m2 / g * q + a2 * m1 / g * p in
    let m = lcm m1 m2 in  
    SomeCongruence m (x % (admit (); m))
  ) else
    EmptyCongruence


//let _ = assert (magic () == lcm  0) by (Tactics.compute (); Tactics.qed ())
//let _ = assert (magic () = inter_cong 2 3 3 4) by (Tactics.compute (); Tactics.qed ())
 

let inter ca cb = 
  let bind = gbind EmptyCongruence in
  ca <-- ca; cb <-- cb; let SomeCongruence ma a = ca in let SomeCongruence mb b = cb in
  if      ma = 1 then (* ca is top *) cb
  else if mb = 1 then (* cb is top *) ca
  else if ma = 0 || mb = 0 then
    (if ca = cb then ca else EmptyCongruence)
  else    inter_cong a ma b mb

//let _ = assert (inter (mkCong 18 2) (mkCong 19 4) ==magic()) by (Tactics.compute (); Tactics.qed ())

 // let _ = 
 //   let x = SomeCongruence 3 1 in
 //   let y = SomeCongruence 4 1 in
 //   assert (inter x y == magic ()) by (Tactics.compute (); Tactics.qed ())
   
   //assert ((solve_two_mod_eq 18 2 18 2 % 18) == magic ()) by (Tactics.compute (); Tactics.qed ())
//   assert (inter x x == magic ()) by (Tactics.compute (); Tactics.qed ())


//let _ = assert (inter x x == magic ()) by (compute (); qed ())

let gamma (i: congruence): GSet.set int = match i with
  | EmptyCongruence -> GSet.empty
  | SomeCongruence _ _ -> GSet.comprehend (fun v -> v =~ i)

let values_to_congruence (l: list int) =
  fold_left union EmptyCongruence (map (fun v -> SomeCongruence 0 v) l)
  // values [v0, v1, v2, ...]
  // v_i === a [b]
  // v_i = k * b + a
  // v_i - a |. b

//let _ = assert (magic () == values_to_congruence [5;8;12]) by (compute (); qed ())

let mkCong (a:nat) (b:int) = SomeCongruence a (if a = 0 then b else b % a) 

let plus c1 c2 = let bind = gbind EmptyCongruence in
  c1 <-- c1; c2 <-- c2; let SomeCongruence a b = c1 in let SomeCongruence a' b' = c2 in
  let a'' = a `gcd` a' in 
  mkCong a'' (b + b')
let minus c1 c2 = let bind = gbind EmptyCongruence in
  c1 <-- c1; c2 <-- c2; let SomeCongruence a b = c1 in let SomeCongruence a' b' = c2 in
  mkCong (a `gcd` a') (b - b')

let mult c1 c2 = let bind = gbind EmptyCongruence in
  c1 <-- c1; c2 <-- c2; let SomeCongruence a b = c1 in let SomeCongruence a' b' = c2 in
  mkCong ((a ** a') `gcd` (a ** b ) `gcd` (a' ** b)) (b ** b')


let divide c1 c2 = let bind = gbind EmptyCongruence in
  c1 <-- c1; c2 <-- c2; let SomeCongruence a b = c1 in let SomeCongruence a' b' = c2 in
       if a' = 0 && b' = 0
  then EmptyCongruence
  else if a' = 0 && not (b' = 0) && (b' |. a) && (b' |. b) then
       mkCong (a / abs(b')) (b / b')
  else mkCong 1 0

 
let unaryMinus c1 = let bind = gbind EmptyCongruence in
  c1 <-- c1; let SomeCongruence a b = c1 in  
  SomeCongruence a (if b = 0 then 0 else (a - b))

let equal (a b:congruence) = a = b

instance _ : hasPartialOrder congruence = { po = (admit (); includes) }

let congruence_alpha set = values_to_congruence (CSet.set_to_list set)

instance congruenceHasGaloisConnection
  : hasGaloisConnection int congruence
    = mkGaloisConnection
       gamma
       (admitP (isMonotonic congruence_alpha); congruence_alpha) (*TODO*)
       (magic ()) 
       (fun cV aV -> aV =~ cV)

let rec congruence_widen (i j:congruence) =
  let bind = gbind EmptyCongruence in
  i <-- i; let SomeCongruence a _ = i in
  if a = 1 then j else i

instance intervalDomain : hasAbstractDomain congruence = mkAbstractDomain #congruence
                          union
                          inter
           (*bottom*)     EmptyCongruence
           (*top*)        (SomeCongruence 1 0)
           (*widen*)      congruence_widen
                          inter // TODO
           (*assign*)     (fun _ (i: congruence) -> i)
                          equal
                          (fun x -> x = EmptyCongruence)
                          
instance _ : hasDefaultValue congruence = {def = top}
instance _ : hasZeroOrLess congruence = {
  zeroOrLess = top;
  zeroOnly   = lift_const 0;
  aroundZero = lift_const (-1) `union` lift_const 0 `union` lift_const 1 (* which is top *)
}

instance intervalOperators : hasAbstractOperators congruence = mkAbstractOperators unaryMinus plus minus mult divide
