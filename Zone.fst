module Zone

open FStar.List.Tot.Base
open ExtInt
open Functor

type slist (n:nat) (a:Type) = (r:list a {length r == n})
type matrix (n m:nat) (a:Type) = slist n (slist m a)

let (<$>) = functor_tup2.fmap

type zone' (#n:nat) (t:eqtype)  = {
    variables: (v:slist n string {noRepeats v})
  ; mat:       matrix (n+1) (n+1) t//list (slist n int)
}
let repeat #a (s:a) (n':nat): slist n' a = 
  let rec h (n:nat): slist n a = match n with
    | 0 -> []
    | n -> s :: h (n-1) in
    h n'
let emptyMatrix (n m:nat) (defVal:'a) = repeat (repeat defVal n) m

let emptyZone (#n:nat) (vars:slist n string{noRepeats vars}) = {
    variables = vars
  ; mat       = emptyMatrix (n+1) (n+1) plusInfty
}

let findIndex (#a:eqtype) (lst:list a{noRepeats lst}) (x:a{mem x lst}): (i:nat{i < length lst}) =
  let rec h (l:list a{noRepeats l /\ mem x l}) (n:nat{length l - 1 = n}): (i:nat{i <= n}) = match l with
    hd::tl -> if hd = x then n else h tl (n - 1) in h lst (length lst - 1)

let rec exact_nth #t (l:list t) (n:nat{n < length l}) = match l with
  hd::tl -> if n = 0 then hd else exact_nth tl (n - 1)

let matGetAt (#sn #sm: nat) #t (mat:matrix sn sm t) (n:nat{n < sn}) (m:nat{m < sm}) = exact_nth (exact_nth mat n) m

let slistUpdAt #a (#nl:nat) (l:slist nl a) (n:nat) (x:a -> a) =
  let rec h (nl:nat) (l:slist nl a) (n:nat): slist nl a = match l with
  | [] -> []
  | hd::tl -> if n = 0 then (x hd)::tl
            else hd::h (nl - 1) tl (n - 1) in h nl l n

let matSetAt (#sn #sm: nat) #t (mat:matrix sn sm t) (n:nat{n < sn}) (m:nat{m < sm}) (value:t) = slistUpdAt mat n (fun r -> slistUpdAt r m (fun _ -> value))

let curry #a #b #c (f:a -> b -> c) ((v,w):(a*b)): c = f v w

let findIndex' (#a:eqtype) (lst:list a{noRepeats lst}) (x:option (x:a{mem x lst})): (i:nat{i <= length lst}) = match x with
  | Some x -> 1 + findIndex lst x
  | _ -> 0

let getConstraint (#n:nat) #t (z:zone' #n t) (v1 v2:(option (x:string{mem x z.variables}))): t =
  // cannot resolve stuff: (curry matGetAt z.mat) (findIndex z.variables <$> (v1, v2))
  let (i, j) = findIndex' z.variables <$> (v1, v2) in matGetAt z.mat i j

let setConstraint (#n:nat) #t (z:zone' #n t) (v1 v2:(option (x:string{mem x z.variables}))) (value:t): zone' #n t =
  let (i, j) = findIndex' z.variables <$> (v1, v2) in {z with mat = matSetAt z.mat i j value}

type zone #n t = | BottomZone : zone #n t | SomeZone : zone' #n t -> zone #n t


