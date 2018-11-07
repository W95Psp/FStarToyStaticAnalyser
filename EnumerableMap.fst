(* 
This module implements an inefficient and hacky (but working) enumerable version of map.
Basically, it provides a map from string to values with a default variable, and each time one updates a value at some key `k`, it keeps track of `k`.
If the user doesn't touch the structure (i.e. the user is only using em_get em_set), then the used keys will be coherent with the content of the map.
Note that I could have specified "every non-null value have their keys listed", but for my purpose that was rather useless.  
@summary: Maps from strings to any type, with enumerable keys
*)
module EnumerableMap

module CSet = CSet
open FStar.String
open ToString
open FStar.Tactics.Typeclasses
open DefaultValue
open FStar.List.Tot.Base

noeq
type enumerableMap a = {
   _em_data: string -> a
 ; _em_keys: CSet.set string
}

(* convert "stupid" raw state (i.e. functions from strings to values) to our em things *)
let state_to_em s = {_em_data = s;_em_keys = []}
let em_get (m:enumerableMap 'a) (k:string): 'a = m._em_data k
let em_set (m:enumerableMap 'a) (k:string) (v:'a) = let data = fun q -> if q = k then v else m._em_data q in {
   _em_data = data
 ; _em_keys = CSet.add_in_set k m._em_keys
}
(* apply an operation on each values pairwise of same keys *)
let em_combine (m1 m2:enumerableMap 'a) (f:'a -> 'a -> 'a) = {
   _em_data = (fun key -> f (em_get m1 key) (em_get m2 key))
 ; _em_keys = CSet.union m2._em_keys m1._em_keys
}
(* equality here means *)
let em_equal #a (myEq:a->a->bool) (m1 m2:enumerableMap a) =
    let f1 = em_get m1 in
    let f2 = em_get m2 in
    let rec h l = (match l with
      | [] -> true
      | hd::tl -> if f1 hd `myEq` f2 hd then h tl else false
    ) in h (CSet.union m2._em_keys m1._em_keys)

(* we derive an instance of ToString to pretty print our maps *)
instance emHasToString #a [| hasToString a |] : hasToString (enumerableMap a) =  { toString = fun i -> 
  "{" `strcat`
         join ", " (List.Tot.Base.map (fun s -> s `strcat` " = " `strcat` toString (em_get i s)) i._em_keys)
      `strcat` "}"
}

let rec listToEnumerableSet (#a:Type) [| hasDefaultValue a |] (lst:list (tuple2 string a))
  = let rec resolver l (query: string) = (match lst with
                  | [] -> def
                  | (name, value)::tl -> if name = query then value else resolver tl query
  ) in {
  _em_data = resolver lst;
  _em_keys = map (fun (k, _) -> k) lst
  }