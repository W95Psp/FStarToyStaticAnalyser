module GaloisConnection

open FStar.Tactics.Typeclasses
open PartialOrder
module CSet = Data.Set.Computable.NonOrdered
open FStar.GSet
open Data.Set.Computable.NonOrdered.PartialOrder

class hasGaloisConnection (c:eqtype) a = {
     c_po  : hasPartialOrder c
   ; a_po  : hasPartialOrder a
   ; gamma : (f:(a -> set c){ isMonotonic f })
   ; alpha : (f:(CSet.set c -> a){ isMonotonic f })
   ; galois_wf : (sa:a) -> (sc:CSet.set c) ->
		 Lemma (CSet.cset_to_set sc `l_po` (gamma sa) <==> sa `l_po` (alpha sc)) // TODO <=>
   ; alpha': c -> a
   ; getBooleanPredicate: a -> (c -> bool)
}

let mkGaloisConnection (#c:eqtype) #a
			     [| hasPartialOrder c |]
			     [| hasPartialOrder a |]
			     (gamma:(a -> set c){ isMonotonic gamma })
			     (alpha:(CSet.set c -> a){ isMonotonic alpha })
			     (galois_wf : (sa:a) -> (sc:CSet.set c) -> 
					Lemma (CSet.cset_to_set sc `l_po` (gamma sa) /\ sa `l_po` (alpha sc))
			     )
                             getBooleanPredicate
  = {
	c_po      = solve
      ; a_po      = solve
      ; gamma     = gamma
      ; alpha     = alpha
      ; galois_wf = galois_wf
      ; alpha'    = (fun c -> alpha (CSet.singleton c))
      ; getBooleanPredicate = getBooleanPredicate
    }
