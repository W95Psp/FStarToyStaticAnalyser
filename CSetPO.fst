module CSetPO

open CSet
open PartialOrder

open FStar.Tactics
open FStar.Tactics.Typeclasses

instance csetLPO #c : hasLPartialOrder (CSet.set c) = {
    l_po_cmp = CSet.equal;
    l_po = let h = (fun (a b: CSet.set c) -> true == CSet.subset a b) in admitP (isPartialOrderL CSet.equal h); h
}

instance gsetLPO #c : hasLPartialOrder (GSet.set c) = {
    l_po_cmp = GSet.equal;
    l_po = GSet.subset
}