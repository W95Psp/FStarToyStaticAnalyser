module ZeroOrLess

open FStar.Tactics.Typeclasses

class hasZeroOrLess a = {zeroOrLess: a}