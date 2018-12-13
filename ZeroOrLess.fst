(*
@summary: allow expressing generically "<= 0" for an abstract domain
*)
module ZeroOrLess

open FStar.Tactics.Typeclasses

class hasZeroOrLess a = {
  zeroOrLess: a;
  zeroOnly: a;
  aroundZero: a
}
