module DefaultValue

open FStar.Tactics.Typeclasses

class hasDefaultValue a = {
  def: a
}

instance _ : hasDefaultValue int = {def = 0}