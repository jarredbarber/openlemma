example (a b : Bool) (h : (a = true ↔ b = true)) : a = b := by
  apply Bool.ext
  exact h
