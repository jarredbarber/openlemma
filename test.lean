import Mathlib.Data.List.Basic
example (l : List ℕ) (x : ℕ) : x ∈ l.eraseDups ↔ x ∈ l := by exact List.mem_eraseDups
