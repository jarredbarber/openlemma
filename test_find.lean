import Mathlib.Data.List.Basic
import Mathlib.Data.Bool.AllAny
example (l : List ℕ) (v : ℕ) (hv : v ∈ l) : List.find? (fun n => n == v) l = some v := by apply?
