/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Common utilities for list manipulation and stack indexing used in
computational complexity proofs.
-/
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith

namespace ComplexityUtils

open List

/-- Monotonicity of take equality. -/
theorem take_mono {α : Type*} {m n : ℕ} {l1 l2 : List α} (hmn : m ≤ n)
    (h : l1.take n = l2.take n) : l1.take m = l2.take m := by
  have := congr_arg (List.take m) h
  simp [List.take_take] at this; rwa [Nat.min_eq_left hmn] at this

/-- Indexing into a reversed list with drop.head? -/
theorem head?_drop_reverse_cons {α : Type*} (x : α) (l : List α) (j : ℕ)
    (hj : j < l.length) :
    ((x :: l).reverse.drop j).head? = (l.reverse.drop j).head? := by
  simp only [reverse_cons, drop_append, hj, ite_true]
  have h_len : j < l.reverse.length := by rwa [length_reverse]
  simp [h_len]

end ComplexityUtils
