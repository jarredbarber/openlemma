import Mathlib.Data.List.Dedup
import Mathlib.Data.Nat.Basic

theorem List.Sublist.sum_le_nat {l1 l2 : List ℕ} (h : l1.Sublist l2) : l1.sum ≤ l2.sum := by
  induction h with
  | slnil => simp
  | cons x h ih =>
    simp; exact Nat.le_trans ih (Nat.le_add_left _ _)
  | cons₂ x h ih =>
    simp; exact Nat.add_le_add_left ih _

#check List.Sublist.sum_le_nat
