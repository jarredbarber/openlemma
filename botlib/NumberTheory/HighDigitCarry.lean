/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Provenance: Originally proved by LLM agents (Claude, Anthropic) working on
Erdős Problem 728, with zero human mathematical input.
Trust level: 🟢 Compiler-verified (zero sorrys, zero axioms).
-/
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Choose.Factorization
import botlib.NumberTheory.BinomialDivisibility

/-!
# High Digits Force Carries in Binomial Coefficients

When a base-p digit of m is "high" (≥ ⌈p/2⌉), the addition m + m produces a
carry at that position. This gives a lower bound on `v_p(C(2m, m))` in terms
of the count of high digits of m.

## Main Results

* `high_digit_forces_carry` — a high digit at position i forces `p^(i+1) ≤ 2·(m mod p^(i+1))`
* `lower_bound_valuation_by_high_digits` — `count_high_digits(p, m, D) ≤ v_p(C(2m, m))`

## Applications

Combined with Chernoff bounds (`botlib.Combinatorics.ChernoffDigits`), this shows
that most values of m have `v_p(C(2m,m))` growing linearly in the number of digits.
-/

open Nat

namespace OpenLemma.HighDigitCarry

/-- The i-th digit of m in base p. -/
def digit (p m i : ℕ) : ℕ := (m / p ^ i) % p

/-- A digit is "high" if it is at least ⌈p/2⌉. -/
def is_high_digit (p m i : ℕ) : Prop := digit p m i ≥ (p + 1) / 2

/-- The set of indices of high digits in m (up to a bound D). -/
noncomputable def high_digits_finset (p m D : ℕ) : Finset ℕ :=
  (Finset.range D).filter (fun i => is_high_digit p m i)

/-- The number of high digits in m (up to a bound D). -/
noncomputable def count_high_digits (p m D : ℕ) : ℕ :=
  (high_digits_finset p m D).card

/-- **High digit forces carry.** If the i-th base-p digit of m is high,
then `p^(i+1) ≤ (m mod p^(i+1)) + (m mod p^(i+1))`, i.e., adding m to itself
produces a carry at position i. -/
lemma high_digit_forces_carry (p m i : ℕ) (h_high : is_high_digit p m i) :
    p ^ (i + 1) ≤ m % p ^ (i + 1) + m % p ^ (i + 1) := by
  have h_digit : digit p m i = (m % p ^ (i + 1)) / p ^ i := by
    rw [digit, ← Nat.mod_mul_right_div_self, Nat.add_one, Nat.pow_succ', mul_comm (p^i) p]
  have h_decomp : m % p ^ (i + 1) = digit p m i * p ^ i + m % p ^ i := by
    nth_rw 1 [← Nat.div_add_mod (m % p ^ (i + 1)) (p ^ i)]
    rw [← h_digit, mul_comm]
    congr 1
    rw [Nat.add_one, Nat.pow_succ, Nat.mod_mod_of_dvd]
    simp only [Nat.dvd_mul_right]
  have h_bound : p ≤ 2 * digit p m i := by
    rw [is_high_digit] at h_high
    apply Nat.le_trans _ (Nat.mul_le_mul_left 2 h_high)
    have h_div_mod := Nat.div_add_mod (p + 1) 2
    have h_mod_le : (p + 1) % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num : 0 < 2))
    omega
  calc
    p ^ (i + 1) = p^i * p := by rw [Nat.pow_succ, mul_comm]
    _ ≤ p^i * (2 * digit p m i) := Nat.mul_le_mul_left _ h_bound
    _ = (2 * digit p m i) * p^i := by rw [mul_comm]
    _ = 2 * (digit p m i * p ^ i) := by ring
    _ ≤ 2 * (digit p m i * p ^ i + m % p ^ i) := Nat.mul_le_mul_left 2 (Nat.le_add_right _ _)
    _ = 2 * (m % p ^ (i + 1)) := by rw [h_decomp]
    _ = m % p ^ (i + 1) + m % p ^ (i + 1) := by ring

/-- **Lower bound on v_p(C(2m, m)) by high digit count.**
The p-adic valuation of the central binomial coefficient C(2m, m) is at least
the number of high base-p digits of m (up to bound D). -/
lemma lower_bound_valuation_by_high_digits (p m D : ℕ) (hp : p.Prime)
    (h_b : log p (2 * m) < D + 1) :
    count_high_digits p m D ≤ ((2 * m).choose m).factorization p := by
  let f : ℕ → ℕ := fun i => i + 1
  rw [Nat.factorization_choose hp (Nat.le_mul_of_pos_left m (by omega)) h_b]
  apply Finset.card_le_card_of_injOn f
  · -- maps into
    intro i hi
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico]
    simp [high_digits_finset] at hi
    let ⟨hi_range, hi_high⟩ := hi
    constructor
    · constructor
      · exact Nat.le_add_left 1 i
      · exact Nat.add_lt_add_right hi_range 1
    · simp only [Nat.two_mul, Nat.add_sub_cancel]
      apply high_digit_forces_carry p m i hi_high
  · -- inj on
    intros x _ y _ hxy
    simp [f] at hxy
    exact hxy

end OpenLemma.HighDigitCarry
