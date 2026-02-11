/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Provenance: Originally proved by LLM agents (Claude, Anthropic) working on
Erdős Problem 728, with zero human mathematical input.
Trust level: 🟢 Compiler-verified (zero sorrys, zero axioms).
-/
import Mathlib

open Nat

namespace OpenLemma.BinomialDivisibility

/-!
# Reduction Lemma

Equivalence between factorial divisibility and binomial coefficient divisibility.
Under the substitution a = m, b = m + k, n = 2m, the factorial condition
`a! * b! | n! * (a + b - n)!` becomes `C(m+k, k) | C(2m, m)`.
-/

lemma choose_centralBinom_factorial_identity (m k : ℕ) :
    (2*m).choose m * m.factorial * (m+k).factorial =
    (m+k).choose k * ((2*m).factorial * k.factorial) := by
  have h1 : (2*m).choose m * m.factorial * (2*m - m).factorial = (2*m).factorial :=
    choose_mul_factorial_mul_factorial (Nat.le_mul_of_pos_left m (by omega))
  have h2 : (m+k).choose k * k.factorial * ((m+k) - k).factorial = (m+k).factorial :=
    choose_mul_factorial_mul_factorial (Nat.le_add_left k m)
  have hsimp1 : 2 * m - m = m := by omega
  have hsimp2 : m + k - k = m := by omega
  rw [hsimp1] at h1; rw [hsimp2] at h2
  rw [← h2, ← h1]; ring

/-- **Reduction Lemma.** `C(m+k, k) | C(2m, m)` iff `m! * (m+k)! | (2m)! * k!`. -/
lemma reduction_lemma (m k : ℕ) :
    (m+k).choose k ∣ (2*m).choose m ↔
    m.factorial * (m+k).factorial ∣ (2*m).factorial * k.factorial := by
  have hid := choose_centralBinom_factorial_identity m k
  have hpos : (m.factorial * (m+k).factorial) ≠ 0 :=
    Nat.ne_of_gt (Nat.mul_pos (factorial_pos m) (factorial_pos (m+k)))
  have hck_pos : (m+k).choose k ≠ 0 :=
    Nat.ne_of_gt (choose_pos (Nat.le_add_left k m))
  constructor
  · intro ⟨q, hq⟩
    use q
    have step : (m+k).choose k * (q * (m.factorial * (m+k).factorial)) =
                (m+k).choose k * ((2*m).factorial * k.factorial) := by
      have : (m+k).choose k * q * m.factorial * (m+k).factorial =
             (m+k).choose k * ((2*m).factorial * k.factorial) := by
        calc (m+k).choose k * q * m.factorial * (m+k).factorial
            = ((m+k).choose k * q) * m.factorial * (m+k).factorial := by ring
          _ = (2*m).choose m * m.factorial * (m+k).factorial := by rw [← hq]
          _ = (m+k).choose k * ((2*m).factorial * k.factorial) := hid
      nlinarith
    have := mul_left_cancel₀ hck_pos step
    linarith
  · intro ⟨q, hq⟩
    use q
    have step : (2*m).choose m * (m.factorial * (m+k).factorial) =
                (m+k).choose k * q * (m.factorial * (m+k).factorial) := by
      calc (2*m).choose m * (m.factorial * (m+k).factorial)
          = (2*m).choose m * m.factorial * (m+k).factorial := by ring
        _ = (m+k).choose k * ((2*m).factorial * k.factorial) := hid
        _ = (m+k).choose k * (m.factorial * (m+k).factorial * q) := by rw [hq]
        _ = (m+k).choose k * q * (m.factorial * (m+k).factorial) := by ring
    exact mul_right_cancel₀ hpos step

/-!
# Carry Dominance Lemma

For any prime `p > 2k` and any non-negative integer `m`,
`v_p(C(m+k, k)) ≤ v_p(C(2m, m))`.

By Kummer's theorem, both sides count carries in base-p addition.
Since `p > 2k`, `k` is a single base-p digit, and every carry in `m + k`
implies a carry in `m + m`.
-/

private lemma carry_dominance_pointwise (p m k i : ℕ) (hp : Nat.Prime p) (hpk : 2 * k < p)
    (hi : 1 ≤ i) (hcarry : p ^ i ≤ k % p ^ i + m % p ^ i) :
    p ^ i ≤ m % p ^ i + m % p ^ i := by
  have hp_pos : 0 < p := hp.pos
  have hk_lt_pi : k < p ^ i := by
    calc k < p := by omega
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ i := Nat.pow_le_pow_right hp_pos hi
  rw [Nat.mod_eq_of_lt hk_lt_pi] at hcarry
  have : 2 * k < p ^ i := by
    calc 2 * k < p := hpk
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ i := Nat.pow_le_pow_right hp_pos hi
  omega

/-- **Carry Dominance Lemma.** For prime `p > 2k`:
`v_p(C(m+k, k)) ≤ v_p(C(2m, m))`. -/
lemma carry_dominance (p m k : ℕ) (hp : Nat.Prime p) (hpk : 2 * k < p) :
    ((m + k).choose k).factorization p ≤ ((2 * m).choose m).factorization p := by
  set b := max (Nat.log p (m + k)) (Nat.log p (2 * m)) + 1
  have hb1 : Nat.log p (m + k) < b := by omega
  have hb2 : Nat.log p (m + m) < b := by
    have : m + m = 2 * m := by ring
    rw [this]; omega
  rw [factorization_choose' hp hb1]
  have h2m : 2 * m = m + m := by ring
  rw [h2m, factorization_choose' hp hb2]
  apply Finset.card_le_card
  intro i
  simp only [Finset.mem_filter, Finset.mem_Ico]
  exact fun ⟨⟨hi1, hi2⟩, hcarry⟩ =>
    ⟨⟨hi1, hi2⟩, carry_dominance_pointwise p m k i hp hpk hi1 hcarry⟩

/-- Carry dominance in terms of `padicValNat`. -/
lemma carry_dominance_padicValNat (p m k : ℕ) (hp : Nat.Prime p) (hpk : 2 * k < p) :
    padicValNat p ((m + k).choose k) ≤ padicValNat p ((2 * m).choose m) := by
  rw [← factorization_def _ hp, ← factorization_def _ hp]
  exact carry_dominance p m k hp hpk

/-- Carry dominance implies the p-part of `C(m+k,k)` divides the p-part of `C(2m,m)`. -/
lemma carry_dominance_dvd (p m k : ℕ) (hp : Nat.Prime p) (hpk : 2 * k < p) :
    p ^ ((m + k).choose k).factorization p ∣ p ^ ((2 * m).choose m).factorization p :=
  Nat.pow_dvd_pow p (carry_dominance p m k hp hpk)

end OpenLemma.BinomialDivisibility
