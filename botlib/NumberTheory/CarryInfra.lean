/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Provenance: Originally proved by LLM agents (Claude, Anthropic) working on
Erdős Problem 1094, with zero human mathematical input.
Trust level: 🟢 Compiler-verified (zero sorrys, zero axioms).
-/
import botlib.NumberTheory.Kummer

/-!
# Carry-based divisibility infrastructure

Decidable checks for whether small primes divide binomial coefficients,
using Kummer's digit-domination criterion. Useful for computational
verification of divisibility properties of C(n,k).

## Main Results

* `hasCarry` — computable check for digit-domination failure
* `hasCarry_dvd_choose` — soundness: hasCarry implies prime divides C(n,k)
* `smallPrimeDivCheck` — checks all primes ≤ 29
* `smallPrimeDivCheck_sound` — soundness of the above
-/

open Nat

namespace OpenLemma.CarryInfra

/-- Returns `true` iff digit-domination fails, i.e., `p ∣ C(n, k)` by Kummer's criterion.
Recurses on `k`, dividing both `k` and `n` by `p` at each step. -/
def hasCarry (p k n : ℕ) : Bool :=
  if k = 0 then false
  else if p ≤ 1 then false
  else k % p > n % p || hasCarry p (k / p) (n / p)
termination_by k
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- `hasCarry` detects a digit violation: if it returns `true`, then there exists
a position `i` where the base-`p` digit of `k` exceeds that of `n`. -/
theorem hasCarry_imp_digit_violation (hp : 2 ≤ p) :
    ∀ k n, hasCarry p k n = true → ∃ i, k / p ^ i % p > n / p ^ i % p := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro n
    unfold hasCarry
    split
    · simp
    · rename_i hk
      split
      · intro h; simp at h
      · simp only [Bool.or_eq_true]
        intro h
        rcases h with h | h
        · exact ⟨0, by simpa using h⟩
        · obtain ⟨i, hi⟩ := ih (k / p) (Nat.div_lt_self (by omega) (by omega)) (n / p) h
          exact ⟨i + 1, by rwa [pow_succ, mul_comm, ← Nat.div_div_eq_div_mul,
                                  ← Nat.div_div_eq_div_mul]⟩

/-- Completeness: `hasCarry` detects all digit violations. -/
theorem hasCarry_complete {p : ℕ} (hp : 2 ≤ p) :
    ∀ k n, (∃ i, k / p ^ i % p > n / p ^ i % p) → hasCarry p k n = true := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro n h
    obtain ⟨i, hi⟩ := h
    unfold hasCarry
    split
    · subst k; simp [Nat.zero_div, Nat.zero_mod] at hi
    · split
      · omega
      · simp only [Bool.or_eq_true]
        by_cases h0 : k % p > n % p
        · left; simp [h0]
        · right
          cases i with
          | zero => simp at hi; contradiction
          | succ i =>
            apply ih (k / p) (Nat.div_lt_self (by omega) (by omega)) (n / p)
            use i
            rwa [pow_succ, mul_comm, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul] at hi

/-- Soundness: `hasCarry p k n = true` implies `p ∣ C(n, k)` for prime `p`. -/
theorem hasCarry_dvd_choose {p n k : ℕ} (hp : Nat.Prime p) (hkn : k ≤ n)
    (h : hasCarry p k n = true) : p ∣ n.choose k := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [OpenLemma.Kummer.kummer_criterion p n k hkn]
  simp_rw [Nat.getD_digits _ _ hp.two_le]
  exact hasCarry_imp_digit_violation hp.two_le k n h

/-- Returns `true` if digit-domination fails for some prime `p ≤ 29`,
meaning that prime divides `C(n, k)` by Kummer's criterion. -/
def smallPrimeDivCheck (n k : ℕ) : Bool :=
  hasCarry 2 k n || hasCarry 3 k n || hasCarry 5 k n || hasCarry 7 k n ||
  hasCarry 11 k n || hasCarry 13 k n || hasCarry 17 k n || hasCarry 19 k n ||
  hasCarry 23 k n || hasCarry 29 k n

/-- Soundness: `smallPrimeDivCheck` implies existence of a small prime divisor. -/
theorem smallPrimeDivCheck_sound {n k : ℕ} (hkn : k ≤ n)
    (h : smallPrimeDivCheck n k = true) :
    ∃ p, p.Prime ∧ p ≤ 29 ∧ p ∣ n.choose k := by
  unfold smallPrimeDivCheck at h
  simp only [Bool.or_eq_true] at h
  rcases h with ((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h
  all_goals first
  | exact ⟨2, by norm_num, by omega, hasCarry_dvd_choose (by norm_num) hkn h⟩
  | exact ⟨3, by norm_num, by omega, hasCarry_dvd_choose (by norm_num) hkn h⟩
  | exact ⟨5, by norm_num, by omega, hasCarry_dvd_choose (by norm_num) hkn h⟩
  | exact ⟨7, by norm_num, by omega, hasCarry_dvd_choose (by norm_num) hkn h⟩
  | exact ⟨11, by norm_num, by omega, hasCarry_dvd_choose (by norm_num) hkn h⟩
  | exact ⟨13, by norm_num, by omega, hasCarry_dvd_choose (by norm_num) hkn h⟩
  | exact ⟨17, by norm_num, by omega, hasCarry_dvd_choose (by norm_num) hkn h⟩
  | exact ⟨19, by norm_num, by omega, hasCarry_dvd_choose (by norm_num) hkn h⟩
  | exact ⟨23, by norm_num, by omega, hasCarry_dvd_choose (by norm_num) hkn h⟩
  | exact ⟨29, by norm_num, by omega, hasCarry_dvd_choose (by norm_num) hkn h⟩

end OpenLemma.CarryInfra
