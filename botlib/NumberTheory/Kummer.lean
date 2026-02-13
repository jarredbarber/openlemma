/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Provenance: Originally proved by LLM agents (Claude, Anthropic) working on
Erdős Problem 1094, with zero human mathematical input.
Trust level: 🟢 Compiler-verified (zero sorrys, zero axioms).
-/
import Mathlib

/-!
# Kummer's Theorem and the Digit-Domination Criterion

This file formalizes the digit-domination criterion for divisibility of binomial
coefficients by a prime, derived from Kummer's theorem (1852).

## Main Results

* `kummer_criterion`: `p ∣ C(n, k) ↔ ∃ i, digit_i(k) > digit_i(n)` in base `p`.
* `trailing_zero_carry`: `v_p(n) > v_p(k) → p ∣ C(n, k)`.
* `smooth_n_has_small_factor`: If `n` is `k`-smooth and `n > k`, then `∃ p ≤ k, p | C(n, k)`.
* `divisible_smooth_quotient_has_small_factor`: If `k | n` and `n/k` is `k`-smooth, same conclusion.

The proof strategy uses Lucas' theorem (already in Mathlib as
`Choose.choose_modEq_choose_mod_mul_choose_div_nat`) combined with strong induction.

## References

* Kummer, E.E. (1852). "Über die Ergänzungssätze zu den allgemeinen Reciprocitätsgesetzen."
  Journal für die reine und angewandte Mathematik, 44, 93–146.
* Lucas, É. (1878). "Théorie des fonctions numériques simplement périodiques."
  American Journal of Mathematics, 1(2), 184–196.
-/

open Nat Finset

namespace OpenLemma.Kummer

variable {p : ℕ} [hp : Fact p.Prime]

private theorem pp : p.Prime := hp.out

private lemma prime_dvd_choose_small (a b : ℕ) (ha : a < p) :
    p ∣ a.choose b ↔ a < b := by
  constructor
  · intro hdvd
    by_contra h
    push_neg at h
    have hpos : 0 < a.choose b := Nat.choose_pos h
    have hfact : (a.choose b).factorization p = 0 :=
      Nat.factorization_choose_eq_zero_of_lt ha
    have h1 := (pp.dvd_iff_one_le_factorization hpos.ne').mp hdvd
    omega
  · intro h
    rw [Nat.choose_eq_zero_of_lt h]
    exact dvd_zero p

private lemma div_pow_succ_mod {p : ℕ} (n i : ℕ) :
    n / p ^ (i + 1) % p = n / p / p ^ i % p := by
  rw [pow_succ, mul_comm, ← Nat.div_div_eq_div_mul]

private lemma digit_violation_iff_or {p : ℕ} [_hp : Fact p.Prime] (n k : ℕ) :
    (∃ i, k / p ^ i % p > n / p ^ i % p) ↔
    (k % p > n % p ∨ ∃ i, (k / p) / p ^ i % p > (n / p) / p ^ i % p) := by
  constructor
  · rintro ⟨i, hi⟩
    cases i with
    | zero => left; simpa using hi
    | succ i =>
      right
      exact ⟨i, by rwa [div_pow_succ_mod, div_pow_succ_mod] at hi⟩
  · rintro (h | ⟨i, hi⟩)
    · exact ⟨0, by simpa using h⟩
    · exact ⟨i + 1, by rwa [div_pow_succ_mod, div_pow_succ_mod]⟩

private theorem kummer_criterion_core :
    ∀ n k : ℕ, k ≤ n → (p ∣ n.choose k ↔ ∃ i, k / p ^ i % p > n / p ^ i % p) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro k hkn
    rcases n.eq_zero_or_pos with rfl | hn
    · have hk0 : k = 0 := Nat.le_zero.mp hkn
      subst hk0
      simp only [choose_self, dvd_one, Nat.zero_div, zero_mod, gt_iff_lt,
        lt_self_iff_false, exists_const, iff_false, ne_eq]
      exact pp.one_lt.ne'
    rw [Choose.choose_modEq_choose_mod_mul_choose_div_nat.dvd_iff dvd_rfl,
        pp.dvd_mul, digit_violation_iff_or]
    constructor
    · rintro (h1 | h2)
      · left; exact (prime_dvd_choose_small _ _ (Nat.mod_lt n pp.pos)).mp h1
      · right; exact (ih (n / p) (Nat.div_lt_self hn pp.one_lt) (k / p)
                        (Nat.div_le_div_right hkn)).mp h2
    · rintro (h1 | ⟨i, hi⟩)
      · left; exact (prime_dvd_choose_small _ _ (Nat.mod_lt n pp.pos)).mpr h1
      · right; exact (ih (n / p) (Nat.div_lt_self hn pp.one_lt) (k / p)
                        (Nat.div_le_div_right hkn)).mpr ⟨i, hi⟩

/-- **Kummer's digit-domination criterion**: A prime `p` divides `C(n, k)` if and only if
some base-`p` digit of `k` exceeds the corresponding base-`p` digit of `n`.

This is equivalent to Kummer's theorem (1852): the `p`-adic valuation of `C(n, k)` equals
the number of carries when adding `k` and `n - k` in base `p`. The divisibility criterion
is the special case: `p ∣ C(n, k) ↔ number of carries > 0 ↔ digit domination fails`. -/
theorem kummer_criterion (p : ℕ) [Fact p.Prime] (n k : ℕ) (hk : k ≤ n) :
    p ∣ n.choose k ↔ ∃ i, (Nat.digits p k).getD i 0 > (Nat.digits p n).getD i 0 := by
  have h2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  simp_rw [Nat.getD_digits _ _ h2]
  exact kummer_criterion_core n k hk


/-! ## ELS93 Lemma 3: Prime divisibility at multiples -/

/-- If p | r and m > 0, then some base-p digit of m exceeds that of r*m. -/
private lemma digit_exceeds_of_dvd (r m : ℕ) (hpr : p ∣ r) (hm : 0 < m) :
    ∃ i, m / p ^ i % p > (r * m) / p ^ i % p := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    by_cases hmp : m % p > 0
    · refine ⟨0, ?_⟩
      simp only [pow_zero, Nat.div_one]
      have : (r * m) % p = 0 := by
        rw [Nat.mul_mod, Nat.dvd_iff_mod_eq_zero.mp hpr, zero_mul, Nat.zero_mod]
      omega
    · push_neg at hmp
      have hpm : p ∣ m := Nat.dvd_of_mod_eq_zero (by omega)
      have hm_div : 0 < m / p := Nat.div_pos (le_of_dvd hm hpm) pp.pos
      have hm_lt : m / p < m := Nat.div_lt_self hm pp.one_lt
      have hrm_div : (r * m) / p = r * (m / p) := Nat.mul_div_assoc r hpm
      obtain ⟨i, hi⟩ := ih (m / p) hm_lt hm_div
      refine ⟨i + 1, ?_⟩
      simp only [pow_succ]
      rw [show p ^ i * p = p * p ^ i from by ring,
          ← Nat.div_div_eq_div_mul m p (p ^ i),
          ← Nat.div_div_eq_div_mul (r * m) p (p ^ i),
          hrm_div]
      exact hi

/-- **ELS93 Lemma 3**: If p | r and k > 0, then p | C(r·k, k).

By Kummer's criterion, since p | r, some base-p digit of k exceeds
the corresponding digit of r·k.

Reference: Erdős, Lacampagne, Selfridge (1993), Lemma 3. -/
theorem prime_dvd_choose_multiple (r k : ℕ) (hr : p ∣ r) (hk : 0 < k) :
    p ∣ (r * k).choose k := by
  rcases r with _ | r
  · simp only [zero_mul, Nat.choose_eq_zero_of_lt hk]; exact dvd_zero p
  · have hrk : k ≤ (r + 1) * k := Nat.le_mul_of_pos_left k (by omega)
    rw [kummer_criterion p ((r + 1) * k) k hrk]
    simp_rw [Nat.getD_digits _ _ pp.two_le]
    exact digit_exceeds_of_dvd (r + 1) k hr hk

/-- For r ≥ 2 and k > 0, minFac(C(r·k, k)) ≤ r. -/
theorem minFac_choose_multiple_le (r k : ℕ) (hr : 2 ≤ r) (hk : 0 < k) :
    ((r * k).choose k).minFac ≤ r := by
  have hr_mf := Nat.minFac_prime (by omega : r ≠ 1)
  have := Fact.mk hr_mf
  have h_dvd : r.minFac ∣ (r * k).choose k :=
    prime_dvd_choose_multiple r k (Nat.minFac_dvd r) hk
  calc ((r * k).choose k).minFac
      ≤ r.minFac := Nat.minFac_le_of_dvd hr_mf.two_le h_dvd
    _ ≤ r := Nat.minFac_le (by omega)

/-! ## Trailing Zero Lemma and Smooth Factor -/

/-- If v_p(n) > v_p(k) and k ≤ n and k ≠ 0, then p | C(n,k).

The base-p digit of k at position v_p(k) is nonzero (by definition of the
p-adic valuation), while the digit of n at that position is zero (since
p^(v_p(k)+1) | n). By Kummer's digit-domination criterion, p | C(n,k). -/
theorem trailing_zero_carry (n k : ℕ) (hk : k ≤ n) (hk0 : k ≠ 0)
    (hv : padicValNat p n > padicValNat p k) :
    p ∣ n.choose k := by
  set v := padicValNat p k
  -- p^(v+1) | n (since v+1 ≤ v_p(n))
  have h_pow_n : p ^ (v + 1) ∣ n := by
    rw [padicValNat_dvd_iff_le (by omega : n ≠ 0)]; omega
  have h_pv_n : p ^ v ∣ n := (pow_dvd_pow p (Nat.le_succ v)).trans h_pow_n
  -- Digit of n at position v is zero: p | n/p^v
  have hn_digit : n / p ^ v % p = 0 := by
    have : p ∣ n / p ^ v := by rwa [Nat.dvd_div_iff_mul_dvd h_pv_n, ← pow_succ]
    exact Nat.dvd_iff_mod_eq_zero.mp this
  -- Digit of k at position v is nonzero: p^(v+1) ∤ k
  have hk_digit : 0 < k / p ^ v % p := by
    rw [Nat.pos_iff_ne_zero]
    intro h_eq
    have : p ^ (v + 1) ∣ k := by
      rw [pow_succ]
      exact Nat.mul_dvd_of_dvd_div pow_padicValNat_dvd (Nat.dvd_of_mod_eq_zero h_eq)
    have := (padicValNat_dvd_iff_le hk0).mp this; omega
  -- Apply Kummer: digit domination fails at position v
  rw [kummer_criterion p n k hk]
  exact ⟨v, by simp_rw [Nat.getD_digits _ _ pp.two_le]; omega⟩

/-- If n is k-smooth (all prime factors ≤ k), n > k, and k ≥ 2,
then some prime p ≤ k divides C(n, k).

If no prime p ≤ k divided C(n,k), then v_p(n) ≤ v_p(k) for all p | n,
forcing n | k. But n > k, contradiction. -/
theorem smooth_n_has_small_factor (n k : ℕ) (hk : 2 ≤ k) (hn : k < n)
    (hsmooth : ∀ q, q.Prime → q ∣ n → q ≤ k) :
    ∃ q, q.Prime ∧ q ≤ k ∧ q ∣ n.choose k := by
  have hn0 : n ≠ 0 := by omega
  have hk0 : k ≠ 0 := by omega
  have hkn : k ≤ n := le_of_lt hn
  by_contra h_none
  push_neg at h_none
  suffices n ∣ k from absurd (Nat.le_of_dvd (by omega) this) (by omega)
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro q e hq hqe_n
  rcases e with _ | e
  · simp
  · have hq_dvd_n : q ∣ n := (dvd_pow_self q (by omega : e + 1 ≠ 0)).trans hqe_n
    have hq_le : q ≤ k := hsmooth q hq hq_dvd_n
    have hq_fact : Fact q.Prime := ⟨hq⟩
    have hv_le : padicValNat q n ≤ padicValNat q k := by
      by_contra hv_gt
      push_neg at hv_gt
      exact h_none q hq hq_le (@trailing_zero_carry q hq_fact n k hkn hk0 hv_gt)
    have he_le : e + 1 ≤ padicValNat q n :=
      (@padicValNat_dvd_iff_le q hq_fact n (e + 1) hn0).mp hqe_n
    exact (@padicValNat_dvd_iff_le q hq_fact k (e + 1) hk0).mpr (le_trans he_le hv_le)

/-- If k | n, n/k is k-smooth, n > k, and k ≥ 2, then ∃ prime p ≤ k with p | C(n,k).

Since k | n, we have n = k · (n/k). Every prime factor of n divides k or n/k,
hence is ≤ k. So n is k-smooth, and `smooth_n_has_small_factor` applies.

**Application:** This eliminates `large_n_smooth_case` (axiom 2 in KGe29.lean)
for the subcase where k | n. -/
theorem divisible_smooth_quotient_has_small_factor
    (n k : ℕ) (hk : 2 ≤ k) (hn : k < n) (hdvd : k ∣ n)
    (hsmooth : ∀ q, q.Prime → q ∣ n / k → q ≤ k) :
    ∃ q, q.Prime ∧ q ≤ k ∧ q ∣ n.choose k := by
  apply smooth_n_has_small_factor n k hk hn
  intro q hq hq_dvd
  rw [(Nat.mul_div_cancel' hdvd).symm] at hq_dvd
  rcases hq.dvd_mul.mp hq_dvd with h | h
  · exact le_of_dvd (by omega) h
  · exact hsmooth q hq h

end OpenLemma.Kummer
