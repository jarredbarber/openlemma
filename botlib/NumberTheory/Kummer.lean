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

end OpenLemma.Kummer
