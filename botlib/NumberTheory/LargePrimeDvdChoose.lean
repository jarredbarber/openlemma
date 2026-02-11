/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Provenance: Originally proved by LLM agents (Claude, Anthropic) working on
Erdős Problem 1094, with zero human mathematical input.
Trust level: 🟢 Compiler-verified (zero sorrys, zero axioms).
-/
import Mathlib

/-!
# Large Prime Divisibility Criterion for Binomial Coefficients

When a prime `p` is larger than `k`, divisibility of `C(n, k)` by `p` is characterized
by a simple modular condition: `p ∣ C(n, k) ↔ n % p < k`.

This is a direct corollary of Lucas' theorem, since `k < p` means `k` is a single
base-`p` digit, collapsing the product to a single factor.

## Main Results

* `large_prime_dvd_choose`: For prime `p > k` with `k ≤ n`,
  `p ∣ C(n, k) ↔ n % p < k`.

## References

* Lucas, É. (1878). "Théorie des fonctions numériques simplement périodiques."
  American Journal of Mathematics, 1(2), 184–196.
-/

open Nat

namespace OpenLemma.LargePrimeDvdChoose

private lemma prime_dvd_choose_of_lt (p a b : ℕ) (hp : p.Prime) (ha : a < p) :
    p ∣ a.choose b ↔ a < b := by
  constructor
  · intro hdvd
    by_contra h
    push_neg at h
    have hpos : 0 < a.choose b := Nat.choose_pos h
    have hfact : (a.choose b).factorization p = 0 :=
      Nat.factorization_choose_eq_zero_of_lt ha
    have h1 := (hp.dvd_iff_one_le_factorization hpos.ne').mp hdvd
    omega
  · intro h
    rw [Nat.choose_eq_zero_of_lt h]
    exact dvd_zero p

private lemma modEq_dvd_iff {a b p : ℕ} (h : a ≡ b [MOD p]) : p ∣ a ↔ p ∣ b := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero]
  exact h ▸ Iff.rfl

/-- **Large prime divisibility criterion**: For a prime `p > k` with `k ≤ n`,
`p ∣ C(n, k)` if and only if `n mod p < k`.

This is the special case of Kummer's digit-domination criterion when `k` has
only a single base-`p` digit. The condition `n % p < k` is equivalent to saying
that the interval `{n-k+1, ..., n}` contains a multiple of `p`. -/
theorem large_prime_dvd_choose (p n k : ℕ) (hp : p.Prime) (hpk : k < p) (_hkn : k ≤ n) :
    p ∣ n.choose k ↔ n % p < k := by
  haveI : Fact p.Prime := ⟨hp⟩
  have lucas := @Choose.choose_modEq_choose_mod_mul_choose_div_nat n k p _
  rw [Nat.mod_eq_of_lt hpk, Nat.div_eq_of_lt hpk, Nat.choose_zero_right, mul_one] at lucas
  rw [modEq_dvd_iff lucas]
  exact prime_dvd_choose_of_lt p (n % p) k hp (Nat.mod_lt n hp.pos)

end OpenLemma.LargePrimeDvdChoose
