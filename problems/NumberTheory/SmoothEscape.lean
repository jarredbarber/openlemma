import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Tendsto
import botlib.NumberTheory.Zsygmondy

/-!
# Smooth Escape Lemma (Erdős Problem 410)

For any integer n ≥ 2 and any finite set S of primes, the σ-orbit
a₀ = n, a_{k+1} = σ₁(aₖ) is NOT eventually S-smooth.

## Status

🟡 Axiom-dependent — complete with one citation axiom (Zsygmondy's theorem).
The open work is to eliminate the axiom by proving Zsygmondy from first principles.

## Background

This is a sub-result towards Erdős Problem 410, which conjectures that
σ(aₖ)/aₖ → ∞ for the iterated sum-of-divisors orbit. The smooth escape
lemma shows that the orbit cannot stay within any finite set of primes,
which is a necessary (but not sufficient) condition for ratio divergence.

## Proof outline

1. The orbit diverges to infinity (σ₁(n) ≥ n+1 for n ≥ 2).
2. S-smooth numbers with bounded exponents are bounded.
3. So some exponent must grow without bound.
4. By pigeonhole on the finite set S, one fixed prime p₀ has unbounded exponent.
5. By Zsygmondy's theorem, for large exponent e, p₀^(e+1) - 1 has a primitive
   prime divisor q with q ≥ e+2.
6. This q divides σ₁(p₀^e) | σ₁(aₖ) = a_{k+1}.
7. But a_{k+1} is S-smooth, so q ∈ S. Since q → ∞, contradiction.

## Citation axiom

Zsygmondy's theorem (1892) is well-established but not yet in Mathlib.
The m ≥ 7 bound avoids all known exceptions. Statement verified by a human
against the original source.

References:
- K. Zsygmondy, "Zur Theorie der Potenzreste," Monatsh. Math. 3 (1892), 265–284.
- G. D. Birkhoff and H. S. Vandiver, "On the integral divisors of aⁿ − bⁿ,"
  Annals of Mathematics 5 (1904), 173–180.

## Provenance

Originally proved by LLM agents (Gemini 3 Pro) with zero human mathematical
input. 279 lines Lean + 100 lines helpers.
-/

open ArithmeticFunction Filter Nat Finset

-- ============================================================================
-- § Helpers: σ₁ growth bounds and orbit divergence
-- ============================================================================

namespace OpenLemma.SmoothEscape.Helpers

/-- For n ≥ 2, σ₁(n) ≥ n + 1 (since 1 and n are always divisors). -/
lemma sigma_one_ge (n : ℕ) (hn : 2 ≤ n) : n + 1 ≤ sigma 1 n := by
  rw [sigma_one_apply]
  have h1n : (1 : ℕ) ≠ n := by omega
  have h1_mem : 1 ∈ n.divisors := Nat.one_mem_divisors.mpr (by omega)
  have hn_mem : n ∈ n.divisors := Nat.mem_divisors.mpr ⟨dvd_refl n, by omega⟩
  have hsub : ({1, n} : Finset ℕ) ⊆ n.divisors := by
    rw [Finset.insert_subset_iff]
    exact ⟨h1_mem, Finset.singleton_subset_iff.mpr hn_mem⟩
  have hpair : ∑ d ∈ ({1, n} : Finset ℕ), (d : ℕ) = 1 + n := Finset.sum_pair h1n
  have hle : ∑ d ∈ ({1, n} : Finset ℕ), (d : ℕ) ≤ ∑ d ∈ n.divisors, d :=
    Finset.sum_le_sum_of_subset (f := fun (d : ℕ) => d) hsub
  linarith

/-- Helper: the k-th iterate of σ₁ applied to n is at least n + k. -/
private lemma iterate_sigma_one_ge (n : ℕ) (hn : 2 ≤ n) (k : ℕ) :
    n + k ≤ (sigma 1)^[k] n := by
  induction k with
  | zero => simp [Function.iterate_zero_apply]
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have hge2 : 2 ≤ (sigma 1)^[k] n := by omega
    have := sigma_one_ge ((sigma 1)^[k] n) hge2
    omega

/-- For n ≥ 2, the iterated σ₁ sequence tends to infinity. -/
lemma sigma_one_iterate_tendsto_atTop (n : ℕ) (hn : 2 ≤ n) :
    Tendsto (fun k => (sigma 1)^[k] n) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  use b
  intro a ha
  have := iterate_sigma_one_ge n hn a
  omega

end OpenLemma.SmoothEscape.Helpers

-- ============================================================================
-- § Smooth Escape
-- ============================================================================

namespace OpenLemma.SmoothEscape

/-- A natural number n is S-smooth if every prime factor of n lies in S. -/
def IsSmooth (S : Finset ℕ) (n : ℕ) : Prop :=
  ∀ p, p.Prime → p ∣ n → p ∈ S

/-- The orbit is eventually S-smooth if there exists K such that
    all iterates aₖ for k ≥ K are S-smooth. -/
def EventuallySmooth (S : Finset ℕ) (n : ℕ) : Prop :=
  ∃ K, ∀ k, K ≤ k → IsSmooth S ((sigma 1)^[k] n)

-- Zsygmondy's theorem imported from botlib.NumberTheory.Zsygmondy
-- Proving it from Mathlib primitives would promote SmoothEscape to 🟢 axiom-free.
open OpenLemma.Zsygmondy

-- ============================================================================
-- § Number theory helpers
-- ============================================================================

lemma sub_one_mul_sigma_prime_pow (p m : ℕ) (hp : p.Prime) (hm : 1 ≤ m) :
    (p - 1) * sigma 1 (p ^ (m - 1)) = p ^ m - 1 := by
  have h1 : sigma 1 (p ^ (m - 1)) = (p ^ m - 1) / (p - 1) := by
    rw [sigma_one_apply_prime_pow hp, show m - 1 + 1 = m from by omega]
    exact Nat.geomSum_eq hp.two_le m
  rw [h1]
  exact Nat.mul_div_cancel' (Nat.sub_one_dvd_pow_sub_one p m)

lemma prime_dvd_sigma_of_dvd_pow_sub_one (p m q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hm : 1 ≤ m) (hdvd : q ∣ p ^ m - 1) (hndvd : ¬(q ∣ p - 1)) :
    q ∣ sigma 1 (p ^ (m - 1)) := by
  have h := sub_one_mul_sigma_prime_pow p m hp hm
  rw [← h] at hdvd
  exact (hq.dvd_mul.mp hdvd).resolve_left hndvd

lemma sigma_one_prime_pow_dvd (n : ℕ) (hn : n ≠ 0) (p : ℕ) (hp : p.Prime) :
    sigma 1 (p ^ n.factorization p) ∣ sigma 1 n := by
  set e := n.factorization p
  set m := n / p ^ e
  have hmul : p ^ e * m = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hcop : (p ^ e).gcd m = 1 :=
    (Nat.coprime_ordCompl hp hn).pow_left e
  conv_rhs => rw [← hmul]
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop]
  exact dvd_mul_right _ _

lemma zsygmondy_prime_dvd_sigma (n p : ℕ) (hp : p.Prime) (hn : n ≠ 0)
    (he : 7 ≤ n.factorization p + 1) :
    ∃ q, q.Prime ∧ q ∣ sigma 1 n ∧ n.factorization p + 2 ≤ q := by
  set e := n.factorization p with he_def
  set m := e + 1
  obtain ⟨q, hqp, hqdvd, hqprim, hqge⟩ := zsygmondy_prime_pow p m hp he
  have hq_not_dvd_pm1 : ¬(q ∣ p - 1) := by
    have := hqprim 1 le_rfl (by omega : 1 < m)
    simpa [pow_one] using this
  have hq_dvd_sigma_pow : q ∣ sigma 1 (p ^ e) :=
    prime_dvd_sigma_of_dvd_pow_sub_one p m q hp hqp (by omega) hqdvd hq_not_dvd_pm1
  have hq_dvd_sigma_n : q ∣ sigma 1 n :=
    dvd_trans hq_dvd_sigma_pow (sigma_one_prime_pow_dvd n hn p hp)
  exact ⟨q, hqp, hq_dvd_sigma_n, by omega⟩

-- ============================================================================
-- § Orbit helpers
-- ============================================================================

lemma iterate_ge_two (n : ℕ) (hn : 2 ≤ n) (k : ℕ) : 2 ≤ (sigma 1)^[k] n := by
  induction k with
  | zero => simp only [Function.iterate_zero, id_eq]; exact hn
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have := OpenLemma.SmoothEscape.Helpers.sigma_one_ge ((sigma 1)^[k] n) ih
    omega

lemma iterate_ne_zero (n : ℕ) (hn : 2 ≤ n) (k : ℕ) : (sigma 1)^[k] n ≠ 0 := by
  have := iterate_ge_two n hn k; omega

lemma iterate_ne_one (n : ℕ) (hn : 2 ≤ n) (k : ℕ) : (sigma 1)^[k] n ≠ 1 := by
  have := iterate_ge_two n hn k; omega

-- ============================================================================
-- § Smooth number bounds and exponent growth
-- ============================================================================

lemma isSmooth_iff {S : Finset ℕ} {n : ℕ} (hn : n ≠ 0) :
    IsSmooth S n ↔ n.primeFactors ⊆ S := by
  constructor
  · intro h p hp
    exact h p (Nat.mem_primeFactors.mp hp).1 (Nat.mem_primeFactors.mp hp).2.1
  · intro h p hp hdvd
    exact h (Nat.mem_primeFactors.mpr ⟨hp, hdvd, hn⟩)

lemma smooth_bounded (S : Finset ℕ) (n : ℕ) (hn : n ≠ 0) (E : ℕ)
    (hSprimes : ∀ p ∈ S, p.Prime)
    (hsmooth : n.primeFactors ⊆ S)
    (hexp : ∀ p ∈ S, n.factorization p ≤ E) :
    n ≤ ∏ p ∈ S, p ^ E := by
  rw [← Nat.factorization_prod_pow_eq_self hn]
  calc ∏ p ∈ n.primeFactors, p ^ n.factorization p
      ≤ ∏ p ∈ S, p ^ n.factorization p := by
        apply Finset.prod_le_prod_of_subset_of_one_le' hsmooth
        intro p _ _
        exact Nat.one_le_pow _ _ (hSprimes p (by assumption)).pos
    _ ≤ ∏ p ∈ S, p ^ E := by
        apply Finset.prod_le_prod (fun p _ => Nat.zero_le _)
        intro p hp
        exact Nat.pow_le_pow_right (hSprimes p hp).pos (hexp p hp)

lemma exponent_growth (n : ℕ) (hn : 2 ≤ n) (S : Finset ℕ) (K : ℕ)
    (hSprimes : ∀ p ∈ S, p.Prime)
    (hK : ∀ k, K ≤ k → IsSmooth S ((sigma 1)^[k] n)) :
    ∀ E : ℕ, ∃ p ∈ S, ∃ k, K ≤ k ∧ E < ((sigma 1)^[k] n).factorization p := by
  by_contra hc
  push_neg at hc
  obtain ⟨E, hE⟩ := hc
  set B := ∏ p ∈ S, p ^ E
  have hbound : ∀ k, K ≤ k → (sigma 1)^[k] n ≤ B := by
    intro k hk
    have hne := iterate_ne_zero n hn k
    have hsmooth := (isSmooth_iff hne).mp (hK k hk)
    exact smooth_bounded S _ hne E hSprimes hsmooth (fun p hp => hE p hp k hk)
  have hdiv := OpenLemma.SmoothEscape.Helpers.sigma_one_iterate_tendsto_atTop n hn
  rw [tendsto_atTop_atTop] at hdiv
  obtain ⟨N, hN⟩ := hdiv (B + 1)
  have hle := hbound (max K N) (le_max_left K N)
  have hge := hN (max K N) (le_max_right K N)
  omega

-- ============================================================================
-- § Pigeonhole
-- ============================================================================

lemma finset_pigeonhole (S : Finset ℕ) (hS : S.Nonempty)
    (P : ℕ → ℕ → Prop)
    (h : ∀ n, ∃ s ∈ S, P n s) :
    ∃ s ∈ S, ∀ n, ∃ m, n ≤ m ∧ P m s := by
  by_contra hc
  push_neg at hc
  have htotal : ∀ s, ∃ Ns, s ∈ S → ∀ m, Ns ≤ m → ¬P m s := by
    intro s
    by_cases hs : s ∈ S
    · obtain ⟨Ns, hNs⟩ := hc s hs
      exact ⟨Ns, fun _ => hNs⟩
    · exact ⟨0, fun h => absurd h hs⟩
  choose N hN using htotal
  set N₀ := S.sup' hS N
  obtain ⟨s, hsS, hPs⟩ := h N₀
  exact (hN s) hsS N₀ (Finset.le_sup' N hsS) hPs

-- ============================================================================
-- § Main theorem
-- ============================================================================

/-- **Smooth escape lemma**: The σ₁-orbit of any n ≥ 2 is not eventually S-smooth
    for any finite set S of primes.

    The only non-Mathlib dependency is `zsygmondy_prime_pow` (citation axiom). -/
theorem orbit_not_eventually_smooth (n : ℕ) (hn : 2 ≤ n) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) :
    ¬EventuallySmooth S n := by
  intro ⟨K, hK⟩
  by_cases hSe : S.Nonempty
  · have hgrowth := exponent_growth n hn S K hS hK
    obtain ⟨p₀, hp₀S, hunb⟩ := finset_pigeonhole S hSe
      (fun E p => ∃ k, K ≤ k ∧ E < ((sigma 1)^[k] n).factorization p)
      hgrowth
    have hp₀ : p₀.Prime := hS p₀ hp₀S
    set E₀ := max 6 (S.max' hSe)
    obtain ⟨E, hEge, k, hkK, hfact⟩ := hunb E₀
    have hak_ne : (sigma 1)^[k] n ≠ 0 := iterate_ne_zero n hn k
    have he_ge : 7 ≤ ((sigma 1)^[k] n).factorization p₀ + 1 := by omega
    obtain ⟨q, hqprime, hqdvd, hqge⟩ :=
      zsygmondy_prime_dvd_sigma ((sigma 1)^[k] n) p₀ hp₀ hak_ne he_ge
    have hiter : (sigma 1)^[k + 1] n = sigma 1 ((sigma 1)^[k] n) :=
      Function.iterate_succ_apply' (sigma 1) k n
    rw [← hiter] at hqdvd
    have hsmooth : IsSmooth S ((sigma 1)^[k + 1] n) := hK (k + 1) (by omega)
    have hqS : q ∈ S := hsmooth q hqprime hqdvd
    have hqbig : S.max' hSe < q := by
      have : S.max' hSe ≤ E₀ := le_max_right _ _
      omega
    exact absurd (Finset.le_max' S q hqS) (not_le.mpr hqbig)
  · rw [Finset.not_nonempty_iff_eq_empty] at hSe
    have hsmooth : IsSmooth S ((sigma 1)^[K] n) := hK K le_rfl
    rw [hSe] at hsmooth
    have ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (iterate_ne_one n hn K)
    exact absurd (hsmooth p hp hpdvd) (by simp)

end OpenLemma.SmoothEscape
