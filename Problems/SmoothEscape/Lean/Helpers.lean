import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Tendsto

open ArithmeticFunction Filter

namespace Erdos410

/-! ## Helper lemmas for σ bounds

These lemmas establish lower bounds on the growth of the sum-of-divisors function.
They form the key building blocks for the main Erdős 410 theorem.

### Key facts used:
- `sigma_apply`: `σ k n = ∑ d ∈ divisors n, d ^ k`
- `sigma_one_apply`: `σ 1 n = ∑ d ∈ divisors n, d`
- `sigma_pos`: `0 < σ k n` when `n ≠ 0`
- `isMultiplicative_sigma`: `σ k` is multiplicative
-/

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

/-- For even n ≥ 2, σ₁(n) ≥ 3n/2 (since 1, n/2, and n are all divisors).
    Stated as `3 * n ≤ 2 * σ₁(n)` to avoid natural number division. -/
lemma sigma_one_even_ge (n : ℕ) (hn : 2 ≤ n) (heven : Even n) :
    3 * n ≤ 2 * sigma 1 n := by
  by_cases hn2 : n = 2
  · subst hn2; decide
  · -- For n ≥ 4 even, extract three distinct divisors: 1, n/2, n
    have h2dvd : 2 ∣ n := even_iff_two_dvd.mp heven
    obtain ⟨k, hk⟩ := heven
    have hn4 : 4 ≤ n := by omega
    rw [sigma_one_apply]
    have h1_mem : 1 ∈ n.divisors := Nat.one_mem_divisors.mpr (by omega)
    have hndiv2_mem : n / 2 ∈ n.divisors :=
      Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd h2dvd, by omega⟩
    have hn_mem : n ∈ n.divisors := Nat.mem_divisors.mpr ⟨dvd_refl n, by omega⟩
    have hsub : ({1, n / 2, n} : Finset ℕ) ⊆ n.divisors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact h1_mem
      · exact hndiv2_mem
      · exact hn_mem
    have hle : ∑ d ∈ ({1, n / 2, n} : Finset ℕ), (d : ℕ) ≤ ∑ d ∈ n.divisors, d :=
      Finset.sum_le_sum_of_subset hsub
    have hnotin1 : (1 : ℕ) ∉ ({n / 2, n} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have hnotin2 : n / 2 ∉ ({n} : Finset ℕ) := by
      simp only [Finset.mem_singleton]; omega
    rw [Finset.sum_insert hnotin1, Finset.sum_insert hnotin2, Finset.sum_singleton] at hle
    -- hle : 1 + (n / 2 + n) ≤ ∑ d ∈ n.divisors, d
    -- Goal: 3 * n ≤ 2 * ∑ d ∈ n.divisors, d
    omega

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

/-- For n ≥ 2, the iterated σ₁ sequence tends to infinity.
    This is a key intermediate result: since σ₁(n) ≥ n + 1 for n ≥ 2,
    the iterates are strictly increasing and unbounded. -/
lemma sigma_one_iterate_tendsto_atTop (n : ℕ) (hn : 2 ≤ n) :
    Tendsto (fun k => (sigma 1)^[k] n) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  use b
  intro a ha
  have := iterate_sigma_one_ge n hn a
  omega

end Erdos410
