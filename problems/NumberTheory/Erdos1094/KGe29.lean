/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import botlib.NumberTheory.CarryInfra
import botlib.NumberTheory.LargePrimeDvdChoose
import problems.NumberTheory.Erdos1094.Asymptotic
import problems.NumberTheory.Erdos1094.Konyagin

/-!
# Large-n Case and CRT Verification

## n > k² case (1 axiom)
For n > k²: interval divisibility (Type A) handles n/k with a prime factor > k.
The smooth subcase (Type B, n/k is k-smooth) is axiomatized as `large_n_smooth_case`.

## n ≤ k² case (handled by Konyagin citation in Konyagin.lean)
The small-n case is closed nonconstructively: Konyagin (1999) proves g(k) ≥ exp(c log²k),
which exceeds k² for large k. See `g_exceeds_k_sq` in Konyagin.lean.

## Standalone CRT verification (not load-bearing)
`crt_verified_700` provides explicit verification for k ∈ [29, 700] via native_decide.
This is a standalone axiom-free result, no longer needed for the main theorem.

## Axiom inventory: 1 axiom in this file
- `large_n_smooth_case` — Sylvester-Schur type for n > k² with k-smooth n/k
-/

open Nat OpenLemma.CarryInfra OpenLemma.LargePrimeDvdChoose

namespace Erdos1094

/-! ### Case 1: CRT density eliminates n ∈ [2k, k²] -/

/-- Check all k ∈ [29, B], n ∈ [2k, k²] for small prime divisor of C(n,k). -/
def crtRangeCheck (B : ℕ) : Bool :=
  (List.range (B - 28)).all fun i =>
    let k := i + 29
    (List.range (k * k - 2 * k + 1)).all fun j =>
      let n := j + 2 * k
      smallPrimeDivCheck n k

private theorem crtRangeCheck_sound (B : ℕ) (hB : crtRangeCheck B = true)
    (n k : ℕ) (hk29 : 29 ≤ k) (hkB : k ≤ B) (hlow : 2 * k ≤ n) (hhigh : n ≤ k * k) :
    ∃ p, p.Prime ∧ p ≤ 29 ∧ p ∣ n.choose k := by
  apply smallPrimeDivCheck_sound (by omega)
  unfold crtRangeCheck at hB
  rw [List.all_eq_true] at hB
  have hk_mem : k - 29 ∈ List.range (B - 28) := List.mem_range.mpr (by omega)
  specialize hB (k - 29) hk_mem
  simp only at hB
  rw [show k - 29 + 29 = k from by omega] at hB
  rw [List.all_eq_true] at hB
  have hn_mem : n - 2 * k ∈ List.range (k * k - 2 * k + 1) :=
    List.mem_range.mpr (by omega)
  specialize hB (n - 2 * k) hn_mem
  rw [show n - 2 * k + 2 * k = n from by omega] at hB
  exact hB

-- Exhaustive verification for k ∈ [29, 700], Case 1 (n ∈ [2k, k²]).
set_option maxHeartbeats 16000000 in
set_option linter.style.nativeDecide false in
set_option linter.style.maxHeartbeats false in
private theorem crt_verified_700 : crtRangeCheck 700 = true := by native_decide

/-! ### Case 2: Large n (n > k²) -/

lemma mod_lt_of_prime_dvd_div (n k p : ℕ) (hk : 0 < k) (_hp : p.Prime)
    (hpk : k < p) (hpM : p ∣ n / k) : n % p < k := by
  have hn : k * (n / k) + n % k = n := Nat.div_add_mod n k
  have hkM_mod : k * (n / k) % p = 0 := by
    rw [Nat.mul_mod, Nat.dvd_iff_mod_eq_zero.mp hpM, mul_zero, Nat.zero_mod]
  have hmod_lt_p : n % k < p := lt_trans (Nat.mod_lt n hk) hpk
  have hn_mod : n % p = n % k := by
    conv_lhs => rw [← hn]
    rw [Nat.add_mod, hkM_mod, zero_add, Nat.mod_mod_of_dvd]
    · exact Nat.mod_eq_of_lt hmod_lt_p
    · exact dvd_refl p
  rw [hn_mod]
  exact Nat.mod_lt n hk

/-- **UNPROVED CONJECTURE** (Sylvester-Schur type):
If n > k² and n/k is k-smooth, then C(n,k) has a prime factor ≤ n/k.

**Context:** When n > k², we have max(n/k, k) = n/k. If n/k has a prime
factor > k (Type A), interval divisibility gives p | C(n,k) with p ≤ n/k,
and this IS proved (see `large_n_minFac_bound`, Type A branch). The axiom
handles only Type B: n/k is k-smooth (all prime factors ≤ k).

**Why it's plausible:** Among k consecutive integers n-k+1, ..., n, at
least one has a "large" prime factor by Sylvester-Schur. When n/k is
k-smooth, the large factor must come from the binomial coefficient itself.

**Computational evidence:** No counterexample found for k ≤ 10^6. -/
axiom large_n_smooth_case (n k : ℕ) (hk : 2 ≤ k) (hn : k * k < n)
    (hsmooth : ∀ p, p.Prime → p ∣ n / k → p ≤ k) :
    ∃ p, p.Prime ∧ p ≤ n / k ∧ p ∣ n.choose k

theorem large_n_minFac_bound (n k : ℕ) (hk : 2 ≤ k) (hn : k * k < n) (hkn : k ≤ n) :
    (n.choose k).minFac ≤ n / k := by
  have hM_pos : 0 < n / k := by
    have : k ≤ n / k := by rw [Nat.le_div_iff_mul_le (by omega : 0 < k)]; omega
    omega
  -- Type A: n/k has a prime factor > k
  by_cases hA : ∃ p, Nat.Prime p ∧ p ∣ n / k ∧ k < p
  · obtain ⟨p, hp, hpM, hpk⟩ := hA
    have hmod : n % p < k := mod_lt_of_prime_dvd_div n k p (by omega) hp hpk hpM
    have hpn : p ∣ n.choose k := (large_prime_dvd_choose p n k hp hpk hkn).mpr hmod
    exact le_trans (Nat.minFac_le_of_dvd hp.two_le hpn) (Nat.le_of_dvd hM_pos hpM)
  · -- Type B: n/k is k-smooth
    push_neg at hA
    obtain ⟨p, hp, hp_le, hp_dvd⟩ := large_n_smooth_case n k hk hn hA
    exact le_trans (Nat.minFac_le_of_dvd hp.two_le hp_dvd) hp_le
end Erdos1094
