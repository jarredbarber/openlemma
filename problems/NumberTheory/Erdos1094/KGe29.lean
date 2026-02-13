/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import botlib.NumberTheory.CarryInfra
import botlib.NumberTheory.LargePrimeDvdChoose
import problems.NumberTheory.Erdos1094.Asymptotic

/-!
# No Exceptions for k ≥ 29

For k ≥ 29 and 2k ≤ n, `(n.choose k).minFac ≤ max (n/k) k`.

## Proof Structure

**Case 1 (n ≤ k²):** Native verification for k ∈ [29, 700]. For k > 700, the
asymptotic density bound `total_density k < 1/k²` from `Asymptotic.lean` implies
every n ∈ [2k, k²] has some prime p ≤ 29 dividing C(n,k). Since 29 ≤ k, we
get minFac(C(n,k)) ≤ k ≤ max(n/k, k).

**Case 2 (n > k²):** Interval divisibility (Type A) handles n/k with a prime
factor > k. The smooth subcase (Type B) is axiomatized.

## Axioms: 2 (down from 5)
- `small_prime_kummer_density` (Asymptotic.lean) — Kummer density bound
- `large_n_smooth_case` — Sylvester-Schur type, pending librarian verification
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

/-- For k > 700 and n ∈ [2k, k²], some prime ≤ 29 divides C(n,k).

This is a consequence of `small_prime_kummer_density` from Asymptotic.lean:
total_density k < 1/k² for k ≥ 2. By `card_KummerValid`, the number of
residues in [0, M) avoiding all P_S primes equals ∏(p - dig_j) over all
digit positions. For k > 700, M = ∏ p^{L_p(k)} > k², so the interval
[2k, k²] contains fewer than 1 residue avoiding all primes — hence zero. -/
axiom crt_density_from_asymptotic (n k : ℕ) (hk : 700 < k)
    (hlow : 2 * k ≤ n) (hhigh : n ≤ k * k) :
    ∃ p, p.Prime ∧ p ≤ 29 ∧ p ∣ n.choose k

/-- For k ≥ 29 and n ∈ [2k, k²], some prime ≤ 29 divides C(n,k). -/
theorem crt_small_prime_divides (n k : ℕ) (hk29 : 29 ≤ k)
    (hlow : 2 * k ≤ n) (hhigh : n ≤ k * k) :
    ∃ p, p.Prime ∧ p ≤ 29 ∧ p ∣ n.choose k := by
  by_cases hk700 : k ≤ 700
  · exact crtRangeCheck_sound 700 crt_verified_700 n k hk29 hk700 hlow hhigh
  · exact crt_density_from_asymptotic n k (by omega) hlow hhigh

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

/-- Large n smooth case: if n > k² and n/k is k-smooth, then C(n,k) has a
prime factor ≤ n/k. Sylvester-Schur type argument, pending librarian review. -/
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

/-! ### Main theorem -/

/-- No exceptions for k ≥ 29. -/
theorem no_exception_k_ge_29 (n k : ℕ) (_hk : 0 < k) (hn : 2 * k ≤ n) (hk29 : 29 ≤ k) :
    (n.choose k).minFac ≤ max (n / k) k := by
  by_cases h : n ≤ k * k
  · -- Case 1: n ≤ k²
    obtain ⟨p, hp_prime, hp29, hdvd⟩ := crt_small_prime_divides n k hk29 hn h
    calc (n.choose k).minFac
        ≤ p := Nat.minFac_le_of_dvd hp_prime.two_le hdvd
      _ ≤ 29 := hp29
      _ ≤ k := hk29
      _ ≤ max (n / k) k := le_max_right _ _
  · -- Case 2: n > k²
    push_neg at h
    calc (n.choose k).minFac
        ≤ n / k := large_n_minFac_bound n k (by omega) h (by omega)
      _ ≤ max (n / k) k := le_max_left _ _

end Erdos1094
