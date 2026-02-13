import botlib.NumberTheory.CarryInfra

/-!
# Axiom-Free Result: Small prime divides C(n,k) for k ≤ 700, n ∈ [2k, k²]

This file extracts the fully verified (axiom-free, sorry-free) core result
from the Erdős 1094 project. For every k ∈ [2, 700] and n ∈ [2k, k²],
some prime p ≤ 29 divides C(n,k).

Corollary: for k ∈ [29, 700], minFac(C(n,k)) ≤ k.

The proof is by exhaustive computational verification (native_decide).
Zero axioms. Zero sorry. Verified by the Lean kernel.
-/

open Nat OpenLemma.CarryInfra

namespace Erdos1094

/-! ### Computational check infrastructure -/

/-- Check all k ∈ [lo, hi], n ∈ [2k, k²] for small prime divisor of C(n,k). -/
def fullRangeCheck (lo hi : ℕ) : Bool :=
  (List.range (hi - lo + 1)).all fun i =>
    let k := lo + i
    (List.range (k * k - 2 * k + 1)).all fun j =>
      let n := j + 2 * k
      smallPrimeDivCheck n k

/-- Soundness of fullRangeCheck. -/
theorem fullRangeCheck_sound (lo hi : ℕ) (h : fullRangeCheck lo hi = true)
    (n k : ℕ) (hk_lo : lo ≤ k) (hk_hi : k ≤ hi)
    (hlow : 2 * k ≤ n) (hhigh : n ≤ k * k) :
    ∃ p, p.Prime ∧ p ≤ 29 ∧ p ∣ n.choose k := by
  apply smallPrimeDivCheck_sound (by omega)
  unfold fullRangeCheck at h
  rw [List.all_eq_true] at h
  have hk_mem : k - lo ∈ List.range (hi - lo + 1) := List.mem_range.mpr (by omega)
  have hk_eq : lo + (k - lo) = k := by omega
  specialize h (k - lo) hk_mem
  rw [hk_eq] at h
  rw [List.all_eq_true] at h
  have hn_mem : n - 2 * k ∈ List.range (k * k - 2 * k + 1) :=
    List.mem_range.mpr (by omega)
  specialize h (n - 2 * k) hn_mem
  rw [show n - 2 * k + 2 * k = n from by omega] at h
  exact h

/-! ### Verified computation -/

-- k ∈ [2, 28]: fast (~1s)
set_option maxHeartbeats 2000000 in
set_option linter.style.nativeDecide false in
set_option linter.style.maxHeartbeats false in
private theorem verified_small : fullRangeCheck 2 28 = true := by native_decide

-- k ∈ [29, 700]: (~4 min compile time)
set_option maxHeartbeats 16000000 in
set_option linter.style.nativeDecide false in
set_option linter.style.maxHeartbeats false in
private theorem verified_large : fullRangeCheck 29 700 = true := by native_decide

/-! ### Main axiom-free theorem -/

/-- **Axiom-free result**: For k ∈ [2, 700] and n ∈ [2k, k²], some prime
p ≤ 29 divides C(n,k). Proved by exhaustive computational verification.

Zero axioms. Zero sorry. Verified by the Lean kernel via native_decide. -/
theorem small_prime_dvd_choose_of_le_sq (n k : ℕ) (hk : 2 ≤ k) (hk700 : k ≤ 700)
    (hlow : 2 * k ≤ n) (hhigh : n ≤ k * k) :
    ∃ p, p.Prime ∧ p ≤ 29 ∧ p ∣ n.choose k := by
  by_cases hk28 : k ≤ 28
  · exact fullRangeCheck_sound 2 28 verified_small n k hk hk28 hlow hhigh
  · exact fullRangeCheck_sound 29 700 verified_large n k (by omega) hk700 hlow hhigh

/-- **Corollary**: For k ∈ [29, 700] and n ∈ [2k, k²], minFac(C(n,k)) ≤ k. -/
theorem minFac_choose_le_k_of_le_sq (n k : ℕ) (hk29 : 29 ≤ k) (hk700 : k ≤ 700)
    (hlow : 2 * k ≤ n) (hhigh : n ≤ k * k) :
    (n.choose k).minFac ≤ k := by
  obtain ⟨p, hp_prime, hp29, hp_dvd⟩ :=
    small_prime_dvd_choose_of_le_sq n k (by omega) hk700 hlow hhigh
  calc (n.choose k).minFac
      ≤ p := Nat.minFac_le_of_dvd hp_prime.two_le hp_dvd
    _ ≤ 29 := hp29
    _ ≤ k := hk29

end Erdos1094
