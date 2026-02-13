/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import problems.NumberTheory.Erdos1094.KGe29
import botlib.NumberTheory.Kummer

/-!
# Progressive elimination of `large_n_smooth_case`

The axiom `large_n_smooth_case` states: for n > k² with n/k k-smooth,
∃ prime p ≤ n/k with p | C(n,k).

We decompose this into subcases, proving each one axiom-free.

## Tree structure

```
large_n_smooth_case (AXIOM — full statement)
├── smooth_case_divisible: k | n  [PROVED]
├── smooth_case_n_smooth: n itself is k-smooth  [PROVED]
├── smooth_case_gap_prime: n has prime p ∈ (k, n/k]  [PROVED]
├── smooth_case_near_prime_nondivisor: n = s·q, q prime > k, s < k, s ∤ k  [PROVED]
└── B3b: n = s·q, q prime > n/k, s | k, s < k  [OPEN — contains (62,6)]
```

All proved nodes are axiom-free and sorry-free.
-/

open Nat OpenLemma.Kummer

namespace Erdos1094.SmoothCase

/-! ### Helper: n > k² implies k ≤ n/k -/

private lemma k_le_div_of_sq_lt (n k : ℕ) (hk : 2 ≤ k) (hn : k * k < n) :
    k ≤ n / k := by
  rw [Nat.le_div_iff_mul_le (by omega : 0 < k)]
  omega

/-! ### Smooth case: k | n -/

/-- **B (k | n):** When k divides n and n/k is k-smooth, the result holds axiom-free.
Since k | n: n = k · (n/k) is k-smooth. Apply `smooth_n_has_small_factor`. -/
theorem smooth_case_divisible (n k : ℕ) (hk : 2 ≤ k) (hn : k * k < n)
    (hsmooth : ∀ p, p.Prime → p ∣ n / k → p ≤ k) (hdvd : k ∣ n) :
    ∃ p, p.Prime ∧ p ≤ n / k ∧ p ∣ n.choose k := by
  have hk_lt_n : k < n := lt_trans (by nlinarith : k < k * k) hn
  obtain ⟨q, hq, hq_le, hq_dvd⟩ :=
    divisible_smooth_quotient_has_small_factor n k hk hk_lt_n hdvd hsmooth
  exact ⟨q, hq, le_trans hq_le (k_le_div_of_sq_lt n k hk hn), hq_dvd⟩

/-! ### B1: n is k-smooth -/

/-- **B1:** When n itself is k-smooth (all prime factors ≤ k) and n > k²,
the result holds axiom-free. This is strictly stronger than "k | n with n/k k-smooth"
since it doesn't require k | n. -/
theorem smooth_case_n_smooth (n k : ℕ) (hk : 2 ≤ k) (hn : k * k < n)
    (_hkn : k ≤ n) (hn_smooth : ∀ p, p.Prime → p ∣ n → p ≤ k) :
    ∃ p, p.Prime ∧ p ≤ n / k ∧ p ∣ n.choose k := by
  have hk_lt_n : k < n := lt_trans (by nlinarith : k < k * k) hn
  obtain ⟨q, hq, hq_le, hq_dvd⟩ := smooth_n_has_small_factor n k hk hk_lt_n hn_smooth
  exact ⟨q, hq, le_trans hq_le (k_le_div_of_sq_lt n k hk hn), hq_dvd⟩

/-! ### B2: n has a "gap prime" in (k, n/k] -/

/-- **B2:** When n has a prime factor p with k < p ≤ n/k, then p | C(n,k).
Since p | n and p > k: by Kummer, the base-p digit 0 of k is k > 0 while
the digit 0 of n is 0 (since p | n). So there's a carry and p | C(n,k). -/
theorem smooth_case_gap_prime (n k : ℕ) (hk : 2 ≤ k) (hn : k * k < n)
    (hkn : k ≤ n) (p : ℕ) (hp : p.Prime) (hpk : k < p) (hpM : p ≤ n / k)
    (hpn : p ∣ n) :
    ∃ q, q.Prime ∧ q ≤ n / k ∧ q ∣ n.choose k := by
  have hp_fact : Fact p.Prime := ⟨hp⟩
  -- v_p(k) = 0 (since p > k and p prime)
  have hvk : padicValNat p k = 0 := by
    rw [← not_ne_iff]
    intro h
    have := dvd_of_one_le_padicValNat (one_le_iff_ne_zero.mpr h)
    exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
  -- v_p(n) ≥ 1 > 0 = v_p(k)
  have hvn : 0 < padicValNat p n :=
    one_le_padicValNat_of_dvd (by omega : n ≠ 0) hpn
  -- Apply trailing_zero_carry
  have h_dvd := @trailing_zero_carry p hp_fact n k hkn (by omega) (by omega)
  exact ⟨p, hp, hpM, h_dvd⟩

/-! ### B3a: n = s·q with q prime > k, s < k, s ∤ k -/

/-- **B3a:** When n = s·q with q prime > k, s < k, and s does not divide k,
then some prime p ≤ k (hence ≤ n/k) divides C(n,k).

Since s ∤ k: some prime power p^e divides s but not k, giving v_p(s) > v_p(k).
Since q is prime and q > k ≥ p: v_p(q) = 0, so v_p(n) = v_p(s) > v_p(k).
Apply `trailing_zero_carry`. -/
theorem smooth_case_near_prime_nondivisor (n k s q : ℕ) (hk : 2 ≤ k)
    (hn : k * k < n) (hkn : k ≤ n) (hn_eq : n = s * q)
    (_hq : q.Prime) (_hqk : k < q) (hs : 0 < s) (hsk : s < k) (hndvd : ¬ (s ∣ k)) :
    ∃ p, p.Prime ∧ p ≤ n / k ∧ p ∣ n.choose k := by
  -- s ∤ k → ∃ prime p, power e with p^e | s and p^e ∤ k
  rw [Nat.dvd_iff_prime_pow_dvd_dvd] at hndvd
  push_neg at hndvd
  obtain ⟨p, e, hp, hpe_s, hpe_k⟩ := hndvd
  -- e ≥ 1 (since p^e | s and p^0 = 1 | k always)
  have he : 1 ≤ e := by
    by_contra h
    push_neg at h
    interval_cases e
    simp at hpe_k
  -- p^e | n (since p^e | s and s | n)
  have hpe_n : p ^ e ∣ n := by
    rw [hn_eq]; exact dvd_mul_of_dvd_left hpe_s q
  -- Fact p.Prime
  have hp_fact : Fact p.Prime := ⟨hp⟩
  -- v_p(n) ≥ e (from p^e | n)
  have hvn : e ≤ padicValNat p n :=
    (@padicValNat_dvd_iff_le p hp_fact n e (by omega : n ≠ 0)).mp hpe_n
  -- v_p(k) < e (from ¬(p^e | k))
  have hvk : padicValNat p k < e := by
    rwa [← not_le, ← @padicValNat_dvd_iff_le p hp_fact k e (by omega : k ≠ 0)]
  -- So v_p(n) > v_p(k)
  have hv : padicValNat p n > padicValNat p k := by omega
  -- Apply trailing_zero_carry
  have h_dvd := @trailing_zero_carry p hp_fact n k hkn (by omega) hv
  -- p ≤ s < k ≤ n/k
  have hp_le_s : p ≤ s := le_trans (Nat.le_of_dvd hs (dvd_trans (dvd_pow_self p (by omega : e ≠ 0)) hpe_s)) le_rfl
  exact ⟨p, hp, le_trans (by omega : p ≤ k) (k_le_div_of_sq_lt n k hk hn), h_dvd⟩

/-! ### B3a minFac version -/

/-- **B3a (minFac):** Axiom-free `minFac(C(n,k)) ≤ n/k` when n = s·q
with q prime > k and s ∤ k.

Proof: s ∤ k gives a prime p with v_p(s) > v_p(k). Since s | n,
v_p(n) ≥ v_p(s) > v_p(k). By `trailing_zero_carry`: p | C(n,k).
Then p ≤ s = n/q < n/k (since q > k), so minFac ≤ p ≤ n/k. -/
theorem near_prime_nondivisor_minFac_bound (n k s q : ℕ)
    (hk : 2 ≤ k) (hn : k * k < n) (hkn : k ≤ n)
    (hnsq : n = s * q) (hq : q.Prime) (hqk : k < q)
    (hs0 : 0 < s) (hsk : ¬ (s ∣ k)) :
    (n.choose k).minFac ≤ n / k := by
  -- s ∤ k → ∃ prime p, e with p^e | s, p^e ∤ k
  rw [Nat.dvd_iff_prime_pow_dvd_dvd] at hsk
  push_neg at hsk
  obtain ⟨p, e, hp, hpe_s, hpe_k⟩ := hsk
  have he : 1 ≤ e := by
    by_contra h; push_neg at h; interval_cases e; simp at hpe_k
  have hp_fact : Fact p.Prime := ⟨hp⟩
  -- v_p(n) ≥ v_p(s) > v_p(k): s | n gives p^e | n
  have hpe_n : p ^ e ∣ n := hnsq ▸ dvd_mul_of_dvd_left hpe_s q
  have hvn : e ≤ padicValNat p n :=
    (@padicValNat_dvd_iff_le p hp_fact n e (by omega)).mp hpe_n
  have hvk : padicValNat p k < e := by
    rwa [← not_le, ← @padicValNat_dvd_iff_le p hp_fact k e (by omega)]
  -- trailing_zero_carry: p | C(n,k)
  have h_dvd := @trailing_zero_carry p hp_fact n k hkn (by omega) (by omega)
  -- p ≤ s: p | s (from p^e | s with e ≥ 1)
  have hp_le_s : p ≤ s :=
    Nat.le_of_dvd hs0 (dvd_trans (dvd_pow_self p (by omega : e ≠ 0)) hpe_s)
  -- s < n/k: since n = s*q and q > k, we have s*k < s*q = n, so s < n/k
  have hs_lt : s < n / k := by
    rw [Nat.lt_div_iff_mul_lt (by omega : 0 < k)]
    calc s * k < s * q := by exact (Nat.mul_lt_mul_left hs0).mpr hqk
      _ = n := hnsq.symm
  -- minFac ≤ p ≤ s < n/k
  exact le_trans (Nat.minFac_le_of_dvd hp.two_le h_dvd) (by omega)

end Erdos1094.SmoothCase
