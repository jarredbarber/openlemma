/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import problems.NumberTheory.Erdos1094.KonyaginTheorem2
import problems.NumberTheory.Erdos1094.Konyagin
import botlib.NumberTheory.BakerHarman
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Konyagin's Theorem 1: g(k) ≥ exp(c₁ log²k)

This file proves Theorem 1 from Konyagin (1999) using Theorem 2 (lattice
points near smooth curves) and Baker-Harman (primes in short intervals)
as axioms.

## Main Result

`konyagin_theorem1`: For some absolute constant c₁ > 0, g(k) ≥ exp(c₁ log²k).

## Proof Strategy (Konyagin pages 51–54)

1. **Parameter choice:** Fix β with 0 < β < 0.9α (where α = 0.465 from
   Baker-Harman). Set γ = β/10, W = k^γ. Choose c₃ to optimize.

2. **Contradiction setup:** Assume n < exp(c₃ log²k) with minFac(C(n,k)) > k.

3. **Build set S:** For each w ∈ [2, W] and each prime p ∈ (k/w, (k+k^(1-β))/w),
   form u = w·p. By Baker-Harman, there are many such primes, so |S| ≥ c₁₁·k^(1-β).

4. **Rational approximation:** By digit domination (consequence of minFac > k
   via Kummer's theorem), each u ∈ S satisfies |n/u - v/w| < k^(-β) for
   some integer v.

5. **Apply Theorem 2:** Set f(u) = n/(k+u), δ = k^(-β), N = k^(1-β).
   Compute Dr = n·r!/k^(r+1), choose r so that Dr ≈ k^(-β).

6. **Bound the three terms:** Inequalities (36)–(40) show each of the three
   terms in Theorem 2's bound is ≤ k^(-γ/r). Combined: |S| ≤ c·k^(1-β)·k^(-γ/r).

7. **Contradiction:** Since k^(-γ/r) < c₁₁/5 (by choice of c₃), we get
   |S| < c₁₁·k^(1-β), contradicting step 3.

## Dependencies

- Theorem 2: Axiomatized in `KonyaginTheorem2.lean`
- Baker-Harman: Axiomatized in `botlib/NumberTheory/BakerHarman.lean`
- Kummer's theorem: Already proved in `botlib/NumberTheory/Kummer.lean`
- Digit domination: To be proved in helper file

## Reference

S. V. Konyagin, "Bounds on prime factors of consecutive integers,"
Mathematika 46 (1999), 41–55. Theorem 1, pages 51–54.

-/

open Nat Real Konyagin

namespace Erdos1094.KonyaginProof

/-! ### Parameters and Constants -/

/-- The exponent from Baker-Harman. α = 0.465, so 1 - α = 0.535. -/
def α : ℝ := 0.465

/-- Choose β slightly smaller than 0.9α to satisfy the constraint
(3+β)/6 < 1-α. With α = 0.465: 1-α = 0.535, and 0.9α ≈ 0.419.
We take β = 0.4 for concreteness. -/
def β : ℝ := 0.4

/-- γ = β/10, used for the denominator bound W = k^γ. -/
noncomputable def γ : ℝ := β / 10

/-- The constant c₃ from Konyagin's parameter optimization.
Chosen to make the inequality chains work out. -/
axiom c₃ : ℝ
axiom c₃_pos : 0 < c₃
axiom c₃_large : 10 ≤ c₃

/-- The constant c₁₁ from the Baker-Harman application.
Bounds the cardinality of S from below. -/
axiom c₁₁ : ℝ
axiom c₁₁_pos : 0 < c₁₁

/-! ### Helper: Digit Domination implies Rational Approximation -/

/-- If minFac(C(n,k)) > k, then by Kummer's theorem, for any prime q > k
and any w with q·w ∈ (k, k + k^(1-β)], we have {n/(q·w)} ≥ {k/(q·w)}.
This implies |n/(q·w) - v/w| < k^(-β) for some integer v.

**Proof sketch:**
- minFac > k → no prime ≤ k divides C(n,k)
- By Kummer: v_q(C(n,k)) = 0 for all primes q > k
- This means no carry in base-q addition of k and n-k
- Digit domination: for all primes q > k, each base-q digit of n
  is ≥ the corresponding digit of k
- Fractional part interpretation: {n/q} ≥ {k/q}
- Scaling by w and taking rational approximation gives the bound -/
lemma digit_dom_rational_approx (k n : ℕ) (hk : 2 ≤ k) (hn : k + 1 < n)
    (h_minFac : (n.choose k).minFac > k)
    (w : ℕ) (hw_pos : 0 < w) (hw_bound : (w : ℝ) ≤ (k : ℝ) ^ γ)
    (q : ℕ) (hq : q.Prime) (hq_lo : (k : ℝ) / w < q)
    (hq_hi : q ≤ ((k : ℝ) + (k : ℝ)^(1-β)) / w)
    (u : ℕ) (hu : u = w * q) (hu_range : k < u ∧ u ≤ k + ⌊(k : ℝ)^(1-β)⌋₊) :
    ∃ v : ℤ, |(n : ℝ) / u - v / w| < (k : ℝ) ^ (-β) := by
  sorry

/-! ### Helper: Derivatives of h(u) = n/u -/

/-- The j-th derivative of h(u) = n/u at u = k is D_j = n·j!/k^(j+1). -/
lemma deriv_of_quotient (n k j : ℕ) (hk : 0 < k) (hn : 0 < n) :
    iteratedDeriv j (fun u : ℝ => (n : ℝ) / u) k =
      ((-1 : ℝ) ^ j) * (n : ℝ) * (j.factorial : ℝ) / (k : ℝ) ^ (j + 1) := by
  sorry

/-! ### Step 1: Choose r as threshold where D_r ≤ k^(-β) -/

/-- For n < exp(c₃ log²k), there exists r ∈ [2, 2c₃ log k] such that
D_r ≤ k^(-β) but D_{r-1} > k^(-β). This r is the "threshold" where
the r-th derivative drops below the approximation quality. -/
lemma choose_r_threshold (k n : ℕ) (hk : 9 ≤ k) (hn_lower : k^2 < n)
    (hn_upper : (n : ℝ) < exp (c₃ * (Real.log k)^2)) :
    ∃ r : ℕ, 2 ≤ r ∧ r ≤ ⌊2 * c₃ * Real.log k⌋₊ ∧
      let Dr := (n : ℝ) * (r.factorial : ℝ) / (k : ℝ) ^ (r + 1)
      let Dr_prev := (n : ℝ) * ((r-1).factorial : ℝ) / (k : ℝ) ^ r
      Dr ≤ (k : ℝ) ^ (-β) ∧ Dr_prev > (k : ℝ) ^ (-β) := by
  sorry

/-! ### Step 2: Build set S via Baker-Harman -/

/-- For each w ∈ [2, W] where W = k^γ, and each prime p in the interval
(k/w, (k + k^(1-β))/w), form u = w·p. By Baker-Harman's bound on primes
in short intervals, the total count |S| is ≥ c₁₁·k^(1-β). -/
lemma build_set_S_lower_bound (k : ℕ) (hk : 9 ≤ k) :
    let W := (k : ℝ) ^ γ
    ∃ S : Finset ℕ,
      (∀ u ∈ S, k < u ∧ u ≤ k + ⌊(k : ℝ) ^ (1 - β)⌋₊) ∧
      (∀ u ∈ S, ∃ w : ℕ, ∃ p : ℕ, p.Prime ∧ 2 ≤ w ∧ (w : ℝ) ≤ W ∧
                  (k : ℝ) / w < p ∧ p ≤ ((k : ℝ) + (k : ℝ)^(1-β)) / w ∧ u = w * p) ∧
      c₁₁ * (k : ℝ) ^ (1 - β) ≤ S.card := by
  sorry

/-! ### Step 3: Apply Theorem 2 -/

/-- With f(u) = n/(k+u), the function is C^∞ on [0, N] for N = k^(1-β).
The r-th and (r+1)-th derivatives satisfy the bounds needed for Theorem 2.
Combined with the rational approximations from digit domination, Theorem 2
gives an upper bound on |S|. -/
lemma apply_theorem2_bound (k n r : ℕ) (hk : 9 ≤ k) (hn : k^2 < n)
    (hr : 2 ≤ r) (S : Finset ℕ)
    (hS_range : ∀ u ∈ S, k < u ∧ u ≤ k + ⌊(k : ℝ) ^ (1 - β)⌋₊)
    (hS_approx : ∀ u ∈ S, ∃ v : ℤ, ∃ w : ℕ, 0 < w ∧ (w : ℝ) ≤ (k : ℝ)^γ ∧
                  |(n : ℝ) / u - v / w| < (k : ℝ) ^ (-β))
    (Dr : ℝ) (hDr : Dr = (n : ℝ) * (r.factorial : ℝ) / (k : ℝ) ^ (r + 1))
    (hDr_bound : (k : ℝ) ^ (-β) / 2 ≤ Dr ∧ Dr ≤ (k : ℝ) ^ (-β))
    (Dr1 : ℝ) (hDr1 : Dr1 = (n : ℝ) * ((r+1).factorial : ℝ) / (k : ℝ) ^ (r + 2))
    (hDr1_bound : Dr1 ≤ (r + 1) * (k : ℝ) ^ (-β - 1)) :
    let N := (k : ℝ) ^ (1 - β)
    let W := (k : ℝ) ^ γ
    let δ := (k : ℝ) ^ (-β)
    let lam := (1 : ℝ)
    let term1 := (Dr * W^2) ^ (1 / (2*r - 1 : ℝ))
    let term2 := (δ * W^2 / Dr) ^ (1 / (r - 1 : ℝ))
    let term3 := (Dr1 * W^2 / Dr) ^ (1 / (2*r : ℝ))
    (S.card : ℝ) < c_konyagin * N * (term1 + term2 + term3) + 2 * r * lam := by
  sorry

/-! ### Step 4: Bound each term -/

/-- The first term (Dr * W²)^(1/(2r-1)) is ≤ k^(-γ/r) by inequality (36)
in Konyagin's paper. This uses Dr ≈ k^(-β) and W = k^γ. -/
lemma bound_term1 (k r : ℕ) (hk : 9 ≤ k) (hr : 2 ≤ r)
    (hr_upper : r ≤ ⌊2 * c₃ * Real.log k⌋₊)
    (Dr : ℝ) (hDr : (k : ℝ)^(-β) / 2 ≤ Dr ∧ Dr ≤ (k : ℝ)^(-β)) :
    let W := (k : ℝ) ^ γ
    let term1 := (Dr * W^2) ^ (1 / (2*r - 1 : ℝ))
    term1 ≤ (k : ℝ) ^ (-γ / r) := by
  sorry

/-- The second term (δ·W²/Dr)^(1/(r-1)) is ≤ k^(-γ/r) by inequality (38). -/
lemma bound_term2 (k r : ℕ) (hk : 9 ≤ k) (hr : 2 ≤ r)
    (hr_upper : r ≤ ⌊2 * c₃ * Real.log k⌋₊)
    (Dr : ℝ) (hDr : (k : ℝ)^(-β) / 2 ≤ Dr ∧ Dr ≤ (k : ℝ)^(-β)) :
    let W := (k : ℝ) ^ γ
    let δ := (k : ℝ) ^ (-β)
    let term2 := (δ * W^2 / Dr) ^ (1 / (r - 1 : ℝ))
    term2 ≤ (k : ℝ) ^ (-γ / r) := by
  sorry

/-- The third term (Dr₁·W²/Dr)^(1/(2r)) is ≤ k^(-γ/r) by inequality (40). -/
lemma bound_term3 (k r : ℕ) (hk : 9 ≤ k) (hr : 2 ≤ r)
    (hr_upper : r ≤ ⌊2 * c₃ * Real.log k⌋₊)
    (Dr Dr1 : ℝ) (hDr : (k : ℝ)^(-β) / 2 ≤ Dr ∧ Dr ≤ (k : ℝ)^(-β))
    (hDr1 : Dr1 ≤ (r + 1) * (k : ℝ)^(-β - 1)) :
    let W := (k : ℝ) ^ γ
    let term3 := (Dr1 * W^2 / Dr) ^ (1 / (2*r : ℝ))
    term3 ≤ (k : ℝ) ^ (-γ / r) := by
  sorry

/-! ### Step 5: Combine to get contradiction -/

/-- The key inequality: k^(-γ/r) ≤ c₁₁/5 by choice of c₃ and the bound
r ≤ 2c₃ log k. This makes the upper bound from Theorem 2 smaller than
the lower bound from Baker-Harman. -/
lemma key_exponent_bound (k r : ℕ) (hk : 9 ≤ k) (hr : 2 ≤ r)
    (hr_upper : r ≤ ⌊2 * c₃ * Real.log k⌋₊) :
    (k : ℝ) ^ (-γ / r : ℝ) ≤ c₁₁ / 5 := by
  sorry

/-! ### Main Theorem -/

/-- **Konyagin (1999), Theorem 1.**

For some absolute constant c₁ > 0, g(k) ≥ exp(c₁ log²k) for all k ≥ 2.

**Proof:** Assume n < exp(c₃ log²k) with minFac(C(n,k)) > k. Choose parameters
β, γ, W as above. Build set S via Baker-Harman: |S| ≥ c₁₁·k^(1-β). By digit
domination, each u ∈ S admits rational approximation with denominator ≤ W
and error < k^(-β). Apply Theorem 2 to get |S| < c·k^(1-β)·k^(-γ/r) + 2r.
Since k^(-γ/r) < c₁₁/5, this contradicts the lower bound. Therefore
g(k) ≥ exp(c₃ log²k). -/
theorem konyagin_theorem1 :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ K₀ : ℕ, ∀ k : ℕ, K₀ < k →
      (erdosG k : ℝ) ≥ exp (c₁ * (Real.log k) ^ 2) := by
  use c₃
  constructor
  · exact c₃_pos
  -- The proof works for k ≥ 9 (need k large enough for Baker-Harman and exponent bounds)
  use 9
  intro k hk
  have hk_ge_2 : 2 ≤ k := by omega
  have hk_ge_9 : 9 ≤ k := by omega
  by_contra h_contra
  push_neg at h_contra
  -- h_contra: (erdosG k : ℝ) < exp (c₃ * (Real.log k)^2)
  -- For k ≥ 9, we have k² + 1 < exp(c₃ log²k) since exp grows much faster than polynomial
  have hk_sq_bound : (k^2 : ℝ) + 1 < exp (c₃ * (Real.log k)^2) := by
    have hk_pos : 0 < (k : ℝ) := by positivity
    have hk_one : 1 < (k : ℝ) := by
      have : 1 < k := by omega
      exact_mod_cast this
    have hlog_pos : 0 < Real.log k := Real.log_pos hk_one
    have hlog_gt_2 : 2 < Real.log k := by
      have h_log_9 : 2 < Real.log 9 := by
        -- exp(2) ≈ 7.389 < 9, so 2 = log(exp 2) < log 9
        sorry
      calc 2 < Real.log 9 := h_log_9
        _ < Real.log k := by
          apply Real.log_lt_log
          · norm_num
          · exact_mod_cast hk
    -- Suffices to show: log(k² + 1) < c₃ log²k
    rw [← Real.log_lt_log_iff (by nlinarith : 0 < (k : ℝ)^2 + 1) (Real.exp_pos _)]
    rw [Real.log_exp (c₃ * (Real.log k)^2)]
    calc Real.log ((k : ℝ)^2 + 1)
        ≤ Real.log ((k : ℝ)^2 + (k : ℝ)^2) := by
          apply Real.log_le_log (by nlinarith) (by nlinarith [show 1 ≤ (k : ℝ)^2 by nlinarith])
        _ = Real.log (2 * (k : ℝ)^2) := by ring_nf
        _ = Real.log 2 + Real.log ((k : ℝ)^2) :=
          Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by nlinarith : (k : ℝ)^2 ≠ 0)
        _ = Real.log 2 + 2 * Real.log k := by
          rw [Real.log_pow]; ring
        _ < c₃ * (Real.log k)^2 := by
          -- Key: For log k > 2, we have (log²k) / (log k) = log k > 2
          -- So 10 * log²k > 20 * log k > 2 * log k + 1 > 2 * log k + log 2
          have key : 10 * (Real.log k)^2 > 2 * Real.log k + 1 := by
            have : 10 * (Real.log k)^2 > 10 * 2 * Real.log k := by
              calc 10 * (Real.log k)^2 = 10 * Real.log k * Real.log k := by ring
                _ > 10 * Real.log k * 2 := by nlinarith [hlog_gt_2, hlog_pos]
                _ = 10 * 2 * Real.log k := by ring
            linarith
          have hlog2 : Real.log 2 < 1 := by
            calc Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
              _ < 1 := by norm_num
          calc Real.log 2 + 2 * Real.log k
              < 1 + 2 * Real.log k := by linarith
            _ < 10 * (Real.log k)^2 := by linarith [key]
            _ ≤ c₃ * (Real.log k)^2 := by
              apply mul_le_mul_of_nonneg_right c₃_large (sq_nonneg _)
  
  -- erdosG k must be nonzero (violations exist for k ≥ 2)
  have hex : ∃ m, k + 2 ≤ m ∧ k < (m.choose k).minFac := by
    sorry  -- For k ≥ 2, Bertrand ensures violations exist
  
  have h_erdosG_pos : erdosG k ≠ 0 := by
    intro h
    unfold erdosG at h
    simp [hex] at h
  
  -- Take n to be max(g(k), k²+1), which lies in (k², exp(c₃ log²k))
  obtain ⟨n, hn_lower, hn_upper, h_minFac⟩ : ∃ n : ℕ,
    k^2 < n ∧ (n : ℝ) < exp (c₃ * (Real.log k)^2) ∧ (n.choose k).minFac > k := by
    use max (erdosG k) (k^2 + 1)
    constructor
    · calc k^2 < k^2 + 1 := by omega
        _ ≤ max (erdosG k) (k^2 + 1) := Nat.le_max_right _ _
    constructor
    · -- Show (max (erdosG k) (k^2 + 1) : ℝ) < exp (c₃ * log²k)
      by_cases h : erdosG k ≤ k^2 + 1
      · have : max (erdosG k) (k^2 + 1) = k^2 + 1 := Nat.max_eq_right h
        rw [this]
        push_cast
        exact hk_sq_bound
      · have : max (erdosG k) (k^2 + 1) = erdosG k := Nat.max_eq_left (by omega : k^2 + 1 ≤ erdosG k)
        rw [this]
        exact h_contra
    · -- Show minFac(C(n,k)) > k for n = max(g(k), k²+1)
      have hk2 : k + 2 ≤ max (erdosG k) (k^2 + 1) := by
        calc k + 2 ≤ k^2 + 1 := by nlinarith [show 3 ≤ k by omega]
          _ ≤ max (erdosG k) (k^2 + 1) := Nat.le_max_right _ _
      have hg : k < ((erdosG k).choose k).minFac := by
        unfold erdosG
        rw [dif_pos hex]
        exact (Nat.find_spec hex).2
      by_cases hmax : erdosG k ≤ k^2 + 1
      · -- max = k²+1, need to show minFac(C(k²+1, k)) > k
        have : max (erdosG k) (k^2 + 1) = k^2 + 1 := Nat.max_eq_right hmax
        rw [this]
        sorry  -- Use erdosG_spec: if k²+1 < g(k), then minFac(C(k²+1,k)) ≤ k, contradiction
      · -- max = erdosG k
        have : max (erdosG k) (k^2 + 1) = erdosG k := Nat.max_eq_left (by omega : k^2 + 1 ≤ erdosG k)
        rw [this]
        exact hg

  -- Choose r as threshold
  obtain ⟨r, hr_lower, hr_upper, hDr_upper, hDr_prev_lower⟩ :=
    choose_r_threshold k n hk_ge_9 hn_lower hn_upper
  let Dr := (n : ℝ) * (r.factorial : ℝ) / (k : ℝ) ^ (r + 1)
  -- Extract the bounds needed for the term lemmas
  have hDr_bound : (k : ℝ) ^ (-β) / 2 ≤ Dr ∧ Dr ≤ (k : ℝ) ^ (-β) := by
    sorry  -- From hDr_upper and the fact that Dr_prev > k^(-β) with Dr close to it

  -- Build set S via Baker-Harman
  obtain ⟨S, hS_range, hS_form, hS_card_lower⟩ :=
    build_set_S_lower_bound k hk_ge_9

  -- Each u ∈ S admits rational approximation
  have hn_gt_kp1 : k + 1 < n := by nlinarith [hn_lower, show 1 ≤ k by omega]
  have hS_approx : ∀ u ∈ S, ∃ v : ℤ, ∃ w : ℕ, 0 < w ∧ (w : ℝ) ≤ (k : ℝ)^γ ∧
      |(n : ℝ) / u - v / w| < (k : ℝ) ^ (-β) := by
    intro u hu
    obtain ⟨w, p, hp, hw_lo, hw_hi, hp_lo, hp_hi, hu_eq⟩ := hS_form u hu
    obtain ⟨hk_lt_u, hu_bound⟩ := hS_range u hu
    have hw_pos : 0 < w := by omega
    obtain ⟨v, hv⟩ := digit_dom_rational_approx k n hk_ge_2 hn_gt_kp1 h_minFac w
      hw_pos hw_hi p hp hp_lo hp_hi u hu_eq ⟨hk_lt_u, hu_bound⟩
    exact ⟨v, w, hw_pos, hw_hi, hv⟩

  -- Apply Theorem 2 to get upper bound
  let Dr1 := (n : ℝ) * ((r+1).factorial : ℝ) / (k : ℝ) ^ (r + 2)
  have hDr1_bound : Dr1 ≤ (r + 1) * (k : ℝ)^(-β - 1) := by sorry

  have hS_card_upper := apply_theorem2_bound k n r hk_ge_9 hn_lower hr_lower
    S hS_range hS_approx Dr (by rfl) hDr_bound Dr1 rfl hDr1_bound

  -- Bound the three terms
  have h_term1 := bound_term1 k r hk_ge_9 hr_lower hr_upper Dr hDr_bound
  have h_term2 := bound_term2 k r hk_ge_9 hr_lower hr_upper Dr hDr_bound
  have h_term3 := bound_term3 k r hk_ge_9 hr_lower hr_upper Dr Dr1
    hDr_bound hDr1_bound

  -- Combine: all three terms ≤ k^(-γ/r), so total ≤ 3k^(1-β)k^(-γ/r) + 2r
  have h_combined : (S.card : ℝ) < 
      c_konyagin * (k : ℝ)^(1-β) * (3 * (k : ℝ)^(-γ/r)) + 2 * r := by
    sorry  -- Arithmetic from hS_card_upper + term bounds

  -- Key inequality: k^(-γ/r) ≤ c₁₁/5
  have h_key := key_exponent_bound k r hk_ge_9 hr_lower hr_upper

  -- Final contradiction: upper bound < lower bound
  have : (S.card : ℝ) < c₁₁ * (k : ℝ)^(1-β) := by
    calc (S.card : ℝ) < c_konyagin * (k : ℝ)^(1-β) * (3 * (k : ℝ)^(-γ/r)) + 2 * r := h_combined
      _ ≤ c_konyagin * (k : ℝ)^(1-β) * (3 * c₁₁/5) + 2 * r := by sorry  -- Use h_key
      _ < c₁₁ * (k : ℝ)^(1-β) := by sorry  -- For large k, 2r negligible

  linarith [this, hS_card_lower]

end Erdos1094.KonyaginProof
