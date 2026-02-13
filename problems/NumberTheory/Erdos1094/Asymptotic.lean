/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Erdős 1094: Asymptotic proof for the finiteness of exceptions.
Focusing on the digit-based Kummer suppression from small primes.
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import botlib.NumberTheory.Kummer
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Erdos1094

open Nat Finset OpenLemma.Kummer

def P_S : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23, 29}
def L_p (p k : ℕ) : ℕ := if p > 1 then (digits p k).length else 0
def dig (p k j : ℕ) : ℕ := (digits p k).getD j 0

def KummerValid (p k : ℕ) : Finset ℕ :=
  (range (p ^ L_p p k)).filter (fun r =>
    ∀ j < L_p p k, dig p k j ≤ (digits p r).getD j 0)

noncomputable def density_p (p k : ℕ) : ℝ :=
  (KummerValid p k).card / (p ^ L_p p k : ℝ)

noncomputable def total_density (k : ℕ) : ℝ :=
  P_S.prod (fun p => density_p p k)

/-! ### Computational Density Verification -/

/-- Computable integer check: k² · ∏ card(KummerValid p k) < ∏ p^L_p(k).
This is equivalent to total_density k < 1/k² (see `densityCheck_sound`). -/
def densityCheck (k : ℕ) : Bool :=
  k * k * P_S.prod (fun p => (KummerValid p k).card) < P_S.prod (fun p => p ^ L_p p k)

/-- Range check: densityCheck holds for all k in [lo, hi]. -/
def densityRangeCheck (lo hi : ℕ) : Bool :=
  (List.range (hi - lo + 1)).all fun i => densityCheck (lo + i)

/-- total_density equals the ratio of nat products cast to ℝ. -/
private lemma total_density_eq_ratio (k : ℕ) :
    total_density k = ↑(P_S.prod (fun p => (KummerValid p k).card)) /
                      ↑(P_S.prod (fun p => p ^ L_p p k)) := by
  unfold total_density density_p
  rw [prod_div_distrib]
  congr 1
  · rw [← Nat.cast_prod]
  · have : (∏ x ∈ P_S, (↑x : ℝ) ^ L_p x k) = ∏ x ∈ P_S, (↑(x ^ L_p x k) : ℝ) := by
      apply prod_congr rfl; intro x _; push_cast; ring
    rw [this, ← Nat.cast_prod]

/-- Soundness: the integer check implies the real density bound. -/
theorem densityCheck_sound (k : ℕ) (hk : k ≥ 2) (h : densityCheck k = true) :
    total_density k < 1 / (k : ℝ) ^ 2 := by
  unfold densityCheck at h
  simp only [decide_eq_true_eq] at h
  have h_cast : (↑(k * k * P_S.prod (fun p => (KummerValid p k).card)) : ℝ) <
                 ↑(P_S.prod (fun p => p ^ L_p p k)) := by exact_mod_cast h
  rw [total_density_eq_ratio]
  have h_denom : (0 : ℝ) < ↑(P_S.prod (fun p => p ^ L_p p k)) := by
    have : 0 < P_S.prod (fun p => p ^ L_p p k) := by
      apply prod_pos; intro p hp
      exact Nat.pos_of_ne_zero (by
        intro h0; simp [Nat.pow_eq_zero] at h0
        have : p ∈ P_S := hp; unfold P_S at this; simp at this; omega)
    exact_mod_cast this
  have hk2_pos : (0 : ℝ) < (k : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    nlinarith
  rw [div_lt_div_iff₀ h_denom hk2_pos, one_mul, sq]
  push_cast at h_cast ⊢
  linarith

/-- Range check soundness. -/
theorem densityRangeCheck_sound (lo hi : ℕ) (hlo : lo ≥ 2)
    (h : densityRangeCheck lo hi = true) :
    ∀ k, lo ≤ k → k ≤ hi → total_density k < 1 / (k : ℝ) ^ 2 := by
  intro k hk_lo hk_hi
  apply densityCheck_sound k (by omega)
  unfold densityRangeCheck at h
  rw [List.all_eq_true] at h
  have hk_sub : lo + (k - lo) = k := by omega
  have hm : k - lo ∈ List.range (hi - lo + 1) := by
    simp only [List.mem_range]; omega
  have := h _ hm
  simp only [hk_sub] at this
  exact this

-- Exhaustive verification for k ∈ [2, 700]. Compile time: ~3 min.
set_option maxHeartbeats 4000000 in
set_option linter.style.nativeDecide false in
set_option linter.style.maxHeartbeats false in
private theorem density_verified_700 : densityRangeCheck 2 700 = true := by native_decide

/-! ### Helper Lemmas -/

private lemma getD_digits_zero (p r : ℕ) (hp : 1 < p) :
    (digits p r).getD 0 0 = r % p := by
  rcases r with rfl | r'
  · simp [digits_zero]
  · rw [digits_of_two_le_of_pos hp (Nat.succ_pos r')]; simp

private lemma getD_digits_succ (p r j : ℕ) (hp : 1 < p) :
    (digits p r).getD (j + 1) 0 = (digits p (r / p)).getD j 0 := by
  rcases r with rfl | r'
  · simp [digits_zero, Nat.zero_div]
  · rw [digits_of_two_le_of_pos hp (Nat.succ_pos r')]; simp

private lemma div_qpd (p q d : ℕ) (hp : 0 < p) (hd : d < p) :
    (q * p + d) / p = q := by
  rw [show q * p + d = d + q * p from by ring]
  rw [Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hd, zero_add]

private lemma mod_qpd (p q d : ℕ) (hd : d < p) :
    (q * p + d) % p = d := by
  rw [show q * p + d = d + q * p from by ring]
  simp [Nat.mod_eq_of_lt hd]

/-! ### Core Counting Lemma -/

lemma card_filter_digits_le (p n k : ℕ) (hp : 1 < p) :
    ((range (p ^ n)).filter (fun r =>
      ∀ j < n, (digits p k).getD j 0 ≤ (digits p r).getD j 0)).card =
    ((List.range n).map (fun j => p - (digits p k).getD j 0)).prod := by
  have hp0 : 0 < p := Nat.lt_trans Nat.zero_lt_one hp
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    -- Abbreviations
    let P := fun (m : ℕ) =>
      ∀ j < n + 1, (digits p k).getD j 0 ≤ (digits p m).getD j 0
    let Q := fun (q : ℕ) =>
      ∀ j < n, (digits p (k / p)).getD j 0 ≤ (digits p q).getD j 0

    -- Step 1: Split predicate via Euclidean decomposition
    have h_split (q d : ℕ) (hd : d < p) :
        P (q * p + d) ↔ ((digits p k).getD 0 0 ≤ d ∧ Q q) := by
      simp only [P, Q]
      constructor
      · intro h
        refine ⟨?_, fun j hj => ?_⟩
        · have h0 := h 0 (Nat.zero_lt_succ n)
          rw [getD_digits_zero p k hp, getD_digits_zero p (q * p + d) hp,
              mod_qpd p q d hd] at h0
          rw [getD_digits_zero p k hp]
          exact h0
        · have hj1 := h (j + 1) (Nat.succ_lt_succ hj)
          rw [getD_digits_succ p k j hp, getD_digits_succ p (q * p + d) j hp,
              div_qpd p q d hp0 hd] at hj1
          exact hj1
      · rintro ⟨h0, hQ⟩ j hj
        cases j with
        | zero =>
          rw [getD_digits_zero p (q * p + d) hp, mod_qpd p q d hd]
          exact h0
        | succ j =>
          rw [getD_digits_succ p (q * p + d) j hp, div_qpd p q d hp0 hd]
          rw [getD_digits_succ p k j hp]
          exact hQ j (Nat.lt_of_succ_lt_succ hj)

    -- Step 2: Euclidean embedding f : ℕ × ℕ → ℕ
    let f := fun (x : ℕ × ℕ) => x.1 * p + x.2

    have hf : Set.InjOn f (↑(range (p ^ n) ×ˢ range p) : Set (ℕ × ℕ)) := by
      intro ⟨q1, d1⟩ h1 ⟨q2, d2⟩ h2 heq
      simp only [mem_product, mem_range, mem_coe] at h1 h2
      simp only [f] at heq
      have hq : q1 = q2 := by
        rw [← div_qpd p q1 d1 hp0 h1.2, ← div_qpd p q2 d2 hp0 h2.2, heq]
      subst hq
      exact Prod.ext rfl (by linarith)

    have h_im : (range (p ^ n) ×ˢ range p).image f = range (p ^ n * p) := by
      ext n_val
      simp only [f, mem_image, mem_product, mem_range]
      constructor
      · rintro ⟨⟨q, d⟩, ⟨hq, hd⟩, rfl⟩
        nlinarith [Nat.succ_le_of_lt hq]
      · intro hn
        exact ⟨⟨n_val / p, n_val % p⟩,
          ⟨(Nat.div_lt_iff_lt_mul hp0).mpr hn, Nat.mod_lt _ hp0⟩,
          by nlinarith [Nat.div_add_mod n_val p, mul_comm p (n_val / p)]⟩

    -- Step 3: Filter decomposition
    have h_filt : (range (p ^ n) ×ˢ range p).filter (fun x => P (f x)) =
        (range (p ^ n)).filter Q ×ˢ
        (range p).filter (fun d => (digits p k).getD 0 0 ≤ d) := by
      ext ⟨q, d⟩
      simp only [f, mem_filter, mem_product, mem_range]
      constructor
      · rintro ⟨⟨hq, hd⟩, hP⟩
        exact ⟨⟨hq, ((h_split q d hd).mp hP).2⟩,
               hd, ((h_split q d hd).mp hP).1⟩
      · rintro ⟨⟨hq, hQ⟩, hd, h0⟩
        exact ⟨⟨hq, hd⟩, (h_split q d hd).mpr ⟨h0, hQ⟩⟩

    -- Step 4: Assemble
    have key : ((range (p ^ (n + 1))).filter P).card =
        ((range (p ^ n)).filter Q).card *
        ((range p).filter (fun d => (digits p k).getD 0 0 ≤ d)).card := by
      rw [pow_succ, ← h_im, filter_image,
          Finset.card_image_of_injOn (hf.mono (fun _ h => (mem_filter.mp h).1)),
          h_filt, card_product]

    rw [key, ih (k / p)]

    -- Step 5: Reassemble the product
    rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, mul_comm]
    congr 1
    · have : (range p).filter (fun d => (digits p k).getD 0 0 ≤ d) =
          Ico ((digits p k).getD 0 0) p := by
        ext d; simp only [mem_filter, mem_range, mem_Ico]
        exact ⟨fun ⟨a, b⟩ => ⟨b, a⟩, fun ⟨a, b⟩ => ⟨b, a⟩⟩
      rw [this, card_Ico]
    · rw [List.map_map]; congr 1
      apply List.map_congr_left
      intro j _
      simp only [Function.comp_apply]
      rw [getD_digits_succ p k j hp]

/-! ### Main Theorems -/

theorem card_KummerValid (p k : ℕ) (hp : p.Prime) :
    (KummerValid p k).card =
    ((List.range (L_p p k)).map (fun j => p - dig p k j)).prod := by
  have hp_one := hp.one_lt
  unfold KummerValid dig
  show ((range (p ^ L_p p k)).filter (fun r =>
    ∀ j < L_p p k, (digits p k).getD j 0 ≤ (digits p r).getD j 0)).card =
    ((List.range (L_p p k)).map (fun j => p - (digits p k).getD j 0)).prod
  have : L_p p k = (digits p k).length := by unfold L_p; simp [hp_one]
  rw [this]
  exact card_filter_digits_le p (digits p k).length k hp_one

/-- Density bound for k ∈ [2, 700], proved by verified computation.
For k > 700, the density bound is not needed directly — the proof uses
`crt_density_from_asymptotic` (KGe29.lean) which bridges to deterministic coverage. -/
theorem erdos_asymptotic_density_bound (k : ℕ) (h_large : k ≥ 2) (h_small : k ≤ 700) :
    total_density k < 1 / (k : ℝ) ^ 2 :=
  densityRangeCheck_sound 2 700 (by norm_num) density_verified_700 k h_large h_small

end Erdos1094
