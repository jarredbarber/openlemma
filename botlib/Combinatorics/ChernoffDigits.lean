/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Provenance: Originally proved by LLM agents (Claude, Anthropic) working on
Erdős Problem 728, with zero human mathematical input.
Trust level: 🟢 Compiler-verified (zero sorrys, zero axioms).
-/
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Independence.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Order.Interval.Finset.Nat
import botlib.Combinatorics.DigitSpace

/-!
# Chernoff Bounds over Digit Spaces

Concentration inequalities for the count of "high" digits in a uniformly
random base-p digit vector. Uses Hoeffding's inequality (sub-Gaussian MGF
bounds from Mathlib) applied to indicator random variables over the product
measure on `Fin D → Fin p`.

## Main Results

* `count_few_high_digits_aux` — probability bound on few high digits
* `count_few_high_digits_bound_chernoff` — cardinality bound: number of
  digit vectors with few high digits is at most `p^D · exp(-2δ²/D)`

## Applications

These bounds are used to show that "most" digit vectors have many high digits,
which (via Kummer's criterion) means most binomial coefficients are divisible
by small primes. This is the key probabilistic ingredient in proofs about
the distribution of prime factors of C(n,k).
-/

open Real MeasureTheory ProbabilityTheory OpenLemma.DigitSpace
open scoped Nat BigOperators ENNReal Classical

namespace OpenLemma.ChernoffDigits

variable {D p : ℕ} [NeZero p]

-- Define measurable space on components
instance : MeasurableSpace (Fin p) := ⊤
instance : MeasurableSingletonClass (Fin p) := ⟨fun _ => trivial⟩

/-- The uniform probability measure on `Fin p`. -/
noncomputable def probFin (p : ℕ) : Measure (Fin p) :=
  (p : ℝ≥0∞)⁻¹ • Measure.count

instance isProb_probFin : IsProbabilityMeasure (probFin p) := by
  constructor
  rw [probFin, Measure.smul_apply, Measure.count_univ]
  rw [ENat.card_eq_coe_fintype_card, Fintype.card_fin]
  have h_ne_zero : (p : ℝ≥0∞) ≠ 0 := by simp [NeZero.ne p]
  have h_ne_top : (p : ℝ≥0∞) ≠ ⊤ := by simp
  rw [smul_eq_mul]
  exact ENNReal.inv_mul_cancel h_ne_zero h_ne_top

/-- The uniform probability measure on `DigitSpace D p`. -/
noncomputable def probDigitSpace (D p : ℕ) : Measure (DigitSpace D p) :=
  Measure.pi (fun _ => probFin p)

instance isProb_probDigitSpace : IsProbabilityMeasure (probDigitSpace D p) := by
  constructor
  rw [probDigitSpace, Measure.pi_univ]
  simp only [measure_univ, Finset.prod_const_one]

/-- The indicator function for the i-th digit being high. -/
noncomputable def highIndicator (i : Fin D) (m : DigitSpace D p) : ℝ :=
  if isHigh p (m i) then 1 else 0

lemma expectation_highIndicator (i : Fin D) :
    (probDigitSpace D p)[highIndicator i] = probHigh p := by
  dsimp [probHigh]
  let proj : DigitSpace D p → Fin p := fun m => m i
  have h_meas : MeasurePreserving proj (probDigitSpace D p) (probFin p) :=
    measurePreserving_eval (fun _ => probFin p) i
  let f : Fin p → ℝ := fun d => if isHigh p d then 1 else 0
  have h_comp : highIndicator i = f ∘ proj := rfl
  rw [h_comp]
  change ∫ x, f (x i) ∂(probDigitSpace D p) = _
  rw [← integral_map (measurable_pi_apply i).aemeasurable]
  rotate_left
  · rw [h_meas.map_eq]
    exact Integrable.of_finite.aestronglyMeasurable
  rw [h_meas.map_eq]
  rw [probFin]
  rw [integral_smul_measure]
  rw [integral_count]
  simp_rw [f]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero]
  rw [Finset.sum_const]
  rw [nsmul_eq_mul, mul_one]
  have h_card : (Finset.filter (isHigh p) Finset.univ).card = p / 2 := by
    rw [← Finset.card_map Fin.valEmbedding]
    have h_p : isHigh p = (fun n => (p + 1) / 2 ≤ n) ∘ Fin.valEmbedding := rfl
    simp_rw [h_p]
    rw [← Finset.filter_map]
    have h_map : Finset.map Fin.valEmbedding (Finset.univ : Finset (Fin p)) = Finset.range p := by
      ext x
      simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_range]
      constructor
      · rintro ⟨y, rfl⟩; exact y.is_lt
      · intro hx; use ⟨x, hx⟩; rfl
    rw [h_map]
    have h_ico : Finset.filter (fun x => (p + 1) / 2 ≤ x) (Finset.range p) = Finset.Ico ((p + 1) / 2) p := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      tauto
    rw [h_ico]
    rw [Nat.card_Ico]
    omega
  rw [h_card]
  rw [ENNReal.toReal_inv]
  rw [ENNReal.toReal_natCast]
  rw [smul_eq_mul]
  rw [inv_mul_eq_div]

lemma indep_highIndicator :
    iIndepFun (fun i => highIndicator i) (probDigitSpace D p) := by
  let X (i : Fin D) (d : Fin p) : ℝ := if isHigh p d then 1 else 0
  have h_meas (i : Fin D) : AEMeasurable (X i) (probFin p) := by
    apply Measurable.aemeasurable
    measurability
  convert iIndepFun_pi h_meas using 1

lemma prob_eq_count_div_total (S : Set (DigitSpace D p)) :
    (probDigitSpace D p S).toReal = (Fintype.card S : ℝ) / (p ^ D : ℝ) := by
  let μ := probDigitSpace D p
  have h_sing_enn (x : DigitSpace D p) : μ {x} = ((p : ℝ≥0∞)⁻¹)^D := by
    dsimp [μ, probDigitSpace]
    rw [Measure.pi_singleton]
    simp only [probFin]
    have h_term (i : Fin D) : ((p : ℝ≥0∞)⁻¹ • Measure.count : Measure (Fin p)) {x i} = (p : ℝ≥0∞)⁻¹ := by
      rw [Measure.smul_apply, Measure.count_singleton, smul_eq_mul, mul_one]
    rw [Finset.prod_congr rfl (fun i _ => h_term i)]
    rw [Finset.prod_const]
    rw [Finset.card_fin]
  have h_sing (x : DigitSpace D p) : (μ {x}).toReal = 1 / (p ^ D : ℝ) := by
    rw [h_sing_enn]
    rw [ENNReal.toReal_pow]
    rw [ENNReal.toReal_inv]
    rw [ENNReal.toReal_natCast]
    rw [one_div, inv_pow]
  have h_meas : MeasurableSet S := S.toFinite.measurableSet
  rw [← MeasureTheory.Measure.tsum_indicator_apply_singleton _ _ h_meas]
  rw [tsum_fintype]
  rw [ENNReal.toReal_sum]
  rotate_left
  · intro x _
    rw [Set.indicator_apply]
    split_ifs
    · exact measure_ne_top _ _
    · simp
  simp_rw [Set.indicator_apply]
  have h_ite : ∀ x, (if x ∈ S then μ {x} else 0).toReal = if x ∈ S then (μ {x}).toReal else 0 := by
    intro x
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun x _ => h_ite x)]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero]
  have h_filter : (Finset.filter (fun x => x ∈ S) Finset.univ) = S.toFinset := by
    ext; simp
  rw [h_filter]
  rw [Finset.sum_congr rfl (fun x _ => h_sing x)]
  rw [Finset.sum_const]
  rw [nsmul_eq_mul]
  rw [Set.toFinset_card]
  rw [mul_one_div]

lemma probHigh_nonneg (p : ℕ) [NeZero p] : 0 ≤ probHigh p := by
  unfold probHigh
  apply div_nonneg
  · norm_cast; apply Nat.zero_le
  · norm_cast; apply Nat.zero_le

lemma probHigh_le_one (p : ℕ) [NeZero p] : probHigh p ≤ 1 := by
  unfold probHigh
  rw [div_le_one]
  · norm_cast; apply Nat.div_le_self
  · norm_cast; apply Nat.pos_of_ne_zero (NeZero.ne p)

lemma integrable_highIndicator (i : Fin D) : Integrable (highIndicator i) (probDigitSpace D p) := by
  apply Integrable.of_finite

lemma highDigitCount_eq_sum (m : DigitSpace D p) :
    (highDigitCount m : ℝ) = ∑ i, highIndicator i m := by
  unfold highDigitCount highIndicator
  have h_term (i : Fin D) : (if isHigh p (m i) then 1 else 0 : ℝ) = ((if isHigh p (m i) then 1 else 0 : ℕ) : ℝ) := by
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun i _ => h_term i)]
  rw [← Nat.cast_sum]
  congr
  rw [Finset.sum_boole]
  simp

/-- Probability that a random digit vector has few high digits is exponentially small. -/
lemma count_few_high_digits_aux (t : ℝ) (ht : t < (D * probHigh p)) :
    (probDigitSpace D p {m | (highDigitCount m : ℝ) ≤ t}).toReal ≤
    exp (-2 * ((D * probHigh p) - t)^2 / D) := by
  by_cases hD : D = 0
  · subst hD
    simp only [Nat.cast_zero, zero_mul] at ht
    have : {m : DigitSpace 0 p | (highDigitCount m : ℝ) ≤ t} = ∅ := by
      ext m
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      have : highDigitCount m = 0 := by
        unfold highDigitCount
        simp
      rewrite [this]
      norm_cast
      linarith
    rw [this, measure_empty, ENNReal.toReal_zero]
    apply exp_nonneg
  have hD_ne_zero : (D : ℝ) ≠ 0 := by exact_mod_cast hD
  let Y (i : Fin D) (m : DigitSpace D p) := -(highIndicator i m - probHigh p)
  let c : Fin D → NNReal := fun _ => ⟨1/4, by norm_num⟩
  have h_indep : iIndepFun Y (probDigitSpace D p) := by
    apply iIndepFun.comp indep_highIndicator (fun _ x => -(x - probHigh p))
    intro i
    exact measurable_id.sub (measurable_const) |>.neg
  have h_bound_Y (i) : ∀ᵐ m ∂(probDigitSpace D p), Y i m ∈ Set.Icc (probHigh p - 1) (probHigh p) := by
    apply ae_of_all
    intro m
    simp only [Y, highIndicator]
    split_ifs
    · rw [Set.mem_Icc]; constructor <;> linarith
    · rw [Set.mem_Icc]; constructor <;> linarith
  have h_int_Y (i) : ∫ m, Y i m ∂(probDigitSpace D p) = 0 := by
    simp only [Y]
    rw [integral_neg, integral_sub (integrable_highIndicator i) (integrable_const _)]
    rw [expectation_highIndicator, integral_const]
    simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul, sub_self, neg_zero]
  have h_subg (i : Fin D) : HasSubgaussianMGF (Y i) (c i) (probDigitSpace D p) := by
    convert ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (hm := AEMeasurable.neg ((integrable_highIndicator i).aemeasurable.sub_const (probHigh p)))
      (hb := h_bound_Y i) (hc := h_int_Y i)
      (a := probHigh p - 1) (b := probHigh p)
    · simp only [c]
      rw [show probHigh p - (probHigh p - 1) = 1 by ring]
      ext; push_cast; norm_num
  let ε := (D : ℝ) * probHigh p - t
  have hε : 0 ≤ ε := sub_nonneg.mpr (le_of_lt ht)
  have h_event : {m | (highDigitCount m : ℝ) ≤ t} = {m | ε ≤ ∑ i, Y i m} := by
    ext m
    simp only [Set.mem_setOf_eq, Y]
    rw [Finset.sum_neg_distrib, Finset.sum_sub_distrib]
    rw [Finset.sum_const, Finset.card_fin]
    rw [nsmul_eq_mul]
    rw [← highDigitCount_eq_sum m]
    dsimp [ε]
    rw [neg_sub, sub_le_sub_iff_left]
  rw [h_event]
  have h_sum_c : ∑ i : Fin D, c i = D * (1/4 : NNReal) := by
    simp only [c]
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    ext; push_cast; ring
  have h_hoeff := ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun h_indep (s := Finset.univ) (fun i _ => h_subg i) hε
  convert h_hoeff using 1
  rw [h_sum_c]
  congr 1
  dsimp [ε]
  push_cast
  field_simp [hD_ne_zero]
  ring

/-- **Chernoff bound for digit spaces**: The number of digit vectors with
few high digits is at most `p^D · exp(-2δ²/D)` where δ is the deviation
from the expected count. -/
lemma count_few_high_digits_bound_chernoff (t : ℝ) (ht : t < (D * probHigh p)) :
    (Finset.univ.filter (fun m : DigitSpace D p => (highDigitCount m : ℝ) ≤ t)).card ≤
    p ^ D * exp (-2 * ((D * probHigh p) - t)^2 / D) := by
  have h_prob := count_few_high_digits_aux t ht
  let S := {m : DigitSpace D p | (highDigitCount m : ℝ) ≤ t}
  rw [prob_eq_count_div_total S] at h_prob
  have h_card : (Finset.univ.filter (fun m : DigitSpace D p => (highDigitCount m : ℝ) ≤ t)).card = Fintype.card S := by
    rw [Fintype.card_ofFinset]
    rfl
  rw [← h_card] at h_prob
  have h_pos : (0 : ℝ) < p ^ D := by
    norm_cast
    apply pow_pos
    exact Nat.pos_of_ne_zero (NeZero.ne p)
  rw [div_le_iff₀ h_pos] at h_prob
  rw [mul_comm] at h_prob
  exact h_prob

end OpenLemma.ChernoffDigits
