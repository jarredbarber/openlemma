/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Soundness of the Cook-Levin tableau reduction.
Theorem: If the machine V accepts the input in T steps, then the generated
formula `tableauFormula` is satisfiable.
-/
import botlib.Complexity.CookLevin.Tableau
import botlib.Complexity.CookLevin.Correctness
import Mathlib.Computability.TMComputable
import Mathlib.Data.Fintype.Basic

namespace CookLevinTableau

open Turing List OpenLemma.Complexity.SAT Encodable

variable {V : FinTM2} [Encodable V.Λ] [Encodable V.σ] [Encodable V.K] [∀ k, Encodable (V.Γ k)]
  [Fintype V.Λ] [Fintype V.σ] [Fintype V.K] [∀ k, Fintype (V.Γ k)]
  [DecidableEq V.Λ] [DecidableEq V.σ] [DecidableEq V.K] [∀ k, DecidableEq (V.Γ k)]
  [∀ k, Nonempty (V.Γ k)]

/-- Construct a valuation from a computation trace. -/
noncomputable def traceValuation (c : ℕ → V.Cfg) : TableauVar V → Bool
  | .label i l => decide ((c i).l = l)
  | .state i s => decide ((c i).var = s)
  | .stkLen i k len => decide (((c i).stk k).length = len)
  | .stkElem i k j γ => 
      let stk := (c i).stk k
      if h : j < stk.length then
        decide (stk.reverse.get ⟨j, by simp [stk.length_reverse]; exact h⟩ = γ)
      else
        decide (γ = Classical.choice (inferInstance : Nonempty (V.Γ k)))
  | .cert _ => false

/-- The boolean assignment corresponding to a trace. -/
noncomputable def traceAssignment (c : ℕ → V.Cfg) (v_idx : ℕ) : Bool :=
  match decode (α := TableauVar V) v_idx with
  | some v => traceValuation c v
  | none => false

/-! ## Helper lemmas -/

theorem evalTLit_trace (c : ℕ → V.Cfg) (v : TableauVar V) (b : Bool) :
    evalLiteral (traceAssignment c) (tLit V v b) = (if b then traceValuation c v else !(traceValuation c v)) := by
  unfold tLit
  cases b <;> simp [evalLiteral, traceAssignment, encodek v]

/-- Exactly one variable in a list of tableau variables is true under the trace valuation. -/
theorem traceValuation_exactlyOne (c : ℕ → V.Cfg) (vars : List (TableauVar V)) (h_nodup : vars.Nodup)
    (h_unique : ∃! v, v ∈ vars ∧ traceValuation c v = true) :
    evalCNF (traceAssignment c) (exactlyOne V vars) = true := by
  unfold exactlyOne evalCNF
  simp only [all_cons, Bool.and_eq_true]
  rcases h_unique with ⟨v, ⟨hv_mem, hv_val⟩, h_unique⟩
  constructor
  · -- at least one
    rw [evalClause, List.any_eq_true]
    use tLit V v true
    simp [hv_mem, evalTLit_trace, hv_val]
  · -- at most one
    rw [List.all_flatMap, List.all_eq_true]
    intro tl h_tl
    match tl with
    | [] => rfl
    | v' :: tl' =>
      rw [List.all_map, List.all_eq_true]
      intro w hw
      simp only [evalClause, any_cons, any_nil, Bool.or_false]
      rw [evalTLit_trace, evalTLit_trace]; simp [ite_false]
      by_contra h_both
      simp only [Bool.not_eq_true, Bool.not_not_eq_true] at h_both
      rcases h_both with ⟨hv'_val, hw_val⟩
      have ev : v' = v := h_unique v' ⟨mem_of_mem_tails h_tl (mem_cons_self _ _), hv'_val⟩
      have ew : w = v := h_unique w ⟨mem_of_mem_tails h_tl (mem_cons_of_mem _ hw), hw_val⟩
      subst ev ew
      have h_v_in_tl' : v ∈ tl' := hw
      have h_tl_in_tails : tl ∈ vars.tails := h_tl
      have : ¬ tl.Nodup := by simp [h_v_in_tl']
      exact this (h_nodup.tails.mem h_tl_in_tails)

lemma TableauVar_label_inj (i : ℕ) : Function.Injective (TableauVar.label (V:=V) i) := fun _ _ h => by injection h
lemma TableauVar_state_inj (i : ℕ) : Function.Injective (TableauVar.state (V:=V) i) := fun _ _ h => by injection h
lemma TableauVar_stkLen_inj (i : ℕ) (k : V.K) : Function.Injective (TableauVar.stkLen (V:=V) i k) := fun _ _ h => by injection h
lemma TableauVar_stkElem_inj (i : ℕ) (k : V.K) (j : ℕ) : Function.Injective (TableauVar.stkElem (V:=V) i k j) := fun _ _ h => by injection h

/-! ## Satisfaction of each constraint group -/

theorem satisfies_consistency (params : Params V) (c : ℕ → V.Cfg)
    (h_depth : ∀ i ≤ params.timeBound, ∀ k, ((c i).stk k).length ≤ params.maxStackDepth) :
    evalCNF (traceAssignment c) (consistencyConstraints params) = true := by
  unfold consistencyConstraints evalCNF
  simp only [all_append, Bool.and_eq_true]
  repeat constructor
  · rw [List.all_flatMap, List.all_eq_true]; intro i _
    apply traceValuation_exactlyOne
    · apply List.Nodup.map (TableauVar_label_inj i) (Finset.nodup_toList _)
    · apply ExistsUnique.intro (TableauVar.label i (c i).l)
      · simp [traceValuation]
      · intro v' ⟨hv'_mem, hv'_val⟩
        simp only [mem_map] at hv'_mem
        rcases hv'_mem with ⟨l', _, rfl⟩
        simp [traceValuation] at hv'_val
        rw [decide_eq_true_iff] at hv'_val
        subst hv'_val; rfl
  · rw [List.all_flatMap, List.all_eq_true]; intro i _
    apply traceValuation_exactlyOne
    · apply List.Nodup.map (TableauVar_state_inj i) (Finset.nodup_toList _)
    · apply ExistsUnique.intro (TableauVar.state i (c i).var)
      · simp [traceValuation]
      · intro v' ⟨hv'_mem, hv'_val⟩
        simp only [mem_map] at hv'_mem
        rcases hv'_mem with ⟨s', _, rfl⟩
        simp [traceValuation] at hv'_val
        rw [decide_eq_true_iff] at hv'_val
        subst hv'_val; rfl
  · rw [List.all_flatMap, List.all_eq_true]; intro i _
    rw [List.all_flatMap, List.all_eq_true]; intro k _
    rw [List.all_flatMap, List.all_eq_true]; intro j _
    let stk := (c i).stk k
    let γ := if h : j < stk.length then stk.reverse.get ⟨j, by simp [stk.length_reverse]; exact h⟩ else Classical.choice (inferInstance : Nonempty (V.Γ k))
    apply traceValuation_exactlyOne
    · apply List.Nodup.map (TableauVar_stkElem_inj i k j) (Finset.nodup_toList _)
    · apply ExistsUnique.intro (TableauVar.stkElem i k j γ)
      · simp [traceValuation, γ]
      · intro v' ⟨hv'_mem, hv'_val⟩
        simp only [mem_map] at hv'_mem
        rcases hv'_mem with ⟨γ', _, rfl⟩
        simp [traceValuation] at hv'_val
        subst rfl
        congr
        simp [γ] at hv'_val
        split at hv'_val <;> split at γ <;> try simp at hv'_val <;> try rw [decide_eq_true_iff] at hv'_val <;> try exact hv'_val
  · rw [List.all_flatMap, List.all_eq_true]; intro i hi
    rw [List.all_flatMap, List.all_eq_true]; intro k _
    apply traceValuation_exactlyOne
    · apply List.Nodup.map (TableauVar_stkLen_inj i k) (nodup_range _)
    · apply ExistsUnique.intro (TableauVar.stkLen i k ((c i).stk k).length)
      · constructor
        · simp; apply Nat.lt_succ_of_le; apply h_depth; simp at hi; exact hi
        · simp [traceValuation]
      · intro v' ⟨hv'_mem, hv'_val⟩
        simp only [mem_map] at hv'_mem
        rcases hv'_mem with ⟨len', _, rfl⟩
        simp [traceValuation] at hv'_val
        rw [decide_eq_true_iff] at hv'_val
        subst hv'_val; rfl

theorem satisfies_initial (params : Params V) (inputContents : List (V.Γ V.k₀)) (c : ℕ → V.Cfg)
    (h_init : c 0 = { l := some V.main, var := V.initialState, stk := fun k => if h : k = V.k₀ then h ▸ inputContents else [] }) :
    evalCNF (traceAssignment c) (initialConstraints params inputContents) = true := by
  unfold initialConstraints evalCNF
  simp only [all_append, all_cons, all_nil, Bool.and_true]
  repeat constructor
  · rw [evalClause, List.any_eq_true]; use tLit V (TableauVar.label 0 (some V.main)) true; constructor; · simp; · rw [evalTLit_trace, traceValuation, h_init]; simp
  · rw [evalClause, List.any_eq_true]; use tLit V (TableauVar.state 0 V.initialState) true; constructor; · simp; · rw [evalTLit_trace, traceValuation, h_init]; simp
  · rw [evalClause, List.any_eq_true]; use tLit V (TableauVar.stkLen 0 V.k₀ inputContents.length) true; constructor; · simp; · rw [evalTLit_trace, traceValuation, h_init]; simp
  · rw [List.all_map, List.all_eq_true]; intro ⟨γ, j⟩ hj
    rw [evalClause, List.any_eq_true]; use tLit V (TableauVar.stkElem 0 V.k₀ j γ) true
    constructor
    · simp only [mem_map, zipIdx_zip_range, mem_zip, mem_reverse, range_length, true_and]; use (γ, j)
    · rw [evalTLit_trace, traceValuation, h_init]
      have h_mem := mem_zipIdx.mp hj
      have h_len : j < inputContents.length := by
        simp [length_reverse] at h_mem; exact h_mem.right
      simp [h_len]
      simp [get_eq_getElem] at h_mem
      exact h_mem.left.symm
  · rw [List.all_flatMap, List.all_eq_true]; intro k hk
    rw [evalClause, List.any_eq_true]; use tLit V (TableauVar.stkLen 0 k 0) true
    constructor
    · simp; use k
    · rw [evalTLit_trace, traceValuation, h_init]
      split at hk <;> simp at hk
      simp [hk]

theorem satisfies_transition (params : Params V) (c : ℕ → V.Cfg)
    (h_step : ∀ i < params.timeBound, c (i + 1) = (V.step (c i)).getD (c i)) :
    evalCNF (traceAssignment c) (transitionConstraints params) = true := by
  sorry

theorem satisfies_frame (params : Params V) (c : ℕ → V.Cfg)
    (h_step : ∀ i < params.timeBound, c (i + 1) = (V.step (c i)).getD (c i)) :
    evalCNF (traceAssignment c) (framePreservation params) = true := by
  sorry

theorem satisfies_acceptance (params : Params V) (c : ℕ → V.Cfg)
    (h_halt : ∃ i ≤ params.timeBound, (c i).l = none) :
    evalCNF (traceAssignment c) (acceptanceConstraints params) = true := by
  unfold acceptanceConstraints evalCNF
  simp only [all_cons, all_nil, Bool.and_true]
  rcases h_halt with ⟨i, hi, h_l⟩
  rw [evalClause, List.any_eq_true]
  use tLit V (TableauVar.label i none) true
  constructor
  · simp only [mem_map, mem_range]; use i; exact ⟨Nat.lt_succ_of_le hi, rfl⟩
  · rw [evalTLit_trace, traceValuation, h_l]; simp

/-- Main Soundness Theorem: Acceptance implies satisfiability. -/
theorem reduction_sound (params : Params V) (inputContents : List (V.Γ V.k₀))
    (c : ℕ → V.Cfg)
    (h_init : c 0 = { l := some V.main, var := V.initialState, stk := fun k => if h : k = V.k₀ then h ▸ inputContents else [] })
    (h_step : ∀ i < params.timeBound, c (i + 1) = (V.step (c i)).getD (c i))
    (h_depth : ∀ i ≤ params.timeBound, ∀ k, ((c i).stk k).length ≤ params.maxStackDepth)
    (h_halt : ∃ i ≤ params.timeBound, (c i).l = none) :
    Satisfiable (tableauFormula params inputContents) := by
  use traceAssignment c
  unfold tableauFormula
  simp only [evalCNF, all_append, Bool.and_eq_true]
  repeat constructor
  · exact satisfies_consistency params c h_depth
  · exact satisfies_initial params inputContents c h_init
  · exact satisfies_transition params c h_step
  · exact satisfies_frame params c h_step
  · exact satisfies_acceptance params c h_halt

end CookLevinTableau
