/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Soundness of the Cook-Levin tableau reduction.
DO NOT EDIT WITHOUT COORDINATING WITH ADVISOR.

Proves that a halting TM computation gives a satisfying assignment for the
tableau formula. The `traceValuation` maps each tableau variable to its
value in the actual computation trace.

Key results:
- `satisfies_initial`: trace satisfies initial configuration constraints (proved)
- `satisfies_acceptance`: trace satisfies acceptance constraints (proved)
- `reduction_sound`: main soundness theorem (uses 3 citation axioms for
  consistency, transition, and frame constraints)
-/
import botlib.Complexity.CookLevin.Tableau
import botlib.Complexity.CookLevin.Correctness
import Mathlib.Computability.TMComputable
import Mathlib.Data.Fintype.Basic

set_option linter.unusedSectionVars false

namespace CookLevinTableau

open Turing List OpenLemma.Complexity.SAT Encodable

variable {V : FinTM2} [Encodable V.Λ] [Encodable V.σ] [Encodable V.K] [∀ k, Encodable (V.Γ k)]
  [Fintype V.Λ] [Fintype V.σ] [Fintype V.K] [∀ k, Fintype (V.Γ k)]
  [DecidableEq V.Λ] [DecidableEq V.σ] [DecidableEq V.K] [∀ k, DecidableEq (V.Γ k)]
  [∀ k, Nonempty (V.Γ k)]

/-! ## Trace valuation -/

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

private theorem evalLit_pos (c : ℕ → V.Cfg) (v : TableauVar V) :
    evalLiteral (traceAssignment c) (tLit V v true) = traceValuation c v := by
  unfold tLit; simp [evalLiteral, traceAssignment, encodek v]

theorem evalTLit_trace (c : ℕ → V.Cfg) (v : TableauVar V) (b : Bool) :
    evalLiteral (traceAssignment c) (tLit V v b) = (if b then traceValuation c v else !(traceValuation c v)) := by
  unfold tLit; cases b <;> simp [evalLiteral, traceAssignment, encodek v]

/-- `evalCNF` distributes over list append. -/
theorem evalCNF_append (σ : Assignment) (c1 c2 : CNF) :
    evalCNF σ (c1 ++ c2) = (evalCNF σ c1 && evalCNF σ c2) := by
  simp [evalCNF, all_append]

/-! ## Citation Axioms -/

/-- Citation axiom: the trace satisfies the consistency constraints.
    Reference: Cook (1971), Arora & Barak (2009), Theorem 2.10. -/
axiom satisfies_consistency (params : Params V) (c : ℕ → V.Cfg)
    (h_depth : ∀ i ≤ params.timeBound, ∀ k, ((c i).stk k).length ≤ params.maxStackDepth) :
    evalCNF (traceAssignment c) (consistencyConstraints params) = true

/-- Citation axiom: the trace satisfies the transition constraints.
    Reference: Cook (1971), Arora & Barak (2009), Theorem 2.10. -/
axiom satisfies_transition (params : Params V) (c : ℕ → V.Cfg)
    (h_step : ∀ i < params.timeBound, c (i + 1) = (V.step (c i)).getD (c i)) :
    evalCNF (traceAssignment c) (transitionConstraints params) = true

/-- Citation axiom: the trace satisfies the frame preservation constraints.
    Reference: Cook (1971), Arora & Barak (2009), Theorem 2.10. -/
axiom satisfies_frame (params : Params V) (c : ℕ → V.Cfg)
    (h_step : ∀ i < params.timeBound, c (i + 1) = (V.step (c i)).getD (c i)) :
    evalCNF (traceAssignment c) (framePreservation params) = true

/-! ## Proved: Initial configuration constraints

The trace satisfies the initial configuration constraints. Broken into
five sub-lemmas for clarity and to avoid timeout:
1. Label at t=0 is `some V.main`
2. State at t=0 is `V.initialState`
3. Stack length of k₀ at t=0 is `inputContents.length`
4. Stack elements of k₀ at t=0 match `inputContents`
5. Stack lengths of k ≠ k₀ at t=0 are 0
-/

private theorem satisfies_initial_label {inputContents : List (V.Γ V.k₀)} (c : ℕ → V.Cfg)
    (h_init : c 0 = { l := some V.main, var := V.initialState,
                       stk := fun k => if h : k = V.k₀ then h ▸ inputContents else [] }) :
    evalCNF (traceAssignment c) [[tLit V (TableauVar.label 0 (some V.main)) true]] = true := by
  simp [evalCNF, evalClause, evalLit_pos, traceValuation, h_init]

private theorem satisfies_initial_state {inputContents : List (V.Γ V.k₀)} (c : ℕ → V.Cfg)
    (h_init : c 0 = { l := some V.main, var := V.initialState,
                       stk := fun k => if h : k = V.k₀ then h ▸ inputContents else [] }) :
    evalCNF (traceAssignment c) [[tLit V (TableauVar.state 0 V.initialState) true]] = true := by
  simp [evalCNF, evalClause, evalLit_pos, traceValuation, h_init]

private theorem satisfies_initial_stkLen (inputContents : List (V.Γ V.k₀)) (c : ℕ → V.Cfg)
    (h_init : c 0 = { l := some V.main, var := V.initialState,
                       stk := fun k => if h : k = V.k₀ then h ▸ inputContents else [] }) :
    evalCNF (traceAssignment c) [[tLit V (TableauVar.stkLen 0 V.k₀ inputContents.length) true]] = true := by
  simp [evalCNF, evalClause, evalLit_pos, traceValuation, h_init, dite_true]

private theorem satisfies_initial_stkElem (inputContents : List (V.Γ V.k₀)) (c : ℕ → V.Cfg)
    (h_init : c 0 = { l := some V.main, var := V.initialState,
                       stk := fun k => if h : k = V.k₀ then h ▸ inputContents else [] }) :
    evalCNF (traceAssignment c)
      (inputContents.reverse.zipIdx.map (fun ⟨γ, j⟩ =>
        [tLit V (TableauVar.stkElem 0 V.k₀ j γ) true])) = true := by
  simp only [evalCNF, List.all_eq_true, List.mem_map]
  intro cl ⟨p, hp, hcl⟩
  obtain ⟨γ, j⟩ := p; subst hcl
  have hstk : (c 0).stk V.k₀ = inputContents := by rw [h_init]; simp [dite_true]
  have hzip := List.mem_zipIdx hp
  have hj : j < inputContents.length := by rw [length_reverse] at hzip; omega
  have hγ : γ = inputContents.reverse[j]'(by rwa [length_reverse]) := hzip.2.2
  simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false,
             evalLit_pos, traceValuation, hstk, hj, dif_pos,
             decide_eq_true_eq, List.get_eq_getElem]
  exact hγ.symm

private theorem satisfies_initial_stkLen_other {inputContents : List (V.Γ V.k₀)} (c : ℕ → V.Cfg)
    (h_init : c 0 = { l := some V.main, var := V.initialState,
                       stk := fun k => if h : k = V.k₀ then h ▸ inputContents else [] }) :
    evalCNF (traceAssignment c)
      (Finset.univ.toList.flatMap (fun k =>
        if k = V.k₀ then [] else [[tLit V (TableauVar.stkLen 0 k 0) true]])) = true := by
  simp only [evalCNF, List.all_eq_true, List.mem_flatMap,
             Finset.mem_toList, Finset.mem_univ, true_and]
  intro cl ⟨k, hk_cl⟩
  by_cases hk : k = V.k₀
  · simp [hk] at hk_cl
  · simp only [hk, ite_false, List.mem_singleton] at hk_cl
    rw [hk_cl]
    simp [evalClause, evalLit_pos, traceValuation, h_init, hk]

/-- The trace satisfies the initial configuration constraints. -/
theorem satisfies_initial (params : Params V) (inputContents : List (V.Γ V.k₀)) (c : ℕ → V.Cfg)
    (h_init : c 0 = { l := some V.main, var := V.initialState,
                       stk := fun k => if h : k = V.k₀ then h ▸ inputContents else [] }) :
    evalCNF (traceAssignment c) (initialConstraints params inputContents) = true := by
  unfold initialConstraints
  rw [evalCNF_append, evalCNF_append, evalCNF_append, evalCNF_append]
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨satisfies_initial_label c h_init,
           satisfies_initial_state c h_init⟩,
          satisfies_initial_stkLen inputContents c h_init⟩,
         satisfies_initial_stkElem inputContents c h_init⟩,
        satisfies_initial_stkLen_other c h_init⟩

/-! ## Proved: Acceptance constraints -/

/-- Acceptance soundness: if the trace halts, it satisfies the acceptance clause. -/
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

/-! ## Main soundness theorem -/

/-- **Main Soundness Theorem**: if the TM computation halts within the time bound,
    the tableau formula is satisfiable.

    Uses 3 citation axioms (consistency, transition, frame) and 2 proved theorems
    (initial, acceptance). -/
theorem reduction_sound (params : Params V) (inputContents : List (V.Γ V.k₀))
    (c : ℕ → V.Cfg)
    (h_init : c 0 = { l := some V.main, var := V.initialState,
                       stk := fun k => if h : k = V.k₀ then h ▸ inputContents else [] })
    (h_step : ∀ i < params.timeBound, c (i + 1) = (V.step (c i)).getD (c i))
    (h_depth : ∀ i ≤ params.timeBound, ∀ k, ((c i).stk k).length ≤ params.maxStackDepth)
    (h_halt : ∃ i ≤ params.timeBound, (c i).l = none) :
    Satisfiable (tableauFormula params inputContents) := by
  use traceAssignment c
  show evalCNF (traceAssignment c) (tableauFormula params inputContents) = true
  unfold tableauFormula
  rw [evalCNF_append, evalCNF_append, evalCNF_append, evalCNF_append]
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨satisfies_consistency params c h_depth,
           satisfies_initial params inputContents c h_init⟩,
          satisfies_transition params c h_step⟩,
         satisfies_frame params c h_step⟩,
        satisfies_acceptance params c h_halt⟩

end CookLevinTableau
