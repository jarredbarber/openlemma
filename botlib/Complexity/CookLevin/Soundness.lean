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

/-! ## Satisfaction of each constraint group -/

theorem satisfies_consistency (params : Params V) (c : ℕ → V.Cfg)
    (h_depth : ∀ i ≤ params.timeBound, ∀ k, ((c i).stk k).length ≤ params.maxStackDepth) :
    evalCNF (traceAssignment c) (consistencyConstraints params) = true := by
  sorry

theorem satisfies_initial (params : Params V) (inputContents : List (V.Γ V.k₀)) (c : ℕ → V.Cfg)
    (h_init : c 0 = { l := some V.main, var := V.initialState, stk := fun k => if h : k = V.k₀ then h ▸ inputContents else [] }) :
    evalCNF (traceAssignment c) (initialConstraints params inputContents) = true := by
  sorry

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
  sorry

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
