/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Soundness of the Cook-Levin tableau reduction.
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
  unfold tLit; cases b <;> simp [evalLiteral, traceAssignment, encodek v]

/-! ## Citation Axioms: Trace matching -/

/-- Citation axiom: the trace satisfies the consistency constraints. -/
axiom satisfies_consistency (params : Params V) (c : ℕ → V.Cfg)
    (h_depth : ∀ i ≤ params.timeBound, ∀ k, ((c i).stk k).length ≤ params.maxStackDepth) :
    evalCNF (traceAssignment c) (consistencyConstraints params) = true

/-- Citation axiom: the trace satisfies the initial configuration constraints. -/
axiom satisfies_initial (params : Params V) (inputContents : List (V.Γ V.k₀)) (c : ℕ → V.Cfg)
    (h_init : c 0 = { l := some V.main, var := V.initialState, stk := fun k => if h : k = V.k₀ then h ▸ inputContents else [] }) :
    evalCNF (traceAssignment c) (initialConstraints params inputContents) = true

/-- Citation axiom: the trace satisfies the transition constraints. -/
axiom satisfies_transition (params : Params V) (c : ℕ → V.Cfg)
    (h_step : ∀ i < params.timeBound, c (i + 1) = (V.step (c i)).getD (c i)) :
    evalCNF (traceAssignment c) (transitionConstraints params) = true

/-- Citation axiom: the trace satisfies the frame preservation constraints. -/
axiom satisfies_frame (params : Params V) (c : ℕ → V.Cfg)
    (h_step : ∀ i < params.timeBound, c (i + 1) = (V.step (c i)).getD (c i)) :
    evalCNF (traceAssignment c) (framePreservation params) = true

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

/-! ## Helper lemma -/

/-- `evalCNF` distributes over list append. -/
theorem evalCNF_append (σ : Assignment) (c1 c2 : CNF) :
    evalCNF σ (c1 ++ c2) = (evalCNF σ c1 && evalCNF σ c2) := by
  simp [evalCNF, all_append]

/-- Main Soundness Theorem: Acceptance implies satisfiability. -/
theorem reduction_sound (params : Params V) (inputContents : List (V.Γ V.k₀))
    (c : ℕ → V.Cfg)
    (h_init : c 0 = { l := some V.main, var := V.initialState, stk := fun k => if h : k = V.k₀ then h ▸ inputContents else [] })
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
