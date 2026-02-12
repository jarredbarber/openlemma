/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Completeness of the Cook-Levin reduction: if the formula is satisfiable, the TM accepts.
-/
import botlib.Complexity.CookLevin.Tableau
import botlib.Complexity.CookLevin.Correctness
import botlib.Complexity.SAT
import Mathlib.Tactic.Linarith

namespace CookLevinTableau

open OpenLemma.Complexity.SAT Turing List

/-! ## Infrastructure for extracting consequences from a satisfying assignment -/

/-- Whether a tableau variable is set to true in the given assignment. -/
noncomputable def varTrue {V : Turing.FinTM2} [Encodable V.Λ] [Encodable V.σ]
    [Encodable V.K] [∀ k, Encodable (V.Γ k)]
    (σ : Assignment) (v : TableauVar V) : Prop :=
  σ (Encodable.encode v) = true

/-- Evaluating `tLit v true` under `σ` gives `σ (encode v)`. -/
theorem evalLiteral_tLit_true {V : Turing.FinTM2} [Encodable V.Λ] [Encodable V.σ]
    [Encodable V.K] [∀ k, Encodable (V.Γ k)]
    (σ : Assignment) (v : TableauVar V) :
    evalLiteral σ (tLit V v true) = σ (Encodable.encode v) := by
  simp [tLit, evalLiteral]

/-- If `σ` satisfies `φ₁ ++ φ₂`, then `σ` satisfies `φ₁`. -/
theorem evalCNF_append_left {σ : Assignment} {φ₁ φ₂ : CNF}
    (h : evalCNF σ (φ₁ ++ φ₂) = true) : evalCNF σ φ₁ = true := by
  simp only [evalCNF, List.all_append, Bool.and_eq_true] at h ⊢; exact h.1

/-- If `σ` satisfies `φ₁ ++ φ₂`, then `σ` satisfies `φ₂`. -/
theorem evalCNF_append_right {σ : Assignment} {φ₁ φ₂ : CNF}
    (h : evalCNF σ (φ₁ ++ φ₂) = true) : evalCNF σ φ₂ = true := by
  simp only [evalCNF, List.all_append, Bool.and_eq_true] at h ⊢; exact h.2

/-- If clause `c ∈ φ` and `evalCNF σ φ = true`, then `evalClause σ c = true`. -/
theorem evalClause_of_mem {σ : Assignment} {c : Clause} {φ : CNF}
    (h_mem : c ∈ φ) (h_sat : evalCNF σ φ = true) : evalClause σ c = true := by
  simp [evalCNF, all_eq_true] at h_sat; exact h_sat c h_mem

/-- If `σ` satisfies `l.flatMap f` and `x ∈ l`, then `σ` satisfies `f x`. -/
theorem evalCNF_flatMap_mem {σ : Assignment} {α : Type*} {l : List α} {f : α → CNF}
    (h : evalCNF σ (l.flatMap f) = true) {x : α} (hx : x ∈ l) :
    evalCNF σ (f x) = true := by
  simp only [evalCNF, all_eq_true] at h ⊢
  intro c hc; exact h c (mem_flatMap.mpr ⟨x, hx, hc⟩)

/-- Implication clause forcing: if `evalClause σ (negs ++ [pos]) = true` and all
    negated literals evaluate to false, then `pos` evaluates to true. -/
theorem implication_forcing {σ : Assignment} {negs : List Literal} {pos : Literal}
    (h_sat : evalClause σ (negs ++ [pos]) = true)
    (h_negs : ∀ l ∈ negs, evalLiteral σ l = false) :
    evalLiteral σ pos = true := by
  simp [evalClause, any_append, any_cons, any_nil] at h_sat
  rcases h_sat with ⟨l, hl_mem, hl_val⟩ | h
  · exact absurd hl_val (by rw [h_negs l hl_mem]; simp)
  · exact h

/-- If `varTrue σ v`, then `tLit v false` evaluates to false. -/
theorem eval_tLit_false_of_varTrue {V : Turing.FinTM2} [Encodable V.Λ] [Encodable V.σ]
    [Encodable V.K] [∀ k, Encodable (V.Γ k)]
    {σ : Assignment} {v : TableauVar V}
    (hv : varTrue σ v) : evalLiteral σ (tLit V v false) = false := by
  simp [tLit, evalLiteral, varTrue] at hv ⊢; exact hv

/-- Extracting `varTrue` from a positive literal evaluation. -/
theorem varTrue_of_eval_tLit {V : Turing.FinTM2} [Encodable V.Λ] [Encodable V.σ]
    [Encodable V.K] [∀ k, Encodable (V.Γ k)]
    {σ : Assignment} {v : TableauVar V}
    (h : evalLiteral σ (tLit V v true) = true) : varTrue σ v := by
  simp [tLit, evalLiteral] at h; exact h

/-- Decompose `tableauFormula` satisfaction into components. -/
private theorem sat_components {V : Turing.FinTM2} [Encodable V.Λ] [Encodable V.σ]
    [Encodable V.K] [∀ k, Encodable (V.Γ k)]
    [Fintype V.Λ] [Fintype V.σ] [Fintype V.K] [∀ k, Fintype (V.Γ k)]
    [DecidableEq V.K] [∀ k, DecidableEq (V.Γ k)]
    (params : Params V) (input : List (V.Γ V.k₀))
    (σ : Assignment) (hsat : evalCNF σ (tableauFormula params input) = true) :
    evalCNF σ (consistencyConstraints params) = true ∧
    evalCNF σ (initialConstraints params input) = true ∧
    evalCNF σ (transitionConstraints params) = true ∧
    evalCNF σ (framePreservation params) = true ∧
    evalCNF σ (acceptanceConstraints params) = true := by
  unfold tableauFormula at hsat
  exact ⟨evalCNF_append_left (evalCNF_append_left (evalCNF_append_left (evalCNF_append_left hsat))),
         evalCNF_append_right (evalCNF_append_left (evalCNF_append_left (evalCNF_append_left hsat))),
         evalCNF_append_right (evalCNF_append_left (evalCNF_append_left hsat)),
         evalCNF_append_right (evalCNF_append_left hsat),
         evalCNF_append_right hsat⟩

/-! ## Completeness: acceptance constraint forces halting -/

theorem completeness_halting {V : Turing.FinTM2} [Encodable V.Λ] [Encodable V.σ]
    [Encodable V.K] [∀ k, Encodable (V.Γ k)]
    [Fintype V.Λ] [Fintype V.σ] [Fintype V.K] [∀ k, Fintype (V.Γ k)]
    [DecidableEq V.K] [∀ k, DecidableEq (V.Γ k)]
    (params : Params V) (input : List (V.Γ V.k₀))
    (σ : Assignment) (hsat : evalCNF σ (tableauFormula params input) = true) :
    ∃ t, t ≤ params.timeBound ∧ varTrue σ (TableauVar.label (V := V) t none) := by
  have ⟨_, _, _, _, hA⟩ := sat_components params input σ hsat
  unfold acceptanceConstraints at hA
  simp only [evalCNF, all_cons, all_nil, Bool.and_true] at hA
  rw [evalClause, any_map, any_eq_true] at hA
  obtain ⟨t, ht_mem, ht_val⟩ := hA
  rw [mem_range] at ht_mem
  exact ⟨t, by omega, by simp [varTrue]; exact ht_val⟩

/-! ## Completeness: initial constraints -/

theorem completeness_initial_label {V : Turing.FinTM2} [Encodable V.Λ] [Encodable V.σ]
    [Encodable V.K] [∀ k, Encodable (V.Γ k)]
    [Fintype V.Λ] [Fintype V.σ] [Fintype V.K] [∀ k, Fintype (V.Γ k)]
    [DecidableEq V.K] [∀ k, DecidableEq (V.Γ k)]
    (params : Params V) (input : List (V.Γ V.k₀))
    (σ : Assignment) (hsat : evalCNF σ (tableauFormula params input) = true) :
    varTrue σ (TableauVar.label (V := V) 0 (some V.main)) := by
  have ⟨_, hI, _, _, _⟩ := sat_components params input σ hsat
  unfold initialConstraints at hI
  simp [evalCNF, evalClause, evalLiteral_tLit_true, varTrue] at hI
  exact hI.1

theorem completeness_initial_state {V : Turing.FinTM2} [Encodable V.Λ] [Encodable V.σ]
    [Encodable V.K] [∀ k, Encodable (V.Γ k)]
    [Fintype V.Λ] [Fintype V.σ] [Fintype V.K] [∀ k, Fintype (V.Γ k)]
    [DecidableEq V.K] [∀ k, DecidableEq (V.Γ k)]
    (params : Params V) (input : List (V.Γ V.k₀))
    (σ : Assignment) (hsat : evalCNF σ (tableauFormula params input) = true) :
    varTrue σ (TableauVar.state (V := V) 0 V.initialState) := by
  have ⟨_, hI, _, _, _⟩ := sat_components params input σ hsat
  unfold initialConstraints at hI
  simp [evalCNF, evalClause, evalLiteral_tLit_true, varTrue] at hI
  exact hI.2.1

/-! ## Main completeness theorem -/

/-- **Completeness of Cook-Levin**:
    If the generated CNF formula is satisfiable, then there exists a
    TM computation that accepts the input. -/
theorem completeness (V : FinTM2) [Encodable V.Λ] [Encodable V.σ] [Encodable V.K] [∀ k, Encodable (V.Γ k)]
    [Fintype V.Λ] [Fintype V.σ] [Fintype V.K] [∀ k, Fintype (V.Γ k)] [DecidableEq V.K] [∀ k, DecidableEq (V.Γ k)]
    (params : Params V) (input : List (V.Γ V.k₀))
    (h_sat : Satisfiable (tableauFormula params input)) :
    ∃ i ≤ params.timeBound, ((Turing.FinTM2.step V)^[i] (Turing.FinTM2.initList V input)).l = none := by
  -- Main proof outline:
  -- 1. From h_sat, get σ with evalCNF σ (tableauFormula ...) = true
  -- 2. From acceptance constraints: ∃ t ≤ T, varTrue σ (label t none)
  -- 3. From initial constraints: at t=0, label = some main, state = initialState
  -- 4. From transition constraints: the extracted trace follows TM2.step
  -- 5. Conclude: the actual TM2 computation reaches none by time t
  sorry

end CookLevinTableau
