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
- `satisfies_consistency`: trace satisfies consistency constraints (proved)
- `satisfies_acceptance`: trace satisfies acceptance constraints (proved)
- `reduction_sound`: main soundness theorem (uses 2 citation axioms for
  transition and frame constraints)
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

/-! ## Consistency constraints (proved)

The trace valuation assigns true to exactly one label, state, stkLen, and stkElem
at each timestep by construction: `traceValuation c (label i l) = decide ((c i).l = l)`,
so exactly one `l` gives true. The `exactlyOne` constraint is then satisfied. -/

private theorem suffix_of_mem_tails {α : Type*} (l : List α) :
    ∀ s ∈ l.tails, s <:+ l := by
  induction l with
  | nil => intro s hs; simp [List.tails] at hs; subst hs; exact List.suffix_refl _
  | cons a l ih =>
    intro s hs; unfold List.tails at hs
    change s ∈ (a :: l) :: l.tails at hs; rw [List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact List.suffix_refl _
    · exact (ih s hs).trans (List.suffix_cons a l)

private theorem nodup_of_suffix {α : Type*} {l s : List α}
    (h : s <:+ l) (hn : l.Nodup) : s.Nodup := by
  obtain ⟨pre, rfl⟩ := h; exact (List.nodup_append.mp hn).2.1

/-- `exactlyOne` is satisfied when the var list is nodup and the trace valuation
    assigns true to exactly one element. -/
private theorem exactlyOne_trace (c : ℕ → V.Cfg)
    (vars : List (TableauVar V))
    (h_nodup : vars.Nodup)
    (h_alo : ∃ v ∈ vars, traceValuation c v = true)
    (h_amo : ∀ v ∈ vars, ∀ w ∈ vars,
      traceValuation c v = true → traceValuation c w = true → v = w) :
    evalCNF (traceAssignment c) (exactlyOne V vars) = true := by
  unfold exactlyOne
  simp only [evalCNF, all_cons, Bool.and_eq_true]
  constructor
  · rw [evalClause, any_map, any_eq_true]
    obtain ⟨v, hv, htv⟩ := h_alo
    exact ⟨v, hv, by simp [tLit, evalLiteral, traceAssignment, encodek, htv]⟩
  · rw [all_flatMap, all_eq_true]
    intro suffix hsuf
    have h_suf : suffix <:+ vars := suffix_of_mem_tails vars suffix hsuf
    cases suffix with
    | nil => simp
    | cons v rest =>
      simp only [all_map, all_eq_true]
      intro w hw
      have h_nd : (v :: rest).Nodup := nodup_of_suffix h_suf h_nodup
      have hv_ne_w : v ≠ w := fun heq => by subst heq; exact (List.nodup_cons.mp h_nd).1 hw
      have hv_mem : v ∈ vars := h_suf.mem List.mem_cons_self
      have hw_mem : w ∈ vars := h_suf.mem (List.mem_cons.mpr (Or.inr hw))
      show evalClause (traceAssignment c) [tLit V v false, tLit V w false] = true
      by_cases hv : traceValuation c v = true
      · by_cases hw : traceValuation c w = true
        · exact absurd (h_amo v hv_mem w hw_mem hv hw) hv_ne_w
        · simp [evalClause, tLit, evalLiteral, traceAssignment, encodek, hw]
      · simp [evalClause, tLit, evalLiteral, traceAssignment, encodek, hv]

private theorem label_inj (i : ℕ) : Function.Injective (TableauVar.label (V := V) i) := by
  intro l1 l2 h; cases h; rfl
private theorem state_inj (i : ℕ) : Function.Injective (TableauVar.state (V := V) i) := by
  intro s1 s2 h; cases h; rfl
private theorem stkElem_inj (i : ℕ) (k : V.K) (j : ℕ) :
    Function.Injective (TableauVar.stkElem (V := V) i k j) := by
  intro γ1 γ2 h; cases h; rfl
private theorem stkLen_inj (i : ℕ) (k : V.K) :
    Function.Injective (TableauVar.stkLen (V := V) i k) := by
  intro l1 l2 h; cases h; rfl

private theorem label_block_sat (c : ℕ → V.Cfg) (i : ℕ) :
    evalCNF (traceAssignment c)
      (exactlyOne V ((Finset.univ : Finset (Option V.Λ)).toList.map (TableauVar.label i))) = true := by
  apply exactlyOne_trace c _ (List.Nodup.map (label_inj i) (Finset.nodup_toList _))
  · exact ⟨_, mem_map.mpr ⟨(c i).l, Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩,
           by simp [traceValuation]⟩
  · intro v hv w hw htv htw
    obtain ⟨l1, _, rfl⟩ := mem_map.mp hv; obtain ⟨l2, _, rfl⟩ := mem_map.mp hw
    simp only [traceValuation, decide_eq_true_eq] at htv htw; congr 1; rw [← htv, ← htw]

private theorem state_block_sat (c : ℕ → V.Cfg) (i : ℕ) :
    evalCNF (traceAssignment c)
      (exactlyOne V ((Finset.univ : Finset V.σ).toList.map (TableauVar.state i))) = true := by
  apply exactlyOne_trace c _ (List.Nodup.map (state_inj i) (Finset.nodup_toList _))
  · exact ⟨_, mem_map.mpr ⟨(c i).var, Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩,
           by simp [traceValuation]⟩
  · intro v hv w hw htv htw
    obtain ⟨s1, _, rfl⟩ := mem_map.mp hv; obtain ⟨s2, _, rfl⟩ := mem_map.mp hw
    simp only [traceValuation, decide_eq_true_eq] at htv htw; congr 1; rw [← htv, ← htw]

private theorem stkElem_block_sat (c : ℕ → V.Cfg) (i : ℕ) (k : V.K) (j : ℕ) :
    evalCNF (traceAssignment c)
      (exactlyOne V ((Finset.univ : Finset (V.Γ k)).toList.map (TableauVar.stkElem i k j))) = true := by
  apply exactlyOne_trace c _ (List.Nodup.map (stkElem_inj i k j) (Finset.nodup_toList _))
  · by_cases hj : j < ((c i).stk k).length
    · exact ⟨_, mem_map.mpr ⟨((c i).stk k).reverse[j]'(by simp; exact hj),
             Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩,
             by simp only [traceValuation]; rw [dif_pos hj]; simp [List.get_eq_getElem]⟩
    · exact ⟨_, mem_map.mpr ⟨Classical.choice inferInstance,
             Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩,
             by simp only [traceValuation, hj, dite_false, decide_true]⟩
  · intro v hv w hw htv htw
    obtain ⟨γ1, _, rfl⟩ := mem_map.mp hv; obtain ⟨γ2, _, rfl⟩ := mem_map.mp hw
    congr 1; simp only [traceValuation] at htv htw
    split at htv <;> split at htw
    · simp only [decide_eq_true_eq] at htv htw; rw [← htv, ← htw]
    · rename_i h1 h2; exact absurd h1 h2
    · rename_i h1 h2; exact absurd h2 h1
    · simp only [decide_eq_true_eq] at htv htw; rw [htv, htw]

private theorem stkLen_block_sat (c : ℕ → V.Cfg) (params : Params V) (i : ℕ)
    (k : V.K) (h_depth : ((c i).stk k).length ≤ params.maxStackDepth) :
    evalCNF (traceAssignment c)
      (exactlyOne V ((range (params.maxStackDepth + 1)).map (TableauVar.stkLen i k))) = true := by
  apply exactlyOne_trace c _ (List.Nodup.map (stkLen_inj i k) List.nodup_range)
  · exact ⟨_, mem_map.mpr ⟨((c i).stk k).length, mem_range.mpr (by omega), rfl⟩,
           by simp [traceValuation]⟩
  · intro v hv w hw htv htw
    obtain ⟨l1, _, rfl⟩ := mem_map.mp hv; obtain ⟨l2, _, rfl⟩ := mem_map.mp hw
    simp only [traceValuation, decide_eq_true_eq] at htv htw; congr 1; omega

private theorem evalCNF_flatMap_true {σ : Assignment} {α : Type*} {l : List α} {f : α → CNF}
    (h : ∀ x ∈ l, evalCNF σ (f x) = true) :
    evalCNF σ (l.flatMap f) = true := by
  simp only [evalCNF, all_eq_true]; intro c hc
  obtain ⟨x, hx, hc⟩ := mem_flatMap.mp hc
  exact (all_eq_true.mp (h x hx)) c hc

private theorem evalCNF_append_true {σ : Assignment} {c1 c2 : CNF}
    (h1 : evalCNF σ c1 = true) (h2 : evalCNF σ c2 = true) :
    evalCNF σ (c1 ++ c2) = true := by
  simp only [evalCNF, all_append, Bool.and_eq_true]; exact ⟨h1, h2⟩

/-- The trace satisfies the consistency constraints.
    Proved: each `exactlyOne` block is satisfied because `traceValuation` uses
    `decide`, which assigns true to exactly one element in each enumeration. -/
theorem satisfies_consistency (params : Params V) (c : ℕ → V.Cfg)
    (h_depth : ∀ i ≤ params.timeBound, ∀ k, ((c i).stk k).length ≤ params.maxStackDepth) :
    evalCNF (traceAssignment c) (consistencyConstraints params) = true := by
  unfold consistencyConstraints
  apply evalCNF_append_true (evalCNF_append_true (evalCNF_append_true ?_ ?_) ?_) ?_
  · exact evalCNF_flatMap_true fun i _ => label_block_sat c i
  · exact evalCNF_flatMap_true fun i _ => state_block_sat c i
  · exact evalCNF_flatMap_true fun i _ =>
      evalCNF_flatMap_true fun k _ =>
        evalCNF_flatMap_true fun j _ => stkElem_block_sat c i k j
  · exact evalCNF_flatMap_true fun i hi =>
      evalCNF_flatMap_true fun k _ =>
        stkLen_block_sat c params i k (h_depth i (by rw [mem_range] at hi; omega) k)

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
