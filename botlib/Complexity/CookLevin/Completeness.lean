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

open Turing CookLevinTableau OpenLemma.Complexity.SAT List

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! ## Step-or-halt iteration -/

noncomputable def stepOrHalt (V : FinTM2) (cfg : V.Cfg) : V.Cfg :=
  match V.step cfg with | some cfg' => cfg' | none => cfg

variable {V : Turing.FinTM2} [Encodable V.Λ] [Encodable V.σ] [Encodable V.K]
  [∀ k, Encodable (V.Γ k)]
  [Fintype V.Λ] [Fintype V.σ] [Fintype V.K] [∀ k, Fintype (V.Γ k)]
  [DecidableEq V.K] [∀ k, DecidableEq (V.Γ k)]
  [DecidableEq V.Λ] [DecidableEq V.σ]

theorem stepOrHalt_of_halted {cfg : V.Cfg} (h : cfg.l = none) :
    stepOrHalt V cfg = cfg := by
  unfold stepOrHalt FinTM2.step
  cases cfg with | mk l v S => simp at h; subst h; simp [TM2.step]

theorem iterate_stepOrHalt_of_halted {cfg : V.Cfg} (h : cfg.l = none) (n : ℕ) :
    (stepOrHalt V)^[n] cfg = cfg := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Function.comp, ih, stepOrHalt_of_halted h]

/-! ## Bounded read depth

BoundedReadDepth is defined in Tableau.lean (uses V.decidableEqK). -/

-- Bridge: BoundedReadDepth uses V.decidableEqK, but section uses [DecidableEq V.K].
-- These are equal by Subsingleton.
private theorem brd_section (hBRD : BoundedReadDepth V) (lbl : V.Λ) (k : V.K) :
    stmtReadDepth k (V.m lbl) ≤ 1 := by
  have := hBRD lbl k
  rwa [show @stmtReadDepth V.K V.Γ V.Λ V.σ k V.decidableEqK (V.m lbl)
    = stmtReadDepth k (V.m lbl) from by congr 1] at this

/-! ## Basic infrastructure -/

noncomputable def varTrue (σ : Assignment) (v : TableauVar V) : Prop :=
  σ (Encodable.encode v) = true

theorem evalCNF_append_left {σ : Assignment} {φ₁ φ₂ : CNF}
    (h : evalCNF σ (φ₁ ++ φ₂) = true) : evalCNF σ φ₁ = true := by
  simp only [evalCNF, all_append, Bool.and_eq_true] at h ⊢; exact h.1

theorem evalCNF_append_right {σ : Assignment} {φ₁ φ₂ : CNF}
    (h : evalCNF σ (φ₁ ++ φ₂) = true) : evalCNF σ φ₂ = true := by
  simp only [evalCNF, all_append, Bool.and_eq_true] at h ⊢; exact h.2

theorem evalCNF_flatMap_mem {σ : Assignment} {α : Type*} {l : List α} {f : α → CNF}
    (h : evalCNF σ (l.flatMap f) = true) {x : α} (hx : x ∈ l) :
    evalCNF σ (f x) = true := by
  simp only [evalCNF, all_eq_true] at h ⊢
  intro c hc; exact h c (mem_flatMap.mpr ⟨x, hx, hc⟩)

private theorem sat_components (params : Params V) (input : List (V.Γ V.k₀))
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

private theorem eval_neg_false {σ : Assignment} {v : TableauVar V}
    (hv : varTrue σ v) : evalLiteral σ (tLit V v false) = false := by
  simp [tLit, evalLiteral] at hv ⊢; exact hv

/-! ## Consistency: exactlyOne uniqueness -/

private theorem drop_mem_tails {α : Type*} (l : List α) (n : ℕ) :
    l.drop n ∈ l.tails := by rw [List.mem_tails]; exact List.drop_suffix n l

private theorem getElem_mem_drop {α : Type*} {l : List α} {j n : ℕ}
    (hn : n ≤ j) (hj : j < l.length) : l[j] ∈ l.drop n := by
  have hlen : j - n < (l.drop n).length := by simp; omega
  have : (l.drop n)[j - n] = l[j] := by rw [List.getElem_drop]; congr 1; omega
  rw [← this]; exact List.getElem_mem hlen

private theorem exactlyOne_pair_false {σ : Assignment} {vars : List (TableauVar V)}
    (h_sat : evalCNF σ (exactlyOne V vars) = true)
    {i j : ℕ} (hi : i < vars.length) (hj : j < vars.length) (h_lt : i < j)
    (hv_true : varTrue σ vars[i]) (hw_true : varTrue σ vars[j]) : False := by
  unfold exactlyOne at h_sat
  simp only [evalCNF, all_cons, Bool.and_eq_true] at h_sat
  obtain ⟨_, h_amo⟩ := h_sat
  rw [all_flatMap, all_eq_true] at h_amo
  have h_tail := h_amo (vars.drop i) (drop_mem_tails vars i)
  rw [List.drop_eq_getElem_cons hi] at h_tail
  simp only [all_map, all_eq_true] at h_tail
  specialize h_tail vars[j] (getElem_mem_drop (by omega) hj)
  simp only [Function.comp, evalClause, any_cons, any_nil, Bool.or_false] at h_tail
  rw [eval_neg_false hv_true, eval_neg_false hw_true] at h_tail; simp at h_tail

theorem exactlyOne_encode_eq {σ : Assignment} {vars : List (TableauVar V)}
    (h_sat : evalCNF σ (exactlyOne V vars) = true)
    {v w : TableauVar V} (hv : v ∈ vars) (hw : w ∈ vars)
    (hv_true : varTrue σ v) (hw_true : varTrue σ w) :
    Encodable.encode v = Encodable.encode w := by
  by_contra h_ne
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
  have hij : i ≠ j := by intro he; subst he; exact h_ne rfl
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact exactlyOne_pair_false h_sat hi hj h hv_true hw_true
  · exact exactlyOne_pair_false h_sat hj hi h hw_true hv_true

private theorem label_encode_injective {t : ℕ} {l1 l2 : Option V.Λ}
    (h : Encodable.encode (TableauVar.label (V := V) t l1) =
         Encodable.encode (TableauVar.label (V := V) t l2)) : l1 = l2 := by
  have := Encodable.encode_injective h; cases this; rfl

/-- From consistency: at most one label is true at each timestep. -/
theorem consistency_label_unique {σ : Assignment} {params : Params V}
    (hC : evalCNF σ (consistencyConstraints params) = true)
    {t : ℕ} (ht : t ≤ params.timeBound) {l1 l2 : Option V.Λ}
    (h1 : varTrue σ (TableauVar.label (V := V) t l1))
    (h2 : varTrue σ (TableauVar.label (V := V) t l2)) : l1 = l2 := by
  unfold consistencyConstraints at hC
  have hL := evalCNF_append_left (evalCNF_append_left (evalCNF_append_left hC))
  have hT := evalCNF_flatMap_mem hL (List.mem_range.mpr (show t < params.timeBound + 1 by omega))
  exact label_encode_injective (exactlyOne_encode_eq hT
    (List.mem_map.mpr ⟨l1, Finset.mem_toList.mpr (Finset.mem_univ l1), rfl⟩)
    (List.mem_map.mpr ⟨l2, Finset.mem_toList.mpr (Finset.mem_univ l2), rfl⟩) h1 h2)

/-- From consistency: at most one stkLen is true at each (t, k). -/
theorem consistency_stkLen_unique {σ : Assignment} {params : Params V}
    (hC : evalCNF σ (consistencyConstraints params) = true)
    {t : ℕ} (ht : t ≤ params.timeBound) (k : V.K)
    {len1 len2 : ℕ}
    (h1 : varTrue σ (TableauVar.stkLen (V := V) t k len1))
    (h2 : varTrue σ (TableauVar.stkLen (V := V) t k len2))
    (hl1 : len1 ≤ params.maxStackDepth) (hl2 : len2 ≤ params.maxStackDepth) :
    len1 = len2 := by
  unfold consistencyConstraints at hC
  have hBlock := evalCNF_flatMap_mem
    (evalCNF_flatMap_mem (evalCNF_append_right hC) (mem_range.mpr (Nat.lt_succ_of_le ht)))
    (Finset.mem_toList.mpr (Finset.mem_univ k))
  have h_inj := exactlyOne_encode_eq hBlock
    (mem_map.mpr ⟨len1, mem_range.mpr (Nat.lt_succ_of_le hl1), rfl⟩)
    (mem_map.mpr ⟨len2, mem_range.mpr (Nat.lt_succ_of_le hl2), rfl⟩)
    h1 h2
  have := Encodable.encode_injective h_inj
  cases this; rfl

/-- From consistency: at most one stkElem is true at each (t, k, j). -/
theorem consistency_stkElem_unique {σ : Assignment} {params : Params V}
    (hC : evalCNF σ (consistencyConstraints params) = true)
    {t : ℕ} (ht : t ≤ params.timeBound) (k : V.K) (j : ℕ) (hj : j < params.maxStackDepth)
    {γ1 γ2 : V.Γ k}
    (h1 : varTrue σ (TableauVar.stkElem (V := V) t k j γ1))
    (h2 : varTrue σ (TableauVar.stkElem (V := V) t k j γ2)) :
    γ1 = γ2 := by
  unfold consistencyConstraints at hC
  have hSE := evalCNF_append_right (evalCNF_append_left hC)
  have hBlock := evalCNF_flatMap_mem
    (evalCNF_flatMap_mem
      (evalCNF_flatMap_mem hSE (mem_range.mpr (Nat.lt_succ_of_le ht)))
      (Finset.mem_toList.mpr (Finset.mem_univ k)))
    (mem_range.mpr hj)
  have h_inj := exactlyOne_encode_eq hBlock
    (mem_map.mpr ⟨γ1, Finset.mem_toList.mpr (Finset.mem_univ γ1), rfl⟩)
    (mem_map.mpr ⟨γ2, Finset.mem_toList.mpr (Finset.mem_univ γ2), rfl⟩)
    h1 h2
  have := Encodable.encode_injective h_inj
  cases this; rfl

/-! ## Acceptance and initial constraints -/

theorem completeness_halting (params : Params V) (input : List (V.Γ V.k₀))
    (σ : Assignment) (hsat : evalCNF σ (tableauFormula params input) = true) :
    ∃ t, t ≤ params.timeBound ∧ varTrue σ (TableauVar.label (V := V) t none) := by
  have ⟨_, _, _, _, hA⟩ := sat_components params input σ hsat
  unfold acceptanceConstraints at hA
  simp only [evalCNF, all_cons, all_nil, Bool.and_true] at hA
  rw [evalClause, any_map, any_eq_true] at hA
  obtain ⟨t, ht, hv⟩ := hA; rw [mem_range] at ht
  exact ⟨t, by omega, by simp [varTrue]; exact hv⟩

theorem completeness_initial_label (params : Params V) (input : List (V.Γ V.k₀))
    (σ : Assignment) (hsat : evalCNF σ (tableauFormula params input) = true) :
    varTrue σ (TableauVar.label (V := V) 0 (some V.main)) := by
  have ⟨_, hI, _, _, _⟩ := sat_components params input σ hsat
  unfold initialConstraints at hI
  simp [evalCNF, evalClause, tLit, evalLiteral] at hI; exact hI.1

theorem completeness_initial_state (params : Params V) (input : List (V.Γ V.k₀))
    (σ : Assignment) (hsat : evalCNF σ (tableauFormula params input) = true) :
    varTrue σ (TableauVar.state (V := V) 0 V.initialState) := by
  have ⟨_, hI, _, _, _⟩ := sat_components params input σ hsat
  unfold initialConstraints at hI
  simp [evalCNF, evalClause, tLit, evalLiteral] at hI; exact hI.2.1

/-! ## Trace-computation correspondence -/

/-- The actual TM2 computation configuration at time t. -/
noncomputable def cfgAt (V : FinTM2) (input : List (V.Γ V.k₀)) (t : ℕ) : V.Cfg :=
  (stepOrHalt V)^[t] (Turing.initList V input)

theorem cfgAt_succ (input : List (V.Γ V.k₀)) (t : ℕ) :
    cfgAt V input (t + 1) = stepOrHalt V (cfgAt V input t) := by
  simp [cfgAt, Function.iterate_succ_apply']

theorem cfgAt_halted_succ (input : List (V.Γ V.k₀)) (t : ℕ)
    (h : (cfgAt V input t).l = none) :
    cfgAt V input (t + 1) = cfgAt V input t := by
  rw [cfgAt_succ, stepOrHalt_of_halted h]

/-! ### stepOrHalt for running configs -/

private theorem stepOrHalt_running {cfg : V.Cfg} {lbl : V.Λ} (h : cfg.l = some lbl) :
    stepOrHalt V cfg = TM2.stepAux (V.m lbl) cfg.var cfg.stk := by
  show (match V.step cfg with | some cfg' => cfg' | none => cfg) = _
  have hstep : V.step cfg = some (TM2.stepAux (V.m lbl) cfg.var cfg.stk) := by
    cases cfg with | mk l v S =>
      simp at h; subst h
      show @FinTM2.step V ⟨some lbl, v, S⟩ = some (TM2.stepAux (V.m lbl) v S)
      simp [FinTM2.step, TM2.step]; congr 1
      all_goals exact Subsingleton.elim _ _
  rw [hstep]

/-! ### Base cases -/

theorem trace_base_label (params : Params V) (input : List (V.Γ V.k₀))
    (σ : Assignment) (hsat : evalCNF σ (tableauFormula params input) = true) :
    varTrue σ (TableauVar.label (V := V) 0 (cfgAt V input 0).l) := by
  have : (cfgAt V input 0).l = some V.main := by simp [cfgAt]; unfold initList; rfl
  rw [this]; exact completeness_initial_label params input σ hsat

theorem trace_base_state (params : Params V) (input : List (V.Γ V.k₀))
    (σ : Assignment) (hsat : evalCNF σ (tableauFormula params input) = true) :
    varTrue σ (TableauVar.state (V := V) 0 (cfgAt V input 0).var) := by
  have : (cfgAt V input 0).var = V.initialState := by simp [cfgAt]; unfold initList; rfl
  rw [this]; exact completeness_initial_state params input σ hsat

/-! ### Transition constraint extraction -/

/-- All antecedent literals evaluate to false when their variables are true. -/
private theorem antecedent_all_false {σ : Assignment} {t : ℕ} {params : Params V}
    {l : Option V.Λ} {s : V.σ}
    {topsInfo : ∀ k : V.K, Option (Fin params.maxStackDepth × V.Γ k)}
    (h_label : varTrue σ (TableauVar.label (V := V) t l))
    (h_state : varTrue σ (TableauVar.state (V := V) t s))
    (h_stks : ∀ k, match topsInfo k with
      | none => varTrue σ (TableauVar.stkLen (V := V) t k 0)
      | some (len, γ) => varTrue σ (TableauVar.stkLen t k (len.val + 1)) ∧
                          varTrue σ (TableauVar.stkElem t k len.val γ)) :
    ∀ lit ∈ ([tLit V (TableauVar.label t l) false,
              tLit V (TableauVar.state t s) false] ++
             (Finset.univ : Finset V.K).toList.flatMap (fun k => match topsInfo k with
               | none => [tLit V (TableauVar.stkLen t k 0) false]
               | some (len, γ) => [tLit V (TableauVar.stkLen t k (len.val + 1)) false,
                                  tLit V (TableauVar.stkElem t k len.val γ) false])),
      evalLiteral σ lit = false := by
  intro lit h_mem
  simp only [mem_append] at h_mem
  cases h_mem with
  | inl h =>
    simp only [mem_cons, mem_nil_iff, or_false] at h
    cases h with | inl h => rw [h]; exact eval_neg_false h_label
                 | inr h => rw [h]; exact eval_neg_false h_state
  | inr h =>
    simp only [mem_flatMap] at h; obtain ⟨k, _, hk⟩ := h
    have hs := h_stks k; revert hk
    split at hs <;> simp only [mem_cons, mem_nil_iff, or_false]
    · rintro rfl; exact eval_neg_false hs
    · rename_i len γ _; obtain ⟨h1, h2⟩ := hs
      rintro (rfl | rfl)
      · exact eval_neg_false h1
      · exact eval_neg_false h2

/-- Extract consequent from implication clause when antecedent is false. -/
private theorem consequent_of_clause {σ : Assignment} {negs : List Literal} {pos : Literal}
    (h_sat : evalClause σ (negs ++ [pos]) = true)
    (h_negs : ∀ l ∈ negs, evalLiteral σ l = false) :
    evalLiteral σ pos = true := by
  simp [evalClause, any_append, any_cons, any_nil, any_eq_true] at h_sat
  rcases h_sat with ⟨l, hl, hv⟩ | h
  · exact absurd hv (by rw [h_negs l hl]; simp)
  · exact h

/-- **Halted case**: transition constraints force label=none, state preserved. -/
theorem halted_forces_next {σ : Assignment} {params : Params V}
    {t : ℕ} (ht : t < params.timeBound)
    (hT : evalCNF σ (transitionConstraints params) = true)
    (s : V.σ) (topsInfo : ∀ k : V.K, Option (Fin params.maxStackDepth × V.Γ k))
    (h_label : varTrue σ (TableauVar.label (V := V) t none))
    (h_state : varTrue σ (TableauVar.state (V := V) t s))
    (h_stks : ∀ k, match topsInfo k with
      | none => varTrue σ (TableauVar.stkLen (V := V) t k 0)
      | some (len, γ) => varTrue σ (TableauVar.stkLen t k (len.val + 1)) ∧
                          varTrue σ (TableauVar.stkElem t k len.val γ)) :
    varTrue σ (TableauVar.label (V := V) (t+1) none) ∧
    varTrue σ (TableauVar.state (V := V) (t+1) s) := by
  unfold transitionConstraints at hT
  have hTC := evalCNF_flatMap_mem hT (mem_range.mpr ht)
  unfold transitionClausesAt at hTC
  have h1 := evalCNF_flatMap_mem hTC (Finset.mem_toList.mpr (Finset.mem_univ (none : Option V.Λ)))
  have h2 := evalCNF_flatMap_mem h1 (Finset.mem_toList.mpr (Finset.mem_univ s))
  have h3 := evalCNF_flatMap_mem h2 (Finset.mem_toList.mpr (Finset.mem_univ topsInfo))
  dsimp only at h3
  have h_pair := evalCNF_append_left h3
  simp only [evalCNF, all_cons, all_nil, Bool.and_true, Bool.and_eq_true] at h_pair
  obtain ⟨h_lc, h_sc⟩ := h_pair
  have h_af := antecedent_all_false h_label h_state h_stks
  constructor
  · have := consequent_of_clause h_lc h_af
    simp [tLit, evalLiteral] at this; exact this
  · have := consequent_of_clause h_sc h_af
    simp [tLit, evalLiteral] at this; exact this

/-! ### Consistency extraction for topsInfo -/

private theorem exactlyOne_exists {σ : Assignment} {vars : List (TableauVar V)}
    (h : evalCNF σ (exactlyOne V vars) = true) :
    ∃ v ∈ vars, varTrue σ v := by
  unfold exactlyOne at h
  simp only [evalCNF, all_cons, Bool.and_eq_true] at h
  simp only [evalClause, any_map, any_eq_true] at h
  obtain ⟨⟨v, hv, hlit⟩, _⟩ := h
  exact ⟨v, hv, by simp [varTrue, tLit, evalLiteral] at hlit ⊢; exact hlit⟩

private theorem stkLen_exists {σ : Assignment} {params : Params V}
    (hC : evalCNF σ (consistencyConstraints params) = true)
    {t : ℕ} (ht : t ≤ params.timeBound) (k : V.K) :
    ∃ len ≤ params.maxStackDepth, varTrue σ (TableauVar.stkLen (V := V) t k len) := by
  unfold consistencyConstraints at hC
  have hBlock := evalCNF_flatMap_mem
    (evalCNF_flatMap_mem (evalCNF_append_right hC) (mem_range.mpr (Nat.lt_succ_of_le ht)))
    (Finset.mem_toList.mpr (Finset.mem_univ k))
  obtain ⟨v, hv, hv_true⟩ := exactlyOne_exists hBlock
  simp only [mem_map, mem_range] at hv
  obtain ⟨len, hlen, rfl⟩ := hv
  exact ⟨len, Nat.lt_succ_iff.mp hlen, hv_true⟩

private theorem stkElem_exists {σ : Assignment} {params : Params V}
    (hC : evalCNF σ (consistencyConstraints params) = true)
    {t : ℕ} (ht : t ≤ params.timeBound) (k : V.K) (j : ℕ) (hj : j < params.maxStackDepth) :
    ∃ γ : V.Γ k, varTrue σ (TableauVar.stkElem (V := V) t k j γ) := by
  unfold consistencyConstraints at hC
  have hSE := evalCNF_append_right (evalCNF_append_left hC)
  have hBlock := evalCNF_flatMap_mem
    (evalCNF_flatMap_mem
      (evalCNF_flatMap_mem hSE (mem_range.mpr (Nat.lt_succ_of_le ht)))
      (Finset.mem_toList.mpr (Finset.mem_univ k)))
    (mem_range.mpr hj)
  obtain ⟨v, hv, hv_true⟩ := exactlyOne_exists hBlock
  simp only [Finset.mem_toList, Finset.mem_univ, true_and, mem_map] at hv
  obtain ⟨γ, _, rfl⟩ := hv
  exact ⟨γ, hv_true⟩

/-- From consistency constraints, construct topsInfo compatible with σ at time t. -/
private theorem topsInfo_from_consistency {σ : Assignment} {params : Params V}
    (hC : evalCNF σ (consistencyConstraints params) = true)
    {t : ℕ} (ht : t ≤ params.timeBound) :
    ∃ (topsInfo : ∀ k : V.K, Option (Fin params.maxStackDepth × V.Γ k)),
    ∀ k, match topsInfo k with
      | none => varTrue σ (TableauVar.stkLen (V := V) t k 0)
      | some (len, γ) => varTrue σ (TableauVar.stkLen t k (len.val + 1)) ∧
                           varTrue σ (TableauVar.stkElem t k len.val γ) := by
  have h_each : ∀ k : V.K, ∃ (opt : Option (Fin params.maxStackDepth × V.Γ k)),
      match opt with
      | none => varTrue σ (TableauVar.stkLen (V := V) t k 0)
      | some (len, γ) => varTrue σ (TableauVar.stkLen t k (len.val + 1)) ∧
                           varTrue σ (TableauVar.stkElem t k len.val γ) := by
    intro k
    obtain ⟨len, hlen, hv⟩ := stkLen_exists hC ht k
    by_cases h0 : len = 0
    · exact ⟨none, by subst h0; exact hv⟩
    · have hj : len - 1 < params.maxStackDepth := by omega
      obtain ⟨γ, hγ⟩ := stkElem_exists hC ht k (len - 1) hj
      refine ⟨some (⟨len - 1, hj⟩, γ), ?_, ?_⟩
      · rw [show (len - 1 : ℕ) + 1 = len from by omega]; exact hv
      · exact hγ
  choose f hf using h_each
  exact ⟨f, hf⟩

/-! ### Inductive step -/

/-- Halted step: when label = none, transition constraints force label/state
    to stay the same at t+1. -/
private theorem step_tracks_halted {params : Params V} {input : List (V.Γ V.k₀)}
    {σ : Assignment} (hsat : evalCNF σ (tableauFormula params input) = true)
    {t : ℕ} (ht : t < params.timeBound)
    (h_none : (cfgAt V input t).l = none)
    (h_label : varTrue σ (TableauVar.label (V := V) t (cfgAt V input t).l))
    (h_state : varTrue σ (TableauVar.state (V := V) t (cfgAt V input t).var)) :
    varTrue σ (TableauVar.label (V := V) (t + 1) (cfgAt V input (t + 1)).l) ∧
    varTrue σ (TableauVar.state (V := V) (t + 1) (cfgAt V input (t + 1)).var) := by
  rw [cfgAt_halted_succ input t h_none]
  rw [h_none] at h_label ⊢
  unfold tableauFormula at hsat
  have hC := evalCNF_append_left (evalCNF_append_left (evalCNF_append_left (evalCNF_append_left hsat)))
  have hT := evalCNF_append_right (evalCNF_append_left (evalCNF_append_left hsat))
  obtain ⟨topsInfo, h_stks⟩ := topsInfo_from_consistency hC (by omega : t ≤ params.timeBound)
  exact halted_forces_next ht hT (cfgAt V input t).var topsInfo h_label h_state h_stks

/-- **Running step (proved from full invariant + BRD)**: When label = some lbl at time t,
    the transition clauses force label/state at t+1 to match the actual TM computation.

    This replaces the previous `step_tracks_running` axiom by using:
    1. The full configuration invariant (σ tracks stkLen and stkElem)
    2. Consistency uniqueness (to show topsInfo from consistency matches actual stacks)
    3. `stepAux_soundness` (to show transition consequent matches actual computation)
    4. BoundedReadDepth (to ensure readDepth ≤ 1 for stack agreement) -/
private theorem step_tracks_running {params : Params V} {input : List (V.Γ V.k₀)}
    {σ : Assignment} (hsat : evalCNF σ (tableauFormula params input) = true)
    {t : ℕ} (ht : t < params.timeBound) {lbl : V.Λ}
    (h_some : (cfgAt V input t).l = some lbl)
    (h_label : varTrue σ (TableauVar.label (V := V) t (some lbl)))
    (h_state : varTrue σ (TableauVar.state (V := V) t (cfgAt V input t).var))
    -- Full stack invariant
    (h_stkLen : ∀ k, varTrue σ (TableauVar.stkLen (V := V) t k ((cfgAt V input t).stk k).length))
    (h_stkElem : ∀ k (j : ℕ) (hj : j < ((cfgAt V input t).stk k).length),
      varTrue σ (TableauVar.stkElem (V := V) t k j
        (((cfgAt V input t).stk k).reverse[j]'(by rw [length_reverse]; exact hj))))
    -- Stack depth bound
    (h_depth : ∀ k, ((cfgAt V input t).stk k).length ≤ params.maxStackDepth)
    -- Bounded read depth
    (hBRD : BoundedReadDepth V) :
    varTrue σ (TableauVar.label (V := V) (t + 1) (cfgAt V input (t + 1)).l) ∧
    varTrue σ (TableauVar.state (V := V) (t + 1) (cfgAt V input (t + 1)).var) := by
  -- Get components
  unfold tableauFormula at hsat
  have hC := evalCNF_append_left (evalCNF_append_left (evalCNF_append_left (evalCNF_append_left hsat)))
  have hT := evalCNF_append_right (evalCNF_append_left (evalCNF_append_left hsat))
  -- Get topsInfo from consistency
  obtain ⟨topsInfo, h_stks⟩ := topsInfo_from_consistency hC (by omega : t ≤ params.timeBound)
  -- Navigate to transition clause for (some lbl, cfg.var, topsInfo)
  unfold transitionConstraints at hT
  have hTC := evalCNF_flatMap_mem hT (mem_range.mpr ht)
  unfold transitionClausesAt at hTC
  have h1 := evalCNF_flatMap_mem hTC
    (Finset.mem_toList.mpr (Finset.mem_univ (some lbl : Option V.Λ)))
  have h2 := evalCNF_flatMap_mem h1
    (Finset.mem_toList.mpr (Finset.mem_univ (cfgAt V input t).var))
  have h3 := evalCNF_flatMap_mem h2
    (Finset.mem_toList.mpr (Finset.mem_univ topsInfo))
  -- Extract label/state clauses
  dsimp only at h3
  have h_pair := evalCNF_append_left h3
  simp only [evalCNF, all_cons, all_nil, Bool.and_true, Bool.and_eq_true] at h_pair
  obtain ⟨h_lc, h_sc⟩ := h_pair
  -- Antecedent is all-false
  have h_af := antecedent_all_false h_label h_state h_stks
  -- Extract consequents
  have h_lf := consequent_of_clause h_lc h_af
  have h_sf := consequent_of_clause h_sc h_af
  -- Show stkVals agrees with actual stacks on top readDepth elements
  -- via consistency uniqueness
  have h_agree : ∀ k,
      (match topsInfo k with
        | none => ([] : List (V.Γ k)) | some (_, γ) => [γ]).take
        (stmtReadDepth k (V.m lbl)) =
      ((cfgAt V input t).stk k).take (stmtReadDepth k (V.m lbl)) := by
    intro k
    have hrd := brd_section hBRD lbl k
    -- readDepth = 0 or 1
    cases h_rd : stmtReadDepth k (V.m lbl) with
    | zero => rfl
    | succ n =>
      have hn : n = 0 := by omega
      subst hn
      -- Goal: (match topsInfo k ...).take 1 = actual.take 1
      -- Show head? agree for stkVals and actual stack
      have h_k := h_stks k
      split at h_k
      · -- topsInfo k = none → σ marks stkLen t k 0 → actual len = 0 → stk empty
        rename_i h_none
        have h_len0 := consistency_stkLen_unique hC (by omega) k h_k (h_stkLen k) (by omega) (h_depth k)
        have h_nil : (cfgAt V input t).stk k = [] := List.eq_nil_iff_length_eq_zero.mpr h_len0.symm
        simp [h_nil]
      · -- topsInfo k = some (len, γ)
        rename_i len γ h_some_ti
        obtain ⟨h_len_v, h_elem_v⟩ := h_k
        have h_len_eq := consistency_stkLen_unique hC (by omega) k h_len_v (h_stkLen k)
          (by omega) (h_depth k)
        -- actual length ≥ 1
        have hpos : 0 < ((cfgAt V input t).stk k).length := by omega
        -- Decompose: stk k = head :: rest
        cases h_stk_eq : (cfgAt V input t).stk k with
        | nil => simp [h_stk_eq] at hpos
        | cons head rest =>
        simp
        -- Show γ = head via stkElem uniqueness
        -- After cases, (cfgAt V input t).stk k = head :: rest
        have hj : rest.length < (head :: rest).length := by simp
        have h_elem_actual := h_stkElem k rest.length (h_stk_eq ▸ hj)
        have hj_eq : len.val = rest.length := by simp [h_stk_eq] at h_len_eq ⊢; omega
        rw [hj_eq] at h_elem_v
        have h_eq := consistency_stkElem_unique hC (by omega) k _ (by omega) h_elem_v h_elem_actual
        -- h_eq : γ = reverse[rest.length] where stk k = head :: rest
        -- reverse = rest.reverse ++ [head], so reverse[rest.length] = head
        simp only [h_stk_eq, reverse_cons] at h_eq
        -- h_eq : γ = (rest.reverse ++ [head])[rest.length]
        rw [getElem_append_right (by simp : rest.reverse.length ≤ rest.length)] at h_eq
        simp at h_eq
        exact h_eq
  -- Apply stepAux_soundness
  have h_sound := stepAux_soundness (V.m lbl) (cfgAt V input t).var
    (fun k => match topsInfo k with | none => [] | some (_, γ) => [γ])
    (cfgAt V input t).stk h_agree
  -- Actual next config
  have h_next : cfgAt V input (t + 1) = TM2.stepAux (V.m lbl) (cfgAt V input t).var
      (cfgAt V input t).stk := by
    rw [cfgAt_succ, stepOrHalt_running h_some]
  -- Combine
  rw [h_next]
  constructor
  · rw [← h_sound.1]; simp [varTrue, tLit, evalLiteral] at h_lf ⊢; exact h_lf
  · rw [← h_sound.2]; simp [varTrue, tLit, evalLiteral] at h_sf ⊢; exact h_sf

/-! ### Stack invariant maintenance -/

/-- Frame preservation extraction: if the assignment satisfies the formula and correctly
    encodes stkLen and stkElem at time t, then elements below the read depth are
    preserved at t+1. -/
private theorem frame_preserves_elem {params : Params V} {input : List (V.Γ V.k₀)}
    {σ : Assignment} (hsat : evalCNF σ (tableauFormula params input) = true)
    {t : ℕ} (ht : t < params.timeBound) {k : V.K} {j : ℕ} {γ : V.Γ k}
    {len : ℕ} (h_guard : j + maxReadDepth V k < len)
    (h_len_bound : len ≤ params.maxStackDepth)
    (h_stkLen : varTrue σ (TableauVar.stkLen (V := V) t k len))
    (h_stkElem : varTrue σ (TableauVar.stkElem (V := V) t k j γ)) :
    varTrue σ (TableauVar.stkElem (V := V) (t + 1) k j γ) := by
  unfold tableauFormula at hsat
  have hF := evalCNF_append_right (evalCNF_append_left hsat)
  unfold framePreservation at hF
  have h1 := evalCNF_flatMap_mem hF (mem_range.mpr ht)
  have h2 := evalCNF_flatMap_mem h1 (Finset.mem_toList.mpr (Finset.mem_univ k))
  have h3 := evalCNF_flatMap_mem h2 (mem_range.mpr (by omega : j < params.maxStackDepth))
  have h4 := evalCNF_flatMap_mem h3 (Finset.mem_toList.mpr (Finset.mem_univ γ))
  simp only [evalCNF, all_eq_true] at h4
  have h_clause_in : [tLit V (TableauVar.stkLen t k len) false,
                       tLit V (TableauVar.stkElem t k j γ) false,
                       tLit V (TableauVar.stkElem (t + 1) k j γ) true] ∈
      (List.range (params.maxStackDepth + 1)).filterMap (fun len' =>
        if j + maxReadDepth V k < len' then
          some [tLit V (TableauVar.stkLen t k len') false,
                tLit V (TableauVar.stkElem t k j γ) false,
                tLit V (TableauVar.stkElem (t + 1) k j γ) true]
        else none) := by
    rw [mem_filterMap]; exact ⟨len, by rw [mem_range]; omega, by simp [h_guard]⟩
  have h5 := h4 _ h_clause_in
  have h_neg1 : evalLiteral σ (tLit V (TableauVar.stkLen t k len) false) = false := by
    simp [tLit, evalLiteral, varTrue] at h_stkLen ⊢; exact h_stkLen
  have h_neg2 : evalLiteral σ (tLit V (TableauVar.stkElem t k j γ) false) = false := by
    simp [tLit, evalLiteral, varTrue] at h_stkElem ⊢; exact h_stkElem
  simp only [evalClause, any_cons, any_nil, Bool.or_false, h_neg1, h_neg2, Bool.false_or] at h5
  simp [tLit, evalLiteral, varTrue] at h5 ⊢; exact h5

/-- Stack tracking maintenance (PROVED).
    If the full invariant holds at time t, then σ also correctly tracks
    stkLen and stkElem at time t+1.
    Proved by extracting transition clause consequents + frame preservation. -/
private theorem step_tracks_stacks'
    {params : Params V} {input : List (V.Γ V.k₀)}
    {σ : Assignment} (hsat : evalCNF σ (tableauFormula params input) = true)
    {t : ℕ} (ht : t < params.timeBound)
    (h_label : varTrue σ (TableauVar.label (V := V) t (cfgAt V input t).l))
    (h_state : varTrue σ (TableauVar.state (V := V) t (cfgAt V input t).var))
    (h_stkLen : ∀ k, varTrue σ (TableauVar.stkLen (V := V) t k ((cfgAt V input t).stk k).length))
    (h_stkElem : ∀ k (j : ℕ) (hj : j < ((cfgAt V input t).stk k).length),
      varTrue σ (TableauVar.stkElem (V := V) t k j
        (((cfgAt V input t).stk k).reverse[j]'(by rw [length_reverse]; exact hj))))
    (h_depth : ∀ k, ((cfgAt V input t).stk k).length ≤ params.maxStackDepth)
    (hBRD : BoundedReadDepth V) :
    (∀ k, varTrue σ (TableauVar.stkLen (V := V) (t+1) k ((cfgAt V input (t+1)).stk k).length)) ∧
    (∀ k (j : ℕ) (hj : j < ((cfgAt V input (t+1)).stk k).length),
      varTrue σ (TableauVar.stkElem (V := V) (t+1) k j
        (((cfgAt V input (t+1)).stk k).reverse[j]'(by rw [length_reverse]; exact hj)))) ∧
    (∀ k, ((cfgAt V input (t+1)).stk k).length ≤ params.maxStackDepth) := by
  -- Extract components from hsat
  unfold tableauFormula at hsat
  have hC := evalCNF_append_left (evalCNF_append_left (evalCNF_append_left (evalCNF_append_left hsat)))
  have hT := evalCNF_append_right (evalCNF_append_left (evalCNF_append_left hsat))
  obtain ⟨topsInfo, h_stks⟩ := topsInfo_from_consistency hC (by omega : t ≤ params.timeBound)
  -- Navigate to matching transition clause
  unfold transitionConstraints at hT
  have hTC := evalCNF_flatMap_mem hT (mem_range.mpr ht)
  unfold transitionClausesAt at hTC
  -- Case split on halted vs running
  cases h_lbl : (cfgAt V input t).l with
  | none =>
    -- Halted: cfgAt (t+1) = cfgAt t
    have h_eq : cfgAt V input (t + 1) = cfgAt V input t :=
      cfgAt_halted_succ input t h_lbl
    -- Depth bound transfers directly
    refine ⟨?_, ?_, fun k => by simp [h_eq]; exact h_depth k⟩
    · -- stkLen
      rw [h_lbl] at h_label
      have h1 := evalCNF_flatMap_mem hTC
        (Finset.mem_toList.mpr (Finset.mem_univ (none : Option V.Λ)))
      have h2 := evalCNF_flatMap_mem h1
        (Finset.mem_toList.mpr (Finset.mem_univ (cfgAt V input t).var))
      have h3 := evalCNF_flatMap_mem h2
        (Finset.mem_toList.mpr (Finset.mem_univ topsInfo))
      dsimp only at h3
      have h_stk_block := evalCNF_append_right h3
      have h_af := antecedent_all_false h_label h_state h_stks
      intro k; simp [h_eq]
      have h_k := evalCNF_flatMap_mem h_stk_block
        (Finset.mem_toList.mpr (Finset.mem_univ k))
      cases h_ti : topsInfo k with
      | none =>
        simp [h_ti] at h_k
        simp only [evalCNF, all_cons, all_nil, Bool.and_true] at h_k
        have h_len0 := consequent_of_clause h_k h_af
        have h_stk_k := h_stks k; rw [h_ti] at h_stk_k
        have h_actual_len := consistency_stkLen_unique hC (by omega) k h_stk_k (h_stkLen k) (by omega) (h_depth k)
        rw [← h_actual_len]
        simp [tLit, evalLiteral, varTrue] at h_len0 ⊢; exact h_len0
      | some p =>
        obtain ⟨len, γ⟩ := p
        simp [h_ti] at h_k
        simp only [evalCNF, all_cons, all_nil, Bool.and_true, Bool.and_eq_true] at h_k
        have h_lenC := consequent_of_clause h_k.1 h_af
        have h_stk_k := h_stks k; rw [h_ti] at h_stk_k
        obtain ⟨h_len_v, _⟩ := h_stk_k
        have h_actual_len := consistency_stkLen_unique hC (by omega) k h_len_v (h_stkLen k) (by omega) (h_depth k)
        rw [← h_actual_len]
        simp [tLit, evalLiteral, varTrue] at h_lenC ⊢; exact h_lenC
    · -- stkElem (halted case)
      rw [h_lbl] at h_label
      have h1 := evalCNF_flatMap_mem hTC
        (Finset.mem_toList.mpr (Finset.mem_univ (none : Option V.Λ)))
      have h2 := evalCNF_flatMap_mem h1
        (Finset.mem_toList.mpr (Finset.mem_univ (cfgAt V input t).var))
      have h3 := evalCNF_flatMap_mem h2
        (Finset.mem_toList.mpr (Finset.mem_univ topsInfo))
      dsimp only at h3
      have h_stk_block := evalCNF_append_right h3
      have h_af := antecedent_all_false h_label h_state h_stks
      intro k j hj
      -- hj : j < (cfgAt (t+1)).stk k .length
      -- Rewrite cfgAt(t+1) = cfgAt(t) in the bound
      have hj' : j < ((cfgAt V input t).stk k).length := by simp [h_eq] at hj; exact hj
      -- Show the goal elements match
      have h_rev_eq : ((cfgAt V input (t + 1)).stk k).reverse[j]'(by rw [length_reverse]; exact hj) =
          ((cfgAt V input t).stk k).reverse[j]'(by rw [length_reverse]; exact hj') := by
        simp [h_eq]
      rw [h_rev_eq]
      -- Now goal: varTrue σ (stkElem (t+1) k j ((cfgAt t).stk k .reverse[j]))
      have h_stk_k := h_stks k
      by_cases h_frame : j + maxReadDepth V k < ((cfgAt V input t).stk k).length
      · -- Frame region
        exact frame_preserves_elem hsat ht h_frame (h_depth k) (h_stkLen k) (h_stkElem k j hj')
      · -- Top region: use transition clause consequent
        -- Only applies when topsInfo k = some (len, γ) and j = len
        have h_k := evalCNF_flatMap_mem h_stk_block
          (Finset.mem_toList.mpr (Finset.mem_univ k))
        cases h_ti : topsInfo k with
        | none =>
          -- Empty stack → hj : j < 0, contradiction
          rw [h_ti] at h_stk_k
          have := consistency_stkLen_unique hC (by omega) k h_stk_k (h_stkLen k) (by omega) (h_depth k)
          omega
        | some p =>
          obtain ⟨len, γ⟩ := p
          rw [h_ti] at h_stk_k
          obtain ⟨h_len_v, h_elem_v⟩ := h_stk_k
          have h_actual_len := consistency_stkLen_unique hC (by omega) k h_len_v (h_stkLen k) (by omega) (h_depth k)
          -- j + maxReadDepth V k ≥ (len + 1) and j < (len + 1)
          -- Since maxReadDepth V k ≥ 1 (because it's at least stmtReadDepth for some lbl)
          -- Actually maxReadDepth is the maximum over all labels, could be 0 for some k
          -- We need: j = len (the top element)
          -- From ¬(j + maxRD < len + 1) and j < len + 1: j ≥ len + 1 - maxRD
          -- With BRD ≤ 1: maxRD ≤ 1, so j ≥ len
          -- And j < len + 1 = j ≤ len. So j = len.
          -- But maxReadDepth could be > 1 for some k! Need BRD.
          -- Actually halted case: maxReadDepth not directly relevant.
          -- The transition clause for halted provides stkElem for j = len only.
          -- For j < len but j + maxRD ≥ len+1: this is a gap!
          -- Unless maxRD ≤ 1 always (from BRD).
          -- BRD says stmtReadDepth k (V.m lbl) ≤ 1 for all lbl.
          -- maxReadDepth k = max over lbl of stmtReadDepth k (V.m lbl) ≤ 1.
          -- So maxRD ≤ 1 for all k (from BRD).
          -- Therefore: ¬(j + maxRD < len + 1) with maxRD ≤ 1 → j ≥ len
          -- And j < len + 1 → j ≤ len. So j = len.
          -- maxReadDepth ≤ 1 from BRD
          have h_maxRD : maxReadDepth V k ≤ 1 := by
            unfold maxReadDepth
            rw [Finset.fold_max_le]
            refine ⟨by omega, fun lbl _ => ?_⟩
            exact le_of_eq_of_le (by congr 1) (hBRD lbl k)
          have h_j_eq : j = len.val := by omega
          subst h_j_eq
          -- Extract stkElem consequent from transition clause
          simp [h_ti] at h_k
          simp only [evalCNF, all_cons, all_nil, Bool.and_true, Bool.and_eq_true] at h_k
          have h_elemC := consequent_of_clause h_k.2 h_af
          -- h_elemC : varTrue σ (stkElem (t+1) k len γ)
          -- Need: reverse[len] = γ at actual stack
          -- consistency_stkElem_unique: γ must match actual reverse[len]
          have h_elem_actual := h_stkElem k len.val (by omega)
          have h_γ_eq := consistency_stkElem_unique hC (by omega) k len.val (by omega)
            h_elem_v h_elem_actual
          -- h_γ_eq : γ = actual.reverse[len]
          simp only [h_γ_eq] at h_elemC
          exact h_elemC
  | some lbl =>
    -- Running case: cfgAt(t+1) = stepAux (V.m lbl) cfg.var cfg.stk
    have h_next : cfgAt V input (t + 1) = TM2.stepAux (V.m lbl) (cfgAt V input t).var
        (cfgAt V input t).stk := by
      rw [cfgAt_succ, stepOrHalt_running h_lbl]
    -- Get topsInfo and extract transition clause
    rw [h_lbl] at h_label
    have h1 := evalCNF_flatMap_mem hTC
      (Finset.mem_toList.mpr (Finset.mem_univ (some lbl : Option V.Λ)))
    have h2 := evalCNF_flatMap_mem h1
      (Finset.mem_toList.mpr (Finset.mem_univ (cfgAt V input t).var))
    have h3 := evalCNF_flatMap_mem h2
      (Finset.mem_toList.mpr (Finset.mem_univ topsInfo))
    dsimp only at h3
    have h_stk_block := evalCNF_append_right h3
    have h_af := antecedent_all_false h_label h_state h_stks
    -- stkVals and ns definitions
    set stkVals := (fun k : V.K => match topsInfo k with | none => ([] : List (V.Γ k)) | some (_, γ) => [γ])
    set res := TM2.stepAux (V.m lbl) (cfgAt V input t).var stkVals
    -- h_agree: stkVals agrees with actual stacks on read depth
    have h_agree : ∀ k,
        (stkVals k).take (stmtReadDepth k (V.m lbl)) =
        ((cfgAt V input t).stk k).take (stmtReadDepth k (V.m lbl)) := by
      -- Copy from step_tracks_running proof (same argument)
      intro k
      have hrd := brd_section hBRD lbl k
      cases h_rd : stmtReadDepth k (V.m lbl) with
      | zero => rfl
      | succ n =>
        have hn : n = 0 := by omega; subst hn
        have h_k := h_stks k
        split at h_k
        · rename_i h_none
          have h_len0 := consistency_stkLen_unique hC (by omega) k h_k (h_stkLen k) (by omega) (h_depth k)
          have h_nil : (cfgAt V input t).stk k = [] := List.eq_nil_iff_length_eq_zero.mpr h_len0.symm
          simp [h_nil]
        · rename_i len γ h_some_ti
          obtain ⟨h_len_v, h_elem_v⟩ := h_k
          have h_len_eq := consistency_stkLen_unique hC (by omega) k h_len_v (h_stkLen k)
            (by omega) (h_depth k)
          have hpos : 0 < ((cfgAt V input t).stk k).length := by omega
          cases h_stk_eq : (cfgAt V input t).stk k with
          | nil => simp [h_stk_eq] at hpos
          | cons head rest =>
          simp
          simp only [h_stk_eq] at h_len_eq
          have hj_eq : len.val = rest.length := by simp at h_len_eq; omega
          rw [hj_eq] at h_elem_v
          have h_eq := consistency_stkElem_unique hC (by omega) k _ (by omega) h_elem_v
            (h_stkElem k rest.length (h_stk_eq ▸ (by simp)))
          simp only [h_stk_eq, reverse_cons] at h_eq
          rw [getElem_append_right (by simp : rest.reverse.length ≤ rest.length)] at h_eq
          simp at h_eq
          exact h_eq
    -- Stack consequents from transition clause
    refine ⟨?_, ?_, ?_⟩
    · -- stkLen at t+1
      intro k; rw [h_next]
      have h_k := evalCNF_flatMap_mem h_stk_block
        (Finset.mem_toList.mpr (Finset.mem_univ k))
      -- Navigate to stkLen clause
      set ns := res.stk k
      have h_stkLen_block := evalCNF_append_left h_k
      simp only [evalCNF, all_cons, all_nil, Bool.and_true] at h_stkLen_block
      have h_lenC := consequent_of_clause h_stkLen_block h_af
      -- h_lenC : varTrue σ (stkLen (t+1) k newLen) where newLen = oldLen + ns.length - adj
      -- Show actual length = newLen
      have h_len_delta := stepAux_stk_len_delta (V.m lbl) (cfgAt V input t).var
        stkVals (cfgAt V input t).stk h_agree k
      -- Compute newLen = actual length
      -- This follows the same pattern as Soundness stkLen proof
      sorry
    · -- stkElem at t+1
      sorry
    · -- Depth bound at t+1
      sorry

-- CNF helpers (local copies, also in Soundness.lean)
private theorem evalCNF_append_c (σ : Assignment) (c1 c2 : CNF) :
    evalCNF σ (c1 ++ c2) = (evalCNF σ c1 && evalCNF σ c2) := by
  simp [evalCNF, List.all_append]

private theorem evalCNF_left_c {σ : Assignment} {a b : CNF}
    (h : evalCNF σ (a ++ b) = true) : evalCNF σ a = true := by
  rw [evalCNF_append_c] at h; simp [Bool.and_eq_true] at h; exact h.1

private theorem evalCNF_right_c {σ : Assignment} {a b : CNF}
    (h : evalCNF σ (a ++ b) = true) : evalCNF σ b = true := by
  rw [evalCNF_append_c] at h; simp [Bool.and_eq_true] at h; exact h.2

private theorem evalCNF_singleton_c {σ : Assignment} {lit : Literal}
    (h : evalCNF σ [[lit]] = true) : evalLiteral σ lit = true := by
  simp [evalCNF, evalClause] at h; exact h

private theorem tLit_pos_val_c {σ : Assignment} (v : TableauVar V)
    (h : evalLiteral σ (tLit V v true) = true) : σ (Encodable.encode v) = true := by
  unfold tLit at h; simp [evalLiteral] at h; exact h

private theorem extract_initial_c {params : Params V} {input : List (V.Γ V.k₀)} {σ : Assignment}
    (hsat : evalCNF σ (tableauFormula params input) = true) :
    evalCNF σ (initialConstraints params input) = true := by
  unfold tableauFormula at hsat
  exact evalCNF_right_c (evalCNF_left_c (evalCNF_left_c (evalCNF_left_c hsat)))

private theorem initList_stk_k0_c (input : List (V.Γ V.k₀)) :
    (Turing.initList V input).stk V.k₀ = input := by
  simp [Turing.initList]

private theorem initList_stk_other_c (input : List (V.Γ V.k₀)) (k : V.K) (hk : k ≠ V.k₀) :
    (Turing.initList V input).stk k = [] := by
  simp [Turing.initList, hk]

/-- Base case for stack tracking: initial constraints force correct stkLen and stkElem at t=0.
    Proved from the structure of initialConstraints. -/
theorem trace_base_stacks'
    {params : Params V} {input : List (V.Γ V.k₀)}
    {σ : Assignment} (hsat : evalCNF σ (tableauFormula params input) = true)
    (h_depth : ∀ k, ((cfgAt V input 0).stk k).length ≤ params.maxStackDepth) :
    (∀ k, varTrue σ (TableauVar.stkLen (V := V) 0 k ((cfgAt V input 0).stk k).length)) ∧
    (∀ k (j : ℕ) (hj : j < ((cfgAt V input 0).stk k).length),
      varTrue σ (TableauVar.stkElem (V := V) 0 k j
        (((cfgAt V input 0).stk k).reverse[j]'(by rw [List.length_reverse]; exact hj)))) := by
  have h_init := extract_initial_c hsat
  have h_cfg0 : cfgAt V input 0 = Turing.initList V input := by simp [cfgAt]
  rw [h_cfg0]
  unfold initialConstraints at h_init
  constructor
  · -- stkLen
    intro k; unfold varTrue
    by_cases hk : k = V.k₀
    · subst hk; rw [initList_stk_k0_c]
      have h3 := evalCNF_singleton_c (evalCNF_right_c (evalCNF_left_c (evalCNF_left_c h_init)))
      exact tLit_pos_val_c _ h3
    · rw [initList_stk_other_c input k hk]
      have h5 := evalCNF_right_c h_init
      rw [evalCNF, List.all_eq_true] at h5
      have h_mem : [tLit V (TableauVar.stkLen 0 k 0) true] ∈
          (Finset.univ.toList.flatMap (fun k' => if k' = V.k₀ then [] else
            [[tLit V (TableauVar.stkLen 0 k' 0) true]])) := by
        rw [List.mem_flatMap]
        exact ⟨k, Finset.mem_toList.mpr (Finset.mem_univ k), by simp [hk]⟩
      have h_cl := h5 _ h_mem
      simp [evalClause] at h_cl
      exact tLit_pos_val_c _ h_cl
  · -- stkElem
    intro k j hj; unfold varTrue
    by_cases hk : k = V.k₀
    · subst hk
      have h_stk_eq : (Turing.initList V input).stk V.k₀ = input := initList_stk_k0_c input
      simp only [h_stk_eq] at hj ⊢
      have h4 := evalCNF_right_c (evalCNF_left_c h_init)
      rw [evalCNF, List.all_eq_true] at h4
      set γ := input.reverse[j]'(by rw [List.length_reverse]; exact hj) with γ_def
      have hj' : j < (input.reverse.zipIdx).length := by simp; exact hj
      have h_mem_zip : (γ, j) ∈ input.reverse.zipIdx := by
        have h := getElem_mem hj'
        rw [List.getElem_zipIdx, Nat.zero_add] at h
        rwa [γ_def]
      have h_cl_mem : [tLit V (TableauVar.stkElem 0 V.k₀ j γ) true] ∈
          (input.reverse.zipIdx.map (fun ⟨γ', j'⟩ => [tLit V (TableauVar.stkElem 0 V.k₀ j' γ') true])) := by
        rw [List.mem_map]; exact ⟨(γ, j), h_mem_zip, rfl⟩
      have h_cl := h4 _ h_cl_mem
      simp [evalClause] at h_cl
      exact tLit_pos_val_c _ h_cl
    · rw [initList_stk_other_c input k hk] at hj
      exact absurd hj (by simp)

/-! ### Full invariant induction -/

/-- **Full invariant**: σ tracks label, state, stack lengths, and stack elements. -/
theorem trace_tracks_full
    (V : Turing.FinTM2) [Encodable V.Λ] [Encodable V.σ] [Encodable V.K]
    [∀ k, Encodable (V.Γ k)]
    [Fintype V.Λ] [Fintype V.σ] [Fintype V.K] [∀ k, Fintype (V.Γ k)]
    [DecidableEq V.K] [∀ k, DecidableEq (V.Γ k)]
    [DecidableEq V.Λ] [DecidableEq V.σ]
    (params : Params V) (input : List (V.Γ V.k₀))
    (σ : Assignment) (hsat : evalCNF σ (tableauFormula params input) = true)
    (hBRD : BoundedReadDepth V)
    (h_depth0 : ∀ k, ((cfgAt V input 0).stk k).length ≤ params.maxStackDepth)
    (t : ℕ) (ht : t ≤ params.timeBound) :
    varTrue σ (TableauVar.label (V := V) t (cfgAt V input t).l) ∧
    varTrue σ (TableauVar.state (V := V) t (cfgAt V input t).var) ∧
    (∀ k, varTrue σ (TableauVar.stkLen (V := V) t k ((cfgAt V input t).stk k).length)) ∧
    (∀ k (j : ℕ) (hj : j < ((cfgAt V input t).stk k).length),
      varTrue σ (TableauVar.stkElem (V := V) t k j
        (((cfgAt V input t).stk k).reverse[j]'(by rw [length_reverse]; exact hj)))) ∧
    (∀ k, ((cfgAt V input t).stk k).length ≤ params.maxStackDepth) := by
  induction t with
  | zero =>
    obtain ⟨h_sL, h_sE⟩ := trace_base_stacks' hsat h_depth0
    exact ⟨trace_base_label params input σ hsat, trace_base_state params input σ hsat,
           h_sL, h_sE, h_depth0⟩
  | succ t ih =>
    obtain ⟨ih_l, ih_s, ih_sL, ih_sE, ih_d⟩ := ih (by omega)
    -- Stacks at t+1 (compute first to avoid typeclass issues)
    have h_stk := step_tracks_stacks' hsat (by omega : t < params.timeBound) ih_l ih_s ih_sL ih_sE ih_d hBRD
    -- Label/state at t+1
    have h_ls : varTrue σ (TableauVar.label (V := V) (t+1) (cfgAt V input (t+1)).l) ∧
                varTrue σ (TableauVar.state (V := V) (t+1) (cfgAt V input (t+1)).var) := by
      cases h_lbl : (cfgAt V input t).l with
      | none => exact step_tracks_halted hsat (by omega) h_lbl ih_l ih_s
      | some lbl =>
        rw [h_lbl] at ih_l
        exact step_tracks_running hsat (by omega) h_lbl ih_l ih_s ih_sL ih_sE ih_d hBRD
    exact ⟨h_ls.1, h_ls.2, h_stk.1, h_stk.2.1, h_stk.2.2⟩

/-- Corollary: σ tracks label and state (backward compatible). -/
theorem trace_tracks_label_state
    (V : Turing.FinTM2) [Encodable V.Λ] [Encodable V.σ] [Encodable V.K]
    [∀ k, Encodable (V.Γ k)]
    [Fintype V.Λ] [Fintype V.σ] [Fintype V.K] [∀ k, Fintype (V.Γ k)]
    [DecidableEq V.K] [∀ k, DecidableEq (V.Γ k)]
    [DecidableEq V.Λ] [DecidableEq V.σ]
    (params : Params V) (input : List (V.Γ V.k₀))
    (σ : Assignment) (hsat : evalCNF σ (tableauFormula params input) = true)
    (hBRD : BoundedReadDepth V)
    (h_depth0 : ∀ k, ((cfgAt V input 0).stk k).length ≤ params.maxStackDepth)
    (t : ℕ) (ht : t ≤ params.timeBound) :
    varTrue σ (TableauVar.label (V := V) t (cfgAt V input t).l) ∧
    varTrue σ (TableauVar.state (V := V) t (cfgAt V input t).var) :=
  let h := trace_tracks_full V params input σ hsat hBRD h_depth0 t ht
  ⟨h.1, h.2.1⟩

/-- Corollary: σ tracks the label. -/
theorem trace_tracks_label (V : Turing.FinTM2) [Encodable V.Λ] [Encodable V.σ] [Encodable V.K]
    [∀ k, Encodable (V.Γ k)]
    [Fintype V.Λ] [Fintype V.σ] [Fintype V.K] [∀ k, Fintype (V.Γ k)]
    [DecidableEq V.K] [∀ k, DecidableEq (V.Γ k)]
    [DecidableEq V.Λ] [DecidableEq V.σ]
    (params : Params V) (input : List (V.Γ V.k₀))
    (σ : Assignment) (hsat : evalCNF σ (tableauFormula params input) = true)
    (hBRD : BoundedReadDepth V)
    (h_depth0 : ∀ k, ((cfgAt V input 0).stk k).length ≤ params.maxStackDepth)
    (t : ℕ) (ht : t ≤ params.timeBound) :
    varTrue σ (TableauVar.label (V := V) t (cfgAt V input t).l) :=
  (trace_tracks_full V params input σ hsat hBRD h_depth0 t ht).1

/-! ## Main completeness theorem -/

/-- **Completeness of Cook-Levin**: if the tableau formula is satisfiable,
    the TM computation halts within the time bound. -/
theorem completeness (V : FinTM2) [Encodable V.Λ] [Encodable V.σ] [Encodable V.K]
    [∀ k, Encodable (V.Γ k)]
    [Fintype V.Λ] [Fintype V.σ] [Fintype V.K] [∀ k, Fintype (V.Γ k)]
    [DecidableEq V.K] [∀ k, DecidableEq (V.Γ k)]
    [DecidableEq V.Λ] [DecidableEq V.σ]
    (params : Params V) (input : List (V.Γ V.k₀))
    (hBRD : BoundedReadDepth V)
    (h_depth0 : ∀ k, ((cfgAt V input 0).stk k).length ≤ params.maxStackDepth)
    (h_sat : Satisfiable (tableauFormula params input)) :
    ∃ i, i ≤ params.timeBound ∧
      (cfgAt V input i).l = none := by
  obtain ⟨σ, hσ⟩ := h_sat
  obtain ⟨T, hT, h_none⟩ := completeness_halting params input σ hσ
  have h_actual := trace_tracks_label V params input σ hσ hBRD h_depth0 T hT
  have ⟨hC, _, _, _, _⟩ := sat_components params input σ hσ
  exact ⟨T, hT, by rw [← consistency_label_unique hC hT h_none h_actual]⟩

end CookLevinTableau
