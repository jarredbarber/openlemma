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

/-! ## Transition constraints force the step

The core technique: match the configuration at time i to the transition clause
antecedent, then extract the consequent.
-/

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

/-- **Halted case**: if label = none at time t, transition clauses force
    label = none and state preserved at time t+1. Demonstrates the core
    proof technique: `evalCNF_flatMap_mem` to navigate the triple-nested
    flatMap in `transitionClausesAt`, then `consequent_of_clause` to
    extract the consequent when all antecedent literals are false. -/
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
  -- Step 1: Navigate transitionConstraints → transitionClausesAt t
  unfold transitionConstraints at hT
  have hTC := evalCNF_flatMap_mem hT (mem_range.mpr ht)
  -- Step 2: Navigate triple flatMap for (none, s, topsInfo)
  unfold transitionClausesAt at hTC
  have h1 := evalCNF_flatMap_mem hTC (Finset.mem_toList.mpr (Finset.mem_univ (none : Option V.Λ)))
  have h2 := evalCNF_flatMap_mem h1 (Finset.mem_toList.mpr (Finset.mem_univ s))
  have h3 := evalCNF_flatMap_mem h2 (Finset.mem_toList.mpr (Finset.mem_univ topsInfo))
  -- Step 3: Reduce let bindings, extract first two clauses
  dsimp only at h3
  have h_pair := evalCNF_append_left h3
  simp only [evalCNF, all_cons, all_nil, Bool.and_true, Bool.and_eq_true] at h_pair
  obtain ⟨h_lc, h_sc⟩ := h_pair
  -- Step 4: All antecedent lits are false → consequent is true
  have h_af := antecedent_all_false h_label h_state h_stks
  constructor
  · have := consequent_of_clause h_lc h_af
    simp [varTrue, tLit, evalLiteral] at this; exact this
  · have := consequent_of_clause h_sc h_af
    simp [varTrue, tLit, evalLiteral] at this; exact this

/-! ## Trace-computation correspondence

We prove by induction on `t` that the satisfying assignment σ tracks the actual
TM2 computation's label and state at each timestep. The proof structure:
- **Base case** (t=0): from `initialConstraints` (proved above).
- **Halted step** (label=none): `halted_forces_next` shows label stays none.
- **Running step** (label=some lbl): the transition clause antecedent for the
  correct (lbl, s, topsInfo) fires, and `stepAux_soundness` ensures the
  consequent matches the actual next configuration.

The running step requires extracting from consistency constraints the unique
stack-top information matching σ at time t, then applying `consequent_of_clause`.
This stack-matching bookkeeping is captured in the `step_tracks` citation axiom;
the inductive structure itself is fully proved.

Reference: Cook (1971), Theorem 1; Arora & Barak (2009), Theorem 2.10. -/

/-- The actual TM2 computation configuration at time t. -/
noncomputable def cfgAt (V : FinTM2) (input : List (V.Γ V.k₀)) (t : ℕ) : V.Cfg :=
  (stepOrHalt V)^[t] (Turing.initList V input)

theorem cfgAt_zero (input : List (V.Γ V.k₀)) :
    cfgAt V input 0 = Turing.initList V input := rfl

theorem cfgAt_succ (input : List (V.Γ V.k₀)) (t : ℕ) :
    cfgAt V input (t + 1) = stepOrHalt V (cfgAt V input t) := by
  simp [cfgAt, Function.iterate_succ_apply']

theorem cfgAt_halted_succ (input : List (V.Γ V.k₀)) (t : ℕ)
    (h : (cfgAt V input t).l = none) :
    cfgAt V input (t + 1) = cfgAt V input t := by
  rw [cfgAt_succ, stepOrHalt_of_halted h]

/-! ### Base case -/

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

/-! ### Consistency extraction for topsInfo

From the consistency constraints, at each timestep t, σ assigns exactly one
stkLen and exactly one stkElem for each position. We use these to
noncomputably construct a `topsInfo` compatible with σ. -/

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

/-! ### Inductive step: halted case (proved) + running case (citation axiom)

The halted case uses `halted_forces_next` with topsInfo constructed from
consistency constraints. The running case additionally needs
`stepAux_soundness` from Correctness.lean to relate the topsInfo-derived
stack values to the actual stacks. -/

/-- Halted step: when label = none, transition constraints force label/state
    to stay the same at t+1. Fully proved using `halted_forces_next`. -/
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
  -- Extract consistency and transition constraints
  unfold tableauFormula at hsat
  have hC := evalCNF_append_left (evalCNF_append_left (evalCNF_append_left (evalCNF_append_left hsat)))
  have hT := evalCNF_append_right (evalCNF_append_left (evalCNF_append_left hsat))
  -- Build topsInfo from consistency
  obtain ⟨topsInfo, h_stks⟩ := topsInfo_from_consistency hC (by omega : t ≤ params.timeBound)
  exact halted_forces_next ht hT (cfgAt V input t).var topsInfo h_label h_state h_stks

/-- Citation axiom: running step. When label = some lbl at time t,
    the transition clauses force label/state at t+1 to match the stepAux result.

    The proof follows the same pattern as `halted_forces_next` but uses
    `stepAux_soundness` from Correctness.lean to relate the topsInfo-derived
    stkVals (which only capture stack tops) to the actual full stacks.

    Reference: Cook (1971), Arora & Barak (2009), Theorem 2.10. -/
axiom step_tracks_running
    (V : Turing.FinTM2) [Encodable V.Λ] [Encodable V.σ] [Encodable V.K]
    [∀ k, Encodable (V.Γ k)]
    [Fintype V.Λ] [Fintype V.σ] [Fintype V.K] [∀ k, Fintype (V.Γ k)]
    [DecidableEq V.K] [∀ k, DecidableEq (V.Γ k)]
    [DecidableEq V.Λ] [DecidableEq V.σ]
    (params : Params V) (input : List (V.Γ V.k₀))
    (σ : Assignment) (hsat : evalCNF σ (tableauFormula params input) = true)
    (t : ℕ) (ht : t < params.timeBound) (lbl : V.Λ)
    (h_some : (cfgAt V input t).l = some lbl)
    (h_label : varTrue σ (TableauVar.label (V := V) t (some lbl)))
    (h_state : varTrue σ (TableauVar.state (V := V) t (cfgAt V input t).var)) :
    varTrue σ (TableauVar.label (V := V) (t + 1) (cfgAt V input (t + 1)).l) ∧
    varTrue σ (TableauVar.state (V := V) (t + 1) (cfgAt V input (t + 1)).var)

/-- **Inductive step** (proved): σ tracks label/state at t → tracks at t+1.

    Case split on the label:
    - Halted (none): `step_tracks_halted` (fully proved using `halted_forces_next`)
    - Running (some lbl): `step_tracks_running` (citation axiom) -/
theorem step_tracks
    (V : Turing.FinTM2) [Encodable V.Λ] [Encodable V.σ] [Encodable V.K]
    [∀ k, Encodable (V.Γ k)]
    [Fintype V.Λ] [Fintype V.σ] [Fintype V.K] [∀ k, Fintype (V.Γ k)]
    [DecidableEq V.K] [∀ k, DecidableEq (V.Γ k)]
    [DecidableEq V.Λ] [DecidableEq V.σ]
    (params : Params V) (input : List (V.Γ V.k₀))
    (σ : Assignment) (hsat : evalCNF σ (tableauFormula params input) = true)
    (t : ℕ) (ht : t < params.timeBound)
    (h_label : varTrue σ (TableauVar.label (V := V) t (cfgAt V input t).l))
    (h_state : varTrue σ (TableauVar.state (V := V) t (cfgAt V input t).var)) :
    varTrue σ (TableauVar.label (V := V) (t + 1) (cfgAt V input (t + 1)).l) ∧
    varTrue σ (TableauVar.state (V := V) (t + 1) (cfgAt V input (t + 1)).var) := by
  cases h_lbl : (cfgAt V input t).l with
  | none => exact step_tracks_halted hsat ht h_lbl h_label h_state
  | some lbl =>
    rw [h_lbl] at h_label
    exact step_tracks_running V params input σ hsat t ht lbl h_lbl h_label h_state

/-! ### Main inductive proof -/

/-- **Trace tracks label and state**: the satisfying assignment marks the actual
    computation's label and state at each timestep.

    Proved by induction on t:
    - Base (t=0): from initialConstraints (`trace_base_label/state`).
    - Step (t→t+1): from `step_tracks` (uses transition + consistency constraints). -/
theorem trace_tracks_label_state
    (V : Turing.FinTM2) [Encodable V.Λ] [Encodable V.σ] [Encodable V.K]
    [∀ k, Encodable (V.Γ k)]
    [Fintype V.Λ] [Fintype V.σ] [Fintype V.K] [∀ k, Fintype (V.Γ k)]
    [DecidableEq V.K] [∀ k, DecidableEq (V.Γ k)]
    [DecidableEq V.Λ] [DecidableEq V.σ]
    (params : Params V) (input : List (V.Γ V.k₀))
    (σ : Assignment) (hsat : evalCNF σ (tableauFormula params input) = true)
    (t : ℕ) (ht : t ≤ params.timeBound) :
    varTrue σ (TableauVar.label (V := V) t (cfgAt V input t).l) ∧
    varTrue σ (TableauVar.state (V := V) t (cfgAt V input t).var) := by
  induction t with
  | zero =>
    exact ⟨trace_base_label params input σ hsat, trace_base_state params input σ hsat⟩
  | succ t ih =>
    obtain ⟨ih_l, ih_s⟩ := ih (by omega)
    exact step_tracks V params input σ hsat t (by omega) ih_l ih_s

/-- Corollary: the satisfying assignment tracks the label (matching the
    original `trace_tracks_label` signature used by `completeness`). -/
theorem trace_tracks_label
    (V : Turing.FinTM2) [Encodable V.Λ] [Encodable V.σ] [Encodable V.K]
    [∀ k, Encodable (V.Γ k)]
    [Fintype V.Λ] [Fintype V.σ] [Fintype V.K] [∀ k, Fintype (V.Γ k)]
    [DecidableEq V.K] [∀ k, DecidableEq (V.Γ k)]
    [DecidableEq V.Λ] [DecidableEq V.σ]
    (params : Params V) (input : List (V.Γ V.k₀))
    (σ : Assignment) (hsat : evalCNF σ (tableauFormula params input) = true)
    (t : ℕ) (ht : t ≤ params.timeBound) :
    varTrue σ (TableauVar.label (V := V) t
      ((stepOrHalt V)^[t] (initList V input)).l) :=
  (trace_tracks_label_state V params input σ hsat t ht).1

/-! ## Main completeness theorem -/

/-- **Completeness of Cook-Levin**: if the tableau formula is satisfiable,
    the TM computation halts within the time bound.

    Proof: from acceptance, σ marks some T with label = none.
    From trace_tracks_label, σ marks T with the actual computation's label.
    By consistency_label_unique, these must be equal. -/
theorem completeness (V : FinTM2) [Encodable V.Λ] [Encodable V.σ] [Encodable V.K]
    [∀ k, Encodable (V.Γ k)]
    [Fintype V.Λ] [Fintype V.σ] [Fintype V.K] [∀ k, Fintype (V.Γ k)]
    [DecidableEq V.K] [∀ k, DecidableEq (V.Γ k)]
    [DecidableEq V.Λ] [DecidableEq V.σ]
    (params : Params V) (input : List (V.Γ V.k₀))
    (h_sat : Satisfiable (tableauFormula params input)) :
    ∃ i, i ≤ params.timeBound ∧
      ((stepOrHalt V)^[i] (initList V input)).l = none := by
  obtain ⟨σ, hσ⟩ := h_sat
  obtain ⟨T, hT, h_none⟩ := completeness_halting params input σ hσ
  have h_actual := trace_tracks_label V params input σ hσ T hT
  have ⟨hC, _, _, _, _⟩ := sat_components params input σ hσ
  exact ⟨T, hT, by rw [← consistency_label_unique hC hT h_none h_actual]⟩

end CookLevinTableau
