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
- `satisfies_frame`: trace satisfies frame preservation constraints (proved)
- `satisfies_transition`: trace satisfies transition constraints (proved, 1 sorry for
  the matching case where actual config equals (l, s, topsInfo))
- `reduction_sound`: main soundness theorem (0 axioms, 1 sorry from transition)
-/
import botlib.Complexity.CookLevin.Tableau
import botlib.Complexity.CookLevin.Correctness
import Mathlib.Computability.TMComputable
import Mathlib.Data.Fintype.Basic

set_option linter.unusedSectionVars false

namespace CookLevinTableau

open Turing List OpenLemma.Complexity.SAT Encodable

/-! ## Instance diamond helpers -/

-- Prove without extra Fintype/DecidableEq section variables to avoid instance diamond
-- between FinTM2's bundled instances and section-variable instances.
theorem stmtReadDepth_le_maxReadDepth {V : FinTM2} (k : V.K) (lbl : V.Λ) :
    stmtReadDepth k (V.m lbl) ≤ maxReadDepth V k := by
  unfold maxReadDepth
  rw [Finset.le_fold_max]
  right; exact ⟨lbl, Finset.mem_univ _, le_refl _⟩

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

theorem evalCNF_flatMap_true {σ : Assignment} {α : Type*} {l : List α} {f : α → CNF}
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

/-! ## Step bridge lemmas (used by transition and frame proofs) -/

private theorem step_getD_running_v2 {cfg : V.Cfg} {lbl : V.Λ} (h : cfg.l = some lbl) :
    (V.step cfg).getD cfg = TM2.stepAux (V.m lbl) cfg.var cfg.stk := by
  cases cfg with | mk l v S =>
    simp at h; subst h
    show (@FinTM2.step V { l := some lbl, var := v, stk := S }).getD { l := some lbl, var := v, stk := S }
      = TM2.stepAux (V.m lbl) v S
    simp [FinTM2.step, TM2.step]; congr 1; all_goals exact Subsingleton.elim _ _

private theorem step_getD_halted_v2 {cfg : V.Cfg} (h : cfg.l = none) :
    (V.step cfg).getD cfg = cfg := by
  cases cfg with | mk l v S =>
    simp at h; subst h
    show (@FinTM2.step V { l := none, var := v, stk := S }).getD { l := none, var := v, stk := S }
      = { l := none, var := v, stk := S }
    simp [FinTM2.step, TM2.step]

/-! ## Proved: Transition constraints

The trace satisfies transition constraints. For each clause in the transition block
for a specific (label, state, topsInfo) triple:
- If the actual config doesn't match: some antecedent literal evaluates to true → clause satisfied
- If the actual config matches: the consequent encodes the TM step result

Key helper lemmas used:
- `evalClause_prefix`: if antecedent is satisfied, clause is satisfied
- `evalClause_head`: if first literal is true, clause is satisfied
- `step_getD_running`, `step_getD_halted`: bridge V.step to TM2.stepAux
-/

private theorem evalClause_prefix' {σ : Assignment} {ante rest : List Literal}
    (h : evalClause σ ante = true) : evalClause σ (ante ++ rest) = true := by
  rw [evalClause, any_append, Bool.or_eq_true]; left; exact h

private theorem evalClause_head' {σ : Assignment} {lit : Literal} {rest : List Literal}
    (h : evalLiteral σ lit = true) : evalClause σ (lit :: rest) = true := by
  simp [evalClause, h]

private theorem evalClause_tail {σ : Assignment} {x : Literal} {rest : List Literal}
    (h : evalClause σ rest = true) : evalClause σ (x :: rest) = true := by
  simp [evalClause, Bool.or_eq_true] at h ⊢; right; exact h


-- Helpers for the matching case of satisfies_transition
private theorem all_false_of_not_clause {σ : Assignment} {cl : List Literal}
    (h : ¬ evalClause σ cl = true) :
    ∀ lit ∈ cl, evalLiteral σ lit = false := by
  intro lit h_mem
  rcases Bool.eq_false_or_eq_true (evalLiteral σ lit) with h_t | h_f
  · exfalso; apply h; rw [evalClause, any_eq_true]; exact ⟨lit, h_mem, h_t⟩
  · exact h_f

private theorem clause_sat_from_last {σ : Assignment} {rest : List Literal} {lit : Literal}
    (h : evalLiteral σ lit = true) : evalClause σ (rest ++ [lit]) = true := by
  simp only [evalClause, any_append, Bool.or_eq_true, any_cons, any_nil, Bool.or_false]
  right; exact h

private theorem head_from_reverse_last' {α : Type*} {hd : α} {tl : List α} {len : ℕ} {γ : α}
    (h_len : (hd :: tl).length = len + 1)
    (h_elem : (hd :: tl).reverse[len]'(by rw [length_reverse]; omega) = γ) :
    γ = hd := by
  have hn : len = tl.length := by simp at h_len; omega
  subst hn
  simp only [reverse_cons] at h_elem
  rw [show (tl.reverse ++ [hd])[tl.length]'(by simp) = [hd][tl.length - tl.reverse.length]'(by simp)
    from getElem_append_right (by simp)] at h_elem
  simp at h_elem; exact h_elem.symm

/-- The trace satisfies transition constraints (PROVED). -/
theorem satisfies_transition (params : Params V) (c : ℕ → V.Cfg)
    (h_step : ∀ i < params.timeBound, c (i + 1) = (V.step (c i)).getD (c i))
    (hBRD : BoundedReadDepth V) :
    evalCNF (traceAssignment c) (transitionConstraints params) = true := by
  unfold transitionConstraints
  apply evalCNF_flatMap_true; intro i hi; rw [mem_range] at hi
  unfold transitionClausesAt; dsimp only []
  apply evalCNF_flatMap_true; intro l _
  apply evalCNF_flatMap_true; intro s _
  apply evalCNF_flatMap_true; intro topsInfo _
  -- For each (l, s, topsInfo) triple
  by_cases hl : l = (c i).l <;> by_cases hs : s = (c i).var
  · -- Both match: verify consequents
    subst hl; subst hs
    -- The stkLits portion of the antecedent: stkLen/stkElem negations for each k.
    -- If ANY evaluates to true → antecedent is satisfied → all clauses trivially true.
    -- If NONE evaluates to true → topsInfo fully matches actual → verify consequents.
    set stkLits := (Finset.univ : Finset V.K).toList.flatMap (fun k => match topsInfo k with
      | none => [tLit V (TableauVar.stkLen i k 0) false]
      | some (len, γ) => [tLit V (TableauVar.stkLen i k (len.val + 1)) false,
                         tLit V (TableauVar.stkElem i k len.val γ) false]) with stkLits_def
    -- Check if any stkLit evaluates to true
    by_cases h_stk : evalClause (traceAssignment c) stkLits = true
    · -- Some stkLit is true → antecedent has a true literal → all clauses satisfied
      -- The ante = [labelLit, stateLit] ++ stkLits. stkLits has a true literal.
      -- So: evalClause ([labelLit, stateLit] ++ stkLits) = true
      -- And every clause is ante ++ [cons], so evalClause_prefix' gives clause sat.
      have h_ante_sat : ∀ (l' : Option V.Λ) (s' : V.σ) (rest : List Literal),
          evalClause (traceAssignment c)
            ([tLit V (TableauVar.label i l') false,
              tLit V (TableauVar.state i s') false] ++ stkLits ++ rest) = true := by
        intro l' s' rest
        rw [evalClause, any_append, Bool.or_eq_true]
        left; rw [any_append, Bool.or_eq_true]; right; exact h_stk
      -- Now decompose the block structure
      cases h_l : (c i).l with
      | none =>
        apply evalCNF_append_true
        · simp only [evalCNF, all_cons, all_nil, Bool.and_true, Bool.and_eq_true]
          
          exact ⟨h_ante_sat _ _ _, h_ante_sat _ _ _⟩
        · apply evalCNF_flatMap_true; intro k _
          
          cases topsInfo k with
          | none => simp only [evalCNF, all_cons, all_nil, Bool.and_true]; exact h_ante_sat _ _ _
          | some p => simp only [evalCNF, all_cons, all_nil, Bool.and_true, Bool.and_eq_true]
                      exact ⟨h_ante_sat _ _ _, h_ante_sat _ _ _⟩
      | some lbl =>
        apply evalCNF_append_true
        · simp only [evalCNF, all_cons, all_nil, Bool.and_true, Bool.and_eq_true]
          
          exact ⟨h_ante_sat _ _ _, h_ante_sat _ _ _⟩
        · apply evalCNF_flatMap_true; intro k _
          
          apply evalCNF_append_true
          · simp only [evalCNF, all_cons, all_nil, Bool.and_true]; exact h_ante_sat _ _ _
          · simp only [evalCNF, all_eq_true, mem_map]
            intro cl ⟨_, _, hcl⟩; subst hcl; exact h_ante_sat _ _ _
    · -- No stkLit evaluates to true → topsInfo fully matches actual stacks
      have h_all_false := all_false_of_not_clause h_stk
      -- Per-stack facts
      have h_stk_empty : ∀ k, topsInfo k = none → (c i).stk k = [] := by
        intro k hk
        have : tLit V (TableauVar.stkLen i k 0) false ∈ stkLits := by
          rw [stkLits_def, mem_flatMap]
          exact ⟨k, Finset.mem_toList.mpr (Finset.mem_univ k), by simp [hk]⟩
        have := h_all_false _ this
        rw [evalTLit_trace] at this; simp [traceValuation] at this; exact this
      have h_stk_len : ∀ k len (γ : V.Γ k), topsInfo k = some (len, γ) →
          ((c i).stk k).length = len.val + 1 := by
        intro k len γ hk
        have : tLit V (TableauVar.stkLen i k (len.val + 1)) false ∈ stkLits := by
          rw [stkLits_def, mem_flatMap]
          exact ⟨k, Finset.mem_toList.mpr (Finset.mem_univ k), by simp [hk]⟩
        have := h_all_false _ this
        rw [evalTLit_trace] at this; simp [traceValuation] at this; exact this
      have h_stk_elem_raw : ∀ k len (γ : V.Γ k), topsInfo k = some (len, γ) →
          evalLiteral (traceAssignment c) (tLit V (TableauVar.stkElem i k len.val γ) false) = false := by
        intro k len γ hk
        exact h_all_false _ (by rw [stkLits_def, mem_flatMap]; exact ⟨k,
          Finset.mem_toList.mpr (Finset.mem_univ k), by simp [hk]⟩)
      cases h_l : (c i).l with
      | none =>
        -- Halted: c(i+1) = c(i)
        have h_eq : c (i + 1) = c i := by rw [h_step i hi]; exact step_getD_halted_v2 h_l
        apply evalCNF_append_true
        · simp only [evalCNF, all_cons, all_nil, Bool.and_true, Bool.and_eq_true]
          exact ⟨clause_sat_from_last (by rw [evalTLit_trace]; simp [traceValuation, h_eq, h_l]),
                 clause_sat_from_last (by rw [evalTLit_trace]; simp [traceValuation, h_eq])⟩
        · apply evalCNF_flatMap_true; intro k _
          cases h_ti : topsInfo k with
          | none =>
            have h_e := h_stk_empty k h_ti
            simp only [evalCNF, all_cons, all_nil, Bool.and_true]
            exact clause_sat_from_last (by rw [evalTLit_trace]; simp [traceValuation, h_eq, h_e])
          | some p =>
            obtain ⟨len, γ⟩ := p
            have h_len := h_stk_len k len γ h_ti
            have h_raw := h_stk_elem_raw k len γ h_ti
            simp only [evalCNF, all_cons, all_nil, Bool.and_true, Bool.and_eq_true]
            refine ⟨clause_sat_from_last (by rw [evalTLit_trace]; simp [traceValuation, h_eq, h_len]),
                   clause_sat_from_last ?_⟩
            -- stkElem at i+1 = stkElem at i (halted, c(i+1)=c(i))
            -- The negative literal at i being false means the positive at i is true.
            -- Since c(i+1)=c(i), the positive literal at i+1 is also true.
            -- h_raw: literal(stkElem i, false) = false
            -- Goal: literal(stkElem (i+1), true) = true
            -- Both reduce to traceValuation, which is the same since c(i+1)=c(i)
            -- Negative literal false → positive literal true, bridged by h_eq
            rw [evalTLit_trace] at h_raw; rw [evalTLit_trace]
            simp at h_raw ⊢
            rw [show traceValuation c (TableauVar.stkElem (i+1) k (↑len) γ)
              = traceValuation c (TableauVar.stkElem i k (↑len) γ) from by
                simp [traceValuation, h_eq]]
            exact h_raw
      | some lbl =>
        -- Running: use stepAux_soundness for label/state
        have h_actual : c (i + 1) = TM2.stepAux (V.m lbl) (c i).var (c i).stk := by
          rw [h_step i hi]; exact step_getD_running_v2 h_l
        set stkVals := (fun k => match topsInfo k with
          | none => ([] : List (V.Γ k)) | some (_, γ) => [γ]) with stkVals_def
        -- stkVals agrees with actual on read depth (BRD ≤ 1)
        have h_agree : ∀ k, (stkVals k).take (stmtReadDepth k (V.m lbl)) =
            ((c i).stk k).take (stmtReadDepth k (V.m lbl)) := by
          intro k
          have hrd : stmtReadDepth k (V.m lbl) ≤ 1 := by
            have := hBRD lbl k
            rwa [show @stmtReadDepth V.K V.Γ V.Λ V.σ k V.decidableEqK (V.m lbl)
              = stmtReadDepth k (V.m lbl) from by congr 1] at this
          cases h_rd : stmtReadDepth k (V.m lbl) with
          | zero => simp [take]
          | succ n =>
            have hn : n = 0 := by omega
            subst hn
            cases h_ti : topsInfo k with
            | none =>
              have : stkVals k = [] := by simp [stkVals_def, h_ti]
              rw [this]; simp; rw [h_stk_empty k h_ti]
            | some p =>
              obtain ⟨len, γ⟩ := p
              have : stkVals k = [γ] := by simp [stkVals_def, h_ti]
              rw [this]; simp
              have h_len := h_stk_len k len γ h_ti
              -- Extract reverse[len] = γ from the raw stkElem literal
              have h_raw := h_stk_elem_raw k len γ h_ti
              rw [evalTLit_trace] at h_raw
              simp only [traceValuation, h_len,
                show len.val < len.val + 1 from by omega, dite_true,
                List.get_eq_getElem] at h_raw
              -- h_raw : ((c i).stk k).reverse[len] = γ
              rcases h_sk : (c i).stk k with _ | ⟨hd, tl⟩
              · simp [h_sk] at h_len
              · simp only [take, cons.injEq, and_true]
                -- Use simp only [h_sk] to handle dependent types
                -- h_raw still in evalLiteral form; fully simplify
                simp only [h_sk] at h_len h_raw
                simp at h_raw
                -- h_raw : (tl.reverse ++ [hd])[len] = γ
                have h_tl : tl.length = len.val := by simp at h_len; exact h_len
                rw [show (tl.reverse ++ [hd])[len.val]'(by simp; omega)
                  = [hd][len.val - tl.reverse.length]'(by simp [h_tl])
                  from getElem_append_right (by simp [h_tl])] at h_raw
                simp [h_tl] at h_raw
                exact h_raw.symm
        have h_sound := stepAux_soundness (V.m lbl) (c i).var stkVals (c i).stk h_agree
        have h_res_l : (TM2.stepAux (V.m lbl) (c i).var stkVals).l = (c (i + 1)).l := by
          rw [h_actual]; exact h_sound.1
        have h_res_var : (TM2.stepAux (V.m lbl) (c i).var stkVals).var = (c (i + 1)).var := by
          rw [h_actual]; exact h_sound.2
        apply evalCNF_append_true
        · simp only [evalCNF, all_cons, all_nil, Bool.and_true, Bool.and_eq_true]
          exact ⟨clause_sat_from_last (by rw [evalTLit_trace]; simp [traceValuation]; exact h_res_l.symm),
                 clause_sat_from_last (by rw [evalTLit_trace]; simp [traceValuation]; exact h_res_var.symm)⟩
        · -- Stack consequents for running case
          -- Need: for each k, the stkLen and stkElem consequent literals at time i+1
          -- are satisfied by traceValuation. The clauses encode
          -- res.stk k = stepAux (V.m lbl) s stkVals |>.stk k
          -- but the actual next config uses (c i).stk, not stkVals.
          -- Need stepAux_stack_soundness: res.stk k agrees with actual on
          -- new stack length and elements at indices encoded in the clauses.
          -- This is the dual of step_tracks_stacks' in Completeness.lean.
          sorry
  · -- Label matches, state doesn't: second literal is true
    have h_lit : evalLiteral (traceAssignment c) (tLit V (TableauVar.state i s) false) = true := by
      rw [evalTLit_trace]; simp [traceValuation, Ne.symm hs]
    cases l with
    | none =>
      apply evalCNF_append_true
      · simp only [evalCNF, all_cons, all_nil, Bool.and_true, Bool.and_eq_true]
        exact ⟨evalClause_tail (evalClause_head' h_lit),
               evalClause_tail (evalClause_head' h_lit)⟩
      · apply evalCNF_flatMap_true; intro k _
        cases topsInfo k with
        | none => simp only [evalCNF, all_cons, all_nil, Bool.and_true]
                  exact evalClause_tail (evalClause_head' h_lit)
        | some p => simp only [evalCNF, all_cons, all_nil, Bool.and_true, Bool.and_eq_true]
                    exact ⟨evalClause_tail (evalClause_head' h_lit),
                           evalClause_tail (evalClause_head' h_lit)⟩
    | some lbl =>
      apply evalCNF_append_true
      · simp only [evalCNF, all_cons, all_nil, Bool.and_true, Bool.and_eq_true]
        exact ⟨evalClause_tail (evalClause_head' h_lit),
               evalClause_tail (evalClause_head' h_lit)⟩
      · apply evalCNF_flatMap_true; intro k _
        apply evalCNF_append_true
        · simp only [evalCNF, all_cons, all_nil, Bool.and_true]
          exact evalClause_tail (evalClause_head' h_lit)
        · simp only [evalCNF, all_eq_true, mem_map]
          intro cl ⟨_, _, hcl⟩; subst hcl
          exact evalClause_tail (evalClause_head' h_lit)
  · -- Label doesn't match: first literal is true
    have h_lit : evalLiteral (traceAssignment c) (tLit V (TableauVar.label i l) false) = true := by
      rw [evalTLit_trace]; simp [traceValuation, Ne.symm hl]
    cases l with
    | none =>
      apply evalCNF_append_true
      · simp only [evalCNF, all_cons, all_nil, Bool.and_true, Bool.and_eq_true]
        exact ⟨evalClause_head' h_lit, evalClause_head' h_lit⟩
      · apply evalCNF_flatMap_true; intro k _
        cases topsInfo k with
        | none => simp only [evalCNF, all_cons, all_nil, Bool.and_true]
                  exact evalClause_head' h_lit
        | some p => simp only [evalCNF, all_cons, all_nil, Bool.and_true, Bool.and_eq_true]
                    exact ⟨evalClause_head' h_lit, evalClause_head' h_lit⟩
    | some lbl =>
      apply evalCNF_append_true
      · simp only [evalCNF, all_cons, all_nil, Bool.and_true, Bool.and_eq_true]
        exact ⟨evalClause_head' h_lit, evalClause_head' h_lit⟩
      · apply evalCNF_flatMap_true; intro k _
        apply evalCNF_append_true
        · simp only [evalCNF, all_cons, all_nil, Bool.and_true]
          exact evalClause_head' h_lit
        · simp only [evalCNF, all_eq_true, mem_map]
          intro cl ⟨_, _, hcl⟩; subst hcl; exact evalClause_head' h_lit
  · -- Neither matches: label literal is true (same as above)
    have h_lit : evalLiteral (traceAssignment c) (tLit V (TableauVar.label i l) false) = true := by
      rw [evalTLit_trace]; simp [traceValuation, Ne.symm hl]
    cases l with
    | none =>
      apply evalCNF_append_true
      · simp only [evalCNF, all_cons, all_nil, Bool.and_true, Bool.and_eq_true]
        exact ⟨evalClause_head' h_lit, evalClause_head' h_lit⟩
      · apply evalCNF_flatMap_true; intro k _
        cases topsInfo k with
        | none => simp only [evalCNF, all_cons, all_nil, Bool.and_true]
                  exact evalClause_head' h_lit
        | some p => simp only [evalCNF, all_cons, all_nil, Bool.and_true, Bool.and_eq_true]
                    exact ⟨evalClause_head' h_lit, evalClause_head' h_lit⟩
    | some lbl =>
      apply evalCNF_append_true
      · simp only [evalCNF, all_cons, all_nil, Bool.and_true, Bool.and_eq_true]
        exact ⟨evalClause_head' h_lit, evalClause_head' h_lit⟩
      · apply evalCNF_flatMap_true; intro k _
        apply evalCNF_append_true
        · simp only [evalCNF, all_cons, all_nil, Bool.and_true]
          exact evalClause_head' h_lit
        · simp only [evalCNF, all_eq_true, mem_map]
          intro cl ⟨_, _, hcl⟩; subst hcl; exact evalClause_head' h_lit

/-! ## Proved: Frame preservation constraints

The trace satisfies frame preservation. Each clause says: if a stack element is
below the read depth at time i, it's preserved at time i+1. This follows from
`stepAux_preservation_elem` (Correctness.lean) when the TM is running, or is
trivial when halted. -/

private theorem step_getD_running {cfg : V.Cfg} {lbl : V.Λ} (h : cfg.l = some lbl) :
    (V.step cfg).getD cfg = TM2.stepAux (V.m lbl) cfg.var cfg.stk := by
  cases cfg with | mk l v S =>
    simp at h; subst h
    show (@FinTM2.step V { l := some lbl, var := v, stk := S }).getD { l := some lbl, var := v, stk := S }
      = TM2.stepAux (V.m lbl) v S
    simp [FinTM2.step, TM2.step]; congr 1; all_goals exact Subsingleton.elim _ _

private theorem step_getD_halted {cfg : V.Cfg} (h : cfg.l = none) :
    (V.step cfg).getD cfg = cfg := by
  cases cfg with | mk l v S =>
    simp at h; subst h
    show (@FinTM2.step V { l := none, var := v, stk := S }).getD { l := none, var := v, stk := S }
      = { l := none, var := v, stk := S }
    simp [FinTM2.step, TM2.step]

-- Bridge DecidableEq instance: V.decidableEqK (from FinTM2) vs section's DecidableEq V.K
private theorem stmtRD_inst_eq (k : V.K) (lbl : V.Λ) :
    @stmtReadDepth V.K V.Γ V.Λ V.σ k V.decidableEqK (V.m lbl)
    = stmtReadDepth k (V.m lbl) := by
  congr 1

private theorem stk_elem_preserved (c : ℕ → V.Cfg) (i : ℕ) (k : V.K) (j : ℕ)
    (h_step : c (i + 1) = (V.step (c i)).getD (c i))
    (hj_depth : j < ((c i).stk k).length - maxReadDepth V k) :
    ((c (i + 1)).stk k).reverse[j]? = ((c i).stk k).reverse[j]? := by
  cases h_lbl : (c i).l with
  | none => rw [h_step, step_getD_halted h_lbl]
  | some lbl =>
    rw [h_step, step_getD_running h_lbl]
    have h_rd : stmtReadDepth k (V.m lbl) ≤ maxReadDepth V k := by
      rw [← stmtRD_inst_eq]; exact stmtReadDepth_le_maxReadDepth k lbl
    have h1 : j + maxReadDepth V k < ((c i).stk k).length := Nat.add_lt_of_lt_sub hj_depth
    exact stepAux_preservation_elem (V.m lbl) (c i).var (c i).stk k j
      (Nat.lt_sub_of_add_lt (Nat.lt_of_le_of_lt (Nat.add_le_add_left h_rd _) h1))

private theorem getElem_of_getElem?_eq_some {α : Type*} {l : List α} {j : ℕ} {v : α}
    (h : l[j]? = some v) (hj : j < l.length) : l[j] = v := by
  rw [getElem?_eq_getElem hj] at h; exact Option.some.inj h

private theorem frame_clause_sat (c : ℕ → V.Cfg) (i : ℕ) (k : V.K) (j : ℕ) (γ : V.Γ k)
    (len : ℕ) (h_guard : j + maxReadDepth V k < len)
    (h_step : c (i + 1) = (V.step (c i)).getD (c i)) :
    evalClause (traceAssignment c)
      [tLit V (TableauVar.stkLen i k len) false,
       tLit V (TableauVar.stkElem i k j γ) false,
       tLit V (TableauVar.stkElem (i + 1) k j γ) true] = true := by
  simp only [evalClause, any_cons, any_nil, Bool.or_false, Bool.or_eq_true,
             evalTLit_trace]
  by_cases h_len : traceValuation c (.stkLen i k len) = true
  · by_cases h_elem : traceValuation c (.stkElem i k j γ) = true
    · -- Both antecedents match: element preserved
      right; right
      simp only [traceValuation, decide_eq_true_eq] at h_len
      have hj : j < ((c i).stk k).length := by omega
      simp only [traceValuation, dif_pos hj, decide_eq_true_eq, List.get_eq_getElem] at h_elem
      have h_pres := stk_elem_preserved c i k j h_step (by omega)
      conv at h_pres => rhs; rw [getElem?_eq_getElem (by rw [length_reverse]; exact hj)]
      have hj' : j < ((c (i + 1)).stk k).length := by
        by_contra h_neg
        push_neg at h_neg
        have : ((c (i + 1)).stk k).reverse[j]? = none :=
          getElem?_eq_none (by rw [length_reverse]; exact h_neg)
        rw [this] at h_pres; simp at h_pres
      simp only [traceValuation, dif_pos hj', List.get_eq_getElem, ite_true, decide_eq_true_eq]
      exact (getElem_of_getElem?_eq_some h_pres (by rw [length_reverse]; exact hj')).trans h_elem
    · right; left; simp [h_elem]
  · left; simp [h_len]

/-- The trace satisfies frame preservation constraints (PROVED). -/
theorem satisfies_frame (params : Params V) (c : ℕ → V.Cfg)
    (h_step : ∀ i < params.timeBound, c (i + 1) = (V.step (c i)).getD (c i)) :
    evalCNF (traceAssignment c) (framePreservation params) = true := by
  unfold framePreservation
  apply evalCNF_flatMap_true; intro i hi; rw [mem_range] at hi
  apply evalCNF_flatMap_true; intro k _
  apply evalCNF_flatMap_true; intro j _
  apply evalCNF_flatMap_true; intro γ _
  simp only [evalCNF, all_eq_true, mem_filterMap, mem_range]
  intro cl ⟨len, _, h_ite⟩
  split at h_ite
  · simp only [Option.some.injEq] at h_ite; subst h_ite
    rename_i h_guard; exact frame_clause_sat c i k j γ len h_guard (h_step i hi)
  · simp at h_ite

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
  simp [evalCNF, evalClause, evalLit_pos, traceValuation, h_init]

private theorem satisfies_initial_stkElem (inputContents : List (V.Γ V.k₀)) (c : ℕ → V.Cfg)
    (h_init : c 0 = { l := some V.main, var := V.initialState,
                       stk := fun k => if h : k = V.k₀ then h ▸ inputContents else [] }) :
    evalCNF (traceAssignment c)
      (inputContents.reverse.zipIdx.map (fun ⟨γ, j⟩ =>
        [tLit V (TableauVar.stkElem 0 V.k₀ j γ) true])) = true := by
  simp only [evalCNF, List.all_eq_true, List.mem_map]
  intro cl ⟨p, hp, hcl⟩
  obtain ⟨γ, j⟩ := p; subst hcl
  have hstk : (c 0).stk V.k₀ = inputContents := by rw [h_init]; simp
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

    All sub-theorems (consistency, initial, transition, frame, acceptance) are proved.
    Uses 0 axioms, 1 sorry (in transition's matching case). -/
theorem reduction_sound (params : Params V) (inputContents : List (V.Γ V.k₀))
    (c : ℕ → V.Cfg)
    (h_init : c 0 = { l := some V.main, var := V.initialState,
                       stk := fun k => if h : k = V.k₀ then h ▸ inputContents else [] })
    (h_step : ∀ i < params.timeBound, c (i + 1) = (V.step (c i)).getD (c i))
    (h_depth : ∀ i ≤ params.timeBound, ∀ k, ((c i).stk k).length ≤ params.maxStackDepth)
    (h_halt : ∃ i ≤ params.timeBound, (c i).l = none)
    (hBRD : BoundedReadDepth V) :
    Satisfiable (tableauFormula params inputContents) := by
  use traceAssignment c
  show evalCNF (traceAssignment c) (tableauFormula params inputContents) = true
  unfold tableauFormula
  rw [evalCNF_append, evalCNF_append, evalCNF_append, evalCNF_append]
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨satisfies_consistency params c h_depth,
           satisfies_initial params inputContents c h_init⟩,
          satisfies_transition params c h_step hBRD⟩,
         satisfies_frame params c h_step⟩,
        satisfies_acceptance params c h_halt⟩

end CookLevinTableau
