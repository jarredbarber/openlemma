/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Cert-aware Cook-Levin tableau.

The base `tableauFormula params inputContents` fixes the ENTIRE input tape `k₀`
to a constant list, yielding a P-style equivalence
  `Satisfiable (tableauFormula params input) ↔ V halts on input`.
For NP-hardness we need the certificate bits to be FREE propositional variables:
  `Satisfiable (tableauFormulaCert params aInput certBound boolSyms)
     ↔ ∃ cert (bools), V halts on (aInput ++ cert)`.

This file defines `initialConstraintsCert` / `tableauFormulaCert` and proves the
"completeness of the reduction" direction (`reduction_sound_cert`: a real halting
computation on `(aInput ++ cert)` makes the cert-aware formula satisfiable),
reusing `satisfies_consistency / transition / frame / acceptance` verbatim.
Only `satisfies_initial_cert` is new: the initial constraint now fixes the
`a`-region (bottom of stack) while leaving the `cert`-region (top of stack) free
apart from a boolean-typing restriction.

Stack layout (`traceValuation` uses `stk.reverse[j]`, i.e. index `j` from the TOP):
for input stack `aInput ++ certMapped`,
  - positions `0 .. certBound-1` (top)         = `certMapped` (free cert bits),
  - positions `certBound .. certBound+|a|-1`   = `aInput`     (fixed input).
-/
import botlib.Complexity.CookLevin.Tableau
import botlib.Complexity.CookLevin.Correctness
import botlib.Complexity.CookLevin.Soundness
import botlib.Complexity.CookLevin.Completeness
import Mathlib.Data.Fintype.Basic

namespace CookLevinTableau

open Turing List OpenLemma.Complexity.SAT Encodable

variable {V : FinTM2} [Encodable V.Λ] [Encodable V.σ] [Encodable V.K] [∀ k, Encodable (V.Γ k)]
  [Fintype V.Λ] [Fintype V.σ] [Fintype V.K] [∀ k, Fintype (V.Γ k)]
  [DecidableEq V.Λ] [DecidableEq V.σ] [DecidableEq V.K] [∀ k, DecidableEq (V.Γ k)]
  [∀ k, Nonempty (V.Γ k)]

/-! ## Cert-aware initial constraints -/

/-- Initial constraints with a fixed `a`-region (bottom of `k₀`) and a free
    `cert`-region (top of `k₀`) restricted to boolean symbols `boolSyms`.
    `aInput` is the already-`V.Γ`-mapped encoding of the instance;
    `certBound` is the exact certificate length;
    `boolSyms` is the set of tape symbols representing cert bits. -/
noncomputable def initialConstraintsCert (params : Params V) (aInput : List (V.Γ V.k₀))
    (certBound : ℕ) (boolSyms : Finset (V.Γ V.k₀)) : CNF :=
  [[tLit V (TableauVar.label 0 (some V.main)) true]] ++
  [[tLit V (TableauVar.state 0 V.initialState) true]] ++
  [[tLit V (TableauVar.stkLen 0 V.k₀ (aInput.length + certBound)) true]] ++
  -- a-region (bottom): position `certBound + j` from top fixed to `aInput.reverse[j]`
  (aInput.reverse.zipIdx.map (fun ⟨γ, j⟩ =>
    [tLit V (TableauVar.stkElem 0 V.k₀ (certBound + j) γ) true])) ++
  -- cert-region (top): position `j` from top must be a boolean symbol
  ((List.range certBound).flatMap (fun j =>
    ((Finset.univ : Finset (V.Γ V.k₀)) \ boolSyms).toList.map
      (fun γ => [tLit V (TableauVar.stkElem 0 V.k₀ j γ) false]))) ++
  -- other stacks empty at t=0
  (Finset.univ.toList.flatMap (fun k =>
    if k = V.k₀ then [] else [[tLit V (TableauVar.stkLen 0 k 0) true]]))

/-- Full cert-aware tableau formula. -/
noncomputable def tableauFormulaCert (params : Params V) (aInput : List (V.Γ V.k₀))
    (certBound : ℕ) (boolSyms : Finset (V.Γ V.k₀)) : CNF :=
  consistencyConstraints params ++ initialConstraintsCert params aInput certBound boolSyms ++
  transitionConstraints params ++ framePreservation params ++ acceptanceConstraints params

/-! ## The trace satisfies the cert-aware initial constraints -/

/-- A computation whose `t=0` configuration has `aInput ++ certMapped` on `k₀`
    (cert at the top, all cert cells in `boolSyms`, `|certMapped| = certBound`)
    satisfies `initialConstraintsCert`. -/
theorem satisfies_initial_cert (params : Params V) (aInput : List (V.Γ V.k₀))
    (certBound : ℕ) (boolSyms : Finset (V.Γ V.k₀)) (certMapped : List (V.Γ V.k₀))
    (hcertlen : certMapped.length = certBound)
    (hcertbool : ∀ γ ∈ certMapped, γ ∈ boolSyms)
    (c : ℕ → V.Cfg)
    (h_init : c 0 = { l := some V.main, var := V.initialState,
                       stk := fun k => if h : k = V.k₀ then h ▸ (aInput ++ certMapped) else [] }) :
    evalCNF (traceAssignment c) (initialConstraintsCert params aInput certBound boolSyms) = true := by
  -- Local facts about the t=0 input stack.
  have hstk : (c 0).stk V.k₀ = aInput ++ certMapped := by rw [h_init]; simp
  have hlen : (aInput ++ certMapped).length = aInput.length + certBound := by
    rw [List.length_append, hcertlen]
  -- Parts 1,2,3: single positive unit clauses on label / state / stkLen.
  have p1 : evalCNF (traceAssignment c) [[tLit V (TableauVar.label 0 (some V.main)) true]] = true := by
    have : traceValuation c (TableauVar.label 0 (some V.main)) = true := by
      simp [traceValuation, h_init]
    simp [evalCNF, evalClause, evalTLit_trace, this]
  have p2 : evalCNF (traceAssignment c) [[tLit V (TableauVar.state 0 V.initialState) true]] = true := by
    have : traceValuation c (TableauVar.state 0 V.initialState) = true := by
      simp [traceValuation, h_init]
    simp [evalCNF, evalClause, evalTLit_trace, this]
  have p3 : evalCNF (traceAssignment c)
      [[tLit V (TableauVar.stkLen 0 V.k₀ (aInput.length + certBound)) true]] = true := by
    have : traceValuation c (TableauVar.stkLen 0 V.k₀ (aInput.length + certBound)) = true := by
      simp [traceValuation, hstk, hlen]
    simp [evalCNF, evalClause, evalTLit_trace, this]
  -- Part 4: a-region (bottom of stack): position `certBound + j` fixed to `aInput.reverse[j]`.
  have p4 : evalCNF (traceAssignment c)
      (aInput.reverse.zipIdx.map (fun ⟨γ, j⟩ =>
        [tLit V (TableauVar.stkElem 0 V.k₀ (certBound + j) γ) true])) = true := by
    simp only [evalCNF, List.all_eq_true, List.mem_map]
    rintro cl ⟨p, hp, hcl⟩
    obtain ⟨γ, j⟩ := p
    subst hcl
    have hzip := List.mem_zipIdx hp
    have hjrev : j < aInput.reverse.length := by omega
    have hj : j < aInput.length := by rwa [List.length_reverse] at hjrev
    have hγ : γ = aInput.reverse[j]'hjrev := hzip.2.2
    simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false]
    rw [evalTLit_trace, if_pos rfl]
    -- Goal: traceValuation c (stkElem 0 k₀ (certBound+j) γ) = true
    have key : traceValuation c (TableauVar.stkElem 0 V.k₀ (certBound + j) γ) = true := by
      have hcell : (aInput ++ certMapped).reverse[certBound + j]? = some γ := by
        rw [List.reverse_append, getElem?_append_right]
        · rw [show (certBound + j) - certMapped.reverse.length = j from by
              rw [List.length_reverse, hcertlen]; omega]
          have := List.getElem?_eq_getElem hjrev
          rw [this, ← hγ]
        · rw [List.length_reverse, hcertlen]; omega
      simp only [traceValuation, hstk, List.length_append, hcertlen,
        dif_pos (by omega : certBound + j < aInput.length + certBound),
        List.get_eq_getElem?]
      -- Goal: decide ((aInput ++ certMapped).reverse[⟨certBound+j, ⋯⟩]?.get ⋯ = γ) = true
      -- Full `simp` reduces the Fin-indexed `getElem?` to the ℕ-indexed form (via the
      -- GetElem? instance / `Fin.val`), then `hcell` + `Option.get_some` close it.
      simp [hcell, Option.get_some, List.getElem_append_right, hγ,
        List.length_reverse, hcertlen, Nat.add_sub_cancel_left]
    exact key
  -- Part 5: cert-region (top of stack): position `j` must be a boolean symbol.
  have p5 : evalCNF (traceAssignment c)
      ((List.range certBound).flatMap (fun j =>
        ((Finset.univ : Finset (V.Γ V.k₀)) \ boolSyms).toList.map
          (fun γ => [tLit V (TableauVar.stkElem 0 V.k₀ j γ) false]))) = true := by
    simp only [evalCNF, List.all_eq_true, List.mem_flatMap]
    rintro cl ⟨j, hj_mem, hcl_mem⟩
    rw [List.mem_range] at hj_mem
    simp only [List.mem_map, Finset.mem_toList] at hcl_mem
    obtain ⟨γ, hγ_mem, hcl⟩ := hcl_mem
    subst hcl
    have hγnot : γ ∉ boolSyms := (Finset.mem_sdiff.mp hγ_mem).2
    have hj' : j < certMapped.reverse.length := by
      rw [List.length_reverse, hcertlen]; exact hj_mem
    have hcell : (aInput ++ certMapped).reverse[j]? = some (certMapped.reverse[j]'hj') := by
      rw [List.reverse_append, getElem?_append_left hj', List.getElem?_eq_getElem hj']
    have hmem : (certMapped.reverse[j]'hj') ∈ boolSyms := by
      have : (certMapped.reverse[j]'hj') ∈ certMapped.reverse := List.getElem_mem hj'
      rw [List.mem_reverse] at this
      exact hcertbool _ this
    have hne : (certMapped.reverse[j]'hj') ≠ γ := fun heq => hγnot (heq ▸ hmem)
    have key : traceValuation c (TableauVar.stkElem 0 V.k₀ j γ) = false := by
      simp [traceValuation, hstk, hcell, hne, hj', List.length_append, hcertlen,
        List.get_eq_getElem?, Option.get_some, List.getElem_append_left,
        List.length_reverse, dif_pos (by omega : j < aInput.length + certBound)]
      intro h
      rw [List.getElem_append_left hj'] at h
      exact hne h
    simp [evalClause, List.any_cons, List.any_nil, Bool.or_false, evalTLit_trace, key]
  -- Part 6: other stacks empty at t=0.
  have p6 : evalCNF (traceAssignment c)
      (Finset.univ.toList.flatMap (fun k =>
        if k = V.k₀ then [] else [[tLit V (TableauVar.stkLen 0 k 0) true]])) = true := by
    simp only [evalCNF, List.all_eq_true, List.mem_flatMap,
      Finset.mem_toList, Finset.mem_univ, true_and]
    rintro cl ⟨k, hk_cl⟩
    by_cases hk : k = V.k₀
    · simp [hk] at hk_cl
    · simp only [hk, if_false, List.mem_singleton] at hk_cl
      rw [hk_cl]
      have : traceValuation c (TableauVar.stkLen 0 k 0) = true := by
        simp [traceValuation, h_init, hk]
      simp [evalCNF, evalClause, evalTLit_trace, this]
  unfold initialConstraintsCert
  rw [evalCNF_append, evalCNF_append, evalCNF_append, evalCNF_append, evalCNF_append]
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨p1, p2⟩, p3⟩, p4⟩, p5⟩, p6⟩

/-! ## Completeness of the reduction (trace → satisfiable) -/

/-- If `V` halts within `params.timeBound` on input `aInput ++ certMapped`
    (with `certMapped` a valid boolean certificate), then the cert-aware tableau
    formula is satisfiable. The satisfying assignment is `traceAssignment c`.
    Reuses `satisfies_consistency / transition / frame / acceptance` verbatim. -/
theorem reduction_sound_cert (params : Params V) (aInput : List (V.Γ V.k₀))
    (certBound : ℕ) (boolSyms : Finset (V.Γ V.k₀)) (certMapped : List (V.Γ V.k₀))
    (hcertlen : certMapped.length = certBound)
    (hcertbool : ∀ γ ∈ certMapped, γ ∈ boolSyms)
    (c : ℕ → V.Cfg)
    (h_init : c 0 = { l := some V.main, var := V.initialState,
                       stk := fun k => if h : k = V.k₀ then h ▸ (aInput ++ certMapped) else [] })
    (h_step : ∀ i < params.timeBound, c (i + 1) = (V.step (c i)).getD (c i))
    (h_depth : ∀ i ≤ params.timeBound, ∀ k, ((c i).stk k).length ≤ params.maxStackDepth)
    (h_halt : ∃ i ≤ params.timeBound, (c i).l = none)
    (hBRD : BoundedReadDepth V) :
    Satisfiable (tableauFormulaCert params aInput certBound boolSyms) := by
  -- The whole formula is satisfied by `traceAssignment c`: consistency,
  -- initial-cert, transition, frame, acceptance all hold for this trace.
  have hinit := satisfies_initial_cert params aInput certBound boolSyms certMapped
    hcertlen hcertbool c h_init
  have hfull : evalCNF (traceAssignment c)
      (tableauFormulaCert params aInput certBound boolSyms) = true := by
    unfold tableauFormulaCert
    rw [evalCNF_append, evalCNF_append, evalCNF_append, evalCNF_append]
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨⟨satisfies_consistency params c h_depth, hinit⟩,
           satisfies_transition params c h_step hBRD⟩,
          satisfies_frame params c h_step⟩,
        satisfies_acceptance params c h_halt⟩
  exact ⟨traceAssignment c, hfull⟩

end CookLevinTableau