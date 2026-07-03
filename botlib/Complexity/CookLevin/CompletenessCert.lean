/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Completeness direction of the cert-aware Cook-Levin reduction:
if `tableauFormulaCert` is satisfiable, then there is a certificate `cert`
(whose cells are boolean symbols) such that the fixed-input
`tableauFormula params (aInput ++ cert)` is satisfiable. Combined with the
existing `completeness` theorem, this yields
  `Satisfiable (tableauFormulaCert params aInput certBound boolSyms) →
     ∃ cert, V halts on (aInput ++ cert) within params.timeBound`
(under the standard `h_adequate` precondition, supplied by the caller who
chose `params.maxStackDepth` from the verifier's polytime bound).

Strategy (reuses the existing completeness machinery, no new trace proofs):
  1. Split `tableauFormulaCert` into consistency / initialCert / transition /
     frame / acceptance (mechanical, like `sat_components`).
  2. From consistency (exactlyOne) extract, per cert cell `j < certBound`, a
     *unique* symbol `gj` with `varTrue σ (stkElem 0 k0 j gj)`
     (`consistency_stkElem_unique` for uniqueness; a new `exactlyOne_exists`
     for existence). The cert-region constraint of `initialConstraintsCert`
     forces every non-`boolSyms` symbol at cell `j` to be false, hence
     `gj ∈ boolSyms`.
  3. Build `cert := certCells.reverse` where `certCells[j] = gj`, so
     `cert.reverse[j] = gj`. Show `σ` satisfies
     `initialConstraints params (aInput ++ cert)`: the `a`-region and
     label/state/stkLen/other-stacks clauses are identical to the cert-aware
     version; the cert-region fixed clauses hold because `σ` makes `gj` true.
  4. Reassemble `evalCNF σ (tableauFormula params (aInput ++ cert)) = true`
     from the shared consistency/transition/frame/acceptance and the new
     initial, hence `Satisfiable (tableauFormula params (aInput ++ cert))`.
-/
import botlib.Complexity.CookLevin.Tableau
import botlib.Complexity.CookLevin.Correctness
import botlib.Complexity.CookLevin.Soundness
import botlib.Complexity.CookLevin.Completeness
import botlib.Complexity.CookLevin.CertTableau
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith

namespace CookLevinTableau

open Turing List OpenLemma.Complexity.SAT Encodable

variable {V : FinTM2} [Encodable V.Λ] [Encodable V.σ] [Encodable V.K] [∀ k, Encodable (V.Γ k)]
  [Fintype V.Λ] [Fintype V.σ] [Fintype V.K] [∀ k, Fintype (V.Γ k)]
  [DecidableEq V.Λ] [DecidableEq V.σ] [DecidableEq V.K] [∀ k, DecidableEq (V.Γ k)]
  [∀ k, Nonempty (V.Γ k)]

set_option maxHeartbeats 800000

/-! ## Existence side of `exactlyOne` (at least one true) -/

/-- From `evalCNF σ (exactlyOne V vars) = true` with `vars ≠ []`, some variable
    in `vars` is true under `σ`. (The first clause of `exactlyOne` is the
    disjunction of positive literals over `vars`.) -/
theorem exactlyOne_exists {σ : Assignment} {vars : List (TableauVar V)}
    (h : evalCNF σ (exactlyOne V vars) = true) (hne : vars ≠ []) :
    ∃ v ∈ vars, varTrue σ v := by
  unfold exactlyOne at h
  rw [evalCNF, List.all_cons, Bool.and_eq_true] at h
  obtain ⟨h1, _⟩ := h
  rw [evalClause, List.any_eq_true] at h1
  obtain ⟨lit, hl_mem, hl_eval⟩ := h1
  rw [List.mem_map] at hl_mem
  obtain ⟨v, hv, rfl⟩ := hl_mem
  refine ⟨v, hv, ?_⟩
  simp only [tLit, if_true, evalLiteral, varTrue] at hl_eval ⊢
  exact hl_eval

/-- From consistency: for every cell `(t, k, j)` with `j < maxStackDepth`,
    some symbol `γ` is true under `σ`. -/
theorem consistency_stkElem_exists {σ : Assignment} {params : Params V}
    (hC : evalCNF σ (consistencyConstraints params) = true)
    {t : ℕ} (ht : t ≤ params.timeBound) (k : V.K) (j : ℕ)
    (hj : j < params.maxStackDepth) :
    ∃ γ : V.Γ k, varTrue σ (TableauVar.stkElem (V := V) t k j γ) := by
  -- consistencyConstraints = labelBlock ++ stateBlock ++ stkElemBlock ++ stkLenBlock
  unfold consistencyConstraints at hC
  have hSE := evalCNF_append_right (evalCNF_append_left hC)
  have hI : t ∈ List.range (params.timeBound + 1) := List.mem_range.mpr (by omega)
  have hK : k ∈ (Finset.univ : Finset V.K).toList := Finset.mem_toList.mpr (Finset.mem_univ k)
  have hJ : j ∈ List.range params.maxStackDepth := List.mem_range.mpr hj
  have hBlock : evalCNF σ
      (exactlyOne V ((Finset.univ : Finset (V.Γ k)).toList.map
        (TableauVar.stkElem (V := V) t k j))) = true :=
    evalCNF_flatMap_mem (evalCNF_flatMap_mem (evalCNF_flatMap_mem hSE hI) hK) hJ
  have hne : ((Finset.univ : Finset (V.Γ k)).toList.map
      (TableauVar.stkElem (V := V) t k j)) ≠ [] := by
    obtain ⟨γ0⟩ : Nonempty (V.Γ k) := inferInstance
    have hγ0 : γ0 ∈ (Finset.univ : Finset (V.Γ k)).toList :=
      Finset.mem_toList.mpr (Finset.mem_univ _)
    exact List.ne_nil_of_mem (List.mem_map.mpr ⟨γ0, hγ0, rfl⟩)
  obtain ⟨v, hv_mem, hv_true⟩ := exactlyOne_exists hBlock hne
  rw [List.mem_map] at hv_mem
  obtain ⟨γ, hγ, rfl⟩ := hv_mem
  exact ⟨γ, hv_true⟩

/-! ## Splitting `tableauFormulaCert` into its components -/

private theorem sat_components_cert (params : Params V) (aInput : List (V.Γ V.k₀))
    (certBound : ℕ) (boolSyms : Finset (V.Γ V.k₀)) (σ : Assignment)
    (hsat : evalCNF σ (tableauFormulaCert params aInput certBound boolSyms) = true) :
    evalCNF σ (consistencyConstraints params) = true ∧
    evalCNF σ (initialConstraintsCert params aInput certBound boolSyms) = true ∧
    evalCNF σ (transitionConstraints params) = true ∧
    evalCNF σ (framePreservation params) = true ∧
    evalCNF σ (acceptanceConstraints params) = true := by
  unfold tableauFormulaCert at hsat
  exact ⟨evalCNF_append_left (evalCNF_append_left (evalCNF_append_left (evalCNF_append_left hsat))),
         evalCNF_append_right (evalCNF_append_left (evalCNF_append_left (evalCNF_append_left hsat))),
         evalCNF_append_right (evalCNF_append_left (evalCNF_append_left hsat)),
         evalCNF_append_right (evalCNF_append_left hsat),
         evalCNF_append_right hsat⟩

/-! ## The cert-region forces non-boolean symbols to be false -/

/-- From `initialConstraintsCert`, for every cert cell `j < certBound` and every
    symbol `γ ∉ boolSyms`, `σ` makes `stkElem 0 k₀ j γ` false. -/
theorem cert_not_bool_false (params : Params V) (aInput : List (V.Γ V.k₀))
    (certBound : ℕ) (boolSyms : Finset (V.Γ V.k₀)) (σ : Assignment)
    (hIC : evalCNF σ (initialConstraintsCert params aInput certBound boolSyms) = true)
    (j : ℕ) (hj : j < certBound) (γ : V.Γ V.k₀) (hγnot : γ ∉ boolSyms) :
    ¬ varTrue σ (TableauVar.stkElem (V := V) 0 V.k₀ j γ) := by
  -- cert-region is the 5th `++` block of `initialConstraintsCert`.
  have hCR : evalCNF σ
      ((List.range certBound).flatMap (fun j =>
        ((Finset.univ : Finset (V.Γ V.k₀)) \ boolSyms).toList.map
          (fun γ => [tLit V (TableauVar.stkElem 0 V.k₀ j γ) false]))) = true :=
    evalCNF_append_right (evalCNF_append_left hIC)
  have hj' : j ∈ List.range certBound := List.mem_range.mpr hj
  have hInner : evalCNF σ
      (((Finset.univ : Finset (V.Γ V.k₀)) \ boolSyms).toList.map
        (fun γ' => [tLit V (TableauVar.stkElem 0 V.k₀ j γ') false])) = true :=
    evalCNF_flatMap_mem hCR hj'
  have hγ'mem : γ ∈ (Finset.univ : Finset (V.Γ V.k₀)) \ boolSyms :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hγnot⟩
  have hγ' : γ ∈ ((Finset.univ : Finset (V.Γ V.k₀)) \ boolSyms).toList :=
    Finset.mem_toList.mpr hγ'mem
  have hAll : ∀ c ∈ ((Finset.univ : Finset (V.Γ V.k₀)) \ boolSyms).toList.map
      (fun γ' => [tLit V (TableauVar.stkElem (V := V) 0 V.k₀ j γ') false]),
      evalClause σ c = true := by
    rw [evalCNF, List.all_eq_true] at hInner; exact hInner
  have hcmem : [tLit V (TableauVar.stkElem (V := V) 0 V.k₀ j γ) false] ∈
      ((Finset.univ : Finset (V.Γ V.k₀)) \ boolSyms).toList.map
        (fun γ' => [tLit V (TableauVar.stkElem (V := V) 0 V.k₀ j γ') false]) :=
    List.mem_map.mpr ⟨γ, hγ', rfl⟩
  have hClauseEval : evalClause σ [tLit V (TableauVar.stkElem (V := V) 0 V.k₀ j γ) false] = true :=
    hAll _ hcmem
  have heq : tLit V (TableauVar.stkElem (V := V) 0 V.k₀ j γ) false =
      Literal.neg (Encodable.encode (TableauVar.stkElem (V := V) 0 V.k₀ j γ)) := by
    simp [tLit]
  rw [heq, evalClause, List.any_cons, List.any_nil, Bool.or_false, evalLiteral] at hClauseEval
  simp at hClauseEval
  intro hvt
  rw [varTrue] at hvt
  simp [hvt] at hClauseEval

end CookLevinTableau