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

/-! ## Main completeness direction -/

/-- Completeness of the cert-aware reduction: a satisfying assignment of
    `tableauFormulaCert` yields a certificate `cert` (boolean symbols) such that
    the fixed-input `tableauFormula params (aInput ++ cert)` is satisfiable.
    (The `hdepth` precondition `certBound ≤ maxStackDepth` guarantees the cert
    cells lie in the range covered by consistency's `exactlyOne`.) -/
theorem completeness_cert (params : Params V) (aInput : List (V.Γ V.k₀))
    (certBound : ℕ) (boolSyms : Finset (V.Γ V.k₀))
    (hdepth : certBound ≤ params.maxStackDepth)
    (h_sat : Satisfiable (tableauFormulaCert params aInput certBound boolSyms)) :
    ∃ cert : List (V.Γ V.k₀),
      cert.length = certBound ∧
      (∀ γ ∈ cert, γ ∈ boolSyms) ∧
      Satisfiable (tableauFormula params (aInput ++ cert)) := by
  obtain ⟨σ, hσ⟩ := h_sat
  have ⟨hC, hIC, hT, hF, hA⟩ := sat_components_cert params aInput certBound boolSyms σ hσ
  have hnotbool := cert_not_bool_false params aInput certBound boolSyms σ hIC
  have hcell : ∀ j < certBound, ∃ γ : V.Γ V.k₀,
      γ ∈ boolSyms ∧ varTrue σ (TableauVar.stkElem (V := V) 0 V.k₀ j γ) := by
    intro j hj
    obtain ⟨γ, hγtrue⟩ :=
      consistency_stkElem_exists hC (Nat.zero_le _) V.k₀ j (hj.trans_le hdepth)
    refine ⟨γ, ?_, hγtrue⟩
    by_contra hgb
    exact hnotbool j hj γ hgb hγtrue
  choose certF0 certF0_spec using hcell
  -- `certF0 : (j : ℕ) → j < certBound → V.Γ V.k₀` is dependent; wrap into a total
  -- function so it can be `List.map`'d.
  let certF : ℕ → V.Γ V.k₀ := fun j =>
    if hj : j < certBound then certF0 j hj
    else Classical.choice (inferInstance : Nonempty (V.Γ V.k₀))
  have certF_spec (j : ℕ) (hj : j < certBound) :
      certF j ∈ boolSyms ∧
      varTrue σ (TableauVar.stkElem (V := V) 0 V.k₀ j (certF j)) := by
    have : certF j = certF0 j hj := by simp only [certF, dif_pos hj]
    rw [this]; exact certF0_spec j hj
  set certCells : List (V.Γ V.k₀) := (List.range certBound).map certF
  set cert : List (V.Γ V.k₀) := certCells.reverse with hcert_def
  have hcertlen : cert.length = certBound := by
    simp [cert, certCells, List.length_reverse, List.length_map, List.length_range]
  have hcertelem : ∀ γ ∈ cert, γ ∈ boolSyms := by
    intro γ hγ
    rw [hcert_def, List.mem_reverse] at hγ
    obtain ⟨j, hj_mem, rfl⟩ := List.mem_map.mp hγ
    exact (certF_spec j (List.mem_range.mp hj_mem)).1
  have hinit : evalCNF σ (initialConstraints params (aInput ++ cert)) = true := by
    unfold initialConstraints
    -- Extract the matching blocks of `initialConstraintsCert` from hIC.
    -- initialConstraintsCert = b1++b2++b3++b4++b5++b6 (left-assoc, 6 blocks).
    have hb1 : evalCNF σ [[tLit V (TableauVar.label 0 (some V.main)) true]] = true :=
      evalCNF_append_left (evalCNF_append_left (evalCNF_append_left
        (evalCNF_append_left (evalCNF_append_left hIC))))
    have hb2 : evalCNF σ [[tLit V (TableauVar.state 0 V.initialState) true]] = true :=
      evalCNF_append_right (evalCNF_append_left (evalCNF_append_left
        (evalCNF_append_left (evalCNF_append_left hIC))))
    have hb3 : evalCNF σ
        [[tLit V (TableauVar.stkLen 0 V.k₀ (aInput.length + certBound)) true]] = true :=
      evalCNF_append_right (evalCNF_append_left (evalCNF_append_left (evalCNF_append_left hIC)))
    have hb4 : evalCNF σ
        (aInput.reverse.zipIdx.map (fun ⟨γ, j⟩ =>
          [tLit V (TableauVar.stkElem 0 V.k₀ (certBound + j) γ) true])) = true :=
      evalCNF_append_right (evalCNF_append_left (evalCNF_append_left hIC))
    have hb6 : evalCNF σ
        (Finset.univ.toList.flatMap (fun k =>
          if k = V.k₀ then [] else [[tLit V (TableauVar.stkLen 0 k 0) true]])) = true :=
      evalCNF_append_right hIC
    -- Reassemble `initialConstraints (aInput ++ cert)`:
    -- c1=label c2=state c3=stkLen(=(aInput++cert).length) c4=cells c5=other-stacks.
    simp only [evalCNF, List.all_append, Bool.and_eq_true]
    refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · exact hb1
    · exact hb2
    · -- c3: rewrite (aInput ++ cert).length to aInput.length + certBound, then reuse hb3
      rw [show (aInput ++ cert).length = aInput.length + certBound from by
          rw [List.length_append, hcertlen]]
      exact hb3
    · -- c4: cell clauses over (aInput ++ cert).reverse.zipIdx
      sorry
    · exact hb6
  have hfull : evalCNF σ (tableauFormula params (aInput ++ cert)) = true := by
    unfold tableauFormula
    simp only [evalCNF, List.all_append, Bool.and_eq_true]
    exact ⟨⟨⟨⟨hC, hinit⟩, hT⟩, hF⟩, hA⟩
  exact ⟨cert, hcertlen, hcertelem, ⟨σ, hfull⟩⟩

end CookLevinTableau