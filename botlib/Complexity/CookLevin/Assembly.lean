/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

# Cook-Levin assembly scaffold (Bridge 5 + final theorem)

This file scaffolds the remaining Cook-Levin assembly that eliminates the crux
axiom `SAT_is_NP_hard_citation` (CookLevin.lean:46). Each component is stated
with a PRECISE type and a `sorry` (temporary, per AGENTS.md), so that closing
each `sorry` is a focused target. The crux axiom is kept until every `sorry`
here closes and `SAT_is_NP_hard_real` is fully proved.

## The structural gap (reviewer-verified)
`acceptanceConstraints` (Tableau.lean:179) encodes HALTING
(`∃ i, label i = none`), NOT output = true. The `InNP` verifier `g` is TOTAL
(`TM2ComputableInPolyTime.outputsFun` halts on ALL inputs, including
`g a = false`), so "V halts" is always-true and `Satisfiable (f a)` would be
always-true — breaking the iff. Hence a DECIDER transformation `V → V'`
(V' halts iff `g = true`, loops iff `g = false`) is REQUIRED, reusing all
existing halting-based tableau lemmas unchanged.

## Component dependency graph
  InNP eb L' → (R, k, g, g_comp)
    → [Lemma F] NormalForm verifier V computing g                (Bridge 3, sorry)
    → [D1]     decider machine V' : FinTM2                        (this file, sorry)
    → [D2]     V' halts (a,cert) within bound ↔ g(a,cert)=true   (this file, sorry)
    → [D3]     NormalForm V → NormalForm V'                       (this file, sorry)
    → f a = tableauFormulaCert (paramsFor a) (aInput a) (certBound a) boolSyms
    → [Bridge 4] f polytime                                      (PolyTime.lean, citation axiom)
    → [Bridge 5] ∀ a, L' a ↔ SAT_Language (f a)                  (this file, sorry)
    → ⟨f, comp, iff⟩ : PolyTimeReducible eb finEncodingCNF L' SAT_Language
    → SAT_is_NP_hard_real : NPHard finEncodingCNF SAT_Language   (this file, sorry)
-/
import botlib.Complexity.CookLevin.Bridge1
import botlib.Complexity.CookLevin.Bridge2
import botlib.Complexity.CookLevin.Bridge3
import botlib.Complexity.CookLevin.Decider
import botlib.Complexity.CookLevin.CertTableau
import botlib.Complexity.CookLevin.CompletenessCert
import botlib.Complexity.CookLevin.Completeness
import botlib.Complexity.CookLevin.PolyTime
import botlib.Complexity.CookLevin.Tableau
import botlib.Complexity.Defs
import botlib.Complexity.SAT
import botlib.Complexity.Encodings

namespace OpenLemma.Complexity.CookLevinAssembly

open Turing OpenLemma.Complexity OpenLemma.Complexity.SAT Computability CookLevinTableau

/-- D1+D2: every polytime verifier `g` admits a decider `V'`. The witness
    `comp : TM2ComputableInPolyTime ... g` supplies the machine computing `g`
    (`comp.tm`), the output alphabet equiv (`comp.outputAlphabet`), the input
    alphabet equiv (`comp.inputAlphabet`), and the time bound (`comp.time`).
    This fixes the prior BREAK where an arbitrary `V`/`outEquiv`/`Nonempty hComp`
    were disconnected (V could compute a different function than `g`).

    The concrete `decider comp.tm comp.outputAlphabet` machine and sorry-free D3
    (`decider_normal_form`) are in `Decider.lean`; this theorem assembles them into
    a `DeciderSpec` (SORRY: needs `decider_halts_iff` (D2) closed first). -/
theorem decider_exists {β : Type} (eb : FinEncoding β) (g : β × List Bool → Bool)
    (comp : Turing.TM2ComputableInPolyTime (pairEncoding eb finEncodingBoolList)
        finEncodingBoolBool g)
    [Fintype (comp.tm.Γ comp.tm.k₁)]
    (hNF : NormalForm comp.tm) :
    Nonempty (DeciderSpec eb g) := by
  sorry

/-- Bridge 5: the cert-aware tableau iff. For the decider `V'` and the
    cert-aware tableau `f a = tableauFormulaCert (paramsFor a) (aInput a)
    (certBound a) boolSyms`, we have `∀ a, L' a ↔ SAT_Language (f a)`.

    Forward (`L' a → Satisfiable (f a)`): `InNP` → cert with
    `|cert| = |enc a|^k ∧ R a cert` → `g (a, cert) = true` → D2 (`V'` halts) →
    Bridge 1 (`cfgAt` reaches `haltList`) → Bridge 2 (`cfgAt_zero`,
    `initList_h_init_shape` = h_init; `initTape_decomp` = tape = aInput ++
    certMapped; `certMapped_length`/`certMapped_bool` = hcertlen/hcertbool) →
    `cfgAt_succ` = h_step → Bridge 3 (`h_adequate_of_normal_form` = h_depth,
    `bounded_read_depth_of_normal_form` = hBRD) → `reduction_sound_cert` →
    Satisfiable.

    Backward (`Satisfiable (f a) → L' a`): sat → `completeness_cert` (needs
    `certBound ≤ maxStackDepth`; holds since `certBound = |enc a|^k ≤
    |enc a| + |enc a|^k + timeBound = maxStackDepth`) → ∃ cert,
    `Satisfiable (tableauFormula (aInput ++ cert))` → `completeness` (needs
    `BoundedReadDepth` + `h_adequate` from Bridge 3 under `NormalForm V'`) →
    ∃ i, `V'` halts → D2(←) → `g (a, cert) = true` → Bridge 2 boolSyms-inverse
    (symbol ∈ boolSyms → Bool; DEFERRED direction) → `certBool` → `R a certBool`
    (`InNP`) → `L' a` (`InNP`).

    SORRY: needs D1-D3 (decider), Lemma F (NormalForm), Bridge 2 boolSyms-inverse
    (deferred direction), and the Bridge-2 residual (DecidableEq instance
    agreement for the concretely-constructed `V'`).

    NOTE: the equality hypotheses fixing `aInput a = (eb.encode a).map
    (hGamma'.invFun ∘ Sum.inl)`, `certBound a = |eb.encode a|^k`, and
    `boolSyms = {invFun (inr true), invFun (inr false)}` are enforced at the
    final-assembly call site (where `f` is built); they are omitted here to keep
    the lemma statement about the iff structural content. -/
theorem bridge5_iff {β : Type} (eb : FinEncoding β) (L' : Language β)
    (R : β → List Bool → Prop) (k : ℕ) (g : β × List Bool → Bool)
    (hInNP : (∀ a cert, R a cert ↔ g (a, cert) = true) ∧
      ∀ a, L' a ↔ ∃ cert, cert.length = (eb.encode a).length ^ k ∧ R a cert)
    (V' : Turing.FinTM2)
    [Encodable V'.Λ] [Encodable V'.σ] [Encodable V'.K] [∀ k, Encodable (V'.Γ k)]
    [Fintype V'.Λ] [Fintype V'.σ] [Fintype V'.K] [∀ k, Fintype (V'.Γ k)]
    [DecidableEq V'.K] [∀ k, DecidableEq (V'.Γ k)]
    [DecidableEq V'.Λ] [DecidableEq V'.σ]
    (hGamma' : V'.Γ V'.k₀ ≃ Sum eb.Γ Bool) (hNF' : NormalForm V')
    (boolSyms : Finset (V'.Γ V'.k₀))
    (paramsFor : β → Params V')
    (aInput : β → List (V'.Γ V'.k₀))
    (certBound : β → ℕ) :
    ∀ a, L' a ↔
      SAT_Language (tableauFormulaCert (paramsFor a) (aInput a) (certBound a) boolSyms) := by
  sorry

/-- The real Cook-Levin NP-hardness theorem: every NP language poly-time reduces
    to SAT. Replaces the crux axiom `SAT_is_NP_hard_citation` once every
    `sorry` above closes. The crux axiom is kept (in CookLevin.lean) until then.

    SORRY: assembles `decider_exists` + `decider_normal_form` + `bridge5_iff`
    + `tableauFormulaCert_is_polytime` (Bridge 4 citation) + Lemma F
    (`normal_form_normalization`, Bridge 3 sorry) into
    `PolyTimeReducible eb finEncodingCNF L' SAT_Language` for every `InNP eb L'`. -/
theorem SAT_is_NP_hard_real : NPHard finEncodingCNF SAT_Language := by
  sorry

end OpenLemma.Complexity.CookLevinAssembly