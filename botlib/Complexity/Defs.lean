/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Computational complexity class definitions: P, NP, NP-completeness,
polynomial-time reductions.

Adapted from LeanMillenniumPrizeProblems (lean-do Dojo) which follows
Cook's Clay Mathematics Institute problem description.

Trust level: 🟡 Definitions only — no theorems yet.
-/
import Mathlib.Computability.TMComputable
import Mathlib.Computability.Encoding
import Mathlib.Logic.Encodable.Basic
import Batteries.Data.List.Basic
import botlib.Complexity.TM2PolyTimeComp
import botlib.Complexity.Encodings
import botlib.Complexity.PolyTimeFst

namespace OpenLemma.Complexity

open Turing Computability

/-! ## Languages (Decision Problems) -/

/-- A language (decision problem) is a predicate on an input type. -/
def Language (α : Type) := α → Prop

/-! ## The Class P -/

/-- A language is in P if its characteristic function is computable
    by a deterministic TM in polynomial time. -/
def InP {α : Type} (ea : FinEncoding α) (L : Language α) : Prop :=
  ∃ (f : α → Bool) (_comp : _root_.Turing.TM2ComputableInPolyTime ea finEncodingBoolBool f),
    ∀ a, L a ↔ f a = true

/-! ## The Class NP -/

/-- A language L is in NP if there exists a polynomial-time verifier `g` taking
    the input `a` and a **raw-bit certificate** `cert : List Bool`, and a bound `k`,
    such that `x ∈ L ↔ ∃ cert, |cert| = |enc(x)|^k ∧ R(x, cert)` where `R(x, cert)`
    holds iff `g (x, cert) = true`.

The certificate uses the identity encoding `finEncodingBoolList` (every bit-string is
    a valid encoding of itself). This is the standard verifier/NDTM characterization of
    NP: the certificate is a raw bit-string read directly from the tape, so that in the
    Cook-Levin tableau the certificate bits can be left as free propositional variables
    with no encoding-validity gap. (A general `FinEncoding` for the certificate would
    permit non-computable encodings and make Cook-Levin false; the raw-bit form is the
    correct, standard one.) -/
def InNP {α : Type} (ea : FinEncoding α) (L : Language α) : Prop :=
  ∃ (R : α → List Bool → Prop) (k : ℕ) (g : α × List Bool → Bool)
    (g_comp : Nonempty (_root_.Turing.TM2ComputableInPolyTime
               (pairEncoding ea finEncodingBoolList) finEncodingBoolBool g)),
    (∀ a cert, R a cert ↔ g (a, cert) = true) ∧
      ∀ a, L a ↔ ∃ cert, cert.length = (ea.encode a).length ^ k ∧ R a cert

/-! ## Reductions -/

/-- Polynomial-time many-one reducibility: L₁ ≤ₚ L₂ if there exists a
    polynomial-time computable f with x ∈ L₁ ↔ f(x) ∈ L₂. -/
def PolyTimeReducible {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β)
    (L₁ : Language α) (L₂ : Language β) : Prop :=
  ∃ (f : α → β) (_comp : _root_.Turing.TM2ComputableInPolyTime ea eb f),
    ∀ a, L₁ a ↔ L₂ (f a)

/-! ## NP-Completeness -/

/-- A language is NP-complete if it is in NP and every NP language
    polynomial-time reduces to it. -/
def NPComplete {α : Type} (ea : FinEncoding α) (L : Language α) : Prop :=
  InNP ea L ∧
    ∀ {β : Type} (eb : FinEncoding β) (L' : Language β),
      InNP eb L' → PolyTimeReducible eb ea L' L

/-! ## NP-Hardness -/

/-- A language is NP-hard if every NP language polynomial-time reduces to it.
    (NP-hard languages need not be in NP themselves.) -/
def NPHard {α : Type} (ea : FinEncoding α) (L : Language α) : Prop :=
  ∀ {β : Type} (eb : FinEncoding β) (L' : Language β),
    InNP eb L' → PolyTimeReducible eb ea L' L

section Assumptions
-- Temporary assumptions pending full formalization.

/-- Poly-time functions are closed under composition.
    Proved in `botlib/Complexity/TM2PolyTimeComp.lean`. -/
lemma PolyTimeComp {α β γ : Type} {ea : FinEncoding α} {eb : FinEncoding β} {ec : FinEncoding γ}
  {f : α → β} {g : β → γ}
  (hf : _root_.Turing.TM2ComputableInPolyTime ea eb f)
  (hg : _root_.Turing.TM2ComputableInPolyTime eb ec g) :
  Nonempty (_root_.Turing.TM2ComputableInPolyTime ea ec (g ∘ f)) :=
  _root_.OpenLemma.Complexity.Turing.TM2ComputableInPolyTime.comp hf hg

/-- Projection (fst) from pairEncoding is poly-time.
    Proved axiom-free in `botlib/Complexity/PolyTimeFst.lean`. -/
noncomputable def PolyTimeFst {α β : Type} {ea : FinEncoding α} {eb : FinEncoding β} :
    _root_.Turing.TM2ComputableInPolyTime (pairEncoding ea eb) ea Prod.fst := by
  by_cases h : Nonempty ea.Γ
  · exact _root_.PolyTimeFstTrack.PolyTimeFst_witness
  · exact _root_.PolyTimeFstTrack.polyTimeFst_empty_alphabet ea eb

end Assumptions

/-- Reduction is transitive. -/
theorem PolyTimeReducible.trans {α β γ : Type} {ea : FinEncoding α} {eb : FinEncoding β} {ec : FinEncoding γ}
    {L₁ : Language α} {L₂ : Language β} {L₃ : Language γ} :
    PolyTimeReducible ea eb L₁ L₂ → PolyTimeReducible eb ec L₂ L₃ → PolyTimeReducible ea ec L₁ L₃ := by
  intro ⟨f, hf, hfL⟩ ⟨g, hg, hgL⟩
  use g ∘ f
  rcases PolyTimeComp hf hg with ⟨h_comp⟩
  use h_comp
  intro a
  rw [hfL, hgL]
  rfl

/-- NP-complete = NP ∩ NP-hard. -/
theorem npComplete_iff_np_and_hard {α : Type} (ea : FinEncoding α) (L : Language α) :
    NPComplete ea L ↔ InNP ea L ∧ NPHard ea L :=
  Iff.rfl

/-- If L₁ is NP-hard and L₁ ≤ₚ L₂, then L₂ is NP-hard. -/
theorem NPHard.reducible {α β : Type} {ea : FinEncoding α} {eb : FinEncoding β}
    {L₁ : Language α} {L₂ : Language β} :
    NPHard ea L₁ → PolyTimeReducible ea eb L₁ L₂ → NPHard eb L₂ := by
  intro h_hard h_red γ ec L' h_np
  have h1 : PolyTimeReducible ec ea L' L₁ := h_hard ec L' h_np
  exact PolyTimeReducible.trans h1 h_red

/-- If L₁ is NP-complete and L₁ ≤ₚ L₂, and L₂ ∈ NP, then L₂ is NP-complete. -/
theorem NPComplete.reducible {α β : Type} {ea : FinEncoding α} {eb : FinEncoding β}
    {L₁ : Language α} {L₂ : Language β} :
    NPComplete ea L₁ → PolyTimeReducible ea eb L₁ L₂ → InNP eb L₂ → NPComplete eb L₂ := by
  intro h_comp h_red h_np
  constructor
  · exact h_np
  · exact NPHard.reducible h_comp.2 h_red

/-! ## P ⊆ NP -/

/-- P is a subset of NP.
    A P-decider ignores the (raw-bit) certificate; we use a certificate of length
    `|enc(x)|^0 = 1` and a relation `R x cert = (f x = true)` independent of `cert`.
    The verifier `g (x, cert) = f x` is poly-time as `f ∘ Prod.fst`. -/
theorem P_subset_NP {α : Type} (ea : FinEncoding α) (L : Language α) :
    InP ea L → InNP ea L := by
  intro ⟨f, hf, hL⟩
  let R := fun (x : α) (_ : List Bool) => f x = true
  have hfst :
      _root_.Turing.TM2ComputableInPolyTime
        (pairEncoding ea finEncodingBoolList) ea Prod.fst := PolyTimeFst
  have hg_comp : Nonempty
      (_root_.Turing.TM2ComputableInPolyTime
        (pairEncoding ea finEncodingBoolList) finEncodingBoolBool (fun p => f p.1)) :=
    PolyTimeComp hfst hf
  refine ⟨R, 0, (fun p => f p.1), hg_comp, ?_, ?_⟩
  · intro a cert; simp [R]
  · intro a
    constructor
    · intro ha
      refine ⟨[false], ?_, ?_⟩
      · rfl
      · show f a = true; exact (hL a).mp ha
    · rintro ⟨cert, hlen, hR⟩
      rw [hL]
      simp [R] at hR
      exact hR

end OpenLemma.Complexity
