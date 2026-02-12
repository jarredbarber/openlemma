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

/-- A checking relation R is polynomial-time if the associated language
    { (w, y) | R(w, y) } is in P. -/
def PolyTimeCheckingRelation {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β)
    (R : α → β → Prop) : Prop :=
  InP (pairEncoding ea eb) (fun p => R p.1 p.2)

/-- A language L is in NP if there exist a polynomial k and a polynomial-time
    checking relation R such that:
    x ∈ L ↔ ∃ y, |y| ≤ |x|^k ∧ R(x, y)
    (Cook's Clay problem description) -/
def InNP {α : Type} (ea : FinEncoding α) (L : Language α) : Prop :=
  ∃ (β : Type) (eb : FinEncoding β) (R : α → β → Prop) (k : ℕ),
    PolyTimeCheckingRelation ea eb R ∧
      ∀ a, L a ↔ ∃ b, (eb.encode b).length ≤ (ea.encode a).length ^ k ∧ R a b

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

/-- P is a subset of NP. -/
theorem P_subset_NP {α : Type} (ea : FinEncoding α) (L : Language α) :
    InP ea L → InNP ea L := by
  intro h
  rcases h with ⟨f, hf, hL⟩
  use Unit, finEncodingUnit
  -- checking relation R(x, y) = f(x)
  let R := fun (x : α) (_ : Unit) => f x = true
  use R, 0
  constructor
  · -- R is poly-time checking
    unfold PolyTimeCheckingRelation InP
    rcases PolyTimeComp PolyTimeFst hf with ⟨h_comp⟩
    exact ⟨fun p => f p.1, h_comp, fun ⟨a, u⟩ => by simp [R]⟩
  · -- witness bound
    intro x
    constructor
    · intro lx
      use ()
      simp [finEncodingUnit]
      rw [hL] at lx
      exact lx
    · intro ⟨y, _, ry⟩
      rw [hL]
      exact ry

end OpenLemma.Complexity
