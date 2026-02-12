/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Computational complexity class definitions: P, NP, NP-completeness,
polynomial-time reductions.

Adapted from LeanMillenniumPrizeProblems (lean-dojo) which follows
Cook's Clay Mathematics Institute problem description.

Trust level: 🟡 Definitions only — no theorems yet.
-/
import Mathlib.Computability.TMComputable
import Mathlib.Computability.Encoding

namespace OpenLemma.Complexity

open Turing Computability

/-! ## Languages (Decision Problems) -/

/-- A language (decision problem) is a predicate on an input type. -/
def Language (α : Type) := α → Prop

/-! ## The Class P -/

/-- A language is in P if its characteristic function is computable
    by a deterministic TM in polynomial time. -/
def InP {α : Type} (ea : FinEncoding α) (L : Language α) : Prop :=
  ∃ (f : α → Bool) (_comp : TM2ComputableInPolyTime ea finEncodingBoolBool f),
    ∀ a, L a ↔ f a = true

/-! ## Pair Encoding -/

private def sumInl? {α β : Type} : Sum α β → Option α
  | Sum.inl a => some a
  | Sum.inr _ => none

private def sumInr? {α β : Type} : Sum α β → Option β
  | Sum.inl _ => none
  | Sum.inr b => some b

/-- Encoding for pairs (α × β) via tagged concatenation of individual encodings.
    Needed for NP verification (input + certificate). -/
def pairEncoding {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β) :
    FinEncoding (α × β) :=
  { Γ := Sum ea.Γ eb.Γ
    encode := fun p => (ea.encode p.1).map Sum.inl ++ (eb.encode p.2).map Sum.inr
    decode := fun l =>
      let a_list := l.filterMap sumInl?
      let b_list := l.filterMap sumInr?
      match ea.decode a_list, eb.decode b_list with
      | some a, some b => some (a, b)
      | _, _ => none
    decode_encode := by
      rintro ⟨a, b⟩
      simp only [List.filterMap_append, List.filterMap_map]
      have h1 : List.filterMap (sumInl? (β := eb.Γ) ∘ Sum.inl (β := eb.Γ)) (ea.encode a) = ea.encode a := by
        induction ea.encode a <;> simp [sumInl?, *]
      have h2 : List.filterMap (sumInl? (α := ea.Γ) ∘ Sum.inr (α := ea.Γ)) (eb.encode b) = [] := by
        induction eb.encode b <;> simp [sumInl?, *]
      have h3 : List.filterMap (sumInr? (β := eb.Γ) ∘ Sum.inl (β := eb.Γ)) (ea.encode a) = [] := by
        induction ea.encode a <;> simp [sumInr?, *]
      have h4 : List.filterMap (sumInr? (α := ea.Γ) ∘ Sum.inr (α := ea.Γ)) (eb.encode b) = eb.encode b := by
        induction eb.encode b <;> simp [sumInr?, *]
      rw [h1, h2, h3, h4]
      simp [ea.decode_encode, eb.decode_encode]
    ΓFin := inferInstance }

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
  ∃ (f : α → β) (_comp : TM2ComputableInPolyTime ea eb f),
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

/-- NP-complete = NP ∩ NP-hard. -/
theorem npComplete_iff_np_and_hard {α : Type} (ea : FinEncoding α) (L : Language α) :
    NPComplete ea L ↔ InNP ea L ∧ NPHard ea L :=
  Iff.rfl

end OpenLemma.Complexity
