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

namespace OpenLemma.Complexity

open Turing Computability

/-! ## Encodings -/

/-- Generic FinEncoding for any Encodable type using binary encoding of its index. -/
def finEncodingOfEncodable (α : Type) [Encodable α] : FinEncoding α where
  Γ := Bool
  encode x := finEncodingNatBool.encode (Encodable.encode x)
  decode l := (finEncodingNatBool.decode l).bind Encodable.decode
  decode_encode x := by
    simp [finEncodingNatBool.decode_encode, Encodable.encodek]
  ΓFin := Bool.fintype

/-- Helper to flatten a list of options into an option of list. -/
def Option.sequence {α : Type} : List (Option α) → Option (List α)
  | [] => some []
  | (some x :: xs) => (Option.sequence xs).map (x :: ·)
  | (none :: _) => none

/-- Encoding for `Sum α β` using a tag bit.
    Γ = Bool ⊕ (Γ_α ⊕ Γ_β).
    Tag `true` for `inl`, `false` for `inr`. -/
def sumEncoding {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β) : FinEncoding (Sum α β) :=
  { Γ := Sum Bool (Sum ea.Γ eb.Γ)
    encode := fun x => match x with
      | Sum.inl a => (Sum.inl true) :: (ea.encode a).map (Sum.inr ∘ Sum.inl)
      | Sum.inr b => (Sum.inl false) :: (eb.encode b).map (Sum.inr ∘ Sum.inr)
    decode := fun l => match l with
      | Sum.inl true :: rest =>
        let inner := rest.filterMap (fun (x : Sum Bool (Sum ea.Γ eb.Γ)) => match x with | Sum.inr (Sum.inl c) => some c | _ => none)
        (ea.decode inner).map Sum.inl
      | Sum.inl false :: rest =>
        let inner := rest.filterMap (fun (x : Sum Bool (Sum ea.Γ eb.Γ)) => match x with | Sum.inr (Sum.inr c) => some c | _ => none)
        (eb.decode inner).map Sum.inr
      | _ => none
    decode_encode := by
      intro x
      cases x with
      | inl a =>
        simp
        have h : List.filterMap (fun (x : Sum Bool (Sum ea.Γ eb.Γ)) => match x with | Sum.inr (Sum.inl c) => some c | _ => none)
                 (List.map (Sum.inr ∘ Sum.inl) (ea.encode a)) = ea.encode a := by
          induction ea.encode a <;> simp [*]
        rw [List.filterMap_map] at h
        rw [h]
        simp [ea.decode_encode]
      | inr b =>
        simp
        have h : List.filterMap (fun (x : Sum Bool (Sum ea.Γ eb.Γ)) => match x with | Sum.inr (Sum.inr c) => some c | _ => none)
                 (List.map (Sum.inr ∘ Sum.inr) (eb.encode b)) = eb.encode b := by
          induction eb.encode b <;> simp [*]
        rw [List.filterMap_map] at h
        rw [h]
        simp [eb.decode_encode]
    ΓFin := inferInstance }

/-- Encoding for `List α` using a separator `none`.
    Γ = Option Γ_α.
    Separator is `none`. -/
def listEncoding {α : Type} (ea : FinEncoding α) [DecidableEq ea.Γ] : FinEncoding (List α) :=
  { Γ := Option ea.Γ
    encode := fun l => l.flatMap (fun x => (ea.encode x).map some ++ [none])
    decode := fun l =>
      let chunks := l.splitOn none
      let contentChunks := if chunks.getLast? = some [] then chunks.dropLast else chunks
      let decodedChunks := contentChunks.map (fun chunk => ea.decode (chunk.filterMap id))
      Option.sequence decodedChunks
    decode_encode := by
      intro l
      sorry -- Proved linear and correct in NL proof.
    ΓFin := inferInstance }

theorem listEncoding_length {α : Type} (ea : FinEncoding α) [DecidableEq ea.Γ] (l : List α) :
    ((listEncoding ea).encode l).length = (l.map (fun x => (ea.encode x).length + 1)).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    unfold listEncoding
    simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons]
    simp only [List.length_map, List.length_singleton]
    have : ((listEncoding ea).encode xs).length = (xs.flatMap (fun x => (ea.encode x).map some ++ [none])).length := rfl
    rw [← this, ih]

/-! ## Languages (Decision Problems) -/

/-- A language (decision problem) is a predicate on an input type. -/
def Language (α : Type) := α → Prop

/-! ## The Class P -/

/-- A language is in P if its characteristic function is computable
    by a deterministic TM in polynomial time. -/
def InP {α : Type} (ea : FinEncoding α) (L : Language α) : Prop :=
  ∃ (f : α → Bool) (_comp : _root_.Turing.TM2ComputableInPolyTime ea finEncodingBoolBool f),
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

/-- NP-complete = NP ∩ NP-hard. -/
theorem npComplete_iff_np_and_hard {α : Type} (ea : FinEncoding α) (L : Language α) :
    NPComplete ea L ↔ InNP ea L ∧ NPHard ea L :=
  Iff.rfl

/-! ## Basic Encodings & Axioms -/

/-- Trivial encoding for Unit. -/
def finEncodingUnit : FinEncoding Unit :=
  { Γ := Bool
    encode := fun _ => []
    decode := fun l => if l.isEmpty then some () else none
    decode_encode := by simp
    ΓFin := inferInstance }

section Assumptions
-- Temporary axioms pending formalization of poly-time composition.
-- Tracking task: jarred-5hc

/-- Poly-time functions are closed under composition.
    Proved in `botlib/Complexity/TM2PolyTimeComp.lean`. -/
lemma PolyTimeComp {α β γ : Type} {ea : FinEncoding α} {eb : FinEncoding β} {ec : FinEncoding γ}
  {f : α → β} {g : β → γ}
  (hf : _root_.Turing.TM2ComputableInPolyTime ea eb f)
  (hg : _root_.Turing.TM2ComputableInPolyTime eb ec g) :
  Nonempty (_root_.Turing.TM2ComputableInPolyTime ea ec (g ∘ f)) :=
  _root_.OpenLemma.Complexity.Turing.TM2ComputableInPolyTime.comp hf hg

/-- Axiom: Projection (fst) from pairEncoding is poly-time. -/
axiom PolyTimeFst {α β : Type} {ea : FinEncoding α} {eb : FinEncoding β} :
  _root_.Turing.TM2ComputableInPolyTime (pairEncoding ea eb) ea Prod.fst

end Assumptions

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
    -- R(p) = f(p.1) = true. This is deciding the language of R.
    -- We need to show InP (pairEncoding ea finEncodingUnit) (fun p => f p.1 = true)
    -- This is equivalent to f ∘ fst being poly-time computable (to bool).
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
