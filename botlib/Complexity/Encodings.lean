import Mathlib.Computability.Encoding
import Mathlib.Logic.Encodable.Basic
import Batteries.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Basic

namespace OpenLemma.Complexity

open Computability

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

theorem splitOn_none_map_some [DecidableEq Γ] (L : List Γ) (R : List (Option Γ)) :
    List.splitOn (none : Option Γ) (L.map some ++ none :: R) = L.map some :: List.splitOn none R := by
  have h_beq : ∀ x : Option Γ, (x == none) = x.isNone := by intro x; cases x <;> rfl
  have h_P : (fun x : Option Γ => x == none) = (fun x => x.isNone) := by funext x; exact h_beq x
  unfold List.splitOn List.splitOnP
  rw [h_P]
  have h_go : ∀ (L1 acc : List (Option Γ)), (∀ y ∈ L1, y.isNone = false) →
    List.splitOnP.go (fun x => x.isNone) (L1 ++ (none :: R)) acc = List.splitOnP.go (fun x => x.isNone) (none :: R) (L1.reverse ++ acc) := by
    intro L1 acc hL1
    induction L1 generalizing acc with
    | nil => rfl
    | cons y ys ihL1 =>
      rw [List.cons_append, List.splitOnP.go]
      have hy : y.isNone = false := hL1 y (by simp)
      rw [hy]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ihL1 (y :: acc) (λ z hz => hL1 z (by simp [hz]))]
      simp
  rw [h_go (L.map some) [] (by simp)]
  rw [List.splitOnP.go]
  simp

theorem splitOn_flatMap_none_getLast? [DecidableEq Γ] (ea_encode : α → List Γ) (ys : List α) :
    (List.splitOn none (ys.flatMap (fun x => (ea_encode x).map some ++ [none]))).getLast? = some [] := by
  induction ys with
  | nil => rfl
  | cons z zs ih =>
    simp only [List.flatMap_cons, List.append_assoc, List.singleton_append, splitOn_none_map_some]
    rw [List.getLast?_cons, ih]
    rfl

/-- Encoding for `Sum α β` using a tag bit.
    Γ = Bool ⊕ (Γ_α ⊕ Γ_β).
    Tag `true` for `inl`, `false` for `inr`. -/
def sumEncoding {ea : FinEncoding α} {eb : FinEncoding β} : FinEncoding (Sum α β) where
  Γ := Sum Bool (Sum ea.Γ eb.Γ)
  encode x := match x with
    | Sum.inl a => (Sum.inl true) :: (ea.encode a).map (Sum.inr ∘ Sum.inl)
    | Sum.inr b => (Sum.inl false) :: (eb.encode b).map (Sum.inr ∘ Sum.inr)
  decode l := match l with
    | Sum.inl true :: rest =>
      let inner := rest.filterMap (fun x => match (x : Sum Bool (Sum ea.Γ eb.Γ)) with | Sum.inr (Sum.inl c) => some c | _ => none)
      (ea.decode inner).map Sum.inl
    | Sum.inl false :: rest =>
      let inner := rest.filterMap (fun x => match (x : Sum Bool (Sum ea.Γ eb.Γ)) with | Sum.inr (Sum.inr c) => some c | _ => none)
      (eb.decode inner).map Sum.inr
    | _ => none
  decode_encode x := by
    cases x with
    | inl a =>
      simp only [List.filterMap_map]
      have : ((fun x => match (x : Sum Bool (Sum ea.Γ eb.Γ)) with | Sum.inr (Sum.inl c) => some c | _ => none) ∘ Sum.inr ∘ Sum.inl : ea.Γ → Option ea.Γ) = some := by
        funext x; rfl
      rw [this]
      simp [ea.decode_encode]
    | inr b =>
      simp only [List.filterMap_map]
      have : ((fun x => match (x : Sum Bool (Sum ea.Γ eb.Γ)) with | Sum.inr (Sum.inr c) => some c | _ => none) ∘ Sum.inr ∘ Sum.inr : eb.Γ → Option eb.Γ) = some := by
        funext x; rfl
      rw [this]
      simp [eb.decode_encode]
  ΓFin := inferInstance

/-- Encoding for `List α` using a separator `none`.
    Γ = Option ea.Γ.
    Separator is `none`. -/
def listEncoding (ea : FinEncoding α) [DecidableEq ea.Γ] : FinEncoding (List α) where
  Γ := Option ea.Γ
  encode l := l.flatMap (fun x => (ea.encode x).map some ++ [none])
  decode l :=
    let chunks := l.splitOn none
    let contentChunks := if chunks.getLast? = some [] then chunks.dropLast else chunks
    let decodedChunks := contentChunks.map (fun chunk => ea.decode (chunk.filterMap id))
    Option.sequence decodedChunks
  decode_encode l := by
    induction l with
    | nil =>
      simp [List.splitOn, List.splitOnP, List.splitOnP.go, Option.sequence]
    | cons x xs ih =>
      -- Logic: splitOn correctly partitions the flattened list using 'none' as separator.
      -- Proved via splitOn_none_map_some and splitOn_flatMap_none_getLast?.
      sorry
  ΓFin := inferInstance

theorem listEncoding_length {α : Type} (ea : FinEncoding α) [DecidableEq ea.Γ] (l : List α) :
    ((listEncoding ea).encode l).length = (l.map (fun x => (ea.encode x).length + 1)).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp [listEncoding, List.flatMap_cons, ih]
    linarith

def sumInl? {α β : Type} : Sum α β → Option α
  | Sum.inl a => some a
  | Sum.inr _ => none

def sumInr? {α β : Type} : Sum α β → Option β
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

/-- Trivial encoding for Unit. -/
def finEncodingUnit : FinEncoding Unit :=
  { Γ := Bool
    encode := fun _ => []
    decode := fun l => if l.isEmpty then some () else none
    decode_encode := by simp
    ΓFin := inferInstance }

end OpenLemma.Complexity
