import Mathlib.Computability.Encoding
import Mathlib.Logic.Encodable.Basic
import Batteries.Data.List.Basic

namespace OpenLemma.Complexity

open Computability

/-- Helper to flatten a list of options into an option of list. -/
def Option.sequence {α : Type} : List (Option α) → Option (List α)
  | [] => some []
  | (some x :: xs) => (Option.sequence xs).map (x :: ·)
  | (none :: _) => none

def sumEncoding {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β) : FinEncoding (Sum α β) where
  Γ := Sum Bool (Sum ea.Γ eb.Γ)
  encode x := match x with
    | Sum.inl a => (Sum.inl true) :: (ea.encode a).map (Sum.inr ∘ Sum.inl)
    | Sum.inr b => (Sum.inl false) :: (eb.encode b).map (Sum.inr ∘ Sum.inr)
  decode l := match l with
    | Sum.inl true :: rest =>
      let inner := rest.filterMap (fun x => match x with | Sum.inr (Sum.inl c) => some c | _ => none)
      (ea.decode inner).map Sum.inl
    | Sum.inl false :: rest =>
      let inner := rest.filterMap (fun x => match x with | Sum.inr (Sum.inr c) => some c | _ => none)
      (eb.decode inner).map Sum.inr
    | _ => none
  decode_encode x := by
    cases x with
    | inl a =>
      simp only [encode, decode, List.filterMap_map, Function.comp_apply]
      have : (fun x => match (Sum.inr (Sum.inl x) : Sum Bool (Sum ea.Γ eb.Γ)) with
        | Sum.inr (Sum.inl c) => some c
        | _ => none) = some := by
        funext x; rfl
      rw [this]
      simp [List.filterMap_some, ea.decode_encode]
    | inr b =>
      simp only [encode, decode, List.filterMap_map, Function.comp_apply]
      have : (fun x => match (Sum.inr (Sum.inr x) : Sum Bool (Sum ea.Γ eb.Γ)) with
        | Sum.inr (Sum.inr c) => some c
        | _ => none) = some := by
        funext x; rfl
      rw [this]
      simp [List.filterMap_some, eb.decode_encode]
  ΓFin := inferInstance

end OpenLemma.Complexity
