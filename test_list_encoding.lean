import Mathlib.Computability.Encoding
import Mathlib.Logic.Encodable.Basic
import Batteries.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Basic

namespace OpenLemma.Complexity

open Computability

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
    rw [List.getLast?_cons]
    · rw [ih]; rfl
    · let R := (zs.flatMap (fun x => (ea_encode x).map some ++ [none]))
      cases chunks_zs : R.splitOn none with
      | nil => simp [chunks_zs] at ih
      | cons c cs => simp [chunks_zs]

def listEncoding {α : Type} (ea : FinEncoding α) [DecidableEq ea.Γ] : FinEncoding (List α) where
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
      simp only [List.flatMap_cons, List.append_assoc, List.singleton_append]
      let L := (ea.encode x).map some
      let enc_xs := xs.flatMap (fun x => (ea.encode x).map some ++ [none])
      let chunks_xs := enc_xs.splitOn none
      have h_last_xs : chunks_xs.getLast? = some [] := splitOn_flatMap_none_getLast? ea.encode xs
      
      rw [splitOn_none_map_some]
      have h_last : (L :: chunks_xs).getLast? = some [] := by
        rw [List.getLast?_cons, h_last_xs]; rfl
        cases h_chunks : chunks_xs with
        | nil => rw [h_chunks] at h_last_xs; simp at h_last_xs
        | cons c cs => simp
      
      simp only [h_last, ↓reduceIte, List.dropLast]
      -- dropLast on L :: chunks_xs
      cases h_chunks : chunks_xs with
      | nil => rw [h_chunks] at h_last_xs; simp at h_last_xs
      | cons c cs =>
        simp only [h_chunks, ↓reduceIte, List.map_cons]
        have h_filt : L.filterMap id = ea.encode x := by
          induction ea.encode x <;> simp [*]
        rw [h_filt, ea.decode_encode, Option.sequence, Option.map_some]
        have h_if : (if chunks_xs.getLast? = some [] then chunks_xs.dropLast else chunks_xs).map (fun chunk => ea.decode (chunk.filterMap id)) =
                     chunks_xs.dropLast.map (fun chunk => ea.decode (chunk.filterMap id)) := by
          simp [h_last_xs]
        rw [← h_if]
        exact ih
  ΓFin := inferInstance

end OpenLemma.Complexity
