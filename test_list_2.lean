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
      simp [Option.sequence]
    | cons x xs ih =>
      simp [List.flatMap_cons]
      sorry
  ΓFin := inferInstance

end OpenLemma.Complexity
