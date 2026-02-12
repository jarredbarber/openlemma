import Mathlib.Computability.Encoding
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import botlib.Complexity.Encodings
import botlib.Complexity.SAT

open OpenLemma.Complexity OpenLemma.Complexity.SAT Computability

variable (φ : CNF)

theorem length_encodeLiteral_test (l : Literal) :
    (finEncodingLiteral.encode l).length = l.var.size + 1 := by
  cases l with
  | pos n => 
    simp [finEncodingLiteral, literalSumEncoding, sumEncoding, finEncodingNatBool, encodingNatBool]
    rw [Nat.size_eq_bits_len]
    rfl
  | neg n =>
    simp [finEncodingLiteral, literalSumEncoding, sumEncoding, finEncodingNatBool, encodingNatBool]
    rw [Nat.size_eq_bits_len]
    rfl

theorem length_encodeClause_test (c : Clause) :
    (finEncodingClause.encode c).length = (c.map (fun l => l.var.size + 2)).sum := by
  rw [finEncodingClause, listEncoding_length]
  simp only [List.map_map, Function.comp_apply]
  congr; funext l
  rw [length_encodeLiteral_test, Nat.add_assoc]
  rfl

theorem length_encodeCNF_test (φ : CNF) :
    (finEncodingCNF.encode φ).length = (φ.map (fun c => (c.map (fun l => l.var.size + 2)).sum + 1)).sum := by
  rw [finEncodingCNF, listEncoding_length]
  simp only [List.map_map, Function.comp_apply]
  congr; funext c
  rw [length_encodeClause_test]

theorem vars_dedup_length_le_encoding_test (φ : CNF) :
    φ.vars.dedup.length ≤ (finEncodingCNF.encode φ).length := by
  rw [length_encodeCNF_test]
  apply (List.length_dedup_le _).trans
  rw [CNF.vars, List.length_flatMap, List.sum_map_comp]
  simp only [Clause.vars, List.length_map]
  apply List.sum_le_sum
  intro c _
  induction c with
  | nil => simp
  | cons l ls ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    have : l.var.size + 2 ≥ 1 := by omega
    omega
