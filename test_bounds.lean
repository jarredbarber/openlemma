import Mathlib.Computability.Encoding
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import botlib.Complexity.Encodings
import botlib.Complexity.SAT

open OpenLemma.Complexity OpenLemma.Complexity.SAT Computability

theorem sum_map_dedup_le {α : Type} [OrderedAddCommMonoid α]
    (f : ℕ → α) (hf : ∀ x, 0 ≤ f x) (l : List ℕ) :
    (l.dedup.map f).sum ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.dedup_cons]
    split_ifs with h
    · simp only [List.map_cons, List.sum_cons]
      exact (ih.trans (le_add_self (a := (xs.map f).sum) (b := f x)))
    · simp only [List.map_cons, List.sum_cons]
      exact add_le_add_left ih _

theorem length_encodeLiteral_test (l : Literal) :
    (finEncodingLiteral.encode l).length = l.var.size + 1 := by
  cases l with
  | pos n => 
    unfold finEncodingLiteral literalSumEncoding sumEncoding finEncodingNatBool encodingNatBool encodeNat encodeNum
    simp only [List.length_cons, List.length_map]
    rw [Nat.size_eq_bits_len]
  | neg n =>
    unfold finEncodingLiteral literalSumEncoding sumEncoding finEncodingNatBool encodingNatBool encodeNat encodeNum
    simp only [List.length_cons, List.length_map]
    rw [Nat.size_eq_bits_len]

theorem length_encodeClause_test (c : Clause) :
    (finEncodingClause.encode c).length = (c.map (fun l => l.var.size + 2)).sum := by
  rw [finEncodingClause, listEncoding_length]
  congr; funext l
  rw [length_encodeLiteral_test, Nat.add_assoc]
  rfl

theorem length_encodeCNF_test (φ : CNF) :
    (finEncodingCNF.encode φ).length = (φ.map (fun c => (c.map (fun l => l.var.size + 2)).sum + 1)).sum := by
  rw [finEncodingCNF, listEncoding_length]
  congr; funext c
  rw [length_encodeClause_test]

theorem vars_dedup_length_le_encoding_test (φ : CNF) :
    φ.vars.dedup.length ≤ (finEncodingCNF.encode φ).length := by
  rw [length_encodeCNF_test]
  apply (List.dedup_length_le φ.vars).trans
  rw [CNF.vars, List.length_flatMap]
  have h_len : (List.flatMap Clause.vars φ).length = (φ.map (fun c => c.vars.length)).sum := by
    induction φ with
    | nil => simp
    | cons c cs ih => simp [ih]
  rw [h_len]
  simp only [Clause.vars, List.length_map]
  apply List.sum_le_sum
  intro c _
  induction c with
  | nil => simp
  | cons l ls ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    have : l.var.size + 2 ≥ 1 := by omega
    omega

theorem sum_var_encoding_le_test (φ : CNF) :
    (φ.vars.dedup.map (fun v => (Computability.finEncodingNatBool.encode v).length)).sum
      ≤ (finEncodingCNF.encode φ).length := by
  rw [length_encodeCNF_test]
  have h_lhs : (φ.vars.dedup.map (fun v => (finEncodingNatBool.encode v).length)).sum = (φ.vars.dedup.map (fun v => v.size)).sum := by
    congr; funext v
    simp [finEncodingNatBool, encodingNatBool, encodeNat, encodeNum]
    rw [Nat.size_eq_bits_len]
  rw [h_lhs]
  have h_dedup : (φ.vars.dedup.map (fun v => v.size)).sum ≤ (φ.vars.map (fun v => v.size)).sum :=
    sum_map_dedup_le (fun v => v.size) (fun _ => Nat.zero_le _) φ.vars
  apply h_dedup.trans
  rw [CNF.vars, List.flatMap_eq_flatten, List.map_flatten, List.sum_flatten]
  simp only [Clause.vars, List.map_map, Function.comp_apply]
  apply List.sum_le_sum
  intro c _
  induction c with
  | nil => simp
  | cons l ls ih =>
    simp only [List.map_cons, List.sum_cons]
    omega

theorem cert_encoding_le_cube_test (φ : CNF) (σ : Assignment) :
    let y := (φ.vars.dedup).map (fun v => (v, σ v))
    (finEncodingSATCertificate.encode y).length ≤ (finEncodingCNF.encode φ).length := by
  intro y
  unfold finEncodingSATCertificate
  rw [listEncoding_length]
  simp only [List.map_map, Function.comp_apply, y]
  have h_len_pair (v : ℕ) (b : Bool) : (pairEncoding finEncodingNatBool finEncodingBoolBool).encode (v, b) |>.length = v.size + 1 := by
    simp [pairEncoding, finEncodingNatBool, encodingNatBool, encodeNat, encodeNum, finEncodingBoolBool, encodeBool]
    rw [Nat.size_eq_bits_len]
    simp
  simp only [h_len_pair]
  have h_lhs : (φ.vars.dedup.map (fun v => v.size + 2)).sum ≤ (finEncodingCNF.encode φ).length := by
    rw [length_encodeCNF_test]
    have h1 : (φ.vars.dedup.map (fun v => v.size + 2)).sum ≤ (φ.vars.map (fun v => v.size + 2)).sum :=
      sum_map_dedup_le (fun v => v.size + 2) (fun _ => Nat.zero_le _) φ.vars
    apply h1.trans
    rw [CNF.vars, List.flatMap_eq_flatten, List.map_flatten, List.sum_flatten]
    simp only [Clause.vars, List.map_map, Function.comp_apply]
    apply List.sum_le_sum
    intro c _
    omega
  apply h_lhs
