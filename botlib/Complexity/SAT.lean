/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Definition of the Boolean Satisfiability Problem (SAT) as a formal language.
This is the target language for the Cook-Levin theorem.

Trust level: 🟡 Definitions only — Cook-Levin proof pending.
-/
import Mathlib.Computability.Encoding
import Mathlib.Logic.Encodable.Basic
import Mathlib.Logic.Equiv.List
import Mathlib.Tactic.DeriveEncodable
import Mathlib.Data.Bool.AllAny
import Mathlib.Data.List.Dedup
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Batteries.Data.List.Basic
import botlib.Complexity.Defs
import botlib.Complexity.Encodings

namespace OpenLemma.Complexity.SAT

open Computability Complexity

/-! ## Boolean Formulas

We define propositional formulas over variables indexed by ℕ.
This is sufficient for Cook-Levin since the reduction produces
formulas with finitely many variables.
-/

/-- A literal is a variable (positive) or its negation. -/
inductive Literal : Type where
  | pos : ℕ → Literal
  | neg : ℕ → Literal
  deriving DecidableEq, Repr, Encodable

/-- A clause is a disjunction of literals. -/
abbrev Clause := List Literal

/-- A CNF formula is a conjunction of clauses. -/
abbrev CNF := List Clause

/-- An assignment maps variable indices to truth values. -/
abbrev Assignment := ℕ → Bool

/-- Evaluate a literal under an assignment. -/
def evalLiteral (σ : Assignment) : Literal → Bool
  | Literal.pos v => σ v
  | Literal.neg v => !σ v

/-- A clause is satisfied if at least one literal is true. -/
def evalClause (σ : Assignment) (c : Clause) : Bool :=
  c.any (evalLiteral σ)

/-- A CNF formula is satisfied if all clauses are satisfied. -/
def evalCNF (σ : Assignment) (φ : CNF) : Bool :=
  φ.all (evalClause σ)

/-- The set of variable indices appearing in a literal. -/
@[simp]
def Literal.var : Literal → ℕ
  | pos v => v
  | neg v => v

/-- The set of variable indices appearing in a clause. -/
def Clause.vars (c : Clause) : List ℕ :=
  c.map Literal.var

/-- The set of variable indices appearing in a CNF formula. -/
def CNF.vars (φ : CNF) : List ℕ :=
  φ.flatMap Clause.vars

theorem evalLiteral_eq_of_vars_eq {σ1 σ2 : Assignment} {l : Literal}
    (h : σ1 l.var = σ2 l.var) : evalLiteral σ1 l = evalLiteral σ2 l := by
  cases l <;> simp [evalLiteral] <;> exact h

theorem evalClause_eq_of_vars_eq {σ1 σ2 : Assignment} {c : Clause}
    (h : ∀ v ∈ c.vars, σ1 v = σ2 v) : evalClause σ1 c = evalClause σ2 c := by
  induction c with
  | nil => rfl
  | cons l ls ih =>
    unfold evalClause
    simp only [List.any_cons]
    have h1 : evalLiteral σ1 l = evalLiteral σ2 l := by
      apply evalLiteral_eq_of_vars_eq
      apply h
      simp only [Clause.vars, List.map_cons, List.mem_cons, true_or]
    have h2 : ls.any (evalLiteral σ1) = ls.any (evalLiteral σ2) := by
      apply ih
      intro v hv
      apply h
      simp only [Clause.vars, List.map_cons, List.mem_cons]
      right; exact hv
    rw [h1, h2]

theorem evalCNF_eq_of_vars_eq {σ1 σ2 : Assignment} {φ : CNF}
    (h : ∀ v ∈ φ.vars, σ1 v = σ2 v) : evalCNF σ1 φ = evalCNF σ2 φ := by
  induction φ with
  | nil => rfl
  | cons c cs ih =>
    unfold evalCNF
    simp only [List.all_cons]
    have h1 : evalClause σ1 c = evalClause σ2 c := by
      apply evalClause_eq_of_vars_eq
      intro v hv
      apply h
      simp only [CNF.vars, List.flatMap_cons, List.mem_append]
      left; exact hv
    have h2 : cs.all (evalClause σ1) = cs.all (evalClause σ2) := by
      apply ih
      intro v hv
      apply h
      simp only [CNF.vars, List.flatMap_cons, List.mem_append]
      right; exact hv
    rw [h1, h2]

/-- A CNF formula is satisfiable if some assignment satisfies it. -/
def Satisfiable (φ : CNF) : Prop :=
  ∃ σ : Assignment, evalCNF σ φ = true

/-- The SAT language: the set of satisfiable CNF formulas. -/
def SAT_Language : CNF → Prop := Satisfiable

/-! ## Encodings

We define standard finite encodings for SAT-related types.
We ensure these encodings are polynomial-time efficient (linear in value/structure).
-/

/-- Raw encoding for Sum ℕ ℕ. -/
abbrev literalSumEncoding : FinEncoding (Sum ℕ ℕ) := sumEncoding finEncodingNatBool finEncodingNatBool

instance : DecidableEq literalSumEncoding.Γ := by
  dsimp [literalSumEncoding, sumEncoding, finEncodingNatBool, encodingNatBool]
  infer_instance

/-- FinEncoding for Literals (isomorphic to Sum ℕ ℕ). -/
abbrev finEncodingLiteral : FinEncoding Literal :=
  let iso : Literal ≃ Sum ℕ ℕ := {
    toFun := fun l => match l with | Literal.pos n => Sum.inl n | Literal.neg n => Sum.inr n
    invFun := fun s => match s with | Sum.inl n => Literal.pos n | Sum.inr n => Literal.neg n
    left_inv := fun l => by cases l <;> simp
    right_inv := fun s => by cases s <;> simp
  }
  { Γ := literalSumEncoding.Γ
    encode := fun l => literalSumEncoding.encode (iso l)
    decode := fun l => (literalSumEncoding.decode l).map iso.symm
    decode_encode := by
      intro l
      rw [literalSumEncoding.decode_encode]
      simp
    ΓFin := literalSumEncoding.ΓFin }

-- Ensure DecidableEq is available for Literal encoding alphabet
instance : DecidableEq finEncodingLiteral.Γ := by
  dsimp [finEncodingLiteral]
  infer_instance

/-- FinEncoding for Clauses (List Literal). -/
abbrev finEncodingClause : FinEncoding Clause := listEncoding finEncodingLiteral

-- Ensure DecidableEq is available for Clause encoding alphabet
instance : DecidableEq finEncodingClause.Γ := by
  dsimp [finEncodingClause, listEncoding, finEncodingLiteral]
  infer_instance

/-- FinEncoding for CNF (List Clause). -/
def finEncodingCNF : FinEncoding CNF := listEncoding finEncodingClause

/-- A certificate for SAT is a finite list of (variable index, truth value) pairs. -/
abbrev SAT_Certificate := List (ℕ × Bool)

/-- DecidableEq instance for the alphabet of the pair encoding (Bool ⊕ Bool). -/
instance : DecidableEq (pairEncoding finEncodingNatBool finEncodingBoolBool).Γ := by
  dsimp [pairEncoding, finEncodingNatBool, finEncodingBoolBool, encodingNatBool]
  infer_instance

/-- FinEncoding for SAT certificates. 
    Use the efficient listEncoding over pairEncoding. -/
def finEncodingSATCertificate : FinEncoding SAT_Certificate :=
  listEncoding (pairEncoding finEncodingNatBool finEncodingBoolBool)

/-- Convert a certificate (list of pairs) to a full assignment.
    Variables not in the list default to `false`. -/
def assignmentOfCertificate (y : SAT_Certificate) : Assignment :=
  fun v => (y.find? (fun p => p.1 == v)).map (fun p => p.2) |>.getD false

theorem find?_map {α β : Type} (l : List α) (f : α → β) (p : β → Bool) :
    List.find? p (l.map f) = (List.find? (p ∘ f) l).map f := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons, List.find?_cons, List.find?_cons, ih]
    generalize h : p (f x) = b
    have h_comp : (p ∘ f) x = b := h
    rw [h_comp]
    cases b <;> rfl

theorem find?_key_eq_some {l : List ℕ} {v : ℕ} (hv : v ∈ l) :
    ∃ x, List.find? (fun n => n == v) l = some x ∧ x = v := by
  induction l with
  | nil => contradiction
  | cons x xs ih =>
    rw [List.find?_cons]
    by_cases h : x = v
    · use x; simp [h]
    · have h_ne : (x == v) = false := by simp [h]
      rw [h_ne]
      apply ih
      simp at hv
      cases hv with
      | inl h_eq => subst h_eq; contradiction
      | inr h_mem => exact h_mem

theorem find?_map_assignment {σ : Assignment} {l : List ℕ} {v : ℕ} (hv : v ∈ l) :
    List.find? (fun (p : ℕ × Bool) => p.1 == v) (l.map (fun v_inner => (v_inner, σ v_inner))) = some (v, σ v) := by
  rw [find?_map]
  have h_comp : (fun (p : ℕ × Bool) => p.1 == v) ∘ (fun v_inner => (v_inner, σ v_inner)) = (fun v_inner => v_inner == v) := by
    funext n; rfl
  rw [h_comp]
  rcases find?_key_eq_some hv with ⟨x, hx, hxv⟩
  rw [hx, hxv]
  rfl

theorem assignmentOfCertificate_eq_of_mem {σ : Assignment} {φ : CNF} {v : ℕ}
    (hv : v ∈ φ.vars) : assignmentOfCertificate ((φ.vars.dedup).map (fun v => (v, σ v))) v = σ v := by
  unfold assignmentOfCertificate
  have hv' : v ∈ φ.vars.dedup := List.mem_dedup.mpr hv
  rw [find?_map_assignment hv']
  rfl

/-- The SAT verifier relation: R(φ, y) iff y represents a satisfying assignment for φ. -/
def SAT_Verifier (φ : CNF) (y : SAT_Certificate) : Prop :=
  evalCNF (assignmentOfCertificate y) φ = true

/-- The Boolean version of the SAT verifier for use in P/NP definitions. -/
def SAT_Verifier_Bool (p : CNF × SAT_Certificate) : Bool :=
  evalCNF (assignmentOfCertificate p.2) p.1

/-- Citation axiom: evaluating a CNF formula under a given assignment is polynomial-time
    computable on a TM2. Standard result; see `artifacts/sat-polytime-citation.md` for
    verified citations (Arora-Barak, Sipser, Garey-Johnson). -/
axiom SAT_Verifier_polytime :
  Turing.TM2ComputableInPolyTime
    (Complexity.pairEncoding finEncodingCNF finEncodingSATCertificate)
    Computability.finEncodingBoolBool
    SAT_Verifier_Bool

/-! ## Bound Lemmas -/

private lemma sum_map_le_sum_map {α : Type} (l : List α) (f g : α → ℕ) (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp
    apply Nat.add_le_add
    · apply h; simp
    · apply ih; intro y hy; apply h; simp [hy]

private lemma sum_flatMap {α β : Type} (l : List α) (f : α → List β) (g : β → ℕ) :
    ((l.flatMap f).map g).sum = (l.map (fun x => ((f x).map g).sum)).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih]

/-- The sum of a sublist of natural numbers is less than or equal to the sum of the full list. -/
private theorem List.Sublist.sum_le_nat {l1 l2 : List ℕ} (h : l1.Sublist l2) : l1.sum ≤ l2.sum := by
  induction h with
  | slnil => simp
  | cons x h ih =>
    simp; omega
  | cons₂ x h ih =>
    simp; omega

/-- The number of distinct variables in a CNF formula is at most the formula encoding length. -/
private theorem vars_dedup_length_le_encoding (φ : CNF) :
    φ.vars.dedup.length ≤ (finEncodingCNF.encode φ).length := by
  have h_len_cnf : (finEncodingCNF.encode φ).length = (φ.map (fun c => (finEncodingClause.encode c).length + 1)).sum := 
    listEncoding_length _ _
  have h_vars_len : φ.vars.length = (φ.map (fun c => c.length)).sum := by
    unfold CNF.vars
    induction φ with
    | nil => simp
    | cons c cs ih => 
        simp [ih]
        have h_this : (Clause.vars c).length = c.length := by simp [Clause.vars]
        rw [h_this]
  have h_dedup_le : φ.vars.dedup.length ≤ φ.vars.length := (List.dedup_sublist _).length_le
  have h_clause_le (c : Clause) : c.length ≤ (finEncodingClause.encode c).length := by
    rw [listEncoding_length]
    have : ∀ l ∈ c, 1 ≤ (finEncodingLiteral.encode l).length + 1 := fun l _ => Nat.le_add_left 1 _
    have h_sum := sum_map_le_sum_map c (fun _ => 1) (fun l => (finEncodingLiteral.encode l).length + 1) this
    simp at h_sum
    exact h_sum
  have h_sum_clause_le : (φ.map (fun c => c.length)).sum ≤ (φ.map (fun c => (finEncodingClause.encode c).length)).sum := 
    sum_map_le_sum_map φ (fun c => c.length) (fun c => (finEncodingClause.encode c).length) (fun c _ => h_clause_le c)
  calc φ.vars.dedup.length
    _ ≤ φ.vars.length := h_dedup_le
    _ = (φ.map (fun c => c.length)).sum := h_vars_len
    _ ≤ (φ.map (fun c => (finEncodingClause.encode c).length)).sum := h_sum_clause_le
    _ ≤ (φ.map (fun c => (finEncodingClause.encode c).length + 1)).sum := 
        sum_map_le_sum_map φ _ _ (fun c _ => Nat.le_add_right _ _)
    _ = (finEncodingCNF.encode φ).length := h_len_cnf.symm

/-- The sum of encoding lengths of distinct variables is at most the formula encoding length. -/
private theorem sum_var_encoding_le (φ : CNF) :
    (φ.vars.dedup.map (fun v => (Computability.finEncodingNatBool.encode v).length)).sum
      ≤ (finEncodingCNF.encode φ).length := by
  have h_len_cnf : (finEncodingCNF.encode φ).length = (φ.map (fun c => (finEncodingClause.encode c).length + 1)).sum := 
    listEncoding_length _ _
  have h_vars_sum : (φ.vars.map (fun v => (finEncodingNatBool.encode v).length)).sum = 
      (φ.map (fun c => (c.vars.map (fun v => (finEncodingNatBool.encode v).length)).sum)).sum := by
    unfold CNF.vars
    rw [sum_flatMap]
    congr; funext c; rfl
  have h_dedup_le : (φ.vars.dedup.map (fun v => (finEncodingNatBool.encode v).length)).sum ≤ 
      (φ.vars.map (fun v => (finEncodingNatBool.encode v).length)).sum := by
    apply List.Sublist.sum_le_nat
    apply List.Sublist.map
    apply List.dedup_sublist
  have h_literal_le (l : Literal) : (finEncodingNatBool.encode l.var).length ≤ (finEncodingLiteral.encode l).length := by
    cases l <;> simp [finEncodingLiteral, sumEncoding, finEncodingNatBool] <;> apply Nat.le_add_left
  have h_clause_le (c : Clause) : (c.vars.map (fun v => (finEncodingNatBool.encode v).length)).sum ≤ 
      (finEncodingClause.encode c).length := by
    rw [listEncoding_length]
    have h_vars : (c.vars.map (fun v => (finEncodingNatBool.encode v).length)).sum = 
        (c.map (fun l => (finEncodingNatBool.encode l.var).length)).sum := by simp [Clause.vars]
    rw [h_vars]
    apply sum_map_le_sum_map
    intro l _
    calc (finEncodingNatBool.encode l.var).length
      _ ≤ (finEncodingLiteral.encode l).length := h_literal_le l
      _ ≤ (finEncodingLiteral.encode l).length + 1 := Nat.le_add_right _ _
  have h_sum_clause_le : (φ.map (fun c => (c.vars.map (fun v => (finEncodingNatBool.encode v).length)).sum)).sum ≤ 
      (φ.map (fun c => (finEncodingClause.encode c).length)).sum := 
    sum_map_le_sum_map φ _ _ (fun c _ => h_clause_le c)
  calc (φ.vars.dedup.map (fun v => (finEncodingNatBool.encode v).length)).sum
    _ ≤ (φ.vars.map (fun v => (finEncodingNatBool.encode v).length)).sum := h_dedup_le
    _ = (φ.map (fun c => (c.vars.map (fun v => (finEncodingNatBool.encode v).length)).sum)).sum := h_vars_sum
    _ ≤ (φ.map (fun c => (finEncodingClause.encode c).length)).sum := h_sum_clause_le
    _ ≤ (φ.map (fun c => (finEncodingClause.encode c).length + 1)).sum := 
        sum_map_le_sum_map φ _ _ (fun c _ => Nat.le_add_right _ _)
    _ = (finEncodingCNF.encode φ).length := h_len_cnf.symm

/-- The certificate encoding length is at most 3 times the formula encoding length.
    Consequence: |encode(y)| ≤ 3·N ≤ N² for N ≥ 3. -/
private theorem cert_encoding_le_cube (φ : CNF) (σ : Assignment) :
    let y := (φ.vars.dedup).map (fun v => (v, σ v))
    (finEncodingSATCertificate.encode y).length ≤ 3 * (finEncodingCNF.encode φ).length := by
  intro y
  have h_len_y : (finEncodingSATCertificate.encode y).length = (y.map (fun p => (finEncodingNatBool.encode p.1).length + 2)).sum := by
    rw [finEncodingSATCertificate, listEncoding_length]
    induction y with
    | nil => simp
    | cons p ps ih => 
      simp [ih, pairEncoding, finEncodingBoolBool, encodeBool]
      cases p; simp [encodeBool]; rfl
  have h_len_y_unfold : (finEncodingSATCertificate.encode y).length = 
      (φ.vars.dedup.map (fun v => (finEncodingNatBool.encode v).length + 2)).sum := by
    rw [h_len_y, List.map_map]; rfl
  have h_split : (φ.vars.dedup.map (fun v => (finEncodingNatBool.encode v).length + 2)).sum = 
      (φ.vars.dedup.map (fun v => (finEncodingNatBool.encode v).length)).sum + 2 * φ.vars.dedup.length := by
    induction φ.vars.dedup with
    | nil => simp
    | cons x xs ih => 
      simp [ih]
      omega
  calc (finEncodingSATCertificate.encode y).length
    _ = (φ.vars.dedup.map (fun v => (finEncodingNatBool.encode v).length)).sum + 2 * φ.vars.dedup.length := by
        rw [h_len_y_unfold, h_split]
    _ ≤ (finEncodingCNF.encode φ).length + 2 * (finEncodingCNF.encode φ).length := by
        apply Nat.add_le_add
        · exact sum_var_encoding_le φ
        · exact Nat.mul_le_mul_left 2 (vars_dedup_length_le_encoding φ)
    _ = 3 * (finEncodingCNF.encode φ).length := by ring

/-- SAT is in NP. -/
theorem SAT_in_NP : InNP finEncodingCNF SAT_Language := by
  /- Use SAT_Certificate as the witness type. -/
  refine ⟨SAT_Certificate, finEncodingSATCertificate, SAT_Verifier, 2, ?_, ?_⟩
  · /- The verifier runs in polynomial time.
       Citation axiom: SAT verification (evaluating a CNF formula under a given assignment)
       is polynomial-time computable. This is standard; see:
       - Arora & Barak (2009), Section 2.1, Example 2.2
       - Sipser (2012), Section 7.3, Page 296
       - Garey & Johnson (1979), Chapter 2, Theorem 2.1
       Full citation verification: artifacts/sat-polytime-citation.md -/
    unfold PolyTimeCheckingRelation InP
    exact ⟨SAT_Verifier_Bool, SAT_Verifier_polytime, fun ⟨φ, y⟩ => by
      simp [SAT_Verifier, SAT_Verifier_Bool]⟩
  · /- φ ∈ SAT ↔ ∃ y, |y| ≤ |φ|^2 ∧ SAT_Verifier φ y -/
    intro φ
    unfold SAT_Language Satisfiable SAT_Verifier
    constructor
    · /- Forward: SAT -> finite certificate -/
      intro hsat
      rcases hsat with ⟨σ, hσ⟩
      let y := (φ.vars.dedup).map (fun v => (v, σ v))
      refine ⟨y, ?_, ?_⟩
      · /- Bound: |encode y| ≤ |encode φ|² -/
        have h3 := cert_encoding_le_cube φ σ
        -- Strategy: |encode y| ≤ 3N ≤ N² for N ≥ 3.
        -- For N < 3, the formula has no variables (any literal needs ≥ 4 encoding
        -- symbols), so y = [] and |encode y| = 0 ≤ N².
        by_cases hge : (finEncodingCNF.encode φ).length ≥ 3
        · calc (finEncodingSATCertificate.encode y).length
              ≤ 3 * (finEncodingCNF.encode φ).length := h3
            _ ≤ (finEncodingCNF.encode φ).length ^ 2 := by
                let n := (finEncodingCNF.encode φ).length
                rw [pow_two]
                apply Nat.mul_le_mul_right
                exact hge
        · -- N < 3, so |dedup| ≤ N < 3, meaning at most 2 entries.
          -- But any formula with a variable has encoding length ≥ 4
          -- (tag + ≥1 nat bit + literal sep + clause sep).
          -- So N < 3 means no variables, y = [], |encode y| = 0.
          push_neg at hge
          have h_vars_nil : φ.vars.dedup = [] := by
            have h_len := vars_dedup_length_le_encoding φ
            have h_le_2 : φ.vars.dedup.length < 3 := Nat.le_trans h_len (Nat.le_of_lt hge)
            -- If length > 0, then at least one literal.
            -- Literal encoding length = 1 + |encodeNat v| + 1 (from list sep) >= 2.
            -- Clause encoding length = (sum of literal lens) + 1 >= 3.
            -- Formula encoding length = (sum of clause lens) + 1 >= 4.
            -- So if N < 3, then no literals.
            by_contra h_not_nil
            have h_pos : φ.vars.dedup.length > 0 := List.length_pos.mpr h_not_nil
            have h_exists : ∃ v, v ∈ φ.vars.dedup := List.exists_mem_of_length_pos h_pos
            rcases h_exists with ⟨v, hv⟩
            rw [List.mem_dedup, CNF.vars, List.mem_flatMap] at hv
            rcases hv with ⟨c, hc, hv_c⟩
            rw [Clause.vars, List.mem_map] at hv_c
            rcases hv_c with ⟨l, hl, _⟩
            -- Now we have a literal l in clause c in formula φ.
            have h_len_c : (finEncodingClause.encode c).length = 
                ((c.map (fun l => (finEncodingLiteral.encode l).length + 1)).sum) := listEncoding_length _ _
            have h_sum_c : (c.map (fun l => (finEncodingLiteral.encode l).length + 1)).sum ≥ 
                (finEncodingLiteral.encode l).length + 1 := List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map_of_mem _ hl)
            have h_len_phi : (finEncodingCNF.encode φ).length = (φ.map (fun c => (finEncodingClause.encode c).length + 1)).sum := listEncoding_length _ _
            have h_sum_phi : (φ.map (fun c => (finEncodingClause.encode c).length + 1)).sum ≥ 
                (finEncodingClause.encode c).length + 1 := List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map_of_mem _ hc)
            have h_total : (finEncodingCNF.encode φ).length ≥ ((finEncodingLiteral.encode l).length + 1) + 1 := by
              calc (finEncodingCNF.encode φ).length 
                _ ≥ (finEncodingClause.encode c).length + 1 := Nat.add_le_add_right h_sum_phi 1
                _ = ((c.map (fun l => (finEncodingLiteral.encode l).length + 1)).sum) + 1 + 1 := by rw [h_len_c]; rfl
                _ ≥ ((finEncodingLiteral.encode l).length + 1) + 1 + 1 := by linarith
            -- Literal length is at least 1.
            have h_lit_pos : (finEncodingLiteral.encode l).length ≥ 1 := by
              cases l <;> simp [finEncodingLiteral, sumEncoding, finEncodingNatBool]
            have h_total_3 : (finEncodingCNF.encode φ).length ≥ 3 := by linarith
            exact Nat.not_lt_of_ge h_total_3 hge
          have hy_nil : y = [] := by
            simp only [y]
            rw [h_vars_nil, List.map_nil]
          rw [hy_nil]
          simp [finEncodingSATCertificate, listEncoding]
      · /- SAT_Verifier φ y -/
        rw [← hσ]
        apply evalCNF_eq_of_vars_eq
        intro v hv
        apply assignmentOfCertificate_eq_of_mem hv
    · /- Backward: finite certificate -> SAT -/
      rintro ⟨y, _, hy⟩
      exact ⟨assignmentOfCertificate y, hy⟩

/-! ## 3-SAT

A restricted version where every clause has exactly 3 literals.
-/

/-- A clause has exactly 3 literals. -/
def isThreeLitClause (c : Clause) : Prop := c.length = 3

/-- A 3-CNF formula has all clauses of length 3. -/
def isThreeCNF (φ : CNF) : Prop := ∀ c ∈ φ, isThreeLitClause c

/-- The 3-SAT language: satisfiable formulas where every clause has 3 literals. -/
def ThreeSAT_Language (φ : CNF) : Prop :=
  isThreeCNF φ ∧ Satisfiable φ

/-! ## Basic Properties -/

/-- Empty formula is satisfiable (vacuously true — no clauses to satisfy). -/
theorem empty_satisfiable : Satisfiable [] := by
  exact ⟨fun _ => true, by simp [evalCNF]⟩

/-- A formula with an empty clause is unsatisfiable (empty disjunction is false). -/
theorem empty_clause_unsat (φ : CNF) (h : [] ∈ φ) : ¬Satisfiable φ := by
  intro ⟨σ, hsat⟩
  simp [evalCNF, List.all_eq_true] at hsat
  have := hsat [] h
  simp [evalClause] at this

end OpenLemma.Complexity.SAT
