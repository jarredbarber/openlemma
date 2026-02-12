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
import Batteries.Data.List.Basic
import botlib.Complexity.Defs

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
  sorry

theorem evalCNF_eq_of_vars_eq {σ1 σ2 : Assignment} {φ : CNF}
    (h : ∀ v ∈ φ.vars, σ1 v = σ2 v) : evalCNF σ1 φ = evalCNF σ2 φ := by
  sorry

/-- A CNF formula is satisfiable if some assignment satisfies it. -/
def Satisfiable (φ : CNF) : Prop :=
  ∃ σ : Assignment, evalCNF σ φ = true

/-- The SAT language: the set of satisfiable CNF formulas. -/
def SAT_Language : CNF → Prop := Satisfiable

/-! ## Encodings

We define standard finite encodings for SAT-related types.
We ensure these encodings are polynomial-time efficient (linear in value/structure).
-/

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
      sorry -- Omitted for now
    ΓFin := inferInstance }

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
  fun v => (y.find? (fun p => p.1 = v)).map (fun p => p.2) |>.getD false

theorem assignmentOfCertificate_eq_of_mem {σ : Assignment} {φ : CNF} {v : ℕ}
    (hv : v ∈ φ.vars) : assignmentOfCertificate ((φ.vars.eraseDups).map (fun v => (v, σ v))) v = σ v := by
  sorry

/-- The SAT verifier relation: R(φ, y) iff y represents a satisfying assignment for φ. -/
def SAT_Verifier (φ : CNF) (y : SAT_Certificate) : Prop :=
  evalCNF (assignmentOfCertificate y) φ = true

/-- The Boolean version of the SAT verifier for use in P/NP definitions. -/
def SAT_Verifier_Bool (p : CNF × SAT_Certificate) : Bool :=
  evalCNF (assignmentOfCertificate p.2) p.1

/-- SAT is in NP. -/
theorem SAT_in_NP : InNP finEncodingCNF SAT_Language := by
  /- Use SAT_Certificate as the witness type. -/
  refine ⟨SAT_Certificate, finEncodingSATCertificate, SAT_Verifier, 2, ?_, ?_⟩
  · /- The verifier runs in polynomial time. -/
    sorry
  · /- φ ∈ SAT ↔ ∃ y, |y| ≤ |φ|^2 ∧ SAT_Verifier φ y -/
    intro φ
    unfold SAT_Language Satisfiable SAT_Verifier
    constructor
    · /- Forward: SAT -> finite certificate -/
      intro hsat
      rcases hsat with ⟨σ, hσ⟩
      let y := (φ.vars.eraseDups).map (fun v => (v, σ v))
      refine ⟨y, ?_, ?_⟩
      · /- Bound: |y| ≤ |φ|^2 -/
        sorry
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
