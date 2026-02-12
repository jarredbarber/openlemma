/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Definition of the Boolean Satisfiability Problem (SAT) as a formal language.
This is the target language for the Cook-Levin theorem.

Trust level: 🟡 Definitions only — Cook-Levin proof pending.
-/
import Mathlib.Computability.Encoding

namespace OpenLemma.Complexity.SAT

/-! ## Boolean Formulas

We define propositional formulas over variables indexed by ℕ.
This is sufficient for Cook-Levin since the reduction produces
formulas with finitely many variables.
-/

/-- A literal is a variable (positive) or its negation. -/
inductive Literal : Type where
  | pos : ℕ → Literal
  | neg : ℕ → Literal
  deriving DecidableEq, Repr

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

/-- A CNF formula is satisfiable if some assignment satisfies it. -/
def Satisfiable (φ : CNF) : Prop :=
  ∃ σ : Assignment, evalCNF σ φ = true

/-- The SAT language: the set of satisfiable CNF formulas. -/
def SAT_Language : CNF → Prop := Satisfiable

/-! ## Encodings -/

open Computability

/-- Helper: split a list of options by `none`. -/
private def splitByNone {Γ : Type} : List (Option Γ) → List (List Γ)
  | [] => []
  | some g :: rest =>
    match splitByNone rest with
    | [] => [[g]]
    | x :: xs => (g :: x) :: xs
  | none :: rest => [] :: splitByNone rest

private theorem splitByNone_encode {Γ : Type} (l : List Γ) (rest : List (Option Γ)) :
    splitByNone (l.map some ++ none :: rest) =
    l :: splitByNone rest := by
  induction l with
  | nil => rfl
  | cons g gs ih => simp [splitByNone, ih]

/-- Generic encoding for lists given an encoding for elements. -/
def listEncoding {α : Type} (ea : FinEncoding α) : FinEncoding (List α) where
  Γ := Option ea.Γ
  encode l := l.flatMap (fun a => (ea.encode a).map some ++ [none])
  decode l := (splitByNone l).mapM ea.decode
  decode_encode l := by
    induction l with
    | nil => rfl
    | cons a as ih =>
      simp [List.flatMap, splitByNone_encode, ea.decode_encode]
      erw [ih]
      rfl
  ΓFin := inferInstance

/-- FinEncoding for literals. -/
def literalFinEncoding : FinEncoding Literal where
  Γ := Γ'
  encode l := match l with
    | .pos n => Γ'.bit true :: encodingNatΓ'.encode n
    | .neg n => Γ'.bit false :: encodingNatΓ'.encode n
  decode l := match l with
    | Γ'.bit b :: l' => (encodingNatΓ'.decode l').map (if b then Literal.pos else Literal.neg)
    | _ => none
  decode_encode l := by
    cases l <;> simp [encodingNatΓ'.decode_encode]
  ΓFin := inferInstance

/-- FinEncoding for clauses. -/
def clauseFinEncoding : FinEncoding Clause := listEncoding literalFinEncoding

/-- FinEncoding for CNF formulas. -/
def cnfFinEncoding : FinEncoding CNF := listEncoding clauseFinEncoding

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
