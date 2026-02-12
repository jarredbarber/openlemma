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

namespace OpenLemma.Complexity.SAT

open Computability

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

/-- A CNF formula is satisfiable if some assignment satisfies it. -/
def Satisfiable (φ : CNF) : Prop :=
  ∃ σ : Assignment, evalCNF σ φ = true

/-- The SAT language: the set of satisfiable CNF formulas. -/
def SAT_Language : CNF → Prop := Satisfiable

/-! ## Encodings

We define standard finite encodings for SAT-related types.
These use a binary encoding of the natural numbers via `Encodable`.
-/

/-- Generic FinEncoding for any Encodable type using binary encoding of its index. -/
def finEncodingOfEncodable (α : Type) [Encodable α] : FinEncoding α where
  Γ := Bool
  encode x := finEncodingNatBool.encode (Encodable.encode x)
  decode l := (finEncodingNatBool.decode l).bind Encodable.decode
  decode_encode x := by
    simp [finEncodingNatBool.decode_encode, Encodable.encodek]
  ΓFin := Bool.fintype

/-- FinEncoding for Literals. -/
def finEncodingLiteral : FinEncoding Literal := finEncodingOfEncodable Literal

/-- FinEncoding for Clauses. -/
def finEncodingClause : FinEncoding Clause := finEncodingOfEncodable Clause

/-- FinEncoding for CNF formulas. -/
def finEncodingCNF : FinEncoding CNF := finEncodingOfEncodable CNF

/-- A certificate for SAT is a finite list of (variable index, truth value) pairs. -/
abbrev SAT_Certificate := List (ℕ × Bool)

/-- FinEncoding for SAT certificates. -/
def finEncodingSATCertificate : FinEncoding SAT_Certificate := finEncodingOfEncodable SAT_Certificate

/-- Convert a certificate (list of pairs) to a full assignment.
    Variables not in the list default to `false`. -/
def assignmentOfCertificate (y : SAT_Certificate) : Assignment :=
  fun v => (y.find? (fun p => p.1 = v)).map (fun p => p.2) |>.getD false

/-- The SAT verifier relation: R(φ, y) iff y represents a satisfying assignment for φ. -/
def SAT_Verifier (φ : CNF) (y : SAT_Certificate) : Prop :=
  evalCNF (assignmentOfCertificate y) φ = true

/-- The Boolean version of the SAT verifier for use in P/NP definitions. -/
def SAT_Verifier_Bool (p : CNF × SAT_Certificate) : Bool :=
  evalCNF (assignmentOfCertificate p.2) p.1

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
