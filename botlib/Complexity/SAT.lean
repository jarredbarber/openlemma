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

/-- Raw encoding for `Sum ℕ ℕ` via tagged concatenation of binary `ℕ` encodings.
    Built from `sumEncoding` over `finEncodingNatBool`. -/
abbrev literalSumEncoding : FinEncoding (Sum ℕ ℕ) :=
  sumEncoding (ea := finEncodingNatBool) (eb := finEncodingNatBool)

instance : DecidableEq literalSumEncoding.Γ :=
  inferInstanceAs (DecidableEq (Sum Bool (Sum Bool Bool)))

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

/-- First index of `a` in `l`, or `l.length` if absent. DecidableEq-based (no BEq). -/
def findPos [DecidableEq α] (a : α) (l : List α) : ℕ :=
  match l with
  | [] => 0
  | b :: l' => if a = b then 0 else findPos a l' + 1

/-- `findPos a l` returns a valid index holding `a`, whenever `a ∈ l`. -/
theorem findPos_mem [DecidableEq α] {a : α} {l : List α} (h : a ∈ l) :
    l[findPos a l]? = some a := by
  induction l with
  | nil => simp at h
  | cons b l' ih =>
    by_cases heq : a = b
    · simp [findPos, heq, List.getElem?_cons]
    · have ha' : a ∈ l' := by simpa [heq] using h
      have hih := ih ha'
      simp [findPos, heq, List.getElem?_cons, hih, Nat.add_sub_cancel]

/-- Pointwise `f a ≤ g a` lifts to sums (by induction on the list). -/
lemma sum_map_le {α : Type*} (l : List α) (f g : α → ℕ) (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a l' ih =>
    have ha : f a ≤ g a := h a (by simp)
    have hI : (l'.map f).sum ≤ (l'.map g).sum := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    simp only [List.map_cons, List.sum_cons]; omega

/-- Build an assignment from a raw-bit certificate `cert` and a formula `φ`:
    variable `v` is looked up by its **position** in `φ.vars.dedup`, defaulting to `false`.
    Position-based (not index-based) so sparse high-index variables are handled by a
    certificate whose length is polynomial in `|enc(φ)|`, not in the max variable index. -/
def assignmentFromBits (cert : List Bool) (φ : CNF) : Assignment :=
  fun v => cert[findPos v φ.vars.dedup]? |>.getD false

/-- The SAT verifier on a raw-bit certificate: evaluate `φ` under the position-indexed
    assignment extracted from `cert`. -/
def SAT_VerifierBits (p : CNF × List Bool) : Bool :=
  evalCNF (assignmentFromBits p.2 p.1) p.1

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

/-- SAT is in NP.
    Certificate: a raw bit-string `cert` of length `|enc(φ)|` (bound `k = 1`), interpreted as
    the satisfying assignment indexed by position in `φ.vars.dedup`. The verifier evaluates
    `φ` under this assignment in polynomial time. -/
theorem SAT_in_NP : InNP finEncodingCNF SAT_Language := by
  let R := fun (φ : CNF) (cert : List Bool) => evalCNF (assignmentFromBits cert φ) φ = true
  have hg_comp : Nonempty
      (_root_.Turing.TM2ComputableInPolyTime
        (pairEncoding finEncodingCNF finEncodingBoolList) finEncodingBoolBool SAT_VerifierBits) := sorry
  refine ⟨R, 1, SAT_VerifierBits, hg_comp, ?_⟩
  refine ⟨?_, ?_⟩
  · intro φ cert; rfl
  · -- `∀ φ, SAT_Language φ ↔ ∃ cert, |cert| = |enc φ| ∧ R φ cert`
    intro φ
    rw [show (finEncodingCNF.encode φ).length ^ 1 = (finEncodingCNF.encode φ).length from Nat.pow_one _]
    refine ⟨?_, ?_⟩
    · -- (→): from a satisfying assignment σ, build a cert (the σ-bits over φ.vars.dedup,
      --       padded to |enc φ|) and show `assignmentFromBits cert φ` agrees with σ on φ.vars.
      rintro ⟨σ, hσ⟩
      -- Narrowly-scoped sorry: encoding-length lower bound `|φ.vars.dedup| ≤ |enc φ|`.
      -- Needed to pad the cert to exactly |enc φ|. The bound holds (each literal encodes to
      -- ≥1 symbol, so |enc φ| ≥ #literals = |φ.vars| ≥ |dedup|) but the proof requires
      -- unwinding the nested `listEncoding` length formula and is deferred.
      have hdedup_len : φ.vars.dedup.length ≤ (finEncodingCNF.encode φ).length := by
        -- |dedup| ≤ |φ.vars| ≤ Σ|c| ≤ Σ(|enc clause c| + 1) = |enc φ|.
        -- Each clause encodes to ≥1 symbol per literal, so |enc clause c| ≥ |c|.
        have hd : φ.vars.dedup.length ≤ φ.vars.length :=
          List.Sublist.length_le (List.dedup_sublist φ.vars)
        have hvars : φ.vars.length = (φ.map (fun c => c.length)).sum := by
          show (φ.flatMap (fun c => c.map Literal.var)).length = (φ.map (fun c => c.length)).sum
          rw [List.length_flatMap]
          simp only [List.length_map]
        have hclause : ∀ c ∈ φ, c.length ≤ (finEncodingClause.encode c).length := by
          intro c _
          show c.length ≤ ((listEncoding finEncodingLiteral).encode c).length
          rw [listEncoding_length]
          have hL : (c.map (fun l => (finEncodingLiteral.encode l).length + 1)).length = c.length := by
            rw [List.length_map]
          rw [← hL]
          apply List.length_le_sum_of_one_le
          intro n hn
          obtain ⟨l, _, rfl⟩ := List.mem_map.mp hn
          omega
        have h2 : (φ.map (fun c => c.length)).sum
            ≤ (φ.map (fun c => (finEncodingClause.encode c).length + 1)).sum := by
          apply sum_map_le
          intro c hc
          have := hclause c hc
          omega
        have henc : (φ.map (fun c => (finEncodingClause.encode c).length + 1)).sum
            = (finEncodingCNF.encode φ).length := by
          show (φ.map (fun c => (finEncodingClause.encode c).length + 1)).sum
              = ((listEncoding finEncodingClause).encode φ).length
          rw [listEncoding_length]
        calc φ.vars.dedup.length ≤ φ.vars.length := hd
          _ = (φ.map (fun c => c.length)).sum := hvars
          _ ≤ (φ.map (fun c => (finEncodingClause.encode c).length + 1)).sum := h2
          _ = (finEncodingCNF.encode φ).length := henc
      set cert : List Bool :=
          φ.vars.dedup.map σ ++
            List.replicate ((finEncodingCNF.encode φ).length - φ.vars.dedup.length) false
        with hcert
      refine ⟨cert, ?_, ?_⟩
      · -- |cert| = |enc φ|
        rw [hcert, List.length_append, List.length_map, List.length_replicate]; omega
      · -- evalCNF (assignmentFromBits cert φ) φ = true  (cert reproduces σ on φ.vars)
        have heq : evalCNF (assignmentFromBits cert φ) φ = evalCNF σ φ :=
          evalCNF_eq_of_vars_eq (by
            intro v hv
            have hvD : v ∈ φ.vars.dedup := List.mem_dedup.mpr hv
            have hfp : φ.vars.dedup[findPos v φ.vars.dedup]? = some v := findPos_mem hvD
            have hfp_lt : findPos v φ.vars.dedup < φ.vars.dedup.length := by
              by_contra hC
              rw [List.getElem?_eq_none_iff.mpr (by omega)] at hfp
              simp at hfp
            have hfp_lt' : findPos v φ.vars.dedup < (φ.vars.dedup.map σ).length := by
              rw [List.length_map]; exact hfp_lt
            show assignmentFromBits cert φ v = σ v
            unfold assignmentFromBits
            rw [hcert, List.getElem?_append_left hfp_lt', List.getElem?_map, hfp]
            simp)
        show evalCNF (assignmentFromBits cert φ) φ = true
        rw [heq]; exact hσ
    · -- (←): the cert itself is the witness assignment.
      rintro ⟨cert, hlen, hR⟩
      exact ⟨assignmentFromBits cert φ, hR⟩

end OpenLemma.Complexity.SAT
