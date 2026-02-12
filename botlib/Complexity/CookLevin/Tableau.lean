/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Cook-Levin Tableau: Variable definitions and constraint generation.
-/
import Mathlib.Computability.TMComputable
import Mathlib.Computability.Encoding
import Mathlib.Logic.Encodable.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import botlib.Complexity.Defs
import botlib.Complexity.SAT

namespace CookLevinTableau

open Computability OpenLemma.Complexity.SAT

/-! ## Read Depth Analysis -/

def stmtReadDepth {K : Type*} {Γ : K → Type*} {Λ : Type*} {σ : Type*} (k : K) [DecidableEq K] : Turing.TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => stmtReadDepth k q
  | .peek k' _ q => (if k' = k then 1 else 0) + stmtReadDepth k q
  | .pop k' _ q => (if k' = k then 1 else 0) + stmtReadDepth k q
  | .load _ q => stmtReadDepth k q
  | .branch _ q₁ q₂ => max (stmtReadDepth k q₁) (stmtReadDepth k q₂)
  | .goto _ => 0
  | .halt => 0

noncomputable def maxReadDepth (V : Turing.FinTM2) (k : V.K) : ℕ :=
  (Finset.univ (α := V.Λ)).fold max 0 (fun l => stmtReadDepth k (V.m l))

/-! ## Tableau Variables -/

inductive TableauVar (V : Turing.FinTM2) where
  | label (i : ℕ) (l : Option V.Λ) : TableauVar V
  | state (i : ℕ) (s : V.σ) : TableauVar V
  | stkElem (i : ℕ) (k : V.K) (j : ℕ) (γ : V.Γ k) : TableauVar V
  | stkLen (i : ℕ) (k : V.K) (len : ℕ) : TableauVar V
  | cert (j : ℕ) : TableauVar V

noncomputable instance TableauVar.encodable {V : Turing.FinTM2} [Encodable V.Λ] [Encodable V.σ] [Encodable V.K]
    [∀ k, Encodable (V.Γ k)] : Encodable (TableauVar V) :=
  let iso : TableauVar V ≃ (ℕ × Option V.Λ) ⊕ (ℕ × V.σ) ⊕ (Σ k : V.K, ℕ × ℕ × V.Γ k) ⊕ (ℕ × V.K × ℕ) ⊕ ℕ := {
    toFun := fun v => match v with
      | .label i l => Sum.inl (i, l)
      | .state i s => Sum.inr (Sum.inl (i, s))
      | .stkElem i k j γ => Sum.inr (Sum.inr (Sum.inl (⟨k, i, j, γ⟩ : (Σ k, ℕ × ℕ × V.Γ k))))
      | .stkLen i k len => Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, k, len))))
      | .cert j => Sum.inr (Sum.inr (Sum.inr (Sum.inr j)))
    invFun := fun x => match x with
      | Sum.inl (i, l) => .label i l
      | Sum.inr (Sum.inl (i, s)) => .state i s
      | Sum.inr (Sum.inr (Sum.inl ⟨k, i, j, γ⟩)) => .stkElem i k j γ
      | Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, k, len)))) => .stkLen i k len
      | Sum.inr (Sum.inr (Sum.inr (Sum.inr j))) => .cert j
    left_inv := fun v => by cases v <;> rfl
    right_inv := fun x => by rcases x with ⟨i, l⟩ | ⟨i, s⟩ | ⟨k, i, j, γ⟩ | ⟨i, k, len⟩ | j <;> rfl
  }
  Encodable.ofEquiv _ iso

/-! ## Constraints (Placeholders for build) -/

structure Params (V : Turing.FinTM2) where
  timeBound : ℕ
  maxStackDepth : ℕ

noncomputable def consistencyConstraints {V : Turing.FinTM2} [Encodable V.Λ] [Encodable V.σ] [Encodable V.K] [∀ k, Encodable (V.Γ k)]
  [Fintype V.Λ] [Fintype V.σ] [Fintype V.K] [∀ k, Fintype (V.Γ k)] (params : Params V) : CNF :=
  sorry

noncomputable def initialConstraints {V : Turing.FinTM2} [Encodable V.Λ] [Encodable V.σ] [Encodable V.K] [∀ k, Encodable (V.Γ k)]
  [DecidableEq V.K] (params : Params V) (inputContents : List (V.Γ V.k₀)) : CNF :=
  sorry

noncomputable def transitionConstraints {V : Turing.FinTM2} [Encodable V.Λ] [Encodable V.σ] [Encodable V.K] [∀ k, Encodable (V.Γ k)]
  [Fintype V.Λ] [Fintype V.σ] [Fintype V.K] [∀ k, Fintype (V.Γ k)]
  [DecidableEq V.K] [∀ k, DecidableEq (V.Γ k)] (params : Params V) : CNF :=
  sorry

noncomputable def framePreservation {V : Turing.FinTM2} [Encodable V.Λ] [Encodable V.σ] [Encodable V.K] [∀ k, Encodable (V.Γ k)]
  [Fintype V.Λ] [Fintype V.σ] [Fintype V.K] [∀ k, Fintype (V.Γ k)] (params : Params V) : CNF :=
  sorry

noncomputable def acceptanceConstraints {V : Turing.FinTM2} [Encodable V.Λ] [Encodable V.σ] [Encodable V.K] [∀ k, Encodable (V.Γ k)]
  (params : Params V) : CNF :=
  sorry

noncomputable def tableauFormula
    (V : Turing.FinTM2) [DecidableEq V.K]
    [Encodable V.Λ] [Encodable V.σ] [Encodable V.K]
    [∀ k, Encodable (V.Γ k)] [∀ k, Fintype (V.Γ k)] [∀ k, DecidableEq (V.Γ k)]
    [Fintype V.Λ] [Fintype V.σ]
    (params : Params V) (inputContents : List (V.Γ V.k₀)) : CNF :=
  consistencyConstraints params ++ initialConstraints params inputContents ++
  transitionConstraints params ++ framePreservation params ++ acceptanceConstraints params

end CookLevinTableau
