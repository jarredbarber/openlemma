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

noncomputable instance {V : Turing.FinTM2} [Encodable V.Λ] [Encodable V.σ] [Encodable V.K]
    [∀ k, Encodable (V.Γ k)] : Encodable (TableauVar V) :=
  let iso : TableauVar V ≃ (ℕ × Option V.Λ) ⊕ (ℕ × V.σ) ⊕ (Σ k : V.K, ℕ × ℕ × V.Γ k) ⊕ (ℕ × V.K × ℕ) ⊕ ℕ := {
    toFun := fun v => match v with
      | .label i l => Sum.inl (i, l)
      | .state i s => Sum.inr (Sum.inl (i, s))
      | .stkElem i k j γ => Sum.inr (Sum.inr (Sum.inl (⟨k, i, j, γ⟩)))
      | .stkLen i k len => Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, k, len))))
      | .cert j => Sum.inr (Sum.inr (Sum.inr (Sum.inr j)))
    invFun := fun x => match x with
      | Sum.inl (i, l) => .label i l
      | Sum.inr (Sum.inl (i, s)) => .state i s
      | Sum.inr (Sum.inr (Sum.inl (⟨k, i, j, γ⟩))) => .stkElem i k j γ
      | Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, k, len)))) => .stkLen i k len
      | Sum.inr (Sum.inr (Sum.inr (Sum.inr j))) => .cert j
    left_inv := fun v => by cases v <;> rfl
    right_inv := fun x => by rcases x with ⟨i, l⟩ | ⟨i, s⟩ | ⟨k, i, j, γ⟩ | ⟨i, k, len⟩ | j <;> rfl
  }
  Encodable.ofEquiv _ iso

noncomputable def tLit {V : Turing.FinTM2} [Encodable V.Λ] [Encodable V.σ] [Encodable V.K]
    [∀ k, Encodable (V.Γ k)] (v : TableauVar V) (b : Bool) : Literal :=
  if b then Literal.pos (Encodable.encode v) else Literal.neg (Encodable.encode v)

noncomputable def exactlyOne {V : Turing.FinTM2} [Encodable V.Λ] [Encodable V.σ] [Encodable V.K]
    [∀ k, Encodable (V.Γ k)] (vars : List (TableauVar V)) : CNF :=
  (vars.map (fun v => tLit v true)) :: (vars.tails.flatMap fun
    | [] => []
    | v :: rest => rest.map (fun w => [tLit v false, tLit w false]))

/-! ## Constraints -/

structure Params (V : Turing.FinTM2) where
  timeBound : ℕ
  maxStackDepth : ℕ

noncomputable def consistencyConstraints {V : Turing.FinTM2} (params : Params V)
  [Encodable V.Λ] [Encodable V.σ] [Encodable V.K] [∀ k, Encodable (V.Γ k)]
  [∀ k, Fintype (V.Γ k)] : CNF :=
  (List.range (params.timeBound + 1)).flatMap (fun i =>
    exactlyOne (Finset.univ.toList.map (TableauVar.label i))) ++
  (List.range (params.timeBound + 1)).flatMap (fun i =>
    exactlyOne (Finset.univ.toList.map (TableauVar.state i))) ++
  (List.range (params.timeBound + 1)).flatMap (fun i =>
    Finset.univ.toList.flatMap (fun k =>
      (List.range params.maxStackDepth).flatMap (fun j =>
        exactlyOne (Finset.univ.toList.map (TableauVar.stkElem i k j))))) ++
  (List.range (params.timeBound + 1)).flatMap (fun i =>
    Finset.univ.toList.flatMap (fun k =>
      exactlyOne ((List.range (params.maxStackDepth + 1)).map (TableauVar.stkLen i k))))

noncomputable def initialConstraints {V : Turing.FinTM2} (params : Params V)
  [Encodable V.Λ] [Encodable V.σ] [Encodable V.K] [∀ k, Encodable (V.Γ k)]
  [DecidableEq V.K] (inputContents : List (V.Γ V.k₀)) : CNF :=
  [[tLit (TableauVar.label 0 (some V.main)) true]] ++
  [[tLit (TableauVar.state 0 V.initialState) true]] ++
  [[tLit (TableauVar.stkLen 0 V.k₀ inputContents.length) true]] ++
  (inputContents.zipIdx.map (fun ⟨γ, j⟩ => [tLit (TableauVar.stkElem 0 V.k₀ j γ) true])) ++
  (Finset.univ.toList.flatMap (fun k => if k = V.k₀ then [] else [[tLit (TableauVar.stkLen 0 k 0) true]]))

noncomputable def transitionClausesAt {V : Turing.FinTM2} (params : Params V)
  [Encodable V.Λ] [Encodable V.σ] [Encodable V.K] [∀ k, Encodable (V.Γ k)]
  [∀ k, Fintype (V.Γ k)] [DecidableEq V.K] [∀ k, DecidableEq (V.Γ k)] (i : ℕ) : CNF :=
  let topsList : List (∀ k : V.K, Option (V.Γ k)) := Finset.univ.toList
  Finset.univ (α := Option V.Λ).toList.flatMap fun l =>
    Finset.univ (α := V.σ).toList.flatMap fun s =>
      topsList.flatMap fun tops =>
        let antecedent : List Literal :=
          [tLit (TableauVar.label i l) false, tLit (TableauVar.state i s) false] ++
          Finset.univ.toList.flatMap (fun k => match tops k with
            | none => [tLit (TableauVar.stkLen i k 0) false]
            | some γ => [tLit (TableauVar.stkElem i k 0 γ) false])
        let stkVals : ∀ k : V.K, List (V.Γ k) := fun k => match tops k with | none => [] | some γ => [γ]
        match l with
        | none =>
          [antecedent ++ [tLit (TableauVar.label (i+1) none) true],
           antecedent ++ [tLit (TableauVar.state (i+1) s) true]] ++
          Finset.univ.toList.flatMap fun k => match tops k with
            | none => [antecedent ++ [tLit (TableauVar.stkLen (i+1) k 0) true]]
            | some γ => [antecedent ++ [tLit (TableauVar.stkElem (i+1) k 0 γ) true]]
        | some lbl =>
          let res := Turing.TM2.stepAux (V.m lbl) s stkVals
          [antecedent ++ [tLit (TableauVar.label (i+1) res.l) true],
           antecedent ++ [tLit (TableauVar.state (i+1) res.var) true]] ++
          Finset.univ.toList.flatMap fun k =>
            let ns := res.stk k
            [antecedent ++ [tLit (TableauVar.stkLen (i+1) k ns.length) true]] ++
            ns.zipIdx.map (fun ⟨γ, j⟩ => antecedent ++ [tLit (TableauVar.stkElem (i+1) k j γ) true])

noncomputable def transitionConstraints {V : Turing.FinTM2} (params : Params V)
  [Encodable V.Λ] [Encodable V.σ] [Encodable V.K] [∀ k, Encodable (V.Γ k)]
  [∀ k, Fintype (V.Γ k)] [DecidableEq V.K] [∀ k, DecidableEq (V.Γ k)] : CNF :=
  (List.range params.timeBound).flatMap (fun i => transitionClausesAt params i)

noncomputable def framePreservation {V : Turing.FinTM2} (params : Params V)
  [Encodable V.Λ] [Encodable V.σ] [Encodable V.K] [∀ k, Encodable (V.Γ k)]
  [∀ k, Fintype (V.Γ k)] : CNF :=
  (List.range params.timeBound).flatMap fun i =>
    Finset.univ.toList.flatMap fun k =>
      (List.range params.maxStackDepth).flatMap fun j =>
        Finset.univ.toList.flatMap fun γ =>
          (List.range (params.maxStackDepth + 1)).filterMap fun len =>
            if j + maxReadDepth V k < len then
              some [tLit (TableauVar.stkLen i k len) false,
                    tLit (TableauVar.stkElem i k j γ) false,
                    tLit (TableauVar.stkElem (i + 1) k j γ) true]
            else none

noncomputable def acceptanceConstraints {V : Turing.FinTM2} (params : Params V)
  [Encodable V.Λ] [Encodable V.σ] [Encodable V.K] [∀ k, Encodable (V.Γ k)] : CNF :=
  [(List.range (params.timeBound + 1)).map (fun i => tLit (TableauVar.label i none) true)]

noncomputable def tableauFormula
    (V : Turing.FinTM2) [DecidableEq V.K]
    [Encodable V.Λ] [Encodable V.σ] [Encodable V.K]
    [∀ k, Encodable (V.Γ k)] [∀ k, Fintype (V.Γ k)] [∀ k, DecidableEq (V.Γ k)]
    (params : Params V) (inputContents : List (V.Γ V.k₀)) : CNF :=
  consistencyConstraints params ++ initialConstraints params inputContents ++
  transitionConstraints params ++ framePreservation params ++ acceptanceConstraints params

end CookLevinTableau
