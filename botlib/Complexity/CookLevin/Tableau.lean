/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Cook-Levin Tableau: Variable definitions and constraint generation for the
Cook-Levin reduction using the "forbidden windows" approach.

Design reference: `proofs/cook-levin-forbidden-windows-design.md`
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

/-- The "read depth" of a statement on stack k: how many elements from the top
    the statement may inspect (via pop or peek). -/
def stmtReadDepth {K : Type*} {Γ : K → Type*} {Λ : Type*} {σ : Type*} (k : K) [DecidableEq K] : Turing.TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => stmtReadDepth k q
  | .peek k' _ q => (if k' = k then 1 else 0) + stmtReadDepth k q
  | .pop k' _ q => (if k' = k then 1 else 0) + stmtReadDepth k q
  | .load _ q => stmtReadDepth k q
  | .branch _ q₁ q₂ => max (stmtReadDepth k q₁) (stmtReadDepth k q₂)
  | .goto _ => 0
  | .halt => 0

/-- Maximum read depth across all labels of a Turing.FinTM2 machine on stack `k`. -/
noncomputable def maxReadDepth (V : Turing.FinTM2) (k : V.K) : ℕ :=
  (Finset.univ (α := V.Λ)).fold max 0 (fun l => stmtReadDepth k (V.m l))

/-- A FinTM2 has bounded read depth when every instruction reads ≤ 1 stack element.
    Note: uses the FinTM2's bundled DecidableEq instance for stmtReadDepth. -/
def BoundedReadDepth (V : Turing.FinTM2) : Prop :=
  ∀ (lbl : V.Λ) (k : V.K), @stmtReadDepth V.K V.Γ V.Λ V.σ k V.decidableEqK (V.m lbl) ≤ 1

/-! ## Tableau Variables -/

/-- Propositional variables for the Cook-Levin reduction. -/
inductive TableauVar (V : Turing.FinTM2) where
  | label (i : ℕ) (l : Option V.Λ) : TableauVar V
  | state (i : ℕ) (s : V.σ) : TableauVar V
  | stkElem (i : ℕ) (k : V.K) (j : ℕ) (γ : V.Γ k) : TableauVar V
  | stkLen (i : ℕ) (k : V.K) (len : ℕ) : TableauVar V
  | cert (j : ℕ) : TableauVar V

/-- Map TableauVar to a large sum type for Encodable derivation. -/
private def TableauVar.toSum {V : Turing.FinTM2} : TableauVar V →
    (ℕ × Option V.Λ) ⊕ (ℕ × V.σ) ⊕ (Σ k : V.K, ℕ × ℕ × V.Γ k) ⊕ (ℕ × V.K × ℕ) ⊕ ℕ
  | .label i l => Sum.inl (i, l)
  | .state i s => Sum.inr (Sum.inl (i, s))
  | .stkElem i k j γ => Sum.inr (Sum.inr (Sum.inl ⟨k, i, j, γ⟩))
  | .stkLen i k len => Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, k, len))))
  | .cert j => Sum.inr (Sum.inr (Sum.inr (Sum.inr j)))

/-- Map from sum type back to TableauVar. -/
private def TableauVar.ofSum {V : Turing.FinTM2} :
    (ℕ × Option V.Λ) ⊕ (ℕ × V.σ) ⊕ (Σ k : V.K, ℕ × ℕ × V.Γ k) ⊕ (ℕ × V.K × ℕ) ⊕ ℕ → TableauVar V
  | Sum.inl (i, l) => .label i l
  | Sum.inr (Sum.inl (i, s)) => .state i s
  | Sum.inr (Sum.inr (Sum.inl ⟨k, i, j, γ⟩)) => .stkElem i k j γ
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, k, len)))) => .stkLen i k len
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr j))) => .cert j

noncomputable instance TableauVar.encodable {V : Turing.FinTM2} [Encodable V.Λ] [Encodable V.σ] [Encodable V.K]
    [∀ k, Encodable (V.Γ k)] : Encodable (TableauVar V) :=
  Encodable.ofEquiv _ {
    toFun := TableauVar.toSum,
    invFun := TableauVar.ofSum,
    left_inv := fun v => by cases v <;> rfl,
    right_inv := fun x => by rcases x with ⟨i, l⟩ | ⟨i, s⟩ | ⟨k, i, j, γ⟩ | ⟨i, k, len⟩ | j <;> rfl
  }

noncomputable def tLit (V : Turing.FinTM2) [Encodable V.Λ] [Encodable V.σ] [Encodable V.K]
    [∀ k, Encodable (V.Γ k)] (v : TableauVar V) (b : Bool) : Literal :=
  if b then Literal.pos (Encodable.encode v) else Literal.neg (Encodable.encode v)

noncomputable def exactlyOne (V : Turing.FinTM2) [Encodable V.Λ] [Encodable V.σ] [Encodable V.K]
    [∀ k, Encodable (V.Γ k)] (vars : List (TableauVar V)) : CNF :=
  (vars.map (fun v => tLit V v true)) :: (vars.tails.flatMap fun
    | [] => []
    | v :: rest => rest.map (fun w => [tLit V v false, tLit V w false]))

/-! ## Constraints -/

structure Params (V : Turing.FinTM2) where
  timeBound : ℕ
  maxStackDepth : ℕ

variable {V : Turing.FinTM2} [Encodable V.Λ] [Encodable V.σ] [Encodable V.K] [∀ k, Encodable (V.Γ k)]
  [Fintype V.Λ] [Fintype V.σ] [Fintype V.K] [∀ k, Fintype (V.Γ k)] [DecidableEq V.K] [∀ k, DecidableEq (V.Γ k)]

/-- timesteps have exactly one label/state/stack element/length. -/
noncomputable def consistencyConstraints (params : Params V) : CNF :=
  (List.range (params.timeBound + 1)).flatMap (fun i =>
    exactlyOne V ((Finset.univ : Finset (Option V.Λ)).toList.map (TableauVar.label i))) ++
  (List.range (params.timeBound + 1)).flatMap (fun i =>
    exactlyOne V ((Finset.univ : Finset V.σ).toList.map (TableauVar.state i))) ++
  (List.range (params.timeBound + 1)).flatMap (fun i =>
    (Finset.univ : Finset V.K).toList.flatMap (fun k =>
      (List.range params.maxStackDepth).flatMap (fun j =>
        exactlyOne V ((Finset.univ : Finset (V.Γ k)).toList.map (TableauVar.stkElem i k j))))) ++
  (List.range (params.timeBound + 1)).flatMap (fun i =>
    (Finset.univ : Finset V.K).toList.flatMap (fun k =>
      exactlyOne V ((List.range (params.maxStackDepth + 1)).map (TableauVar.stkLen i k))))

/-- Fix the initial configuration. -/
noncomputable def initialConstraints (params : Params V) (inputContents : List (V.Γ V.k₀)) : CNF :=
  [[tLit V (TableauVar.label 0 (some V.main)) true]] ++
  [[tLit V (TableauVar.state 0 V.initialState) true]] ++
  [[tLit V (TableauVar.stkLen 0 V.k₀ inputContents.length) true]] ++
  (inputContents.reverse.zipIdx.map (fun ⟨γ, j⟩ => [tLit V (TableauVar.stkElem 0 V.k₀ j γ) true])) ++
  (Finset.univ.toList.flatMap (fun k => if k = V.k₀ then [] else [[tLit V (TableauVar.stkLen 0 k 0) true]]))

/-- Local transition logic at time i. -/
noncomputable def transitionClausesAt (params : Params V) (i : ℕ) : CNF :=
  (Finset.univ : Finset (Option V.Λ)).toList.flatMap fun l =>
    (Finset.univ : Finset V.σ).toList.flatMap fun s =>
      -- For each stack, either it's empty or it has some length len_k > 0 and top γ_k
      (Finset.univ : Finset (∀ k : V.K, Option (Fin params.maxStackDepth × V.Γ k))).toList.flatMap fun topsInfo =>
        let antecedent : List Literal :=
          [tLit V (TableauVar.label i l) false, tLit V (TableauVar.state i s) false] ++
          (Finset.univ : Finset V.K).toList.flatMap (fun k => match topsInfo k with
            | none => [tLit V (TableauVar.stkLen i k 0) false]
            | some (len, γ) => [tLit V (TableauVar.stkLen i k (len.val + 1)) false,
                               tLit V (TableauVar.stkElem i k len.val γ) false])
        
        let stkVals : ∀ k : V.K, List (V.Γ k) := fun k => match topsInfo k with | none => [] | some (_, γ) => [γ]
        match l with
        | none =>
          [antecedent ++ [tLit V (TableauVar.label (i+1) none) true],
           antecedent ++ [tLit V (TableauVar.state (i+1) s) true]] ++
          (Finset.univ : Finset V.K).toList.flatMap fun k => match topsInfo k with
            | none => [antecedent ++ [tLit V (TableauVar.stkLen (i+1) k 0) true]]
            | some (len, γ) => [antecedent ++ [tLit V (TableauVar.stkLen (i+1) k (len.val + 1)) true],
                               antecedent ++ [tLit V (TableauVar.stkElem (i+1) k len.val γ) true]]
        | some lbl =>
          let res := Turing.TM2.stepAux (V.m lbl) s stkVals
          [antecedent ++ [tLit V (TableauVar.label (i+1) res.l) true],
           antecedent ++ [tLit V (TableauVar.state (i+1) res.var) true]] ++
          (Finset.univ : Finset V.K).toList.flatMap fun k =>
            let ns := res.stk k
            -- If push/pop happened, the new length is (len + 1) + (ns.length - 1)
            let oldLen := match topsInfo k with | none => 0 | some (len, _) => len.val + 1
            let newLen := oldLen + ns.length - (if (topsInfo k).isSome then 1 else 0)
            [antecedent ++ [tLit V (TableauVar.stkLen (i+1) k newLen) true]] ++
            ns.reverse.zipIdx.map (fun ⟨γ, j⟩ => 
              -- j is index from bottom of the new segment. 
              -- We need to add (oldLen - (if isSome then 1 else 0)) to get the absolute index.
              let base := oldLen - (if (topsInfo k).isSome then 1 else 0)
              antecedent ++ [tLit V (TableauVar.stkElem (i+1) k (base + j) γ) true])

/-- Transition constraints for all timesteps. -/
noncomputable def transitionConstraints (params : Params V) : CNF :=
  (List.range params.timeBound).flatMap (transitionClausesAt params)

/-- Suffix of the stack is preserved. -/
noncomputable def framePreservation (params : Params V) : CNF :=
  (List.range params.timeBound).flatMap fun i =>
    (Finset.univ : Finset V.K).toList.flatMap fun k =>
      (List.range params.maxStackDepth).flatMap fun j =>
        (Finset.univ : Finset (V.Γ k)).toList.flatMap fun γ =>
          (List.range (params.maxStackDepth + 1)).filterMap fun len =>
            if j + maxReadDepth V k < len then
              some [tLit V (TableauVar.stkLen i k len) false,
                    tLit V (TableauVar.stkElem i k j γ) false,
                    tLit V (TableauVar.stkElem (i + 1) k j γ) true]
            else none

/-- At least one state is a halting state. -/
noncomputable def acceptanceConstraints (params : Params V) : CNF :=
  [(List.range (params.timeBound + 1)).map (fun i => tLit V (TableauVar.label i none) true)]

/-- Full formula for the reduction. -/
noncomputable def tableauFormula (params : Params V) (inputContents : List (V.Γ V.k₀)) : CNF :=
  consistencyConstraints params ++ initialConstraints params inputContents ++
  transitionConstraints params ++ framePreservation params ++ acceptanceConstraints params

end CookLevinTableau
