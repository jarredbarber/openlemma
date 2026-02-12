/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Cook-Levin Tableau: Variable definitions and constraint generation for the
Cook-Levin reduction using the "forbidden windows" approach (Option A).

Design reference: `proofs/cook-levin-forbidden-windows-design.md`

This file defines:
- TableauVariable: the propositional variables encoding TM2 computation
- Constraint generation functions (consistency, initial, transition, acceptance)
- The abstract step interface for forbidden window enumeration

Trust level: 🟡 Definitions and scaffolding.
-/
import Mathlib.Computability.TMComputable
import Mathlib.Computability.Encoding
import Mathlib.Logic.Encodable.Basic
import Mathlib.Data.Fintype.Basic
import botlib.Complexity.Defs
import botlib.Complexity.SAT

namespace OpenLemma.Complexity.CookLevin

open Turing Computability SAT Complexity

-- Re-export Turing names that get shadowed by the OpenLemma.Complexity namespace

/-! ## Statement Analysis

Before defining the tableau, we need to know how deeply the TM2 `stepAux`
reads into each stack within a single step. This determines the "window depth"
for the forbidden windows encoding.
-/

section StmtAnalysis

variable {K : Type*} {Γ : K → Type*} {Λ : Type*} {σ : Type*}

/-- Maximum number of pops on stack `k` within a TM2 statement.
    This determines how many stack elements need to be tracked
    in the transition window for stack `k`. -/
def stmtPopDepth (k : K) [DecidableEq K] : Turing.TM2.Stmt Γ Λ σ → ℕ
  | .push k' _ q => stmtPopDepth k q
  | .peek k' _ q => stmtPopDepth k q
  | .pop k' _ q => (if k' = k then 1 else 0) + stmtPopDepth k q
  | .load _ q => stmtPopDepth k q
  | .branch _ q₁ q₂ => max (stmtPopDepth k q₁) (stmtPopDepth k q₂)
  | .goto _ => 0
  | .halt => 0

/-- Maximum number of pushes on stack `k` within a TM2 statement. -/
def stmtPushDepth (k : K) [DecidableEq K] : Turing.TM2.Stmt Γ Λ σ → ℕ
  | .push k' _ q => (if k' = k then 1 else 0) + stmtPushDepth k q
  | .peek _ _ q => stmtPushDepth k q
  | .pop _ _ q => stmtPushDepth k q
  | .load _ q => stmtPushDepth k q
  | .branch _ q₁ q₂ => max (stmtPushDepth k q₁) (stmtPushDepth k q₂)
  | .goto _ => 0
  | .halt => 0

/-- The "read depth" of a statement on stack k: how many elements from the top
    the statement may inspect (via pop or peek). After processing, at most
    this many elements are consumed (and possibly replaced). -/
def stmtReadDepth (k : K) [DecidableEq K] : Turing.TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => stmtReadDepth k q
  | .peek k' _ q => (if k' = k then 1 else 0) + stmtReadDepth k q
  | .pop k' _ q => (if k' = k then 1 else 0) + stmtReadDepth k q
  | .load _ q => stmtReadDepth k q
  | .branch _ q₁ q₂ => max (stmtReadDepth k q₁) (stmtReadDepth k q₂)
  | .goto _ => 0
  | .halt => 0

end StmtAnalysis

/-- Maximum read depth across all labels of a Turing.FinTM2 machine on stack `k`. -/
noncomputable def maxReadDepth (V : Turing.FinTM2) (k : V.K) : ℕ :=
  @Finset.sup V.Λ ℕ _ Finset.univ (fun l => stmtReadDepth k (V.m l))

/-! ## Abstract Step Input/Output

For the forbidden windows approach, we abstract each TM2 step into:
- Input: (label, state, top elements of each stack)
- Output: (new label, new state, stack modifications)
-/

/-- The observable state before a step: label, internal state, and the top
    `d(k)` elements of each stack (where d is the read depth). -/
structure StepInput (V : Turing.FinTM2) where
  /-- Current label (None = halted) -/
  label : Option V.Λ
  /-- Current internal state -/
  state : V.σ
  /-- Top elements of each stack (head = top of stack) -/
  tops : ∀ k : V.K, List (V.Γ k)

/-- The stack modification produced by a single step. -/
inductive StackDelta (Γ : Type*)
  /-- No change to the stack -/
  | unchanged : StackDelta Γ
  /-- Pop the top element -/
  | pop : StackDelta Γ
  /-- Push a new element -/
  | push : Γ → StackDelta Γ

/-- The observable output after a step. -/
structure StepOutput (V : Turing.FinTM2) where
  /-- New label -/
  label : Option V.Λ
  /-- New internal state -/
  state : V.σ
  /-- Stack modifications for each stack -/
  delta : ∀ k : V.K, StackDelta (V.Γ k)

/-! ## Tableau Variables (revised)

We define variables for the Cook-Levin tableau. Each variable is a proposition
about the TM2 computation at a specific timestep.
-/

/-- Variables used in the Cook-Levin reduction for a Turing.FinTM2 machine V.
    The time bound T and stack size bound S are parameters. -/
inductive TableauVar (V : Turing.FinTM2) where
  /-- The machine has label `l` at time `i`. -/
  | label (i : ℕ) (l : Option V.Λ) : TableauVar V
  /-- The machine has internal state `s` at time `i`. -/
  | state (i : ℕ) (s : V.σ) : TableauVar V
  /-- Stack `k` has symbol `γ` at position `j` (0-indexed from bottom) at time `i`. -/
  | stkElem (i : ℕ) (k : V.K) (j : ℕ) (γ : V.Γ k) : TableauVar V
  /-- Stack `k` has length `len` at time `i`. -/
  | stkLen (i : ℕ) (k : V.K) (len : ℕ) : TableauVar V
  /-- Bit `j` of the certificate encoding (free variables for the witness). -/
  | cert (j : ℕ) : TableauVar V

/-! ## Encodable instance for TableauVar

We need `Encodable (TableauVar V)` to map tableau variables to SAT variable
indices. We construct this via equivalence with a sum type. -/

/-- Auxiliary sum type isomorphic to TableauVar, for Encodable derivation. -/
private abbrev TableauVarSum (V : Turing.FinTM2) :=
  -- label
  (ℕ × Option V.Λ) ⊕
  -- state
  (ℕ × V.σ) ⊕
  -- stkElem: we use Sigma to handle dependent types
  (ℕ × (Σ k : V.K, ℕ × V.Γ k)) ⊕
  -- stkLen
  (ℕ × V.K × ℕ) ⊕
  -- cert
  ℕ

/-- Convert TableauVar to the sum representation. -/
private def TableauVar.toSum {V : Turing.FinTM2} : TableauVar V → TableauVarSum V
  | .label i l => Sum.inl (i, l)
  | .state i s => Sum.inr (Sum.inl (i, s))
  | .stkElem i k j γ => Sum.inr (Sum.inr (Sum.inl (i, ⟨k, j, γ⟩)))
  | .stkLen i k len => Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, k, len))))
  | .cert j => Sum.inr (Sum.inr (Sum.inr (Sum.inr j)))

/-- Convert the sum representation back to TableauVar. -/
private def TableauVar.ofSum {V : Turing.FinTM2} : TableauVarSum V → TableauVar V
  | Sum.inl (i, l) => .label i l
  | Sum.inr (Sum.inl (i, s)) => .state i s
  | Sum.inr (Sum.inr (Sum.inl (i, ⟨k, j, γ⟩))) => .stkElem i k j γ
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, k, len)))) => .stkLen i k len
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr j))) => .cert j

private theorem TableauVar.toSum_ofSum {V : Turing.FinTM2} (x : TableauVarSum V) :
    TableauVar.toSum (TableauVar.ofSum x) = x := by
  rcases x with ⟨i, l⟩ | ⟨i, s⟩ | ⟨i, ⟨k, j, γ⟩⟩ | ⟨i, k, len⟩ | j <;> rfl

private theorem TableauVar.ofSum_toSum {V : Turing.FinTM2} (v : TableauVar V) :
    TableauVar.ofSum (TableauVar.toSum v) = v := by
  cases v <;> rfl

/-- Equivalence between TableauVar and the sum type. -/
private def TableauVar.equiv (V : Turing.FinTM2) : TableauVar V ≃ TableauVarSum V where
  toFun := TableauVar.toSum
  invFun := TableauVar.ofSum
  left_inv := TableauVar.ofSum_toSum
  right_inv := TableauVar.toSum_ofSum

/-- Encodable instance for TableauVar, derived from the sum-type equivalence.
    Requires Encodable instances for V.Λ, V.σ, V.K, and V.Γ k. -/
noncomputable instance {V : Turing.FinTM2} [Encodable V.Λ] [Encodable V.σ] [Encodable V.K]
    [∀ k, Encodable (V.Γ k)] :
    Encodable (TableauVar V) :=
  Encodable.ofEquiv _ (TableauVar.equiv V).symm

/-! ## Literal and Clause Construction -/

/-- Encode a TableauVar and polarity into a SAT Literal.
    `pos` = the variable is true; `neg` = the variable is false. -/
noncomputable def tLit [Encodable V.Λ] [Encodable V.σ] [Encodable V.K]
    [∀ k, Encodable (V.Γ k)] (v : TableauVar V) (b : Bool) : SAT.Literal :=
  if b then SAT.Literal.pos (Encodable.encode v) else SAT.Literal.neg (Encodable.encode v)

/-- Unit clause fixing a variable to a value. -/
noncomputable def fixClause [Encodable V.Λ] [Encodable V.σ] [Encodable V.K]
    [∀ k, Encodable (V.Γ k)] (v : TableauVar V) (b : Bool) : SAT.Clause :=
  [tLit v b]

/-- "At least one" clause: at least one variable in the list is true. -/
noncomputable def atLeastOne [Encodable V.Λ] [Encodable V.σ] [Encodable V.K]
    [∀ k, Encodable (V.Γ k)] (vars : List (TableauVar V)) : SAT.Clause :=
  vars.map (fun v => tLit v true)

/-- "At most one" clauses: for every pair, at most one is true.
    Implemented as pairwise mutual exclusion clauses. -/
noncomputable def atMostOne [Encodable V.Λ] [Encodable V.σ] [Encodable V.K]
    [∀ k, Encodable (V.Γ k)] (vars : List (TableauVar V)) : SAT.CNF :=
  vars.tails.flatMap fun
    | [] => []
    | v :: rest => rest.map (fun w => [tLit v false, tLit w false])

/-- "Exactly one" constraints: at least one and at most one. -/
noncomputable def exactlyOne [Encodable V.Λ] [Encodable V.σ] [Encodable V.K]
    [∀ k, Encodable (V.Γ k)] (vars : List (TableauVar V)) : SAT.CNF :=
  atLeastOne vars :: atMostOne vars

/-! ## Reduction Parameters -/

/-- Parameters for the Cook-Levin reduction for a specific machine and input. -/
structure Params (V : Turing.FinTM2) where
  /-- Time bound T: the computation runs for at most T steps. -/
  timeBound : ℕ
  /-- Maximum stack depth: each stack has at most this many elements. -/
  maxStackDepth : ℕ

/-! ## Group 1: Consistency Constraints

Every timestep has exactly one label, exactly one state, each stack position
has exactly one symbol, and each stack has exactly one length.
-/

section Consistency

variable (V : Turing.FinTM2) (params : Params V)
  [Encodable V.Λ] [Encodable V.σ] [Encodable V.K] [∀ k, Encodable (V.Γ k)]
  [∀ k, Fintype (V.Γ k)]

/-- Exactly one label per timestep. -/
noncomputable def labelConsistency : SAT.CNF :=
  (List.range (params.timeBound + 1)).flatMap fun i =>
    exactlyOne (Finset.univ (α := Option V.Λ).toList.map fun l => TableauVar.label i l)

/-- Exactly one state per timestep. -/
noncomputable def stateConsistency : SAT.CNF :=
  (List.range (params.timeBound + 1)).flatMap fun i =>
    exactlyOne (Finset.univ (α := V.σ).toList.map fun s => TableauVar.state i s)

/-- Exactly one symbol per (timestep, stack, position). -/
noncomputable def stkElemConsistency : SAT.CNF :=
  (List.range (params.timeBound + 1)).flatMap fun i =>
    Finset.univ (α := V.K).toList.flatMap fun k =>
      (List.range params.maxStackDepth).flatMap fun j =>
        exactlyOne (Finset.univ (α := V.Γ k).toList.map fun γ =>
          TableauVar.stkElem i k j γ)

/-- Exactly one length per (timestep, stack). -/
noncomputable def stkLenConsistency : SAT.CNF :=
  (List.range (params.timeBound + 1)).flatMap fun i =>
    Finset.univ (α := V.K).toList.flatMap fun k =>
      exactlyOne ((List.range (params.maxStackDepth + 1)).map fun len =>
        TableauVar.stkLen i k len)

/-- All consistency constraints combined. -/
noncomputable def consistencyConstraints : SAT.CNF :=
  labelConsistency V params ++
  stateConsistency V params ++
  stkElemConsistency V params ++
  stkLenConsistency V params

end Consistency

/-! ## Group 2: Initial Configuration

At time 0, the machine is in its initial state with the input loaded
on stack k₀ and all other stacks empty.
-/

section Initial

variable (V : Turing.FinTM2) (params : Params V)
  [Encodable V.Λ] [Encodable V.σ] [Encodable V.K] [∀ k, Encodable (V.Γ k)]

/-- Fix the label at time 0 to `some V.main`. -/
noncomputable def initialLabel : SAT.CNF :=
  [fixClause (TableauVar.label (V := V) 0 (some V.main)) true]

/-- Fix the state at time 0 to `V.initialState`. -/
noncomputable def initialState : SAT.CNF :=
  [fixClause (TableauVar.state (V := V) 0 V.initialState) true]

/-- Fix stack contents at time 0 from a list of encoded input symbols. -/
noncomputable def initialStack (k : V.K) (contents : List (V.Γ k)) : SAT.CNF :=
  -- Fix length
  [fixClause (TableauVar.stkLen 0 k contents.length) true] ++
  -- Fix each position
  contents.enum.map fun ⟨j, γ⟩ =>
    fixClause (TableauVar.stkElem 0 k j γ) true

/-- Fix non-input stacks to be empty at time 0. -/
noncomputable def initialEmptyStacks [DecidableEq V.K] : SAT.CNF :=
  Finset.univ.toList.flatMap fun k =>
    if k = V.k₀ then [] else [fixClause (TableauVar.stkLen 0 k 0) true]

/-- All initial configuration constraints. -/
noncomputable def initialConstraints [DecidableEq V.K]
    (inputContents : List (V.Γ V.k₀)) : SAT.CNF :=
  initialLabel V params ++
  initialState V params ++
  initialStack V params V.k₀ inputContents ++
  initialEmptyStacks V params

end Initial

/-! ## Group 3: Transition Constraints (Forbidden Windows)

For each timestep i, we enumerate all possible "abstract step inputs"
(label, state, top elements of relevant stacks) and enforce that the
configuration at time i+1 is consistent with `Turing.TM2.step V.m`.

The key insight: since `Λ`, `σ`, and `Γ k` are all `Fintype`, we can
enumerate all possible input tuples. For each one, we compute what the
next configuration should be, and emit implication clauses.
-/

section Transitions

variable (V : Turing.FinTM2) (params : Params V)
  [Encodable V.Λ] [Encodable V.σ] [Encodable V.K] [∀ k, Encodable (V.Γ k)]
  [DecidableEq V.K] [∀ k, Fintype (V.Γ k)] [∀ k, DecidableEq (V.Γ k)]

/-- Build a minimal Cfg from an abstract step input, with stacks containing
    only the provided top elements. Used to compute the step output. -/
def mkMinimalCfg (inp : StepInput V) : Turing.TM2.Cfg V.Γ V.Λ V.σ :=
  ⟨inp.label, inp.state, inp.tops⟩

/-- Compute the abstract step output by running `Turing.TM2.step V.m` on a minimal Cfg.
    Returns `none` if the machine is halted (label = none). -/
def computeStep (inp : StepInput V) : Option (Turing.TM2.Cfg V.Γ V.Λ V.σ) :=
  Turing.TM2.step V.m (mkMinimalCfg inp)

/-- Generate transition clauses for a single timestep i.
    For each possible (label, state, stack-tops) combination:
    - Compute the expected next configuration via `TM2.step`
    - Emit clauses: "if input matches this pattern, then output must match"

    Each implication `(A₁ ∧ ... ∧ Aₙ) → B` becomes `¬A₁ ∨ ... ∨ ¬Aₙ ∨ B` in CNF.

    TODO: This is a placeholder. The full implementation needs to:
    1. Enumerate all (label × state × stack-top-elements) tuples
    2. For each, compute `TM2.step` result
    3. Emit clauses linking time i variables to time i+1 variables
    4. Handle the stack position updates (push/pop affects length and top element)
-/
noncomputable def transitionClausesAt (_i : ℕ) : SAT.CNF :=
  sorry

/-- Transition constraints for all timesteps. -/
noncomputable def transitionConstraints : SAT.CNF :=
  (List.range params.timeBound).flatMap fun i =>
    transitionClausesAt V params i

end Transitions

/-! ## Group 4: Stack Frame Preservation

Elements below the top of the stack are unchanged between timesteps.
If `stkLen(i, k) = len` and `j < len - maxReadDepth`, then
`stkElem(i, k, j, γ) → stkElem(i+1, k, j, γ)`.
-/

section FramePreservation

variable (V : Turing.FinTM2) (params : Params V)
  [Encodable V.Λ] [Encodable V.σ] [Encodable V.K] [∀ k, Encodable (V.Γ k)]
  [∀ k, Fintype (V.Γ k)]

/-- For each (i, k, j, γ): if position j is below the modification zone
    (j < len - maxReadDepth), then the symbol is preserved.
    
    Encoding: ¬stkLen(i, k, len) ∨ ¬stkElem(i, k, j, γ) ∨ stkElem(i+1, k, j, γ)
    
    This says: if the stack has length `len` at time i AND position j has
    symbol γ at time i, then position j still has symbol γ at time i+1
    (provided j is deep enough in the stack to be unaffected). -/
noncomputable def framePreservationAt (i : ℕ) : SAT.CNF :=
  Finset.univ (α := V.K).toList.flatMap fun k =>
    (List.range params.maxStackDepth).flatMap fun j =>
      Finset.univ (α := V.Γ k).toList.flatMap fun γ =>
        -- For each possible stack length where j is in the preserved zone
        (List.range (params.maxStackDepth + 1)).filterMap fun len =>
          if j + maxReadDepth V k < len then
            some [tLit (TableauVar.stkLen i k len) false,
                  tLit (TableauVar.stkElem i k j γ) false,
                  tLit (TableauVar.stkElem (i + 1) k j γ) true]
          else none

/-- Frame preservation for all timesteps. -/
noncomputable def framePreservation : SAT.CNF :=
  (List.range params.timeBound).flatMap fun i =>
    framePreservationAt V params i

end FramePreservation

/-! ## Group 5: Acceptance Constraints

The machine must halt in an accepting state within the time bound.
For our formalization, "accepting" means the machine halts (label = none)
with a specific output on stack k₁.
-/

section Acceptance

variable (V : Turing.FinTM2) (params : Params V)
  [Encodable V.Λ] [Encodable V.σ] [Encodable V.K] [∀ k, Encodable (V.Γ k)]

/-- The machine must halt at some point: at least one timestep has label = none. -/
noncomputable def mustHalt : SAT.CNF :=
  [atLeastOne ((List.range (params.timeBound + 1)).map fun i =>
    TableauVar.label (V := V) i none)]

/-- Acceptance constraints: the machine halts within the time bound.
    Additional output-checking constraints would be added here. -/
noncomputable def acceptanceConstraints : SAT.CNF :=
  mustHalt V params

end Acceptance

/-! ## Main Reduction Assembly -/

/-- The complete set of clauses for the Cook-Levin reduction.
    Given machine V, parameters, and input contents, produces a CNF formula
    that is satisfiable iff V accepts some input with some certificate. -/
noncomputable def tableauFormula [DecidableEq V.K]
    [Encodable V.Λ] [Encodable V.σ] [Encodable V.K]
    [∀ k, Encodable (V.Γ k)] [∀ k, Fintype (V.Γ k)] [∀ k, DecidableEq (V.Γ k)]
    (V : Turing.FinTM2) (params : Params V) (inputContents : List (V.Γ V.k₀)) : SAT.CNF :=
  consistencyConstraints V params ++
  initialConstraints V params inputContents ++
  transitionConstraints V params ++
  framePreservation V params ++
  acceptanceConstraints V params

end OpenLemma.Complexity.CookLevin
