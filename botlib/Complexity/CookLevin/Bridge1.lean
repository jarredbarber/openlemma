/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Bridge 1 — Verifier Semantics: equating the Kleene (`flip bind`) iteration scheme
with the step-or-halt (`cfgAt`) iteration scheme for a deterministic TM2 step function.

This file translates the reviewer-approved Python code proof at
`exploration/cook-levin/bridge1_verifier_semantics.py` into machine-verified Lean 4.
It contains two theorems:

  * `kleene_some_implies_stepOrHalt_eq` — the core invariant (induction on `t`):
    if the Kleene iteration `(flip bind V.step)^[t] (some init)` is `some c`, then the
    step-or-halt iteration `(stepOrHalt V)^[t] init` equals `c`.
    This is `lemma_K_some_implies_S_eq` in the Python proof.
    The argument is purely structural (Option case analysis + iteration unfolding +
    `getD` on `some`) and holds for every deterministic step function `Cfg → Option Cfg`,
    which is automatic for the pure Lean function `FinTM2.step`.

  * `cfgAt_reaches_halt` — the forward Bridge 1 implication:
    `TM2OutputsInTime V input (some out) m` witnesses a `t ≤ m` with
    `cfgAt V input t = haltList V out`.
    This is `lemma_TM2OutputsInTime_to_cfgAt_halt` in the Python proof; it composes the
    core invariant with the witness carried explicitly by `TM2OutputsInTime`.
-/
import botlib.Complexity.CookLevin.Completeness
import Mathlib.Computability.TMComputable

namespace CookLevinTableau

open Turing CookLevinTableau

set_option linter.unusedSectionVars false

variable {V : Turing.FinTM2} [Encodable V.Λ] [Encodable V.σ] [Encodable V.K]
  [∀ k, Encodable (V.Γ k)]
  [Fintype V.Λ] [Fintype V.σ] [Fintype V.K] [∀ k, Fintype (V.Γ k)]
  [DecidableEq V.K] [∀ k, DecidableEq (V.Γ k)]
  [DecidableEq V.Λ] [DecidableEq V.σ]

/-! ## Bridge 1 — Verifier semantics

### Lemma A — core invariant (induction on t)

The Kleene scheme iterates `K_step := flip bind V.step : Option V.Cfg → Option V.Cfg`
  (`K_step (some c) = V.step c`, `K_step none = none`),
and the step-or-halt scheme iterates `S_step := stepOrHalt V : V.Cfg → V.Cfg`
  (`S_step c = (V.step c).getD c`).

The invariant — `K_t = some c → S_t = c` — holds for every deterministic step function.
In Lean, `FinTM2.step V : V.Cfg → Option V.Cfg` is a pure function, so the two calls to
`V.step c₀` (one advancing `K`, one advancing `S`) coincide definitionally; this is the
determinism that the Python `DeterministicStep` wrapper guarantees by construction.
-/

/-- Core invariant: if the Kleene iteration `(flip bind V.step)^[t] (some init)` is
    `some c`, then the step-or-halt iteration `(stepOrHalt V)^[t] init` equals `c`.

    Proof by induction on `t`, mirroring `lemma_K_some_implies_S_eq` in the approved
    Python code proof.  The step case is pure Option case analysis on
    `(flip bind V.step)^[t] (some init)`:
      * `none` → `(flip bind V.step) none = none`, contradicting `= some c`;
      * `some c₀` → `V.step c₀ = some c` (by `bind_some`), the IH gives
        `(stepOrHalt V)^[t] init = c₀`, and `stepOrHalt V c₀ = (V.step c₀).getD c₀ = c`
        (by `getD_some`). -/
theorem kleene_some_implies_stepOrHalt_eq
    (init : V.Cfg) (t : ℕ) (c : V.Cfg)
    (hK : (flip bind V.step)^[t] (some init) = some c) :
    (stepOrHalt V)^[t] init = c := by
  induction t generalizing c with
  | zero =>
    -- Base case (t = 0): K_0 = some init, S_0 = init; some init = some c ⟹ init = c.
    -- K_0 = (flip bind V.step)^[0] (some init) is definitionally `some init` (iterate 0 = id),
    -- and S_0 = (stepOrHalt V)^[0] init is definitionally `init`.  So hK coerces to
    -- `some init = some c` and the goal coerces to `init = c`, closed by Some-injectivity.
    have h0 : (flip bind V.step)^[0] (some init) = some init := rfl
    rw [h0] at hK
    -- hK : some init = some c
    exact Option.some.inj hK
  | succ n ih =>
    -- Step case (t = n+1): unfold one iteration of K.
    -- `generalizing c` gives ih : ∀ c, (flip bind V.step)^[n] (some init) = some c →
    --                                 (stepOrHalt V)^[n] init = c
    simp only [Function.iterate_succ_apply'] at hK
    -- hK : (flip bind V.step) ((flip bind V.step)^[n] (some init)) = some c
    -- ih : ∀ c, (flip bind V.step)^[n] (some init) = some c → (stepOrHalt V)^[n] init = c
    cases hk : (flip bind V.step)^[n] (some init) with
    | none =>
      -- K_{n} = none ⟹ K_{n+1} = (flip bind V.step) none = none, contradicting hK.
      rw [hk] at hK
      -- (flip bind V.step) none is definitionally none (Option.bind none _ = none)
      have hNone : (flip bind V.step) (none : Option V.Cfg) = none := rfl
      rw [hNone] at hK
      -- hK : none = some c — contradiction; `simp at hK` derives False and closes the goal.
      simp at hK
    | some c₀ =>
      -- K_{n} = some c₀ ⟹ K_{n+1} = (flip bind V.step) (some c₀) = V.step c₀ = some c.
      rw [hk] at hK
      -- (flip bind V.step) (some c₀) is definitionally (V.step c₀)
      have hSome : (flip bind V.step) (some c₀) = V.step c₀ := rfl
      rw [hSome] at hK
      -- hK : V.step c₀ = some c
      -- Apply the IH at c₀ to get (stepOrHalt V)^[n] init = c₀.
      have hIH := ih c₀ hk
      -- Goal: (stepOrHalt V)^[n+1] init = c.  Unfold one step-or-halt iteration.
      simp only [Function.iterate_succ_apply']
      -- Goal: (stepOrHalt V) ((stepOrHalt V)^[n] init) = c
      rw [hIH]
      -- Goal: stepOrHalt V c₀ = c
      unfold stepOrHalt
      -- Goal: (match V.step c₀ with | some cfg' => cfg' | none => c₀) = c
      rw [hK]
      -- Goal: (match some c with | some cfg' => cfg' | none => c₀) = c
      -- reduces definitionally to `c = c`, closed by `rw`

/-! ### Lemma B — forward Bridge 1

`TM2OutputsInTime V input (some out) m` carries an explicit witness `t = h.toEvalsTo.steps`
with `t ≤ m` and `(flip bind V.step)^[t] (initList V input) = some (haltList V out)`.
Applying the core invariant at this witness yields
`(stepOrHalt V)^[t] (initList V input) = haltList V out`, i.e. `cfgAt V input t = haltList V out`.
-/

/-- Forward Bridge 1: if `V` outputs `out` on `input` within `m` steps (Kleene scheme),
    then `cfgAt` reaches `haltList V out` within `m` steps (step-or-halt scheme).

    This is `lemma_TM2OutputsInTime_to_cfgAt_halt` in the approved Python code proof.
    It uses ONLY the core invariant (`kleene_some_implies_stepOrHalt_eq`); it does not
    depend on the TM2 halt convention (`step (haltList out) = none`), which only concerns
    whether the hypothesis is realizable, not the implication. -/
theorem cfgAt_reaches_halt
    (input : List (V.Γ V.k₀)) (out : List (V.Γ V.k₁)) (m : ℕ)
    (h : TM2OutputsInTime V input (some out) m) :
    ∃ t ≤ m, cfgAt V input t = haltList V out := by
  -- h : EvalsToInTime V.step (initList V input) (Option.map (haltList V) (some out)) m
  -- carries the witness t = h.toEvalsTo.steps with h.steps_le_m : t ≤ m and
  -- h.toEvalsTo.evals_in_steps : (flip bind V.step)^[t] (initList V input) = Option.map ...
  have h_evals := h.toEvalsTo.evals_in_steps
  -- Option.map (haltList V) (some out) = some (haltList V out)
  simp only [Option.map_some] at h_evals
  -- h_evals : (flip bind V.step)^[h.steps] (initList V input) = some (haltList V out)
  -- Apply the core invariant at this witness.
  have h_inv :=
    kleene_some_implies_stepOrHalt_eq (initList V input) h.steps (haltList V out) h_evals
  -- h_inv : (stepOrHalt V)^[h.steps] (initList V input) = haltList V out
  refine ⟨h.steps, h.steps_le_m, ?_⟩
  -- Goal: cfgAt V input h.steps = haltList V out
  -- cfgAt V input t unfolds to (stepOrHalt V)^[t] (Turing.initList V input)
  show (stepOrHalt V)^[h.steps] (Turing.initList V input) = haltList V out
  exact h_inv

/-! ### Strengthening: the witness is the first halting step

`cfgAt_reaches_halt` produces a step `T = h.steps` with `cfgAt V input T = haltList V out`,`
but the decider halting-step argument (`cfgAt_decider_while_running`) needs the stronger
fact that `V` is still *running* at every earlier step `t < T`.

This follows from the Kleene trace structure `K_t := (flip bind V.step)^[t] (some init)`:
  * `K_t = some _` for every `t ≤ h.steps` — once `K` becomes `none` it stays `none`
    (`(flip bind V.step) none = none`), contradicting `K_{h.steps} = some _`;
  * the `some`-witness `c` at step `t < h.steps` satisfies `c.l = some` — if `c.l = none`
    then `V.step c = none`, making `K_{t+1} = none`, contradicting `K_{t+1} = some _`
    (since `t+1 ≤ h.steps`).
Both halves use only `V.step ⟨none, _, _⟩ = none` (the TM2 halt convention).
-/
theorem cfgAt_reaches_halt_first
    (input : List (V.Γ V.k₀)) (out : List (V.Γ V.k₁)) (m : ℕ)
    (h : TM2OutputsInTime V input (some out) m) :
    ∃ T ≤ m, cfgAt V input T = haltList V out ∧ ∀ t < T, (cfgAt V input t).l ≠ none := by
  have h_evals := h.toEvalsTo.evals_in_steps
  simp only [Option.map_some] at h_evals
  -- h_evals : (flip bind V.step)^[h.steps] (some (initList V input)) = some (haltList V out)
  have h_inv := kleene_some_implies_stepOrHalt_eq (initList V input) h.steps (haltList V out) h_evals
  -- h_inv : (stepOrHalt V)^[h.steps] (initList V input) = haltList V out
  set K := fun n : ℕ => (flip bind V.step)^[n] (some (initList V input))
  have hKT : K h.steps = some (haltList V out) := h_evals
  -- (flip bind V.step) none = none: once `K` becomes `none`, it stays `none`.
  have hstays : ∀ n, K n = none → K n.succ = none := by
    intro n hn
    show (flip bind V.step)^[n.succ] (some (initList V input)) = none
    rw [Function.iterate_succ_apply']
    show (flip bind V.step) (K n) = none
    rw [hn]
    rfl
  -- `K n = some _` for every `n ≤ h.steps`.
  have hK_some : ∀ n ≤ h.steps, ∃ c, K n = some c := by
    intro n _hn
    by_contra hcon
    push_neg at hcon
    -- hcon : ∀ c, K n = some c → False
    cases hKn : K n with
    | none =>
      have hchain : ∀ k, K (n + k) = none := by
        intro k
        induction k with
        | zero => exact hKn
        | succ k ih =>
          rw [show (n + k.succ) = (n + k).succ from by omega]
          exact hstays _ ih
      have hKnone : K h.steps = none := by
        have := hchain (h.steps - n)
        rwa [show n + (h.steps - n) = h.steps from by omega] at this
      rw [hKnone] at hKT
      simp at hKT
    | some c => exact absurd hKn (hcon c)
  refine ⟨h.steps, h.steps_le_m, ?_, ?_⟩
  · -- cfgAt V input h.steps = haltList V out
    show (stepOrHalt V)^[h.steps] (Turing.initList V input) = haltList V out
    exact h_inv
  · -- ∀ t < h.steps, (cfgAt V input t).l ≠ none
    intro t ht
    obtain ⟨c, hKt⟩ := hK_some t (le_of_lt ht)
    have hinv_t := kleene_some_implies_stepOrHalt_eq (initList V input) t c hKt
    -- hinv_t : (stepOrHalt V)^[t] (initList V input) = c, i.e. cfgAt V input t = c
    show ((stepOrHalt V)^[t] (Turing.initList V input)).l ≠ none
    rw [hinv_t]
    -- goal: c.l ≠ none
    by_cases hcl : c.l = none
    · -- c.l = none  ⟹  V.step c = none  (TM2 halt convention)
      have hstep : V.step c = none := by
        have heta : c = ⟨c.l, c.var, c.stk⟩ := rfl
        rw [heta, hcl]
        rfl
      -- K (t+1) = (flip bind V.step) (K t) = (flip bind V.step) (some c) = V.step c = none
      have hKsucc : K t.succ = none := by
        show (flip bind V.step)^[t.succ] (some (initList V input)) = none
        rw [Function.iterate_succ_apply']
        show (flip bind V.step) (K t) = none
        rw [hKt]
        exact hstep
      -- but K (t+1) = some _ (since t+1 ≤ h.steps): contradiction.
      obtain ⟨c', hKsucc'⟩ := hK_some t.succ (Nat.succ_le_of_lt ht)
      rw [hKsucc] at hKsucc'
      simp at hKsucc'
    · -- c.l ≠ none: the goal is exactly this.
      exact hcl

end CookLevinTableau