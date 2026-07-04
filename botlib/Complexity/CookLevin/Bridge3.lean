/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Bridge 3 — Adequacy / Depth Preconditions.

This file translates the reviewer-approved Python code proof at
`exploration/cook-levin/bridge3_adequacy_depth.py` into machine-verified Lean 4.

The completeness/soundness theorems require, for the chosen `params : Params V`:
  * `h_adequate : ∀ t' k, t' ≤ params.timeBound → (cfgAt V input t').stk k |>.length ≤ params.maxStackDepth`
  * `BoundedReadDepth V` (∀ lbl k, stmtReadDepth k (V.m lbl) ≤ 1).

A single `V.step` executes the WHOLE statement chain `V.m lbl` via `TM2.stepAux`, which can push
multiple times onto the same stack. The time polynomial bounds the NUMBER OF STEPS, not the
per-step stack growth or the per-step read count. Hence:

  * `BoundedReadDepth V` and a per-step stack-growth bound are STRUCTURAL properties of `V.m`,
    NOT consequences of the time polynomial.

We introduce a `NormalForm V` precondition (each statement chain touches each stack at most
once — at most one push/peek/pop per stack in the chain). Under `NormalForm V`:
  * one step grows each stack by ≤ 1  (`step_length_change_bounded`),
  * the inductive stack-depth bound `len(stk k) ≤ initLen k + t` holds (`stack_depth_bound`),
  * `h_adequate` follows with `maxStackDepth := n + timeBound` (`h_adequate_of_normal_form`),
  * `BoundedReadDepth V` follows  (`bounded_read_depth_of_normal_form`).

The remaining piece is the NORMAL-FORM NORMALIZATION: any polytime TM2 verifier computing `g`
can be transformed into a `NormalForm` verifier computing the same `g` with polynomial blowup
(introduce intermediate labels so each chain touches each stack ≤ 1 time). This is STRUCTURAL
and is NOT a consequence of the time polynomial; it is scaffolded here as a single `sorry`
(`normal_form_normalization`) per the handoff's concrete-scaffold guidance, to be closed as a
separate code-as-proof effort.

Axiom/sorry inventory: ZERO axioms, exactly ONE sorry (normal_form_normalization).
-/
import botlib.Complexity.CookLevin.Completeness
import botlib.Complexity.CookLevin.Correctness
import botlib.Complexity.CookLevin.Bridge1
import botlib.Complexity.CookLevin.Bridge2
import Mathlib.Computability.TMComputable
import botlib.Complexity.Defs

namespace CookLevinTableau

open Turing CookLevinTableau OpenLemma.Complexity Computability List Function

set_option linter.unusedSectionVars false

/-! ## Generic `Stmt`-induction lemmas (no `FinTM2` instance needed) -/

/-- The "touch depth" of a statement on stack k: how many stack-touching actions (push, peek, or
    pop) the statement chain performs on stack `k`. Unlike `stmtReadDepth` (peeks+pops only),
    this also counts pushes, so it bounds BOTH the read count and the per-step length growth. -/
def stmtTouchDepth {K : Type*} {Γ : K → Type*} {Λ : Type*} {σ : Type*} (k : K) [DecidableEq K] :
    Turing.TM2.Stmt Γ Λ σ → ℕ
  | .push k' _ q => (if k' = k then 1 else 0) + stmtTouchDepth k q
  | .peek k' _ q => (if k' = k then 1 else 0) + stmtTouchDepth k q
  | .pop k' _ q => (if k' = k then 1 else 0) + stmtTouchDepth k q
  | .load _ q => stmtTouchDepth k q
  | .branch _ q₁ q₂ => max (stmtTouchDepth k q₁) (stmtTouchDepth k q₂)
  | .goto _ => 0
  | .halt => 0

/-- Reads are a sub-count of touches: `stmtReadDepth ≤ stmtTouchDepth`. -/
theorem stmtReadDepth_le_stmtTouchDepth {K : Type*} {Γ : K → Type*} {Λ : Type*} {σ : Type*}
    (k : K) [DecidableEq K] (q : Turing.TM2.Stmt Γ Λ σ) :
    stmtReadDepth k q ≤ stmtTouchDepth k q := by
  induction q with
  | halt => simp [stmtReadDepth, stmtTouchDepth]
  | goto _ => simp [stmtReadDepth, stmtTouchDepth]
  | load _ q ih => simp [stmtReadDepth, stmtTouchDepth]; exact ih
  | branch _ q₁ q₂ ih₁ ih₂ =>
    simp only [stmtReadDepth, stmtTouchDepth]; exact max_le_max ih₁ ih₂
  | push k' _ q ih =>
    by_cases h : k' = k
    · simp [stmtReadDepth, stmtTouchDepth, h]; omega
    · simp [stmtReadDepth, stmtTouchDepth, h]; omega
  | peek k' _ q ih =>
    by_cases h : k' = k
    · simp [stmtReadDepth, stmtTouchDepth, h]; omega
    · simp [stmtReadDepth, stmtTouchDepth, h]; omega
  | pop k' _ q ih =>
    by_cases h : k' = k
    · simp [stmtReadDepth, stmtTouchDepth, h]; omega
    · simp [stmtReadDepth, stmtTouchDepth, h]; omega

/-- **Lemma A — per-step length bound under touch depth** (structural induction on `q`).
    Executing a statement chain `q` grows stack `k` by at most `stmtTouchDepth k q`. -/
theorem stepAux_stkLength_bound {K : Type*} {Γ : K → Type*} {Λ : Type*} {σ : Type*}
    (q : Turing.TM2.Stmt Γ Λ σ) (k : K) [DecidableEq K] (s : σ) (S : ∀ k, List (Γ k)) :
    ((Turing.TM2.stepAux q s S).stk k).length ≤ (S k).length + stmtTouchDepth k q := by
  induction q generalizing s S with
  | halt => simp [Turing.TM2.stepAux, stmtTouchDepth]
  | goto _ => simp [Turing.TM2.stepAux, stmtTouchDepth]
  | load a q ih => simp [Turing.TM2.stepAux, stmtTouchDepth]; exact ih (a s) S
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [Turing.TM2.stepAux, stmtTouchDepth]
    cases h : f s with
    | true =>
      simp only [Bool.cond_true]
      exact le_trans (ih₁ s S) (Nat.add_le_add_left (Nat.le_max_left _ _) _)
    | false =>
      simp only [Bool.cond_false]
      exact le_trans (ih₂ s S) (Nat.add_le_add_left (Nat.le_max_right _ _) _)
  | push k' f q ih =>
    simp only [Turing.TM2.stepAux, stmtTouchDepth]
    by_cases h : k = k'
    · subst k'
      simp only [if_true]
      have := ih s (update S k (f s :: S k))
      rw [Function.update_self k (f s :: S k) S] at this
      rw [List.length_cons] at this
      omega
    · simp only [if_neg (Ne.symm h)]
      have := ih s (update S k' (f s :: S k'))
      rw [Function.update_of_ne h (f s :: S k') S] at this
      omega
  | peek k' f q ih =>
    simp only [Turing.TM2.stepAux, stmtTouchDepth]
    by_cases h : k = k'
    · subst k'
      simp only [if_true]
      have := ih (f s (S k).head?) S
      omega
    · simp only [if_neg (Ne.symm h)]
      have := ih (f s (S k').head?) S
      omega
  | pop k' f q ih =>
    simp only [Turing.TM2.stepAux, stmtTouchDepth]
    by_cases h : k = k'
    · subst k'
      simp only [if_true]
      have := ih (f s (S k).head?) (update S k (S k).tail)
      rw [Function.update_self k (S k).tail S] at this
      rw [List.length_tail] at this
      omega
    · simp only [if_neg (Ne.symm h)]
      have := ih (f s (S k').head?) (update S k' (S k').tail)
      rw [Function.update_of_ne h (S k').tail S] at this
      omega

/-! ## `FinTM2` instance block — Bridge 3 main lemmas -/

variable {V : Turing.FinTM2} [Encodable V.Λ] [Encodable V.σ] [Encodable V.K]
  [∀ k, Encodable (V.Γ k)]
  [Fintype V.Λ] [Fintype V.σ] [Fintype V.K] [∀ k, Fintype (V.Γ k)]
  [DecidableEq V.K] [∀ k, DecidableEq (V.Γ k)]
  [DecidableEq V.Λ] [DecidableEq V.σ]

/-- A `FinTM2` is in normal form when every statement chain touches each stack at most once
    (so at most one push AND at most one read per stack per step). Uses the bundled
    `V.decidableEqK` instance, mirroring `BoundedReadDepth`. -/
def NormalForm (V : Turing.FinTM2) : Prop :=
  ∀ (lbl : V.Λ) (k : V.K),
    @stmtTouchDepth V.K V.Γ V.Λ V.σ k V.decidableEqK (V.m lbl) ≤ 1

/-- **Lemma B — under `NormalForm`, one step grows each stack by ≤ 1.** -/
theorem step_length_change_bounded (cfg : V.Cfg) (k : V.K)
    (hNF : NormalForm V) {cfg' : V.Cfg} (hstep : V.step cfg = some cfg') :
    (cfg'.stk k).length ≤ (cfg.stk k).length + 1 := by
  obtain ⟨l, v, S⟩ := cfg
  cases l with
  | none =>
    have hs : V.step ⟨none, v, S⟩ = none := by
      simp only [FinTM2.step, Turing.TM2.step.eq_1]
    rw [hs] at hstep
    cases hstep
  | some lbl =>
    have hstep' : V.step ⟨some lbl, v, S⟩ =
        some (@TM2.stepAux V.K V.Γ V.Λ V.σ V.decidableEqK (V.m lbl) v S) :=
      @Turing.TM2.step.eq_2 V.K V.Γ V.Λ V.σ V.decidableEqK V.m lbl v S
    rw [hstep'] at hstep
    injection hstep with heq
    subst heq
    have bound :=
      @stepAux_stkLength_bound V.K V.Γ V.Λ V.σ (V.m lbl) k V.decidableEqK v S
    have touch : @stmtTouchDepth V.K V.Γ V.Λ V.σ k V.decidableEqK (V.m lbl) ≤ 1 := hNF lbl k
    show ((@TM2.stepAux V.K V.Γ V.Λ V.σ V.decidableEqK (V.m lbl) v S).stk k).length ≤ (S k).length + 1
    omega

/-- **Lemma C — inductive stack-depth bound**: under `NormalForm`, after `t` steps each stack
    length is at most `initLen k + t`, where `initLen k = n` on `k₀` and `0` elsewhere. -/
theorem stack_depth_bound (input : List (V.Γ V.k₀)) (n : ℕ) (hn : input.length = n)
    (hNF : NormalForm V) (t : ℕ) (k : V.K) :
    ((cfgAt V input t).stk k).length ≤ (if k = V.k₀ then n else 0) + t := by
  induction t with
  | zero =>
    have h0 : cfgAt V input 0 = Turing.initList V input := by simp [cfgAt]
    rw [h0]
    by_cases hk : k = V.k₀
    · subst hk
      have hk0 : (Turing.initList V input).stk V.k₀ = input := by simp [Turing.initList]
      rw [hk0, if_pos (rfl : V.k₀ = V.k₀)]
      omega
    · have hko : (Turing.initList V input).stk k = [] := by simp [Turing.initList, hk]
      rw [hko, if_neg hk]
      simp
  | succ t ih =>
    rw [cfgAt_succ]
    cases hstep : V.step (cfgAt V input t) with
    | some cfg' =>
      have hnext : stepOrHalt V (cfgAt V input t) = cfg' := by
        simp only [stepOrHalt, hstep]
      rw [hnext]
      have bound := step_length_change_bounded (cfgAt V input t) k hNF hstep
      omega
    | none =>
      have hnext : stepOrHalt V (cfgAt V input t) = cfgAt V input t := by
        simp only [stepOrHalt, hstep]
      rw [hnext]
      omega

/-- **Lemma D — `h_adequate` with `maxStackDepth := n + timeBound`.** -/
theorem h_adequate_of_normal_form (params : Params V) (input : List (V.Γ V.k₀)) (n : ℕ)
    (hn : input.length = n) (hNF : NormalForm V)
    (hMD : params.maxStackDepth = n + params.timeBound) :
    ∀ t' k, t' ≤ params.timeBound →
      ((cfgAt V input t').stk k).length ≤ params.maxStackDepth := by
  intro t' k ht'
  have bound := stack_depth_bound input n hn hNF t' k
  rw [hMD]
  by_cases hk : k = V.k₀
  · rw [if_pos hk] at bound
    omega
  · rw [if_neg hk] at bound
    omega

/-- **Lemma E — `NormalForm V → BoundedReadDepth V`.** -/
theorem bounded_read_depth_of_normal_form (hNF : NormalForm V) : BoundedReadDepth V := by
  intro lbl k
  have touch : @stmtTouchDepth V.K V.Γ V.Λ V.σ k V.decidableEqK (V.m lbl) ≤ 1 := hNF lbl k
  have rd_le_td :=
    @stmtReadDepth_le_stmtTouchDepth V.K V.Γ V.Λ V.σ k V.decidableEqK (V.m lbl)
  have rd : @stmtReadDepth V.K V.Γ V.Λ V.σ k V.decidableEqK (V.m lbl) ≤ 1 :=
    le_trans rd_le_td touch
  exact rd

/-! ## Lemma F — Normal-form normalization (SCAFFOLD `sorry`) -/

/-- Normal-form normalization: any polytime TM2 verifier computing `g` can be transformed into a
    `NormalForm` verifier computing the same `g` with polynomial blowup (introduce intermediate
    labels so each statement chain touches each stack ≤ 1 time). STRUCTURAL — not a consequence
    of the time polynomial. This is the normal-form normalization sub-lemma; scaffolded here as
    a `sorry` per the handoff's concrete-scaffold guidance, to be closed as a separate
    code-as-proof effort. -/
theorem normal_form_normalization
    {α : Type} (ea : FinEncoding α) (g : α × List Bool → Bool)
    (g_comp : Turing.TM2ComputableInPolyTime (pairEncoding ea finEncodingBoolList)
      finEncodingBoolBool g) :
    ∃ (comp' : Turing.TM2ComputableInPolyTime (pairEncoding ea finEncodingBoolList)
        finEncodingBoolBool g), NormalForm comp'.tm := by
  -- GAP: normal-form transformation of an arbitrary polytime TM2 verifier.
  -- Introduce intermediate labels so each statement chain touches each stack ≤ 1 time;
  -- polynomial blowup (factor = max chain length, a machine constant).
  -- Structural, NOT a consequence of the time polynomial.
  sorry

end CookLevinTableau