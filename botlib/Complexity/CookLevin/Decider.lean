/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

# Decider transformation `V → V'` (D1 construction + D3 NormalForm preservation)

Concrete `FinTM2` construction of the decider `V'` that halts iff the verifier
`g` returns `true` (loops iff `g = false`), closing the halts-vs-accepts gap
(see `Assembly.lean` / `DECIDER_SPEC.md`).

## Sorry-free here
- `CheckLoop`, `liftStmt`, `checkStmt`, `loopStmt`, `decider` (definitions).
- `liftStmt_touchDepth` : `stmtTouchDepth k (liftStmt s) = stmtTouchDepth k s`
  (clean `Stmt` induction — `liftStmt` preserves every push/peek/pop).
- `decider_normal_form` (D3) : `NormalForm V → NormalForm (decider V outEquiv)`.

  KEY SIMPLIFICATION: `NormalForm` is per-STATEMENT (`stmtTouchDepth k (V'.m lbl)`
  for each `lbl`), NOT across labels. `liftStmt` redirects `halt → goto check`,
  so the V-portion's chain keeps its touches within `V'.m (inl l)` (preserved by
  `liftStmt_touchDepth`), and the output peek lives in `V'.m (inr check)` (a
  DIFFERENT label, ≤ 1 touch). No chain-splitting required.

## Remains sorry (D2 — the hard simulation lemma)
- `decider_halts_iff` : V' halts on `(a, cert)` within bound ↔ `g (a, cert) = true`.
  Needs the step-by-step simulation `cfgAt V' = cfgAt V` (V-portion) + the
  output-head convention. See `DECIDER_SPEC.md` §D2.
-/
import botlib.Complexity.CookLevin.Bridge3
import botlib.Complexity.CookLevin.Completeness
import botlib.Complexity.CookLevin.Tableau
import botlib.Complexity.Defs
import botlib.Complexity.Encodings
import Mathlib.Computability.TMComputable

namespace OpenLemma.Complexity.CookLevinAssembly

open Computability CookLevinTableau OpenLemma.Complexity

/-- The encoded pair `(a, cert)` as a tape over the verifier's input alphabet.
    `pairEncoding eb finEncodingBoolList` has `Γ = Sum eb.Γ Bool`; `hGamma` maps
    it to the machine's `Γ k₀`. -/
def encodedPairTape {β : Type} (eb : FinEncoding β) {V : Turing.FinTM2}
    (hGamma : V.Γ V.k₀ ≃ Sum eb.Γ Bool) (a : β) (cert : List Bool) :
    List (V.Γ V.k₀) :=
  ((pairEncoding eb finEncodingBoolList).encode (a, cert)).map hGamma.invFun

/-- A decider for `g : β × List Bool → Bool` is a `FinTM2` `V'` (with input
    alphabet `Sum eb.Γ Bool`) that halts on `(a, cert)` within `timeBound'`
    iff `g (a, cert) = true`. (D1 constructs `V'`; D2 proves `halts_iff`.) -/
structure DeciderSpec {β : Type} (eb : FinEncoding β) (g : β × List Bool → Bool) where
  /-- the decider machine -/
  V' : Turing.FinTM2
  /-- its input alphabet matches the verifier's (`Sum eb.Γ Bool`) -/
  hGamma' : V'.Γ V'.k₀ ≃ Sum eb.Γ Bool
  /-- polynomial time bound for the decider (poly in input length) -/
  timeBound' : ℕ → ℕ
  /-- D2: V' halts on `(a, cert)` within the bound iff `g (a, cert) = true`. -/
  halts_iff :
    ∀ a cert,
      (∃ i, i ≤ timeBound' ((eb.encode a).length + cert.length) ∧
        (cfgAt V' (encodedPairTape eb hGamma' a cert) i).l = none) ↔
      g (a, cert) = true

/-- Two extra labels for the decider: `check` (peek output, branch) and `loop`
    (the non-halting trap reached when `g = false`). -/
inductive CheckLoop : Type
  | check : CheckLoop
  | loop : CheckLoop
  deriving DecidableEq, Fintype, Encodable

/-- Lift a verifier statement (state `σ`, labels `Λ`) to a decider statement
    (state `σ × σ'`, labels `Λ ⊕ CheckLoop`), preserving the second state
    component and redirecting `halt → goto check`. -/
def liftStmt {K : Type*} {Γ : K → Type*} {Λ : Type*} {σ : Type*} {σ' : Type*}
    (s : Turing.TM2.Stmt Γ Λ σ) : Turing.TM2.Stmt Γ (Λ ⊕ CheckLoop) (σ × σ') :=
  match s with
  | .push k f q     => .push k (fun (v, _) => f v) (liftStmt q)
  | .peek k f q     => .peek k (fun (v, h) oh => (f v oh, h)) (liftStmt q)
  | .pop k f q      => .pop k (fun (v, h) oh => (f v oh, h)) (liftStmt q)
  | .load a q       => .load (fun (v, h) => (a v, h)) (liftStmt q)
  | .branch f q₁ q₂ => .branch (fun (v, h) => f v) (liftStmt q₁) (liftStmt q₂)
  | .goto l         => .goto (fun (v, _) => .inl (l v))
  | .halt           => .goto (fun _ => .inr CheckLoop.check)

/-- `liftStmt` preserves the touch depth of every stack: it maps each
    push/peek/pop to a push/peek/pop (same key), and goto/halt/load/branch
    contribute identically. (halt → goto contributes 0 either way.) -/
theorem liftStmt_touchDepth {K : Type*} {Γ : K → Type*} {Λ : Type*} {σ : Type*}
    {σ' : Type*} [DecidableEq K] (k : K) (s : Turing.TM2.Stmt Γ Λ σ) :
    stmtTouchDepth k (@liftStmt K Γ Λ σ σ' s) = stmtTouchDepth k s := by
  induction s with
  | push k' f q ih => simp only [liftStmt, stmtTouchDepth, ih]
  | peek k' f q ih => simp only [liftStmt, stmtTouchDepth, ih]
  | pop k' f q ih => simp only [liftStmt, stmtTouchDepth, ih]
  | load a q ih => simp only [liftStmt, stmtTouchDepth, ih]
  | branch f q₁ q₂ ih₁ ih₂ => simp only [liftStmt, stmtTouchDepth, ih₁, ih₂]
  | goto l => simp only [liftStmt, stmtTouchDepth]
  | halt => simp only [liftStmt, stmtTouchDepth]

/-- The `check` statement: peek the output stack `k₁`, store its head in the
    state, branch on "head maps to `true`" → halt, else → `loop`.
    `outEquiv : V.Γ V.k₁ ≃ Bool` witnesses the output alphabet is Bool. -/
def checkStmt (V : Turing.FinTM2) (outEquiv : V.Γ V.k₁ ≃ Bool) :
    Turing.TM2.Stmt V.Γ (V.Λ ⊕ CheckLoop) (V.σ × Option (V.Γ V.k₁)) :=
  .peek V.k₁ (fun (v, _) oh => (v, oh))
    (.branch (fun (v, h) => h.map outEquiv |>.getD false)
       .halt
       (.goto (fun _ => .inr CheckLoop.loop)))

/-- The `loop` trap: `goto loop` forever (never halts). -/
def loopStmt (V : Turing.FinTM2) :
    Turing.TM2.Stmt V.Γ (V.Λ ⊕ CheckLoop) (V.σ × Option (V.Γ V.k₁)) :=
  .goto (fun _ => .inr CheckLoop.loop)

/-- The decider machine `V'`: runs `V` (lifted, `halt → check`), then peeks the
    output and branches `true → halt`, `false → loop`.
    State = `V.σ × Option (V.Γ V.k₁)`; labels = `V.Λ ⊕ CheckLoop`;
    stacks/alphabets/keys unchanged. -/
def decider (V : Turing.FinTM2) (outEquiv : V.Γ V.k₁ ≃ Bool) [Fintype (V.Γ V.k₁)] :
    Turing.FinTM2 where
  K := V.K
  kDecidableEq := V.kDecidableEq
  kFin := V.kFin
  k₀ := V.k₀
  k₁ := V.k₁
  Γ := V.Γ
  Λ := V.Λ ⊕ CheckLoop
  main := .inl V.main
  ΛFin := by have := V.ΛFin; exact inferInstance
  σ := V.σ × Option (V.Γ V.k₁)
  initialState := (V.initialState, none)
  σFin := by have := V.σFin; exact inferInstance
  Γk₀Fin := V.Γk₀Fin
  m := fun lbl =>
    match lbl with
    | .inl l => liftStmt (V.m l)
    | .inr CheckLoop.check => checkStmt V outEquiv
    | .inr CheckLoop.loop => loopStmt V

/-- D3 (sorry-free): the decider is in `NormalForm` whenever the verifier is.
    `liftStmt` preserves touch depth (per-label), `check` peeks `k₁` once (≤ 1),
    and `loop` touches nothing. No chain-splitting required. -/
theorem decider_normal_form (V : Turing.FinTM2) (outEquiv : V.Γ V.k₁ ≃ Bool)
    [Fintype (V.Γ V.k₁)] (hNF : NormalForm V) : NormalForm (decider V outEquiv) := by
  intro lbl k
  rcases lbl with l | cl
  · show stmtTouchDepth k (liftStmt (V.m l)) ≤ 1
    rw [liftStmt_touchDepth k (V.m l)]
    exact hNF l k
  · rcases cl with rfl | rfl
    · show stmtTouchDepth k (checkStmt V outEquiv) ≤ 1
      simp only [checkStmt, stmtTouchDepth]
      by_cases h : V.k₁ = k
      · subst k; simp only [if_true]; omega
      · simp only [if_neg h]; omega
    · show stmtTouchDepth k (loopStmt V) ≤ 1
      simp only [loopStmt, stmtTouchDepth]; omega

/-- D2 core (SORRY-FREE): one `stepAux` of the lifted statement simulates one
    `stepAux` of the original statement, threading the second state component `h`
    and redirecting `halt → goto check`. This is the structural-induction heart of
    `decider_halts_iff`; the `cfgAt`-level lifting and output-head convention
    assemble it into the full iff (see `DECIDER_SPEC.md` §D2).

    Concretely: `stepAux (liftStmt s) (v, h) S` equals `stepAux s v S` with the
    label wrapped `Sum.inl` (running) or sent to `inr check` (V halted), and the
    state paired with the unchanged `h`. -/
theorem stepAux_liftStmt {K : Type*} {Γ : K → Type*} {Λ : Type*} {σ : Type*}
    {σ' : Type*} [DecidableEq K] (s : Turing.TM2.Stmt Γ Λ σ) (v : σ) (h : σ')
    (S : ∀ k, List (Γ k)) :
    Turing.TM2.stepAux (liftStmt s) (v, h) S =
      match Turing.TM2.stepAux s v S with
      | ⟨some l, v', S'⟩ => ⟨some (Sum.inl l), (v', h), S'⟩
      | ⟨none, v', S'⟩ => ⟨some (Sum.inr CheckLoop.check), (v', h), S'⟩ := by
  induction s generalizing v h S with
  | push k' f q ih => simp only [liftStmt, Turing.TM2.stepAux.eq_1]; rw [ih]
  | peek k' f q ih => simp only [liftStmt, Turing.TM2.stepAux.eq_2]; rw [ih]
  | pop k' f q ih => simp only [liftStmt, Turing.TM2.stepAux.eq_3]; rw [ih]
  | load a q ih => simp only [liftStmt, Turing.TM2.stepAux.eq_4]; rw [ih]
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [liftStmt, Turing.TM2.stepAux.eq_5]
    cases h' : f v with
    | true => simp only [h', Bool.cond_true]; rw [ih₁]
    | false => simp only [h', Bool.cond_false]; rw [ih₂]
  | goto l => simp only [liftStmt, Turing.TM2.stepAux.eq_6]
  | halt => simp only [liftStmt, Turing.TM2.stepAux.eq_6, Turing.TM2.stepAux.eq_7]

/-- The decider's statement at a verifier label `lbl` is the lifted verifier
    statement. (Needed because `(decider V outEquiv).m (Sum.inl lbl)` does not reduce
    under `rw`/`rfl` auto-closing — `decider` is not `reducible`.) -/
theorem decider_m_inl (V : Turing.FinTM2) (outEquiv : V.Γ V.k₁ ≃ Bool)
    [Fintype (V.Γ V.k₁)] (lbl : V.Λ) :
    (decider V outEquiv).m (Sum.inl lbl) = liftStmt (V.m lbl) := by
  simp only [decider]

/-- D2 lifting (SORRY-FREE): while `V` is still running at step `t`, the decider
    `V'` at step `t` is exactly the V-configuration with the label wrapped `Sum.inl`,
    the state paired with `none`, and the same stacks. Proved by induction on `t`,
    using `stepOrHalt_running` + `stepAux_liftStmt`; the "once halted, stays halted"
    fact (`cfgAt_halted_succ`) supplies the predecessor-running hypothesis.

    This is the `cfgAt`-level simulation lemma; combined with the halting-step
    analysis and the output-head convention it closes `decider_halts_iff`. -/
theorem cfgAt_decider_while_running (V : Turing.FinTM2) (outEquiv : V.Γ V.k₁ ≃ Bool)
    [Encodable V.Λ] [Encodable V.σ] [Encodable V.K] [∀ k, Encodable (V.Γ k)]
    [Fintype V.Λ] [Fintype V.σ] [Fintype V.K] [∀ k, Fintype (V.Γ k)]
    [DecidableEq V.K] [∀ k, DecidableEq (V.Γ k)]
    [DecidableEq V.Λ] [DecidableEq V.σ]
    [Fintype (V.Γ V.k₁)] (input : List (V.Γ V.k₀)) (t : ℕ) :
    (cfgAt V input t).l ≠ none →
    cfgAt (decider V outEquiv) input t =
      ⟨(cfgAt V input t).l.map Sum.inl, ((cfgAt V input t).var, none), (cfgAt V input t).stk⟩ := by
  haveI : Encodable (decider V outEquiv).Λ := inferInstanceAs (Encodable (V.Λ ⊕ CheckLoop))
  haveI : Encodable (decider V outEquiv).σ :=
    inferInstanceAs (Encodable (V.σ × Option (V.Γ V.k₁)))
  haveI : Encodable (decider V outEquiv).K := inferInstanceAs (Encodable V.K)
  haveI : ∀ k, Encodable ((decider V outEquiv).Γ k) := inferInstanceAs (∀ k, Encodable (V.Γ k))
  haveI : Fintype (decider V outEquiv).Λ := inferInstanceAs (Fintype (V.Λ ⊕ CheckLoop))
  haveI : Fintype (decider V outEquiv).σ :=
    inferInstanceAs (Fintype (V.σ × Option (V.Γ V.k₁)))
  haveI : Fintype (decider V outEquiv).K := inferInstanceAs (Fintype V.K)
  haveI : ∀ k, Fintype ((decider V outEquiv).Γ k) := inferInstanceAs (∀ k, Fintype (V.Γ k))
  haveI : DecidableEq (decider V outEquiv).Λ := inferInstanceAs (DecidableEq (V.Λ ⊕ CheckLoop))
  haveI : DecidableEq (decider V outEquiv).σ :=
    inferInstanceAs (DecidableEq (V.σ × Option (V.Γ V.k₁)))
  haveI : DecidableEq (decider V outEquiv).K := inferInstanceAs (DecidableEq V.K)
  haveI : ∀ k, DecidableEq ((decider V outEquiv).Γ k) := inferInstanceAs (∀ k, DecidableEq (V.Γ k))
  induction t with
  | zero =>
    intro _
    simp only [cfgAt, Function.iterate_zero]
    rfl
  | succ t ih =>
    intro h
    have h0' : (cfgAt V input t).l ≠ none := by
      intro hc
      rw [cfgAt_halted_succ input t hc] at h
      exact h hc
    cases hl : (cfgAt V input t).l with
    | none => exact absurd hl h0'
    | some lbl =>
      have hsuccV : cfgAt V input (t + 1) =
          Turing.TM2.stepAux (V.m lbl) (cfgAt V input t).var (cfgAt V input t).stk := by
        rw [cfgAt_succ, stepOrHalt_running hl]
      have ih' := ih h0'
      rw [hl] at ih'
      simp only [Option.map_some] at ih'
      have hsuccV' : cfgAt (decider V outEquiv) input (t + 1) =
          Turing.TM2.stepAux (liftStmt (V.m lbl)) ((cfgAt V input t).var, none)
            (cfgAt V input t).stk := by
        rw [cfgAt_succ, ih',
          stepOrHalt_running (rfl :
            (⟨some (Sum.inl lbl), ((cfgAt V input t).var, none), (cfgAt V input t).stk⟩ :
              (decider V outEquiv).Cfg).l = some (Sum.inl lbl)),
          decider_m_inl V outEquiv lbl]
      rw [stepAux_liftStmt (V.m lbl) (cfgAt V input t).var (none : Option (V.Γ V.k₁))
          (cfgAt V input t).stk] at hsuccV'
      rw [hsuccV] at h
      cases hstep : Turing.TM2.stepAux (V.m lbl) (cfgAt V input t).var (cfgAt V input t).stk with
      | mk l' v' S' =>
        cases l' with
        | none => rw [hstep] at h; exact absurd rfl h
        | some l'' =>
          rw [hstep] at hsuccV hsuccV'
          have key : cfgAt (decider V outEquiv) input (t + 1) =
              ⟨some (Sum.inl l''), (v', none), S'⟩ := by rw [hsuccV']
          rw [key, hsuccV]
          rfl

/-! ### D2 halting-step: the decider reaches `check` when `V` halts

If `V` is running at step `T-1` and halts at step `T` with output `out` (i.e.
`cfgAt V input T = haltList V out`), then the decider `V'` at step `T` is at the `check`
label, carrying `haltList V out`'s variable and stacks — so the decider's `k₁` stack
is exactly `out`, and the next step (`checkStmt`) peeks `out.head?` and branches.

This consumes `cfgAt_reaches_halt_first` (which supplies `hrun` and `hhalt` from
`TM2OutputsInTime`); combined with `stepAux_checkStmt` (the `T+1` transition) it
closes `decider_halts_iff`.
-/
theorem cfgAt_decider_at_check (V : Turing.FinTM2) (outEquiv : V.Γ V.k₁ ≃ Bool)
    [Encodable V.Λ] [Encodable V.σ] [Encodable V.K] [∀ k, Encodable (V.Γ k)]
    [Fintype V.Λ] [Fintype V.σ] [Fintype V.K] [∀ k, Fintype (V.Γ k)]
    [DecidableEq V.K] [∀ k, DecidableEq (V.Γ k)]
    [DecidableEq V.Λ] [DecidableEq V.σ]
    [Fintype (V.Γ V.k₁)] (input : List (V.Γ V.k₀)) (out : List (V.Γ V.k₁)) (T : ℕ)
    (hTpos : 1 ≤ T)
    (hrun : (cfgAt V input (T-1)).l ≠ none)
    (hhalt : cfgAt V input T = Turing.haltList V out) :
    cfgAt (decider V outEquiv) input T =
      ⟨some (Sum.inr CheckLoop.check), ((Turing.haltList V out).var, none), (Turing.haltList V out).stk⟩ := by
  -- 12 instance shims for the decider's projection fields (decider is not reducible).
  haveI : Encodable (decider V outEquiv).Λ := inferInstanceAs (Encodable (V.Λ ⊕ CheckLoop))
  haveI : Encodable (decider V outEquiv).σ := inferInstanceAs (Encodable (V.σ × Option (V.Γ V.k₁)))
  haveI : Encodable (decider V outEquiv).K := inferInstanceAs (Encodable V.K)
  haveI : ∀ k, Encodable ((decider V outEquiv).Γ k) := inferInstanceAs (∀ k, Encodable (V.Γ k))
  haveI : Fintype (decider V outEquiv).Λ := inferInstanceAs (Fintype (V.Λ ⊕ CheckLoop))
  haveI : Fintype (decider V outEquiv).σ := inferInstanceAs (Fintype (V.σ × Option (V.Γ V.k₁)))
  haveI : Fintype (decider V outEquiv).K := inferInstanceAs (Fintype V.K)
  haveI : ∀ k, Fintype ((decider V outEquiv).Γ k) := inferInstanceAs (∀ k, Fintype (V.Γ k))
  haveI : DecidableEq (decider V outEquiv).Λ := inferInstanceAs (DecidableEq (V.Λ ⊕ CheckLoop))
  haveI : DecidableEq (decider V outEquiv).σ := inferInstanceAs (DecidableEq (V.σ × Option (V.Γ V.k₁)))
  haveI : DecidableEq (decider V outEquiv).K := inferInstanceAs (DecidableEq V.K)
  haveI : ∀ k, DecidableEq ((decider V outEquiv).Γ k) := inferInstanceAs (∀ k, DecidableEq (V.Γ k))
  -- V' at T-1 = running config (V's label wrapped inl, V's var/stk, no cert-head).
  have hVTm1 := cfgAt_decider_while_running V outEquiv input (T-1) hrun
  cases hl : (cfgAt V input (T-1)).l with
  | none => exact absurd hl hrun
  | some lbl =>
    -- V' at T = stepAux (liftStmt (V.m lbl)) (V.var, none) V.stk
    --   (via cfgAt_succ [T = (T-1)+1] + stepOrHalt_running + decider_m_inl)
    have hVT : cfgAt (decider V outEquiv) input T =
        Turing.TM2.stepAux (liftStmt (V.m lbl)) ((cfgAt V input (T-1)).var, none) (cfgAt V input (T-1)).stk := by
      conv_lhs => rw [show T = (T - 1) + 1 from by omega]
      rw [cfgAt_succ, hVTm1, hl, Option.map_some,
        stepOrHalt_running (rfl :
          (⟨some (Sum.inl lbl), ((cfgAt V input (T-1)).var, none), (cfgAt V input (T-1)).stk⟩ :
            (decider V outEquiv).Cfg).l = some (Sum.inl lbl)),
        decider_m_inl V outEquiv lbl]
    -- V at T = stepAux (V.m lbl) (V.var) (V.stk) = haltList V out  (via cfgAt_succ + stepOrHalt_running)
    have hVTstep : Turing.TM2.stepAux (V.m lbl) (cfgAt V input (T-1)).var (cfgAt V input (T-1)).stk =
        Turing.haltList V out := by
      have hVT' : cfgAt V input T =
          Turing.TM2.stepAux (V.m lbl) (cfgAt V input (T-1)).var (cfgAt V input (T-1)).stk := by
        conv_lhs => rw [show T = (T - 1) + 1 from by omega]
        rw [cfgAt_succ, stepOrHalt_running hl]
      rw [← hVT', hhalt]
    -- stepAux_liftStmt: the decider redirects V's halt → goto check (the `none` branch).
    rw [hVT, stepAux_liftStmt (V.m lbl) (cfgAt V input (T-1)).var (none : Option (V.Γ V.k₁))
        (cfgAt V input (T-1)).stk, hVTstep]
    rfl

/-- D2 (SORRY): the decider halts on `(a, cert)` within `comp.time + 2` iff
    `g (a, cert) = true`.

    WIRED TO THE WITNESS: `comp : TM2ComputableInPolyTime ... g` supplies the machine
    computing `g` (`comp.tm`), the output alphabet equiv (`comp.outputAlphabet`),
    the input alphabet equiv (`comp.inputAlphabet`), and the time bound (`comp.time`).
    This fixes the prior BREAK where an arbitrary `V`/`outEquiv`/`Nonempty hComp` were
    disconnected — V could have computed a different function than `g`.

    Proof sketch (see `DECIDER_SPEC.md` §D2): step-by-step simulation
    `cfgAt (decider comp.tm comp.outputAlphabet) = cfgAt comp.tm` on the V-portion
    (structural induction on `Stmt` via `liftStmt` semantics + `cfgAt_succ`), then
    `comp.outputsFun` gives the output-head convention `head k₁ = g(a,cert)`, and
    `checkStmt` branches `true → halt`, `false → loop`. -/
theorem decider_halts_iff {β : Type} (eb : FinEncoding β) (g : β × List Bool → Bool)
    (comp : Turing.TM2ComputableInPolyTime (pairEncoding eb finEncodingBoolList)
        finEncodingBoolBool g)
    [Fintype (comp.tm.Γ comp.tm.k₁)] :
    ∀ a cert,
      (∃ i, i ≤ comp.time.eval ((pairEncoding eb finEncodingBoolList).encode (a, cert)).length + 2 ∧
        (cfgAt (decider comp.tm comp.outputAlphabet)
          (encodedPairTape eb comp.inputAlphabet a cert) i).l = none) ↔
      g (a, cert) = true := by
  sorry

end OpenLemma.Complexity.CookLevinAssembly