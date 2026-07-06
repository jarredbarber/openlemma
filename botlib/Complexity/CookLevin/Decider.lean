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
  deriving DecidableEq, Fintype

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