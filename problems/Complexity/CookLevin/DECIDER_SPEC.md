# Decider Construction Spec (D1–D3)

This document specifies the **decider transformation** `V → V'` required to close
the halts-vs-accepts gap in the Cook-Levin assembly (Bridge 5 backward
direction). It is the hardest remaining component (`decider_exists` /
`decider_normal_form` in `Assembly.lean`). Every field and helper below is
specified concretely so that the Lean construction is mechanical (if tedious).

## Why the decider is required (reviewer-verified)

`acceptanceConstraints` (Tableau.lean:179) encodes **halting**
(`∃ i, label i = none`), NOT output = true. The `InNP` verifier `g` is **total**
(`TM2ComputableInPolyTime.outputsFun` halts on ALL inputs within the time bound,
including `g a = false`). The backward chain is:

```
Satisfiable (tableauFormulaCert params aInput certBound boolSyms)
  →[completeness_cert] ∃ cert, Satisfiable (tableauFormula (aInput ++ cert))
  →[completeness]      ∃ i ≤ timeBound, (cfgAt V (aInput ++ cert) i).l = none
                       (V halts on (aInput ++ cert))
```

If `V` is total, "V halts" is true for EVERY cert, so backward yields no
information about `g`. The fix: replace `V` with a **decider** `V'` that halts
iff `g = true` (loops iff `g = false`). Then backward's "∃ cert, V' halts"
becomes "∃ cert, g(a,cert) = true" = `L' a`.

**Forward direction also uses V'** (the tableau is for one machine):
`L' a → ∃ cert, g=true →[D2(→)] V' halts →[reduction_sound_cert] Satisfiable(f a)`.

## Mathlib `Stmt` constructors (TuringMachine.lean:127)

```
inductive Stmt
  | push : ∀ k, (σ → Γ k) → Stmt → Stmt        -- push f v on stack k, then q
  | peek : ∀ k, (σ → Option (Γ k) → σ) → Stmt → Stmt  -- peek head (no remove), update state, then q
  | pop  : ∀ k, (σ → Option (Γ k) → σ) → Stmt → Stmt  -- pop head, update state, then q
  | load : (σ → σ) → Stmt → Stmt               -- update state, then q
  | branch : (σ → Bool) → Stmt → Stmt → Stmt   -- if f v then q1 else q2
  | goto : (σ → Λ) → Stmt                       -- set label to f v
  | halt : Stmt                                  -- set label to none (halt)
```

**Critical**: `branch` reads ONLY the state `σ`, not the stacks. To branch on a
stack head, one must `peek`/`pop` it into the state first, then `branch`. This
forces `V'` to carry the peeked output in its state.

## V' machine specification (D1)

### Alphabets & state

| Field | Value | Rationale |
|-------|-------|-----------|
| `V'.Λ` | `V.Λ ⊎ CheckLoop` where `inductive CheckLoop \| check \| loop` | add a check phase + a loop trap |
| `V'.σ` | `V.σ × Option Bool` | carry the peeked k₁ head (`Bool`, since output alphabet is `finEncodingBoolBool.Γ = Bool`) |
| `V'.K` | `V.K` | same stacks |
| `V'.Γ` | `V.Γ` | same stack alphabets |
| `V'.k₀` | `V.k₀` | same input stack |
| `V'.k₁` | `V.k₁` | same output stack (peeked by check) |
| `V'.l₀` | `inl V.l₀` | start where V starts |
| `V'.s₀` | `(V.s₀, none)` | start state (no peeked value yet) |
| `V'.main` | `inl V.main` | main entry (matches reduction_sound_cert's `V.main`) |

### Instances (mechanical, via `deriving`/explicit)

- `V'.Λ = V.Λ ⊎ CheckLoop`: `Encodable` (sum + empty/enum), `Fintype` (sum of
  fintypes; `CheckLoop` is a 2-element fintype), `DecidableEq` (sum decidable).
- `V'.σ = V.σ × Option Bool`: `Encodable` (prod + option), `Fintype` (prod of
  fintypes), `DecidableEq` (prod decidable).
- `V'.K, V'.Γ, V'.k₀, V'.k₁`: inherited from `V` (same types), so instances
  carry over (`V'.decidableEqK = V.decidableEqK`, etc.).

`CheckLoop` should be declared with `deriving Encodable, Fintype, DecidableEq`
(2-element inductive). The sum instances come from Mathlib's
`Encodable.sumEncodable`, `Fintype.sumFintype`, `Sum.instDecidableEq`; the prod
instances from `Encodable.prodEncodable`, `Fintype.prodFintype`,
`Prod.instDecidableEq`.

### `V'.m` : the transition function

Define two helpers, then `V'.m`:

**`liftStmt`** — lifts a `V`-statement (state `V.σ`, labels `V.Λ`) to a `V'`-
statement (state `V.σ × Option Bool`, labels `V.Λ ⊎ CheckLoop`), preserving the
second state component and redirecting `halt → goto check`:

```
def liftStmt (s : TM2.Stmt V.σ V.Γ V.K V.Λ) : TM2.Stmt (V.σ × Option Bool) V.Γ V.K (V.Λ ⊎ CheckLoop) :=
  match s with
  | .push k f q     => .push k (fun (v, h) => f v) (liftStmt q)
  | .peek k f q     => .peek k (fun (v, h) oh => (f v oh, h)) (liftStmt q)
  | .pop k f q      => .pop k (fun (v, h) oh => (f v oh, h)) (liftStmt q)
  | .load a q       => .load (fun (v, h) => (a v, h)) (liftStmt q)
  | .branch f q1 q2 => .branch (fun (v, h) => f v) (liftStmt q1) (liftStmt q2)
  | .goto l         => .goto (fun (v, h) => .inl (l v))
  | .halt           => .goto (fun _ => .inr .check)   -- redirect halt to check
```

**Check + loop statements:**

```
-- peek k₁ head into state, branch on (head = some true): true → halt, false → loop
def checkStmt : TM2.Stmt (V.σ × Option Bool) V.Γ V.K (V.Λ ⊎ CheckLoop) :=
  .peek V.k₁ (fun (v, _) oh => (v, oh))        -- store peeked head (a Bool) in 2nd component
    (.branch (fun (v, h) => h = some true)
       .halt                                    -- g = true → halt
       (.goto (fun _ => .inr .loop)))           -- g = false → loop

-- loop trap: goto loop forever (never halts)
def loopStmt : TM2.Stmt (V.σ × Option Bool) V.Γ V.K (V.Λ ⊎ CheckLoop) :=
  .goto (fun _ => .inr .loop)
```

**`V'.m`:**

```
V'.m := fun lbl =>
  match lbl with
  | .inl l  => liftStmt (V.m l)
  | .inr .check => checkStmt
  | .inr .loop  => loopStmt
```

### `shift`, `Supports`

- `V'.shift := liftStmt V.shift` (or the check/loop as appropriate; `shift` is
  the statement run when the machine "shifts" — check Mathlib's `FinTM2.shift`
  semantics; likely `liftStmt V.shift` suffices, or it can be `halt`/a no-op
  depending on the model). **VERIFY** against `FinTM2` definition.
- `Supports`: `V'.supports` must hold for the start label. The lifted statements
  support `inl V.l₀ ∪ {inr check, inr loop}`. Since `liftStmt` redirects halt →
  check and gotos → inl, and check/loop reference only `inr check`/`inr loop`,
  the support set is closed. This is a `Supports` proof (mechanical via the
  `SupportsStmt` induction).

## D2: `decider_halts_iff_g_true` (both directions)

**Statement** (the `halts_iff` field of `DeciderSpec`):
```
∀ a cert,
  (∃ i, i ≤ timeBound'.eval ((eb.encode a).length + cert.length) ∧
    (cfgAt V' (encodedPairTape eb hGamma' a cert) i).l = none) ↔
  g (a, cert) = true
```

where `timeBound'.eval n = V.timeBound.eval n + C` for a constant `C` (the check
phase takes O(1) extra steps after V halts; `C` ≈ 2: one peek, one branch).

### Proof sketch

**Forward (V' halts → g = true):** By contrapositive. If `g(a,cert) = false`,
then V's output on k₁ is `finEncodingBoolBool.encode false = [false]`, so k₁'s
head at V's halting step is `false`. V' simulates V (simulation lemma below)
until V would halt, then `liftStmt` redirects to `check`; `check` peeks k₁ head
= `false`, branches to `loop`; `loop` gotos `loop` forever. So V' never halts.
Contrapositive: V' halts → g = true.

**Backward (g = true → V' halts):** If `g(a,cert) = true`, V's output k₁ head
= `true`. V' simulates V (which halts within `V.timeBound` since g is total /
computable-in-poly-time), redirects to `check`, peeks `true`, branches to `halt`.
So V' halts within `V.timeBound + 2`.

### Key sub-lemma: simulation (V' simulates V on the V-portion)

```
theorem decider_simulates (a : β) (cert : List Bool) :
  ∀ i ≤ V.timeBound.eval n,
    let cfgV  := cfgAt V  (encodedPairTape eb hGamma a cert) i
    let cfgV' := cfgAt V' (encodedPairTape eb hGamma' a cert) i
    cfgV'.l = (cfgV.l).map (.inl)  -- V' label = inl of V label (while V not halted)
    ∧ cfgV'.var = (cfgV.var, none) -- V' state = V state, no peeked value yet
    ∧ cfgV'.stk = cfgV.stk          -- same stacks
```

(When V would halt at step i, V' at step i is at label `inr check` instead of
`none`; the simulation holds for steps before V halts.) Proved by induction on
`i`, using `cfgAt_succ` and the definition of `liftStmt` (each `Stmt` constructor
lifts faithfully). This is the crux sub-lemma — a careful `Stmt`-induction.

### Output convention sub-lemma

```
theorem V_output_head_iff_g (a cert) :
  g (a, cert) = true ↔
    ((cfgAt V (encodedPairTape eb hGamma a cert) (V.timeBound.eval n)).stk V.k₁).head? = some true
```

This follows from `TM2ComputableInPolyTime.outputsFun`: V halts within the time
bound with output `finEncodingBoolBool.encode (g(a,cert))` on k₁, and
`finEncodingBoolBool.encode true = [true]`, `encode false = [false]`. **VERIFY**
the exact output-stack convention in Mathlib's `TM2ComputableInPolyTime`
(`outputsFun` field + how output is placed on k₁).

## D3: `decider_normal_form` (NormalForm V → NormalForm V')

`NormalForm V := ∀ lbl k, stmtTouchDepth k (V.m lbl) ≤ 1`
(each statement chain touches each stack ≤ 1 time: at most one push+peek+pop per
stack per chain).

**The subtlety:** If `V.m l` ends with `... push k₁ f halt` (a push to k₁
immediately before halt), then `liftStmt` produces `... push k₁ f (goto check)`,
and `check` does `peek k₁ ...`. So in `V'.m(inl l)`, k₁ is touched (pushed) once,
and then control flows to `inr check` which touches k₁ (peek) again. BUT
`NormalForm` is per-STATEMENT (`stmtTouchDepth k (V'.m lbl)` for each `lbl`
separately), NOT across labels. `V'.m(inl l)` touches k₁ once (the push); the
peek is in `V'.m(inr check)`, a DIFFERENT label. So `stmtTouchDepth k₁ (V'.m(inl l))`
counts only the push = 1, and `stmtTouchDepth k₁ (V'.m(inr check))` counts only
the peek = 1. **So D3 holds WITHOUT chain-splitting** — the redirect to a
separate `check` label naturally separates the touches across labels.

Wait — re-examine. `liftStmt` replaces `halt` with `goto check` at the END of the
chain. If `V.m l = push k₁ f halt`, then `liftStmt (V.m l) = push k₁ f (goto check)`.
`stmtTouchDepth k₁ (push k₁ f (goto check))` = 1 (one push; goto doesn't touch).
And `stmtTouchDepth k₁ checkStmt` = 1 (one peek). Both ≤ 1. ✓

**The ONLY risk:** a `V.m l` whose chain touches k₁ TWICE already would violate
`NormalForm V` — but `NormalForm V` PRECLUDES that. So under `NormalForm V`,
`liftStmt (V.m l)` touches each stack ≤ 1 time (liftStmt preserves touch count:
push/peek/pop map to push/peek/pop, goto/halt/load don't touch). Hence
`stmtTouchDepth k (liftStmt (V.m l)) = stmtTouchDepth k (V.m l) ≤ 1`. ✓

And `checkStmt` touches only k₁ once (peek); other stacks 0. `loopStmt` touches
nothing. So `NormalForm V'` holds. **D3 proof:**
```
intro lbl k
cases lbl with
| inl l => simp [V'.m, liftStmt]; exact hNF l k   -- liftStmt preserves touch depth
| inr cl => cases cl <;> simp [V'.m, checkStmt, loopStmt, stmtTouchDepth]  -- ≤ 1 by computation
```

**The `stmtTouchDepth`-preservation lemma** (needed for the `inl` case):
```
theorem liftStmt_touchDepth (s : TM2.Stmt V.σ V.Γ V.K V.Λ) (k : V.K) :
  stmtTouchDepth k (liftStmt s) = stmtTouchDepth k s
```
proved by `Stmt` induction on `s` (liftStmt maps each touch constructor to the
same constructor, so depth is identical). This is a clean induction — likely
sorry-free.

## Lemma F dependency (NormalForm V)

D2's simulation does NOT need `NormalForm V` — it needs V to be the verifier
computing g (via `TM2ComputableInPolyTime`), which is given by `hComp`. But
`reduction_sound_cert` / `completeness` (called in `bridge5_iff`) need
`BoundedReadDepth V'` (from Bridge 3's `bounded_read_depth_of_normal_form` under
`NormalForm V'`). So `NormalForm V'` (D3) is needed for Bridge 5, and `NormalForm V'`
follows from `NormalForm V` (D3) — so `NormalForm V` is needed.

`NormalForm V` itself comes from Lemma F (`normal_form_normalization`, Bridge 3
sorry): any polytime verifier can be normalized to NormalForm with polynomial
blowup. So Bridge 5 depends on Lemma F via D3. **If Lemma F is not closed,
Bridge 5 stays sorry.** Lemma F is a separate, substantial sub-lemma (chain-
splitting: break a chain touching a stack twice into two labels via a fresh
intermediate state).

## Summary of construction effort

| Piece | Difficulty | Depends on |
|-------|-----------|------------|
| `liftStmt` def | mechanical | — |
| `checkStmt`, `loopStmt`, `V'.m` | mechanical | `liftStmt` |
| `FinTM2` instances for V' | tedious (sum/prod instances) | — |
| `Supports` proof | mechanical (induction) | `V'.m` |
| `liftStmt_touchDepth` (D3 core) | clean induction | `liftStmt`, `stmtTouchDepth` |
| `decider_normal_form` (D3) | easy, given touchDepth | D3 core |
| `V_output_head_iff_g` | needs Mathlib output-convention check | `outputsFun` |
| `decider_simulates` (D2 core) | **hard** — careful Stmt-induction + cfgAt | `liftStmt`, `cfgAt` |
| `decider_halts_iff_g_true` (D2) | medium — assembles simulation + output | D2 core |

The **single hardest piece** is `decider_simulates` (relating `cfgAt V` and
`cfgAt V'` step-by-step). Everything else is mechanical.

## Open verification items (check before/during construction)

1. **`FinTM2.shift` semantics**: what is `shift` and does `liftStmt V.shift`
   suffice? (Read `FinTM2` structure in TMComputable.lean:45–106.)
2. **`TM2ComputableInPolyTime` output convention**: how is the output placed on
   k₁? Is it `encode` of the result, head-first? (Read `outputsFun` field.)
3. **`finEncodingBoolBool.encode`**: confirm `encode true = [true]`,
   `encode false = [false]` (head = the bool). (Encoding.lean:192.)
4. **`cfgAt` / `cfgAt_succ`** exact statements for the simulation induction.
   (Completeness.lean:218, 221.)
5. **`V.main`** vs `V.l₀`: which is the start label used by
   `reduction_sound_cert`'s `h_init`? (CertTableau.lean:188 uses `V.main`.)
   Ensure `V'.main = inl V.main` and the simulation starts there.