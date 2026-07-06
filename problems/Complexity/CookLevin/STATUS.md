# Status: Cook-Levin crux-axiom elimination

## Current State
Build green (`lake build botlib.Complexity.CookLevin`, only linter warnings). Starting Bridge 1
(verifier-semantics: `EvalsToInTime ↔ cfgAt-halts`).

## Lemma Pipeline
| Lemma | Python | Review | Lean | Notes |
|-------|--------|--------|------|-------|
| lemma_K_some_implies_S_eq (invariant) | ✅ | APPROVED | ✅ | `kleene_some_implies_stepOrHalt_eq` (Bridge1.lean) |
| lemma_TM2OutputsInTime_to_cfgAt_halt | ✅ | APPROVED | ✅ | `cfgAt_reaches_halt` (Bridge1.lean), 0 sorries |
| bridge2_initTape_decomp | ✅ | APPROVED | ✅ | `initTape_decomp` (Bridge2.lean) |
| bridge2_certMapped_length | ✅ | APPROVED | ✅ | `certMapped_length` |
| bridge2_certMapped_bool | ✅ | APPROVED | ✅ | `certMapped_bool` + `boolSyms` def |
| bridge2_h_init_connection | ✅ | APPROVED | ✅ | `cfgAt_zero` + `initList_h_init_shape` |
| bridge3 halting_time_bound | ✅ | APPROVED | ✅ | `stmtTouchDepth`/`NormalForm` defs (Bridge3.lean) |
| bridge3 stack_depth_bound (induction) | ✅ | APPROVED | ✅ | `stack_depth_bound` (Lemma C), 0 sorries |
| bridge3 h_adequate (maxStackDepth := n+T) | ✅ | APPROVED | ✅ | `h_adequate_of_normal_form` (Lemma D) |
| bridge3 bounded_read_depth_from_NormalForm | ✅ | APPROVED | ✅ | `bounded_read_depth_of_normal_form` (Lemma E) |
| bridge3 normal_form_normalization (GAP) | ✅ (None) | APPROVED (gap) | ⛔ sorry | `normal_form_normalization` (Lemma F) — one `sorry`, future sub-lemma |
| bridge4_f_polytime | ✅ | APPROVED (gaps) | ⏳ | researcher pinned down `f` + axiom stmt; reviewer verified halts-vs-accepts gap REAL; scaffold next |
| bridge5_L_iff_satisfiable | ✅ (strategy) | GAP (1 BREAK fixed) | ⏳ | forward+backward strategy attributed; depends on D1-D3 + Lemma F + boolSyms inverse |
| theorem SAT_is_NP_hard_real | ✅ (call graph) | GAP | ⏳ | full assembly call graph; transitively depends on Lemma F + D1-D3 |

## Activity Log
- 2026-07-04 orchestrator: verified build green; read handoff + assembly-blocker + workflow docs;
  created Pi project agents `cl-researcher`/`cl-reviewer`/`cl-coder`; created problem dir.
- 2026-07-04 orchestrator: dispatched `cl-researcher` for Bridge 1 (verifier-semantics).
- 2026-07-04 researcher: wrote `exploration/cook-levin/bridge1_verifier_semantics.py` (invariant + forward lemma, adversarial tests).
- 2026-07-04 reviewer (round 1): BREAK on non-determinism (return-type dishonesty) + GAPs (IH not parameter, false-None gate, unlisted iter-unfolding).
- 2026-07-04 researcher (round 2): fixed via `DeterministicStep` wrapper, IH-as-parameter, `lemma_iter_succ`, removed false-None gate.
- 2026-07-04 reviewer (round 2): all 6 units APPROVED; residual framing GAP (non-blocking).
- 2026-07-04 orchestrator: dispatched `cl-coder` to formalize Bridge 1 in Lean (sorry-free target).
- 2026-07-04 coder: formalized Bridge 1 in `Bridge1.lean` (`kleene_some_implies_stepOrHalt_eq`, `cfgAt_reaches_halt`), 0 axioms, 0 sorries, builds green.
- 2026-07-04 orchestrator: independently verified builds green + axiom/sorry inventory unchanged; committing Bridge 1.
- 2026-07-04 researcher (B2): wrote `bridge2_input_decomposition.py` (decomp + length + bool + h_init, no gaps).
- 2026-07-04 reviewer B2 (r1): no BREAK; GAPs (assert-not-prove, latent initList_shape arg bug, misleading Lemma-3 docstring).
- 2026-07-04 researcher (B2 r2): fixed latent bug (concrete arg), docstring scope, threaded sub-lemma deps with propagation.
- 2026-07-04 reviewer B2 (r2): all 4 units APPROVED.
- 2026-07-04 coder: formalized Bridge 2 in `Bridge2.lean` (5 lemmas A-E), 0 axioms, 0 sorries, builds green.
- 2026-07-04 orchestrator: verified builds green + inventory unchanged; committing Bridge 2. (Noted residual: `V.kDecidableEq` vs context `[DecidableEq V.K]` instance agreement - Bridge 5 concern.)
- 2026-07-04 researcher (B3): wrote `bridge3_adequacy_depth.py` (10 adversarial tests PASS; reviewer approved all 7 units). Key insight: `BoundedReadDepth`/per-step growth are STRUCTURAL (`NormalForm`), not from polytime bound.
- 2026-07-04 coder attempts for Bridge 3 Lean failed (budget/interrupted); orchestrator wrote `Bridge3.lean` directly (Python proof already vetted; `lake build` is independent verifier).
- 2026-07-04 orchestrator: `Bridge3.lean` builds green — ZERO axioms, exactly ONE sorry (`normal_form_normalization` Lemma F scaffold). Lemmas A–E sorry-free: `stmtTouchDepth`/`NormalForm` defs, `stepAux_stkLength_bound` (A, Stmt induction with dependent `Function.update_self`/`update_of_ne`), `step_length_change_bounded` (B), `stack_depth_bound` (C), `h_adequate_of_normal_form` (D), `bounded_read_depth_of_normal_form` (E). Key Lean hurdles: `FinTM2.step` unfold via `Turing.TM2.step.eq_2` with explicit `V.decidableEqK` instance (Bridge-2 residual); dependent `update` needs `update_self`/`update_of_ne` (not non-dependent `update_apply`); `subst` direction on case-binder vs theorem-param nondeterministic — used `by_cases h : k = k'` + `subst k'` to force survivor. Committing Bridge 3.- 2026-07-04 researcher (B4/5): wrote `bridge4_5_assembly.py` (11/11 tests). Pinned down real `f = tableauFormulaCert (paramsFor a) (aInput a) (certBound a) boolSyms` + Bridge 4 citation axiom stmt + Bridge 5 iff strategy + final assembly call graph.
- 2026-07-04 reviewer (B4/5): VERIFIED central diagnosis against actual Lean — `acceptanceConstraints` (Tableau.lean:179) encodes HALTING not output=true; `g` is TOTAL via `outputsFun` (halts on ALL inputs incl. g=false); so decider transformation V→V' REQUIRED. Confirmed D3 k₁-push touch-depth-2 subtlety, type-mismatch trap (input alphabet Sum eb.Γ Bool), Lemma F transitive dep, Bridge-2 residual. 1 BREAK: vacuous `or True` test — FIXED. Bridge 4 fix can proceed independently.
- 2026-07-04 orchestrator: next = scaffold full remaining assembly (Bridge 4 axiom + D1-D3 + Bridge 5 + SAT_is_NP_hard_real) as precisely-typed sorry-lemmas, green build, per handoff concrete-scaffold guidance.
- 2026-07-04 orchestrator: wrote `Assembly.lean` scaffold — D1+D2 (`decider_exists`), D3 (`decider_normal_form`), Bridge 5 (`bridge5_iff`), `SAT_is_NP_hard_real` as precisely-typed sorry'd theorems. Build green. Exactly 4 sorries (all non-crux: conclusions are DeciderSpec/NormalForm/iff, NOT the NPHard theorem). `DeciderSpec` structure defined (V', hGamma', timeBound', halts_iff). Crux axiom `SAT_is_NP_hard_citation` KEPT until all 4 sorries close + `SAT_is_NP_hard_real` fully proved. Added Assembly import to CookLevin.lean aggregator.
- 2026-07-04 orchestrator: wrote `Decider.lean` — CONCRETE decider `FinTM2` construction (D1) + **D3 SORRY-FREE**.
  - `CheckLoop` (2 labels: check/loop), `liftStmt` (lifts V's Stmt to decider state `σ × σ'`, redirects halt→goto check), `checkStmt` (peek k₁, branch true→halt/false→loop), `loopStmt` (goto loop trap), `decider V outEquiv : FinTM2` (concrete machine: Λ=V.Λ⊕CheckLoop, σ=V.σ×Option(V.Γ V.k₁), m=liftStmt on V labels + check/loop).
  - `liftStmt_touchDepth` (SORRY-FREE): stmtTouchDepth preserved by liftStmt (clean Stmt induction).
  - `decider_normal_form` (D3, SORRY-FREE): NormalForm V → NormalForm (decider V outEquiv). KEY SIMPLIFICATION: NormalForm is per-STATEMENT, liftStmt redirects halt→check (separate label), so V-portion touches stay within V'.m(inl l) (preserved by liftStmt_touchDepth), check peeks k₁ once (≤1), loop touches nothing. NO chain-splitting needed (the spec's worry was unfounded).
  - `decider_halts_iff` (D2, SORRY): the hard simulation lemma (cfgAt V' = cfgAt V on V-portion + output-head convention). This is the sole remaining decider sorry.
  - `encodedPairTape`, `DeciderSpec` moved here from Assembly.lean.
  - Assembly.lean trimmed: decider_exists (sorry, assembles decider+decider_halts_iff into DeciderSpec), bridge5_iff (sorry), SAT_is_NP_hard_real (sorry). Assembly's redundant decider_normal_form removed (concrete sorry-free one is in Decider.lean).
  - Debugging note: botlib uses `⊕` for Sum (not `⊎`); `⊎` is unparseable → "expected token" cascade. `FinTM2` does not bundle Fintype (Γ k₁) — added `[Fintype (V.Γ V.k₁)]` param to decider. Instance fields via `by have := V.ΛFin; exact inferInstance`.
  - Build green. Sorry inventory: Decider.lean=1 (D2), Assembly.lean=3 (decider_exists/bridge5_iff/SAT_is_NP_hard_real), Bridge3.lean=1 (Lemma F), +2 pre-existing.

## Reviewer meta-review (d952fb30) — verdicts
- Gap diagnosis CORRECT (verified vs actual Lean: acceptanceConstraints=HALTING, g total via outputsFun ∀a, backward breaks, forward OK).
- Decider strategy CORRECT in principle.
- D3 (decider_normal_form) valid & sorry-free but PROCRASTINATION: trivially easy (12 lines), offloads all difficulty to NormalForm V (the hard unresolved Lemma F). Orchestrator chose easiest piece.
- **BREAK (fixed this commit)**: decider_halts_iff/decider_exists took arbitrary V/outEquiv + Nonempty hComp with NO connection between V and g's machine. V could compute a different function → iff fails. FIXED: both now take comp : TM2ComputableInPolyTime ... g and use comp.tm/comp.outputAlphabet/comp.inputAlphabet/comp.time directly.
- D2 simulation lemma FEASIBLE (~50-100 lines, clean Stmt structural induction); spec OVERSTATED difficulty. The actual blocker.
- Lemma F (normal_form_normalization) HARD, independent, untouched.
- Verdict: orchestrator was polishing easy lemmas + docs while D2/Lemma F/BREAK untouched. FIX applied (BREAK). Next: PROVE D2 (the real blocker), then Lemma F.

### This commit: BREAK fix
- decider_halts_iff (Decider.lean): rewired to comp : TM2ComputableInPolyTime (pairEncoding eb finEncodingBoolList) finEncodingBoolBool g; uses comp.tm, comp.outputAlphabet, comp.inputAlphabet, comp.time. Time bound = comp.time.eval (encode (a,cert)).length + 2 (V's time + check phase).
- decider_exists (Assembly.lean): rewired to comp + hNF : NormalForm comp.tm. Produces Nonempty (DeciderSpec eb g) from the concrete decider comp.tm comp.outputAlphabet.
- Build green. Sorry inventory unchanged (D2 + assembly sorries still sorry; BREAK was a statement-correctness fix, not a proof).

## D2 progress (commits a6b1f66, 049cfb3, bedd1b0) — simulation core DONE sorry-free
Reviewer meta-review (d952fb30) prompted pivoting from easy polish to the hard core (D2). Delivered:
- **BREAK fix (bedd1b0)**: decider_halts_iff/decider_exists were UNPROVABLE (arbitrary V/outEquiv + Nonempty hComp disconnected V from g's machine — V could compute a different function). Rewired both to the full witness comp : TM2ComputableInPolyTime ... g (comp.tm/comp.outputAlphabet/comp.inputAlphabet/comp.time).
- **stepAux_liftStmt (a6b1f66, SORRY-FREE)**: the structural-induction heart of D2. stepAux (liftStmt s) (v,h) S = match stepAux s v S with | ⟨some l,v',S'⟩ => ⟨some (inl l),(v',h),S'⟩ | ⟨none,v',S'⟩ => ⟨some (inr check),(v',h),S'⟩. Clean 7-case Stmt induction.
- **cfgAt_decider_while_running (049cfb3, SORRY-FREE)**: the cfgAt-level lifting. While V runs at step t, V' at t = ⟨(cfgAt V input t).l.map Sum.inl, ((cfgAt V input t).var, none), (cfgAt V input t).stk⟩. Induction on t via cfgAt_succ + stepOrHalt_running + stepAux_liftStmt; "once halted stays halted" (cfgAt_halted_succ contrapositive) supplies predecessor-running.
- Helpers: decider_m_inl ((decider V outEquiv).m (inl lbl) = liftStmt (V.m lbl); needed because decider isn't reducible), CheckLoop deriving Encodable, 12 haveI instance shims for the decider's projection fields, stepOrHalt_running made non-private (visibility-only).

### D2 remaining (still sorry: decider_halts_iff)
The halting-step + output-head + iff-assembly:
1. Halting-step: V halts at T (running at T-1) => V' at T = ⟨some (inr check),(v',none),S'⟩ (stepAux_liftStmt none-branch); V' at T+1 = checkStmt (peek k1 -> branch); V' at T+2 = halt iff head maps true.
2. Output-head: comp.outputsFun (a,cert) : TM2OutputsInTime => EvalsToInTime reaches haltList with stk k1 = [outputAlphabet.invFun (g(a,cert))]; head = invFun (g(a,cert)); outEquiv = comp.outputAlphabet so outEquiv head = g(a,cert). Needs Bridge 1 (EvalsToInTime <-> cfgAt halting).
3. iff both directions: forward V' halts => via check (V-portion redirects halt->check, loop never halts) => branch true => g=true; backward g=true => V halts at T<=time with output [invFun true] => V' halts at T+2 <= time+2.
Estimated ~60-100 lines, cross-module Bridge 1 + outputsFun plumbing. This is the hardest remaining sub-piece.

### Sorry inventory (CookLevin)
Bridge1=0, Bridge2=0, Bridge3=1 (Lemma F), Decider=1 (decider_halts_iff), Assembly=3 (decider_exists/bridge5_iff/SAT_is_NP_hard_real), +2 pre-existing. Crux axiom SAT_is_NP_hard_citation KEPT until SAT_is_NP_hard_real closes.
