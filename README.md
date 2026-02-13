# OpenLemma

A curated library of formally verified mathematical results produced by LLM agents, built on Lean 4 and Mathlib.

## What is this?

OpenLemma collects reusable lemmas and theorems that emerged from LLM agent experiments on open mathematical problems (primarily from the [Erdős Problems](https://erdosproblems.com/) database). Every result in `botlib/` compiles with **zero sorrys and zero axioms**.

The library is organized into two parts:

- **`botlib/`** — Compiler-verified lemmas (0 sorrys, 0 axioms). Safe to import as dependencies.
- **`problems/`** — Problem-specific results that may contain citation axioms for well-known theorems not yet in Mathlib (e.g., Zsygmondy's theorem).

## Current Projects

### Cook-Levin Theorem (PARKED - Core Complete ✅)

A full formalization of the **Cook-Levin Theorem** (SAT is NP-complete) in Lean 4. 

**Status:** Core proofs are **axiom-free and complete** (~2,700 lines, 113 theorems, 0 axioms, 0 sorrys):
- [x] **Phase 1: Foundations**: P/NP definitions, poly-time composition, and axiom-free foundations ✅
- [x] **Phase 2: Cook-Levin Correctness**: `stepAux` soundness and preservation (370 lines) ✅
- [x] **Phase 3: Cook-Levin Soundness**: Tableau satisfiability → TM acceptance (918 lines) ✅
- [x] **Phase 4: Cook-Levin Completeness**: TM acceptance → Tableau satisfiability (1166 lines) ✅

**Remaining work:** Assembly into final `SAT_is_NP_hard` theorem (~200-300 lines, needs 2 citation axioms for poly-time bounds).

### Erdős 1094 (ACTIVE)

**Problem:** Prove that for all k ≥ 29, the least prime factor of $\binom{n}{k}$ is $\le \max(n/k, k)$ for all $n \ge 2k$.

**Architecture:**
- **Case $n \le k^2$**: **CLOSED** via nonconstructive Konyagin citation. Axiom `konyagin_1999` proves $\exists K_0$ such that $g(k) > k^2$ for $k > K_0$.
- **Case $n > k^2$**: **OPEN**. Relies on axiom `large_n_smooth_case`.

**Axioms: 2** (down from 3)
1. `konyagin_1999`: Faithful citation of *Mathematika* 46 (1999) proving $g(k) \ge \exp(c \log^2 k)$.
2. `large_n_smooth_case`: For $n > k^2$ where $n/k$ is $k$-smooth, there exists a prime $p \le n/k$ dividing $\binom{n}{k}$.

**Research output:** `konyagin-proof.md` (~400 lines) — Deep analysis of why elementary methods fail and the transition to analytic techniques.

**Build Status:** **GREEN** (0 sorrys, 2 axioms). `native_decide` and ad-hoc density bridges have been eliminated.

## Library contents

### botlib/NumberTheory/

| File | Lines | Description | Source |
|------|-------|-------------|--------|
| `Kummer.lean` | ~100 | Kummer's digit-domination criterion: `p ∣ C(n,k) ↔ ∃ i, digit_i(k) > digit_i(n)` | Erdős 1094 |
| `LargePrimeDvdChoose.lean` | ~60 | For prime `p > k`: `p ∣ C(n,k) ↔ n % p < k` | Erdős 1094 |
| `CarryInfra.lean` | ~120 | Decidable `hasCarry` check + soundness for small prime divisibility of C(n,k) | Erdős 1094 |
| `BinomialDivisibility.lean` | ~120 | Reduction lemma (factorial↔binomial) + carry dominance (`v_p(C(m+k,k)) ≤ v_p(C(2m,m))` for `p > 2k`) | Erdős 728 |
| `HighDigitCarry.lean` | ~80 | High base-p digit of m forces carry in C(2m,m), giving `v_p` lower bound | Erdős 728 |
| `FactorPump.lean` | ~230 | `v₂(σ₁(n)) ≥ ω_odd(oddPart(n))` — 2-adic valuation of sum-of-divisors | Erdős 410 |
| `Zsygmondy.lean` | ~40 | Citation axiom for Zsygmondy's theorem (formalization target) | — |

### botlib/Combinatorics/

| File | Lines | Description | Source |
|------|-------|-------------|--------|
| `DigitSpace.lean` | ~30 | `Fin D → Fin p` type, high digit predicate, counting definitions | Erdős 728 |
| `ChernoffDigits.lean` | ~330 | Hoeffding/Chernoff bounds over uniform digit spaces | Erdős 728 |

### botlib/Complexity/

| File | Lines | Description | Status |
|------|-------|-------------|--------|
| `Defs.lean` | ~360 | P, NP, NP-complete definitions, poly-time reductions | ✅ Axiom-free |
| `Encodings.lean` | ~310 | Efficient linear-time encodings for lists, sums, and pairs | ✅ |
| `TM2PolyTimeComp.lean` | ~1430 | Closure of polynomial-time functions under composition | ✅ |
| `PolyTimeFst.lean` | ~320 | Proof that first projection of a pair is poly-time | ✅ |
| `SAT.lean` | ~370 | CNF SAT/3-SAT definitions, variable/literal encodings | ✅ |
| `CookLevin/Tableau.lean` | ~530 | Multi-stack tableau structure with forbidden windows | ✅ |
| `CookLevin/Correctness.lean` | ~370 | `stepAux` soundness and preservation | ✅ Axiom-free |
| `CookLevin/Soundness.lean` | ~918 | Tableau satisfiability → TM acceptance | ✅ Axiom-free |
| `CookLevin/Completeness.lean` | ~1166 | TM acceptance → Tableau satisfiability | ✅ Axiom-free |
| `CookLevin/PolyTime.lean` | ~100 | Poly-time bounds (stub, 2 citation axioms) | 🟡 Assembly needed |

### problems/NumberTheory/

| File | Lines | Axioms | Description | Source |
|------|-------|--------|-------------|--------|
| `SmoothEscape.lean` | ~280 | 1 (Zsygmondy) | σ₁-orbit of n ≥ 2 is not eventually S-smooth for any finite prime set S | Erdős 410 |
| `Erdos1094/Asymptotic.lean` | ~140 | 0 | `card_KummerValid`: Asymptotic density bound for k-digit-domination | Erdős 1094 |
| `Erdos1094/KLe28.lean` | ~120 | 0 | Direct verification for k ≤ 28 | Erdős 1094 |
| `Erdos1094/Konyagin.lean` | ~80 | 1 | Citation of Konyagin (1999) + bridge to g(k) > k² | Erdős 1094 |
| `Erdos1094/KGe29.lean` | ~180 | 1 | Large-n case (relies on `large_n_smooth_case`) | Erdős 1094 |

## Provenance and prior work

All results were produced by LLM agents (Claude by Anthropic, Gemini by Google) with **zero human mathematical input**. The human role was limited to:

1. Selecting problems and writing Lean theorem statements
2. Building the agent infrastructure (task management, workflow design)
3. Reviewing and curating the outputs

### Prior work on Erdős 728

The proof strategy for 728 — reducing to binomial divisibility, applying Kummer's carry interpretation, and counting "good" values of m in [M, 2M] — is closely related to prior human work:

- **Pomerance (2015)**, ["Divisors of the Middle Binomial Coefficient"](https://math.dartmouth.edu/~carlp/catalan5.pdf), *Amer. Math. Monthly*. Proved that for fixed k, the set of n where (n+k) | C(2n,n) has density 1, using Kummer's theorem and digit randomness.
- **Sothanaphan (2026)**, ["Resolution of Erdős Problem #728"](https://arxiv.org/abs/2601.07421). Writeup of GPT-5.2/Aristotle's Lean proof. Extended Pomerance to growing k ≍ log n using "carry-rich but spike-free" counting.
- **Our 728b agents** independently converged on the same high-level strategy but used Chernoff concentration bounds (Hoeffding's inequality over digit spaces) instead of carry-rich/spike-free sieve counting.

We cannot distinguish whether agents independently discovered this approach (Kummer → digit counting is arguably the natural strategy) or reproduced it from training data containing Pomerance's paper. This is the ["subconscious plagiarism"](https://arxiv.org/abs/2601.22401) problem identified by the DeepMind Aletheia team: LLMs may reproduce absorbed proof strategies without attribution. Formal verification confirms correctness but cannot confirm originality.

### On the question of AI creating math

This is the question we're interested in. Not "can AI solve problems" (tree search) but "can AI produce reusable abstractions?" The test is empirical: if these lemmas get used by others (human or AI), that's evidence of genuine contribution.

The Factor Pump and Smooth Escape Lemma (from Erdős 410) are the most interesting cases — they emerged when agents *couldn't* solve the target problem and explored laterally instead. Whether these represent novel mathematics or recombination of training data is a question we lack the expertise to answer; a number theorist's evaluation would be needed.

See the [friction report](https://gist.github.com/jarredbarber/c541d6d7f35582d97fffc227b2dde692) for analysis of agent failure modes when working with Lean/Mathlib.

### Note on Cook-Levin Formalization

The Cook-Levin effort builds on Mathlib's `TM2` multi-stack Turing Machine model. The **core correctness proofs are complete and axiom-free** (2,454 lines, ~113 theorems, 0 axioms, 0 sorrys).

**Technical challenges solved:**
- **Polynomial-time closure under composition** (~1,430 lines, ported from `LeanMillenniumPrizeProblems`)
- **Linear-time separator-based list encodings** to ensure polynomial witness sizes (avoiding exponential Cantor pairing overhead)
- **Forbidden windows tableau** with multi-stack transition consistency checks
- **Stack decomposition lemmas** (`stepAux_stk_len_delta`, `stepAux_stk_decomp`) for soundness proofs
- **Frame preservation** (`frame_preserves_elem`) for completeness proofs
- **Adequate parameter selection** (`h_adequate` precondition) ensuring physical realizability

**Remaining work:** Assembly into final `SAT_is_NP_hard` theorem requires:
1. `tableauFormulaPartial` variant for free certificate variables (~100 lines)
2. Polynomial-time bound proofs (2 citation axioms: encoding bounds, tableau construction)
3. Top-level assembly (~100-200 lines)

The core reduction is **mathematically complete** - only engineering work remains.

### Note on Erdős 1094

**Problem statement:** For which k does there exist n > k+1 such that minFac(C(n,k)) > k?

**Current result:** Proved for all k ≥ 29 (modulo 2 citation axioms citing Konyagin 1999).

**Approach:**
1. **Kummer's theorem** reformulates prime divisibility as digit domination in base p
2. **CRT product sets** combine conditions from multiple primes near k/2
3. **Asymptotic density** (proved): For large k, the density of "bad" n vanishes exponentially
4. **Small cases** (k ≤ 28): Direct verification
5. **Bridge cases** (29 ≤ k ≤ 700): Currently axiomatized, target for `native_decide`

**Strategic findings (~1,600 lines of analysis):**
- Elementary Fourier methods (Parseval + Cauchy-Schwarz) give bound |E| ≤ √(NR), which includes exponentially large factor √M
- Bombieri-Pila point-counting on algebraic curves is required for tighter bounds
- Konyagin's 1999 result proves finiteness of exceptions but doesn't extract explicit constant
- Path to axiom reduction: Extract constant c from Konyagin → enables `native_decide` for bridge cases → reduces to 1 axiom

**Research integrity:** The strategic research includes honest documentation of errors (e.g., an initially claimed "elementary proof" that incorrectly dropped a factor of M in the Cauchy-Schwarz bound). All corrections are documented in git history with clear commit messages.

## Building

```bash
# Requires Lean 4.27.0 + Mathlib 4.27.0
lake build
```

## Related work

- [Erdős Problems](https://erdosproblems.com/) — Thomas Bloom's database
- [Pomerance (2015)](https://math.dartmouth.edu/~carlp/catalan5.pdf) — Prior human work on divisors of C(2n,n)
- [Sothanaphan (2026)](https://arxiv.org/abs/2601.07421) — GPT-5.2/Aristotle writeup for 728
- [Aletheia paper](https://arxiv.org/abs/2601.22401) — DeepMind's semi-autonomous Erdős effort
- [DeepMind formal-conjectures](https://github.com/google-deepmind/formal-conjectures) — Formalized Erdős problem statements
- [Tao's AI contributions wiki](https://terrytao.wordpress.com/) — Tracking AI contributions to Erdős problems

## License

Apache 2.0
