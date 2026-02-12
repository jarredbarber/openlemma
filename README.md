# OpenLemma

A curated library of formally verified mathematical results produced by LLM agents, built on Lean 4 and Mathlib.

## What is this?

OpenLemma collects reusable lemmas and theorems that emerged from LLM agent experiments on open mathematical problems (primarily from the [Erdős Problems](https://erdosproblems.com/) database). Every result in `botlib/` compiles with **zero sorrys and zero axioms**.

The library is organized into two parts:

- **`botlib/`** — Compiler-verified lemmas (0 sorrys, 0 axioms). Safe to import as dependencies.
- **`problems/`** — Problem-specific results that may contain citation axioms for well-known theorems not yet in Mathlib (e.g., Zsygmondy's theorem).

## Current Project: Cook-Levin Theorem

The current focus of the library is a full formalization of the **Cook-Levin Theorem** (SAT is NP-complete) in Lean 4. 

**Progress:**
- [x] **Phase 1: Foundations**: P/NP definitions, poly-time composition, and axiom-free foundations.
- [ ] **Phase 2: SAT ∈ NP**: Verifier definition and polynomial witness size proofs (In progress).
- [ ] **Phase 3: Cook-Levin Reduction**: Tableau construction for multi-stack Turing machines (Scaffolding).
- [x] **Phase 4: NP-Completeness Library**: Verified NL proofs for reductions (3-SAT, Clique, Vertex Cover, Dominating Set, Subset Sum, Partition, Knapsack, Bin Packing).

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
| `Defs.lean` | ~140 | P, NP, NP-complete definitions, poly-time reductions | 🟡 1 axiom |
| `Encodings.lean` | ~130 | Efficient linear-time encodings for lists, sums, and pairs | ✅ |
| `TM2PolyTimeComp.lean` | ~1430 | Closure of polynomial-time functions under composition | ✅ |
| `PolyTimeFst.lean` | ~320 | Proof that first projection of a pair is poly-time | ✅ |
| `SAT.lean` | ~370 | CNF SAT/3-SAT definitions, SAT ∈ NP (verifier + cert bounds) | 🟡 WIP |
| `CookLevin.lean` | ~120 | Tableau-based reduction from NP languages to SAT | 🔴 Scaffolding |

### problems/NumberTheory/

| File | Lines | Axioms | Description | Source |
|------|-------|--------|-------------|--------|
| `SmoothEscape.lean` | ~280 | 1 (Zsygmondy) | σ₁-orbit of n ≥ 2 is not eventually S-smooth for any finite prime set S | Erdős 410 |

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

The Cook-Levin effort builds on Mathlib's `TM2` multi-stack Turing Machine model. Significant technical challenges addressed include:
- Establishing the closure of polynomial-time functions under composition (ported from `LeanMillenniumPrizeProblems`).
- Designing linear-time separator-based encodings for lists to ensure polynomial witness sizes (avoiding the exponential overhead of standard Cantor pairing).
- Formalizing a "forbidden windows" transition consistency check for the multi-stack tableau.

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
