# OpenLemma

A curated library of formally verified mathematical results produced by LLM agents, built on Lean 4 and Mathlib.

## What is this?

OpenLemma collects reusable lemmas and theorems that emerged from LLM agent experiments on open mathematical problems (primarily from the [Erdős Problems](https://erdosproblems.com/) database). Every result in `botlib/` compiles with **zero sorrys and zero axioms**.

The library is organized into two parts:

- **`botlib/`** — Compiler-verified lemmas (0 sorrys, 0 axioms). Safe to import as dependencies.
- **`problems/`** — Problem-specific results that may contain citation axioms for well-known theorems not yet in Mathlib (e.g., Zsygmondy's theorem).

## Library contents

### botlib/NumberTheory/

| File | Lines | Description | Source |
|------|-------|-------------|--------|
| `Kummer.lean` | ~100 | Kummer's digit-domination criterion: `p ∣ C(n,k) ↔ ∃ i, digit_i(k) > digit_i(n)` | Erdős 1094 |
| `LargePrimeDvdChoose.lean` | ~60 | For prime `p > k`: `p ∣ C(n,k) ↔ n % p < k` | Erdős 1094 |
| `CarryInfra.lean` | ~120 | Decidable `hasCarry` check + soundness for small prime divisibility of C(n,k) | Erdős 1094 |
| `BinomialDivisibility.lean` | ~120 | Reduction lemma (factorial↔binomial) + carry dominance (`v_p(C(m+k,k)) ≤ v_p(C(2m,m))` for `p > 2k`) | Erdős 728 |
| `FactorPump.lean` | ~230 | `v₂(σ₁(n)) ≥ ω_odd(oddPart(n))` — 2-adic valuation of sum-of-divisors | Erdős 410 |

### problems/NumberTheory/

| File | Lines | Axioms | Description | Source |
|------|-------|--------|-------------|--------|
| `SmoothEscape.lean` | ~280 | 1 (Zsygmondy) | σ₁-orbit of n ≥ 2 is not eventually S-smooth for any finite prime set S | Erdős 410 |

## Provenance

All results were produced by LLM agents (Claude by Anthropic, Gemini by Google) with **zero human mathematical input**. The human role was limited to:

1. Selecting problems and writing Lean theorem statements
2. Building the agent infrastructure (task management, workflow design)
3. Reviewing and curating the outputs

See the [friction report](https://gist.github.com/jarredbarber/c541d6d7f35582d97fffc227b2dde692) for analysis of agent failure modes when working with Lean/Mathlib.

## Can AI create math?

This is the question we're interested in. Not "can AI solve problems" (tree search) but "can AI produce reusable abstractions?" The test is empirical: if these lemmas get used by others (human or AI), that's evidence.

The Factor Pump and Smooth Escape Lemma are the most interesting cases — they emerged when agents couldn't solve the target problem and explored laterally instead.

## Building

```bash
# Requires Lean 4.27.0 + Mathlib 4.27.0
lake build
```

## Related work

- [Erdős Problems](https://erdosproblems.com/) — Thomas Bloom's database
- [DeepMind formal-conjectures](https://github.com/google-deepmind/formal-conjectures) — Formalized Erdős problem statements
- [Aletheia paper](https://arxiv.org/abs/2601.22401) — DeepMind's semi-autonomous Erdős effort
- [Tao's AI wiki](https://terrytao.wordpress.com/) — Tracking AI contributions to Erdős problems

## License

Apache 2.0
