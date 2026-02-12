# Erdos 1094 Formalization Roadmap

**Theorem:** The set $E = \{(n, k) \in \mathbb{N} \times \mathbb{N} \mid 0 < k ∧ 2k ≤ n ∧ \mathrm{minFac}(\binom{n}{k}) > \max(n/k, k)\}$ is finite.
The conjectured exceptions are all for $k < 29$ and $n \le 284$.

## Current State
- **Finite Cases**: Covered by `native_decide` for $k \in [29, 1000]$ and $n \in [2k, k^2]$.
- **Non-Finite Cases**: Currently using `axiom` declarations in `KGe29.lean`.
- **Complexity**: Compilation is extremely slow due to large computational ranges.

## Proof Roadmap (Phase 1: Closing Axioms)

### 1. Large n Smooth Case ($n \ge 2k^2$)
- [x] Draft NL proof for Type B using density argument (`proofs/erdos-1094/large-n-smooth-case.md`)
- [ ] Formalize Bertrand prime existence for relevant ranges
- [ ] Formalize structural argument: if $\lfloor n/k \rfloor$ is $k$-smooth, $\binom{n}{k}$ must have a prime factor $\le n/k$.

### 2. CRT Density ($k > 10000$ or $k > 700$)
- [x] Draft NL proof for Mertens-bound on large prime density (`proofs/erdos-1094/mertens-density-bound.md`)
- [ ] Research explicit thresholds for Stewart/Bugeaud bounds on joint digit sums
- [ ] Replace heuristic axioms with effective analytic bounds

### 3. Integration
- [ ] Close `erdos_1094` main theorem by combining finite and non-finite cases
- [ ] Optimize Lean proofs to avoid excessive `native_decide` heartbeats where possible

## Guidelines
- **Avoid Compilation**: Do not run `lake build` on the Erdos 1094 files unless specifically testing a small snippet.
- **Detailed NL**: Focus on step-by-step logic that maps to Lean tactics (induction, cases, omega, etc.).
