# Erdos 1094 Formalization Roadmap

**Theorem:** The set $E = \{(n, k) \in \mathbb{N} \times \mathbb{N} \mid 0 < k ∧ 2k ≤ n ∧ \mathrm{minFac}(\binom{n}{k}) > \max(n/k, k)\}$ is finite.

## Current Focus: The Asymptotic Crux (k → ∞)
All finite-case verification is sidelined as a black-box compute task.

## Proof Roadmap (The Limit)

### 1. Analytic Combined Density Proof
- [x] Research explicit effective constants for Stewart/Bugeaud digit sum theorems
- [x] Draft NL proof: **Combined Density via Disjoint Prime Ranges** (`proofs/erdos-1094/combined-density-proof.md`)
- [x] Unified strategy: $\delta(P_S \cup P_L) = \delta(P_S) \cdot \delta(P_L) < 1/k^2$ for $k > 1000$.

### 2. Implementation State
- [x] Digest NL proof into Lean skeleton (`Asymptotic.lean`)
- [x] Prove `moduli_coprime` in `Asymptotic.lean` (Algebraic bedrock)
- [ ] Prove `card_KummerValid` in `Asymptotic.lean` (Blueprint provided)
- [ ] Formalize CRT factorization for Kummer densities
- [ ] Resolve Case 1 threshold ($k \in [10001, 178416]$) via batch compute
