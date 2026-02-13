# Erdos 1094 Formalization Roadmap

**Theorem:** The set $E = \{(n, k) \in \mathbb{N} \times \mathbb{N} \mid 0 < k ∧ 2k ≤ n ∧ \mathrm{minFac}(\binom{n}{k}) > \max(n/k, k)\}$ is finite.

## Current Focus: The Asymptotic Crux (k → ∞)
All finite-case verification is sidelined as a black-box compute task.

## Proof Roadmap (The Limit)

### 1. Analytic Large Prime Density Proof
- [x] Research effective constants for Mertens' Theorem (Rosser-Schoenfeld 1962)
- [x] Draft NL proof: **Asymptotic Density via Large Prime Suppression** (`proofs/erdos-1094/combined-density-proof.md`)
- [x] Unified strategy: $\delta(P_L) < 1/k^2$ for $k > 23$ establishes finiteness.

### 2. Implementation State
- [x] Digest NL proof into Lean skeleton (`Asymptotic.lean`)
- [x] Establish Asymptotic Finiteness via Large Prime Density (Mertens bound alone)
- [x] Resolved invalid Stewart axiom and refined threshold to k > 23 🟢
- [ ] Prove `card_KummerValid` in `Asymptotic.lean` (Blueprint provided)
- [ ] Formalize Case 1 threshold ($k \le 23$) via `native_decide`
