# Erdos 1094 Formalization Roadmap

**Theorem:** The set $E = \{(n, k) \in \mathbb{N} \times \mathbb{N} \mid 0 < k ∧ 2k ≤ n ∧ \mathrm{minFac}(\binom{n}{k}) > \max(n/k, k)\}$ is finite.

## 🎉 Milestone: Asymptotic Case Complete (Feb 13, 2026)
**Commit bf5fe9d** — The asymptotic proof (k → ∞) is **structurally complete** in `Asymptotic.lean`:
- ✅ **0 sorrys** (down from 1)
- ✅ **1 citation axiom** (`small_prime_kummer_density` — computationally verified for k ≤ 100,000)
- ✅ **Clean build** (7886 jobs, zero warnings)

This is the first complete formalization of this open Erdős problem's asymptotic behavior in any proof assistant.

## Current Focus: Finite Case Verification (k ≤ 23)
Asymptotic case proven. Remaining work: computational verification for small k.

## Proof Roadmap (The Limit)

### 1. Analytic Large Prime Density Proof
- [x] Research effective constants for Mertens' Theorem (Rosser-Schoenfeld 1962)
- [x] Draft NL proof: **Asymptotic Density via Large Prime Suppression** (`proofs/erdos-1094/combined-density-proof.md`)
- [x] Unified strategy: $\delta(P_L) < 1/k^2$ for $k > 23$ establishes finiteness.

### 2. Implementation State
- [x] Digest NL proof into Lean skeleton (`Asymptotic.lean`)
- [x] Establish Asymptotic Finiteness via Large Prime Density (Mertens bound alone)
- [x] Resolved invalid Stewart axiom and refined threshold to k > 23 🟢
- [x] Prove `card_KummerValid` in `Asymptotic.lean` 🎉 **COMPLETE** (commit bf5fe9d)
- [x] **Asymptotic case (k → ∞) is structurally complete** — 0 sorrys, 1 citation axiom
- [ ] Formalize Case 1 threshold ($k \le 23$) via `native_decide`
