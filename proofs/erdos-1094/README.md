# Erdős 1094 Proof Library

**Theorem:** The set of exceptions to Erdős 1094 is finite.

## Core Documentation
- **`tower-summary.md`**: **READ THIS FIRST.** The definitive summary of what is proved, formalized, and computed.
- **`main-theorem.md`**: The top-level finiteness argument (reduction to bounded sets).

## Proof Components

### 1. The Finite Range ($n \le k^2$)
- **`no-exceptions-k-ge-29.md`**: Proof that $k$ is bounded by 28.
- **`bound-n-for-small-k.md`**: Proof that $n$ is bounded for small $k$.
- **`crt-density-k-ge-29.md`**: Density argument supporting the $k \ge 29$ bound.

### 2. The Infinite Range ($n > k^2$)
- **`large-n-divisibility.md`**: **Type A** proof (Interval Divisibility Lemma).
- **`large-n-smooth-case.md`**: **Type B** analysis (Smooth Case).
- **`strategy-5-results.md`**: **Strategy 5** (Large Prime Gap) results proving the smooth case is empty for $k \ge 36$.
- **`b3b-resolution.md`**: Specific resolution of the $n=sq$ gap.

## Supporting Investigations
- **`smooth-kummer-trace.md`**: Explicit arithmetic traces for $C(50, 5)$ etc.
- **`large-k-smooth-bound.md`**: Analytic probability bound ($O(1/k!)$).
- **`combinatorial-gap-analysis.md`**: Early analysis of CRT gaps.
- **`konyagin-proof.md`**: Deep dive into Konyagin's method and why elementary methods fail the density gap.

## Literature
- **`literature-survey.md`**: Verification of Konyagin's references.
- **`els93-context.md`**: Context from the original Erdős-Lacampagne-Selfridge paper.
