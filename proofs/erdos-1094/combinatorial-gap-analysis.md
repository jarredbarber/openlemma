# Combinatorial Gap Analysis for Erdős 1094

**Status:** Complete investigation ✅  
**Date:** 2026-02-12  
**Depends on:** konyagin-proof.md, filaseta-trifonov-large-n.md

## Summary

Direct combinatorial enumeration of "bad" CRT classes (n satisfying Kummer
constraints for all primes in (k/2, k)) reveals:

1. **The gap structure is exactly the density** — avg CRT gap = N/δN.
2. **Progressive elimination** reduces survivors rapidly (786 → 42 → 1 → 0 for k=200).
3. **Two-layer sieve** (big primes + small primes) catches ALL exceptions for k ∈ [29, 500].
4. **The density-to-deterministic gap persists** in both layers.

## §1. Direct CRT Enumeration

For k=200 with 4 primes p = (101, 103, 107, 109), c = (2, 6, 14, 18):

- M' = Πp = 121,330,189
- Bad CRT classes: Πc = 3,024
- Average gap between consecutive bad reps: M'/Πc = 40,122 ≈ k²

**Key computation:** ALL 3,024 bad CRT representatives can be enumerated.
Of these, exactly 2 fall below the interval [400, 40000]:

| Representative | Residues (mod 101, 103, 107, 109) |
|----------------|-----------------------------------|
| n = 0 | (0, 0, 0, 0) |
| n = 1 | (1, 1, 1, 1) |

The next bad representative is at n = 46,662 > k² = 40,000.
The interval [400, 40000] falls entirely within the gap [2, 46661].

## §2. Progressive Elimination

For k=200, adding primes one at a time:

| Primes used | Survivors in [400, 40000] | Notes |
|-------------|--------------------------|-------|
| p₁ = 101 (c=2) | 786 | n ≡ 0 or 1 mod 101 |
| +p₂ = 103 (c=6) | 42 | CRT sieve |
| +p₃ = 107 (c=14) | **1** | Only n=5253 survives |
| +p₄ = 109 (c=18) | **0** | 5253 mod 109 = 21 ≥ 18: killed |

The sole 3-prime survivor n=5253 has residues (1, 0, 10) and is killed
by the 4th prime with **margin of only 3** (residue 21 vs threshold 18).

### 2-prime class structure

In one period [0, 10403) of p₁p₂:

```
Classes: [0, 1, 4949, 5050, 5051, 5151, 5152, 5253, 10201, 10202, 10302, 10303]
Gaps:    [1, 4948, 101, 1, 100, 1, 101, 4948, 1, 100, 1]
```

Three clusters: {0,1}, {4949–5253}, {10201–10303}. The 3rd prime eliminates
8/10 non-trivial classes; only n=5253 survives.

## §3. Gap = Density (Exact Equivalence)

**Theorem (informal):** avg_gap = M'/Πc = N/δN.

- When δN < 1: average gap > k², so the interval likely falls in one gap.
- When δN > 1: average gap < k², so the interval likely contains bad reps.

This is verified for all k ∈ [29, 500]:

| k | Min δN (r≤6) | δN < 1? | Bad count | Caught by small primes? |
|---|-------------|---------|-----------|------------------------|
| 50 | 101.73 | ✗ | 99 | All 99 ✅ |
| 100 | 11.45 | ✗ | 3 | All 3 ✅ |
| 150 | 2.52 | ✗ | 1 | 1 ✅ |
| 200 | 0.097 | ✓ | 0 | — |
| 300 | 0.295 | ✓ | 0 | — |
| 500 | 0.046 | ✓ | 0 | — |

For k < 200: the big-prime sieve fails (δN > 1), but small primes catch all failures.

## §4. Two-Layer Sieve

**Layer 1 (big primes):** For each prime p ∈ (k/2, k), the Kummer criterion
gives: p | C(n,k) iff n mod p ≥ 2p−k. The Kummer sieve eliminates n values
that have "large" residues modulo big primes.

**Layer 2 (small primes):** For each prime p ≤ k/2, the Kummer criterion
gives: p | C(n,k) iff there's a carry in adding k and n−k in base p.

**Computational result:** For ALL k ∈ [29, 500], every n ∈ [2k, k²] is
caught by at least one prime p ≤ k. That is, for every such n, some
prime p ≤ k divides C(n,k).

### Which small primes do the work?

| Prime p | Fraction of Kummer failures caught | Mechanism |
|---------|-----------------------------------|-----------|
| p = 2 | 80–95% | C(n,k) even for most n |
| p = 3 | 3–15% | Ternary carries |
| p = 5 | 1–3% | Quinary carries |
| p ≥ 7 | < 1% | Rarely needed |

**Density explanation:** The fraction of n where C(n,k) is NOT divisible by p is
$$\prod_{i=0}^{L_p-1} \frac{p - d_i}{p}$$
where $d_0, \ldots, d_{L_p-1}$ are the base-$p$ digits of $k$.

For k=100: after primes 2, 3, 5, 7, 11, 13, the expected number of n ∈ [200, 10000]
with C(n,k) coprime to all six is **0.43 < 1**.

## §5. Why The Proof Gap Persists

Despite the computational success, **neither layer** provides a rigorous proof
that count = 0:

### Layer 1 (big primes):
- CS bound: √(Πc × N) ≈ 10⁴ (gap to actual ≈ 1)
- The gap = M'/√(ΠcN) grows exponentially with r
- Requires Bombieri–Pila to bridge (see konyagin-proof.md §8)

### Layer 2 (small primes):
- Period: Π p^{L_p} ≫ k² (e.g., for primes ≤ 13 and k=100: period ≈ 2.7 × 10¹³)
- Interval [2k, k²] covers < 0.00004% of one period
- Short-interval density-to-deterministic gap applies equally

### Combined:
The two layers provide **redundant coverage** — most n are caught by both.
But the proof that the intersection of "uncaught" sets is empty requires
precisely the structural argument (BP or equivalent) that we cannot supply
by elementary methods.

## §6. Structural Observations

### 6.1 Trivial cluster
n = 0, 1, ..., c_min − 1 always satisfy all Kummer constraints
(since each c_i ≥ c_min ≥ 2). These form the "trivial bad cluster" near 0.
The interval [2k, k²] starts well above this cluster (at n = 2k ≥ 58).

### 6.2 Post-trivial gap
After n = c_min − 1, the next bad representative is determined by CRT
interactions between all primes. For k=200: gap = 46,661 > k² = 40,000.

The gap size depends on the **specific arithmetic** of the primes (not just
their density). The margin can be as small as 3 (n=5253 for k=200).

### 6.3 The gap IS the density
We have the exact relationship: avg_gap = 1/δ = Πp/Πc.
The interval length is k² − 2k ≈ k². So gap > k² iff δ < 1/k², i.e., δN < 1.
No additional algebraic structure was found beyond this CRT density.

### 6.4 Kummer failures cluster near 0
For k=100: the 3 Kummer failures are n = 2014, 2015, 2016 — consecutive!
These satisfy n mod p < 2p−k for all 10 primes in (50, 100), meaning
n has "small residues" modulo all big primes. By CRT, such n must be
close to 0 modulo M' = Π p ≈ 6 × 10¹⁷. Since n < 10⁴ ≪ M', this
means n is in the CRT "neighborhood of 0."

### 6.5 Small primes catch CRT-small n
Values near 0 (mod M') tend to have simple factorizations (small absolute
value or small prime factors). The carry structure in base 2 is particularly
favorable: C(n, k) is even for ~87.5% of n when k has 3 one-bits.

## §7. Conclusion

The combinatorial approach provides:
- **Visualization**: the problem is about a line in a torus missing a product set
- **Confirmation**: gap structure exactly mirrors CRT density
- **New angle**: two-layer sieve catches everything computationally
- **No shortcut**: the density-to-deterministic gap persists in all formulations

The combinatorial analysis does NOT bypass the need for Bombieri–Pila
(or equivalent) for a rigorous proof. It provides the same information
as the exponential sum approach, viewed from a dual perspective.

**For formalization:** The computational verification (k ≤ 500) could be
certified as a `Decidable` computation in Lean. For k > 500, a citation
axiom for Konyagin's theorem remains necessary.
