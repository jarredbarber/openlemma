# Erdős Problem 1094

For all n ≥ 2k, the least prime factor of C(n,k) is at most max(n/k, k), with only finitely many exceptions.

```lean
theorem erdos_1094 :
    {(n, k) : ℕ × ℕ | 0 < k ∧ 2 * k ≤ n ∧ (n.choose k).minFac > max (n / k) k}.Finite
```

**THIS THEOREM STATEMENT IS IMMUTABLE.**

## Current State

Partially formalized in `erdos-1094` repo. 1 sorry + 4 axioms remaining.

### Axiom Classification
- `crt_density_large_k` (k > 10000): **CRUX** — claims CRT density covers all cases
- `crt_density_case2_large_k` (k > 700): **CRUX** — similar for case 2
- `large_n_smooth_case` (n > k²): **BORDERLINE** — extra hypotheses narrow scope
- `residual_small_prime_coverage` (k ≤ 28): **COMPUTATIONAL** — should be provable via native_decide

### Sorry
- `CrtCheck.lean:59`: Computational bridge — soundness of exhaustive check

### What's needed
1. Prove or eliminate the 2 crux axioms (the hard math)
2. Close the computational sorry and bridge axiom
3. Possible alternative: find a completely different proof strategy that avoids CRT density

### Available infrastructure (already in OpenLemma botlib)
- `Kummer.lean` — Kummer's theorem formalization
- `CarryInfra.lean` — carry counting infrastructure
- `LargePrimeDvdChoose.lean` — large prime divisibility criterion

### NL proofs available
See `proofs/erdos-1094/` directory.

## Prize
$500 (erdosproblems.com)
