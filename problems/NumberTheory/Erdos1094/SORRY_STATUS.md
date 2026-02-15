# Sorry Status - Erdős 1094 Project

**Last updated:** 2026-02-15

## ⚠️ CRITICAL: GapPrime.lean is MATHEMATICALLY BROKEN

**DO NOT work on GapPrime.lean sorrys.** The `F_lt_one` theorem is FALSE.
The CRT counting bound (kM/Q + 1)·R has remainder R = ∏(q_i - k) which is
astronomical (≈10³⁰ for k=9, M=100). The density kM·R/Q < 1 is correct
but the integer count bound is always >> 1. The approach cannot prove count = 0.

`large_prime_divides_choose_iff` is valid and reusable. Everything else in
GapPrime.lean should be ignored.

## Open Problem: B3b (the last gap)

The `large_n_smooth_case` axiom is NOT proved. The B3b case (n = sq, s | k,
q prime > M, M k-smooth) remains open for general k.

**What we know:**
- Computationally verified for k ≤ 50 (CRT intersection empty in (k, k²])
- Density argument gives expected count < 1 but does NOT prove count = 0
- No known structural proof for all k > K₀

**What we need:** A proof that works for ALL k above some threshold,
independent of n. This is the hard part.

### KonyaginTheorem1.lean (10 sorry)
File builds: ✅ GREEN (type errors fixed)
Contains the Konyagin (1999) proof scaffold. Sorrys are real analysis
(derivative bounds, parameter optimization). These are CORRECT targets
but lower priority than finding a B3b proof.

## Medium Priority (Infrastructure)

### botlib/Complexity/Soundness.lean (2 sorry)
- Cook-Levin soundness theorem
- **Status**: PARKED per chief directive (Erdős 1094 priority)

### botlib/Complexity/SAT.lean (2 sorry)
- Pre-existing scaffolding (lines 137, 139)
- **Status**: PARKED

### botlib/Complexity/Encodings.lean (1 sorry)
- `listEncoding.decode_encode` (line 76)
- **Status**: PARKED

## Low Priority (Old Scaffolding)

These are in files with 1 sorry each, likely old scaffolding or technical details:

- `botlib/Combinatorics/ChernoffDigits.lean`
- `botlib/Combinatorics/DigitSpace.lean`
- `botlib/NumberTheory/HighDigitCarry.lean`
- `botlib/NumberTheory/LargePrimeDvdChoose.lean`
- `botlib/NumberTheory/FactorPump.lean`
- `botlib/NumberTheory/Kummer.lean`
- `botlib/NumberTheory/CarryInfra.lean`
- `botlib/NumberTheory/BinomialDivisibility.lean`
- `botlib/Complexity/CookLevin/Correctness.lean`

**Status**: Not currently blocking main results

## Summary

**Total active sorry**: ~29 across project
**Blocking Erdős 1094 completion**: 4 (all in GapPrime.lean)
**Critical issue**: `hM_pos` needs hypothesis strengthening or case split

**Recent progress**: 
- ✅ Closed `large_prime_divides_choose_iff` using Kummer criterion + digit/mod conversion

**Recommendation**: Continue with GapPrime.lean sorry 2-4, then address the `hM_pos` design issue.
