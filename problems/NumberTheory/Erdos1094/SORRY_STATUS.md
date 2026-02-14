# Sorry Status - Erdős 1094 Project

**Last updated:** 2026-02-13 (after 71 commits)

## High Priority (Blocking Main Results)

### GapPrime.lean (3 sorry) 
File builds: ✅ GREEN

1. **Line 78**: `large_prime_divides_choose_iff` — ✅ **CLOSED**
   - **What**: For prime q > k: q | C(n,k) ⟺ n mod q < k
   - **Proof**: Used `kummer_criterion` + `Nat.getD_digits` to convert digit form to div/mod form
   - **Key insight**: For k < q, only position i=0 matters; higher positions have k/q^i = 0

2. **Line 123**: `crt_bad_count`
   - **What**: CRT counting bound for bad residues
   - **Why hard**: Requires CRT bijection + interval counting
   - **Impact**: Core of gap prime counting argument

3. **Line 141**: `mertens_product_bound`
   - **What**: ∏(1 - k/q) ≤ (C ln k / ln M)^k
   - **Why hard**: Derive from Rosser-Schoenfeld axiom via logarithms
   - **Impact**: Needed to show F < 1

4. **Line 154**: `F_lt_one`
   - **What**: F(k,M) < 1 for k ≥ 9
   - **Why hard**: Combine all bounds and optimize over M
   - **Impact**: Core of contradiction in main theorem

5. **Line 171**: `hM_pos` (in main theorem)
   - **What**: k < M where M = n/k
   - **Why hard**: n > k² insufficient for n/k > k (integer division)
   - **Fix needed**: Either strengthen hypothesis to n > k²+k-1, or handle M ≤ k separately
   - **Impact**: BLOCKS main theorem proof completion

**Status**: Main proof structure complete (60 lines), 1 sorry closed, 4 remaining.

### KonyaginTheorem1.lean (10 sorry)
File builds: ❌ HAS TYPE ERRORS (15 compile errors)

- Not currently blocking since file doesn't compile
- Needs type coercion fixes before sorry work
- Chief directive: parked until ready

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
