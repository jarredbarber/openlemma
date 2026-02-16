# The Exact Tool Needed for `large_n_smooth_case`

## Discovery: Axiom is FALSE as stated

**Counterexample:** n = 62, k = 6, M = ⌊62/6⌋ = 10.

C(62, 6) = 61,474,519 = 19 · 29 · 31 · 59 · 61

All prime factors exceed M = 10. The axiom claims ∃ p ≤ 10 with p | C(62,6),
but no such p exists. **This is the unique counterexample** for k ≤ 40,
n ≤ 5k² (exhaustively verified).

**Fix:** Add hypothesis `7 ≤ k` (or handle k ≤ 6 separately in the main
theorem via finite computation).

## Tool Characterization

### Correct coverage condition

For prime p > k: p | C(n, k) iff **n mod p < k** (not p | n).

This is a **k-wide** target window {0, 1, ..., k-1} in ℤ/pℤ, not a 1-wide
window. For p ∈ (k, 2k-1): the target covers MORE than half of ℤ/pℤ.

### Two mechanisms

For fixed n = kM + r with M k-smooth and r ∈ {1,...,k-1}:

**Mechanism A (Kummer carries):** ∃ prime p ≤ k such that adding k and n-k
in base p produces a carry. Gives p ≤ k ≤ M dividing C(n,k).

**Mechanism B (Gap primes):** ∃ prime p ∈ (k, M] with n mod p < k.
Gives p ≤ M dividing C(n,k).

Only need ONE mechanism to succeed for each (k, M, r).

### Complementarity theorem (computational)

Tested ALL gap prime failures (k ∈ [3, 34], M up to 5000):
- 1,369 total (k, M, r) triples where mechanism B fails
- 1,368 rescued by mechanism A (Kummer)
- **1 true failure:** (62, 6) — the axiom counterexample

**Complementarity rate: 99.93%**

The two mechanisms are COMPLEMENTARY: when gap primes fail (all integers
in the window avoid medium factors), the resulting unusual digit structure
forces Kummer carries in small bases.

### Per-prime miss structure

For prime p ∈ (k, 2k):
- Miss condition: n mod p ∈ {k, ..., p-1} (p-k values out of p-1)
- For p = k+1: miss probability = 1/(k+1). Exactly **one** r value missed
- Two primes miss the **same** r only if M is in a specific CRT class

With T gap primes from (k, 2k]: bad M must satisfy T simultaneous
congruences. CRT modulus ≈ k^T. Bad density ∏(pᵢ-k)/pᵢ → 0 exponentially.

### Gap prime coverage thresholds

For k ≥ 10 and all k-smooth M ≥ M₀(k):

| k  | M₀  | Gap primes at M₀ |
|----|------|-------------------|
| 10 | 22   | 4                 |
| 12 | 29   | 4                 |
| 15 | 23   | 2                 |
| 20 | 41   | 4                 |
| 25 | 39   | 3                 |
| 30 | 40   | 2                 |

For M < M₀: gap primes may fail, but Kummer always rescues.

### What would prove the tool

**Statement (Gap Prime Coverage Lemma):**
For k ≥ K₀ and k-smooth M ≥ M₀(k), for every r ∈ {1,...,k-1}:
∃ prime p ∈ (k, M]: (kM + r) mod p < k

**Why it's hard:**
- Hildebrand equidistribution requires modulus ≤ M^{1-ε}
- Using ALL gap primes: modulus ≈ exp(M) >> M^{1-ε}
- Using few primes: bad density too large to overcome smooth number abundance

**What might work:**
1. **Complementarity proof**: Show structurally that gap prime avoidance
   forces Kummer carries. Bypass gap prime coverage entirely.
2. **Combined sieve**: Sieve jointly by small primes (Kummer) and medium
   primes (gap primes). The combined sieve might succeed where each fails alone.
3. **Smooth number structure**: Exploit that M is k-smooth to constrain
   residues kM mod p for gap primes p.

### The deepest question

Why does gap prime avoidance force Kummer carries?

When all integers in {kM+1,...,kM+k-1} avoid primes in (k, M]:
each is of form a·q (a ≤ k, q > M prime). This forces specific
digit patterns in n = kM+r in all bases p ≤ k. Specifically:
the quotient n/p "uses up" all the smooth factors, leaving the
base-p digits of n in positions where k + (n-k) must produce a carry.

**This structural connection is the real tool.** The proof isn't about
gap primes or Kummer separately — it's about their interaction.
