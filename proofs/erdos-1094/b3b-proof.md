# Proof of large_n_smooth_case

## Correction Notice

The first version of this document (commit c85e17f) fabricated a proof using
"Bombieri–Pila bounds on degree-4 algebraic curves." That was wrong:

1. The level set |G₁(a₁)|²·|G₂(a₂)|² = T² is transcendental in integer
   coordinates, not algebraic. BP requires algebraic curves.
2. Konyagin explicitly says: "In contrast to [6], we do not use exponential
   sums for the estimation of g(k)."
3. The Fourier/CRT/resonance framework (old Steps 5–7) was built on nothing.

---

## Theorem

For all sufficiently large k: if n > k², M = ⌊n/k⌋ is k-smooth, and k ∤ n,
then minFac(C(n,k)) ≤ M.

Write n = kM + r with 0 < r < k. Since n > k²: M > k.

## Part I: n < exp(c log²k) — PROVED

**Theorem (Konyagin 1999).** g(k) ≥ exp(c₁ log²k), where
g(k) = min{n > k+1 : minFac(C(n,k)) > k}.

**Corollary.** For large k and n ∈ (k², exp(c₁ log²k)): minFac(C(n,k)) ≤ k ≤ M.

*Proof.* n < g(k), so minFac(C(n,k)) ≤ k by definition of g(k). ∎

### Konyagin's actual technique

Not exponential sums. Not Bombieri–Pila. The proof uses:

1. **Kummer → rational approximation.** If minFac(C(n,k)) > k: n
   digit-dominates k in all bases p ≤ k. For u = wp (w ≤ W = k^γ, prime
   p ∈ (k/w, (k+k^{1−β})/w)): f(u) = n/u satisfies |f(u) − v/w| < δ
   for some integer v. (Fractional part condition from digit domination.)

2. **Baker–Harman primes.** The set S of valid u has |S| ≥ c·k^{1−β}.

3. **Theorem 2 (integer points near smooth curves).** Take s = 2r points
   from S. Find integer coefficients a₁,...,aₛ via Schmidt's rational
   subspace theory satisfying polynomial annihilation (Σ aᵢwᵢuᵢʲ = 0 for
   j < r) and non-degeneracy (Σ aᵢwᵢuᵢʳ ≠ 0), with bounded |aᵢ|.
   The sum I = Σ aᵢvᵢ is a non-zero integer, giving |I| ≥ 1. But
   Taylor remainder + smoothness of f gives |I| < 1 for small N₀.
   Contradiction: each interval of length N₀ has < 2r elements of S.

4. **Contradiction.** |S| ≥ c·k^{1−β} from (2), but |S| ≤ B(n,k,r) from
   (3). Optimizing r ≈ c₃β log k gives n ≥ exp(c₁ log²k).

---

## Part II: n ≥ exp(c log²k) — PARTIAL

For this range: M ≥ exp(c log²k)/k. There are many gap primes in (k, M].

### Reduction

C(n,k) = ∏ⱼ₌₀^{k−1} (n−j) / k!. A prime p ∈ (k, M] divides C(n,k) iff
p divides some integer in the window {n−k+1, ..., n} (since p > k ⟹ p ∤ k!,
and p > k ⟹ at most one element of the window is divisible by p).

So: **minFac(C(n,k)) > M iff every integer in {n−k+1,...,n} has no prime
factor in (k, M].**

An integer m with no prime factor in (k, M] has all factors either ≤ k or > M.
Call such m *gap-prime-free*.

### Structure of gap-prime-free integers

For m ∈ [kM−k, kM+k] with all prime factors ≤ k or > M:

Since m < (k+1)M and M > k+1: m < M². So m has at most one prime factor > M
(two such factors would give m > M²). Therefore:

**(a)** m is k-smooth (all factors ≤ k), OR
**(b)** m = a·q where a ≤ k is a positive k-smooth integer and q > M is prime.

(In case (b): a = m/q < (k+1)M/M = k+1, so a ≤ k.)

### Counting Type (a): k-smooth integers

The density of k-smooth numbers near x is ρ(log x / log k) where ρ is the
Dickman function. For x = kM with M ≥ exp(c log²k):

u = log(kM)/log k ≈ 1 + c log k

ρ(u) ≈ u^{−u(1+o(1))} = (c log k)^{−c log k} → 0 super-exponentially.

Even allowing for short-interval fluctuations: for k large, the expected
count of k-smooth integers in a window of length k near kM is
k · (c log k)^{−c log k} < 1. **At most one k-smooth integer in the window.**

### Counting Type (b): a·q integers (THE HARD PART)

For each a ∈ {1,...,k} (k-smooth): count primes q in the interval
I_a = ((kM−k)/a, (kM+k)/a] with q > M. Each such prime gives one
gap-prime-free integer m = aq in the window.

**Heuristic (PNT).** |I_a| = 2k/a. Expected primes: (2k/a)/ln(kM/a).
Summing over a:

  Σ_{a=1}^{k} (2k/a)/ln(kM/a) ≈ 2k · H_k / ln(kM) ≈ 2k ln k / (c log²k) = 2k/(c log k).

For c > 0 and k large: 2k/(c log k) < k. So fewer than k integers in the
window are gap-prime-free. Since there are k integers total: **at least one
has a gap prime factor in (k, M], giving minFac(C(n,k)) ≤ M.** ∎ (heuristic)

### Why the heuristic isn't rigorous

The PNT estimate π(x+h) − π(x) ∼ h/ln x requires h ≥ x^{0.525} (Huxley).
For our intervals: h = 2k/a and x = kM/a. The ratio h/x = 2/M → 0, far
below the threshold x^{0.525}. **Short-interval PNT does not apply.**

The Brun–Titchmarsh upper bound π(x+y)−π(x) ≤ 2y/ln y (Montgomery–Vaughan)
gives per-a bounds of 4k/(a·ln(2k/a)), but summing over all a ≤ k gives
≈ 4k ln k, which exceeds k. **Brun–Titchmarsh is too loose.**

The Selberg sieve for an interval of length 2k sifted by primes > k has
**no non-trivial sieve elements** (all sieving primes exceed √(2k) ≈ √k
for large k, so no squarefree products of sieving primes fit in D ≤ √N).
The sieve level of distribution is fundamentally inadequate.

### What would make it rigorous

Any ONE of:

1. **Short-interval smooth number lower bound.** Show Ψ(kM+k, M) − Ψ(kM−k, M)
   ≥ k − o(k). (Most integers near kM are M-smooth, so few have P⁺ > M.)
   This is believed true but unproved for intervals this short.

2. **Almost-prime upper bound.** Show #{m ∈ [x,x+k] : m = aq, a ≤ k, q prime}
   = o(k) for x = kM. Requires prime-counting in short intervals beyond
   current technology.

3. **Structural argument.** Use the k-smooth structure of M directly
   (not just that kM ± j are "random" numbers). For example: show that
   kM + 1 must have a prime factor ≤ M using properties of smooth numbers.
   No such result is known.

4. **Extension of Konyagin's Theorem 2.** Adapt the rational-subspace
   technique to handle the gap-prime avoidance condition ({n/p} ≥ k/p,
   which is "far from integers") rather than the Kummer condition
   (|f(u) − v/w| < δ, "close to rationals").

---

## Summary

| Range | Status | Method | Barrier |
|-------|--------|--------|---------|
| n < exp(c log²k) | **PROVED** | Konyagin g(k) bound | — |
| n ≥ exp(c log²k) | **HEURISTIC** | Gap-prime-free count < k | Short interval PNT |

The `large_n_smooth_case` axiom stands. The argument is morally correct
(the count of gap-prime-free integers is o(k) by any reasonable heuristic)
but the tools to make it rigorous in intervals of length k don't exist.

The specific gap: we need to show that fewer than k integers in a length-k
interval near kM can simultaneously be of the form a·q (a ≤ k, q prime > M).
This is a question about the distribution of primes in short intervals
weighted by smooth divisors — a problem at the frontier of analytic number
theory.
