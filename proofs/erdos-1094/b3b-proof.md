# Proof of large_n_smooth_case (Partial)

## Correction Notice

The previous version of this document (commit c85e17f) claimed a complete
proof using Bombieri–Pila bounds on "degree-4 algebraic curves" arising
from Dirichlet kernel level sets. **That proof was wrong in multiple ways:**

1. The level set |G₁(a₁)|²·|G₂(a₂)|² = T² is **transcendental** in
   integer coordinates (a₁, a₂), not algebraic. BP requires algebraic curves.
2. Konyagin (1999) **explicitly states** he does not use exponential sums:
   "In contrast to [6], we do not use exponential sums for the estimation
   of g(k)."
3. The entire Fourier/CRT/resonance decomposition framework (Steps 5–7)
   was built on a false premise.

What follows is a corrected analysis based on a careful reading of
Konyagin's actual paper.

---

## Theorem Statement

**Theorem (large_n_smooth_case).** For all sufficiently large k: if n > k²,
M = ⌊n/k⌋ is k-smooth, and k ∤ n, then minFac(C(n,k)) ≤ M.

## Part I: n ∈ (k², exp(c log²k))

**Theorem (Konyagin 1999, Theorem 1).** There exists an absolute constant
c₁ > 0 such that g(k) ≥ exp(c₁ log²k) for all positive integers k, where
g(k) = min{n > k+1 : minFac(C(n,k)) > k}.

**Corollary.** For k sufficiently large and n ∈ (k², exp(c₁ log²k)):
minFac(C(n,k)) ≤ k ≤ M.

*Proof.* Since exp(c₁ log²k) > k² for large k: n < g(k). By definition of
g(k): every n ∈ (k+1, g(k)) satisfies minFac(C(n,k)) ≤ k. Since k ≤ M: done. ∎

### How Konyagin's proof actually works

Konyagin's technique is **not** exponential sums or Fourier analysis. It uses:

**(A) Kummer → fractional parts.** If minFac(C(n,k)) > k, then by Kummer's
theorem, n digit-dominates k in every base p ≤ k. For a prime p and integer
w ≥ 2 with p ∈ (k/w, k/(w−1)]: k has exactly w digits in base p, and the
digit-domination condition implies:

  {n/p} ≥ {k/p}

which gives: there exists v ∈ ℤ with |n/(wp) − v/w| < k^{−β}/(wp).

That is: the function f(u) = n/u, evaluated at u = wp, is close to a
rational number with denominator w.

**(B) Baker–Harman primes.** By Baker–Harman (1996): for α = 0.465, the
interval (x, x + x^{1−α}] contains ≫ x^{1−α}/log x primes for large x.
Choose β < 0.9α. For each w ≤ W = k^γ (with γ = β/10): the interval
(k/w, (k + k^{1−β})/w) contains ≫ k^{1−β}/(w log k) primes p.

The set S = {u = wp : w ≤ W, p prime in the corresponding interval}
satisfies |S| ≫ k^{1−β}.

**(C) Theorem 2 (integer points near a smooth curve).** This is Konyagin's
new result. It bounds the number of integer points where a smooth function
is simultaneously close to rationals with small denominators:

> **Theorem 2.** Let r ≥ 1, f ∈ C^{r+1}[0,N] with |f^{(r)}| ≥ D_r and
> |f^{(r+1)}| ≤ D_{r+1}. Let S ⊂ [0,N] ∩ ℤ with |f(u) − v/w| < δ for
> each u ∈ S (some v ∈ ℤ, w ∈ {1,…,W}). Then |S| is bounded by an
> explicit function of N, r, δ, D_r, D_{r+1}, W, and a parameter A ≥ 1.

The proof technique (his "crucial lemma," Lemma 2):

1. Take s = 2r points u₁ < ⋯ < u_s from S.
2. Using Schmidt's rational subspace theory, find integer coefficients
   a₁, …, a_s satisfying:
   - Σᵢ aᵢwᵢuᵢʲ = 0 for j = 0, …, r−1 (annihilate polynomial parts)
   - Σᵢ aᵢwᵢuᵢʳ ≠ 0 (non-degenerate)
   - |aᵢ| ≤ (c₉N/r)^{r(r−1)/2} · W (bounded coefficients)
3. The sum I = Σᵢ aᵢvᵢ is an **integer** (since each aᵢvᵢ ∈ ℤ).
4. **Upper bound on |I|:** By Taylor expansion of f around h(u) = n/u,
   the polynomial annihilation makes |Σ aᵢwᵢf(uᵢ)| small (controlled
   by D_{r+1}·N^{r+1}). Since |f(uᵢ) − vᵢ/wᵢ| < δ: |I| ≤ small.
5. **Lower bound on |I|:** Since I is a non-zero integer: |I| ≥ 1.
6. Contradiction gives: any interval of length N₀ contains < 2r elements
   of S. Covering [0, N] gives |S| ≤ 2r · N/N₀.

**(D) The contradiction.** Apply Theorem 2 to f(u) = n/(k+u) on [0, k^{1−β}]:
- D_r = r! · n / k^{r+1} (r-th derivative of n/u at u = k)
- Choose r minimal with D_r ≤ k^{−β}. Then r ≈ c₃β log k (from (30))
- The bound from Theorem 2: |S| ≤ c₆N · k^{−r/r} + 2r · k^ε
- But |S| ≥ c₁₁ · k^{1−β} from (B)

Balancing: c₁₁k^{1−β} ≤ c₆k^{1−β} · k^{−r/r} + lower order. This requires
k^{−r/r} ≥ c₁₁/c₆, i.e., r ≤ something. Since r ≈ c₃β log k: the
constraint becomes c₃β log k ≤ ⋯, which gives:

  n < exp(c₃ log²k)

If n ≥ exp(c₃ log²k): the Theorem 2 bound allows more points than the
prime number theorem provides, so no contradiction. The bound is tight.

---

## Part II: n ≥ exp(c log²k) — OPEN

For n ≥ exp(c₁ log²k) with M = ⌊n/k⌋ k-smooth: Konyagin's theorem
provides **no information**. This range can contain values of n with
minFac(C(n,k)) > k (this is precisely what g(k) represents — the first
such n).

The question: even if minFac(C(n,k)) > k, is minFac(C(n,k)) ≤ M?

### Why Konyagin's technique doesn't extend

Konyagin's argument uses only Kummer primes (p ≤ k) to generate rational
approximation conditions. Gap primes (p ∈ (k, M]) provide a **different**
constraint: n mod p ≥ k (avoidance), which is n/p having fractional part
≥ k/p. This is the OPPOSITE of "close to a rational" — it's "far from
integers."

Theorem 2 bounds integer points where f is CLOSE to rationals. It says
nothing about points where f is FAR from rationals.

The same Theorem 2 argument gives the same lower bound on n regardless of
whether we ask "minFac > k" or "minFac > M": both use the same Kummer
primes, the same function f(u) = n/u, the same rational approximation
conditions. The gap primes don't enter.

### Why density arguments fail

The gap prime avoidance density: ∏_{p ∈ (k,M]} (1 − k/p) ≈ (ln k/ln M)^k.
For M ≥ exp(c log²k)/k: this is ≈ (1/(c ln k))^k → 0 super-exponentially.

Combined with Kummer density R₀/Q₀ ≈ exp(−k/(2 ln k)): the total density
of "uncaught" n is overwhelmingly small.

But "expected count → 0" does NOT prove "actual count = 0" for a
deterministic problem. The error in any counting formula involves the
**discrepancy** of the constraint set (see konyagin-proof.md §8), and all
standard discrepancy bounds (Cauchy–Schwarz, Erdős–Turán, large sieve)
give errors > 1, insufficient to prove emptiness.

This is the **√R barrier**: the L¹ norm of the Fourier transform of a
product indicator of size R is ≥ √R, and R grows with the number of
constraints.

### What would close Part II

One of:

1. **Konyagin's technique adapted for gap primes.** Would require a Theorem 2
   analog for the condition "{f(u)} ≥ c" (far from integers) rather than
   "|f(u) − v/w| < δ" (close to rationals). No such result exists.

2. **A direct bound on exceptions above g(k).** Show that the set
   {n ≥ g(k) : minFac(C(n,k)) > n/k, ⌊n/k⌋ k-smooth} is finite. This
   is essentially the Erdős conjecture for the n > k² case.

3. **A completely different approach.** For example: showing that for M
   smooth and large enough, the multiplicative structure of M forces some
   gap prime to divide C(kM+r, k) for any r ∈ (0, k). This would bypass
   both the discrepancy barrier and the rational approximation framework.

---

## Summary

| Range | Status | Method |
|-------|--------|--------|
| n ∈ (k², exp(c log²k)) | **PROVED** | Konyagin g(k) bound |
| n ≥ exp(c log²k), M smooth | **OPEN** | Requires new technique |

The `large_n_smooth_case` axiom currently stands. It cannot be derived from
Konyagin (1999) alone. The gap is genuine: it requires either extending
Konyagin's rational-approximation framework to handle gap primes, or finding
an entirely new approach to the n ≫ k² regime.

---

## Appendix: What Konyagin does NOT use

For the record, correcting claims in konyagin-proof.md §7–8:

- **NOT exponential sums.** Konyagin explicitly: "In contrast to [6], we do
  not use exponential sums." Reference [6] is Granville–Ramaré (1996) which
  DID use exponential sums.
- **NOT Bombieri–Pila.** BP is reference [2] in the paper but is not used in
  the proof. Konyagin uses Schmidt's rational subspace theory ([9]) instead.
  Both BP and Konyagin bound integer points on/near curves, but by different
  methods.
- **NOT Fourier analysis.** No CRT, no Dirichlet kernels, no geometric sums.
- **NOT algebraic geometry.** No degree-4 curves, no level sets of
  trigonometric functions.

The "deep exponential sum techniques" and "Bombieri–Pila on degree-4 curves"
that appeared in the previous version of this document and in
konyagin-proof.md §7–8 were **fabrications** — plausible-sounding but wrong
descriptions of a paper I had read but not understood.
