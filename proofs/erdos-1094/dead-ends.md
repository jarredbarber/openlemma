# Dead Ends and Approaches Tried

This document records approaches that have been considered and why they don't immediately work, to prevent re-exploration.

## 1. Using a single prime (e.g., 2 or 3) to handle all k

**Idea:** Show that 2 | C(n,k) for all n ≥ 2k and k ≥ K₀.

**Why it fails:** For any k, there exist infinitely many n where 2 ∤ C(n,k). By Kummer's theorem, 2 ∤ C(n,k) iff k is a binary submask of n. Taking n with k's 1-bits set always works. Similarly for any fixed prime p: there exist infinitely many n where p ∤ C(n,k).

**Conclusion:** No single prime suffices. The proof must use the interplay of MULTIPLE primes simultaneously.

## 2. Pure size/counting argument

**Idea:** Since C(n,k) ≈ n^k/k! and the threshold is max(n/k, k), show that C(n,k) is "too large" to have all prime factors > threshold.

**Why it fails:** C(n,k) could in principle be a product of a few large primes. A number with ω(m) prime factors, all > M, satisfies m > M^{ω(m)}, but C(n,k) with k prime factors each ≈ n gives n^k/k! > M^k, which only requires M < n/k^{1/k} ≈ n. This doesn't give M ≤ max(n/k, k).

## 3. Density argument alone (no CRT structure)

**Idea:** The probability that C(n,k) avoids all primes ≤ M is ∏(1 - k/p) ≈ (ln k/ln M)^k. Since this goes to 0, there are "few" exceptions.

**Why it's insufficient:** The density decays like (c/ln n)^k, and ∑_n (c/ln n)^k diverges for any fixed k ≥ 1. So the density argument alone doesn't prove finiteness — it only proves zero density.

**The fix:** Must also use the digit-domination conditions for primes ≤ k, which provide an additional density factor δ_k that is exponentially small in k. The COMBINED density (δ_k × primes-above-k factor) is small enough in practice, but making this rigorous still requires careful sieve theory.

## 4. Bertrand's postulate for a single interval

**Idea:** By Bertrand, there's a prime p ∈ (k, 2k]. If this p divides C(n,k), we're done.

**Why it's insufficient:** For p > k, p | C(n,k) iff n mod p ≤ k-1. With p ∈ (k, 2k], the condition n mod p ≥ k holds for (p-k)/p ≤ 1/2 of all n. So there's only a 50% chance (at best) that the Bertrand prime helps. We can't guarantee it works for a specific n.

Also: we need p ≤ max(n/k, k). The Bertrand prime p ≤ 2k satisfies p ≤ max(n/k, k) only when n/k ≥ 2k, i.e., n ≥ 2k². For n < 2k², the Bertrand prime might exceed the threshold.

## 5. Stewart/Bugeaud bounds for CRT density threshold

**Idea:** Use Stewart (1980) and Bugeaud (2008) to prove that the CRT density $\delta_k < 1/k^2$ for all $k > K_0$ with an explicit $K_0$ (e.g., $K_0 = 10000$).

**Why it fails:** Stewart proves $s_a(n) + s_b(n) \to \infty$ for multiplicatively independent $a, b$, with effective bound $\geq C \cdot \log n / (\log \log n)^2$. This grows **sublinearly** in $\log n$, but we need $-\ln(\delta_k) > 2 \ln k$, which requires the weighted sum $\sum_{p \leq 29} s_p(k)/p$ to exceed $2 \ln k$. Stewart's bound is too weak by a factor of $(\log \log k)^2$. Bugeaud gives asymptotic distribution results but no explicit thresholds.

**Empirical status:** The worst-case ratio $-\ln(\delta_k) / (2\ln k)$ is **1.036** at $k = 178416$, barely above 1. No known analytical technique provides a bound this tight. See proofs/crt-density-large-k.md for full analysis.

**Conclusion:** The Stewart/Bugeaud approach CANNOT provide the explicit threshold needed for the axioms. The gap between their bounds and what we need is fundamental, not just a matter of making constants explicit.

## 6. Using primes 2 and 3 alone for large k

**Idea:** Since $M_{2,3} = 2^{L_2} \cdot 3^{L_3} > k^2$ (Lemma 1), perhaps the density from just primes 2 and 3 is small enough that $\delta_{2,3} \cdot k^2 < 1$.

**Why it fails spectacularly:** For $k = 178416$, $\delta_{2,3} \cdot k^2 \approx 3{,}070{,}242$. The density from primes 2 and 3 alone leaves MILLIONS of candidate $n$ values in $[2k, k^2]$. All 10 primes are needed to eliminate them. The 8 additional primes $\{5, 7, 11, 13, 17, 19, 23, 29\}$ provide the crucial filtering.

## 7. Trying to avoid Kummer's theorem

**Idea:** Prove the result using only elementary divisibility, without the digit-representation machinery.

**Why it's hard:** The exceptions are precisely characterized by the digit-domination conditions. Without understanding this structure, it's very hard to explain why (284, 28) is an exception but (285, 28) is not. Kummer's theorem is the natural and essentially necessary tool.
