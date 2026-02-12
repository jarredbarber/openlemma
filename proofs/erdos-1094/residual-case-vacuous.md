# Refutation of `residual_case_vacuous`

**Status:** Draft ✏️
**Statement:** The axiom `residual_case_vacuous` (KGe29.lean:312) claims that for $n, k \in \mathbb{N}$ with $k \geq 2$ and $n \geq 2k^2$, if $\lfloor n/k \rfloor$ is $k$-smooth (all prime factors $\leq k$) and $n / \gcd(n,k)$ is a prime greater than $\lfloor n/k \rfloor$, then no such $n$ exists (False). **This is false.** Counterexamples exist for all $k \geq 2$, including $k \geq 29$ where the axiom is actually used.
**Dependencies:** None
**Confidence:** Certain

---

## 1. The Axiom

```lean
axiom residual_case_vacuous (n k : ℕ) (hk : 2 ≤ k) (hn : 2 * k * k ≤ n)
    (hsmooth : ∀ p, p.Prime → p ∣ n / k → p ≤ k)
    (hprime : (n / n.gcd k).Prime) (hlarge : n / k < n / n.gcd k) : False
```

In words: there do not exist natural numbers $n, k$ with $k \geq 2$, $n \geq 2k^2$, such that:
1. Every prime factor of $\lfloor n/k \rfloor$ is $\leq k$ (i.e., $\lfloor n/k \rfloor$ is $k$-smooth),
2. $d := n / \gcd(n,k)$ is prime, and
3. $\lfloor n/k \rfloor < d$.

## 2. Structural Analysis

Let $g = \gcd(n, k)$. Since $g \mid k$ and condition (3) requires $\lfloor n/k \rfloor < n/g$ (which forces $g < k$, i.e., $k \nmid n$), write $k = gq$ for integer $q \geq 2$.

Then $d = n/g$ and $\lfloor n/k \rfloor = \lfloor n/(gq) \rfloor = \lfloor d/q \rfloor$.

The conditions become:
- $d$ is prime,
- $d \geq 2gq^2$ (from $n = gd \geq 2k^2 = 2g^2q^2$, so $d \geq 2gq^2$),
- $\lfloor d/q \rfloor$ is $k$-smooth,
- $\lfloor d/q \rfloor < d$ (automatic since $q \geq 2$).

So we seek: a prime $d$ such that $\lfloor d/q \rfloor$ is $gq$-smooth.

**There is no reason this should be impossible.** The value $\lfloor d/q \rfloor$ is essentially $d/q$ rounded down — it bears no algebraic relation to $d$ that would force it to have large prime factors. For any target $k$-smooth number $a$, one can look for primes $d$ in the interval $[aq, (a+1)q)$, and by the prime number theorem such primes exist for most values of $a$.

## 3. Explicit Counterexamples

### 3.1. Counterexample for $k = 2$

Take $n = 17$, $k = 2$.

| Condition | Verification |
|-----------|-------------|
| $k \geq 2$ | $2 \geq 2$ ✓ |
| $n \geq 2k^2$ | $17 \geq 8$ ✓ |
| $\gcd(n,k)$ | $\gcd(17,2) = 1$ |
| $\lfloor n/k \rfloor$ | $\lfloor 17/2 \rfloor = 8 = 2^3$, which is $2$-smooth ✓ |
| $n/\gcd(n,k)$ prime | $17/1 = 17$, prime ✓ |
| $\lfloor n/k \rfloor < n/\gcd(n,k)$ | $8 < 17$ ✓ |

All conditions satisfied; $(17, 2)$ is a counterexample.

Additional counterexamples for $k = 2$: $(n, k) = (257, 2)$ and $(65537, 2)$. These arise from Fermat primes $m = 2^{j+1}+1$ where $\lfloor m/2 \rfloor = 2^j$ is trivially 2-smooth.

### 3.2. Counterexample for $k = 3$

Take $n = 19$, $k = 3$.

| Condition | Verification |
|-----------|-------------|
| $k \geq 2$ | $3 \geq 2$ ✓ |
| $n \geq 2k^2$ | $19 \geq 18$ ✓ |
| $\gcd(n,k)$ | $\gcd(19,3) = 1$ |
| $\lfloor n/k \rfloor$ | $\lfloor 19/3 \rfloor = 6 = 2 \cdot 3$, which is $3$-smooth ✓ |
| $n/\gcd(n,k)$ prime | $19/1 = 19$, prime ✓ |
| $\lfloor n/k \rfloor < n/\gcd(n,k)$ | $6 < 19$ ✓ |

### 3.3. Counterexample for $k = 29$ (the critical case)

Take $n = 1693$, $k = 29$.

| Condition | Verification |
|-----------|-------------|
| $k \geq 2$ | $29 \geq 2$ ✓ |
| $n \geq 2k^2$ | $1693 \geq 1682$ ✓ |
| $\gcd(n,k)$ | $\gcd(1693, 29) = 1$ (since $1693 = 58 \times 29 + 11$) |
| $\lfloor n/k \rfloor$ | $\lfloor 1693/29 \rfloor = 58 = 2 \times 29$, which is $29$-smooth ✓ |
| $n/\gcd(n,k)$ prime | $1693/1 = 1693$, prime ✓ |
| $\lfloor n/k \rfloor < n/\gcd(n,k)$ | $58 < 1693$ ✓ |

**Primality of 1693:** $\sqrt{1693} < 42$. Check primes up to 41: not divisible by 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41. Confirmed prime.

Additional counterexamples for $k = 29$: $(1741, 29)$, $(1831, 29)$, $(1861, 29)$, $(1889, 29)$, and infinitely many more (see Section 4).

### 3.4. Counterexample for $k = 100$

Take any prime $d$ in $[20001, 20100)$ (so that $\lfloor d/100 \rfloor = 200 = 2^3 \times 5^2$, which is 5-smooth hence 100-smooth). Since $\gcd(d, 100) = 1$ for any prime $d > 5$, we get $n = d$, $k = 100$, $\lfloor n/k \rfloor = 200$, $n/\gcd(n,k) = d > 200$, and $n \geq 20001 \geq 20000 = 2 \times 100^2$.

By the prime number theorem, the interval $[20001, 20100)$ contains approximately $100/\ln(20000) \approx 10$ primes. Indeed, $20011, 20021, 20023, 20029, \ldots$ are all valid.

## 4. Why Counterexamples Are Abundant

For any $k \geq 2$, the counterexamples are **infinitely many**. Here is why:

Choose $g = 1$ (so $q = k$, $d = n$). The conditions reduce to:
- $n$ is prime,
- $n \geq 2k^2$,
- $\lfloor n/k \rfloor$ is $k$-smooth.

Fix any $k$-smooth number $a \geq 2k$ (infinitely many exist). Look for primes in $[ak, (a+1)k)$. By the prime number theorem (or Bertrand-type results for short intervals), for $a$ sufficiently large, the interval $[ak, ak+k)$ contains a prime with probability approaching 1. The number of primes in $[ak, ak+k)$ is asymptotically $k / \ln(ak)$, which is $\geq 1$ for all but finitely many $k$-smooth values $a$.

Moreover, $k$-smooth numbers are infinite (e.g., $a = k^j$ for all $j$), and for each such $a$ with $a \geq 2k$, any prime $n \in [ak, (a+1)k)$ gives a valid counterexample (since $\lfloor n/k \rfloor = a$ and $\gcd(n,k) = 1$ for $n$ prime and $n > k$... unless $k$ has a prime factor dividing $n$, but since $n$ is prime and $n > k$, we have $\gcd(n,k) = 1$ unless $n \mid k$, which is impossible).

Wait — we need $\gcd(n, k) = 1$ when $n$ is prime and $n > k$. This holds unless the prime $n$ divides $k$, which requires $n \leq k$, contradicting $n > k$. So $\gcd(n,k) = 1$ for all primes $n > k$. ✓

## 5. Impact on the Formalization

### Where the axiom is used

The axiom is invoked at KGe29.lean:343, inside `prime_large_divisor_case`, for the sub-case $n \geq 2k^2$ within the proof of `large_n_minFac_bound`. In context, the calling lemma also has $k \geq 29$.

### Why the overall theorem is NOT broken

Crucially, the overall theorem $\mathrm{minFac}(\binom{n}{k}) \leq n/k$ (for $n > k^2$) is still true at the counterexamples. For instance:

- $\binom{1693}{29}$: smallest prime factor is $3$, and $3 \leq 58 = \lfloor 1693/29 \rfloor$. ✓
- $\binom{17}{2} = 136 = 2^3 \times 17$: smallest prime factor is $2 \leq 8$. ✓

The conditions of the axiom describe $(n, k)$ pairs where the *particular proof strategy* (using $d = n/\gcd(n,k)$ as a direct witness) cannot work (because $d > n/k$), but the theorem itself is still true via other witnesses. In these cases, some prime $p \leq k$ divides $\binom{n}{k}$ (e.g., by Kummer's theorem / digit domination), providing the required small factor.

### Required fix

The proof of `prime_large_divisor_case` for the sub-case $n \geq 2k^2$ must be restructured. Instead of claiming this case is vacuous, it should:

1. Find a prime $p \leq k$ (or $p \leq n/k$) that divides $\binom{n}{k}$, using CRT/digit domination arguments (extending the approach already used for $k^2 < n < 2k^2$), **or**
2. Show that the composite case ($d$ not prime) always provides a small factor, and handle the prime-$d$ case separately with a different witness.

One natural approach: when $n \geq 2k^2$ and $\lfloor n/k \rfloor$ is $k$-smooth, Bertrand's postulate gives a prime $p^* \in (k, 2k]$. Since $p^* \leq 2k \leq n/k$ (as $n \geq 2k^2$), we have $p^* \leq n/k$. It suffices to show $p^* \mid \binom{n}{k}$, i.e., $n \bmod p^* < k$. This doesn't always hold, but the *combined* CRT constraints from $p^*$ and the digit domination constraints for primes $\leq k$ may eliminate all exceptions. This is essentially the argument from proofs/large-n-divisibility.md Section 7.3 (Type B, Case B1), but it needs to be applied *here* in the proof, not replaced by a vacuity claim.

## References

- Erdos/KGe29.lean lines 306–343 (axiom statement and usage)
- proofs/large-n-divisibility.md Section 7.3 (the Type B case analysis that should replace this axiom)
