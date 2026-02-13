# Literature Survey: Erdős Problem 1094

This survey explores the background, status, and related results for Erdős Problem 1094, which concerns the least prime factor of binomial coefficients.

## 1. Problem Statement
The problem asks to show that the set of "exceptional" pairs $(n, k)$ is finite:
$$ E = \{ (n, k) : 0 < k, 2k \leq n, \text{minFac}\left(\binom{n}{k}\right) > \max(n/k, k) \} $$
where $\text{minFac}(m)$ denotes the least prime factor of $m$.

An exception $(n, k)$ must satisfy two conditions:
1. $\text{minFac}\left(\binom{n}{k}\right) > k$: The binomial coefficient is $k$-rough (all prime factors are $> k$).
2. $\text{minFac}\left(\binom{n}{k}\right) > n/k$: The least prime factor is also greater than the ratio $n/k$.

## 2. Original Sources and Conjectures
The problem was posed and studied by **Paul Erdős, C. B. Lacampagne, and J. L. Selfridge** in the late 1980s and early 1990s.

*   **[ELS88]**: P. Erdős, C. B. Lacampagne, and J. L. Selfridge, "Prime factors of binomial coefficients and related problems", *Acta Arith.* 49 (1988), no. 5, 507–523.
*   **[ELS93]**: P. Erdős, C. B. Lacampagne, and J. L. Selfridge, "Estimates of the least prime factor of a binomial coefficient", *Math. Comp.* 61 (1993), 215-224.
*   **[Gu04]**: Richard K. Guy, "Unsolved Problems in Number Theory" (3rd ed., 2004), Problems B31 and B33.

In [ELS93], the authors conjecture that $\text{minFac}\left(\binom{n}{k}\right) \leq \max(n/k, 29)$ holds for all $n \geq 2k$, which implies the finiteness of $E$ since any exception would necessarily have $k < 29$.

## 3. Known Exceptions
There are **14 known exceptions** to the inequality $\text{minFac}\left(\binom{n}{k}\right) \leq \max(n/k, k)$, all discovered through numerical searches. They are:
*   $k=3: \binom{7}{3}=35 \implies p=5 > 3$
*   $k=4: \binom{13}{4}=715 \implies p=5 > 4$; $\binom{14}{4}=1001 \implies p=7 > 4$
*   $k=5: \binom{23}{5}=33649 \implies p=7 > 5$
*   $k=6: \binom{62}{6}=61474519 \implies p=19 > 10.33$
*   $k=8: \binom{44}{8} \implies p=13 > 8$
*   $k=10: \binom{46}{10}, \binom{47}{10}, \binom{74}{10}, \binom{94}{10}, \binom{95}{10}$
*   $k=11: \binom{47}{11}$
*   $k=16: \binom{241}{16} \implies p=17 > 15.06$
*   $k=28: \binom{284}{28} \implies p=29 > 28$

Note that the largest value of $k$ among these exceptions is **28**. This supports the conjecture that no exceptions exist for $k \geq 29$.

## 4. Partial Results and Progress
### The Erdős-Selfridge Function $g(k)$
The function $g(k)$ is defined as the least integer $n > k+1$ such that $\text{minFac}\left(\binom{n}{k}\right) > k$.
*   **Schur (1929)** proved $g(k) > k$.
*   **Ecklund, Erdős, and Selfridge (1974)** proved $g(k) \geq 2k$ for most $k$.
*   **Granville and Ramaré (1996)** proved $g(k) \ge \exp(c\sqrt{\log^3 k / \log\log k})$ for an absolute constant $c > 0$. This is the best verified unconditional lower bound (per MathWorld).
*   **Konyagin (1999)** published "Estimates of the least prime factor of a binomial coefficient" in *Mathematika* 46 (1999), 41–55. The exact bound proved is unverified by us — the abstract formula is rendered as an image on Cambridge Core. The paper cites both ELS93 and Granville–Ramaré.
*   **Sorenson (2019)** computed $g(k)$ up to $k = 323$ and conjectured $\log g(k) \sim k/\log k$ conditionally.

**Critical note:** The Granville–Ramaré bound grows **slower than any polynomial** in $k$ — it is $o(k^\varepsilon)$ for every $\varepsilon > 0$. In particular, it does NOT prove $g(k) > k^2$, or even $g(k) > k^{1+\varepsilon}$, for any fixed $\varepsilon$. The conjecture $g(k) > k^2$ for $k > 16$ (ELS93 Conjecture 1) remains **open even ineffectively** as far as we can verify.

### Divisibility by Small Primes
Erdős observed that for a fixed $k$, $\text{minFac}\left(\binom{n}{k}\right) \leq n/k$ for all $n$ sufficiently large. This is because as $n \to \infty$, the probability that $n$ avoids carries in base $p$ for all primes $p \leq n/k$ approaches zero.

## 5. Sylvester-Schur Type Results
*   **Sylvester-Schur Theorem**: For $n \geq 2k$, $\binom{n}{k}$ has a prime factor $p > k$. This theorem guarantees the existence of a "large" prime factor but does not bound the "least" prime factor from above.
*   **Refinement**: Erdős et al. showed that $\binom{n}{k}$ usually has prime factors $\leq n/k$. The "Interval Divisibility Lemma" (often attributed to Selfridge or Erdős) states that if $p$ is a prime in $(k, n/k]$, and $p$ divides $\lfloor n/k \rfloor$, then $p$ divides $\binom{n}{k}$.

## 6. Summary of Status
The problem of showing that $E$ is finite remains **OPEN**. The best unconditional lower bound on $g(k)$ is subpolynomial (Granville–Ramaré 1996), far from the conjectured $g(k) > k^2$. Strong numerical evidence supports the conjecture (no exceptions found for $k \ge 29$), but no theoretical path to a proof is known.

## 7. Key Authors for Further Research
*   **Andrew Granville**: Extensive work on the distribution of prime factors of binomial coefficients.
*   **Shanta Laishram and T. N. Shorey**: Often work on least/greatest prime factors of products of consecutive integers and binomial coefficients.
*   **Yann Bugeaud**: Studies the digital representation of integers with bounded prime factors, which is closely related via Kummer's Theorem.
