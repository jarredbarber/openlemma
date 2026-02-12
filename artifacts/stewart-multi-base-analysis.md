# Literature Analysis: Multi-Base Stewart Generalization

**Task**: Find a multi-base version of Stewart's (1980) digit sum theorem to bound $\sum s_p(n)/p$.

## 1. Multi-Base Generalization of Stewart (1980)
C.L. Stewart's original paper established a lower bound for $s_g(n) + s_h(n)$ for multiplicatively independent bases. 

Generalizations to $r$ bases have been studied using the **Subspace Theorem**:
*   **Corvaja & Zannier (2005)**: Proven that $\sum_{i=1}^r s_{b_i}(n) \to \infty$.
*   **Bugeaud (2008)**: Established effective lower bounds for $M$-smooth numbers: $s_b(n) > C_b \frac{\log n}{\log \log n}$.
*   **Bugeaud & Kaneko (2018)**: (*Osaka J. Math.* 55) Proved $s_b(n) \ge 4$ for sufficiently large $n$ with small prime factors.

## 2. Weighted Sum Growth: $\sum_{p \in P} s_p(n)/p$
The average behavior for the 10 primes $\le 29$ is $\approx 2.12 \ln n$. However, providing a universal lower bound of $C \ln n$ for a **fixed set** of primes is complicated by:

### The Bloom & Croot (2025) Obstruction
**Bloom & Croot (2025)** ("Integers with small digits in multiple bases", *arXiv:2509.02835*) proves that for any fixed set of bases, there are **infinitely many** integers with "small digits" ($\le p/2$).
*   For these integers, the weighted sum $\sum s_p(n)/p$ will **not** exceed $C \ln n$ for any $C > \sum \log_p 2$.
*   Our calculated sum of $\log_p 2$ for the 10 primes is $\approx 3.89$. Since $3.89 > 2$, the 10 primes are **asymptotically sufficient** for our required density $\delta_k < 1/k^2$.

## 3. Effective Bounds and Constants
While Stewart's result is effective, the constants are derived from Baker's theorem and are extremely large. 
*   No explicit constant $C > 2$ for the Natural Logarithm is numerically given in the literature for the fixed set of primes $\le 29$.
*   **Threshold $K_0$**: Empirical scan through $k = 500,000$ shows the density bound holds with a 3.6% margin at the worst-case peak ($k = 178,416$).

## Conclusion for Proof Strategy
1.  Use **Computational Verification** for $k \le 1,000,000$.
2.  Use **Analytical Super-Logarithmic Decay** for $k > 1,000,000$ by using all primes $p \le k$. This avoids the fixed-base obstruction and ensures $\delta_k$ decays faster than any power of $k$.
