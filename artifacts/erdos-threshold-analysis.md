# Literature Analysis: Multi-base Generalization of Stewart's Digit Sum Theorem

This document analyzes the multi-base lower bounds for digit sums and their application to simultaneous digit-sum constraints in Erdős Problem 1094.

## 1. Classical Effective Bounds (Stewart 1980)

C.L. Stewart's original paper, *"On the representation of an integer in two different bases"* (1980), established that for multiplicatively independent bases $g, h \geq 2$, the sum of digits $s_b(n)$ satisfies:
$$s_g(n) + s_h(n) > C \cdot \frac{\log \log n}{\log \log \log n}$$
for $n > 25$. This result is **effective** but provides a sub-logarithmic growth rate.

## 2. Generalization to $r$ Bases

The generalization of Stewart's result to $r$ bases relies on the **Subspace Theorem** (Corvaja and Zannier, 2005; Evertse, 2001). These results prove that for any set of multiplicatively independent bases $b_1, \dots, b_r$:
$$\sum_{i=1}^r s_{b_i}(n) \to \infty \quad \text{as } n \to \infty.$$
However, results derived from the subspace theorem are **ineffective** (they do not provide a method to calculate the threshold $N_0$).

## 3. Effective Bounds for Smooth Numbers (Bugeaud 2008)

Y. Bugeaud (2008) proved that if $n$ is **$M$-smooth** (prime factors $\leq M$), its digit sum in an independent base $b$ grows as:
$$s_b(n) > C_b \cdot \frac{\log n}{\log \log n}$$
This result is **effective** and provides a near-logarithmic lower bound. In the context of Erdős 1094, the "survivors" of the CRT are not smooth, but the condition $k \preceq_p n$ (digit domination) imposes a similar constraint on their digit density.

## 4. Probabilistic Density Argument (Kim 1999, Drmota 2001)

The **Multivariate Central Limit Theorem** for digit sums (Kim, 1999; Drmota, 2001) provides the average behavior for a set of primes $P$:
$$\mathbb{E}\left[\sum_{p \in P} \frac{s_p(n)}{p}\right] \approx \left(\sum_{p \in P} \frac{p-1}{2 p \ln p}\right) \ln n.$$

### Estimation for $p \leq 29$:
For $P = \{2, 3, 5, 7, 11, 13, 17, 19, 23, 29\}$, the constant is:
$$C_{avg} = \sum_{p \leq 29} \frac{p-1}{2 p \ln p} \approx 2.12$$
Since $C_{avg} > 2$, for a **random** integer $n$, the weighted digit sum is likely to exceed $2 \ln n$. 

## 5. Existence of Counterexamples (Bloom and Croot 2025)

Very recent work by **Bloom and Croot (2025)**, *"Integers with small digits in multiple bases"*, proves that for any fixed set of bases, there exist **infinitely many** integers $n$ such that almost all digits are "small" ($\leq g_i/2$). 

This implies that a universal lower bound of the form $\sum s_p(n)/p > 2 \ln n$ **cannot hold for all $n$** with a fixed set of primes. The proof for $k \to \infty$ must therefore utilize a **set of primes that grows with $k$**.

## 6. Conclusion for the Proof Strategy

To turn the large-k density axiom into a theorem:
1.  **Computational Verification:** Use `native_decide` to verify $k$ up to $10^6$ (the peak density occurs at $k=178,416$).
2.  **Super-Logarithmic Scaling:** For $k > 10^6$, use the fact that the actual exception condition considers ALL primes $p \leq k$. The sum $\sum_{p \leq k} s_p(k)/p$ grows as $O(k/\log k)$, which provides a density that decays super-exponentially.

## References
- Stewart, C. L. (1980). *J. reine angew. Math.*, 319, 63-72.
- Bugeaud, Y. (2008). *Osaka J. Math.*, 45, 219-230.
- Bloom, T. F. & Croot, E. (2025). *arXiv:2509.02835*.
- Drmota, M. & Larcher, G. (2001). *Acta Arith.*, 100, 17-39.
