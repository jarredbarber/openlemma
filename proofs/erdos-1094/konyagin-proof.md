# Proof: $g(k) \ge k^{c\log k}$ via Exponential Sums

**Status:** Draft ✏️  
**Goal:** Prove an explicit lower bound $g(k) \ge k^{c\log k}$ for a computable $c > 0$.  
**Method:** Exponential sum estimates over digit-constrained sets, following Konyagin (1999).

---

## 1. Setup

**Definition.** $g(k) = \min\{n > k+1 : \mathrm{minFac}\binom{n}{k} > k\}$.

By Kummer's theorem: $p \mid \binom{n}{k}$ iff there is a carry when adding $k$ and $n-k$ in base $p$. Equivalently: $p \nmid \binom{n}{k}$ iff $n$ **digit-dominates** $k$ in base $p$ (each digit of $n$ is $\ge$ the corresponding digit of $k$).

So $g(k) \le N$ iff there exists $n \le N$ with $n > k+1$ such that $n$ digit-dominates $k$ in base $p$ for ALL primes $p \le k$.

**Our goal:** Show no such $n$ exists in $[k+2, N-1]$ for $N = k^{c\log k}$.

## 2. Primes Near $k/2$

Fix $k \ge 4$. For a prime $p \in (k/2, k)$: $k$ has exactly 2 digits in base $p$:
$$k = 1 \cdot p + (k - p), \quad \text{digits } a_0 = k-p \in [1, \lfloor p/2 \rfloor), \quad a_1 = 1.$$

The digit-domination set modulo $p^2$:
$$S_p = \{s \in \{0,\ldots,p^2-1\} : d_0(s) \ge k-p,\; d_1(s) \ge 1\}$$

where $s = d_0 + d_1 p$ with $0 \le d_0, d_1 < p$.

- Valid $d_0$: $\{k-p, k-p+1, \ldots, p-1\}$, count $= 2p - k$.
- Valid $d_1$: $\{1, 2, \ldots, p-1\}$, count $= p - 1$.
- $|S_p| = (2p-k)(p-1)$.
- Density: $\delta_p = (2p-k)(p-1)/p^2$.

## 3. The Product Set

Choose $r$ distinct primes $p_1 < p_2 < \cdots < p_r$ from $(k/2, k)$. Set:
$$M = \prod_{i=1}^r p_i^2, \qquad S = \{n \bmod M : n \bmod p_i^2 \in S_{p_i} \;\forall\, i\}$$

By CRT ($p_i$ are distinct primes): $|S| = R := \prod_{i=1}^r |S_{p_i}|$ and the density is $\delta = R/M = \prod_i \delta_{p_i}$.

**Fact.** If $n$ digit-dominates $k$ in ALL bases $p_1, \ldots, p_r$, then $n \bmod M \in S$. So:

$$|\{n \in [k+2, N] : n \text{ digit-dom } k \text{ for } p_1,\ldots,p_r\}| \le |S \cap [k+2, N]|$$

## 4. Counting $S$-Elements in $[1, N]$: Exponential Sum Approach

$$|S \cap [1, N]| = \frac{1}{M}\sum_{h=0}^{M-1} \hat{S}(h) \cdot D_N(h)$$

where $\hat{S}(h) = \sum_{s \in S} e(hs/M)$ and $D_N(h) = \sum_{n=1}^{N} e(-hn/M)$.

The $h = 0$ term gives $R \cdot N / M = \delta N$ (the main term).

For $h \ne 0$: $|D_N(h)| \le \min(N, 1/(2\|h/M\|))$ where $\|\cdot\|$ is distance to nearest integer.

**Key identity:** $\hat{S}(h)$ factors via CRT:
$$\hat{S}(h) = \prod_{i=1}^r f_i(h_i)$$
where $h_i \equiv h \cdot (M/p_i^2)^{-1} \pmod{p_i^2}$ and $f_i(h_i) = \sum_{s \in S_{p_i}} e(h_i s/p_i^2)$.

## 5. Per-Prime Exponential Sum $f_p(h)$

For prime $p \in (k/2, k)$ with $a_0 = k-p$, $c_0 = 2p-k$:

$$f_p(h) = \underbrace{\left(\sum_{d_0=a_0}^{p-1} e\!\left(\frac{h d_0}{p^2}\right)\right)}_{\tau_0(h)} \cdot \underbrace{\left(\sum_{d_1=1}^{p-1} e\!\left(\frac{h d_1}{p}\right)\right)}_{\tau_1(h)}$$

**Lemma 5.1** (Evaluation of $\tau_1$).
$$\tau_1(h) = \begin{cases} p - 1 & \text{if } p \mid h \\ -1 & \text{if } p \nmid h \end{cases}$$

*Proof.* $\sum_{d=0}^{p-1} e(hd/p) = 0$ for $p \nmid h$ (roots of unity), $= p$ for $p \mid h$. Subtract the $d=0$ term. $\square$

**Lemma 5.2** (Bound on $\tau_0$). For $p^2 \nmid h$:
$$|\tau_0(h)| \le \min\!\left(c_0,\; \frac{1}{2\sin(\pi/p^2)}\right) \le \min(c_0,\; p^2/\pi)$$

The trivial bound $c_0 = 2p - k$ is tight when $h$ is near a multiple of $p^2$.

**Combining:** For $p \nmid h$: $|f_p(h)| = |\tau_0(h)|$.  
For $p \mid h$, $p^2 \nmid h$: $|f_p(h)| = (p-1) \cdot |\tau_0^{(1)}(h/p)|$ where $\tau_0^{(1)}(j) = \sum_{d=a_0}^{p-1} e(jd/p)$.

**Lemma 5.3** (Bound on $\tau_0^{(1)}$). For $p \nmid j$:
$$|\tau_0^{(1)}(j)| = \left|\frac{\sin(\pi c_0 j/p)}{\sin(\pi j/p)}\right| \le \min\!\left(c_0,\; \frac{1}{2\|j/p\|}\right)$$

## 6. The Discrepancy Bound

The error term (discrepancy) is:
$$E(N) = |S \cap [1,N]| - \delta N = \frac{1}{M}\sum_{h=1}^{M-1} \hat{S}(h)\, D_N(h)$$

We bound $|E(N)|$ by splitting the sum over $h$ according to the $p$-adic structure.

**Partition of $\{1, \ldots, M-1\}$:** For each subset $I \subseteq \{1,\ldots,r\}$, let $H_I = \{h : p_i \mid h_i \Leftrightarrow i \in I\}$.

For $h \in H_I$:
$$|\hat{S}(h)| = \prod_{i \in I} (p_i - 1) |\tau_0^{(1)}(\cdot)| \cdot \prod_{i \notin I} |\tau_0(h_i)|$$

**Case $I = \emptyset$** (generic $h$): $|\hat{S}(h)| \le \prod_{i=1}^r c_{0,i}$ where $c_{0,i} = 2p_i - k$.

This is the dominant case. The contribution to $|E(N)|$ is:
$$E_\emptyset \le \frac{\prod c_{0,i}}{M} \sum_{h \in H_\emptyset} \min(N, 1/(2\|h/M\|))$$

The inner sum, over ALL $h$ (not just $H_\emptyset$), is bounded by $N + M\log M$. So:
$$E_\emptyset \le \frac{\prod c_{0,i}}{M} \cdot (N + M\log M) = \frac{N \prod c_{0,i}}{M} + (\log M) \prod c_{0,i}$$

Now $\prod c_{0,i} / M = \prod c_{0,i} / \prod p_i^2 = \prod (c_{0,i}/p_i^2)$. And $\delta = \prod c_{0,i}(p_i-1)/p_i^2$. So $\prod c_{0,i}/M = \delta / \prod(1-1/p_i) \approx \delta \cdot \prod p_i/(p_i-1)$.

For primes near $k/2$: $\prod p_i/(p_i-1) \le (1 + 2/k)^r \approx 1$ for $r$ bounded. So:
$$E_\emptyset \lesssim \delta N + (\log M) \prod c_{0,i}$$

The first term is $\delta N$ (same order as the main term — useless for bounding $E$!).

**This confirms: the trivial bound on $\tau_0$ gives $E_\emptyset \sim \delta N$, which cannot prove $|S \cap [1,N]| < 1$.**

## 7. Where Bombieri–Pila Enters

The trivial bound $|\tau_0(h)| \le c_0$ counts ALL $c_0$ terms. But for most $h$, the sum $\tau_0(h)$ has cancellation: $|\tau_0(h)| \ll \sqrt{c_0}$ on average.

**Precisely:** By Parseval, $\sum_{h=0}^{p^2-1} |\tau_0(h)|^2 = p^2 \cdot c_0$, so the mean-square is $c_0$, giving RMS $= \sqrt{c_0}$.

The problem: we need to bound the SUM $\sum_h |\hat{S}(h)| / h$, not individual values. The "bad" $h$ values (where ALL $|\tau_0(h_i)|$ are simultaneously large) determine the discrepancy.

**Definition.** Call $h$ **$\alpha$-resonant for prime $p_i$** if $|\tau_0(h_i)| \ge \alpha \sqrt{c_{0,i}}$.

By Parseval (Markov): $|\{h_i : h \text{ is } \alpha\text{-resonant for } p_i\}| \le p_i^2 / \alpha^2$.

**For $r$ primes simultaneously:** An $h$ that is $\alpha$-resonant for ALL $r$ primes satisfies $r$ constraints. By CRT, the set of such $h$ modulo $M$ has size at most:
$$\text{(naive)} \le \prod_{i=1}^r p_i^2/\alpha^2 = M/\alpha^{2r}$$

This naive bound (CRT independence) gives: the number of $\alpha$-resonant $h$ in $[1, M]$ is $\le M/\alpha^{2r}$. Their contribution to the discrepancy:

$$E_{\text{res}} \le (M/\alpha^{2r}) \cdot (\alpha\sqrt{c_0})^r \cdot \frac{\log M}{M} = \frac{(\sqrt{c_0})^r \cdot \log M}{\alpha^r}$$

Optimizing: $\alpha = 1$ gives $E_{\text{res}} \le (\sqrt{c_0})^r \cdot \log M$.

**Bombieri–Pila improves this** by showing the resonant set has FEWER lattice points than the naive CRT bound predicts. Specifically, the simultaneous resonance condition defines algebraic curves (from the structure of geometric sums), and BP bounds the number of lattice points on these curves.

**BP Theorem (simplified).** For a plane algebraic curve $\Gamma$ of degree $d$ and a box of side $B$: $|\Gamma \cap \mathbb{Z}^2| \le C_d \cdot B^{1/d}$ for an explicit constant $C_d$.

For 2 primes: the resonance condition on $(h_1, h_2) \in (\mathbb{Z}/p_1^2) \times (\mathbb{Z}/p_2^2)$ defines a curve of degree $\le 2c_0$ (from the structure of $\tau_0$). By BP:

$$|\{(h_1, h_2) : \text{simultaneously resonant}\}| \le C_{2c_0} \cdot (p_1 p_2)^{2/(2c_0)}$$

For $c_0$ small (primes near $k/2$, $c_0 = 2p-k \approx 2t$ for $t = p - k/2$): the degree is $\approx 4t$, and the BP bound is $\approx C \cdot k^{1/t}$.

## 8. Putting It Together

Choose $r$ primes with $c_{0,i} = 2t_i$ (where $t_i = p_i - k/2$). 

**Main term:** $\delta N = \prod_i (2t_i(p_i-1)/p_i^2) \cdot N \approx \prod_i (4t_i/k) \cdot N$.

For $r$ primes with $t_i = t$: $\delta \approx (4t/k)^r$ and $\delta N = (4t/k)^r \cdot N$.

**Discrepancy (with BP):** Using BP for pairs of primes:
$$|E(N)| \le C \cdot r^2 \cdot k^{2/t} \cdot \frac{(2t)^r}{M} \cdot (N + M\log M)$$

(The $r^2$ comes from summing over all $\binom{r}{2}$ pairs; the $k^{2/t}$ from BP.)

For $|E(N)| < 1$ and $\delta N < 1$: need $N < (k/(4t))^r$ and $k^{2/t} \cdot (2t)^r / M \ll 1$.

**Optimal choice:** $t \approx \log k$ and $r \approx c' \log k / \log\log k$. Then:
- $\delta \approx (4\log k / k)^r = \exp(-r(\log k - \log(4\log k))) \approx \exp(-c' \log^2 k / \log\log k)$.
- BP cost: $k^{2/\log k} = e^2 \approx 7.4$ (bounded constant!).
- Discrepancy: dominated by the BP-bounded resonant set, which is $O(1)$.

**Conclusion:** $g(k) \ge 1/\delta \ge \exp(c' \log^2 k / \log\log k)$ for explicit $c'$.

This matches the Granville–Ramaré form $\exp(c\sqrt{\log^3 k / \log\log k})$ up to the exponent structure. Konyagin's improvement to $\exp(c\log^2 k)$ comes from a more refined analysis of the BP curves (using higher-dimensional lattice point counting rather than pairwise).

## 9. Explicit Constant

From the above with $t = \lfloor\log k\rfloor$ and $r = \lfloor\log k / (2\log\log k)\rfloor$:

$$g(k) \ge \exp\!\left(\frac{\log^2 k}{4\log\log k}\right) \quad \text{for } k \ge k_0$$

This gives $g(k) > k^2$ when $\log^2 k / (4\log\log k) > 2\log k$, i.e., $\log k > 8\log\log k$, i.e., $k > (\log k)^8$, which holds for $k \ge 2$.

**⚠️ CAVEAT:** The argument in §8 uses BP in a simplified way (pairwise, not optimally). The constants $C$ and the degree bound need to be made fully explicit. The BP constant $C_d$ for degree-$d$ curves satisfies $C_d \le (d+1)^2$ (from Pila 1995). For $d = 4t \approx 4\log k$: $C_d \le (4\log k + 1)^2$.

## 10. What Remains to Make This Rigorous

| Step | Status | Difficulty |
|------|--------|-----------|
| §1–5: Setup and factorization | Complete ✅ | Easy |
| §6: Trivial discrepancy fails | Complete ✅ | Easy |
| §7: Identify BP curves | **Sketch only** | Hard |
| §8: Combine BP with density | **Sketch only** | Medium |
| §9: Explicit constants | **Needs full BP details** | Medium |

**The key gap:** §7 requires identifying the specific algebraic curves that the resonance conditions define. This depends on the structure of $\tau_0(h)$ as a function of $h \bmod p^2$, and how the simultaneous resonance for two primes $(p_1, p_2)$ constrains $(h_1, h_2)$.

**Conjecture (based on §8 analysis):** An explicit $c \ge 1/4$ is achievable with careful bookkeeping of the BP constants. This would give $K_0 \le 4200$, reducible to 1 axiom via computation.

---

## References

1. S. V. Konyagin, *Mathematika* **46** (1999), 41–55.
2. A. Granville, O. Ramaré, *Mathematika* **43** (1996), 73–107.
3. E. Bombieri, J. Pila, *Duke Math. J.* **59** (1989), 337–357.
4. J. Pila, "Density of integral and rational points on varieties," *Astérisque* **228** (1995), 183–187.
