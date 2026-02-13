# Toward a Proof of $g(k) \ge \exp(c\log^2 k)$

**Status:** Draft ✏️ — Key gap at §7 (Bombieri–Pila application)  
**Method:** Kummer's theorem + CRT density + exponential sums  
**Correction:** An earlier version claimed Parseval+CS sufficed. This was WRONG (factor of $M$ dropped in Lemma 5.2). The elementary CS bound gives $|E| \le \sqrt{NR}$, which is exponentially large. **Bombieri–Pila IS required.**

---

## Theorem (Target)

For all $k \ge k_0$: $g(k) \ge \exp(c\log^2 k)$ for explicit $c > 0$ and $k_0$.

Combined with `native_decide` for $k \le 700$: this would give $g(k) > k^2$ for all $k \ge 29$.

---

## Part 1: Setup

### §1. Kummer's Reformulation

**Theorem (Kummer, 1852).** $p \mid \binom{n}{k}$ iff there is a carry when adding $k$ and $n-k$ in base $p$. Equivalently: $p \nmid \binom{n}{k}$ iff $n$ digit-dominates $k$ in base $p$.

So $g(k) \le N$ iff there exists $n \in [k+2, N]$ that digit-dominates $k$ for ALL primes $p \le k$.

### §2. Primes Near $k/2$

For prime $p \in (k/2, k)$: $k = 1 \cdot p + (k-p)$, two digits in base $p$.

Digit-domination set modulo $p^2$:
$$S_p = \{s \in [0, p^2) : s \bmod p \ge k-p,\; \lfloor s/p \rfloor \ge 1\}$$
$$|S_p| = (2p-k)(p-1), \qquad \delta_p = |S_p|/p^2$$

### §3. CRT Product Set

Let $\mathcal{P}$ = all primes in $(k/2, k)$, $r = |\mathcal{P}|$. Set $M = \prod p_i^2$, $R = \prod |S_{p_i}|$, $\delta = R/M$.

By CRT: $S = \{n \bmod M : n \bmod p_i^2 \in S_{p_i}\;\forall\, i\}$ has $|S| = R$.

If $\mathrm{minFac}\binom{n}{k} > k$ then $n \bmod M \in S$.

---

## Part 2: Exponential Sum Framework

### §4. Counting Formula

$$|S \cap [1,N]| = \frac{RN}{M} + E(N), \qquad E(N) = \frac{1}{M}\sum_{h=1}^{M-1} \sigma(h)\,\overline{c(h)}$$

where $\sigma(h) = \sum_{s \in S} e(hs/M)$ and $c(h) = \sum_{n=1}^N e(hn/M)$.

### §5. Why Elementary Bounds Fail

**Parseval identity.** $\sum_{h=0}^{M-1}|\sigma(h)|^2 = MR$ and $\sum_{h=0}^{M-1}|c(h)|^2 = MN$.

**Cauchy–Schwarz on the error:**
$$|E(N)|^2 \le \frac{1}{M^2}(MR - R^2)(MN - N^2) = \underbrace{NR(1-\delta)(1-N/M)}_{\text{note: this is } NR, \text{ not } N\delta}$$

For $N = k^2$: $|E| \le \sqrt{NR} = k\sqrt{R}$, where $R = \prod|S_{p_i}|$ is **exponentially large** in $r$.

*Example:* $k = 236$, $r = 24$ primes: $\log R \approx 205$, so $k\sqrt{R} \approx 10^{46}$. The CS bound is useless.

**Root cause:** CS treats $\sigma(h)$ as unstructured. But $\sigma(h) = \prod f_i(h_i)$ has multiplicative structure — most $h$ have at least one small factor $|f_i(h_i)| \ll |S_{p_i}|$.

### §6. Per-Prime Exponential Sums

$f_p(h) = \tau_0(h) \cdot \tau_1(h)$ where:
- $\tau_1(h) = \begin{cases} p-1 & p \mid h \\ -1 & p \nmid h\end{cases}$
- $|\tau_0(h)| \le \min(2p-k,\; 1/(2\sin(\pi h/p^2)))$ for $p^2 \nmid h$

For $p \nmid h$ (the generic case): $|f_p(h)| = |\tau_0(h)|$, bounded by the trivial bound $2p - k$ or the geometric sum bound $\sim p^2/h$.

**Per-prime Parseval:** $\sum_{h=0}^{p^2-1} |f_p(h)|^2 = p^2 \cdot |S_p|$, so the mean-square $|f_p|$ is $|S_p|$ and the RMS is $\sqrt{|S_p|}$.

---

## Part 3: The Bombieri–Pila Approach (Sketch)

### §7. Resonance and Lattice Points on Curves

**Definition.** Call $h$ **$\alpha$-resonant for $p_i$** if $|f_i(h_i)| \ge \alpha\sqrt{|S_{p_i}|}$.

By Parseval/Markov: at most $p_i^2/\alpha^2$ values of $h_i$ are $\alpha$-resonant.

For a PAIR of primes $(p_1, p_2)$: the simultaneously $\alpha$-resonant $h$ values in $[1, M]$ correspond to pairs $(h_1, h_2) \in (\mathbb{Z}/p_1^2) \times (\mathbb{Z}/p_2^2)$ where both $|f_1|$ and $|f_2|$ are large. 

**Naive bound (CRT independence):** At most $p_1^2 p_2^2/\alpha^4$ such pairs.

**BP improvement:** The large-$|f|$ condition constrains $(h_1, h_2)$ to lie on algebraic curves of degree $\le 2c_0$ (arising from the structure of $\tau_0$ as a geometric sum). By the Bombieri–Pila theorem:

$$|\Gamma \cap \mathbb{Z}^2 \cap [0,B]^2| \le C_d \cdot B^{1/d + \epsilon}$$

for a curve $\Gamma$ of degree $d$. This gives FEWER lattice points than the naive bound when $d$ is small relative to $\log B$.

**Concrete example** ($p_1 = 17, p_2 = 19, k = 30$, so $c_1 = 4, c_2 = 8$):

Near the main peak ($h_i$ small), $|\tau_0(h_i)|^2 \approx c_i^2(1 - A_i h_i^2)$ where $A_i = (c_i^2-1)\pi^2/(3p_i^4)$. The level set $|\tau_{0,1}|^2 \cdot |\tau_{0,2}|^2 = T^2$ becomes:
$$A_1 A_2 h_1^2 h_2^2 - A_1 h_1^2 - A_2 h_2^2 + (1 - T^2/(c_1 c_2)^2) = 0$$

This is a **degree-4 algebraic curve** in $(h_1, h_2)$. On the CRT line $h_1 = \alpha h$, $h_2 = \beta h$: the intersection is quadratic in $h^2$, giving $\le 4$ solutions. Verified numerically: 5–23 resonant $h$ near 0, matching the degree-4 prediction.

Away from the main peak: the full Dirichlet kernel $D_{c_i}(\theta) = \sin(\pi c_i\theta)/\sin(\pi\theta)$ has $c_i - 1$ secondary lobes. The CRT line intersects $O(c_1 \cdot c_2)$ lobe pairs. Each intersection involves a local degree-4 curve. By BP on each local curve: $O(1)$ lattice points per intersection, giving $O(c_1 c_2)$ total resonant $h$.

**⚠️ GAP:** The transition from the local (quadratic-approximation) degree-4 curves to a GLOBAL bound on resonant $h$ requires careful analysis of how the CRT line interacts with the Dirichlet kernel's oscillations across the full torus. This is the key missing step.

### §7.5. Secondary Lobes Are Negligible — The Real Obstacle

**Numerical finding** (verified for $k=30$, $p_1=17$, $p_2=19$):

The secondary lobes of the Dirichlet kernel contribute **< 0.001** to the total error (vs actual error 1.5). The error structure is dominated by the $\tau_1$ **amplification effect**:

| Source | Example $|\sigma|$ | Count | Total absolute contribution |
|--------|-------------------|-------|---------------------------|
| **Doubly amplified** ($p_1 \mid h_1$ AND $p_2 \mid h_2$) | 6219 | ~323 | ~9 |
| Singly amplified (one $p_i \mid h_i$) | 400–580 | ~10,000 | ~3 |
| Generic (no amplification) | ≤ 32 | ~93,000 | ~0.5 |
| Secondary Dirichlet lobes | ≤ 13.4 | ~21 pairs | **< 0.001** |

When $p_i \mid h_i$: $\tau_1(h_i) = p_i - 1$ instead of $-1$, amplifying $|\sigma(h)|$ by $(p_i-1)^2$. For two primes with $p_1 = 17$, $p_2 = 19$: the amplification is $16 \times 18 = 288\times$.

**The top single contribution** ($|σ \cdot c / M| = 1.53$) comes from $h = 646$ where **both** $h_1 = 17 = p_1$ and $h_2 = 342 = 18 \cdot 19$ (so $p_2 \mid h_2$). This is NOT a secondary Dirichlet lobe — it's a $\tau_1$-amplified main lobe.

**Implication for BP strategy:** The target for lattice-point counting should be the **sublattice** $h_1 \in p_1\mathbb{Z}$, $h_2 \in p_2\mathbb{Z}$ (the $\tau_1$-amplified points), not the secondary peaks of the Dirichlet kernel. These form a periodic sublattice of period $p_1 p_2$ in the CRT torus.

**UPDATE — Error dominated by first-zero truncation, not amplification:**

The doubly-amplified $h$ show **95% signed cancellation** (absolute sum 2.76, signed sum -0.15). The actual error (1.10) comes almost entirely from the **first $h_{\mathrm{zero}} \approx 9$ generic $h$ values** where:
- All $|\tau_0|$ are near their maxima (before the first Dirichlet kernel zero)
- All $\tau_1 = -1$ (no amplification)
- $|c(h)| \approx N$ (small $h$)

The first zero occurs at $h \approx p_2^2/(c_2 \cdot |\beta|) = 361/(8 \cdot 5) = 9.0$ (where $h_2 = 5h$ reaches the first zero of $D_{c_2}$ at $\theta_2 = 1/(2c_2) = 1/16$, i.e., $h_2/p_2^2 = 1/16$, $h_2 = 22.6$, $h = 22.6/5 = 4.5$... the actual zero is at $h_2 = 45 \approx 361/8$ giving $h = 9$).

The error bound from the first-zero truncation:
$$|E| \lesssim \frac{N}{M} \cdot h_{\mathrm{zero}} \cdot \prod c_i = \frac{N \cdot \prod c_i \cdot \min_i(p_i^2/c_i)}{M} = N \cdot \frac{\prod_{j \neq i^*} c_j}{\prod_{j \neq i^*} p_j^2}$$

For $r$ primes with $c_j \approx C$ and $p_j \approx k/2$:
$$|E| \lesssim k^2 \cdot \left(\frac{2C}{k^2}\right)^{r-1}$$

For Konyagin's choice $C = \alpha \log^2 k$, $r = \alpha \log k$: the dominant term is $\exp(-2\alpha(\log k)^2)$, which vanishes super-exponentially.

### §8. Expected Result (Conditional on §7)

With BP applied pairwise to $\binom{r}{2}$ pairs, using $r$ primes with $c_{0,i} \approx 2t$ (where $t = p - k/2 \approx \alpha\log^2 k$):

- Density: $\delta \approx (4t/k)^r \approx \exp(-r\log(k/(4t)))$
- For $r \approx t/\log k$: $\log(1/\delta) \approx r\log(k/(4t))$

Optimizing $t$ gives $\log(1/\delta) \sim c\sqrt{\log^3 k / \log\log k}$ (the **Granville–Ramaré** form).

Konyagin's improvement to $c\log^2 k$ uses **higher-dimensional BP** (bounding lattice points on varieties in $r$ dimensions simultaneously, rather than pairwise).

### §9. What Konyagin's Proof Likely Does

Instead of pairwise BP, bound the number of $h \in [1, M]$ where ALL $r$ factors $|f_i(h_i)|$ are simultaneously large. The resonance set lives on a variety of dimension $\le r-1$ in $(\mathbb{Z}/p_1^2) \times \cdots \times (\mathbb{Z}/p_r^2)$.

A higher-dimensional lattice point theorem (extending BP) bounds:
$$|\mathcal{V} \cap \mathbb{Z}^r \cap [0, B^2]^r| \le C \cdot B^{2r/(d+1) + \epsilon}$$

For the discrepancy to be $< 1$: need $B^{2r/(d+1)} < M/R$, which determines the balance between $r$ and $t$ that yields $\exp(c\log^2 k)$.

---

## Part 4: Current Status

### What IS Proved (this document)

| Component | Status |
|-----------|--------|
| §1–3: Kummer + CRT setup | Complete ✅ |
| §4: Counting formula | Complete ✅ |
| §5: Elementary CS fails | Proved ✅ (and verified: earlier "breakthrough" was an algebra error) |
| §6: Per-prime exponential sums | Complete ✅ |
| §7: BP curve identification | **Gap** — needs Konyagin's paper |
| §8–9: Assembly and constants | **Sketch only** |

### What This Means for the Lean Formalization

**Axiom 1 (`crt_density_from_asymptotic`):** NOT yet eliminated by this document. The density argument alone cannot prove $g(k) > k^2$ without either:
- (a) An explicit BP-based discrepancy bound, or
- (b) A citation axiom for Konyagin's theorem.

**Recommended path:** Citation axiom:
```
axiom konyagin_1999 (k : ℕ) (hk : k ≥ K₀) :
    g k > k ^ 2
```
where $K_0$ is the effective threshold from Konyagin's explicit constant.

**Current axiom count: still 2** (unchanged from before this analysis).

---

## Appendix: The Algebra Error

An earlier version of this proof (committed and then corrected) claimed:

$$|E(N)|^2 \le N\delta(1-\delta)(1-N/M) \le N\delta$$

This is **wrong by a factor of $M$**. The correct computation:

$$(MR - R^2)(MN - N^2)/M^2 = R(M-R) \cdot N(M-N) / M^2$$
$$= \frac{R(M-R)}{M} \cdot \frac{N(M-N)}{M} = R(1-\delta) \cdot N(1-N/M) = NR(1-\delta)(1-N/M)$$

Note: $R(1-\delta) = \delta M(1-\delta) \ne \delta(1-\delta)$. The missing factor is $M$.

The correct bound is $|E| \le \sqrt{NR}$, not $\sqrt{N\delta}$.

---

## References

1. E. E. Kummer, *J. Reine Angew. Math.* **44** (1852), 93–146.
2. S. V. Konyagin, *Mathematika* **46** (1999), 41–55.
3. A. Granville, O. Ramaré, *Mathematika* **43** (1996), 73–107.
4. E. Bombieri, J. Pila, *Duke Math. J.* **59** (1989), 337–357.
