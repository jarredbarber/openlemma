# Finiteness of the Exceptional Set via Konyagin's Theorem

**Status:** Draft ✏️  
**Dependencies:** Konyagin (1999), IDL (Verified ✅), PNT (Dickman estimates), CRT density  
**Confidence:** High (Part 1), Exploratory (Part 2)

---

# Part 1: Nonconstructive Finiteness Proof

## 1.1 Citation Axiom

**Theorem (Konyagin, 1999).** *There exists an absolute constant $c > 0$ such that for all $k \ge 2$:*
$$g(k) \ge \exp(c \log^2 k)$$
*where $g(k)$ is the least integer $n > k+1$ with $\mathrm{minFac}\binom{n}{k} > k$.*

**Source:** S. V. Konyagin, "Estimates of the least prime factor of a binomial coefficient," *Mathematika* **46** (1999), no. 1, 41–55.

**What this means:** For ALL $n \in \{k+2, k+3, \ldots, g(k)-1\}$: some prime $p \le k$ divides $\binom{n}{k}$.

## 1.2 Threshold

Since $\exp(c\log^2 k)/(2k^2) = \exp(c\log^2 k - 2\log k - \log 2) \to \infty$, there exists $K_1$ with:

$$\forall\, k > K_1:\quad g(k) > 2k^2. \tag{$\star$}$$

We fix $K_1$ but never compute it.

## 1.3 Analysis of $E_k$ for $k > K_1$

**Notation.** $E_k = \{n \ge 2k : \mathrm{minFac}\binom{n}{k} > \max(\lfloor n/k\rfloor, k)\}$.

We split by $n$.

### Range I: $n \le 2k^2$

Since $g(k) > 2k^2$: all $n \le 2k^2$ satisfy $n < g(k)$, so $\mathrm{minFac}\binom{n}{k} \le k$.

- For $n \le k^2$: $\max(n/k, k) = k$. So $\mathrm{minFac} \le k = \max$. Not in $E$. ✓
- For $n \in (k^2, 2k^2]$: $\max(n/k, k) = n/k > k$. So $\mathrm{minFac} \le k < n/k$. Not in $E$. ✓

### Range II: $n > 2k^2$

Here $M := \lfloor n/k\rfloor > 2k$ and $\max = M$. We need $\mathrm{minFac}\binom{n}{k} \le M$.

**Type A: $M$ has a prime factor $p > k$.** Then $p \le M$, $p \mid M$. By the IDL: $n \bmod p < k$, so $p \mid \binom{n}{k}$. Hence $\mathrm{minFac} \le p \le M$. ✓

**Type B: $M$ is $k$-smooth.** Since $g(k) > 2k^2$ and $M > 2k$: $n = kM + r > 2k^2$. If $n < g(k)$: $\mathrm{minFac} \le k \le M$ (since $M > k$). ✓

For $n \ge g(k)$: we use the **medium-prime argument**. Among the $k-1$ integers $m \in \{n-k+1, \ldots, n-1\}$, consider their prime factorizations. Each composite $m$ with a prime factor $q \in (k, \sqrt{n}\,]$ satisfies $q \mid \binom{n}{k}$ (since $q > k \Rightarrow q \nmid k!$ and $q \mid m$ with $m \in (n-k, n]$). And $q \le \sqrt{n} \le \sqrt{kM} \le M$ (since $k \le M$). So $\mathrm{minFac} \le q \le M$. ✓

An integer $m > k^2$ can only LACK a prime factor in $(k, \sqrt{m}\,]$ if all its prime factors are either $\le k$ or $> \sqrt{m}$ — i.e., $m = A \cdot B$ with $A$ being $k$-smooth and $B$ being $\sqrt{m}$-rough ($B = 1$ or $B$ prime $> \sqrt{m}$). By the prime number theorem applied to short intervals, the count of such $m$ in any interval of length $k$ is bounded by:

$$\underbrace{\text{($k$-smooth $m$)}}_{\le\, k \cdot \rho(\log n / \log k)} + \underbrace{\text{($m = Ap$, $A$ $k$-smooth, $p > \sqrt{n}$)}}_{\le\, \sum_{A\, k\text{-smooth}} \frac{2k}{A \ln(n/A)}}$$

**Bound on term 2.** For $A \le \sqrt{n}$ ($k$-smooth): $\ln(n/A) \ge \tfrac{1}{2}\ln n$. By Mertens: $\sum_{A\, k\text{-smooth}} 1/A = \prod_{p \le k}(1-1/p)^{-1} \le e^\gamma \ln k + O(1)$. So:

$$\text{Term 2} \le \frac{4k\,(e^\gamma \ln k + 1)}{\ln n}$$

**Bound on term 1.** By Dickman: for $n > k^{2k}$, $\rho(\log n / \log k) \le \rho(2k) < 1/(2k)$, so term 1 $< 1/2$.

**Combined.** For $\ln n > 8k(e^\gamma \ln k + 1) + 1$, i.e., $n > n_0(k) := \exp(15k\ln k)$: total count $< 1$. So every $m \in (n-k, n]$ has a medium prime. ✓

**The gap: $g(k) \le n \le n_0(k)$ with $k$-smooth $M$.**

For $k > K_1$: $g(k) \ge \exp(c\log^2 k)$. The gap $[g(k), n_0(k)]$ is enormous — $n_0(k) = \exp(15k\ln k)$ dwarfs $g(k) = \exp(c\log^2 k)$ for large $k$. Within this gap, $k$-smooth values of $M$ exist (e.g., powers of 2), so Type B pairs $(kM+r, k)$ arise.

**Expected count.** The count of exceptions in the gap is at most $k \cdot \Psi(n_0(k)/k, k) \cdot \delta_k$, where $\Psi$ counts $k$-smooth integers. By Dickman with $u = 15k-1$:

$$\Psi(n_0(k)/k,\, k) \approx \frac{n_0(k)}{k} \cdot \rho(15k) = \frac{\exp(-O(k))}{k}$$

So the expected count $\le \exp(-O(k))/k^2 < 1$ for all $k \ge 1$.

**⚠️ HONEST ASSESSMENT:** Expected count $< 1$ does NOT prove actual count $= 0$. The CRT density $\delta_k$ bounds the fraction of $n$ satisfying digit domination, but this is a density statement, not a deterministic one. Going from "expected $< 1$" to "count $= 0$" requires either:

1. **An explicit Konyagin constant** $c$ large enough that $g(k) > n_0(k)$ (impossible: $\exp(c\log^2 k) < \exp(15k\ln k)$ for all large $k$), OR
2. **An explicit Konyagin constant** $c$ with $g(k) > k^2$ so that the Lean axiom `crt_density_from_asymptotic` handles $[2k, k^2]$ and no gap remains, OR
3. **A direct proof** that for $n \ge g(k)$ with $k$-smooth $M$, some prime $\le M$ divides $\binom{n}{k}$ (this is exactly axiom `large_n_smooth_case`).

**Conclusion for §1.3:** We CANNOT prove $E_k = \emptyset$ for large $k$ using Konyagin alone, without either an explicit constant or the smooth-case axiom. $\square$

## 1.4 What IS Proved: $E_k$ is Finite for Each Fixed $k$

**Theorem.** *For each fixed $k \ge 2$: $E_k$ is finite.*

*Proof.* By the medium-prime argument (§1.3, Range II): for $n > n_0(k) = \exp(15k\ln k)$, every $m \in (n-k, n]$ has a prime factor $q \in (k, \sqrt{n}\,]$. Since $q > k$: $q \mid \binom{n}{k}$, and $q \le \sqrt{n} \le n/k$ (for $n > k^2$). So $\mathrm{minFac} \le n/k = \max$. Not in $E$.

Therefore $E_k \subseteq [2k,\, n_0(k)]$. This is a bounded interval of integers, hence finite. $\square$

**This is unconditional** — no axioms needed. PNT + Dickman are classical.

## 1.5 What is NOT Proved: $E_k = \emptyset$ for Large $k$

The proof in §1.3 shows:
- **Range I** ($n \le 2k^2$): $E_k \cap [2k, 2k^2] = \emptyset$ for $k > K_1$. ✓ (Konyagin)
- **Range II, Type A**: Handled by IDL. ✓
- **Range II, Type B, $n < g(k)$**: $\mathrm{minFac} \le k$. ✓
- **Range II, Type B, $n \ge g(k)$, $n > n_0(k)$**: Medium-prime. ✓
- **Range II, Type B, $g(k) \le n \le n_0(k)$**: ⚠️ **OPEN GAP**

To close the gap and prove $E_k = \emptyset$, we need ONE of:

| Path | What's needed | Closes gap? | Axiom count |
|------|--------------|-------------|-------------|
| A: Explicit Konyagin | $c$ effective, $g(k) > k^2$ computable | No (only [2k, k²]) | 1 (smooth case) |
| B: Smooth-case axiom | `large_n_smooth_case` | Yes (all $n > k^2$) | 1 (+ Konyagin citation) |
| C: Direct argument | Prove smooth case analytically | Yes | 0 (if combined with A) |

## 1.6 Conclusion: Two Tiers

**Tier 1 (Unconditional):** $E_k$ is finite for each $k$. Therefore $E$ is finite iff only finitely many $k$ have $E_k \ne \emptyset$. *Proved by medium-prime argument alone.*

**Tier 2 (Conditional):** $E_k = \emptyset$ for $k > K_1$, hence $|E| < \infty$. *Requires closing the gap via Path A, B, or C above.*

$$E = \bigcup_{k=1}^{\infty} \{k\} \times E_k$$

- **Path A** (explicit $c$, $g(k) > k^2$ for $k > K_0$): Eliminates axiom 1 (`crt_density_from_asymptotic`) — Konyagin directly proves no $n \in [2k, k^2]$ is $k$-rough. Combined with `native_decide` for $k \le K_0$. But axiom 2 (`large_n_smooth_case`) still needed for $n > k^2$. **1 axiom + 1 citation.**
- **Path B** (smooth-case axiom): $E_k \subseteq [2k, k^2]$ for all $k$. Konyagin (nonconstructive) gives $E_k = \emptyset$ for $k > K_1$. **1 axiom** (smooth case) + **1 citation** (Konyagin).
- **Current Lean:** **2 axioms** (`crt_density_from_asymptotic` + `large_n_smooth_case`).
- **0 axioms:** Requires explicit $c$ (Path A) AND proving `large_n_smooth_case` analytically or reducing $n_0(k)$ to a computationally feasible range. Both are open.

## 1.7 What This Proof Uses

| Input | Role | Status |
|-------|------|--------|
| Medium-prime (PNT + Dickman) | $E_k \subseteq [2k, n_0(k)]$, hence finite | Classical ✅ |
| Konyagin: $g(k) \ge \exp(c\log^2 k)$ | $E_k \cap [2k, 2k^2] = \emptyset$ for $k > K_1$ | Citation |
| IDL (Type A) | Handles $n > k^2$ when $n/k$ has large prime | Verified ✅ |
| **Gap:** $g(k) \le n \le n_0(k)$, smooth $M$ | Requires Path A, B, or C | **Open** |

---

# Part 2: Toward an Explicit Constant

## 2.1 Why It Matters

If we can extract an explicit $c$ from Konyagin's proof, then:
- $K_0$ becomes computable: solve $\exp(c\log^2 k) > k^2$.
- For $k > K_0$: Konyagin directly proves $g(k) > k^2$, eliminating axiom 1 (`crt_density_from_asymptotic`).
- For $k \le K_0$: extend `native_decide` or external computation to cover $[2k, k^2]$.
- **Result: 1 axiom** (smooth-case only). Down from 2.

| Explicit $c$ | $K_0$ threshold | Verification method |
|:---:|:---:|:---|
| $\ge 0.5$ | $\approx 75$ | Already covered by `native_decide` (k ≤ 700) |
| $\ge 0.25$ | $\approx 4{,}200$ | Moderate computation extension |
| $\ge 0.1$ | $\approx 7 \times 10^8$ | External CRT algorithm |
| $\ge 0.05$ | $\approx 4 \times 10^{17}$ | Infeasible |

**Note:** The smooth-case axiom (`large_n_smooth_case`) remains regardless of $c$. It handles $n > k^2$ with $k$-smooth $M$ — a structural requirement independent of $g(k)$.

**Empirical evidence:** From known $g(k)$ values (OEIS A003458, Sorenson 2019), the empirical constant $c_{\text{emp}}(k) = \log g(k) / \log^2 k$ ranges from $0.51$ (at $k = 28$, the last known exception) to $1.6$. For $k \ge 29$: $c_{\text{emp}} \ge 0.67$, giving $K_0 \le 20$. Even a theoretical $c = 0.5$ would give $K_0 \approx 75$, well within `native_decide` range.

## 2.2 Konyagin's Method: Overview

The proof of $g(k) \ge \exp(c\log^2 k)$ proceeds in three stages:

**Stage 1: Reformulation.** $g(k) > N$ iff every $n \in [k+2, N]$ has some prime $p \le k$ with $p \mid \binom{n}{k}$. By Kummer: $p \mid \binom{n}{k}$ iff there is a carry when adding $k$ and $n-k$ in base $p$. So $g(k) \le N$ iff there exists $n \le N$ with NO carry in base $p$ for ALL primes $p \le k$.

**Stage 2: Counting via exponential sums.** The set of "carry-free" $n$ modulo $M_k = \prod_{p \le k} p^{L_p}$ forms a product set $S_k \subset \mathbb{Z}/M_k\mathbb{Z}$ via CRT. Konyagin bounds the discrepancy of $S_k$ in short intervals using exponential sums that factor over primes.

**Stage 3: The key bound.** By carefully choosing which primes to exploit (specifically, primes in $(k^{1-\varepsilon}, k]$ for a suitable $\varepsilon$), and using the Bombieri–Pila bound for lattice points on curves, Konyagin shows that $S_k \cap [1, N] = \emptyset$ for $N = \exp(c\log^2 k)$.

## 2.3 Stage 2 in Detail: The Exponential Sum Framework

### The discrepancy problem

Let $S_p \subset \{0, 1, \ldots, p^{L_p}-1\}$ be the set of residues satisfying digit domination in base $p$. By CRT:
$$S_k = \{n \bmod M_k : n \bmod p^{L_p} \in S_p\ \forall\ p \le k\}$$

The cardinality $|S_k| = R_k = \prod_{p \le k} |S_p|$ and the density is $\delta_k = R_k / M_k$.

The number of elements of $S_k$ in an interval $[a, a+H]$ is:
$$\mathcal{N}(a, H) = \frac{R_k}{M_k} \cdot H + E(a, H)$$

where $E$ is the error (discrepancy). We want $\mathcal{N}(k+2, N) = 0$, which requires:
$$|E| > \delta_k \cdot N, \quad\text{i.e.,}\quad N < |E| / \delta_k.$$

Wait — that's backwards. We want $\mathcal{N} = 0$, so $\delta_k N + E < 1$, meaning $E < 1 - \delta_k N$. For $N > 1/\delta_k$: we need $E < 0$ (the elements are pushed AWAY from short intervals).

### Exponential sum representation

By the Erdős–Turán inequality:
$$|E(a, H)| \le \sum_{h=1}^{T} \frac{1}{h} \left|\sum_{s \in S_k} e(hs/M_k)\right| + O(R_k / T)$$

The inner sum factors via CRT:
$$\sum_{s \in S_k} e(hs/M_k) = \prod_{p \le k} \sigma_p(h_p)$$

where $h_p \equiv h \cdot (M_k/p^{L_p})^{-1} \pmod{p^{L_p}}$ and:
$$\sigma_p(h_p) = \sum_{s_p \in S_p} e(h_p s_p / p^{L_p})$$

### Per-prime exponential sums

The set $S_p$ has **product structure** across digit positions. Write $s_p = \sum_{j=0}^{L_p-1} d_j p^j$ with $d_j \ge a_j$ where $a_j = d_j^{(p)}(k)$ (the $j$-th digit of $k$ in base $p$). Then:

$$\sigma_p(h_p) = \prod_{j=0}^{L_p-1} \underbrace{\sum_{d=a_j}^{p-1} e(h_p d p^j / p^{L_p})}_{=: \tau_{p,j}(h_p)}$$

Each factor $\tau_{p,j}$ is a geometric sum:
$$\tau_{p,j}(h_p) = \sum_{d=a_j}^{p-1} e(h_p d / p^{L_p-j}) = e(h_p a_j / p^{L_p-j}) \cdot \frac{1 - e(h_p(p - a_j)/p^{L_p-j})}{1 - e(h_p / p^{L_p-j})}$$

**Trivial bound:** $|\tau_{p,j}| \le p - a_j$.

**Cancellation bound:** For $p^{L_p-j} \nmid h_p$:
$$|\tau_{p,j}(h_p)| \le \frac{1}{|\sin(\pi h_p / p^{L_p-j})|}$$

In particular, for $\gcd(h_p, p^{L_p-j}) = 1$: $|\tau_{p,j}| \le 1/(2\|h_p/p^{L_p-j}\|)$ where $\|\cdot\|$ is the distance to the nearest integer.

## 2.4 Stage 3: Where the Bound Comes From

### Primes near $k$

For a prime $p \in (k/2, k)$: $k$ has exactly $L_p = 2$ digits in base $p$. Specifically $k = 1 \cdot p + (k-p)$ with $a_0 = k-p \in [1, p/2)$ and $a_1 = 1$.

The density contribution from this prime is:
$$\frac{|S_p|}{p^2} = \frac{(p - a_0)(p - 1)}{p^2} = \frac{(2p-k)(p-1)}{p^2}$$

For $p$ near $k/2$: this is $\approx 2/k$. For $p$ near $k$: this is $\approx (p-1)/p \approx 1$.

The product over primes in $(k/2, k)$:
$$\prod_{k/2 < p \le k} \frac{(2p-k)(p-1)}{p^2} \approx \exp\left(-\frac{k\ln 2}{2\ln k}\right)$$

(Computed by converting the sum $\sum_p \log((2p-k)/p)$ to an integral via PNT.)

### Discrepancy from primes near $k$

For these primes: $L_p = 2$, so $\sigma_p(h_p)$ involves a product of two geometric sums. The cancellation in $\tau_{p,0}$ depends on $h_p \bmod p^2$.

**Key observation (Konyagin).** The exponential sums $\sigma_p(h_p)$ for primes $p \in (k/2, k)$ exhibit cancellation that COMPOUNDS multiplicatively across primes. The number of "bad" $h$ values (those giving large $|\sigma_p|$ for many primes simultaneously) is bounded by lattice-point counting on algebraic curves.

### Why elementary methods fail

The CRT density from $r$ primes near $k/2$ is $\delta \approx (2/k)^r$. For $r = 3$ and $N = k^2$: the expected count $E = \delta \cdot k^2 \approx 8/k < 1$. But the **discrepancy** (difference between actual and expected count) dominates.

**Elementary discrepancy** (Parseval + Cauchy–Schwarz): $D \le \sqrt{R \cdot \log M}$ where $R = |S_k|$ and $M$ is the CRT modulus. For 3 primes: $D \approx k^{3/2}\sqrt{\log k} \gg 1$. The density gain ($E < 1$) is completely wiped out by the error.

**Root cause:** The exponential sum $\sum_{s \in S_k} e(hs/M)$ has $R$ terms. The mean-square bound (Parseval) gives $\sqrt{R}$, but $\sqrt{R} \gg k^2$ for 3 primes. The elementary approach cannot prove $g(k) > k^2$.

This is the fundamental reason why Konyagin needs a non-trivial tool.

### The Bombieri–Pila connection

The condition $|\sigma_p(h_p)| \ge \alpha |S_p|$ for multiple primes $p_1, \ldots, p_r$ simultaneously imposes constraints on $h \bmod p_1^2 \cdots p_r^2$. These constraints define algebraic curves in $(\mathbb{Z}/p_i^2)^r$, and the number of lattice points is bounded by the Bombieri–Pila theorem.

**Bombieri–Pila (1989).** *The number of integer points on a plane curve of degree $d$ inside a box of side $N$ is $O_{d,\varepsilon}(N^{1/d+\varepsilon})$.*

This limits how many $h$ values can simultaneously satisfy the "bad" conditions for $r$ primes. As $r$ grows (more primes in $(k/2, k)$ are used): the constraint tightens, the discrepancy improves, and $g(k)$ is pushed higher.

### Why $\exp(c\log^2 k)$

The number of primes in $(k/2, k)$ is $r \approx k/(2\ln k)$ by PNT. Each contributes a density factor $\approx 2/k$ (for primes near $k/2$). The naive density is:
$$\delta_{\text{near}} \approx (2/k)^r \approx \exp(-r \ln(k/2)) \approx \exp\left(-\frac{k \ln k}{2\ln k}\right) = \exp(-k/2)$$

But we can't use all $r$ primes simultaneously (Bombieri–Pila limits how many constraints can be combined). Using $r' = c'\log k$ primes (optimally chosen): the density becomes:
$$\delta' \approx (2/k)^{c'\log k} = \exp(-c'\log k \cdot \log(k/2)) = \exp(-c'\log^2 k + O(\log k))$$

So $g(k) \ge 1/\delta' \ge \exp(c\log^2 k)$ with $c = c' - o(1)$.

The constant $c'$ depends on:
- The exponent in Bombieri–Pila ($1/d$ for degree-$d$ curves).
- The degree of the algebraic curves arising from the exponential sum constraints.
- The optimization over which subset of primes to use.

## 2.5 Extracting an Explicit $c$

### What's needed

1. **Identify the curves.** For two primes $p_1, p_2 \in (k/2, k)$: the constraint $|\sigma_{p_i}(h_{p_i})| \ge \alpha |S_{p_i}|$ for $i = 1, 2$ defines a subset of $\mathbb{Z}/p_1^2 \times \mathbb{Z}/p_2^2$. Identify the algebraic curves these constraints lie on.

2. **Degree bound.** Determine the degree $d$ of these curves. For geometric sums: the condition $|\tau_{p,j}| \ge \alpha(p-a_j)$ constrains $h_p/p^{L_p-j}$ to lie near a rational with small denominator. This is a Diophantine condition of bounded degree.

3. **Apply Bombieri–Pila with explicit constants.** The original Bombieri–Pila bound has an effective implied constant. Several authors have made it explicit:
   - Pila (1995): explicit bounds for rational curves.
   - Walsh (2015): explicit bounds for arbitrary plane curves.
   - Bilu–Parent (2011): effective Chabauty-type bounds.

4. **Optimize.** Choose $r'$ (number of primes used) to maximize $g(k)$. The optimal $r'$ balances the density gain from more primes against the Bombieri–Pila penalty.

### Estimated constants

Based on the structure of the argument:
- The curves arising from two-prime constraints are of degree $d \le 4$ (from the structure of geometric sums in two variables).
- Bombieri–Pila gives $O(N^{1/4+\varepsilon})$ lattice points for degree-4 curves.
- Using $r' = (1/8)\log k$ primes: $\delta' \approx \exp(-(1/8)\log^2 k)$.
- Adjusting for Bombieri–Pila losses: $c \approx 1/16$.

**Very rough estimate:** $c = 1/16$ gives $K_1 \approx \exp(\sqrt{32/c}) = \exp(16\sqrt{2}) \approx \exp(22.6) \approx 6.5 \times 10^9$.

This is FAR too large for `native_decide`. But with more careful analysis of the geometric sum structure, $c$ could be larger (perhaps $c \ge 1/4$), giving $K_1 \approx \exp(4) \approx 55$, which would be within computational range.

### Alternative: Simpler proofs of weaker bounds

If the full Konyagin reconstruction is too complex, a SIMPLER argument might suffice:

**Granville–Ramaré (1996)** proves $g(k) \ge \exp(c\sqrt{\log^3 k / \log\log k})$. This is weaker than Konyagin but does NOT use Bombieri–Pila — it uses elementary exponential sum estimates. If this bound can be made explicit with $c$ large enough that $\exp(c\sqrt{\log^3 k / \log\log k}) > k^2$ for $k > K_0$ with $K_0$ small: it would suffice.

**Required:** $c\sqrt{\log^3 k / \log\log k} > 2\log k$, i.e., $c > 2\sqrt{\log\log k / \log k}$. For $k = 1000$: $c > 2\sqrt{1.93/6.9} \approx 1.06$. So $c > 1.1$ would handle $k > 1000$.

## 2.6 The Reconstruction Roadmap

| Step | Task | Difficulty | Payoff |
|------|------|-----------|--------|
| 1 | Formalize the CRT product structure of $S_k$ | Medium | Foundation |
| 2 | Implement per-prime exponential sums $\sigma_p$ | Medium | Key computation |
| 3 | Prove cancellation in $\sigma_p$ for primes near $k$ | Hard | The crux |
| 4 | Bound lattice points on the constraint curves | Hard | Bombieri–Pila |
| 5 | Optimize and extract explicit $c$ | Medium | The prize |
| Alt | Explicit Granville–Ramaré (simpler, weaker) | Medium | Fallback |

### Priority recommendation

**Start with Granville–Ramaré.** Their method is elementary (no algebraic geometry) and the paper is more accessible (31 pages, published in *Mathematika* 43). Making their constant explicit is a realistic goal and would give a weaker but sufficient bound.

**Then attempt Konyagin** if the GR constant isn't good enough (i.e., if $K_0$ from GR is too large for computation).

## 2.7 Effectivity Analysis

### Konyagin's references (from Cambridge Core)

| # | Reference | Effective? | Role in proof |
|---|-----------|-----------|---------------|
| 2 | Bombieri–Pila (1989) | ✅ Yes | Lattice points on curves |
| 5 | Filaseta–Trifonov (1996) | ✅ Yes | Fractional part distribution |
| 6 | Granville–Ramaré (1996) | ✅ Yes | Prior bound (superseded) |
| 7 | Huxley–Trifonov (1996) | ✅ Yes | Squarefull numbers |
| 9 | Schmidt (1991) | ⚠️ Unclear | Diophantine approximation |
| 10 | Swinnerton-Dyer (1974) | ✅ Yes | Lattice points on curves |

**Key observation:** All the analytic tools (Bombieri–Pila, Filaseta–Trifonov, Swinnerton-Dyer) are **effective** — they give explicit bounds with computable constants. The only potential source of ineffectivity is Schmidt's *Diophantine Approximation and Diophantine Equations* (reference 9), which contains both effective and ineffective results.

**Hypothesis:** Konyagin's constant $c$ is **effective** (computable). The claim of "ineffectivity" in earlier discussions may have been premature. The key methods — exponential sum estimates and lattice point counting — are all effective. Whether $c$ is merely "not computed" vs "not computable" requires reading the full paper.

**If $c$ is effective:** Axiom 1 can be eliminated. Extract $c$ → compute $K_0$ → verify $k \le K_0$ computationally → axiom 1 gone. The smooth-case axiom (axiom 2) would remain as the sole axiom.

**If $c$ is ineffective** (uses Schmidt's Thue–Siegel–Roth): Fall back to Granville–Ramaré, which is definitely effective (elementary exponential sums only).

**Action item:** Obtain Konyagin's full paper and check whether reference 9 (Schmidt) is used in the main theorem or only in auxiliary results. This is the single most impactful question for the project.

---

## References

1. S. V. Konyagin, "Estimates of the least prime factor of a binomial coefficient," *Mathematika* **46** (1999), no. 1, 41–55.
2. A. Granville, O. Ramaré, "Explicit bounds on exponential sums and the scarcity of squarefree binomial coefficients," *Mathematika* **43** (1996), 73–107.
3. P. Erdős, C. B. Lacampagne, J. L. Selfridge, "Estimates of the least prime factor of a binomial coefficient," *Math. Comp.* **61** (1993), no. 203, 215–224.
4. E. Bombieri, J. Pila, "The number of integral points on arcs and ovals," *Duke Math. J.* **59** (1989), no. 2, 337–357.
5. J. Sorenson, "Computing the least prime factor of a binomial coefficient," arXiv:1907.08559, 2019.
