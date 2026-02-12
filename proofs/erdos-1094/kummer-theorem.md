# Kummer's Theorem (p-adic valuation of binomial coefficients)

**Status:** Verified ✅  
**Reviewed by:** erdos1094-nii  
**Statement:** Let $p$ be a prime and let $n, k$ be non-negative integers with $n \geq k$. Then:

$$v_p\!\left(\binom{n}{k}\right) = \text{(number of carries when adding } k \text{ and } n - k \text{ in base } p\text{)}.$$

Equivalently:

$$v_p\!\left(\binom{n}{k}\right) = \frac{s_p(k) + s_p(n-k) - s_p(n)}{p - 1}$$

where $s_p(m)$ denotes the sum of the base-$p$ digits of $m$.

**Corollary (Digit-domination criterion):** $p \nmid \binom{n}{k}$ if and only if every base-$p$ digit of $k$ is $\leq$ the corresponding base-$p$ digit of $n$.

**Dependencies:** None  
**Confidence:** Certain

---

## Definitions and Notation

Throughout, $p$ denotes a fixed prime. For a positive integer $m$, we write $v_p(m)$ for the $p$-adic valuation of $m$, i.e., the largest exponent $e \geq 0$ such that $p^e \mid m$. We set $v_p(0) = +\infty$ by convention.

For a non-negative integer $m$, its **base-$p$ representation** is the unique sequence of digits $(d_0, d_1, d_2, \ldots)$ with $0 \leq d_j \leq p - 1$ for all $j$, only finitely many $d_j \neq 0$, and

$$m = \sum_{j=0}^{\infty} d_j \, p^j.$$

We write $\mathrm{dig}_j^{(p)}(m) = d_j$ for the $j$-th digit, and

$$s_p(m) = \sum_{j=0}^{\infty} d_j$$

for the **digit sum** of $m$ in base $p$. (The sum is finite since only finitely many $d_j$ are nonzero.)

---

## Part 1: Legendre's Formula

**Lemma 1 (Legendre's formula).** *For every non-negative integer $m$ and every prime $p$:*

$$v_p(m!) = \sum_{i=1}^{\infty} \left\lfloor \frac{m}{p^i} \right\rfloor.$$

*(The sum is finite: $\lfloor m/p^i \rfloor = 0$ for $p^i > m$.)*

### Proof of Lemma 1

We count the total multiplicity of $p$ in the prime factorization of $m! = 1 \cdot 2 \cdots m$.

$$v_p(m!) = \sum_{j=1}^{m} v_p(j).$$

Now, $v_p(j) \geq i$ if and only if $p^i \mid j$. Therefore:

$$v_p(j) = \sum_{i=1}^{\infty} \mathbf{1}[p^i \mid j]$$

where $\mathbf{1}[\cdot]$ is the indicator function. Substituting:

$$v_p(m!) = \sum_{j=1}^{m} \sum_{i=1}^{\infty} \mathbf{1}[p^i \mid j] = \sum_{i=1}^{\infty} \sum_{j=1}^{m} \mathbf{1}[p^i \mid j] = \sum_{i=1}^{\infty} \left\lfloor \frac{m}{p^i} \right\rfloor.$$

The exchange of summation is justified because all terms are non-negative and the sums are finite (for $i > \lfloor \log_p m \rfloor$, the inner sum is zero). $\square$

---

## Part 2: Digit Sum Identity

**Lemma 2.** *For every non-negative integer $m$ and every prime $p$:*

$$\sum_{i=1}^{\infty} \left\lfloor \frac{m}{p^i} \right\rfloor = \frac{m - s_p(m)}{p - 1}.$$

*Equivalently, by Lemma 1: $v_p(m!) = \dfrac{m - s_p(m)}{p - 1}$.*

### Proof of Lemma 2

Let $m = \sum_{j=0}^{L} d_j \, p^j$ be the base-$p$ representation of $m$ (so $d_j = 0$ for $j > L$).

**Step 1: Express $\lfloor m/p^i \rfloor$ in terms of digits.**

For $1 \leq i \leq L$:

$$\left\lfloor \frac{m}{p^i} \right\rfloor = \left\lfloor \frac{\sum_{j=0}^{L} d_j \, p^j}{p^i} \right\rfloor = \sum_{j=i}^{L} d_j \, p^{j-i}$$

since the terms with $j < i$ contribute $\sum_{j=0}^{i-1} d_j \, p^{j-i}$, which is a sum of fractions strictly less than 1 in total (as $\sum_{j=0}^{i-1} d_j \, p^{j-i} \leq \sum_{j=0}^{i-1} (p-1) p^{j-i} = 1 - p^{-i} < 1$), and so falls away under the floor.

For $i > L$: $\lfloor m/p^i \rfloor = 0$.

**Step 2: Sum over $i$.**

$$\sum_{i=1}^{L} \left\lfloor \frac{m}{p^i} \right\rfloor = \sum_{i=1}^{L} \sum_{j=i}^{L} d_j \, p^{j-i}.$$

Exchange the order of summation (both sums are finite):

$$= \sum_{j=1}^{L} d_j \sum_{i=1}^{j} p^{j-i} = \sum_{j=1}^{L} d_j \sum_{\ell=0}^{j-1} p^{\ell} = \sum_{j=1}^{L} d_j \cdot \frac{p^j - 1}{p - 1}.$$

(The $j = 0$ term contributes nothing since the inner sum over $i$ from 1 to 0 is empty.)

**Step 3: Simplify.**

$$\sum_{j=1}^{L} d_j \cdot \frac{p^j - 1}{p - 1} = \frac{1}{p-1} \sum_{j=1}^{L} d_j (p^j - 1) = \frac{1}{p-1} \left( \sum_{j=1}^{L} d_j \, p^j - \sum_{j=1}^{L} d_j \right).$$

Now, $\sum_{j=1}^{L} d_j \, p^j = m - d_0$ and $\sum_{j=1}^{L} d_j = s_p(m) - d_0$. Therefore:

$$= \frac{1}{p-1} \big( (m - d_0) - (s_p(m) - d_0) \big) = \frac{m - s_p(m)}{p - 1}. \quad \square$$

**Remark.** Note that $m - s_p(m)$ is always divisible by $p - 1$. Indeed, $m = \sum d_j p^j$ and $s_p(m) = \sum d_j$, so $m - s_p(m) = \sum d_j(p^j - 1)$, and $p^j - 1$ is divisible by $p - 1$ for every $j \geq 0$.

---

## Part 3: The Valuation of $\binom{n}{k}$

**Proposition 3.** *For $n \geq k \geq 0$ and any prime $p$:*

$$v_p\!\left(\binom{n}{k}\right) = \frac{s_p(k) + s_p(n - k) - s_p(n)}{p - 1}.$$

### Proof of Proposition 3

Since $\binom{n}{k} = \frac{n!}{k! \cdot (n-k)!}$, and all three factorials are positive integers with $\binom{n}{k}$ being a positive integer, we have:

$$v_p\!\left(\binom{n}{k}\right) = v_p(n!) - v_p(k!) - v_p((n-k)!).$$

Applying Lemma 2 to each term:

$$v_p\!\left(\binom{n}{k}\right) = \frac{n - s_p(n)}{p-1} - \frac{k - s_p(k)}{p-1} - \frac{(n-k) - s_p(n-k)}{p-1}.$$

Combining into a single fraction:

$$= \frac{\big(n - s_p(n)\big) - \big(k - s_p(k)\big) - \big((n-k) - s_p(n-k)\big)}{p - 1}.$$

The numerator simplifies:

$$n - s_p(n) - k + s_p(k) - (n - k) + s_p(n-k) = s_p(k) + s_p(n-k) - s_p(n).$$

(The terms $n$, $-k$, and $-(n-k) = -n + k$ cancel.) Therefore:

$$v_p\!\left(\binom{n}{k}\right) = \frac{s_p(k) + s_p(n-k) - s_p(n)}{p - 1}. \quad \square$$

**Remark.** Since $v_p(\binom{n}{k}) \geq 0$ (as $\binom{n}{k}$ is a positive integer), we obtain the inequality $s_p(k) + s_p(n-k) \geq s_p(n)$ for all $n \geq k \geq 0$ and all primes $p$. In fact, this holds for all integers $a, b \geq 0$: $s_p(a) + s_p(b) \geq s_p(a + b)$, which is a well-known consequence of carries increasing digit sums.

---

## Part 4: Carry Analysis (Kummer's Theorem)

**Theorem 4 (Kummer, 1852).** *Let $p$ be a prime and $n \geq k \geq 0$ be integers. Then*

$$v_p\!\left(\binom{n}{k}\right) = C_p(k, n-k)$$

*where $C_p(a, b)$ denotes the number of carries when adding $a$ and $b$ in base $p$.*

### Setup: Carry Arithmetic

Let $a = k$ and $b = n - k$, so that $a + b = n$. Write:

$$a = \sum_{j=0}^{L} a_j \, p^j, \quad b = \sum_{j=0}^{L} b_j \, p^j, \quad n = a + b = \sum_{j=0}^{L} n_j \, p^j$$

where $0 \leq a_j, b_j, n_j \leq p - 1$ are the respective base-$p$ digits. (We may take $L$ large enough that all higher digits are zero.)

When adding $a$ and $b$ in base $p$, we process digit-by-digit from the least significant position upward. Define the **carry sequence** $(c_0, c_1, c_2, \ldots)$ by:

- $c_0 = 0$ (no initial carry),
- For each $j \geq 0$: $a_j + b_j + c_j = n_j + p \cdot c_{j+1}$.

Here $c_{j+1} \in \{0, 1\}$ is the carry out of position $j$ into position $j + 1$. This is well-defined because $a_j + b_j + c_j \leq (p-1) + (p-1) + 1 = 2p - 1 < 2p$, so the quotient when dividing by $p$ is either 0 or 1.

We also have $c_{L+1} = 0$ provided $L$ is chosen large enough (i.e., $L \geq \lfloor \log_p n \rfloor$), since $n = a + b$ has no digit beyond position $L$.

The **number of carries** is:

$$C_p(a, b) = \sum_{j=0}^{L} c_{j+1} = \sum_{j=1}^{L+1} c_j = \sum_{j=1}^{L} c_j$$

(using $c_0 = 0$ and $c_{L+1} = 0$).

### Proof of Theorem 4

By Proposition 3, it suffices to show:

$$s_p(a) + s_p(b) - s_p(a + b) = (p - 1) \sum_{j=1}^{L} c_j.$$

**Step 1: Sum the carry recurrence over all positions.**

From the carry recurrence $a_j + b_j + c_j = n_j + p \cdot c_{j+1}$, sum both sides over $j = 0, 1, \ldots, L$:

$$\sum_{j=0}^{L} a_j + \sum_{j=0}^{L} b_j + \sum_{j=0}^{L} c_j = \sum_{j=0}^{L} n_j + p \sum_{j=0}^{L} c_{j+1}.$$

The left side gives:

$$s_p(a) + s_p(b) + \sum_{j=0}^{L} c_j.$$

The right side gives:

$$s_p(n) + p \sum_{j=1}^{L+1} c_j.$$

**Step 2: Simplify the carry sums.**

Using $c_0 = 0$:

$$\sum_{j=0}^{L} c_j = \sum_{j=1}^{L} c_j.$$

Using $c_{L+1} = 0$:

$$\sum_{j=1}^{L+1} c_j = \sum_{j=1}^{L} c_j.$$

Let $C = \sum_{j=1}^{L} c_j$ (the total number of carries). Substituting:

$$s_p(a) + s_p(b) + C = s_p(n) + pC.$$

**Step 3: Solve for the digit sum discrepancy.**

$$s_p(a) + s_p(b) - s_p(n) = pC - C = (p-1)C.$$

Therefore:

$$v_p\!\left(\binom{n}{k}\right) = \frac{s_p(k) + s_p(n-k) - s_p(n)}{p-1} = \frac{(p-1)C}{p-1} = C = C_p(k, n-k). \quad \square$$

---

## Part 5: The Digit-Domination Criterion

**Corollary 5 (Lucas-type criterion).** *Let $p$ be a prime and $n \geq k \geq 0$. The following are equivalent:*

*(i) $p \nmid \binom{n}{k}$.*

*(ii) There are no carries when adding $k$ and $n - k$ in base $p$.*

*(iii) For every $j \geq 0$: $\mathrm{dig}_j^{(p)}(k) \leq \mathrm{dig}_j^{(p)}(n)$ (digit-domination).*

### Proof of Corollary 5

**(i) $\Leftrightarrow$ (ii):** By Theorem 4, $v_p(\binom{n}{k}) = C_p(k, n-k)$. Since carries $c_j \in \{0, 1\}$, the total number of carries $C_p(k, n-k) = 0$ if and only if all $c_j = 0$, which happens if and only if $p \nmid \binom{n}{k}$ (i.e., $v_p(\binom{n}{k}) = 0$).

**(ii) $\Rightarrow$ (iii):** Assume there are no carries, i.e., $c_j = 0$ for all $j \geq 0$. Let $a_j, b_j, n_j$ be the base-$p$ digits of $k$, $n - k$, $n$ respectively. The carry recurrence with all $c_j = 0$ gives:

$$a_j + b_j = n_j \quad \text{for all } j \geq 0.$$

Since $b_j \geq 0$, we obtain $a_j \leq n_j$ for all $j$. That is, $\mathrm{dig}_j^{(p)}(k) \leq \mathrm{dig}_j^{(p)}(n)$.

**(iii) $\Rightarrow$ (ii):** Assume $a_j \leq n_j$ for all $j$, where $a_j = \mathrm{dig}_j^{(p)}(k)$ and $n_j = \mathrm{dig}_j^{(p)}(n)$. Define $b_j = n_j - a_j$ for each $j$. Then $0 \leq b_j \leq p - 1$ (since $0 \leq a_j \leq n_j \leq p - 1$), and:

$$\sum_{j=0}^{L} b_j \, p^j = \sum_{j=0}^{L} (n_j - a_j) \, p^j = n - k.$$

So $(b_0, b_1, \ldots)$ is the base-$p$ representation of $n - k$. Now $a_j + b_j = n_j < p$ for every $j$, so no carry is ever produced. That is, $c_j = 0$ for all $j \geq 1$, and the number of carries is 0. $\square$

---

## Part 6: An Equivalent Formulation via Lucas' Theorem

For completeness, we record how the digit-domination criterion relates to Lucas' theorem.

**Theorem 6 (Lucas, 1878).** *Let $p$ be a prime and write $n = \sum_{j} n_j p^j$ and $k = \sum_{j} k_j p^j$ in base $p$. Then:*

$$\binom{n}{k} \equiv \prod_{j \geq 0} \binom{n_j}{k_j} \pmod{p}.$$

*In particular, $p \nmid \binom{n}{k}$ if and only if $k_j \leq n_j$ for all $j$ (since $\binom{n_j}{k_j} = 0$ when $k_j > n_j$, and $1 \leq \binom{n_j}{k_j} \leq \binom{p-1}{0} = 1$ when $0 \leq k_j \leq n_j \leq p-1$, and the product is nonzero mod $p$ iff no factor is zero).*

We do not prove Lucas' theorem here, but note that the direction relevant to our applications — the characterization of when $p \nmid \binom{n}{k}$ — is already established by Corollary 5 without needing the full congruence. Specifically:

- **Corollary 5 gives:** $p \nmid \binom{n}{k} \Leftrightarrow k_j \leq n_j$ for all $j$.
- **Lucas' theorem additionally gives:** the exact residue of $\binom{n}{k}$ mod $p$.

For the applications in this project (determining which primes divide $\binom{n}{k}$), Corollary 5 (derived from Kummer's theorem) is sufficient.

---

## Summary of Key Results for Formalization

The results to be formalized, in dependency order:

1. **Legendre's formula (Lemma 1):** $v_p(m!) = \sum_{i \geq 1} \lfloor m/p^i \rfloor$.

2. **Digit sum identity (Lemma 2):** $\sum_{i \geq 1} \lfloor m/p^i \rfloor = (m - s_p(m))/(p-1)$.

3. **Valuation of binomials (Proposition 3):** $v_p(\binom{n}{k}) = (s_p(k) + s_p(n-k) - s_p(n))/(p-1)$.

4. **Carry identity (Theorem 4 = Kummer's theorem):** $v_p(\binom{n}{k}) = C_p(k, n-k)$.

5. **Digit-domination criterion (Corollary 5):** $p \nmid \binom{n}{k} \Leftrightarrow \forall j,\; \mathrm{dig}_j^{(p)}(k) \leq \mathrm{dig}_j^{(p)}(n)$.

For the main project application, the key consequences are:

- **For primes $p \leq k$:** $p \mid \binom{n}{k}$ iff some base-$p$ digit of $k$ exceeds the corresponding digit of $n$.
- **For primes $p > k$:** Since $k < p$, the number $k$ has a single base-$p$ digit $k_0 = k$, and all higher digits are 0. Digit-domination then says $p \nmid \binom{n}{k}$ iff $k \leq n_0 = n \bmod p$, i.e., $n \bmod p \geq k$. Equivalently, $p \mid \binom{n}{k}$ iff $n \bmod p < k$, which is the same as saying there exists a multiple of $p$ in the interval $\{n - k + 1, \ldots, n\}$.

## References

- Kummer, E.E. (1852). "Über die Ergänzungssätze zu den allgemeinen Reciprocitätsgesetzen." *Journal für die reine und angewandte Mathematik*, 44, 93–146.
- Lucas, É. (1878). "Théorie des fonctions numériques simplement périodiques." *American Journal of Mathematics*, 1(2), 184–196.
- Granville, A. (1997). "Arithmetic properties of binomial coefficients. I. Binomial coefficients modulo prime powers." *CMS Conference Proceedings*, 20, 253–276.
