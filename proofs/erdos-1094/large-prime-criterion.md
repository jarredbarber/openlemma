# Large Prime Divisibility Criterion for Binomial Coefficients

**Status:** Verified ✅
**Reviewed by:** erdos1094-oil
**Statement:** Let $p$ be a prime with $p > k \geq 1$, and let $n \geq k$. Then $p \mid \binom{n}{k}$ if and only if $n \bmod p < k$.
**Dependencies:** proofs/kummer-theorem.md (Legendre's formula; used in one step but re-derived inline for self-containment)
**Confidence:** Certain

---

## Proof

### Assumptions

Throughout, $p$ denotes a prime number, $k$ a positive integer with $p > k \geq 1$, and $n$ a non-negative integer with $n \geq k$.

### Step 1: Express $v_p\bigl(\binom{n}{k}\bigr)$ in terms of the falling factorial

Since $\binom{n}{k} = \frac{n!}{k!\,(n-k)!}$ is a positive integer (as $n \geq k \geq 1$), the $p$-adic valuation satisfies:

$$v_p\!\left(\binom{n}{k}\right) = v_p(n!) - v_p(k!) - v_p((n-k)!).$$

### Step 2: Show $v_p(k!) = 0$

Since $p > k \geq 1$, no integer in $\{1, 2, \ldots, k\}$ is divisible by $p$ (as all are strictly less than $p$). Therefore:

$$v_p(k!) = \sum_{j=1}^{k} v_p(j) = 0.$$

### Step 3: Apply Legendre's formula

From Steps 1 and 2:

$$v_p\!\left(\binom{n}{k}\right) = v_p(n!) - v_p((n-k)!).$$

By Legendre's formula (proved in proofs/kummer-theorem.md, Lemma 1):

$$v_p(m!) = \sum_{i=1}^{\infty} \left\lfloor \frac{m}{p^i} \right\rfloor$$

for any non-negative integer $m$. Applying this to both $n!$ and $(n-k)!$:

$$v_p\!\left(\binom{n}{k}\right) = \sum_{i=1}^{\infty} \left( \left\lfloor \frac{n}{p^i} \right\rfloor - \left\lfloor \frac{n-k}{p^i} \right\rfloor \right).$$

### Step 4: Show that $p \mid \binom{n}{k}$ iff a multiple of $p$ lies in $\{n-k+1,\ldots,n\}$

For each $i \geq 1$, the quantity $\left\lfloor \frac{n}{p^i} \right\rfloor - \left\lfloor \frac{n-k}{p^i} \right\rfloor$ counts the number of multiples of $p^i$ in the set $\{n-k+1, n-k+2, \ldots, n\}$. (This is the standard identity: the number of multiples of $d$ in $\{a+1, \ldots, b\}$ is $\lfloor b/d \rfloor - \lfloor a/d \rfloor$.)

This set has exactly $k$ elements. Since $p^i \geq p > k$ for all $i \geq 1$, consecutive multiples of $p^i$ are spaced at least $p^i > k$ apart. Therefore the interval $\{n-k+1, \ldots, n\}$ contains **at most one** multiple of $p^i$, so each term satisfies:

$$\left\lfloor \frac{n}{p^i} \right\rfloor - \left\lfloor \frac{n-k}{p^i} \right\rfloor \in \{0, 1\}.$$

Now we establish the key equivalence. Since every multiple of $p^i$ (for $i \geq 2$) is also a multiple of $p$, if no multiple of $p$ lies in the interval, then no multiple of $p^i$ for any $i \geq 1$ lies there either. This gives:

- **If the $i = 1$ term is 0** (no multiple of $p$ in the interval): all terms in the sum are 0, so $v_p\bigl(\binom{n}{k}\bigr) = 0$ and $p \nmid \binom{n}{k}$.
- **If the $i = 1$ term is 1** (some multiple of $p$ in the interval): $v_p\bigl(\binom{n}{k}\bigr) \geq 1$ and $p \mid \binom{n}{k}$.

Therefore:

$$p \mid \binom{n}{k} \iff \left\lfloor \frac{n}{p} \right\rfloor > \left\lfloor \frac{n-k}{p} \right\rfloor. \tag{$\star$}$$

### Step 5: Translate the floor condition to a modular condition

Write $n = qp + r$ where $q = \lfloor n/p \rfloor$ and $r = n \bmod p$, so $0 \leq r \leq p-1$.

Then $n - k = qp + r - k$.

**Case A: $r \geq k$.**

Since $r \geq k \geq 1$ and $r \leq p - 1$, we have $r - k \geq 0$. Also $r - k \leq p - 1 - 1 = p - 2 < p - 1$, so:

$$\left\lfloor \frac{n-k}{p} \right\rfloor = \left\lfloor q + \frac{r-k}{p} \right\rfloor = q$$

since $0 \leq r - k < p$. Therefore $\lfloor n/p \rfloor - \lfloor (n-k)/p \rfloor = q - q = 0$.

By $(\star)$, this gives $p \nmid \binom{n}{k}$.

**Case B: $r < k$.**

Since $0 \leq r < k < p$, we have $-p < r - k < 0$, so we can write:

$$n - k = qp + (r - k) = (q - 1)p + (p + r - k).$$

We verify that $p + r - k$ is a valid remainder modulo $p$:
- **Lower bound:** $p + r - k \geq p + 0 - (p - 1) = 1 > 0$ (using $r \geq 0$ and $k \leq p - 1$).
- **Upper bound:** $p + r - k \leq p + (k - 1) - k = p - 1$ (using $r \leq k - 1$, i.e., $r < k$).

So $\lfloor (n-k)/p \rfloor = q - 1$.

Therefore $\lfloor n/p \rfloor - \lfloor (n-k)/p \rfloor = q - (q-1) = 1 > 0$.

By $(\star)$, this gives $p \mid \binom{n}{k}$.

### Step 6: Combine

From Cases A and B of Step 5:

$$p \mid \binom{n}{k} \iff r < k \iff n \bmod p < k.$$

This completes the proof. $\blacksquare$

---

## Alternative Proof via Digit Domination (Corollary of Kummer's Theorem)

We give a second, shorter proof using the digit-domination criterion from proofs/kummer-theorem.md (Corollary 5).

**Setup.** Since $p > k \geq 1$, the base-$p$ representation of $k$ is simply $k$ itself: $k$ has a single digit $k_0 = k$ (with $0 < k < p$) and all higher digits are 0.

**By Corollary 5** (digit domination): $p \nmid \binom{n}{k}$ iff every base-$p$ digit of $k$ is $\leq$ the corresponding digit of $n$. Since the only nonzero digit of $k$ is $k_0 = k$, this reduces to:

$$p \nmid \binom{n}{k} \iff k \leq n_0$$

where $n_0 = n \bmod p$ is the least significant base-$p$ digit of $n$. (All higher-digit conditions are $0 \leq n_j$, which hold trivially.)

Taking the negation:

$$p \mid \binom{n}{k} \iff n \bmod p < k. \qquad \blacksquare$$

---

## Corollary: Geometric Interpretation

The condition $n \bmod p < k$ is equivalent to saying that there exists a multiple of $p$ in the interval $\{n-k+1, n-k+2, \ldots, n\}$.

*Proof.* A multiple of $p$ lies in $\{n-k+1, \ldots, n\}$ iff $\lfloor n/p \rfloor \cdot p \geq n - k + 1$, i.e., $n - \lfloor n/p \rfloor \cdot p \leq k - 1$, i.e., $n \bmod p \leq k - 1$, i.e., $n \bmod p < k$. $\square$

---

## Corollary: Sharpened Valuation

Under the same hypotheses ($p$ prime, $p > k \geq 1$, $n \geq k$), we have more precisely:

$$v_p\!\left(\binom{n}{k}\right) = \left\lfloor \frac{n}{p} \right\rfloor - \left\lfloor \frac{n-k}{p} \right\rfloor \in \{0, 1\}.$$

*Proof.* This was established in Steps 3–4 of the main proof: each term $\lfloor n/p^i \rfloor - \lfloor (n-k)/p^i \rfloor$ for $i \geq 1$ is either 0 or 1 (since the interval has length $k < p \leq p^i$), and the $i \geq 2$ terms are dominated by the $i = 1$ term (any multiple of $p^2$ is a multiple of $p$). The $i = 1$ term thus equals the full sum. $\square$

This shows that for primes $p > k$, the binomial coefficient $\binom{n}{k}$ is either coprime to $p$ or divisible by $p$ exactly once — never by $p^2$.

## References

- proofs/kummer-theorem.md — Legendre's formula (Lemma 1) and the digit-domination criterion (Corollary 5)
