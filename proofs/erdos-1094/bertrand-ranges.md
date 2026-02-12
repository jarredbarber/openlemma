# Erdos 1094: Bertrand Prime Range Lemmas

**Status:** Verified ✅
**Reviewed by:** verify
**Statement:**
1. For $k \ge 29$, there exists a prime $p$ such that $k < p \le 2k$.
2. For any prime $p$ and integers $n, k$ such that $k < p$ and $n \pmod p < k$, we have $p \mid \binom{n}{k}$.

## Review Notes
- **Bertrand's Postulate**: The existence of a prime in $(k, 2k]$ is a standard result in number theory (Chebyshev's Theorem) and is correctly applied.
- **Divisibility Rigor**: The proof for $p \mid \binom{n}{k}$ is provided via two independent methods (Direct Enumeration and Kummer's Theorem), both of which are rigorous.
- **Corner Cases**: The proof correctly handles the $n < k$ (where $\binom{n}{k}=0$) and the $q=0$ cases.

**Dependencies:** Bertrand's Postulate, Kummer's Theorem (or elementary divisibility).
**Confidence:** Certain

## Proof

### 1. Existence of Prime in (k, 2k]

This is a direct application of **Bertrand's Postulate** (Chebyshev's Theorem).
Bertrand's Postulate states that for every $n > 1$, there exists a prime $p$ such that $n < p < 2n - 2$.
A more common form used in Mathlib (`Nat.exists_prime_and_le_and_lt`) states that for $n > 1$, there exists a prime $p \in (n, 2n)$.
For $k \ge 29$, the interval $(k, 2k]$ contains at least one prime.

### 2. Divisibility Lemma: $n \bmod p < k \implies p \mid \binom{n}{k}$

Let $p$ be a prime and $n, k$ be integers such that $k < p$.
Let $r = n \bmod p$. Then $n = qp + r$ for some integer $q$, with $0 \le r < p$.
Assume $r < k$.

We want to show $p \mid \binom{n}{k} = \frac{n(n-1)\dots(n-k+1)}{k!}$.

#### Method A: Direct Enumeration
The factors in the numerator are $N = \{n, n-1, \dots, n-k+1\}$.
We know $n = qp + r$.
Consider the value $x = n - r = qp$.
Since $0 \le r < k$ (by assumption), we have:
$n - (k-1) \le n - r \le n$.
Thus $x \in N$.
This means the numerator contains a multiple of $p$.
Furthermore, since $p > k$, the interval $(n-k, n]$ of length $k$ can contain at most one multiple of $p$ (since the distance between multiples is $p > k$).
So the numerator contains exactly one factor divisible by $p$ (if $q > 0$).
Wait, if $q=0$, then $n=r < k$, in which case $\binom{n}{k} = 0$, which is divisible by $p$.
If $q \ge 1$, then $x = qp \ge p > k$, so $x$ is a positive multiple of $p$.
The power of $p$ dividing the numerator is at least $v_p(qp) \ge 1$.

Now consider the denominator $k!$.
Since $p > k$, all factors $1, 2, \dots, k$ are less than $p$.
Thus $p \nmid j$ for all $1 \le j \le k$.
By Euclid's Lemma, $p \nmid k!$.
Therefore, $p$ must divide the integer $\binom{n}{k}$.

#### Method B: Kummer's Theorem
Kummer's theorem states that $v_p(\binom{n}{k})$ is the number of carries when adding $k$ and $n-k$ in base $p$.
Since $k < p$, the base-$p$ expansion of $k$ is just the single digit $k_0 = k$.
Let $n = \dots n_1 p + n_0$ where $n_0 = n \bmod p$.
Let $m = n - k = \dots m_1 p + m_0$ where $m_0 = m \bmod p$.
We have $n = k + m$.
In the 0-th digit (units place), we are adding $k_0 = k$ and $m_0 = (n-k) \bmod p$.
A carry occurs from the 0-th digit to the 1-st digit if:
$k_0 + m_0 \ge p$.
Substitute $m_0$:
$k + (n-k) \bmod p \ge p$.
Recall $(n-k) \bmod p = (n \bmod p - k \bmod p) \bmod p = (n_0 - k) \bmod p$.
If $n_0 < k$, then $n_0 - k < 0$.
Since $|n_0 - k| < p$, $(n_0 - k) \bmod p = n_0 - k + p$.
Then $k + m_0 = k + (n_0 - k + p) = n_0 + p$.
Since $n_0 \ge 0$, $n_0 + p \ge p$, so a carry occurs.
Thus $v_p(\binom{n}{k}) \ge 1$, which means $p \mid \binom{n}{k}$.
