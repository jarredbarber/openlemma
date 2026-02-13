# Kummer Carry Analysis for Smooth Case

**Objective:** Trace the arithmetic of $\binom{n}{k}$ divisibility for specific smooth-case examples to understand the structural mechanism.

## Example 1: $k=5, n=50$

Here $M = n/k = 10 = 2 \cdot 5$. $M$ is 5-smooth.
$\binom{50}{5} = 2,118,760 = 2^3 \cdot 5^1 \cdot 7^2 \cdot 23 \cdot 47$.
Prime factors $\le 5$: **2, 5**. (3 does not divide).

### Prime $p=2$ (Divides)
**Values:** $k=5=101_2$, $n-k=45=101101_2$.
**Addition $k+(n-k)=n$:**
```
  101101 (45)
+    101 (5)
--------
  110010 (50)
```
**Carries:**
1.  Pos 0: $1+1=10_2$. Carry generated.
2.  Pos 2: $1+1=10_2$. Carry generated.
3.  Pos 3: $1+0+1=10_2$. Carry generated.
**Result:** 3 carries $\implies v_2(\binom{50}{5}) = 3$.
**Mechanism:** Both $k$ and $n-k$ are odd, forcing a carry at bit 0. Propagates.

### Prime $p=3$ (Does NOT Divide)
**Values:** $k=5=12_3$, $n-k=45=1200_3$.
**Addition:**
```
  1200 (45)
+   12 (5)
------
  1212 (50)
```
**Carries:**
1.  Pos 0: $0+2=2 < 3$. No carry.
2.  Pos 1: $0+1=1 < 3$. No carry.
**Result:** 0 carries $\implies 3 \nmid \binom{50}{5}$.
**Mechanism:** Digits of $k$ ($1, 2$) and $n-k$ ($0, 0$) never sum to $\ge 3$.

### Prime $p=5$ (Divides)
**Values:** $k=5=10_5$, $n-k=45=140_5$.
**Addition:**
```
   140 (45)
+   10 (5)
------
   200 (50)
```
**Carries:**
1.  Pos 0: $0+0=0$. No carry.
2.  Pos 1: $4+1=5=10_5$. Carry generated.
**Result:** 1 carry $\implies v_5(\binom{50}{5}) = 1$.
**Mechanism:** $v_5(n)=2 > v_5(k)=1$. The higher valuation of $n$ forces a carry to "clear" the digits of $k$. Specifically, digit 1 of $k$ meets digit 4 of $n-k$ to sum to 5.

---

## Example 2: $k=5, n=30$

Here $M = n/k = 6 = 2 \cdot 3$. $M$ is 5-smooth.
$\binom{30}{5} = 142,506 = 2 \cdot 3 \cdot 13 \cdot 1827$.
Prime factors $\le 5$: **2, 3**. (5 does not divide).

### Prime $p=2$ (Divides)
**Values:** $k=5=101_2$, $n-k=25=11001_2$.
**Addition:**
```
  11001 (25)
+   101 (5)
-------
  11110 (30)
```
**Carries:**
1.  Pos 0: $1+1=10_2$. Carry generated.
**Result:** 1 carry.
**Mechanism:** Both odd.

### Prime $p=3$ (Divides)
**Values:** $k=5=12_3$, $n-k=25=221_3$.
**Addition:**
```
  221 (25)
+  12 (5)
-----
 1010 (30)
```
**Carries:**
1.  Pos 0: $1+2=3$. Carry.
2.  Pos 1: $2+1+1=4$. Carry.
3.  Pos 2: $2+1=3$. Carry.
**Result:** 3 carries.
**Mechanism:** $k \equiv 2, n-k \equiv 1 \pmod 3$. Sum to 0 mod 3, carry.

### Prime $p=5$ (Does NOT Divide)
**Values:** $k=5=10_5$, $n-k=25=100_5$.
**Addition:**
```
  100 (25)
+  10 (5)
-----
  110 (30)
```
**Carries:**
1.  Pos 0: $0+0=0$.
2.  Pos 1: $0+1=1$.
**Result:** 0 carries.
**Mechanism:** $v_5(n)=1, v_5(k)=1$. $n$ is not "more divisible" than $k$. Digits align without overflow.

---

## Structural Insight

1.  **Divisibility by Factors of M:**
    -   For $n=50$ ($M=10=2 \cdot 5$), primes 2 and 5 divided $\binom{n}{k}$.
    -   For $n=30$ ($M=6=2 \cdot 3$), primes 2 and 3 divided $\binom{n}{k}$.
    -   **Pattern:** If $p \mid M$ (and $p \le k$), then $p$ tends to divide $\binom{kM}{k}$.
    -   **Reason:** If $p \mid M$, then $v_p(n) = v_p(k) + v_p(M) > v_p(k)$. The higher valuation of $n$ requires a carry in the addition $k + (n-k)$ to clear the non-zero digits of $k$ at position $v_p(k)$.

2.  **Smoothness Implication:**
    -   Since $M$ is $k$-smooth, it has *some* prime factor $p \le k$.
    -   This prime $p$ is forced to divide $\binom{kM}{k}$ by the valuation argument.
    -   Thus, $\binom{kM}{k}$ is never an exception.

3.  **Interval Extension:**
    -   For $n \in (kM, kM+k)$, the property $v_p(n) > v_p(k)$ is lost (since $n$ is not a multiple of $k$).
    -   However, other primes take over. E.g., for $n=31, k=5$, $p=3$ divides (carry chain).
    -   The "no exception" property relies on the **density** of carries for small primes.
