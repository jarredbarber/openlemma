# Kummer Carry Analysis for C(50, 5)

**Target:** Explicitly trace Kummer carries for $\binom{50}{5}$.
$k=5$, $n=50$.
$\binom{50}{5} = 2,118,760$.

## 1. Factorization
$2,118,760 = 2^3 \cdot 5^1 \cdot 7^2 \cdot 23^1 \cdot 47^1$.
Primes $\le 5$ dividing it: **2 and 5**. (3 does not divide).

## 2. Kummer Trace ($5 + 45 = 50$)

### Base 2 ($p=2$)
-   $k=5=101_2$
-   $n-k=45=101101_2$
```
  101101
+    101
--------
  110010
```
-   **Bit 0:** $1+1=10_2$ (0, carry 1). **Carry.**
-   **Bit 1:** $0+0+1=1$. No carry.
-   **Bit 2:** $1+1=10_2$ (0, carry 1). **Carry.**
-   **Bit 3:** $1+0+1=10_2$ (0, carry 1). **Carry.**
-   **Bit 4:** $0+1=1$. No carry.
-   **Bit 5:** $1$.
**Result:** 3 carries $\implies v_2 = 3$. Matches $2^3$.

### Base 3 ($p=3$)
-   $k=5=12_3$
-   $n-k=45=1200_3$
```
  1200
+   12
------
  1212
```
-   **Pos 0:** $0+2=2 < 3$. No carry.
-   **Pos 1:** $0+1=1 < 3$. No carry.
-   **Pos 2:** $2$.
-   **Pos 3:** $1$.
**Result:** 0 carries $\implies v_3 = 0$. Matches $3 \nmid \binom{50}{5}$.

### Base 5 ($p=5$)
-   $k=5=10_5$
-   $n-k=45=140_5$
```
   140
+   10
------
   200
```
-   **Pos 0:** $0+0=0$. No carry.
-   **Pos 1:** $4+1=5=10_5$ (0, carry 1). **Carry.**
-   **Pos 2:** $1+1=2$. No carry.
**Result:** 1 carry $\implies v_5 = 1$. Matches $5^1$.

## 3. Structural Reason for Divisibility
-   **For $p=5$:** The divisibility is forced by the carry at position $5^1$. $n-k=45$ has digit 4 at this position ($4 \times 5$), and $k=5$ has digit 1 ($1 \times 5$). Since $4+1=5$, a carry is generated. This corresponds to the valuation condition $v_5(n)=2 > v_5(k)=1$.
-   **For $p=2$:** Divisibility starts at bit 0 because both $k$ and $n-k$ are odd.
-   **For $p=3$:** No alignment of digits sums to $\ge 3$.
