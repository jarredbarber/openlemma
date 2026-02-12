# Proof: 3-SAT reduces to SUBSET SUM

**Statement:** 3-SAT $\le_p$ SUBSET SUM.
**Status:** Draft ✏️
**Goal:** Construct a polynomial-time reduction $f$ that maps any 3-CNF formula $\phi$ to an instance $(S, t)$ of SUBSET SUM such that $\phi$ is satisfiable if and only if there exists a subset of $S$ that sums to $t$.

## 1. Definitions

### 1.1 The SUBSET SUM Problem
**Input:** A finite set of natural numbers $S = \{w_1, \dots, w_n\}$ and a target integer $t$.
**Question:** Does there exist a subset $S' \subseteq S$ such that $\sum_{w \in S'} w = t$?

## 2. The Reduction

Let $\phi$ be a 3-CNF formula with $n$ variables $x_1, \dots, x_n$ and $k$ clauses $C_1, \dots, C_k$.
We represent the numbers in base 10 (or any base $B > k$).
Each number will have $n + k$ digits.
-   The first $n$ digits correspond to variables.
-   The last $k$ digits correspond to clauses.

### 2.1 The Set $S$
We construct the set $S$ containing the following integers:

1.  **Variable Pairs:** For each variable $x_i$ ($1 \le i \le n$), we create two numbers $v_i$ and $v'_i$.
    -   $v_i$: Corresponds to setting $x_i = \text{true}$.
        -   Digit $i$ (variable region) is 1.
        -   Digit $n+j$ (clause region) is 1 if $x_i \in C_j$, else 0.
    -   $v'_i$: Corresponds to setting $x_i = \text{false}$.
        -   Digit $i$ (variable region) is 1.
        -   Digit $n+j$ (clause region) is 1 if $\neg x_i \in C_j$, else 0.
    -   All other digits are 0.

2.  **Slack Variables:** For each clause $C_j$ ($1 \le j \le k$), we create two slack numbers $s_{j,1}$ and $s_{j,2}$.
    -   $s_{j,1}$:
        -   Digit $n+j$ (clause region) is 1.
        -   All other digits 0.
    -   $s_{j,2}$:
        -   Digit $n+j$ (clause region) is 1.
        -   All other digits 0.
    -   (Note: These are identical in value, but treated as distinct elements in $S$. Or we can make them distinct by encoding index differently, but standard reduction uses identical values).

### 2.2 The Target $t$
The target sum $t$ is defined digit-by-digit:
-   **Digits $1 \dots n$ (Variables):** Target is 1.
    -   Ensures we pick exactly one of $v_i$ or $v'_i$ for each $i$.
-   **Digits $n+1 \dots n+k$ (Clauses):** Target is 3.
    -   Ensures the sum of literals + slack in clause $j$ is exactly 3. Since the maximum number of literals summing to 3 is 3, and slack can add up to 2, we can reach 3 iff we have at least 1 literal (1+2=3, 2+1=3, 3+0=3).

### 2.3 Formal Representation
Let $D = n+k$.
Base $B = 10$.
$v_i = 10^{D-i} + \sum_{j=1}^k (\mathbb{I}(x_i \in C_j) \cdot 10^{k-j})$
$v'_i = 10^{D-i} + \sum_{j=1}^k (\mathbb{I}(\neg x_i \in C_j) \cdot 10^{k-j})$
$s_{j,1} = s_{j,2} = 10^{k-j}$
$t = \sum_{i=1}^n 10^{D-i} + \sum_{j=1}^k 3 \cdot 10^{k-j}$

## 3. Correctness

We must show: $\phi$ is satisfiable $\iff \exists S' \subseteq S, \sum S' = t$.

### 3.1 Completeness ($\implies$)
Assume $\phi$ is satisfiable by assignment $\sigma$.
Construct $S'$:
1.  **Variables:** For each $i$, if $\sigma(x_i) = \text{true}$, select $v_i$. If false, select $v'_i$.
    -   This contributes exactly 1 to each variable digit $1 \dots n$.
    -   This contributes $L_j$ to clause digit $j$, where $L_j$ is the number of satisfied literals in $C_j$.
    -   Since $\phi$ is satisfied, $1 \le L_j \le 3$.
2.  **Slack:** For each clause $j$:
    -   If $L_j = 1$ (1 satisfied literal), select both $s_{j,1}$ and $s_{j,2}$. (Total digit sum $1+1+1=3$).
    -   If $L_j = 2$ (2 satisfied literals), select $s_{j,1}$. (Total digit sum $2+1=3$).
    -   If $L_j = 3$ (3 satisfied literals), select neither. (Total digit sum $3+0=3$).
    -   (If $L_j=0$, we need slack=3, impossible with two 1s. This confirms satisfaction necessity).

Summing digits:
-   Variable digits: Exactly 1 (from $v_i/v'_i$). Matches target.
-   Clause digits: $L_j + \text{slack} = 3$. Matches target.
-   **No Carries:** Since maximum sum in any digit is $3+2=5 < 10$, there are no carries. The digit-wise sum equals the integer sum.
Thus, $\sum S' = t$.

### 3.2 Soundness ($\impliedby$)
Assume $\exists S' \subseteq S$ such that $\sum S' = t$.
Since there are no carries (sum of any column is at most $1+1$ (vars) + $3$ (lits) + $2$ (slack) = $7 < 10$? Wait.
-   Variable column: max 2 elements ($v_i, v'_i$).
-   Clause column: max 3 literals + 2 slack = 5.
-   So no carries occur. We can reason digit-by-digit.

**Variable Digits ($1 \dots n$):**
Target is 1.
For each $i$, we must select exactly one of $\{v_i, v'_i\}$.
If we select none, sum is 0. If both, sum is 2.
Let $\sigma(x_i) = \text{true}$ if $v_i \in S'$, and $\text{false}$ if $v'_i \in S'$.
This defines a valid truth assignment.

**Clause Digits ($n+1 \dots n+k$):**
Target is 3.
The contribution from variable numbers is $L_j$ (number of satisfied literals in $C_j$).
The contribution from slack numbers is $S_j \in \{0, 1, 2\}$ (subset of $\{s_{j,1}, s_{j,2}\}$).
Equation: $L_j + S_j = 3$.
Since $S_j \le 2$, we must have $L_j \ge 1$.
Thus, at least one literal in $C_j$ is satisfied by $\sigma$.
This holds for all $j$, so $\phi$ is satisfiable.

## 4. Complexity

-   **Size:**
    -   Number of integers: $2n + 2k$.
    -   Number of digits per integer: $n + k$.
    -   Bit length of numbers: $O((n+k) \log 10) = O(n+k)$.
    -   Total size: $O((n+k)^2)$. Polynomial.
-   **Time:**
    -   Generating digits is a direct loop over variables and clauses.
    -   Polynomial time.

## 5. Conclusion

We have constructed a polynomial-time reduction from 3-SAT to SUBSET SUM.
Since 3-SAT is NP-hard, SUBSET SUM is NP-hard.
Since SUBSET SUM is clearly in NP (certificate is the subset), SUBSET SUM is NP-complete.
