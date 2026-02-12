# Proof: SUBSET SUM reduces to PARTITION

**Statement:** SUBSET SUM $\le_p$ PARTITION.
**Status:** Under review 🔍
**Reviewed by:** verify
**Goal:** Construct a polynomial-time reduction $f$ that maps any instance $(S, t)$ of SUBSET SUM to an instance $S'$ of PARTITION such that there exists a subset of $S$ summing to $t$ if and only if $S'$ can be partitioned into two subsets of equal sum.

## Review Notes
(Resolved)


## 1. Definitions

### 1.1 SUBSET SUM
**Input:** A multiset of natural numbers $S = \{x_1, \dots, x_n\}$ and a target $t$.
**Question:** Does there exist $A \subseteq S$ such that $\sum_{x \in A} x = t$?

### 1.2 PARTITION
**Input:** A multiset of natural numbers $S' = \{y_1, \dots, y_m\}$.
**Question:** Does there exist $A' \subseteq S'$ such that $\sum_{y \in A'} y = \sum_{y \in S' \setminus A'} y$?
Note that this is equivalent to $\sum_{y \in A'} y = \frac{1}{2} \sum_{y \in S'} y$.

## 2. The Reduction

Let $(S, t)$ be an instance of SUBSET SUM.
Let $\sigma = \sum_{x \in S} x$ be the total sum of elements in $S$.

### 2.1 Construction of $S'$
**Case $t > \sigma$:**
If the target sum $t$ exceeds the total sum $\sigma$, the SUBSET SUM instance is trivially unsatisfiable (since elements are non-negative).
In this case, we output a fixed unsatisfiable PARTITION instance, e.g., $S' = \{1, 2\}$ (odd sum 3, cannot be partitioned).
This correctly maps "no" instance to "no" instance.

**Case $t \le \sigma$:**
We construct $S'$ by adding two new elements to $S$:
$$ S' = S \cup \{J_1, J_2\} $$
where
$$ J_1 = 2\sigma - t $$
$$ J_2 = \sigma + t $$
Since $t \le \sigma$, $J_1 = 2\sigma - t \ge \sigma \ge 0$, so $J_1$ is a valid natural number.
$J_2$ is clearly valid.

### 2.2 Target Sum
The total sum of $S'$ is:
$$ \Sigma' = \sigma + J_1 + J_2 = \sigma + (2\sigma - t) + (\sigma + t) = 4\sigma $$
The target for PARTITION is half the total sum:
$$ T' = \frac{\Sigma'}{2} = 2\sigma $$

## 3. Correctness

We show: $\exists A \subseteq S, \sum A = t \iff \exists A' \subseteq S', \sum A' = 2\sigma$.

### 3.1 Completeness ($\implies$)
Assume there exists $A \subseteq S$ such that $\sum_{x \in A} x = t$.
Let $B = S \setminus A$. Then $\sum_{x \in B} x = \sigma - t$.

Construct a partition of $S'$ into $A'$ and $B'$:
Let $A' = A \cup \{J_1\}$.
Let $B' = B \cup \{J_2\}$.

Check the sum of $A'$:
$$ \sum A' = \sum A + J_1 = t + (2\sigma - t) = 2\sigma $$
Since the total sum is $4\sigma$, the sum of $B'$ must also be $2\sigma$.
Thus, $A'$ is a valid partition.

### 3.2 Soundness ($\impliedby$)
Assume there exists a partition of $S'$ into $A', B'$ such that $\sum A' = \sum B' = 2\sigma$.

The set $S'$ contains $J_1 = 2\sigma - t$ and $J_2 = \sigma + t$.
Consider where $J_1$ and $J_2$ are located in the partition.

**Case 1: $J_1$ and $J_2$ are in the same subset (WLOG $A'$).**
Then $\sum A' \ge J_1 + J_2 = (2\sigma - t) + (\sigma + t) = 3\sigma$.
But the target sum is $2\sigma$.
Since elements are non-negative, $3\sigma \le 2\sigma \implies \sigma = 0$.
If $\sigma > 0$, this is impossible.
If $\sigma = 0$, then $t=0$, which is trivially solvable.
Assuming non-trivial case, $J_1$ and $J_2$ must be in different subsets.

**Case 2: $J_1 \in A'$ and $J_2 \in B'$.**
Then $A'$ consists of $J_1$ plus some subset $A \subseteq S$.
Sum constraint:
$$ \sum A' = J_1 + \sum_{x \in A} x = 2\sigma $$
Substitute $J_1 = 2\sigma - t$:
$$ (2\sigma - t) + \sum_{x \in A} x = 2\sigma $$
$$ \sum_{x \in A} x = t $$
Thus, the subset $A \subseteq S$ sums to $t$.
SUBSET SUM is satisfied.

## 4. Complexity

-   **Size:** $|S'| = |S| + 2$. The numbers $J_1, J_2$ have bit length $O(\log \sigma)$, which is comparable to the input size (sum of bit lengths). Linear size increase.
-   **Time:** Computing sums and adding elements is linear in the input size.

## 5. Conclusion

We have constructed a polynomial-time reduction from SUBSET SUM to PARTITION.
Since SUBSET SUM is NP-hard, PARTITION is NP-hard.

**PARTITION $\in$ NP:**
A witness for PARTITION is a subset indicator bit-vector $c$ (where $c_i = 1 \iff y_i \in A'$).
A verifier takes $(S', c)$, computes the sum of elements where $c_i = 1$ and the sum where $c_i = 0$, and checks if they are equal.
These sums can be computed in a single linear pass over the input.
Since a linear-time (hence polynomial-time) verifier exists, PARTITION is in NP.

Thus, **PARTITION is NP-complete**.
