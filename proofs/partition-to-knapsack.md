# Proof: PARTITION reduces to KNAPSACK

**Statement:** PARTITION $\le_p$ KNAPSACK.
**Status:** Verified ✅
**Reviewed by:** verify
**Goal:** Construct a polynomial-time reduction $f$ that maps any instance $S$ of PARTITION to an instance $(I, W, V)$ of KNAPSACK such that $S$ can be partitioned into two subsets of equal sum if and only if there exists a subset of items in $I$ with total weight at most $W$ and total value at least $V$.

## 1. Definitions

### 1.1 PARTITION
**Input:** A multiset of natural numbers $S = \{x_1, \dots, x_n\}$.
**Question:** Does there exist a subset $A \subseteq S$ such that $\sum_{x \in A} x = \frac{1}{2} \sum_{x \in S} x$?

### 1.2 KNAPSACK
**Input:** A set of items, where each item $i$ has a weight $w_i$ and a value $v_i$. A capacity $W$ and a target value $V$.
**Question:** Does there exist a subset of items $J$ such that $\sum_{j \in J} w_j \le W$ and $\sum_{j \in J} v_j \ge V$?

## 2. The Reduction

Let $S = \{x_1, \dots, x_n\}$ be an instance of PARTITION.
Let $\sigma = \sum_{i=1}^n x_i$ be the total sum.

### 2.1 Pre-check
If $\sigma$ is odd, the PARTITION instance is unsatisfiable. In this case, map to a trivial "no" instance of KNAPSACK (e.g., one item with weight 1, value 1, capacity 0, target 1).

### 2.2 Construction
If $\sigma$ is even, let $T = \sigma / 2$.
We construct a KNAPSACK instance as follows:
1.  **Items:** For each $x_i \in S$, create an item $i$ with:
    -   Weight $w_i = x_i$
    -   Value $v_i = x_i$
2.  **Capacity:** $W = T$.
3.  **Target Value:** $V = T$.

## 3. Correctness

We show: $S \in \text{PARTITION} \iff (Items, W, V) \in \text{KNAPSACK}$.

### 3.1 Completeness ($\implies$)
Assume $S$ has a partition $A$. Then $\sum_{x \in A} x = T$.
Select the items corresponding to elements in $A$.
-   Total weight: $\sum_{x \in A} w_i = \sum_{x \in A} x = T \le W$.
-   Total value: $\sum_{x \in A} v_i = \sum_{x \in A} x = T \ge V$.
Thus, the KNAPSACK instance has a solution.

### 3.2 Soundness ($\impliedby$)
Assume there is a subset of items $J$ satisfying the KNAPSACK constraints.
-   Condition 1: $\sum_{j \in J} w_j \le W \implies \sum_{j \in J} x_j \le T$.
-   Condition 2: $\sum_{j \in J} v_j \ge V \implies \sum_{j \in J} x_j \ge T$.
Combining these inequalities:
$$ T \le \sum_{j \in J} x_j \le T $$
Therefore, $\sum_{j \in J} x_j = T$.
The set of numbers $\{x_j \mid j \in J\}$ is a subset of $S$ that sums to half the total sum.
Thus, $S$ has a partition.

## 4. Complexity

-   **Size:** The reduction creates $n$ items. The numbers used are identical to the input. Linear size increase.
-   **Time:** Computing the sum $\sigma$ and creating the items is linear in the input size.

## 5. Conclusion

We have constructed a polynomial-time reduction from PARTITION to KNAPSACK.
Since PARTITION is NP-complete, KNAPSACK is NP-hard.
KNAPSACK is in NP (witness is the subset $J$, verifiable in linear time).
Thus, **KNAPSACK is NP-complete**.
