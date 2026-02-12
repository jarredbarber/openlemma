# Proof: SUBSET SUM reduces to BIN PACKING

**Statement:** SUBSET SUM $\le_p$ BIN PACKING.
**Status:** Verified ✅
**Reviewed by:** verify
**Goal:** Construct a polynomial-time reduction $f$ that maps any instance $(S, t)$ of SUBSET SUM to an instance $(I, C, k)$ of BIN PACKING such that a subset of $S$ sums to $t$ if and only if the items $I$ can be packed into $k$ bins of capacity $C$.

## 1. Definitions

### 1.1 SUBSET SUM
**Input:** A multiset of natural numbers $S = \{x_1, \dots, x_n\}$ and a target $t$.
**Question:** Does there exist $A \subseteq S$ such that $\sum_{x \in A} x = t$?

### 1.2 BIN PACKING
**Input:** A multiset of item sizes $I = \{a_1, \dots, a_m\}$, a bin capacity $C$, and a number of bins $k$.
**Question:** Can $I$ be partitioned into $k$ subsets $B_1, \dots, B_k$ such that for each $j \in \{1, \dots, k\}$, $\sum_{x \in B_j} x \le C$?

## 2. The Reduction

Let $(S, t)$ be an instance of SUBSET SUM.
Let $\sigma = \sum_{x \in S} x$.

### 2.1 Construction
We effectively combine the reduction to PARTITION with the definition of Bin Packing.

1.  **Balancing Items:** Create two new items:
    -   $J_1 = 2\sigma - t$
    -   $J_2 = \sigma + t$
    (If $t > \sigma$, return a trivial "no" instance, e.g., item $> C$).

2.  **Item Set $I$:** $S \cup \{J_1, J_2\}$.
3.  **Capacity $C$:** $2\sigma$.
4.  **Number of Bins $k$:** $2$.

### 2.2 Total Sum Check
The sum of all items in $I$ is:
$$ \sum_{x \in S} x + J_1 + J_2 = \sigma + (2\sigma - t) + (\sigma + t) = 4\sigma $$
The total capacity of $k=2$ bins is $2 \times 2\sigma = 4\sigma$.
Thus, for the items to fit, each bin must be **exactly full**. The inequality $\le C$ becomes equality $= C$.

## 3. Correctness

We show: $\exists A \subseteq S, \sum A = t \iff I \text{ fits in 2 bins of capacity } 2\sigma$.

### 3.1 Completeness ($\implies$)
Assume there exists $A \subseteq S$ with $\sum_{x \in A} x = t$.
Let $B = S \setminus A$. Note $\sum_{x \in B} x = \sigma - t$.

Construct the packing:
-   **Bin 1:** $A \cup \{J_1\}$.
    Sum: $t + (2\sigma - t) = 2\sigma = C$. Fits.
-   **Bin 2:** $B \cup \{J_2\}$.
    Sum: $(\sigma - t) + (\sigma + t) = 2\sigma = C$. Fits.

Thus, the instance is accepted.

### 3.2 Soundness ($\impliedby$)
Assume the items $I$ fit into 2 bins $B_1, B_2$.
Since total item weight ($4\sigma$) equals total capacity ($4\sigma$), each bin must contain items summing to exactly $2\sigma$.

Consider the location of $J_1$ and $J_2$.
-   $J_1 + J_2 = (2\sigma - t) + (\sigma + t) = 3\sigma$.
-   Since $3\sigma > 2\sigma$ (assuming $\sigma > 0$), $J_1$ and $J_2$ cannot be in the same bin.
-   Thus, they are separated. Let $J_1 \in B_1$ and $J_2 \in B_2$.

Consider Bin 1 ($B_1$):
It contains $J_1$ and some subset $A \subseteq S$.
Sum constraint: $J_1 + \sum_{x \in A} x = 2\sigma$.
Substitute $J_1$: $(2\sigma - t) + \sum_{x \in A} x = 2\sigma$.
Solving for the sum: $\sum_{x \in A} x = t$.

Thus, $A$ is a subset of $S$ summing to $t$.

## 4. Complexity

-   **Size:** We add 2 items. The values require $O(\log \sigma)$ bits. Linear size increase.
-   **Time:** Linear time to compute sum and new items.

## 5. Conclusion

We have constructed a polynomial-time reduction from SUBSET SUM to BIN PACKING.
Since SUBSET SUM is NP-hard, BIN PACKING is NP-hard.
BIN PACKING is in NP (witness is the assignment of items to bins).
Thus, **BIN PACKING is NP-complete**.
