# Proof: 3-SAT reduces to CLIQUE

**Statement:** 3-SAT $\le_p$ CLIQUE.
**Status:** Draft ✏️
**Goal:** Construct a polynomial-time reduction $f$ that maps any 3-CNF formula $\phi$ to a pair $(G, K)$ such that $\phi$ is satisfiable if and only if the graph $G$ contains a clique of size $K$.

## 1. Definitions

### 1.1 The CLIQUE Problem
**Input:** An undirected graph $G = (V, E)$ and an integer $K$.
**Question:** Does $G$ contain a clique of size $K$?
A subset of vertices $S \subseteq V$ is a **clique** if for every pair of distinct vertices $u, v \in S$, $(u, v) \in E$.
**Language:** `CLIQUE = { (G, K) | G has a clique of size K }`.

### 1.2 The Reduction
Let $\phi = C_1 \land C_2 \land \dots \land C_k$ be a 3-CNF formula with $k$ clauses.
Each clause $C_r$ contains literals $l_{r,1}, l_{r,2}, l_{r,3}$ (possibly fewer if padding wasn't used, but 3-SAT typically assumes exactly 3; we handle $\le 3$ generally).

We construct a graph $G = (V, E)$ as follows:

1.  **Vertices:**
    For each clause $C_r$ and each literal $l_{r,i}$ in it, create a vertex.
    We denote vertices as pairs $(r, i)$ where $1 \le r \le k$ and $1 \le i \le |C_r|$.
    The total number of vertices is $\sum |C_r| \le 3k$.

2.  **Edges:**
    Two distinct vertices $(r, i)$ and $(s, j)$ are connected by an edge if and only if:
    *   They are in different clauses ($r \neq s$).
    *   Their literals are consistent ($l_{r,i} \neq \neg l_{s,j}$).
    
    (Note: Consistency means they are not negations of each other. If $l_{r,i} = x_1$ and $l_{s,j} = \neg x_1$, no edge. If both are $x_1$, edge exists. If one is $x_1$ and other is $x_2$, edge exists).

3.  **Target K:**
    Set $K = k$ (the number of clauses).

## 2. Correctness

We must show: $\phi$ is satisfiable $\iff G$ has a clique of size $k$.

### 2.1 Completeness ($\implies$)
Assume $\phi$ is satisfiable.
There exists an assignment $\sigma$ such that every clause $C_r$ has at least one true literal.
For each clause $r$, select one index $i_r$ such that $l_{r, i_r}$ is true under $\sigma$.
Let $S = \{ (r, i_r) \mid 1 \le r \le k \}$.
The size of $S$ is exactly $k$.

We claim $S$ is a clique.
Consider any two distinct vertices $(r, i_r), (s, i_s) \in S$.
1.  Since $r \neq s$ (we picked one per clause), they are in different clusters.
2.  Both $l_{r, i_r}$ and $l_{s, i_s}$ are true under $\sigma$.
    It is impossible for one to be the negation of the other (a variable cannot be both true and false).
    Thus, $l_{r, i_r} \neq \neg l_{s, i_s}$.
3.  Therefore, an edge exists between them.

Since all pairs are connected, $S$ is a $k$-clique.

### 2.2 Soundness ($\impliedby$)
Assume $G$ has a clique $S$ of size $k$.
1.  Vertices in a clique must be pairwise connected.
2.  Edges only exist between vertices in *different* clauses (clusters).
3.  Therefore, a clique of size $k$ must contain exactly one vertex from each of the $k$ clauses.
    Let $S = \{ (r, i_r) \mid 1 \le r \le k \}$.

Construct a partial assignment $\sigma$:
For each $(r, i_r) \in S$, set the literal $l_{r, i_r}$ to true.
Is this assignment consistent?
Suppose it requires setting variable $x$ to true (from one clique node) and false (from another).
This would mean $S$ contains two nodes corresponding to $x$ and $\neg x$.
But by construction, no edge exists between complementary literals.
Since $S$ is a clique, all its nodes are connected, so no such contradiction exists.
Thus, the assignment is consistent.
Any variables not in $S$ can be set arbitrarily.

This assignment $\sigma$ satisfies every clause $C_r$ (since it makes $l_{r, i_r}$ true).
Therefore, $\phi$ is satisfiable.

## 3. Complexity

-   **Size:**
    -   Vertices: $|V| \le 3k$.
    -   Edges: $|E| \le \binom{3k}{2} = O(k^2)$.
    -   The graph size is polynomial in the size of $\phi$.
-   **Time:**
    -   Generating vertices takes $O(k)$.
    -   Generating edges takes $O(k^2)$ checks. Each check (consistency of literals) is constant time (or log time depending on variable index encoding).
    -   Total time is $O(k^2)$, which is polynomial in $|\phi|$.

## 4. Conclusion

We have constructed a polynomial-time reduction from 3-SAT to CLIQUE.
Since 3-SAT is NP-complete (proven previously), and CLIQUE is in NP (verifier checks if a set of vertices forms a clique in $O(|V|^2)$), **CLIQUE is NP-complete**.
