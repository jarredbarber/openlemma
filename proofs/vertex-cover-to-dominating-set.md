# Proof: VERTEX COVER reduces to DOMINATING SET

**Statement:** VERTEX COVER $\le_p$ DOMINATING SET.
**Status:** Draft ✏️
**Goal:** Construct a polynomial-time reduction $f$ that maps any instance $(G, k)$ of VERTEX COVER to an instance $(G', k')$ of DOMINATING SET such that $G$ has a vertex cover of size $k$ if and only if $G'$ has a dominating set of size $k'$.

## 1. Definitions

### 1.1 VERTEX COVER
**Input:** A graph $G=(V, E)$ and integer $k$.
**Question:** Does there exist $C \subseteq V$ such that $|C| \le k$ and $\forall (u,v) \in E, u \in C \lor v \in C$?

### 1.2 DOMINATING SET
**Input:** A graph $G'=(V', E')$ and integer $k'$.
**Question:** Does there exist $D \subseteq V'$ such that $|D| \le k'$ and $\forall v \in V', v \in D \lor \exists u \in D, (u,v) \in E'$?

## 2. The Reduction

Let $(G, k)$ be an instance of VERTEX COVER.
Let $G = (V, E)$.
We construct $G' = (V', E')$ as follows:

1.  **Vertices ($V'$):**
    -   For each edge $(u,v) \in E$, create a vertex $e_{uv}$.
    -   For each vertex $u \in V$, create a vertex $v_u$.
    -   Ideally, we want to force the dominating set to pick vertices from the $v_u$ set to cover the $e_{uv}$ vertices.
    -   But we need to ensure the $v_u$ vertices themselves are covered.
    -   **Standard Construction:**
        -   $V' = V \cup I$ where $I$ is a set of isolated vertices? No.
        -   **Correct Construction:** remove isolated vertices from $G$ first (or handle them).
        -   Let's use the standard "edge-to-vertex" approach.
        -   Vertices $V'$: $V \cup E$ (treating edges as vertices).
        -   Edges $E'$:
            -   Connect $v_u \in V$ to $v_v \in V$ if $(u,v) \in E$? No.
            -   Connect $v_u \in V$ to $e_{uv} \in E$ if $u$ is an endpoint of the edge $(u,v)$.
            -   Add edges to make $V$ a clique? No.
            -   Add dummy vertices?

    **Standard Reduction (Garey & Johnson):**
    For each edge $(u, v) \in E$, introduce a new vertex $z_{uv}$.
    Edges in $G'$:
    -   Keep all edges from $G$.
    -   Connect $z_{uv}$ to $u$ and to $v$.
    -   Wait, this doesn't force covering $z_{uv}$ by $u$ or $v$. $z_{uv}$ could cover itself.
    -   We need to make picking $z_{uv}$ "expensive" or useless.

    **Correct Standard Reduction:**
    1.  Start with $G=(V, E)$.
    2.  For each edge $e = (u,v) \in E$, add a new vertex $z_e$.
    3.  Add edges $(u, z_e)$ and $(v, z_e)$.
    4.  The vertices of $G'$ are $V \cup \{z_e \mid e \in E\}$.
    5.  The edges of $G'$ are $E \cup \{(u, z_{uv}), (v, z_{uv}) \mid (u,v) \in E\}$. (Original edges + new edges).
    6.  **Crucial Step:** We must ensure "isolated" vertices in $V$ are covered.
        -   Actually, simple Dominating Set covers adjacency.
    7.  Target $k' = k$.

    **Wait, check correctness:**
    If we pick $z_e$, it only covers $u, v, z_e$. If we pick $u$, it covers $u$, all neighbors $v$, and all incident edge-nodes $z_{uv}$.
    Picking $u$ is strictly better than picking $z_{uv}$?
    -   $z_{uv}$ covers $\{z_{uv}, u, v\}$.
    -   $u$ covers $\{u\} \cup N(u) \cup \{z_{ux} \mid x \in N(u)\}$.
    -   If we have a VC $C$ of size $k$:
        -   For every edge $e=(u,v)$, at least one of $u,v \in C$.
        -   If $u \in C$, $u$ covers $z_e$.
        -   So all $z_e$ are covered.
        -   All $v \in V$ are covered?
            -   If $v \in C$, it covers itself.
            -   If $v \notin C$, is it covered?
            -   If $v$ is isolated, it's not covered by neighbors.
            -   VERTEX COVER usually assumes no isolated vertices or handles them (must not be in C unless loop?). Isolated vertex doesn't need to be in VC.
            -   But in DOM SET, isolated vertex MUST be in D.
            -   This is a mismatch.

    **Refined Reduction (isolated vertices handled):**
    Remove isolated vertices from $G$ first (they don't affect VC size, but affect DS).
    Assume $G$ has no isolated vertices.
    Construct $G'$ as above: $V' = V \cup E_{nodes}$, edges: original $E$ + connections to edge-nodes.
    Target $k' = k$.

## 3. Correctness

### 3.1 Completeness ($\implies$)
Assume $G$ has a vertex cover $C$ of size $k$.
Let $D = C$.
-   **Covering $z_{uv}$:** Since $C$ is a VC, for every $e=(u,v)$, either $u \in C$ or $v \in C$. Thus $z_{uv}$ is adjacent to a vertex in $D$. Covered.
-   **Covering $v \in V$:**
    -   If $v \in C$, $v$ covers itself.
    -   If $v \notin C$, since $G$ has no isolated vertices, $v$ has a neighbor $u$.
    -   Is $u \in C$? Not necessarily.
    -   Wait. If $v \notin C$, all edges incident to $v$ must be covered by their other endpoints.
    -   Let $(u,v) \in E$. Since $v \notin C$, $u$ must be in $C$.
    -   Thus $u \in D$.
    -   In $G'$, does $u$ cover $v$?
    -   Yes, we kept the original edges $E$ in $G'$. So $(u,v) \in E'$.
    -   So $v$ is covered by $u$.
Thus, $D$ is a dominating set of size $k$.

### 3.2 Soundness ($\impliedby$)
Assume $G'$ has a dominating set $D$ of size $k$.
We construct a vertex cover $C$ for $G$.
Transformation:
-   If $v \in D \cap V$, keep $v$ in $C$.
-   If $z_{uv} \in D$, this node was likely picked to cover itself or $u/v$.
    -   Replace $z_{uv}$ with $u$ (or $v$).
    -   $u$ covers $z_{uv}$ and $u$ and neighbors.
    -   $z_{uv}$ covers $z_{uv}, u, v$.
    -   The replacement maintains size and likely improves coverage.
Let $C = (D \cap V) \cup \{u \mid z_{uv} \in D\}$. Size $|C| \le |D| = k$.

**Is $C$ a vertex cover?**
Consider any edge $e = (u,v) \in E$.
In $G'$, there is a vertex $z_e$.
$z_e$ must be dominated by $D$.
-   Case 1: $z_e \in D$. Then one of $u, v$ (or both) is added to $C$ by our replacement rule. Edge covered.
-   Case 2: $z_e \notin D$. Then a neighbor of $z_e$ must be in $D$.
    -   Neighbors of $z_e$ are $u$ and $v$.
    -   So $u \in D$ or $v \in D$.
    -   These are preserved in $C$. Edge covered.
Thus, $C$ covers all edges.

## 4. Pre-processing
The assumption "no isolated vertices" is crucial.
Algorithm:
1.  Iterate $V$. If degree(v) == 0, remove $v$. (Isolated vertices require 0 VC, but 1 DS).
2.  Run reduction on $G_{clean}$.
3.  Output $(G', k)$.

## 5. Complexity
-   **Size:** $|V'| = |V| + |E|$. $|E'| = |E| + 2|E| = 3|E|$. Linear increase.
-   **Time:** Graph traversal and construction is polynomial ($O(V+E)$).

## 6. Conclusion
VERTEX COVER $\le_p$ DOMINATING SET.
Since VERTEX COVER is NP-complete, and DOMINATING SET is in NP, **DOMINATING SET is NP-complete**.
