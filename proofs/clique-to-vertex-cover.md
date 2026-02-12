# Proof: CLIQUE reduces to VERTEX COVER

**Statement:** CLIQUE $\le_p$ VERTEX COVER.
**Status:** Verified ✅
**Reviewed by:** verify
**Goal:** Construct a polynomial-time reduction $f$ that maps an instance $(G, K)$ of CLIQUE to an instance $(G', K')$ of VERTEX COVER such that $G$ has a clique of size $K$ if and only if $G'$ has a vertex cover of size $K'$.

## 1. Definitions

### 1.1 The Problems
**CLIQUE:**
Input: Graph $G=(V, E)$, integer $K$.
Question: Does there exist $S \subseteq V$ such that $|S| = K$ and $\forall u,v \in S, u \neq v \implies (u,v) \in E$?

**VERTEX COVER:**
Input: Graph $G'=(V', E')$, integer $K'$.
Question: Does there exist $C \subseteq V'$ such that $|C| = K'$ and $\forall (u,v) \in E', u \in C \lor v \in C$?

### 1.2 The Reduction
Let $(G, K)$ be an instance of CLIQUE where $G=(V, E)$.
We construct $(G', K') = f(G, K)$ as follows:
1.  **Graph $G'$:** Let $G' = \bar{G} = (V, \bar{E})$ be the complement graph of $G$.
    -   $V' = V$.
    -   $(u, v) \in \bar{E} \iff u \neq v \land (u, v) \notin E$.
2.  **Integer $K'$:** Set $K' = |V| - K$.

## 2. Correctness

We rely on the intermediate concept of an **Independent Set**.
An independent set $I \subseteq V$ is a set where no two vertices are connected by an edge.

**Lemma 1:** $S$ is a clique in $G \iff S$ is an independent set in $\bar{G}$.
*Proof:*
$S$ is a clique in $G$
$\iff \forall u, v \in S, u \neq v \implies (u, v) \in E$
$\iff \forall u, v \in S, u \neq v \implies (u, v) \notin \bar{E}$ (definition of complement)
$\iff S$ is an independent set in $\bar{G}$.

**Lemma 2:** $I$ is an independent set in $G' \iff V' \setminus I$ is a vertex cover in $G'$.
*Proof:*
$I$ is an independent set in $G'$
$\iff \forall u, v \in I, (u, v) \notin E'$
$\iff \neg (\exists u, v \in I, (u, v) \in E')$
$\iff$ No edge in $E'$ has both endpoints in $I$.
$\iff$ For every edge $(u, v) \in E'$, at least one endpoint is NOT in $I$.
$\iff$ For every edge $(u, v) \in E'$, at least one endpoint is in $V' \setminus I$.
$\iff V' \setminus I$ is a vertex cover in $G'$.

**Main Argument:**
$G$ has a clique of size $K$
$\iff \bar{G}$ has an independent set $S$ of size $K$ (by Lemma 1)
$\iff \bar{G}$ has a vertex cover $C = V \setminus S$ of size $|V| - K$ (by Lemma 2).
Since $G' = \bar{G}$ and $K' = |V| - K$, this proves the reduction is correct.

## 3. Complexity

-   **Size:**
    -   $|V'| = |V|$.
    -   $|E'| \le |V|^2$.
    -   The size of $G'$ is bounded by $O(|V|^2)$.
-   **Time:**
    -   Constructing $\bar{G}$ involves iterating over all pairs of vertices in $G$ and checking for edge existence. This takes $O(|V|^2)$ time.
    -   Calculating $K'$ is constant/linear time.
    -   The total time is $O(|V|^2)$, which is polynomial in the size of the input.

## 4. Conclusion

We have constructed a polynomial-time reduction from CLIQUE to VERTEX COVER.
Since CLIQUE is NP-complete (proven previously), and VERTEX COVER is in NP (verifier checks if a set covers all edges in $O(|E|)$), **VERTEX COVER is NP-complete**.
