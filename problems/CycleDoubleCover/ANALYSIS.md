# Cycle Double Cover Conjecture — Proof Analysis

**Source:** `cdc_proof.pdf`, "A Proof of the Cycle Double Cover Conjecture", attributed to OpenAI / GPT 5.6 Sol Ultra.

**Verdict:** *No flaw found.* The proof uses $\Gamma = \mathbb{F}_2^{3}$ (the nowhere-zero **8-flow**, which holds for every bridgeless graph — Kilpatrick–Jaeger), reduces to loopless cubic graphs, and converts the flow into a cycle double cover via an elementary $\mathbb{F}_2$ linear-algebra argument. Every step checks out on inspection, the key lemma (2.2) has been re-derived by hand for $\mathbb{F}_2^3$, and the full construction produces a **valid CDC on the Petersen graph** and other snarks computationally. Because CDC is a famous open problem and the 8-flow theorem is old, an elementary proof would be extraordinary and warrants formal verification — but no gap has been identified. See §3.

> **Correction history.** An earlier version of this document declared the proof "fatally flawed," claiming it used a nowhere-zero $\mathbb{F}_2^2$-flow (= 4-flow), which snarks lack. **That was an error in this document, not the proof.** The PDF says $\mathbb{F}_2^{3}$ throughout (raw text extraction: "`F32`" = $\mathbb{F}_2^3$; corroborated by "8-flow", by the intro's $\mathbb{F}_2^3$, and by the Lemma 2.2 phrase "unique nonzero dual vector vanishing on the 2-dimensional $W$", which requires $\dim\Gamma=3$). The superscript 3 was misread as a 2, and the critique was built on that misreading, compounded by an arithmetic slip ($\dim W^0 = 3-2 = 1$, not 2). Both errors are corrected below.

---

## 1. Problem Statement

A **graph** here is a finite loopless undirected multigraph: parallel edges are allowed and are distinct. A **bridge** is an edge whose deletion increases the number of connected components. A **cycle** is a connected 2-regular submultigraph; thus two parallel edges form a cycle of length two. A **cycle double cover** (CDC) of $G$ is a finite multiset of cycles of $G$ such that every edge of $G$ occurs in exactly two members of the multiset, counted with multiplicity.

**Cycle Double Cover Conjecture** (Tutte; Itai–Rodeh; Szekeres; Seymour):

> **Theorem 1.1 (claimed).** Every finite bridgeless loopless multigraph has a cycle double cover.

Disconnected graphs are permitted, and the edgeless graph has the empty cycle double cover. Cycles in the cover need not be induced or edge-disjoint; the requirement is exactly two total occurrences of each edge. The full conjecture asks for this **without** additional assumptions such as cubicity, planarity, connectivity, or higher edge-connectivity.

---

## 2. The Proof (as given)

### 2.1 Introduction / strategy

Among partial results: Jaeger observed CDC holds for planar graphs (facial boundary cycles of blocks); Szekeres observed it for 3-edge-colourable cubic graphs (three unions of pairs of colour classes); Alspach, Goddyn, and Zhang proved it for bridgeless graphs with no Petersen subdivision.

The claimed proof proceeds by:
1. Using the standard reduction that it suffices to consider **cubic** graphs.
2. Using the **8-flow theorem** and a result of Tutte to obtain a labeling of the edges by nonzero elements of $\Gamma = \mathbb{F}_2^{3}$ such that the sum at each vertex is zero.
3. Converting this labeling into a labeling of the edges by **sets of two elements** in $\Gamma$ such that each element of $\Gamma$ appears either zero or twice next to a given vertex.
4. Reducing to an elementary linear algebra argument.

*(Statement of AI use: the proof is attributed entirely to GPT 5.6 Sol Ultra, writeup with Codex / GPT 5.6 Sol.)*

### 2.2 Proof of the conjecture

We allow parallel edges and regard two parallel edges as a cycle. By Jaeger [3, Prop. 4] it suffices to treat **loopless cubic graphs**. In fact, Jaeger observed that a minimum counterexample must fail to be 3-edge-colourable — that is, **it must be a snark**.

Fix an orientation of a graph. If $A$ is an abelian group, an **$A$-flow** is a map $f : E(G) \to A$ such that at every vertex the sum on out-edges equals the sum on in-edges. It is **nowhere-zero** if $f(e) \ne 0$ for every edge. For an integer $k \ge 2$, an **integer $k$-flow** is an integer-valued flow $\phi$ with $0 < |\phi(e)| < k$ on every edge.

Let $\Gamma = \mathbb{F}_2^{3}$, written additively. Kilpatrick and Jaeger independently proved that every bridgeless graph has a nowhere-zero $\Gamma$-flow [5, 4], or, equivalently by Tutte's group-flow theorem, a nowhere-zero 8-flow [9]. (Seymour's 6-flow theorem [7] is stronger but unnecessary.) We now massage this $\Gamma$-flow into a cycle double cover; this reduction only requires that $G$ is loopless and cubic.

**Lemma 2.1.** *Let $G$ be a loopless cubic multigraph. Suppose that every edge $e$ is assigned a two-element set $P_e \subseteq \Gamma$ such that, for every $v \in V(G)$ and $s \in \Gamma$,*
$$\big|\{e \ni v : s \in P_e\}\big| \in \{0, 2\}. \tag{1}$$
*Then $G$ has a cycle double cover.*

A proper 3-edge-colouring is an assignment of this form: for distinct $e_1, e_2 \in \Gamma$, assign $\{0,e_1\}, \{0,e_2\}, \{e_1,e_2\}$ to the red/blue/green edges; at each vertex each of $0, e_1, e_2$ appears twice. So Lemma 2.1 is a relaxed variant of a proper 3-edge-colouring.

*Proof.* For $s \in \Gamma$, let $M_s = \{e : s \in P_e\}$. By (1), every vertex has degree 0 or 2 in $M_s$, so $M_s$ is a disjoint union of cycles. Every edge belongs to exactly two of the $M_s$, since $P_e$ has two elements. The cycle components of all the $M_s$, taken with multiplicity, form a cycle double cover. $\square$

**Constructing the sets $P_e$.** Fix a nowhere-zero $\Gamma$-flow $f$. At each vertex $v$, locally order the incident edges as $a, b, c$ and write $x = f(a)$, $y = f(b)$, $z = f(c)$. Since $\Gamma$ has characteristic two, the flow equation is $x + y + z = 0$, so $z = x + y$; moreover $x$ and $y$ are distinct. Define
$$g_{v,a} = 0, \qquad g_{v,b} = x, \qquad g_{v,c} = 0. \tag{2}$$
For any $t \in \Gamma$, the three local sets
$$\{t + g_{v,e},\ t + g_{v,e} + f(e)\} \qquad (e \ni v) \tag{3}$$
are $\{t, t+x\}$, $\{t+x, t+z\}$, and $\{t, t+z\}$. Hence every vector occurs in zero or two of them. This assignment works locally, but the two ends of an edge need not assign it the same set.

For $e = uv$, put $d_e = g_{u,e} + g_{v,e}$. For any $p \in \Gamma$, $\{A, A+p\} = \{B, B+p\}$ precisely when $A + B \in \{0, p\}$. Apply with $A = t_u + g_{u,e}$, $B = t_v + g_{v,e}$, $p = f(e)$. Then $A + B = t_u + t_v + d_e$, and the choice of $\epsilon_e \in \mathbb{F}_2$ records whether this vector is $0$ or $f(e)$. Thus the local sets in (3) agree across every edge precisely when there are $t_v \in \Gamma$ and $\epsilon_e \in \mathbb{F}_2$ satisfying
$$t_u + t_v + \epsilon_e f(e) = d_e \qquad (e = uv). \tag{4}$$

**Lemma 2.2.** *The system (4) has a solution.*

Assuming the lemma, define $P_e = \{t_v + g_{v,e},\ t_v + g_{v,e} + f(e)\}$ using either endpoint $v$ of $e$. Equation (4) makes this independent of the endpoint, and $f(e) \ne 0$ makes the two elements distinct. The local calculation gives (1); Lemma 2.1 then proves the theorem.

*Proof of Lemma 2.2.* Let
$$L : \Gamma^{V(G)} \oplus \mathbb{F}_2^{E(G)} \longrightarrow \Gamma^{E(G)}, \qquad L(t, \epsilon)_e = t_u + t_v + \epsilon_e f(e) \quad (e = uv).$$
Thus (4) asks whether $d = (d_e)_e$ belongs to $\operatorname{im} L$. Let $\Gamma^*$ be the dual space of $\Gamma$ (an $\mathbb{F}_2$-linear map $\Gamma \to \mathbb{F}_2$). Write a dual vector to $\Gamma^{E(G)}$ as a family $\eta = (\eta_e)_{e}$ with $\eta_e \in \Gamma^*$. By duality, $d \in \operatorname{im} L$ iff every $\eta$ vanishing on $\operatorname{im} L$ also satisfies $\sum_e \eta_e(d_e) = 0$. Now
$$\sum_e \eta_e\big(L(t,\epsilon)_e\big) = \sum_v \Big(\sum_{e \ni v} \eta_e\Big)(t_v) + \sum_e \epsilon_e \eta_e(f(e)).$$
Since the $t_v$ and $\epsilon_e$ are independent, this vanishes for every $(t,\epsilon)$ precisely when
$$\eta_e(f(e)) = 0 \ (e \in E(G)), \qquad \sum_{e \ni v} \eta_e = 0 \ (v \in V(G)). \tag{5}$$
So it suffices to prove every family satisfying (5) also satisfies
$$\sum_e \eta_e(d_e) = 0. \tag{6}$$

Fix $v$ and retain $a,b,c,x,y,z$. Conditions (5) become
$$\eta_a + \eta_b + \eta_c = 0, \qquad \eta_a(x) = 0, \qquad \eta_b(y) = 0, \qquad \eta_c(z) = 0. \tag{7}$$
Set $\lambda = \eta_b(x)$. Since $\eta_c = \eta_a + \eta_b$ and $z = x + y$,
$$0 = \eta_c(z) = \eta_a(y) + \eta_b(x),$$
using $\eta_a(x) = \eta_b(y) = 0$. Hence $\eta_a(y) = \lambda$. By (2), only edge $b$ contributes at $v$, so
$$\sum_{e \ni v} \eta_e(g_{v,e}) = \eta_b(x) = \lambda. \tag{8}$$

We interpret $\lambda$. If $\lambda = 0$, all three dual vectors vanish on $W = \langle x, y\rangle$. There is a unique nonzero dual vector vanishing on this 2-dimensional space, so each of $\eta_a, \eta_b, \eta_c$ is either zero or this vector; since their sum is zero, the nonzero vector occurs zero or two times. If $\lambda = 1$, their values on the ordered basis $x, y$ are $(0,1), (1,0), (1,1)$, so all three are nonzero. In either case $\lambda$ is the parity of the number of nonzero members of $\{\eta_a, \eta_b, \eta_c\}$. Writing $\mathbf{1}_{\eta \ne 0}$ for the corresponding bit,
$$\sum_{e \ni v} \eta_e(g_{v,e}) = \sum_{e \ni v} \mathbf{1}_{\eta_e \ne 0}. \tag{9}$$

Finally, for $e = uv$, the definition $d_e = g_{u,e} + g_{v,e}$ and linearity give $\eta_e(d_e) = \eta_e(g_{u,e}) + \eta_e(g_{v,e})$. Summing over all edges and grouping the two endpoint terms at each vertex, (9) gives
$$\sum_e \eta_e(d_e) = \sum_v \sum_{e \ni v} \eta_e(g_{v,e}) = \sum_v \sum_{e \ni v} \mathbf{1}_{\eta_e \ne 0}.$$
Each edge with $\eta_e \ne 0$ occurs twice in the last sum, once at each endpoint. Hence it equals $2\sum_e \mathbf{1}_{\eta_e \ne 0} = 0$ in $\mathbb{F}_2$. This proves (6); by duality $d \in \operatorname{im} L$, so (4) has a solution. $\square$

### References cited

- [1] Alspach, Goddyn, Zhang, *Graphs with the circuit cover property*, Trans. AMS **344** (1994).
- [2] Itai, Rodeh, *Covering a graph by circuits*, ICALP 1978.
- [3] Jaeger, *A survey of the cycle double cover conjecture*, 1985.
- [4] Jaeger, *On nowhere-zero flows in graphs*, 1976.
- [5] Kilpatrick, *Tutte's first colour-cycle conjecture*, M.Sc. thesis, Cape Town, 1975.
- [6] Seymour, *Sums of circuits*, 1979.
- [7] Seymour, *Nowhere-zero 6-flows*, JCTB **30** (1981).
- [8] Szekeres, *Polyhedral decompositions of cubic graphs*, 1973.
- [9] Tutte, *A contribution to the theory of chromatic polynomials*, 1954.
- [10] Tutte, personal correspondence with H. Fleischner, July 22, 1987.

---

## 3. Critique

**Summary: no flaw found.** An earlier draft of this section claimed a fatal error; that claim was based on a misreading of the source (see the correction note at the top of this document) and is fully retracted. What follows is the corrected assessment.

### 3.1 The retracted objection (what was wrong with the earlier critique)

The earlier critique asserted that §2.2 uses a nowhere-zero $\mathbb{F}_2^2$-flow (a **4**-flow), which snarks lack, making the proof self-refuting. This rested on two mistakes **in the analysis, not the proof**:

1. **Misread group.** The PDF uses $\Gamma = \mathbb{F}_2^{3}$, not $\mathbb{F}_2^2$. The superscript 3 was misread as 2. Confirming $\mathbb{F}_2^3$: the raw text extraction renders the symbol as "`F32`" ($\mathbb{F}$, subscript 2, superscript 3); the same sentence says "nowhere-zero **8-flow**" and $|\mathbb{F}_2^3| = 8$; the introduction independently uses $\mathbb{F}_2^3$; and Lemma 2.2 speaks of "a **unique nonzero** dual vector vanishing on the 2-dimensional $W$", which is true only when $\dim\Gamma \ge 3$ (in $\mathbb{F}_2^2$, $W$ is the whole space and its annihilator is $\{0\}$). A nowhere-zero $\mathbb{F}_2^3$-flow is a nowhere-zero 8-flow, which **every** bridgeless graph has (Kilpatrick–Jaeger). No false premise, no snark contradiction.

2. **Arithmetic slip.** The earlier draft claimed that in $\mathbb{F}_2^3$ a 2-dimensional subspace $W$ has a "2-dimensional annihilator," collapsing the parity argument. In fact $\dim W^0 = \dim\Gamma - \dim W = 3 - 2 = 1$. The annihilator is a *line* $\{0, v^\*\}$, so the "unique nonzero dual vector" is exactly right and Lemma 2.2 goes through (see §3.2).

### 3.2 Why Lemma 2.2 works for $\mathbb{F}_2^3$ (the crux)

Fix a vertex $v$ with incident edges $a,b,c$, flow values $x,y,z$, all nonzero with $x+y+z=0$, so $x,y$ are distinct and independent and $W=\langle x,y\rangle$ is 2-dimensional. For $\eta$ satisfying (5), conditions (7) give $\eta_a|_W=(0,\lambda)$, $\eta_b|_W=(\lambda,0)$, $\eta_c|_W=(\lambda,\lambda)$ in coordinates $(\cdot(x),\cdot(y))$, where $\lambda=\eta_b(x)$.

- **If $\lambda=1$:** all three restrictions are nonzero, so $\eta_a,\eta_b,\eta_c$ are all nonzero. Count $=3$, parity $=1=\lambda$. ✓
- **If $\lambda=0$:** all three lie in $W^0$. Since $\dim W^0 = 1$, $W^0=\{0,v^\*\}$, so each $\eta_e\in\{0,v^\*\}$. With $\eta_a+\eta_b+\eta_c=0$ and $v^\*+v^\*+v^\*=v^\*\ne 0$, the number of nonzero terms is $0$ or $2$ — parity $0=\lambda$. ✓

So eq. (9), $\sum_{e\ni v}\eta_e(g_{v,e})=\sum_{e\ni v}\mathbf 1_{\eta_e\ne 0}$, holds. Summing over vertices, each edge with $\eta_e\ne 0$ is counted at both endpoints, giving $\sum_e\eta_e(d_e)=2\sum_e\mathbf 1_{\eta_e\ne 0}=0$ in $\mathbb{F}_2$, i.e. (6). By duality (4) is solvable. **The argument depends only on $\dim W^0 = 1$, i.e. $\dim\Gamma = 3$ with $W$ 2-dimensional — exactly the paper's setting.** (It would *fail* at $\mathbb{F}_2^4$, where $\dim W^0=2$; but $\mathbb{F}_2^4$ is not used.)

### 3.3 Computational verification

The full construction was implemented and run end-to-end: find a nowhere-zero $\mathbb{F}_2^3$-flow ($\mathbb{F}_2^3\cong\{0,\dots,7\}$ under XOR), solve the linear system (4) over $\mathbb{F}_2$ for $(t_v,\epsilon_e)$, build $P_e$ (checking endpoint-consistency and the $\{0,2\}$ condition (1)), form the $M_s$, and verify every $M_s$ is 2-regular and every edge is covered exactly twice.

- **Petersen graph** (the canonical snark, no 4-flow): **valid CDC produced.**
- $K_4$, triangular prism: valid CDC produced.

This is a spot check, not a proof, but it exercises the exact case (a snark) where the earlier critique wrongly claimed the construction was inapplicable.

### 3.4 What remains to scrutinize

No error has been found. The proof's non-elementary inputs are both legitimate:

- **8-flow theorem** (Kilpatrick–Jaeger): every bridgeless graph has a nowhere-zero $\mathbb{F}_2^3$-flow. Standard, true.
- **Reduction to loopless cubic** (Jaeger, survey Prop. 4): CDC for all bridgeless graphs follows from CDC for bridgeless cubic graphs. Standard, true.

The remaining discomfort is entirely a *prior*, not an identified gap: CDC has been open for decades **while the 8-flow theorem has been available since 1979**, so an elementary reduction "8-flow $\Rightarrow$ CDC" would be a major surprise and should be treated with the scrutiny that any such claim deserves. If there is an error, it is subtle and not one this analysis has located. Lemma 2.1, Lemma 2.2, and the local construction all appear individually correct, and their composition appears to yield a genuine CDC.

### 3.5 Recommendation for formalization

- **Formalizing this in Lean is the right way to settle it** — and is the project's stated goal. Because the argument is elementary ($\mathbb{F}_2$ linear algebra + a double count), the two lemmas are attractive formalization targets; the load-bearing external citations are the 8-flow theorem and Jaeger's cubic reduction (legitimate **citation axioms** if not yet in Mathlib).
- **Suggested order:** (1) Lemma 2.1 (two-element sets with the $\{0,2\}$ property $\Rightarrow$ CDC); (2) Lemma 2.2 (solvability of (4) via the $\dim W^0 = 1$ parity argument); (3) the local $P_e$ construction tying them together; (4) cite 8-flow + cubic reduction. If any step resists formalization, that is precisely where the (currently unidentified) gap — if one exists — would surface. This is the honest, decisive test.
