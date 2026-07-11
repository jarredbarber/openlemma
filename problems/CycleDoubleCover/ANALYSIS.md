# Cycle Double Cover Conjecture — Proof Analysis

**Source:** `cdc_proof.pdf`, "A Proof of the Cycle Double Cover Conjecture", attributed to OpenAI / GPT 5.6 Sol Ultra.

**Verdict:** The proof is **incorrect**. It contains a fatal, non-repairable error: it invokes a nowhere-zero $\mathbb{F}_2^2$-flow (= nowhere-zero 4-flow) for all bridgeless cubic graphs, which does not exist (the Petersen graph is the classical counterexample), on precisely the class of graphs — snarks — to which the proof has just reduced. **Do not formalize this as a proof of CDC.** See the critique in §3.

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

Let $\Gamma = \mathbb{F}_2^{2}$, written additively. Kilpatrick and Jaeger independently proved that every bridgeless graph has a nowhere-zero $\Gamma$-flow [5, 4], or, equivalently by Tutte's group-flow theorem, a nowhere-zero 8-flow [9]. (Seymour's 6-flow theorem [7] is stronger but unnecessary.) We now massage this $\Gamma$-flow into a cycle double cover; this reduction only requires that $G$ is loopless and cubic.

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

### 3.1 The fatal error

The load-bearing sentence is in §2.2:

> Let $\Gamma = \mathbb{F}_2^{2}$ ... Kilpatrick and Jaeger independently proved that every bridgeless graph has a nowhere-zero $\Gamma$-flow [5, 4], or, equivalently by Tutte's group-flow theorem, a nowhere-zero 8-flow.

This is false, and it is false in two mutually reinforcing ways:

1. **A nowhere-zero $\mathbb{F}_2^2$-flow is a nowhere-zero 4-flow, not an 8-flow.** By Tutte's group-independence theorem, a graph has a nowhere-zero flow in an abelian group $A$ iff it has a nowhere-zero $|A|$-flow. Since $|\mathbb{F}_2^2| = 4$, a nowhere-zero $\mathbb{F}_2^2$-flow is *exactly* a nowhere-zero 4-flow. The claimed equivalence "$\mathbb{F}_2^2$-flow $\equiv$ 8-flow" is wrong; 8-flow corresponds to $\mathbb{F}_2^{3}$ (order 8).

2. **Not every bridgeless graph has a nowhere-zero 4-flow.** The Petersen graph is bridgeless, cubic, and has *no* nowhere-zero 4-flow. So the asserted theorem of Kilpatrick–Jaeger is simply not a true statement. What Kilpatrick [5] and Jaeger [4] actually proved is the **8-flow theorem**: every bridgeless graph has a nowhere-zero 8-flow $=$ nowhere-zero $\mathbb{F}_2^{3}$-flow. The exponent 3 is not optional.

### 3.2 Why this is self-refuting, not a typo

The error is not a harmless notation slip, because the proof has *already reduced to the exact class of graphs where the false hypothesis fails*:

- §2.2 states a minimum counterexample "must be a snark," i.e. **not 3-edge-colourable**.
- For a **cubic** graph, a nowhere-zero 4-flow exists **iff** the graph is 3-edge-colourable (nowhere-zero 4-flow $\Leftrightarrow$ proper 3-edge-colouring for cubic graphs).
- Therefore snarks are *precisely* the cubic graphs with **no** nowhere-zero $\mathbb{F}_2^2$-flow.

So the proof reduces to snarks and then assumes the one thing snarks never have. The hypothesis of the construction is unavailable exactly where the conjecture is hard. The proof is self-contradictory.

### 3.3 Why substituting the correct group does not repair it

One might hope to "fix" the proof by reading $\Gamma = \mathbb{F}_2^{3}$ throughout (which *does* exist for all bridgeless graphs, by the genuine 8-flow theorem). This fails:

- **CDC from a 4-flow is the known easy case.** A nowhere-zero 4-flow yields a CDC by a classical argument (and cubic graphs with a 4-flow are 3-edge-colourable, already handled by Szekeres [8]). So the §2.2 construction, *as written for $\mathbb{F}_2^2$*, only reproves a decades-old special case — it is not a proof of CDC.
- **The construction is built for $\mathbb{F}_2^2$ and does not lift to $\mathbb{F}_2^3$.** The whole mechanism depends on the two-element sets $P_e$ and the vertex relation $x + y + z = 0$ with $x, y$ **distinct** spanning a **2-dimensional** space $W = \langle x, y\rangle$. Lemma 2.2's key step (§2, eq. 9) uses that a 2-dimensional subspace of $\Gamma$ has a *unique* nonzero annihilator, forcing the $\lambda = 0$ dichotomy. In $\mathbb{F}_2^3$ the incident flow values $x, y, z = x+y$ still span only a 2-dimensional subspace, but $\Gamma^*$ is now 3-dimensional and a 2-dimensional subspace has a *2-dimensional* annihilator — the "unique nonzero dual vector" argument collapses, and with it eq. (9) and the whole parity cancellation. The elegant linear algebra is specific to $\dim \Gamma = 2$.

In other words, the genuine difficulty of CDC lives entirely in the snarks — the cubic graphs that have only an 8-flow ($\mathbb{F}_2^3$) and no 4-flow — and the construction silently swaps in the (nonexistent) 4-flow hypothesis exactly there.

### 3.4 A one-line refutation

> **The Petersen graph** is bridgeless, loopless, cubic, and has no nowhere-zero 4-flow $=$ no nowhere-zero $\mathbb{F}_2^2$-flow. It is a snark, so the proof reduces to it, then assumes a flow it does not possess.

### 3.5 What is and isn't salvageable

- **Lemma 2.1** (two-element sets with the $\{0,2\}$ property $\Rightarrow$ CDC) is correct and self-contained.
- **Lemma 2.2** (solvability of the linear system (4)) appears correct **as a statement about $\mathbb{F}_2^2$-flows** — but is vacuous on snarks because no $\mathbb{F}_2^2$-flow exists there.
- Together they honestly prove only: *"a cubic graph with a nowhere-zero 4-flow has a cycle double cover"* — a known, easy result.

### 3.6 Recommendation for formalization

- **Do not formalize Theorem 1.1 from this proof.** Formalization would force the false premise "every bridgeless cubic graph has a nowhere-zero $\mathbb{F}_2^2$-flow" to be introduced as an axiom. That is not a citation axiom — it is a **false** statement, and a crux-level one (it trivially implies the conjecture). Per the repo axiom policy this is an immediate escalate/reject.
- **Salvageable target:** formalize Lemmas 2.1 and 2.2 to produce a clean Lean proof of *"nowhere-zero 4-flow $\Rightarrow$ CDC for cubic graphs,"* which makes the missing hypothesis (4-flow existence) explicit and turns this into an honest negative result consistent with the project's error-documentation ethos.
</content>
</invoke>
