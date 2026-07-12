# CDC Proof Comparison — OpenAI vs. DeepThinker

Two LLM-produced proofs of the Cycle Double Cover Conjecture (*every finite loopless
bridgeless multigraph has a cycle double cover*):

- **OpenAI** — `cdc_proof.pdf` (GPT 5.6 Sol Ultra), plus a complete Lean 4 formalization at
  <https://github.com/openai/cdc-lean>. Analyzed in `ANALYSIS.md`.
- **DeepThinker** — a natural-language writeup wrapped in a "multiagent v2 execution log."

**Bottom line: both proofs are valid, and they are essentially the *same* proof.** The
$\mathbb{F}_2^3$/8-flow algebraic core is identical; they differ only in the presentation of
the reduction to cubic graphs, and both reductions are correct. The decisive difference is
*verification status*: OpenAI's proof is machine-checked in Lean; DeepThinker's is an
unverified writeup dressed up with theatrical orchestration logs.

---

## 1. The shared core (identical mathematics)

Parts II–V of DeepThinker are, in substance, the OpenAI proof — same construction, same
lemmas, same variable names, same key steps.

| Element | DeepThinker | OpenAI |
|---|---|---|
| Group | $\Gamma=\mathbb{F}_2^3$, nowhere-zero 8-flow (Jaeger 1979) | $\Gamma=(\text{ZMod }2)^3$, 8-flow (Jaeger–Kilpatrick) |
| "even sets ⇒ CDC" | Lemma 1: $M_s=\{e:s\in P_e\}$ is 2-regular; each edge in exactly two $M_s$ | Lemma 2.1 (identical) |
| Local offsets | $g_{v,a}=0,\;g_{v,b}=x,\;g_{v,c}=0$ | identical |
| Three local sets | $\{t,t{+}x\},\{t{+}x,t{+}z\},\{t,t{+}z\}$ | identical |
| Compatibility system | $t_u+t_v+\epsilon_e f(e)=d_e$ | identical (eq. 4) |
| Solvability | Lemma 2: duality / Fredholm; $\lambda_v$ parity; handshaking cancellation | Lemma 2.2 (identical) |

The crux step is the same in both: at each vertex the dual functionals restrict to
$W=\langle x,y\rangle$ as $(0,\lambda_v),(\lambda_v,0),(\lambda_v,\lambda_v)$, and $\lambda_v$
equals the parity of the number of nonzero $\eta_e$ at $v$; summing over vertices,
$\sum_e\eta_e(d_e)=\sum_v\lambda_v=2\,|\{\eta_e\neq0\}|\equiv 0\pmod 2$, so the system is
solvable and Lemma 1/2.1 produces the cover.

Notably, DeepThinker states the key dimension fact **correctly**: "the annihilator of $W$ in
$\Gamma^*$ is strictly 1-dimensional" ($\dim W^0 = 3-2 = 1$). This is exactly the point an
earlier draft of `ANALYSIS.md` got wrong; both AI proofs have it right.

## 2. The one real difference — reduction to cubic (Part I)

This is the only place DeepThinker reasons independently rather than echoing OpenAI.

- **OpenAI**: reduces via a rotation system and a projection map
  (`projectEvenDoubleCover` in the Lean development).
- **DeepThinker**: expands each vertex into a gadget (degree 2 → two vertices joined by a
  double edge; degree $d\ge4$ → a $d$-cycle), then, given a CDC of the cubic expansion $G$,
  **contracts the gadgets** and applies **Veblen's theorem** to decompose the contracted
  image into cycles.

Both are correct. The load-bearing claim in DeepThinker's version is that contracting a
gadget sends each cycle $C$ of $G$ to an **even-degree** subgraph of $M$. Verification of the
parity, at an expanded vertex $v$ with gadget vertices $w$:

- Let $p_w\in\{0,1\}$ indicate whether $C$ uses the pendant (original) edge at $w$, and $c_w$
  the number of gadget-cycle edges $C$ uses at $w$; since $C$ is 2-regular,
  $\deg_C(w)=c_w+p_w\in\{0,2\}$.
- $\sum_w \deg_C(w)$ is even; $\sum_w c_w = 2\cdot(\#\text{gadget-cycle edges used})$ is even.
- Hence the contracted degree at $v$, which is $\sum_w p_w$, is **even**. ✓

So the contracted image is even everywhere, Veblen decomposes it into cycles, and the original
edges — untouched by contraction and covered exactly twice in the cubic CDC — remain covered
exactly twice in $M$. (Bridgeless ⇒ minimum degree $\ge 2$, so the two cases $d=2$ and
$d\ge4$ are exhaustive.) The reduction is sound.

## 3. Validity assessment

**DeepThinker: no error found.**

- Parts II–V are trusted with high confidence because they are mathematically identical to a
  proof that has been formalized and kernel-checked in Lean (see below). This same core was
  independently re-derived by hand and confirmed computationally (a valid CDC was constructed
  on the Petersen graph, the canonical snark) — see `ANALYSIS.md` §3.
- Part I (the one independently-reasoned piece) was checked by hand via the parity argument in
  §2 above and holds up.

**Caveat on presentation.** DeepThinker's "SYSTEM EXECUTION LOG / 64 concurrent agents /
Round 14 / adversarial audit" preamble is theatrical and contributes nothing to validity;
several of its incidental claims are loose (e.g. the "Fractional CDC Polytope … strictly
requiring a nowhere-zero 4-flow" bullet describes an *abandoned* route in hand-wavy terms).
The proof should be judged on Parts I–V, not the orchestration narrative.

## 4. Verification status — the decisive difference

| | OpenAI | DeepThinker |
|---|---|---|
| Form | Math note + **Lean 4 / Mathlib formalization** | Natural-language writeup |
| 8-flow theorem | **Formalized** (not axiomatized) — `JaegerKilpatrick.lean`, `NashWilliams.lean` | Cited |
| Machine-checked | **Yes** — `cycleDoubleCover_of_bridgeless`; no `sorry`, no custom axioms (static grep of all 16 `.lean` files is clean; `Audit.lean` runs `#print axioms`) | No |
| Definition fidelity | `Cycle` = nonempty inclusion-minimal even edge set (cannot be a repeated-edge closed trail); `CycleDoubleCover` = multiset with `coveredTwice` — faithful | Prose only |
| Settles the question? | Yes (modulo running the build + confirming the `#print axioms` output) | No — unverified |

## 5. Implication for this project

DeepThinker adds **no new formalizable content**: it is the same theorem via the same
$\mathbb{F}_2^3$ core that OpenAI already formalized. The only mildly novel element is its
Part I reduction (gadget contraction + Veblen), an alternative to OpenAI's rotation-system
projection — but OpenAI's reduction is already done and verified, so there is little payoff in
re-formalizing DeepThinker's.

If the goal is a trustworthy Lean CDC in `openlemma`, the action item is to **build and audit
OpenAI's repo** (`lake build CDCLean`; `lake env lean CDCLean/Audit.lean`, confirming the axiom
list is only `propext`, `Classical.choice`, `Quot.sound`) and optionally port it — not to
formalize DeepThinker from scratch.
</content>
