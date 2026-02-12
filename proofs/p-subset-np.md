# P is a subset of NP

**Status:** Draft ✏️
**Statement:** Let $P$ be the class of languages decidable by a deterministic Turing machine in polynomial time, and $NP$ be the class of languages decidable by a non-deterministic Turing machine in polynomial time. Then $P \subseteq NP$.
**Dependencies:** None
**Confidence:** Certain

## Proof

Let $L$ be a language in $P$. By definition, there exists a deterministic Turing machine $M$ and a polynomial $p(n)$ such that for any string $x \in \{0, 1\}^*$, $M$ decides whether $x \in L$ in at most $p(|x|)$ steps.

To show that $L \in NP$, we can use the verifier-based definition of $NP$. A language $L$ is in $NP$ if there exists a deterministic polynomial-time Turing machine $V$ (the verifier) and a polynomial $q(n)$ such that:
$$x \in L \iff \exists w \in \{0, 1\}^*, |w| \le q(|x|) \text{ and } V(x, w) = \text{accept}$$

We construct a verifier $V$ for $L$ as follows:
On input $(x, w)$:
1. Run the deterministic Turing machine $M$ on input $x$.
2. If $M$ accepts $x$, then $V$ accepts $(x, w)$.
3. If $M$ rejects $x$, then $V$ rejects $(x, w)$.

We now verify that $V$ satisfies the requirements:
- **Deterministic and Polynomial Time:** $V$ is deterministic because $M$ is deterministic. The runtime of $V$ is dominated by the runtime of $M$ on $x$, which is at most $p(|x|)$. Thus, $V$ runs in polynomial time relative to the length of the input $x$.
- **Completeness:** Suppose $x \in L$. Then $M$ accepts $x$ in at most $p(|x|)$ steps. Let $w$ be the empty string $\epsilon$. Then $|w| = 0$, which is less than or equal to any polynomial $q(|x|) \ge 0$. On input $(x, \epsilon)$, $V$ runs $M(x)$, which accepts, so $V(x, \epsilon)$ accepts.
- **Soundness:** Suppose $x \notin L$. Then $M$ does not accept $x$. For any string $w$, $V(x, w)$ runs $M(x)$, which rejects. Thus, there exists no $w$ such that $V(x, w)$ accepts.

Since such a verifier $V$ exists, $L \in NP$ by definition. Since $L$ was an arbitrary language in $P$, it follows that $P \subseteq NP$.

## References

1. Sipser, M. (2012). *Introduction to the Theory of Computation*. Cengage Learning.
