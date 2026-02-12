# Proof: Transitivity of Polynomial-Time Reductions

**Statement:** If $L_1 \le_p L_2$ and $L_2 \le_p L_3$, then $L_1 \le_p L_3$.
**Status:** Draft ✏️
**Dependencies:** `TM2ComputableInPolyTime.comp` (assumed/axiomatized)

## Definitions

Let $L_1, L_2, L_3$ be languages over alphabets $\Sigma_1, \Sigma_2, \Sigma_3$ respectively.
A language $L_a$ is polynomial-time reducible to $L_b$ ($L_a \le_p L_b$) if there exists a function $f : \Sigma_a^* \to \Sigma_b^*$ such that:
1.  $f$ is computable by a deterministic Turing machine in polynomial time.
2.  For all $x \in \Sigma_a^*$, $x \in L_a \iff f(x) \in L_b$.

## Proof

Let $f: \Sigma_1^* \to \Sigma_2^*$ be the reduction from $L_1$ to $L_2$.
Let $g: \Sigma_2^* \to \Sigma_3^*$ be the reduction from $L_2$ to $L_3$.

Define $h: \Sigma_1^* \to \Sigma_3^*$ as $h(x) = g(f(x))$.

### 1. Correctness

We must show that $x \in L_1 \iff h(x) \in L_3$.
$$
\begin{aligned}
x \in L_1 &\iff f(x) \in L_2 & (\text{definition of } f) \\
&\iff g(f(x)) \in L_3 & (\text{definition of } g) \\
&\iff h(x) \in L_3 & (\text{definition of } h)
\end{aligned}
$$
Thus, $h$ correctly reduces instances of $L_1$ to instances of $L_3$.

### 2. Complexity

We must show that $h$ is computable in polynomial time.

Let $T_f(n)$ be the runtime of $f$ on input of size $n$. Since $f$ is poly-time, $T_f(n) \le c_1 \cdot n^{k_1}$ for some constants $c_1, k_1$.
Let $T_g(m)$ be the runtime of $g$ on input of size $m$. Since $g$ is poly-time, $T_g(m) \le c_2 \cdot m^{k_2}$ for some constants $c_2, k_2$.

Consider the runtime of computing $h(x) = g(f(x))$:
1.  Compute $y = f(x)$. This takes time $T_f(|x|) \le c_1 \cdot |x|^{k_1}$.
2.  The size of the output $|y|$ is bounded by the runtime of $f$, since a TM can write at most one symbol per step. Thus $|y| \le T_f(|x|) \le c_1 \cdot |x|^{k_1}$.
3.  Compute $z = g(y)$. This takes time $T_g(|y|) \le c_2 \cdot |y|^{k_2}$.

Substituting the bound for $|y|$:
$$
T_g(|y|) \le c_2 \cdot (c_1 \cdot |x|^{k_1})^{k_2} = c_2 \cdot c_1^{k_2} \cdot |x|^{k_1 k_2}
$$

The total time is the sum of the time to compute $f$ and $g$:
$$
T_h(|x|) = T_f(|x|) + T_g(|y|) \le c_1 \cdot |x|^{k_1} + c_2 \cdot c_1^{k_2} \cdot |x|^{k_1 k_2}
$$
Since $k_1 k_2$ is a constant, this is a polynomial in $|x|$.

Therefore, $h$ is computable in polynomial time.

## Axiomatic Dependency

In Lean 4 `Mathlib.Computability.TMComputable`, the theorem stating that the composition of two polynomial-time computable functions is polynomial-time (`TM2ComputableInPolyTime.comp`) is currently missing ("proof wanted").
For the formalization of this theorem, we will assume this property as an axiom until it is proven in Mathlib.

**Axiom:** `TM2ComputableInPolyTime.comp`
If `f` is TM-computable in poly-time and `g` is TM-computable in poly-time, then `g ∘ f` is TM-computable in poly-time.
