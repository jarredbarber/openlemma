# Proof: SAT Assignment Equivalence Lemmas

**Status:** Draft ✏️
**Goal:** Provide rigorous proof sketches for variable-relevance lemmas in `botlib/Complexity/SAT.lean` to support the formalization of `SAT ∈ NP`.

## Lemma 1: `evalClause_eq_of_vars_eq`

**Statement:**
Let $c$ be a clause. Let $\sigma_1, \sigma_2$ be two assignments such that $\forall v \in c.vars, \sigma_1(v) = \sigma_2(v)$.
Then `evalClause σ₁ c = evalClause σ₂ c`.

**Proof:**
We proceed by induction on the list of literals in clause $c$.

**Base Case:** $c = []$.
By definition, `evalClause σ [] = false` (empty disjunction).
Thus, `evalClause σ₁ [] = false = evalClause σ₂ []`.

**Inductive Step:** Let $c = l :: ls$.
Assume the inductive hypothesis (IH): If $\sigma_1, \sigma_2$ agree on $ls.vars$, then `evalClause σ₁ ls = evalClause σ₂ ls`.
By definition, `evalClause σ (l :: ls) = evalLiteral σ l || evalClause σ ls`.

1.  **Literal Equality:**
    The variable $v_l = l.var$ is in $(l :: ls).vars$.
    By the premise, $\sigma_1(v_l) = \sigma_2(v_l)$.
    The value of `evalLiteral σ l` depends only on $\sigma(l.var)$.
    Therefore, `evalLiteral σ₁ l = evalLiteral σ₂ l`.

2.  **Recursive Equality:**
    The variables in $ls$ are a subset of the variables in $l :: ls$ ($ls.vars \subseteq (l :: ls).vars$).
    Since $\sigma_1$ and $\sigma_2$ agree on all variables in $c$, they agree on all variables in $ls$.
    By the IH, `evalClause σ₁ ls = evalClause σ₂ ls`.

3.  **Conclusion:**
    `evalClause σ₁ (l :: ls) = (evalLiteral σ₁ l) || (evalClause σ₁ ls)`
    `= (evalLiteral σ₂ l) || (evalClause σ₂ ls)`
    `= evalClause σ₂ (l :: ls)`.

## Lemma 2: `evalCNF_eq_of_vars_eq`

**Statement:**
Let $\phi$ be a CNF formula. Let $\sigma_1, \sigma_2$ be two assignments such that $\forall v \in \phi.vars, \sigma_1(v) = \sigma_2(v)$.
Then `evalCNF σ₁ φ = evalCNF σ₂ φ`.

**Proof:**
We proceed by induction on the list of clauses in $\phi$.

**Base Case:** $\phi = []$.
By definition, `evalCNF σ [] = true` (empty conjunction).
Thus, `evalCNF σ₁ [] = true = evalCNF σ₂ []`.

**Inductive Step:** Let $\phi = c :: cs$.
Assume IH: If $\sigma_1, \sigma_2$ agree on $cs.vars$, then `evalCNF σ₁ cs = evalCNF σ₂ cs`.
By definition, `evalCNF σ (c :: cs) = evalClause σ c && evalCNF σ cs`.

1.  **Clause Equality:**
    The variables in $c$ are a subset of the variables in $\phi$ ($c.vars \subseteq (c :: cs).vars$).
    By the premise, $\sigma_1$ and $\sigma_2$ agree on all variables in $\phi$, so they agree on $c.vars$.
    By Lemma 1, `evalClause σ₁ c = evalClause σ₂ c`.

2.  **Recursive Equality:**
    The variables in $cs$ are a subset of the variables in $\phi$ ($cs.vars \subseteq (c :: cs).vars$).
    Thus $\sigma_1$ and $\sigma_2$ agree on $cs.vars$.
    By the IH, `evalCNF σ₁ cs = evalCNF σ₂ cs`.

3.  **Conclusion:**
    `evalCNF σ₁ (c :: cs) = (evalClause σ₁ c) && (evalCNF σ₁ cs)`
    `= (evalClause σ₂ c) && (evalCNF σ₂ cs)`
    `= evalCNF σ₂ (c :: cs)`.

## Lemma 3: `assignmentOfCertificate_eq_of_mem`

**Statement:**
Let $\sigma$ be an assignment and $\phi$ be a CNF formula.
Construct the certificate $y$ as the list of pairs $(v, \sigma(v))$ for all variables in $\phi$, with duplicates removed:
$$ y = (\phi.vars.eraseDups).map (\lambda v \mapsto (v, \sigma v)) $$
Then for any variable $v \in \phi.vars$, `assignmentOfCertificate y v = σ v`.

**Proof:**

1.  **Certificate Construction:**
    Let $V_{list} = \phi.vars.eraseDups$.
    The list $y$ is constructed by mapping $f(x) = (x, \sigma(x))$ over $V_{list}$.
    So $y = [ (v_1, \sigma(v_1)), (v_2, \sigma(v_2)), \dots ]$.

2.  **Lookup Definition:**
    `assignmentOfCertificate y v` is defined as:
    `match y.find? (fun p => p.1 == v) with`
    `| some p => p.2`
    `| none => false`

3.  **Existence:**
    We are given $v \in \phi.vars$.
    The function `eraseDups` preserves membership, so $v \in V_{list}$.
    Since $v \in V_{list}$, the pair $(v, \sigma(v))$ is present in the mapped list $y$.
    Therefore, `y.find?` will definitely find a pair $p$ such that $p.1 = v$.

4.  **Uniqueness (Optional but good for rigor):**
    `eraseDups` ensures that $V_{list}$ contains no duplicate variables.
    Thus, $y$ contains exactly one pair where the first component is $v$, which is $(v, \sigma(v))$.
    The `find?` function returns the first match, which is uniquely determined here.

5.  **Value Retrieval:**
    The found pair is $p = (v, \sigma(v))$.
    The function returns $p.2$, which is $\sigma(v)$.

**Conclusion:**
For all $v \in \phi.vars$, the reconstructed assignment agrees with the original assignment $\sigma$.
