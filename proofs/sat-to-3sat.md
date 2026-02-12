# Proof: SAT reduces to 3-SAT

**Statement:** SAT $\le_p$ 3-SAT.
**Status:** Verified ✅
**Reviewed by:** verify
**Goal:** Construct a polynomial-time reduction $f$ that maps any CNF formula $\phi$ to a 3-CNF formula $\psi$ such that $\phi$ is satisfiable if and only if $\psi$ is satisfiable.

## 1. The Reduction

Let $\phi = C_1 \land C_2 \land \dots \land C_m$ be a CNF formula over variables $x_1, \dots, x_n$.
We construct $\psi = f(\phi)$ by transforming each clause $C_i$ into a set of 3-literal clauses.
Let $C_i = (l_1 \lor l_2 \lor \dots \lor l_k)$.

### Case 0: $k = 0$
Clause is empty $()$.
This is always false.
Replace with $(y_{i,1} \lor y_{i,1} \lor y_{i,1}) \land (\neg y_{i,1} \lor \neg y_{i,1} \lor \neg y_{i,1})$, where $y_{i,1}$ is a fresh variable.
This conjunction is unsatisfiable (requires $y_{i,1}$ true and false).
Thus, if $\phi$ contains an empty clause, $\psi$ is unsatisfiable, preserving equivalence.

### Case 1: $k = 1$
Clause is $(l_1)$.
Replace with $(l_1 \lor l_1 \lor l_1)$.
This clause is satisfied iff $l_1$ is true.

**Note on Distinct Literals:** Our definition of `Clause` is `List Literal`, and `isThreeLitClause` only checks `length = 3`. It does not require distinct literals. If distinct literals were required, we would need two fresh variables $z_1, z_2$ and use 4 clauses: $(l_1 \lor z_1 \lor z_2) \land (l_1 \lor \neg z_1 \lor z_2) \land (l_1 \lor z_1 \lor \neg z_2) \land (l_1 \lor \neg z_1 \lor \neg z_2)$. Given our definitions, repetition is valid and simpler.

### Case 2: $k = 2$
Clause is $(l_1 \lor l_2)$.
Replace with $(l_1 \lor l_2 \lor l_1)$.
Equivalent to $l_1 \lor l_2$.

### Case 3: $k = 3$
Keep the clause as is: $(l_1 \lor l_2 \lor l_3)$.

### Case 4: $k > 3$
Clause is $(l_1 \lor l_2 \lor \dots \lor l_k)$.
We introduce $k-3$ fresh variables $y_{i,1}, \dots, y_{i, k-3}$ specific to this clause.
Replace $C_i$ with the conjunction of $k-2$ clauses:
$$
(l_1 \lor l_2 \lor y_{i,1}) \land
(\neg y_{i,1} \lor l_3 \lor y_{i,2}) \land
(\neg y_{i,2} \lor l_4 \lor y_{i,3}) \land
\dots \land
(\neg y_{i, k-4} \lor l_{k-2} \lor y_{i, k-3}) \land
(\neg y_{i, k-3} \lor l_{k-1} \lor l_k)
$$

### Variable Indexing
To ensure fresh variables don't conflict, we can index the new variables by the clause index $i$ and the position $j$. If the original variables are $1 \dots n$, the new variables can start from $n+1$.

## 2. Correctness

We show $\phi$ is satisfiable $\iff \psi$ is satisfiable.

### 2.1 Completeness ($\implies$)
Assume $\phi$ is satisfiable. Let $\sigma$ be a satisfying assignment for variables $x_1, \dots, x_n$.
For each clause $C_i$:
- If $k \le 3$, the transformed clauses are satisfied directly by $\sigma$.
- If $k > 3$, at least one literal $l_j$ is true under $\sigma$.
    - If $l_1$ or $l_2$ is true, set all $y_{i, \cdot}$ to false.
        - First clause satisfied by $l_1/l_2$.
        - Subsequent clauses satisfied by $\neg y_{i, \cdot}$.
    - If $l_k$ or $l_{k-1}$ is true, set all $y_{i, \cdot}$ to true.
        - Last clause satisfied by $l_{k-1}/l_k$.
        - Previous clauses satisfied by $y_{i, \cdot}$.
    - If some intermediate $l_j$ (where $3 \le j \le k-2$) is true:
        - Set $y_{i, 1}, \dots, y_{i, j-2}$ to true.
        - Set $y_{i, j-1}, \dots, y_{i, k-3}$ to false.
        - Clause containing $l_j$ is $(\neg y_{i, j-2} \lor l_j \lor y_{i, j-1})$.
        - Since $l_j$ is true, this clause is satisfied.
        - Preceding clauses have $y$ true on the right (satisfied).
        - Following clauses have $\neg y$ true on the left (satisfied).

Thus, we can extend $\sigma$ to an assignment $\sigma'$ satisfying $\psi$.

### 2.2 Soundness ($\impliedby$)
Assume $\psi$ is satisfiable by some assignment $\sigma'$.
Consider the restriction of $\sigma'$ to the original variables $x_1, \dots, x_n$.
For any original clause $C_i$:
- If $k \le 3$, the clauses in $\psi$ are logically equivalent to $C_i$, so $C_i$ must be satisfied.
- If $k > 3$, suppose for contradiction that all literals $l_1, \dots, l_k$ are false.
    - The first clause $(l_1 \lor l_2 \lor y_{i,1})$ implies $y_{i,1}$ must be true (since $l_1, l_2$ false).
    - The second clause $(\neg y_{i,1} \lor l_3 \lor y_{i,2})$ implies $y_{i,2}$ must be true (since $\neg y_{i,1}$ false, $l_3$ false).
    - By induction, $y_{i,j}$ must be true for all $j$.
    - The last clause $(\neg y_{i, k-3} \lor l_{k-1} \lor l_k)$ becomes $(\text{false} \lor \text{false} \lor \text{false})$, which is unsatisfied.
    - Contradiction.
Thus, at least one literal in $C_i$ must be true.
So $\phi$ is satisfied.

## 3. Complexity

- **Size:** For a clause of length $k > 3$, we generate $k-2$ clauses of length 3. The number of new variables is $k-3$. Total size increase is linear in the length of the original formula.
    - $|\psi| \le 3 \cdot \sum \max(1, |C_i|)$.
    - The reduction is $O(|\phi|)$.
- **Time:** The transformation iterates through clauses and literals once, performing constant work per literal. It is computable in linear time (and thus polynomial time).

## Conclusion

We have shown SAT $\le_p$ 3-SAT: there exists a polynomial-time computable function $f$ such that $\phi$ is satisfiable if and only if $f(\phi)$ is satisfiable and $f(\phi)$ is in 3-CNF.

**3-SAT is NP-complete:**

1. **3-SAT is NP-hard:** SAT is NP-hard (Cook-Levin theorem, proved separately). Since SAT $\le_p$ 3-SAT (this proof), by reduction transitivity, for any language $L \in NP$: $L \le_p \text{SAT} \le_p \text{3-SAT}$. Therefore every NP language reduces to 3-SAT, i.e., 3-SAT is NP-hard.

2. **3-SAT $\in$ NP:** Every 3-CNF formula is a valid CNF formula. The polynomial-time verifier for SAT (which checks any CNF formula against an assignment) therefore also serves as a verifier for 3-SAT with the same certificate type and polynomial bound. Thus 3-SAT $\in$ NP.

3. **NP-hard $\land$ NP $\implies$ NP-complete.** ∎

