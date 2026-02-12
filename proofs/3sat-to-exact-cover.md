# Proof: 3-SAT reduces to EXACT COVER

**Statement:** 3-SAT $\le_p$ EXACT COVER.
**Status:** Draft ✏️
**Goal:** Construct a polynomial-time reduction $f$ that maps any 3-CNF formula $\phi$ to an instance $(X, \mathcal{S})$ of EXACT COVER such that $\phi$ is satisfiable if and only if there exists a subcollection $\mathcal{S}^* \subseteq \mathcal{S}$ that partitions $X$ (every element in $X$ is in exactly one set in $\mathcal{S}^*$).

## 1. Definitions

### 1.1 3-SAT
**Input:** A 3-CNF formula $\phi$ with $n$ variables $x_1, \dots, x_n$ and $m$ clauses $C_1, \dots, C_m$.
**Question:** Is there a truth assignment satisfying $\phi$?

### 1.2 EXACT COVER (XC)
**Input:** A set $X$ and a collection $\mathcal{S}$ of subsets of $X$.
**Question:** Does there exist $\mathcal{S}^* \subseteq \mathcal{S}$ such that $\bigcup_{S \in \mathcal{S}^*} S = X$ and $\forall A, B \in \mathcal{S}^*, A \neq B \implies A \cap B = \emptyset$?

## 2. The Reduction

Let $\phi$ be an instance of 3-SAT.
Variables: $x_1, \dots, x_n$.
Clauses: $C_1, \dots, C_m$.

### 2.1 Universe $X$
The universe $X$ consists of:
1.  **Variable Elements:** For each variable $x_i$, an element $x_i$. (Wait, standard reduction uses more elements to enforce choice).
    **Standard Reduction Elements:**
    For each variable $x_i$, elements $a_i$ (or maybe a structure enforcing exactly one choice).
    Let's use the standard "variable gadget" + "clause gadget".
    $X = \{x_i \mid 1 \le i \le n\} \cup \{C_j \mid 1 \le j \le m\}$.
    This is insufficient.

    **Correct Standard Reduction:**
    Universe $X$:
    -   For each variable $x_i$: elements $x_i$ and $\bar{x}_i$? No.
    -   Usually: $X = \{u_i \mid 1 \le i \le n\} \cup \{c_j \mid 1 \le j \le m\}$?
    -   Let's follow the standard Garey & Johnson / Karp reduction.
    
    **Elements:**
    -   Variable region: For each $x_i$, create elements. We need to force a choice between True/False.
        Typically, we have elements $p_{i,j}$ related to occurrences.
    -   Clause region: Elements $c_1, \dots, c_m$.

    **Sets ($\mathcal{S}$):**
    1.  **True/False Sets:** For each variable $x_i$, create sets $T_i$ and $F_i$.
        -   $T_i$ represents $x_i = \text{true}$.
        -   $F_i$ represents $x_i = \text{false}$.
        -   We need elements in $X$ such that we MUST pick exactly one of $T_i, F_i$.
        -   Create element $u_i$. $T_i = \{u_i, \dots\}$, $F_i = \{u_i, \dots\}$.
        -   This forces picking exactly one.
    2.  **Clause Satisfaction:**
        -   $T_i$ should contain clause element $c_j$ if literal $x_i \in C_j$.
        -   $F_i$ should contain clause element $c_j$ if literal $\neg x_i \in C_j$.
        -   If we do this directly: if $x_i \in C_j$, picking $T_i$ covers $c_j$.
        -   Problem: A clause can be satisfied by multiple literals. If we pick two true literals for $C_j$, we cover $c_j$ twice. This violates EXACT cover.
        -   Exact Cover requires exactly one cover.
        -   Solution: Slack sets.

    **Refined Reduction:**
    **Universe $X$:**
    -   Variable elements: $u_1, \dots, u_n$.
    -   Clause elements: $c_1, \dots, c_m$.
    
    **Collection $\mathcal{S}$:**
    1.  **Variable Sets:** For each $x_i$:
        -   $T_i = \{u_i\} \cup \{c_j \mid x_i \in C_j\}$.
        -   $F_i = \{u_i\} \cup \{c_j \mid \neg x_i \in C_j\}$.
        -   (Note: This is still the "overlap" version. We need to handle the overlap).
    
    **Handling Overlap (Exactness):**
    We cannot simply include $c_j$ in $T_i$.
    We need "slack" sets to cover $c_j$ if it's NOT covered by a literal?
    No, Exact Cover means we MUST cover it exactly once.
    If a clause has 3 true literals, we cover it 3 times? Bad.
    
    **The "X3C" Reduction (Exact Cover by 3-sets) is slightly different.**
    Let's stick to general Exact Cover.
    
    **Correct Construction:**
    Universe $X = \{x_i\}_{1\le i \le n} \cup \{c_j\}_{1\le j \le m}$.
    
    Sets for variable $x_i$:
    -   $T_i = \{x_i\} \cup \{ \text{something related to clauses} \}$?
    
    Let's interpret the "valid" reduction carefully.
    For each clause $C_j = (l_1 \lor l_2 \lor l_3)$:
    We need to select subsets such that $c_j$ is covered exactly once.
    This implies we satisfy the clause exactly once. But SAT allows multiple true literals.
    
    **Padding Trick:**
    For each clause $C_j$, add two slack sets $S_{j,1}, S_{j,2}$.
    Wait, slack sets usually just contain $c_j$ and nothing else?
    If $S_{j,1} = \{c_j\}$, then we can always cover $c_j$ with it.
    Then the choice of literals doesn't matter.
    
    The constraint must be: The chosen literals cover $c_j$ some number of times ($k \in \{1,2,3\}$).
    The slack sets must cover the *remaining* requirements.
    But in set theory, "covering 3 times" is impossible (sets are binary).
    
    **Alternative Representation:**
    Represent the clause $C_j$ not as a single element, but as a gadget.
    Or:
    **Standard 3-SAT to X3C reduction:**
    Variable gadget is a cycle. Clause gadget hooks into cycle.
    This is complex.
    
    **Simpler Reduction (3-SAT to EXACT COVER):**
    Maybe via ONE-IN-THREE 3-SAT?
    3-SAT $\le_p$ 1-in-3 3-SAT $\le_p$ EXACT COVER.
    1-in-3 3-SAT: Is there an assignment where exactly one literal per clause is true?
    If we assume 1-in-3 SAT is hard, the reduction is:
    $X = \{u_i\} \cup \{c_j\}$.
    Sets: $T_i = \{u_i\} \cup \{c_j \mid x_i \in C_j\}$, $F_i = \{u_i\} \cup \{c_j \mid \neg x_i \in C_j\}$.
    This works directly for 1-in-3 SAT.
    
    To prove 3-SAT $\le_p$ EXACT COVER directly, we need to simulate logical OR.
    
    **Reduction using Clause Components:**
    For each clause $C_j = (l_1 \lor l_2 \lor l_3)$, we add elements $\{c_j\}$.
    Variable sets $T_i, F_i$ cover $u_i$. They DO NOT cover $c_j$ directly.
    Instead, they cover "occurrence elements" $p_{i,j}$.
    
    Let's use the reduction 3-SAT $\le_p$ 3-Dimensional Matching $\le_p$ Exact Cover.
    Or just standard text (Sipser/Karp).
    
    **Reduction:**
    Elements:
    1.  Variable element $x_i$ for each $i$.
    2.  Clause element $c_j$ for each $j$.
    3.  Distractor elements?
    
    Let's go with the **Slack Variable approach** but mapping to sets.
    Each clause $C_j$ needs to be covered exactly once.
    Literals contribute to covering.
    Slack sets contribute to covering.
    We need: (Literals count) + (Slack count) = 1? No.
    
    Let's reduce 3-SAT to **Exact Hitting Set** (dual of Exact Cover)?
    No, Exact Cover.
    
    **Strategy: 3-SAT $\to$ 1-in-3 3-SAT $\to$ Exact Cover.**
    Is this permitted?
    The first step (3-SAT to 1-in-3) is a known reduction.
    $C = (a \lor b \lor c)$.
    Replace with $R(a, b, c, d_1, \dots)$.
    This seems too long for a single proof file.
    
    **Direct Reduction:**
    Let's define the sets to represent "Literal $l$ is true".
    $X = \{x_1, \dots, x_n\} \cup \{c_1, \dots, c_m\}$.
    
    For each variable $x_i$:
    -   Set $A_i = \{x_i, p_{i,1}, p_{i,2}, \dots\}$ (True)
    -   Set $B_i = \{x_i, q_{i,1}, q_{i,2}, \dots\}$ (False)
    -   Force exactly one of $A_i, B_i$.
    
    For clause $C_j = (l_1 \lor l_2 \lor l_3)$:
    -   We need to cover $c_j$.
    -   If $l_1$ is true (set $A/B$ chosen), does it cover $c_j$?
    -   If yes, we can't have $l_2$ true.
    -   We need slack.
    -   Add pairs of slack sets for each clause.
    
    **Construction:**
    $X = \{x_1, \dots, x_n\} \cup \{c_1, \dots, c_m\}$.
    Sets $\mathcal{S}$:
    1.  **Variable Sets:**
        For each $x_i$, create $T_i = \{x_i\} \cup \{c_j \mid x_i \in C_j\}$ ?? NO.
        Create elements $p_{i,j}$ for occurrences?
        Let's assume the literals in sets $T_i, F_i$ simply "contain" the clause element $c_j$.
        This implies 1-in-3 SAT.
        
    **Solution:**
    Reduce **3-SAT** to **Exact Cover** by adding **slack sets**.
    For each clause $C_j$, allow covering $c_j$ by "True Literals" OR "Slack".
    But Exact Cover means disjoint.
    
    Correct structure:
    Universe $X = \{x_1, \dots, x_n\} \cup \{c_1, \dots, c_m\} \cup P$ (auxiliary).
    
    **Actually, 3-SAT $\le_p$ 3-Dimensional Matching (3DM) $\le_p$ Exact Cover.**
    3DM is a special case of Exact Cover ($|S|=3$).
    Reducing 3-SAT to 3DM is the standard path.
    
    **Let's write the reduction 3-SAT $\to$ EXACT COVER directly using the 3DM logic.**
    
    **1. Variable Gadget:**
    A cycle of $2k$ sets (where $k$ is occurrences).
    This handles consistency.
    
    **2. Clause Gadget:**
    Sets that cover clause elements and hook into the variable cycle.
    
    **Simplified Construction (from a reliable source):**
    Input: 3-CNF $\phi$.
    Universe $U = \{x_i\} \cup \{c_j\} \cup \{p_{ij} : x_i \in C_j \text{ or } \neg x_i \in C_j\}$.
    This is getting complicated.
    
    **Let's use the Generalized Exact Cover reduction.**
    Variable $x_i$: Sets $T_i = \{x_i, \text{pos-occurrences}\}$, $F_i = \{x_i, \text{neg-occurrences}\}$.
    This forces exactly one assignment.
    Problem: "pos-occurrences" for $x_i$ might overlap with other variables in the clause?
    No, a clause element $c_j$ is shared.
    
    If $T_1$ has $c_1$ and $T_2$ has $c_1$, and both are true, we overlap on $c_1$. INVALID.
    
    **Slack Sets to the rescue:**
    For each clause $C_j$, add pairs of sets that can "absorb" the clause element if it's NOT covered by variables?
    No, we need to cover it EXACTLY once.
    So if variables cover it 1, 2, or 3 times, we fail.
    We need variables to cover it 0 or 1 time?
    
    **Key Insight:**
    The transformation from 3-SAT to Exact Cover usually goes through **Generalized Exact Cover** (where we must cover *at least* once? No, that's Set Cover).
    
    Let's draft **3-SAT $\to$ 3DM $\to$ XC**.
    Or just standard **3-SAT $\to$ XC**.
    
    **Construction (Garey & Johnson, 3-SAT to X3C):**
    This is complex (variable cycles).
    
    **Alternative: Generalized Exact Cover?**
    Maybe the planner meant **SET COVER**?
    3-SAT $\le_p$ VERTEX COVER $\le_p$ SET COVER $\le_p$ EXACT COVER?
    Actually Vertex Cover $\le_p$ Set Cover is trivial.
    Set Cover $\le_p$ Exact Cover is NOT trivial.
    
    **Back to basics:**
    If we just want a valid reduction:
    Reduce **3-SAT** to **Subset Sum** (done).
    Reduce **Subset Sum** to **Exact Cover**? No.
    
    **Let's do the standard 3-SAT to Exact Cover (Variable/Clause/Slack):**
    Elements:
    1.  $x_i$ for each variable.
    2.  $c_j$ for each clause.
    
    Sets:
    1.  **Variables:** $T_i = \{x_i\} \cup P_{i, \text{pos}}$, $F_i = \{x_i\} \cup P_{i, \text{neg}}$.
        where $P$ are occurrence identifiers.
        Actually, let's treat occurrences as distinct elements $o_{j,k}$ (clause $j$, literal $k$).
        $T_i$ covers $o_{j,k}$ if $x_i$ is the $k$-th literal in $C_j$.
    2.  **Clause Satisfaction:**
        We need to cover $c_j$.
        Who covers $c_j$?
        Connect $o_{j,k}$ to $c_j$?
    
    **Standard Valid Construction:**
    Universe $U = \{x_1, \dots, x_n\} \cup \{c_1, \dots, c_m\}$.
    For each clause $C_j = \{l_1, l_2, l_3\}$:
    Add slack sets to "eat" the clause element $c_j$ if satisfied?
    
    Let's reduce **3-SAT** to **Exact Cover** via **Coloring**?
    
    **Decision:**
    I will use the standard **Clause-Slack** reduction.
    Universe $X = \{x_i\} \cup \{c_j\}$.
    Sets:
    - $T_i$: $\{x_i\} \cup \{c_j \mid x_i \in C_j\}$. (Wait, overlap issue).
    
    **Correct Logic:**
    For each occurrence of a literal in a clause, create a unique element.
    $U = \{x_i\} \cup \{y_{jk} : \text{literal } k \text{ in clause } j\}$.
    Variable sets pick row of $y$'s.
    Clause sets pick "remaining" $y$'s.
    
    Let's draft based on the **3DM** style but simplified for general sets.
    
## 3. The Reduction (Draft)

**Universe $X$:**
-   Variable elements $x_1, \dots, x_n$.
-   Clause elements $c_1, \dots, c_m$.
-   Slack elements $s_{j,1}, s_{j,2}$ for each clause $j$. (Total $2m$ slack elements).

**Sets $\mathcal{S}$:**
1.  **Truth Assignment Sets:** For each variable $i$:
    -   $A_i^{true} = \{x_i\} \cup \{c_j \mid x_i \in C_j \text{ is true}\}$. (Problem: Overlap).
    
    **Wait, the overlap is the hardest part.**
    If $x_1$ and $x_2$ are both in $C_1$, and both true, $A_1$ and $A_2$ both contain $c_1$. Intersection $\neq \emptyset$.
    
    **Solution:**
    The variable sets should NOT contain $c_j$ directly.
    They should contain an intermediate element $p_{j,k}$ representing "literal $k$ in clause $j$ is true".
    Then the CLAUSE element $c_j$ must be covered by ONE of $\{p_{j,1}, p_{j,2}, p_{j,3}\}$ plus slack.
    
    **Refined Universe:**
    $X = \{x_1, \dots, x_n\} \cup \{c_1, \dots, c_m\} \cup \{p_{j,k} \mid 1 \le j \le m, k \in \{1,2,3\}\}$.
    
    **Sets:**
    1.  **Variable Choice:**
        For each $x_i$:
        -   $T_i = \{x_i\} \cup \{p_{j,k} \mid \text{literal } k \text{ in } C_j \text{ is } x_i\}$.
        -   $F_i = \{x_i\} \cup \{p_{j,k} \mid \text{literal } k \text{ in } C_j \text{ is } \neg x_i\}$.
        Constraint: Must pick exactly one (to cover $x_i$).
        Effect: If $T_i$ picked, all $p$ corresponding to $x_i$ are covered (set to "true").
        
    2.  **Clause Satisfaction:**
        For each clause $j$, we must cover $c_j$ exactly once.
        And we must cover the $p_{j,k}$ elements that were NOT covered by variables (i.e., false literals).
        
        This is "Exact Hitting Set" logic inverted.
        Here, picking $T_i$ *consumes* $p$.
        We need to cover the *remaining* $p$'s and the clause $c_j$.
        
        Sets for clause $j$:
        -   The variables cover some $p_{j,k}$'s (the true ones).
        -   We need to cover the *false* $p_{j,k}$'s.
        -   And cover $c_j$.
        -   Since clause is satisfied, at least one $p_{j,k}$ is covered by variables.
        -   So at most 2 $p$'s are uncovered.
        -   We provide slack sets that cover $\{c_j\} \cup (\text{subset of } \{p_{j,1}, p_{j,2}, p_{j,3}\})$.
        
        Slack sets for $C_j$:
        -   $Z_{j,1} = \{c_j, p_{j,1}, p_{j,2}\}$ (Covers 2 false, checks 1 true). Wait.
        -   If $p_{j,3}$ is covered by variable (true), we need to cover $c_j, p_{j,1}, p_{j,2}$. $Z_{j,1}$ works.
        -   If $p_{j,2}, p_{j,3}$ true, we need to cover $c_j, p_{j,1}$.
        -   We need sets for all combinations of "False literals".
        
        **Slack Sets:**
        -   $\{c_j, p_{j,1}, p_{j,2}\}$ (Assumes $l_3$ true)
        -   $\{c_j, p_{j,2}, p_{j,3}\}$ (Assumes $l_1$ true)
        -   $\{c_j, p_{j,1}, p_{j,3}\}$ (Assumes $l_2$ true)
        -   $\{c_j, p_{j,1}\}$ (Assumes $l_2, l_3$ true)
        -   $\{c_j, p_{j,2}\}$ (Assumes $l_1, l_3$ true)
        -   $\{c_j, p_{j,3}\}$ (Assumes $l_1, l_2$ true)
        -   $\{c_j\}$ (Assumes $l_1, l_2, l_3$ true)
        
    **Verification:**
    -   Variables pick "True" $p$'s.
    -   Slack sets must pick the "False" $p$'s + $c_j$.
    -   Since slack sets must be disjoint from variables, they cover only "False" $p$'s.
    -   Can we always find a slack set?
        -   The "False" $p$'s are exactly $\{p_{j,1}, p_{j,2}, p_{j,3}\} \setminus \text{Covered}$.
        -   If clause is satisfied, number of false is 0, 1, or 2.
        -   Our slack sets cover all subsets of size 0, 1, 2.
        -   (Actually size 2: $\{p_1, p_2\}$, size 1: $\{p_1\}$, size 0: $\emptyset$).
        -   So yes, we can always cover the exact remainder + $c_j$.
        -   If clause is unsatisfied, all 3 $p$'s are false (uncovered by vars).
        -   We need a slack set covering $\{c_j, p_1, p_2, p_3\}$.
        -   We DO NOT include this slack set.
        -   Thus, if unsatisfied, we cannot cover everything.
        
    This works!

## 4. Complexity
-   Universe size: $n + m + 3m = n + 4m$.
-   Sets: $2n$ (vars) + $7m$ (slack).
-   Linear size.

## 5. Conclusion
3-SAT $\le_p$ EXACT COVER.
EXACT COVER is NP-complete.
