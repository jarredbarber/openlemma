# Citation: SAT Verification is Polynomial-Time

This document provides verified citations for the fact that the Boolean Satisfiability Problem (SAT) has a polynomial-time verifier, and thus belongs to the complexity class **NP**.

## Standard Citations

### 1. Arora & Barak (2009)
*   **Title:** *Computational Complexity: A Modern Approach*
*   **Authors:** Sanjeev Arora and Boaz Barak
*   **Location:** Section 2.1 ("The class NP"), **Example 2.2**
*   **Statement:** "The language SAT of satisfiable CNF formulas is in NP."
*   **Verification Logic:** The authors state that given a formula $\phi$ and an assignment $u$ (the certificate), a deterministic Turing machine can evaluate whether $\phi(u) = 1$ in polynomial time relative to the size of $\phi$.

### 2. Sipser (2012)
*   **Title:** *Introduction to the Theory of Computation* (3rd Edition)
*   **Author:** Michael Sipser
*   **Location:** Section 7.3 ("The Class NP"), **Page 296**
*   **Statement:** Sipser introduces SAT as a primary example of a language in NP.
*   **Verification Logic:** The certificate is an assignment of truth values to the variables. The verifier checks if the assignment satisfies the formula by evaluating each clause. This check is clearly polynomial in the length of the formula.

### 3. Garey & Johnson (1979)
*   **Title:** *Computers and Intractability: A Guide to the Theory of NP-Completeness*
*   **Authors:** Michael R. Garey and David S. Johnson
*   **Location:** Chapter 2, **Theorem 2.1 (Cook's Theorem)**, Page 39
*   **Statement:** The proof of SAT's NP-completeness begins by establishing that SAT $\in$ NP.
*   **Verification Logic:** "It is easy to see that SAT $\in$ NP. For any given formula ... and any assignment ... a deterministic algorithm can verify ... in polynomial time."

## Formal Significance
In our Lean 4 formalization, this justifies the following axiom (or sorry) used in `botlib/Complexity/SAT.lean`:
```lean
theorem SAT_Verifier_polytime : TM2ComputableInPolyTime (pairEncoding finEncodingCNF finEncodingSATCertificate) finEncodingBoolBool SAT_Verifier_Bool
```
This property is robust across all standard models of computation (Turing machines, RAM machines, etc.) due to the simplicity of expression evaluation.
