# Mathlib Coverage: Computational Complexity

## Available

### Definitions
- `Turing.FinTM2`: Bundled deterministic Turing machine (TM2 model) with finitely many stacks, labels, and internal states.
- `Computability.FinEncoding α`: Finiteness conditions on the encoding of type `α`.
- `Turing.TM2Computable ea eb f`: Predicate stating that a function `f : α → β` is computable by a TM2 machine.
- `Turing.TM2ComputableInTime ea eb f`: Function `f` is computable in time bounded by a given time function `time : ℕ → ℕ`.
- `Turing.TM2ComputableInPolyTime ea eb f`: Function `f` is computable in polynomial time (bounded by a `Polynomial ℕ`).

### Fundamental Results
- `Turing.idComputableInPolyTime`: The identity function is computable in polynomial time (uses $P(n) = 1$).
- `Turing.TM2to1`: Infrastructure for emulating the multi-stack TM2 model on the single-tape TM1 model (includes analysis of the quadratic time overhead).

## Not Available (Missing)

### Poly-time Composition
- `Turing.TM2ComputableInPolyTime.comp`: The theorem that the composition of two polynomial-time computable functions is also polynomial-time computable is currently a **`proof_wanted`** in Mathlib (`Mathlib.Computability.TMComputable.lean`).
- This blocks the formal verification of the transitivity of polynomial-time reductions (`PolyTimeReducible`) without additional proof effort.

### Complexity Classes Theorems
- While `P`, `NP`, and `NP-complete` are defined in `botlib/Complexity/Defs.lean`, Mathlib itself does not yet contain these definitions or major theorems about them (e.g., $P \subseteq NP$, $NP$-completeness of SAT).
- **Cook-Levin Theorem**: No formalization exists in Mathlib or the wider Lean 4 ecosystem yet (as noted in `botlib/Complexity/ROADMAP.md`).

## Reference Locations
- Definitions: `.lake/packages/mathlib/Mathlib/Computability/TMComputable.lean`
- TM Models: `.lake/packages/mathlib/Mathlib/Computability/TuringMachine.lean`
