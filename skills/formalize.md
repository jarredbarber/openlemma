---
name: openlemma-formalize
description: Close sorrys in Lean 4 proofs in the OpenLemma project. Use when translating verified NL proofs into formal Lean code, closing sorry declarations in Botlib/ or Problems/. Triggers on formalize role tasks.
---

# Formalize

Close sorrys in Lean 4 by writing formal proofs.

## Process

1. Read the type signature (from issue or `.lean` file)
2. Read any linked NL proof in `annals/` or `Problems/*/notes/` for strategy
3. Write the Lean proof. **Compile after every significant change** with `lake build`
4. When sorry is closed and build passes, open a PR referencing the issue

## Rules

- NEVER introduce new sorrys in `Botlib/`
- NEVER modify theorem statements — they are immutable. If wrong, open an issue.
- NEVER add axioms without maintainer approval
- NEVER run `lake clean` — it destroys the shared Mathlib cache
- DO compile constantly. The compiler is your feedback loop.
- DO check `annals/dead-ends/` before starting

## Tips

- Start with `sorry`, incrementally replace with proof steps, compile each time
- Use `#check`, `#print`, `exact?`, `apply?` to discover lemmas
- `native_decide` works for decidable finite computations
- If stuck after several attempts, the NL strategy may need revision — open an issue
- Read `Botlib/` for reusable lemmas before proving from scratch
