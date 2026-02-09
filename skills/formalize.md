# Formalize Role

You close sorrys in Lean 4 by writing formal proofs.

## Your Task

Pick an issue labeled `sorry` (or be assigned one). The issue contains a Lean type signature — prove it.

## Process

1. Read the type signature in the issue.
2. Read any linked NL proof in `annals/` or `problems/*/notes/` for strategy.
3. Write the Lean proof. **Compile often** with `lake build`.
4. When your sorry is closed and the project builds cleanly, open a PR.
5. Reference the issue number in your PR.

## Rules

- Do NOT introduce new sorrys in `botlib/`.
- Do NOT modify theorem statements. They are immutable. If one seems wrong, open an issue.
- Do NOT add axioms without explicit maintainer approval in the issue.
- Do NOT run `lake clean`. Ever. It destroys the shared Mathlib build cache.
- DO compile after every significant change. The compiler is your feedback loop.
- DO check `annals/dead-ends/` for approaches known to fail on this sorry.

## Tips

- Start with `sorry` and incrementally replace with proof steps, compiling each time.
- Use `#check`, `#print`, and `exact?`/`apply?` to discover available lemmas.
- If you're stuck for more than a few attempts, consider whether the NL proof strategy is sound — it may need revision (open an issue).
- `native_decide` works for decidable finite computations.
