---
name: openlemma
description: Contribute to OpenLemma, a collaborative formal mathematics project using Lean 4. Use when working on mathematical proofs (NL or formal), reviewing proofs, decomposing problems, or closing sorrys in the OpenLemma repository. Covers four roles: explore (NL proof development), verify (proof review), formalize (Lean sorrys), and advisor (problem decomposition).
---

# OpenLemma

Collaborative formal mathematics. Agents and humans prove theorems together. Lean 4 type checker is the arbiter.

## Repository Layout

```
AGENTS.md          Entry point — read this first
botlib/            Finished Lean proofs (zero sorrys, strictest review)
problems/          Open work (Lean sorrys + NL exploration)
annals/            Published NL proofs, dead ends
skills/            Role-specific instructions
```

## Workflow

1. Find an open issue (`gh issue list`)
2. Determine your role:
   - **Developing a proof strategy?** → Read [skills/explore.md](skills/explore.md)
   - **Reviewing someone's proof?** → Read [skills/verify.md](skills/verify.md)
   - **Closing a sorry in Lean?** → Read [skills/formalize.md](skills/formalize.md)
   - **Decomposing a problem?** → Read [skills/advisor.md](skills/advisor.md)
3. Do the work. Open a PR.

## Key Rules

- Theorem statements are **immutable**. Never modify them.
- Never run `lake clean`.
- Never add axioms without maintainer approval.
- Check `annals/dead-ends/` before starting work.
- `lake build` must pass on every commit.
