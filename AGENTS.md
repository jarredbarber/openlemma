# OpenLemma Social — Shared Workspace

You are an agent working on the OpenLemma project. All agents share **this single directory**. There are no separate clones.

## How This Works

- **Your role** is in `roles/<your-name>.md` — your name matches your agent name (check `echo $PI_AGENT_NAME` or the name others use to DM you)
- **The codebase** is the repo you're in — read it to understand current state
- **Other agents** are discoverable via `list_remote_agents`
- **Communication** is via `remote_prompt` (direct messages to named agents)
- **Read `roles/<your-name>.md` first** to understand your responsibilities

## File Ownership

Since we all share one directory, **announce before editing**. Respect these ownership zones:

| Role | Owns | May read |
|------|------|----------|
| **explore** | `proofs/*.md` | everything |
| **formalize** | `botlib/Complexity/*.lean` | proofs/, ROADMAP.md |
| **verify** | (reviews, no owned files) | everything |
| **planner** | `botlib/Complexity/ROADMAP.md`, tm tasks | everything |
| **advisor** | strategic guidance (no owned files) | everything |
| **librarian** | `artifacts/*.md` | everything |

**Rules:**
- DM the owner before editing their files
- If you need a change in someone else's file, ask them to make it
- The only exception: fixing a typo or obvious build error — commit with a clear message

## Git

**Only the planner handles git.** Everyone else: just edit files directly.

- **planner** periodically does `git add -A && git commit && git push`
- If you finished something, DM the planner: "I updated X, ready to commit"
- **Never run git commands yourself** (add, commit, push, pull, rebase). The planner handles all of it.
- **Never run `lake update` or `lake clean`.** The `.lake` directory is a shared cache symlink.

## Communication

### Discovering agents
Use `list_remote_agents` to see who's online.

### Sending messages
Use `remote_prompt` to DM another agent:
- **advisor** — strategic guidance, proof strategy
- **librarian** — verify citations, search literature
- **planner** — decompose problems, coordinate work, git operations
- **verify** — review your natural language proof
- **explore/formalize** — collaborate on proof ↔ Lean translation

### Coordination norms
- **Announce what file you're touching** — DM relevant agents
- **Ask before you assume** — need a fact? DM the librarian
- **Report results** — DM the planner when you finish something
- **Flag blockers** — if you're stuck, say so

## Project: Computational Complexity in Lean 4

Goal: formalize complexity foundations and prove Cook-Levin (SAT is NP-complete) in Lean 4.

### Current state
See `botlib/Complexity/ROADMAP.md` for full status. Key files:
- `botlib/Complexity/Defs.lean` — P, NP, NP-complete, poly-time reductions
- `botlib/Complexity/SAT.lean` — CNF formulas, SAT/3-SAT
- `botlib/Complexity/CookLevin.lean` — Tableau-based reduction (WIP)
- `botlib/Complexity/PolyTimeFst.lean` — Poly-time projection (complete)
- `botlib/Complexity/TM2PolyTimeComp.lean` — Poly-time composition (ported)
- `proofs/*.md` — Natural language proofs

### Building
```bash
lake build                           # Full build
lake build botlib.Complexity.Defs    # Single file
```

## Axiom Policy

- **Citation axioms** (citing known results): Allowed, but MUST be verified by librarian first
- **Crux axioms** (conclusion matches the theorem): NOT allowed — DM the advisor
- **Sorry**: Temporary only. Comment explaining what's needed. Flag to planner
