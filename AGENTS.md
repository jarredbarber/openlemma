# OpenLemma — Agent Workflow

This project uses Claude Code subagents orchestrated through the code-as-proof workflow.

## How It Works

A single **orchestrator** agent manages the proof pipeline by spawning subagents with curated context. Each subagent sees only what it needs — information barriers are structural, not disciplinary.

```
orchestrator (persistent, manages pipeline)
  ├── researcher subagent  (Python code proofs)
  ├── reviewer subagent    (adversarial, breaks proofs)
  └── coder subagent       (Lean 4 formalization)
```

## Workflow Documentation

All workflow details are in `workflows/code-as-proof/`:

| File | Purpose |
|------|---------|
| `README.md` | Overview and pipeline diagram |
| `conventions.md` | Structural proof notation rules |
| `orchestrator.md` | System prompt for the orchestrator |
| `agents/researcher.md` | Researcher subagent prompt |
| `agents/reviewer.md` | Reviewer subagent prompt |
| `agents/coder.md` | Coder subagent prompt |

## Key Rules

- **Theorem statements are immutable.** Never modify them.
- **Never run `lake clean`.** It corrupts the shared Mathlib cache.
- **Never add axioms without maintainer approval.** Citation axioms only with verification.
- **`lake build` must pass on every commit.** Sorrys are OK, errors are not.
- **Check `annals/dead-ends/` before starting work.** Don't repeat known failures.

## Building

```bash
lake build                           # Full build
lake build botlib.Complexity.Defs    # Single file
```

## Axiom Policy

- **Citation axioms** (citing known results): Allowed with source citation
- **Crux axioms** (conclusion matches the theorem): NOT allowed — escalate to human
- **Sorry**: Temporary only. Comment explaining what's needed.
