# Code-as-Proof Workflow

A proof search workflow where Python code is the intermediate representation between mathematical insight and formal verification.

## The Idea

Natural language hides gaps. Lean is expensive. Python code proofs sit in between: precise enough to be falsifiable, cheap enough to iterate on, and structured enough to translate mechanically to Lean.

```python
def lemma_name(params) -> bool | None:
    """Precise claim."""
    # True = proved. False = disproved. None = gap.
```

The function signature is the lemma statement. The call graph is the dependency structure. Refactoring the code is restructuring the proof.

## Pipeline

```
researcher  →  reviewer  →  coder
(Python)       (verdicts)    (Lean 4)
    ↑              |
    └──────────────┘  on BREAK or GAP
```

1. **Researcher** writes Python code proofs following the conventions in `conventions.md`
2. **Reviewer** tries to break them — adversarial, sees only the code, no context
3. **Coder** translates approved code proofs to Lean 4

An **orchestrator** manages the pipeline, curating what context each agent sees. Information barriers are enforced structurally — each subagent only receives what's in its prompt.

## Files

| File | Purpose |
|------|---------|
| `conventions.md` | The structural proof notation rules |
| `.claude/agents/code-as-proof.md` | Orchestrator agent |
| `.claude/agents/researcher.md` | Researcher subagent |
| `.claude/agents/reviewer.md` | Reviewer subagent |
| `.claude/agents/coder.md` | Coder subagent |

All agent prompts live in `.claude/agents/` (project root). This directory just has `conventions.md`.

## Key Principles

- **Computation is testing, not proving.** Tests catch bugs. The proof is the argument for WHY it generalizes.
- **Return type honesty.** True/False/None. Never True when you mean "probably."
- **Context control.** The reviewer doesn't know the problem is hard. The coder doesn't see failed attempts. Information barriers prevent contamination.
- **Frame tasks as routine.** Never say "open problem" or "unsolved conjecture" to subagents. Difficulty framing causes surrender.
- **Name gaps precisely.** Not "this doesn't work" but "the set of primes depends on n, so CRT over a fixed modulus doesn't apply."

## Running a Problem

1. Create a problem directory under `problems/` with a `PROBLEM.md`
2. The orchestrator reads the workspace, spawns a researcher subagent
3. Researcher writes code proofs to `exploration/`
4. Orchestrator routes to reviewer, then coder
5. `STATUS.md` tracks progress

## Origins

Developed through the Erdős 1094 and Cook-Levin formalization experiments. Lessons learned: separating math reasoning from Lean formalization prevents the wrong bottleneck from dominating; adversarial review catches gaps that computation misses; honest gap-naming drives insight more than optimistic hand-waving.
