# NL-Proof Workflow

A bidirectional proof search workflow that separates mathematical reasoning from formal verification. Natural language is the intermediate representation.

## The Idea

Forward (explore): cheap models draft NL proofs → peer reviewed → published to literature directory.
Backward (formalize): expensive models close `sorry` holes in Lean → guided by verified NL proofs → every commit must compile.
The join (orchestrator): reads sorry types + literature, spots where a verified NL proof can close a sorry, creates bridging tasks.

## Pipeline

```
explorer  →  verifier  →  formalizer
(NL proofs)   (review)     (Lean 4)
    ↑             |
    └─────────────┘  on Revision Requested
```

1. **Explorer** drafts rigorous NL proofs with formalization-ready blueprints
2. **Verifier** reviews for logical soundness — Verified/Revision Requested/Rejected
3. **Formalizer** translates verified NL proofs to Lean 4, closing sorrys
4. **Advisor** decomposes problems into sub-questions, manages proof strategy

An **orchestrator** manages the pipeline and maintains the ROADMAP.

## Files

| File | Purpose |
|------|---------|
| `.claude/agents/nl-proof.md` | Orchestrator agent |
| `.claude/agents/explorer.md` | Explorer subagent |
| `.claude/agents/verifier.md` | Verifier subagent |
| `.claude/agents/formalizer.md` | Formalizer subagent |
| `.claude/agents/advisor.md` | Advisor subagent |

All agent prompts live in `.claude/agents/` (project root).

## Key Principles

- **Separate math from Lean.** Different skills, different models, different costs.
- **Verify NL before formalizing.** Catch bad math before expensive Lean cycles.
- **Never tell workers a problem is hard.** Surrender is contagious.
- **Compiler defines the DAG.** Sorry types are better task specs than upfront planning.
- **Information asymmetry.** Advisor knows difficulty, workers don't.

## The Literature Directory

`proofs/` decouples forward exploration from backward formalization:

| Status | Meaning | Who sets it |
|--------|---------|-------------|
| Draft ✏️ | Unreviewed proof | explorer |
| Under Review 🔍 | Needs revision | verifier |
| Verified ✅ | Correct, ready for formalization | verifier |
| Rejected ❌ | Flawed (kept to prevent re-exploration) | verifier |

## Origins

The original OpenLemma workflow, developed through the Cook-Levin and Erdős 1094 experiments. Lessons learned: mathematical reasoning and Lean formalization are different skills; cheap models explore while expensive models formalize; verifying NL before formalizing saves costly Lean cycles.
