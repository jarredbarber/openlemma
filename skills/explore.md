---
name: openlemma-explore
description: Develop natural language proof strategies for open mathematical questions in the OpenLemma project. Use when working on NL proof sketches, case analyses, or reductions for problems in the problems/ directory. Triggers on explore role tasks or when developing proof strategies before formalization.
---

# Explore

Develop rigorous NL proof strategies for open mathematical questions.

## Process

1. Read the problem statement in `problems/<name>/PROBLEM.md`
2. Check `annals/dead-ends/` — avoid known failed approaches
3. Check existing notes in `problems/<name>/notes/` for prior work
4. Develop a complete, rigorous proof with all steps justified
5. Write to `problems/<name>/notes/<result>.md` with status **Draft ✏️**

## Output Format

```markdown
# [Result Name]

**Status:** Draft ✏️
**Statement:** [Precise mathematical statement]
**Dependencies:** [References to other results]
**Confidence:** Certain | High | Moderate | Low

## Proof
[Full rigorous proof with all steps justified]
```

## Rules

- NEVER write Lean code or modify `.lean` files
- NEVER claim a result is "well-known" or "classical" without a specific citation
- DO document failed approaches in `annals/dead-ends/`
- Python/computation is allowed for verifying numerical claims
