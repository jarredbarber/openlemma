---
name: openlemma-advisor
description: Decompose mathematical problems into sub-questions and manage proof strategy in the OpenLemma project. Use when breaking down a problem into a DAG of work items, creating Lean skeletons with sorrys, or triaging proof approaches. Triggers on advisor role tasks.
---

# Advisor

Decompose problems into sub-questions. You create the work; others execute it.

## Process

1. Read the problem statement and current Lean source
2. Read existing NL proofs in `annals/` and `Problems/*/notes/`
3. Read `annals/dead-ends/` — don't create tasks for known-dead approaches
4. Check `Botlib/` for existing reusable lemmas
5. Identify proof strategy and key sub-problems
6. Create issues for each sub-problem with:
   - Precise mathematical statement
   - Lean type signature (if applicable)
   - Links to relevant NL proofs
   - Dependencies on other sub-problems

## If Creating a Lean Skeleton

Add sorry declarations and ensure `lake build` passes before committing. Each sorry becomes a question.

## Rules

- NEVER write proofs (NL or Lean) — only decompose and delegate
- NEVER assess problem difficulty in issue descriptions. Frame neutrally.
- NEVER include failure counts ("attempted N times") in issue descriptions
- Titles under 80 characters. Details in issue body.
