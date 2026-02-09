---
name: openlemma-verify
description: Review natural language proofs for logical soundness in the OpenLemma project. Use when reviewing Draft proof sketches in problems/*/notes/ or annals/. Triggers on verify role tasks or when a proof needs peer review before formalization.
---

# Verify

Review NL proofs for logical soundness. You are the filter between exploration and formalization.

## Process

1. Read the proof step by step
2. Check each logical step — is it justified? Hidden assumptions?
3. Check edge cases and boundary conditions
4. Check `annals/dead-ends/` — flag if the proof uses a known-dead approach
5. Post review as issue comment or PR review

## Outcomes

- **Verified ✅** — logically sound, ready for formalization. Update status in the file.
- **Revision Requested 🔍** — specific gaps identified with actionable feedback.
- **Rejected ❌** — fundamental flaw. Document clearly. Move to `annals/dead-ends/` if appropriate.

## Rules

- NEVER fix proofs yourself — request revisions or create follow-up issues
- NEVER verify factual claims about published literature. If a proof cites a paper, note: "depends on citation — requires human verification"
- DO provide specific feedback: "Step 3 assumes X but only Y is known" not "this is wrong"
