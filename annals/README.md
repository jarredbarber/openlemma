# Published Results

This directory contains verified natural language proofs, notes, and dead-end reports.

## Structure

- **Top-level `.md` files**: Verified NL proofs (Status: Verified ✅)
- **`dead-ends/`**: Documented failed approaches (preserved to prevent repetition)

## Status Lifecycle

1. Explore agent writes a proof → **Draft ✏️** (lives in `problems/*/notes/`)
2. Verify agent reviews it → **Verified ✅** (promoted to `annals/`) or **Rejected ❌**
3. Formalize agent uses verified proof as strategy for Lean formalization
4. Finished Lean proof promoted to `botlib/`
