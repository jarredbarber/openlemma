# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Quick Start

**Build:** `lake build` (requires Lean 4.27.0 + Mathlib 4.27.0)

**Single file:** `lake build botlib.Complexity.Defs` (replace with actual module path)

**Check status:** `git log --oneline -10` to see recent work and current state

## Project Overview

**OpenLemma** is a curated library of formally verified mathematical results produced by LLM agents, built on Lean 4 and Mathlib.

### Library Structure

Two main components:
- **`botlib/`** — Compiler-verified lemmas with zero sorrys and zero axioms. Safe to import as dependencies.
- **`problems/`** — Problem-specific results that may use citation axioms for theorems not yet in Mathlib.

### Current Projects

#### Cook-Levin Theorem (Core Complete ✅, Assembly Pending)
- **Location:** `botlib/Complexity/` and `problems/Complexity/`
- **Goal:** Prove SAT is NP-complete via polynomial-time reduction from Turing Machines
- **Status:** Core proofs complete (~2,723 lines, ~124 theorems, 2 axioms, 0 sorrys)
- **Key files:**
  - `Defs.lean` — P, NP, NP-complete definitions, poly-time reductions (~360 lines, 0 axioms)
  - `SAT.lean` — CNF formulas, SAT/3-SAT definitions (~370 lines)
  - `CookLevin/Tableau.lean` — Multi-stack tableau structure (~530 lines, 0 axioms)
  - `CookLevin/Correctness.lean` — `stepAux` soundness (~370 lines, 0 axioms)
  - `CookLevin/Soundness.lean` — Tableau satisfiability → TM acceptance (~918 lines, 0 axioms)
  - `CookLevin/Completeness.lean` — TM acceptance → Tableau satisfiability (~1,166 lines, 0 axioms)
- **Remaining:** Assembly into final theorem and polynomial-time bound verification (2 citation axioms needed)
- **Roadmap:** `botlib/Complexity/ROADMAP.md`

#### Erdős 1094 (Active)
- **Location:** `problems/NumberTheory/Erdos1094/` and supporting lemmas in `botlib/`
- **Goal:** Prove for all k ≥ 29: the least prime factor of C(n,k) is ≤ max(n/k, k) for all n ≥ 2k
- **Status:** GREEN (0 sorrys, 2 citation axioms)
- **Key files:**
  - `botlib/NumberTheory/Kummer.lean` — Kummer's digit-domination criterion
  - `botlib/NumberTheory/LargePrimeDvdChoose.lean` — Prime divisibility test
  - `botlib/NumberTheory/CarryInfra.lean` — Decidable carry check
  - `problems/NumberTheory/Erdos1094/Konyagin.lean` — Citation of Konyagin (1999)
  - `problems/NumberTheory/Erdos1094/KGe29.lean` — Main large-n case
- **Architecture:** Case split on n ≤ k² (closed via Konyagin) vs. n > k² (relies on `large_n_smooth_case` axiom, guarded by k ≥ 7 after (62,6) counterexample)
- **Strategy:** Kummer's theorem + CRT product sets + asymptotic density + small-case verification
- **Recent:** `large_n_smooth_case` axiom found to be FALSE for (62,6); k ≥ 7 guard added. 3-layer hybrid proof strategy with zero failures for k ≥ 7. See `proofs/erdos-1094/tool-characterization.md` and `proofs/erdos-1094/proof-strategy.md`.

## Architecture & Design Patterns

### Agent Workflow

This project uses the **code-as-proof** workflow with Claude Code subagents. See `workflows/code-as-proof/README.md` for the full pipeline.

- **Orchestrator** manages the pipeline, spawning researcher/reviewer/coder subagents
- **Context control** is the key design dimension — each subagent sees only what it needs
- See `AGENTS.md` for the current setup

### Axiom Policy

- **Citation axioms** (citing well-known results): Allowed with source citation.
- **Crux axioms** (where the conclusion matches the theorem): NOT allowed. Escalate to human.
- **Sorrys**: Temporary only. Comment explaining what's needed.

Current axioms are documented in README.md and individual ROADMAP files.

### Code Organization

```
botlib/
├── NumberTheory/        # Lemmas for Erdős problems
│   ├── Kummer.lean
│   ├── LargePrimeDvdChoose.lean
│   ├── CarryInfra.lean
│   └── ... (7+ files)
├── Combinatorics/       # Digit spaces, concentration bounds
├── Complexity/          # Cook-Levin formalization
│   ├── Defs.lean        # P, NP, reductions
│   ├── SAT.lean         # Satisfiability
│   ├── TM2PolyTimeComp.lean  # Composition closure
│   ├── PolyTimeFst.lean      # First projection
│   ├── CookLevin/       # Main proof components
│   │   ├── Tableau.lean
│   │   ├── Correctness.lean
│   │   ├── Soundness.lean
│   │   ├── Completeness.lean
│   │   └── PolyTime.lean
│   └── CookLevin.lean   # Hub assembling components
└── Utils.lean

problems/
├── NumberTheory/
│   ├── SmoothEscape.lean     # Erdős 410
│   └── Erdos1094/
│       ├── Asymptotic.lean
│       ├── KLe28.lean
│       ├── Konyagin.lean
│       └── KGe29.lean
└── Complexity/             # Problem-specific complexity proofs

proofs/                    # Natural-language proof sketches (markdown)
├── erdos-1094/           # Strategic research and proof designs
├── cook-levin-*/         # Blueprint documents for reduction
└── ... (16+ files)

exploration/              # Computational verification scripts (Python)
archive/                  # Stale/abandoned formalizations (not active)
artifacts/                # Analysis and research outputs
annals/                   # Historical documentation
workflows/                # Agent workflow definitions (code-as-proof, etc.)
```

## Development Workflow

### Understanding Proof State

1. **Check the ROADMAP** for the project you're working on (`botlib/Complexity/ROADMAP.md` or `problems/NumberTheory/Erdos1094/ROADMAP.md`)
2. **Read recent commits** to understand what was just completed
3. **Read problem statements** in `problems/*/README.md` or `.md` files to understand what needs to be proven

### Adding or Fixing Proofs

1. Read the natural-language proof in `proofs/` or strategic research in `artifacts/`
2. Check the corresponding ROADMAP for dependencies
3. Edit the `.lean` file in `botlib/` or `problems/`
4. Run `lake build` to check for compilation errors

### Handling Sorrys

- Add an explanatory comment above the sorry describing what's needed
- Track it in the ROADMAP file or commit message

## Key Mathematical Insights

### Kummer's Theorem (Core to Erdős 1094)
A prime p divides C(n,k) if and only if there exists a digit position where k's base-p digit exceeds n's base-p digit. This is the foundation for all prime divisibility tests in Erdős 1094.

### Cook-Levin Reduction Strategy
Encode a Turing Machine computation as Boolean satisfiability via:
1. **Tableau**: Variables for each tape cell, state, and time step
2. **Constraints**: Initial config → transition rules → acceptance
3. **Polynomial bound**: Encoding size is polynomial in TM size

The key technical challenge is proving that forbidden-window constraints correctly encode all valid state transitions.

## Common Tasks

### Running a specific test/build
```bash
lake build botlib.NumberTheory.Kummer
lake build problems.NumberTheory.Erdos1094.KGe29
```

### Finding where a theorem is used
```bash
grep -r "theorem_name" botlib/ problems/
```

### Checking what depends on a file
```bash
grep -r "import.*ModuleName" botlib/ problems/
```

### Understanding recent changes
```bash
git log --oneline -20
git show <commit-hash>
```

## Important Notes

- **`.lake` symlink:** Points to a shared cache. Never run `lake update` or `lake clean`.
- **Mathlib version:** Fixed at v4.27.0 in `lakefile.toml`. Changes require explicit update.
- **Relaxed auto-implicits:** Disabled in `lakefile.toml` (set to false). Use explicit binders.
- **Citation axioms:** Documented in individual files. Search for `noncomputable axiom` to find them.

## Research Integration

- **`artifacts/`** contains analysis documents that may be referenced in proofs
- **`proofs/`** contains blueprint markdown files that guide formalization
- **Git history** tracks false starts and dead-ends (documented in commit messages for learning)
- Honest error documentation: If an approach fails, failures are documented with clear explanations

## Where to Look for Context

- **Project vision & architecture:** README.md
- **Cook-Levin status:** `botlib/Complexity/ROADMAP.md`
- **Erdős 1094 status:** `problems/NumberTheory/Erdos1094/ROADMAP.md`
- **Agent coordination:** AGENTS.md (workflow overview)
- **Strategic research:** `proofs/erdos-1094/*.md` (deep analysis of approaches)
- **Workflow definitions:** `workflows/` (code-as-proof pipeline, agent prompts)
