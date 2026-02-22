# Coder Agent Memory

## Project Setup
- Lean/Mathlib version: v4.27.0 (fixed in lakefile.toml)
- `relaxedAutoImplicit = false` — always use explicit binders
- Never run `lake clean` or `lake update` — shared Mathlib cache
- Build single module: `lake build problems.Geometry.Leancubes.SafeHyperplane`

## Proven Patterns

### Disjointness proofs
- Use `rw [Set.disjoint_left]` to reduce `Disjoint A B` to `∀ x, x ∈ A → x ∉ B`
- Then unpack membership, derive contradiction via `linarith` or `exact absurd`

### Unused hypotheses
- Prefix with `_` (e.g., `_hh`) to silence the `unusedVariables` linter
- Keep them in the interface if the approved spec includes them

### Segment/cube geometry
- `Fin n → ℝ` is the simplest vector type for axis-aligned geometry
- Define cube as `{x | ∀ i, |x i - c i| ≤ h}` — easy to specialize to one coordinate
- Linear interpolation: `x i = A i + t * (B i - A i)`; when `A k = B k`, `simp` closes it

## File Locations
- Geometry: `problems/Geometry/Leancubes/`
- Number theory: `botlib/NumberTheory/`, `problems/NumberTheory/Erdos1094/`
- Complexity: `botlib/Complexity/`, `problems/Complexity/`

## Build Times
- Full build from scratch: ~94s (cached Mathlib)
- Incremental rebuild of one file: ~6s
