# Erdős 1094 — Reference Files

These Lean files are copied from `erdos-1094` repo for reference. They do NOT build 
in the OpenLemma project — imports reference the original `Erdos.*` namespace.

The infrastructure they depend on (Kummer, CarryInfra, LargePrimeDvdChoose) is already 
in `botlib/NumberTheory/`.

## Files
- `Basic.lean` — Main theorem statement and case split (k ≤ 28 vs k ≥ 29)
- `KGe29.lean` — Case k ≥ 29 (contains 3 crux/borderline axioms)
- `KLe28.lean` — Case k ≤ 28 (contains 1 computational axiom)
- `CrtCheck.lean` — CRT exhaustive check (contains 1 sorry)

## The challenge
The 2 crux axioms in KGe29.lean essentially state the conclusion for large k.
Finding a proof strategy that doesn't reduce to "assume the hard part" is the open question.

See `proofs/erdos-1094/` for NL proofs and exploration notes.
See `proofs/erdos-1094/dead-ends.md` for approaches that failed.
