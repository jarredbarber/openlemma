# Researcher Agent Memory

## Running Python in this project
- Use `python3` not `python` (python not in PATH)
- Use absolute paths: `python3 /home/jarred/openlemma/...`
- To exec a file for interactive testing: `exec(open('exploration/leancubes/lemma_escape.py').read())`

## Code-as-proof patterns

### Return type discipline
- `True` = proved for this input. `None` = gap. `False` = counterexample.
- Never return `True` when empirical tests pass but the argument isn't structural.

### Key pattern: necessary-condition intervals
When proving a segment A->T(d) misses a cube: compute a necessary-condition interval
for d (if d is outside this interval, cube is missed). This is the core of `_d_interval_for_coord`.
- The interval can be finite [lo,hi], half-line (-inf,hi] or [lo,+inf), or full (-inf,+inf).
- d outside [lo,hi] => cube missed. Verify this with P1/P2 tests before trusting.

### 2-step sweep pattern
Used in `lemma_escape.py`: choose d1 then d2 to avoid all cubes.
1. Classify each cube by whether d1_interval, d2_interval is finite/half-line/full.
2. 'both_unbounded' = impossible when A outside cj (verify empirically).
3. d1_candidates includes explicit escape values (lo-1, hi+1) for each finite bound.
4. choose_d2: for each d1, collect d2 intervals that need to be avoided.
5. Verify every returned T with _segment_clear.

## Leancubes project
- Location: `exploration/leancubes/`
- Key file: `lemma_escape.py` (2-parameter escape proof, n>=3)
- Previous version: `proof_v5.py` (1-parameter escape, also works)
- Cube builder: `_build_cube_centers(n, lengths)` returns origin cube + 2^n vertices
- Standard params: h=0.5, S=M+1 where M=max|c[i]|+h
