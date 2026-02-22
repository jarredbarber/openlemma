# Researcher Agent Memory

## Project: OpenLemma

Working directory: /home/jarred/openlemma
Proof exploration scripts: exploration/leancubes/
Run python3 (not python) with absolute paths.

## Key Patterns

### Code-as-proof methodology
- Return type honesty: `True` = proved, `None` = gap, never `True` for "probably".
- Each function is a lemma. Call graph = proof structure. Refactor until obvious.
- Name gaps precisely: "the bad d-set is unbounded because A is only outside cj via coord 0"
  is more useful than "this doesn't work".

### Leancubes v5 proof (exploration/leancubes/proof_v5.py) - CORRECT
The bad-d set for the 1D parameterization T(d)=(S,S+d,...,S+d) CAN be unbounded in one direction
but is always bounded in AT LEAST ONE direction (one-sided bound). Use `lemma_cube_one_sided_bound`:

Case analysis on witness coord k (max margin coord):
- k>=1, A[k]>cj[k]+h: direction=+1, R=0 (large pos d -> T[k]>cj[k]+h, both above slab)
- k>=1, A[k]<cj[k]-h: direction=-1, R=S-cj[k]+h (large neg d -> T[k]<cj[k]-h, both below slab)
- k=0, A[0]>cj[0]+h: direction=+1, R=0 (T[0]=S>A[0]>cj[0]+h, segment stays above)
- k=0, A[0]<cj[0]-h:
  - If any j>=1 has A[j]>cj[j]+h: direction=+1, R=0 (pos d -> T[j]=S+d>cj[j]+h, both above)
  - If any j>=1 has A[j]<cj[j]-h: direction=-1, R=S-cj[j]+h (neg d -> T[j]<cj[j]-h, both below)
  - Else (only coord 0 outside): use coord-0 crossing time + n>=3 extra coord. direction=+1, finite R.

escape_to_safe: search d=0,±1,±2,... up to R_search=2*max_j(R_j)+10. Always terminates.
n>=3 is essential: provides extra dimension to escape.

### Common pitfall: claiming bounded bad sets without verification
Always empirically verify "the bad set is bounded" before building proof on it.
The 1D diagonal parameterization's bad set can be unbounded in one direction for cases where
A is above a cube in some coords and below in others.

### Bad eps interval analysis (earlier work, leancubes/constructive_proof.py)
- t_lo > 0 (A outside cube's transverse slab): bounded interval
- t_lo = 0: half-lines arise; conflicting half-lines -> try different P directions

### Syntax in docstrings
Avoid `\ ` (backslash-space) in docstrings -- use "minus" or parenthetical instead.
