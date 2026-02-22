# LeancubeS: Complement Connectedness Investigation

## Problem

Let C_0 be an axis-aligned solid unit cube in R^n, n > 2, centered at the origin.
Starting at the center of C_0, project n rays through n distinct vertices of one face of C_0.
Each ray has length l_i. These rays define a parallelepiped. At each of its 2^n vertices,
attach an axis-aligned unit cube C_i at its center.

**Claim:** For n > 2 and any choice of lengths l_i > 0, the complement R^n \ C is connected,
where C = C_0 ∪ C_1 ∪ ... ∪ C_{2^n}.

## Files

- `geometry.py` — Constructs cube centers, verifies geometry for various n and l_i
- `connectedness.py` — Grid-based BFS flood-fill connectedness check
- `adversarial.py` — Attempts to construct counterexamples
- `dimension_analysis.py` — Why n > 2 matters; analyzes n=1 and n=2 cases
- `proof_analysis.py` — Fiber connectivity analysis; core of the proof idea
- `proof_structure.py` — Full proof structure with sub-lemmas
- `main_proof.py` — Final consolidated lemma structure and test suite

## Geometry

- A face of the n-cube has 2^{n-1} vertices. We pick n of them as ray directions.
- The canonical choice: positive x_0 face, with base vertex (-1/2,...,-1/2,+1/2) → varies.
- Total cubes: 1 (C_0) + 2^n (at parallelepiped vertices) = **2^n + 1**
- All cubes are axis-aligned regardless of direction vectors

## Numerical Results

Grid-discretized BFS confirms connectedness for all tested cases:
- n=3: 12+ distinct length configurations, all connected
- n=4: several configurations, all connected
- n=2: also appears connected (but not covered by the main proof strategy)
- n=1: DISCONNECTED for l > 1 (the only case that fails)

## Proof Structure

### Why n=1 fails
Three intervals on R^1 can disconnect R^1 (e.g., for l > 1: three separate intervals).

### Why n=2 doesn't obviously fail
Five unit squares in R^2 cannot form a closed loop (Jordan curve) to trap a region.
The complement is connected, but the fiber argument doesn't directly prove it.

### Why n >= 3 works (the fiber argument)

**Key Lemma (fiber connectivity):** For n >= 3 and any collection of finitely many
axis-aligned unit cubes in R^n, every cross-section {x_0 = t} ∩ (R^n \ C) is
path-connected in R^{n-1}. This holds because n-1 >= 2, and the complement of finitely
many bounded cubes in R^m (m >= 2) is always connected.

**Proof sketch for n >= 3:**

Given A, B ∈ R^n \ C:
1. **Safe fiber exists:** Choose T = max(|c_0| over all cube centers) + 1.
   At x_0 = T, no cube is active. The "safe hyperplane" {x_0 = T} is entirely
   in the complement.
2. **Connect A to safe hyperplane:** Move A's transverse coordinates
   (x_1, ..., x_{n-1}) to a "safe" value outside all cube projections.
   For n-1 >= 2, the complement of finitely many (n-1)-cubes in R^{n-1} is connected
   (the outer region connects everything). A generic path works.
3. **Connect along safe hyperplane:** A' = (T, ...) connects to B' = (T, ...) freely.
4. **Mirror for B.**

**Gap (for formalization):** The "generic path" in step 2 uses the fact that
in R^m (m >= 2), the obstruction set for a straight line to avoid finitely many cubes
is measure-zero. This needs explicit path construction for a Lean proof.

### Computational Verification of Key Sub-Lemmas

| Lemma | Status |
|-------|--------|
| Safe fiber exists (T beyond all cubes) | True (analytic) |
| Outer region connected (n >= 2) | True (analytic, S^{n-1} connected) |
| Fiber complement connected for n=3 | True (BFS verified, 100+ cases) |
| Fiber fails for n=2 | True (BFS shows disconnected fibers for n=2) |
| Complement connected for n=3 | True (BFS verified, 12+ length configs) |
| Complement connected for n=4 | True (BFS verified, 3 configs) |

## Open Questions

1. Does the claim hold for n=2? All grid tests say yes, but no proof.
2. Is the "n is not a power of two" condition useful? (Not needed numerically.)
3. Can the fiber argument be made fully constructive (avoiding measure theory)?
