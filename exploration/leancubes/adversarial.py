"""
Phase 3: Try to construct adversarial inputs.

Key question: can we make the complement disconnected?

For this, we'd need the union of cubes to "surround" some region.
In R^n, axis-aligned cubes can disconnect R^n iff their union
contains a hypersurface separating R^n into two components.

Key structural observation:
- All cube centers lie in a parallelepiped whose edge vectors come from
  a single face of C_0.
- The face vertices all have x_0 = +1/2 (if using the +x_0 face).
  So all edge vectors e_i have e_i[0] > 0.
- The parallelepiped vertices (±e_1 ± e_2 ± ... ± e_n) can have
  x_0 component of any sign, since we take ± combinations.

Wait — let me reconsider. The edge vectors all have positive x_0 component.
So:
- +e_1 has positive x_0
- -e_1 has negative x_0
- sum of all signs: can get positive or negative x_0

The parallelepiped IS symmetric: if v is a vertex, -v is also a vertex.

Strategy for disconnection: if the cubes form a "curtain" perpendicular
to some axis, they could disconnect R^n into left and right halves.

For axis-aligned unit cubes, a "curtain" in the x_0 direction would require
every point (x_0_val, *, ..., *) to be covered for some x_0_val ∈ [-ε, +ε].

Actually, axis-aligned cubes have projections onto coordinate axes that are
intervals of length 1 (the cube side length). For the union to disconnect R^n,
the projections in some coordinate-slab configuration would need to cover all of R^{n-1}.

This is where n > 2 matters: in n=3, a single unit cube's projection onto a plane
is a unit square, and you'd need infinitely many to cover R^2. But we have only finitely many.

Let me think differently. Can the union of 2^n + 1 unit cubes disconnect R^n?

For n=2 with 5 unit squares: can we disconnect R^2?
For n=3 with 9 unit cubes: can we disconnect R^3?

Attempted adversarial construction for n=3:
- Place cubes so they form a thick "ring" or "wall"
- But the cubes must be at specific positions (parallelepiped vertices)

Let me try extreme l_i values to get cubes very far apart or
in special configurations.
"""

import itertools
import math
from collections import deque
from typing import List, Tuple, Optional
import sys

Vec = Tuple[float, ...]

def vadd(a, b): return tuple(x + y for x, y in zip(a, b))
def vscale(s, v): return tuple(s * x for x in v)
def vnorm(v): return math.sqrt(sum(x*x for x in v))
def vhat(v): nm = vnorm(v); return tuple(x/nm for x in v)
def vzero(n): return tuple(0.0 for _ in range(n))

def select_n_face_vertices(n: int) -> List[Vec]:
    base = (0.5,) + tuple([-0.5] * (n-1))
    verts = [base]
    for i in range(1, n):
        v = list(base)
        v[i] = 0.5
        verts.append(tuple(v))
    return verts

def parallelepiped_vertices(face_verts: List[Vec], lengths: List[float]) -> List[Vec]:
    n = len(lengths)
    edge_vectors = [vscale(lengths[i], vhat(face_verts[i])) for i in range(n)]
    vertices = []
    for signs in itertools.product([-1, 1], repeat=n):
        v = vzero(n)
        for s, e in zip(signs, edge_vectors):
            v = vadd(v, vscale(s, e))
        vertices.append(v)
    return vertices

def build_cube_centers(n: int, lengths: List[float]) -> List[Vec]:
    face_verts = select_n_face_vertices(n)
    para_verts = parallelepiped_vertices(face_verts, lengths)
    return [vzero(n)] + para_verts

def point_in_cube(center: Vec, point: Vec) -> bool:
    return all(abs(point[i] - center[i]) <= 0.5 for i in range(len(center)))

def complement_is_connected_detailed(n: int, lengths: List[float], resolution: int = 20):
    """
    Full connectedness check with detailed output.
    """
    centers = build_cube_centers(n, lengths)

    # Bounding box
    max_coord = max(abs(c[i]) for c in centers for i in range(n)) + 1.5
    grid_min = -max_coord
    step = (2 * max_coord) / resolution

    # Build grid
    grid = {}
    for idx in itertools.product(range(resolution + 1), repeat=n):
        point = tuple(grid_min + idx[i] * step for i in range(n))
        in_union = any(point_in_cube(c, point) for c in centers)
        grid[idx] = not in_union

    complement_points = {idx for idx, val in grid.items() if val}

    # Find starting point (far corner, must be in complement)
    start = None
    for corner in itertools.product([0, resolution], repeat=n):
        if grid.get(corner, False):
            start = corner
            break

    if start is None:
        return None, 0, 0, centers

    # BFS
    visited = set([start])
    queue = deque([start])
    while queue:
        current = queue.popleft()
        for dim in range(n):
            for delta in [-1, 1]:
                nb = list(current)
                nb[dim] += delta
                nb = tuple(nb)
                if any(c < 0 or c > resolution for c in nb):
                    continue
                if nb not in visited and grid.get(nb, False):
                    visited.add(nb)
                    queue.append(nb)

    connected = (len(visited) == len(complement_points))
    return connected, len(complement_points), len(visited), centers

# ---- Adversarial attempt 1: Make cubes form a "wall" ----

def adversarial_wall_attempt():
    """
    For n=3: try to make cubes form a wall separating x<0 from x>0.
    The cubes have side length 1, so they extend ±0.5 in each direction.
    A cube centered at (x0, y0, z0) covers x in [x0-0.5, x0+0.5].
    To form a wall at x=0, we need the union to contain {x=0} × R^2.
    This is impossible with finitely many cubes, so complement is always connected.

    BUT: can the cubes form a "shell" surrounding a bounded region?
    """
    print("=== Adversarial: trying to maximize 'enclosure' ===")
    n = 3

    # Try lengths that put cubes in symmetric positions forming a ring
    # Parallelepiped vertices: ±e_1 ± e_2 ± e_3
    # To form a ring around origin, we want vertices equidistant from origin

    test_cases = [
        [1.0, 1.0, 1.0],    # standard
        [0.9, 0.9, 0.9],    # slightly smaller
        [0.7, 0.7, 0.7],    # small — cubes might touch C_0
        [0.6, 0.6, 0.6],    # even smaller — cubes overlap C_0?
        [0.5, 0.5, 0.5],    # cube edges just touching C_0?
        [0.4, 0.4, 0.4],    # cubes overlapping C_0
        [0.3, 0.3, 0.3],    # heavy overlap
    ]

    for lengths in test_cases:
        centers = build_cube_centers(n, lengths)
        conn, comp, reach, ctrs = complement_is_connected_detailed(n, lengths, resolution=30)
        # Check if any cubes overlap
        max_dist = max(math.sqrt(sum(c[i]**2 for i in range(n))) for c in centers[1:])
        min_dist = min(math.sqrt(sum(c[i]**2 for i in range(n))) for c in centers[1:])
        print(f"  l={lengths[0]:.2f}: connected={conn}, min_dist_from_origin={min_dist:.3f}, max_dist={max_dist:.3f}")

# ---- Adversarial attempt 2: Check if n=2 can disconnect ----

def adversarial_n2():
    """
    For n=2, we have 5 unit squares (C_0 + 4 at parallelepiped vertices).
    The parallelepiped is a parallelogram with 4 vertices.
    All edge vectors come from one edge of C_0 (an edge = face in 2D).
    A face of C_0 in 2D is a 1D face (an edge), which has 2 vertices.
    We pick n=2 vertices from this 2-vertex edge.

    So the directions ARE the two endpoints of one edge.
    For the top edge (y=+0.5), these are (-0.5, 0.5) and (0.5, 0.5).

    Edge vectors: l_1 * hat(-0.5, 0.5) and l_2 * hat(0.5, 0.5)
                = l_1 * (-1/sqrt(2), 1/sqrt(2)) and l_2 * (1/sqrt(2), 1/sqrt(2))

    The 4 parallelepiped vertices are ±e_1 ± e_2.
    """
    print("\n=== n=2 adversarial ===")
    n = 2

    # With equal lengths, by symmetry the 4 cube centers form a square
    for l in [0.3, 0.5, 0.7, 1.0, 1.5, 2.0, 5.0]:
        lengths = [l, l]
        conn, comp, reach, ctrs = complement_is_connected_detailed(n, lengths, resolution=30)
        print(f"  l={l:.1f}: connected={conn}, cubes={len(ctrs)}")
        if not conn:
            print(f"    DISCONNECTED! Centers: {ctrs}")

# ---- Check: are the cubes ever arranged to "surround" a region? ----

def check_bounding_box_coverage(n: int, lengths: List[float]):
    """
    Check whether the union of cubes covers every point along a line segment
    from the origin to outside the bounding box.
    If it does, that line is "blocked" — but the complement can still be connected
    around it.
    """
    centers = build_cube_centers(n, lengths)

    # Check along x_0 axis: does the union block passage in x_0 direction?
    # A point (t, 0, 0, ..., 0) is in some cube iff |t - c_0| <= 0.5 for some center c
    # with |c_i| <= 0.5 for i > 0.

    print(f"\n=== Coverage along x_0 axis (n={n}, l={lengths}) ===")
    t_values = [i * 0.1 for i in range(-30, 31)]
    blocked_count = 0
    for t in t_values:
        point = (t,) + (0.0,) * (n - 1)
        blocked = any(point_in_cube(c, point) for c in centers)
        if blocked:
            blocked_count += 1

    print(f"  {blocked_count}/{len(t_values)} axis points blocked")
    # Find gaps: intervals not covered
    gaps = []
    in_gap = False
    for t in t_values:
        point = (t,) + (0.0,) * (n - 1)
        blocked = any(point_in_cube(c, point) for c in centers)
        if not blocked and not in_gap:
            in_gap = True
            gap_start = t
        elif blocked and in_gap:
            in_gap = False
            gaps.append((gap_start, t))
    if in_gap:
        gaps.append((gap_start, t_values[-1]))
    print(f"  Gaps on axis: {len(gaps)}")

# ---- Key observation: slab structure ----

def analyze_slab_structure():
    """
    Key insight: each axis-aligned unit cube covers exactly the interval
    [c_i - 0.5, c_i + 0.5] in coordinate i.

    For the complement to be disconnected, the union must contain a
    "hypersurface" separating R^n. For an axis-aligned union, the natural
    candidates are hyperplanes x_i = const.

    A hyperplane x_0 = a is "blocked" iff every point on it is covered by some cube.
    This means: for every (x_1, ..., x_{n-1}), there exists a cube center c
    with |a - c_0| <= 0.5 and |x_i - c_i| <= 0.5 for i = 1, ..., n-1.

    This requires the projections of the cubes onto R^{n-1} (fixing x_0 = a) to
    cover ALL of R^{n-1}. But finitely many (2^n + 1) unit (n-1)-cubes can only
    cover a bounded region of R^{n-1}. So NO hyperplane can be completely blocked.

    Therefore: the complement contains every "far enough" part of every hyperplane.
    More specifically: for any coordinate slab, there's a complementary direction
    in the remaining n-1 coordinates where we can escape.

    This is the key structural reason why the complement is always connected
    for n > 2 — and possibly for n >= 2!
    """
    print("""
=== Slab structure analysis ===
Key insight:
- An axis-aligned unit cube covers a bounded (1x1x...x1) region
- For the union to disconnect R^n, it would need to contain a hypersurface
- The only natural hypersurfaces for axis-aligned cubes are coordinate hyperplanes
- A coordinate hyperplane x_0 = a is fully blocked iff the cube projections onto
  R^{n-1} cover all of R^{n-1}
- But finitely many unit (n-1)-cubes cover only bounded area in R^{n-1}
- Therefore: the complement is ALWAYS connected, for ANY n >= 2!

Wait — but the problem says n > 2. Why?

For n = 1: The cubes are intervals. We have 2^1 + 1 = 3 intervals on R.
  These could completely block R, disconnecting it (e.g., if the union
  contains an interval [a,b] ⊂ R, splitting into (-∞,a) and (b,∞)).

For n = 2: The cubes are squares. A square has bounded projection. So no
  line x = const is completely blocked. The complement should be connected...
  But is there another way to disconnect R^2?

Actually, the complement of a compact set in R^n can be disconnected even
without blocking a full hyperplane. Think of a solid torus: its complement has
two components (inside the hole and outside). But axis-aligned cubes have very
special structure...

The real question: can 5 axis-aligned unit squares in R^2 disconnect R^2?
Answer: No! Because their union is compact, and the complement of a compact
set in R^2 can have at most one bounded component (by Alexander duality /
Jordan curve theorem generalization). But actually that's for surfaces, not volumes.

For n >= 2: the complement of finitely many cubes (a compact set) in R^n
is always connected iff n >= 2. Wait, that can't be right in general...

Hmm, but the problem says n > 2 is essential. Let me reconsider.
""")

if __name__ == "__main__":
    adversarial_wall_attempt()
    adversarial_n2()

    check_bounding_box_coverage(3, [1.0, 1.0, 1.0])
    check_bounding_box_coverage(3, [0.5, 0.5, 0.5])

    analyze_slab_structure()
