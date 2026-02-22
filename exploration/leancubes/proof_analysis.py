"""
Phase 3: Proof structure analysis.

The key geometric fact: the union of 2^n + 1 axis-aligned unit cubes
(arranged as described) has a connected complement in R^n for n >= 2.
The n > 2 condition may be for a specific reason we need to identify.

Let me reason about WHY the complement is connected.

=== Approach 1: Escape direction ===

Key observation: each axis-aligned unit cube centered at c is contained in
the "slab" {x : |x_i - c_i| <= 1/2} for each coordinate i.

For the complement to be disconnected, two points A and B in the complement
must have no path between them that avoids all cubes.

Strategy: given any two points A, B outside all cubes, we can connect them
by moving in coordinate directions, avoiding the cubes.

For n >= 2: can we always find a "safe" direction to move?

A cube centered at c blocks coordinate-direction movement in a tube of width 1
around c. With 2^n + 1 cubes, we have at most 2^n + 1 such blocked tubes
in each coordinate direction.

But in R^n with n >= 2, moving in the x_1 direction at height x_2 = h
avoids the cube at c iff |h - c_2| > 1/2 OR we pass it by before/after.

=== Approach 2: Slab complement ===

Consider the projection π_i: R^n -> R onto coordinate i.
Each cube projects to an interval [c_i - 1/2, c_i + 1/2] of length 1.

The complement of this projected interval in R is two half-lines: (-∞, c_i-1/2) and (c_i+1/2, ∞).

Key lemma: for any x_i value, the "cross-section" of the complement at x_i
is a connected set in R^{n-1} provided n >= 2.

Proof of key lemma: The cross-section at x_i = t is:
  {(x_1,...,x_{i-1}, x_{i+1}, ..., x_n) : (x_1,...,t,...,x_n) not in any cube}

Cubes active at x_i = t: those with |t - c_i| <= 1/2, i.e., |t - c_i| <= 1/2.
These cubes project to bounded boxes in R^{n-1}, each of size 1^{n-1}.

The complement in R^{n-1} of finitely many bounded boxes is connected (for n-1 >= 1)
because R^{n-1} is unbounded and the boxes don't block all of R^{n-1}.

WAIT: this is not quite right. "Connected complement of finitely many cubes in R^m"
is true for m >= 1 (since we can go around any finite collection of cubes)
as long as the cubes don't cover all of R^m.

For m >= 1: complement of a compact set in R^m is connected iff we can path-connect
any two exterior points. This is true for m >= 1 when the compact set doesn't
disconnect R^m (which requires the compact set to be "hollow" or form a barrier).

For m = 1 (n-1 = 1, so n = 2): the complement of a compact set in R^1 can be
disconnected if the set contains an interval that spans all of R^1 (impossible since
compact). Wait, compact in R^1 means closed and bounded. The complement of a
compact proper subset of R^1 is always two disjoint rays plus the gaps.

Actually: R^1 \ (compact set) can have multiple connected components!
E.g., R \ [-1, 1] = (-∞, -1) ∪ (1, ∞) — two components!

So my approach 2 is too simple. The cross-section at x_i = t is R^{n-1} minus
finitely many cubes. For n-1 >= 2, this complement is connected. But for n-1 = 1
(i.e., n = 2), it might not be.

=== Approach 3: The "escape to infinity" argument ===

Claim: for any two points A, B in the complement of C, we can connect them
via a path that:
1. First moves to a "far" point F_A far from all cubes
2. Then connects F_A to F_B far from all cubes (easy, since far from everything)
3. Then moves from F_B to B

The key is that "far from all cubes" means we can move in any direction freely.
For n >= 2, we can always "go around" any cube by making a detour in the other
coordinates.

More precisely:

Lemma: for n >= 2, given any cube C_j with center c and any two points A, B
outside C_j, we can connect A to B by a path that avoids C_j.

Proof: The complement of C_j (a closed unit cube) in R^n is connected for n >= 2.
This is because C_j is a convex body with nonempty interior, and its complement
in R^n (n >= 2) is connected. (General fact: R^n \ K is connected if K is compact
and n >= 2.)

WAIT: R^n minus a closed convex body is connected for n >= 2. TRUE.
But we're removing MULTIPLE cubes. The union might disconnect things.

Actually: R^n minus a finite union of closed convex bodies is still connected for n >= 2,
AS LONG AS the union doesn't cover a "barrier". And since each cube is bounded and
axis-aligned, and we have finitely many, the union is bounded, and its complement
is connected (the far-field region of R^n is connected and connects to everything).

More precisely:
R^n \ (bounded set) is connected for n >= 2.

Proof: For n >= 2 and K a bounded subset of R^n, R^n \ K is path-connected.
- Take any two points A, B in R^n \ K.
- Both have distance > 0 from K (since K is closed; if K is open, they're just outside).
  Actually K = union of closed cubes = closed. So A, B ∉ K means they're in the complement.
- Since K is bounded, there exists R > 0 such that K ⊂ B(0, R).
- Choose a point F on the sphere of radius 2R (far from K).
  F is in R^n \ K since K ⊂ B(0, R).
- Path from A to F: go radially outward from A to the sphere S(0, 2R), then
  along the sphere to the angular position of F.
  Wait — the radial path from A might pass through K!

Better: For n >= 2, the sphere S^{n-1} is connected (since n-1 >= 1).
- Move A radially outward: A -> (2R / |A|) * A. But this path might cross K.

Alternative: A path from A to F avoiding K.
- Since K is bounded by R, any point with |x| > R is in the complement.
- The "outer region" {x : |x| > R} ⊂ R^n \ K is connected for n >= 2
  (it's the complement of a closed ball, which is connected for n >= 2).
- We need to connect A to the outer region without passing through K.

Hmm, but A might be "inside" the convex hull of K, and paths from A to the
outer region might be forced through K.

ACTUALLY: This is the key topological fact.

FACT: If K ⊂ R^n is compact and n >= 2, then R^n \ K is path-connected.

Proof: Given A, B ∉ K. Choose R large enough so K ⊂ B(0, R) and A, B ∈ B(0, R).
Since S(0, 2R) is connected (n >= 2 implies S^{n-1} is connected), choose a path
on S(0, 2R) from 2R * A/|A| to 2R * B/|B|.
Now we need paths from A and B to S(0, 2R) avoiding K.

For n >= 2: consider the "cone" from A to S(0, 2R). Since K is compact,
it's covered by finitely many small balls. Using a generic linear path,
we can perturb it to avoid K (Baire category argument).

Actually the clean argument:

FACT: R^n minus a compact set K is connected iff K doesn't separate R^n.
For n >= 2 and K a compact subset of R^n that is NOT a topological (n-1)-sphere
enclosing a region... this gets into Alexander duality.

Simple clean argument for our case:
K = finite union of closed axis-aligned unit cubes = compact + axis-aligned.

For n >= 2: the complement R^n \ K is connected.

Proof by explicit path construction:
Given A, B ∉ K. WLOG |A|, |B| < R for some R.
Choose a value t_0 such that no cube has x_1-center at t_0 (possible since
finitely many cubes, each with measure-zero set of "bad" t values).
Move along x_1 from A's x_1 coord to t_0, keeping other coords fixed — but
this might hit cubes in the x_1 direction!

=== Better approach for axis-aligned cubes: coordinate slab argument ===

The key property of AXIS-ALIGNED cubes: they are products of intervals.
C = [a_1, b_1] × ... × [a_n, b_n].

For a collection of axis-aligned cubes, we can use a "grid" structure.

CRITICAL LEMMA: Let K = union of finitely many closed axis-aligned unit cubes
in R^n. Then R^n \ K is connected for n >= 2.

Proof:
Let L = max over all cubes of all |c_i| for centers c. So all cube centers
have coordinates in [-L, L].

Consider the set S = {x : |x_1| = L + 2 or ... or |x_n| = L + 2}.
S is a "boundary frame" at distance L+2 from origin.
S doesn't intersect K (all cubes are contained in [-L-1, L+1]^n ⊂ [-L-2, L-2]^n?
Wait: L+2 > L+1/2, so S doesn't intersect any cube. S is in the complement.

S is path-connected for n >= 2:
- S contains the face {x_1 = L+2, x_2 ∈ R, ..., x_n ∈ R} which is all of R^{n-1}.
  Wait, S is not compact. Let me think again.

Take any A, B in the complement.
Path from A to B:
1. A -> A' where A' = A with x_1 coordinate replaced by L+2.
   This is the horizontal path staying at same (x_2, ..., x_n).
   But this might cross a cube!

Better: let me think about which values of x_1 are "free" in the sense that
the "fiber" {x_1 = t} × R^{n-1} is not completely covered by the cubes.

Since each cube covers a bounded set, the fiber at any x_1 = t has complement
in R^{n-1} that is nonempty. But we need the complement to be CONNECTED in R^{n-1},
which requires n-1 >= 2, i.e., n >= 3.

THIS IS THE KEY! For n >= 3:
- Fiber at x_1 = t: remove finitely many bounded boxes from R^{n-1} (n-1 >= 2).
  The complement of finitely many bounded sets in R^{n-1} for n-1 >= 2 is connected.
  (Because we can go around them; the "outer region" connects them.)

For n = 2:
- Fiber at x_1 = t: remove finitely many intervals from R^1.
  This can be disconnected!

So the n > 2 (i.e., n >= 3) condition is NECESSARY for the fiber argument.

But wait — even if individual fibers can be disconnected, the total complement
might still be connected. The n=2 case computed above always gave connected complement.

Let me think more carefully...

For n=2: even if some vertical slices (fibers) are disconnected, the path can
go around the disconnecting cubes in the 2D plane.

For n=1: a fiber is a point, can be disconnected trivially.

So the FIBER argument proves connectedness for n >= 3, but doesn't cover n=2.
For n=2, we need a different argument (perhaps using planarity or winding).

The problem statement saying n > 2 might be because:
1. The fiber argument only covers n >= 3
2. n=2 is actually true but harder to prove
3. The authors wanted to avoid the n=2 case

Let me now verify the fiber argument more carefully computationally.
"""

import itertools
import math

def fiber_complement_connected(n: int, lengths: list, t_value: float, coord: int = 0, resolution: int = 20) -> bool:
    """
    Check if the fiber at x_{coord} = t_value has connected complement in R^{n-1}.
    (i.e., R^{n-1} \ (cross-sections of active cubes) is connected)
    """
    # Build centers
    from connectedness import build_cube_centers, select_n_face_vertices, parallelepiped_vertices

    def build_centers_simple(n, lengths):
        # Inline version
        base = (0.5,) + tuple([-0.5] * (n-1))
        face_verts = [base]
        for i in range(1, n):
            v = list(base); v[i] = 0.5
            face_verts.append(tuple(v))
        def vnorm(v): return math.sqrt(sum(x*x for x in v))
        def vhat(v): nm = vnorm(v); return tuple(x/nm for x in v)
        def vscale(s, v): return tuple(s*x for x in v)
        def vadd(a, b): return tuple(x+y for x,y in zip(a,b))
        edge_vectors = [vscale(lengths[i], vhat(face_verts[i])) for i in range(n)]
        vertices = []
        for signs in itertools.product([-1, 1], repeat=n):
            v = tuple(0.0 for _ in range(n))
            for s, e in zip(signs, edge_vectors):
                v = vadd(v, vscale(s, e))
            vertices.append(v)
        return [tuple(0.0 for _ in range(n))] + vertices

    centers = build_centers_simple(n, lengths)

    # Active cubes at x_{coord} = t_value
    active_centers = []
    for c in centers:
        if abs(c[coord] - t_value) <= 0.5:
            # Project out coord -> (n-1)-dimensional center
            proj = tuple(c[i] for i in range(n) if i != coord)
            active_centers.append(proj)

    if not active_centers:
        return True  # no cubes at this fiber, complement is all of R^{n-1}

    m = n - 1  # fiber dimension
    if m == 0:
        return True  # trivially

    # Grid in R^{m}
    max_c = max(abs(c[i]) for c in active_centers for i in range(m)) + 1.5
    step = (2 * max_c) / resolution

    grid = {}
    for idx in itertools.product(range(resolution+1), repeat=m):
        pt = tuple(-max_c + idx[i]*step for i in range(m))
        in_union = any(all(abs(pt[j] - c[j]) <= 0.5 for j in range(m)) for c in active_centers)
        grid[idx] = not in_union

    comp_pts = {k for k,v in grid.items() if v}
    if not comp_pts:
        return False

    # BFS
    from collections import deque
    start = None
    for corner in itertools.product([0, resolution], repeat=m):
        if grid.get(corner, False):
            start = corner
            break
    if start is None:
        return False

    visited = {start}
    queue = deque([start])
    while queue:
        cur = queue.popleft()
        for dim in range(m):
            for delta in [-1, 1]:
                nb = list(cur); nb[dim] += delta; nb = tuple(nb)
                if any(c < 0 or c > resolution for c in nb): continue
                if nb not in visited and grid.get(nb, False):
                    visited.add(nb); queue.append(nb)

    return len(visited) == len(comp_pts)

def test_fiber_connectivity():
    """Test whether fibers are connected for various n and lengths."""
    print("=== Fiber connectivity test ===")
    print("(Is R^{n-1} minus cross-sections connected at various x_0 values?)\n")

    cases = [
        (3, [1.0, 1.0, 1.0]),
        (3, [0.5, 0.5, 0.5]),
        (3, [2.0, 2.0, 2.0]),
        (2, [1.0, 1.0]),
        (2, [0.3, 0.3]),
    ]

    for n, lengths in cases:
        print(f"n={n}, lengths={lengths}:")
        t_values = [-2.0, -1.0, -0.5, 0.0, 0.5, 1.0, 2.0]
        all_connected = True
        for t in t_values:
            conn = fiber_complement_connected(n, lengths, t, coord=0, resolution=20)
            if not conn:
                all_connected = False
                print(f"  t={t:.1f}: DISCONNECTED fiber!")
        if all_connected:
            print(f"  All tested fibers connected.")
        print()

if __name__ == "__main__":
    print(__doc__)
    test_fiber_connectivity()

    print("""
=== SUMMARY OF PROOF STRATEGY ===

For n >= 3 (n > 2):
  Given any two points A, B in R^n \ C:
  1. Choose a coordinate direction x_j "not blocked" by any cube center projection.
     (Possible since finitely many cubes project to measure-zero sets in x_j coord.)
  2. In the fiber at appropriate x_j value, the fiber complement in R^{n-1} is connected
     (because n-1 >= 2 and we're removing finitely many bounded sets from R^{n-1}).
  3. Connect A to B via this fiber.

For n = 2:
  The fiber argument fails (fibers are in R^1, can be disconnected by intervals).
  But the complement is still connected because the cubes form a "compact obstacle"
  and R^2 minus a compact set is path-connected... wait, is it?

  R^2 minus a DISK is connected: yes.
  R^2 minus a SOLID TORUS (embedded in R^3) is... in R^3.

  In R^2: R^2 minus a compact convex body is connected.
  R^2 minus a finite union of compact convex bodies is connected.

  Actually: R^2 minus finitely many compact sets is connected if the compact sets
  don't form a "closed curve" separating R^2. For convex bodies, this can't happen.

  But: axis-aligned squares are convex bodies. Their union is connected (possibly).
  The complement of a connected compact simply-connected set in R^2 might be
  disconnected (e.g., complement of a filled square = connected).

  Wait: R^2 minus a closed square IS connected (you can go around it).
  R^2 minus 5 closed squares IS connected (you can go around all of them from outside).

  The complement is connected iff you can go from any exterior point to any other.
  Since the union of cubes is bounded, the far-away region is all connected.
  From any exterior point, you can reach the far-away region... unless the union
  forms a "ring" around you.

  5 axis-aligned squares cannot form a ring in R^2 that traps a point.
  (A ring would require a Jordan curve formed by the boundary of the union.)
  The boundary of the union of 5 squares is a rectilinear polygon.
  For this polygon to be a closed curve separating R^2, it would need to be
  a Jordan curve — but with 5 squares in the specific configuration described,
  this would require exact overlap to close the ring.

  Actually, 5 squares CAN form a ring: imagine 4 squares arranged around a central gap,
  with 1 closing the ring. But with our specific parallelepiped arrangement, can this happen?

  The n=2 case with l = 1/√2 gives centers at (0,0), (0,±1), (±1,0).
  The squares at (0,±1) and (±1,0) each touch the center square.
  Do they form a ring? No — the four off-center squares are at ±1 in one axis,
  and they all touch the center, but they DON'T form a closed ring in R^2.
  The region between e.g. (1,0) and (0,1) is NOT enclosed.

CONCLUSION:
  For n >= 2, the complement appears always connected.
  The n > 2 condition in the problem might be for a PROOF technique reason,
  not a counterexample reason. The conjecture may hold for n = 2 as well.

  The clean proof for n >= 3 uses the fiber argument.
  A proof for n = 2 would need a different approach.
""")
