"""
Dimension analysis: why does n > 2 matter?

Let's carefully analyze each small n.

n=1:
- C_0 is the interval [-1/2, 1/2]
- "One face" of C_0 in R^1: a face is a 0D face = a point = {-1/2} or {1/2}
- "n=1 distinct vertices of one face": we pick 1 vertex from the face {-1/2} or {1/2}
- That's just one point, say v = -1/2 or v = 1/2
- Ray from origin (center) through v, length l: endpoint at l * sign(v) * 1 = ±l
- Parallelepiped in R^1 with 1 direction vector: has 2^1 = 2 vertices at ±l * hat(v)
  If we use the +face (v = 1/2), hat(v) = 1, so vertices at +l and -l
- Place unit intervals at x = +l and x = -l
- Union C = [-1/2, 1/2] ∪ [-l-1/2, -l+1/2] ∪ [l-1/2, l+1/2]
- This has 3 components (if l > 1)
- The complement R \ C has 2 bounded components and 2 unbounded components
  WAIT: if l > 1, the intervals are disjoint, so complement has gaps BETWEEN them
  But the complement of the union of intervals is a union of intervals itself,
  and it's disconnected if there are isolated gaps.

For l > 1: R \ C = (-∞, -l-1/2) ∪ (-l+1/2, -1/2) ∪ (1/2, l-1/2) ∪ (l+1/2, ∞)
  This has 4 connected components (4 intervals). DISCONNECTED!

For l = 1: right endpoints touch. [-3/2, -1/2] ∪ [-1/2, 1/2] ∪ [1/2, 3/2] = [-3/2, 3/2]
  Complement: (-∞, -3/2) ∪ (3/2, ∞) — two components. STILL DISCONNECTED!

For l < 1: all three intervals overlap into one big interval. Complement connected.

So for n=1, the complement CAN be disconnected. This is why n=1 is excluded.

n=2:
- C_0 is a unit square centered at origin
- "One face" = one edge (1D face), which has 2 vertices
- We pick n=2 vertices from this 2-vertex edge — we pick BOTH vertices
- The edge, say top edge, has vertices (-1/2, 1/2) and (1/2, 1/2)
- Edge vectors: l_1 * hat(-1/2, 1/2) and l_2 * hat(1/2, 1/2)
  = l_1/√2 * (-1, 1) and l_2/√2 * (1, 1)

Let e_1 = (l_1/√2)(-1, 1) and e_2 = (l_2/√2)(1, 1)

The 4 parallelepiped vertices are:
  ±e_1 ± e_2

For l_1 = l_2 = l:
  (+e_1 + e_2) = (l/√2)(0, 2) = (0, l√2)
  (+e_1 - e_2) = (l/√2)(-2, 0) = (-l√2, 0)
  (-e_1 + e_2) = (l/√2)(2, 0) = (l√2, 0)
  (-e_1 - e_2) = (l/√2)(0, -2) = (0, -l√2)

So the 4 cube centers are: (0, l√2), (-l√2, 0), (l√2, 0), (0, -l√2)
Plus C_0 at origin.

This is 5 squares arranged in a "plus" pattern!
The centers are at distance l√2 from origin.

For large l, these 5 squares are far apart (no overlap).
Can they disconnect R^2?

Connectivity of complement of 5 non-overlapping unit squares:
The complement of a finite collection of convex bodies in R^2 is simply connected
if and only if no bounded complementary component exists.

With 5 isolated squares, the complement is R^2 minus 5 disjoint squares.
This is connected (you can go around any individual square), and simply connected
is NOT guaranteed — actually no, removing 5 disjoint disks from R^2 gives a
multiply-connected domain (5 "holes") but it IS still connected.

KEY DISTINCTION: connected vs simply connected.
The complement is CONNECTED but not simply connected when we remove compact sets in R^2.

So for n=2, the complement is also always connected!

n=1 is the exception because R^1 has "codimension 0" for its subsets — an interval
can completely block R^1.

So WHY does the problem say n > 2?

Hypothesis 1: The problem is wrong about n=2 being a counterexample.
(Maybe n > 2 is just a sufficient condition, not necessary.)

Hypothesis 2: There's a specific n=2 case where the complement IS disconnected.

Hypothesis 3: The "n > 2" condition is needed for the PROOF, not for the result.
(The result holds for n=2 too, but the proof works more cleanly for n>2.)

Let me verify hypothesis 2 by being more careful about what can happen in n=2.
"""

import itertools
import math
from collections import deque

def build_centers_n2(l1: float, l2: float) -> list:
    """
    For n=2, using top face vertices (-1/2, 1/2) and (1/2, 1/2).
    """
    v1 = (-0.5, 0.5)
    v2 = (0.5, 0.5)
    norm1 = math.sqrt(0.5**2 + 0.5**2)
    norm2 = math.sqrt(0.5**2 + 0.5**2)
    e1 = (l1 * v1[0] / norm1, l1 * v1[1] / norm1)
    e2 = (l2 * v2[0] / norm2, l2 * v2[1] / norm2)

    # 4 parallelepiped vertices: ±e1 ± e2
    para_verts = [
        (s1 * e1[0] + s2 * e2[0], s1 * e1[1] + s2 * e2[1])
        for s1, s2 in itertools.product([-1, 1], repeat=2)
    ]
    return [(0.0, 0.0)] + para_verts

def print_n2_centers(l: float):
    centers = build_centers_n2(l, l)
    print(f"\nl={l:.2f}: cube centers = {[(round(c[0],3), round(c[1],3)) for c in centers]}")
    # Check for overlap: two cubes overlap if |c1-c2|_inf < 1
    for i in range(len(centers)):
        for j in range(i+1, len(centers)):
            c1, c2 = centers[i], centers[j]
            dist_inf = max(abs(c1[k] - c2[k]) for k in range(2))
            if dist_inf < 1.0:
                print(f"  Overlap: C_{i} and C_{j} (inf-dist = {dist_inf:.3f})")

def check_n2_all_lengths():
    """Check many l values for n=2"""
    print("=== n=2: all lengths equal ===")
    for l_int in range(1, 51):
        l = l_int * 0.1
        centers = build_centers_n2(l, l)

        # Grid check
        max_c = max(abs(c[i]) for c in centers for i in range(2)) + 1.5
        res = 40
        step = (2 * max_c) / res
        grid = {}
        for idx in itertools.product(range(res+1), repeat=2):
            pt = ((-max_c + idx[0]*step), (-max_c + idx[1]*step))
            in_union = any(abs(pt[0]-c[0]) <= 0.5 and abs(pt[1]-c[1]) <= 0.5 for c in centers)
            grid[idx] = not in_union

        comp_pts = {k for k,v in grid.items() if v}
        # Find a corner start
        start = None
        for corner in itertools.product([0, res], repeat=2):
            if grid.get(corner, False):
                start = corner
                break
        if start is None:
            print(f"l={l:.1f}: no valid start")
            continue

        visited = {start}
        queue = deque([start])
        while queue:
            cur = queue.popleft()
            for dim in range(2):
                for delta in [-1, 1]:
                    nb = list(cur); nb[dim] += delta; nb = tuple(nb)
                    if any(c < 0 or c > res for c in nb): continue
                    if nb not in visited and grid.get(nb, False):
                        visited.add(nb); queue.append(nb)

        conn = (len(visited) == len(comp_pts))
        if not conn:
            print(f"l={l:.1f}: DISCONNECTED! comp={len(comp_pts)}, reach={len(visited)}")

    print("Done checking n=2")

# ---- Think about n=2 algebraically ----

def analyze_n2_geometry():
    """
    For n=2 with l_1 = l_2 = l:
    Centers: (0,0), (0, l√2), (-l√2, 0), (l√2, 0), (0, -l√2)

    Each cube has side 1. The union is 5 unit squares.

    For the complement to be disconnected, we'd need to "trap" some region.
    The 5 squares arranged in a + pattern: can they trap a square of air in the middle?

    The square at origin covers [-1/2, 1/2]^2.
    The square at (l√2, 0) covers [l√2-1/2, l√2+1/2] × [-1/2, 1/2].

    For these to "touch" (share boundary), we need l√2 - 1/2 = 1/2, so l = 1/√2 ≈ 0.707.
    For l < 1/√2: they overlap.
    For l = 1/√2: they share a boundary.
    For l > 1/√2: they're separated.

    Can the union form a closed curve in R^2?
    With 5 squares, the boundary of the union can be complex, but for the complement
    to be disconnected, the boundary would need to form a Jordan curve.

    In this arrangement (l > 1/√2), the 5 squares are separate. The complement
    is R^2 minus 5 squares = one connected set (you can go around all of them).

    For l < 1/√2: they form a connected blob. The complement is still connected.

    CONCLUSION: For n=2, the complement is ALWAYS connected with this construction.
    The n > 2 condition might be conservative, or needed for a specific edge case
    I'm not seeing.
    """
    l = 1.0 / math.sqrt(2)
    print(f"\n=== n=2, critical length l=1/sqrt(2) = {l:.4f} ===")
    centers = build_centers_n2(l, l)
    print(f"Centers: {[(round(c[0],3), round(c[1],3)) for c in centers]}")
    # Check distances
    for i in range(len(centers)):
        for j in range(i+1, len(centers)):
            c1, c2 = centers[i], centers[j]
            dist_inf = max(abs(c1[k] - c2[k]) for k in range(2))
            dist_euc = math.sqrt(sum((c1[k]-c2[k])**2 for k in range(2)))
            if dist_inf <= 1.0:
                print(f"  C_{i}-C_{j}: inf-dist={dist_inf:.3f}, euc-dist={dist_euc:.3f} (touching or overlapping)")

if __name__ == "__main__":
    print("=== n=1 analysis ===")
    print("For n=1: the cube is an interval, 3 intervals total.")
    print("The complement CAN be disconnected (e.g., for l > 1, 3 separate intervals).")
    print("This is why n=1 fails the conjecture.\n")

    for l in [0.5, 1.0, 1.5]:
        print(f"n=1, l={l}:")
        # 3 intervals: [-0.5, 0.5], [-l-0.5, -l+0.5], [l-0.5, l+0.5]
        intervals = [(-0.5, 0.5), (-l-0.5, -l+0.5), (l-0.5, l+0.5)]
        # Sort by left endpoint
        intervals.sort()
        print(f"  Intervals: {[(round(a,2), round(b,2)) for a,b in intervals]}")
        # Check gaps
        merged = [intervals[0]]
        for (a, b) in intervals[1:]:
            if a <= merged[-1][1]:  # overlap or touch
                merged[-1] = (merged[-1][0], max(merged[-1][1], b))
            else:
                merged.append((a, b))
        print(f"  After merging: {[(round(a,2), round(b,2)) for a,b in merged]}")
        print(f"  Gaps (complement components): {len(merged)+1}")  # +1 for unbounded parts

    print()
    analyze_n2_geometry()
    print()
    print_n2_centers(0.5)
    print_n2_centers(1.0)
    print_n2_centers(2.0)
    print()
    check_n2_all_lengths()
