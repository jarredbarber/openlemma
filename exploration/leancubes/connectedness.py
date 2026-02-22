"""
Phase 2: Test connectedness of R^n \ C numerically via grid discretization.

Strategy:
- Discretize R^n on a grid
- Mark grid points inside any cube
- Check if complement is connected via BFS flood-fill from a far-away point
- Test various l_i choices for n=3

Key: we need a bounding box large enough to contain all cubes plus some buffer,
and a "starting point" for BFS that's outside all cubes.
"""

import itertools
import math
from collections import deque
from typing import List, Tuple, Optional

Vec = Tuple[float, ...]

# ---- Pure python geometry (repeated from geometry.py) ----

def vadd(a: Vec, b: Vec) -> Vec:
    return tuple(x + y for x, y in zip(a, b))

def vsub(a: Vec, b: Vec) -> Vec:
    return tuple(x - y for x, y in zip(a, b))

def vscale(s: float, v: Vec) -> Vec:
    return tuple(s * x for x in v)

def vnorm(v: Vec) -> float:
    return math.sqrt(sum(x*x for x in v))

def vhat(v: Vec) -> Vec:
    nm = vnorm(v)
    return tuple(x / nm for x in v)

def vzero(n: int) -> Vec:
    return tuple(0.0 for _ in range(n))

def unit_cube_vertices(n: int) -> List[Vec]:
    return list(itertools.product([-0.5, 0.5], repeat=n))

def select_n_face_vertices(n: int) -> List[Vec]:
    """
    Select n linearly independent vertices from the positive x_0 face.
    Strategy: pick vertices that differ in each coordinate one at a time.
    """
    # positive x_0 face: x_0 = 0.5, others can be ±0.5
    # We want n independent directions from origin.
    # Use: v_0 = (0.5, -0.5, -0.5, ..., -0.5)  [base vertex]
    #      v_1 = v_0 with x_1 flipped to +0.5
    #      v_2 = v_0 with x_2 flipped to +0.5
    #      ...
    #      v_{n-1} = v_0 with x_{n-1} flipped to +0.5
    base = tuple([-0.5] * n)
    base = (0.5,) + base[1:]  # x_0 = +0.5
    verts = [base]
    for i in range(1, n):
        v = list(base)
        v[i] = 0.5  # flip coordinate i
        verts.append(tuple(v))
    return verts

def parallelepiped_vertices(face_verts: List[Vec], lengths: List[float]) -> List[Vec]:
    """2^n vertices of the parallelepiped defined by n edge vectors."""
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
    """Build all 2^n + 1 cube centers using the canonical face vertex selection."""
    face_verts = select_n_face_vertices(n)
    para_verts = parallelepiped_vertices(face_verts, lengths)
    return [vzero(n)] + para_verts

# ---- Grid-based connectedness check ----

def point_in_cube(center: Vec, point: Vec) -> bool:
    """Is point inside (closed) axis-aligned unit cube centered at center?"""
    return all(abs(point[i] - center[i]) <= 0.5 for i in range(len(center)))

def make_grid(n: int, centers: List[Vec], resolution: int) -> Tuple[dict, float, float]:
    """
    Create a grid covering all cubes plus buffer.
    Returns: (grid_dict, grid_min, step)
    grid_dict: maps integer coords tuple -> True if in complement
    """
    # Bounding box of cube centers
    max_coord = max(abs(c[i]) for c in centers for i in range(n)) + 1.5  # 1.5 = cube radius + buffer
    grid_min = -max_coord
    grid_max = max_coord
    step = (grid_max - grid_min) / resolution

    grid = {}
    count_interior = 0
    count_total = 0

    # Iterate over all grid points
    for idx in itertools.product(range(resolution + 1), repeat=n):
        point = tuple(grid_min + idx[i] * step for i in range(n))
        in_union = any(point_in_cube(c, point) for c in centers)
        grid[idx] = not in_union  # True = in complement
        count_total += 1
        if in_union:
            count_interior += 1

    return grid, grid_min, step, resolution, count_interior, count_total

def bfs_flood_fill(grid: dict, start: tuple, resolution: int, n: int) -> set:
    """BFS from start through complement points. Returns connected component."""
    if not grid.get(start, False):
        return set()  # start is inside a cube

    visited = set()
    queue = deque([start])
    visited.add(start)

    while queue:
        current = queue.popleft()
        # Check all 2n neighbors (axis-aligned adjacency)
        for dim in range(n):
            for delta in [-1, 1]:
                neighbor = list(current)
                neighbor[dim] += delta
                neighbor = tuple(neighbor)
                # Check bounds
                if any(coord < 0 or coord > resolution for coord in neighbor):
                    continue
                if neighbor not in visited and grid.get(neighbor, False):
                    visited.add(neighbor)
                    queue.append(neighbor)

    return visited

def complement_is_connected(n: int, lengths: List[float], resolution: int = 20) -> Optional[bool]:
    """
    Check if the complement R^n \ C is connected, discretized on a grid.

    Returns:
    - True: complement appears connected (all exterior grid points reachable from boundary)
    - False: complement has multiple connected components
    - None: couldn't determine (boundary issue, etc.)
    """
    centers = build_cube_centers(n, lengths)
    grid, grid_min, step, res, count_interior, count_total = make_grid(n, centers, resolution)

    # Starting point: corner of the bounding box (should be far from all cubes)
    start = tuple([0] * n)  # grid corner
    # Actually use (0,0,...,0) index = grid_min in all coords, which is far from cubes
    # But we need to verify it's in the complement
    if not grid.get(start, False):
        # Try another corner
        start = tuple([resolution] * n)
        if not grid.get(start, False):
            return None  # can't find a valid start

    # Count complement points
    complement_points = {idx for idx, val in grid.items() if val}

    if not complement_points:
        return None  # degenerate

    # BFS from start
    reachable = bfs_flood_fill(grid, start, resolution, n)

    # Connected iff all complement points are reachable
    connected = (len(reachable) == len(complement_points))
    return connected

# ---- Test suite ----

def test_connectedness_n3(resolution: int = 20) -> bool:
    """
    Test complement connectedness for n=3, various l_i.
    Returns True if all tests pass (complement always connected).
    """
    n = 3
    test_cases = [
        [1.0, 1.0, 1.0],
        [0.5, 0.5, 0.5],
        [0.1, 0.1, 0.1],
        [2.0, 2.0, 2.0],
        [0.5, 1.0, 2.0],
        [0.1, 5.0, 3.0],
        [3.0, 0.3, 1.5],
        [0.01, 0.01, 0.01],  # very small — cubes almost all merge with C_0
        [10.0, 10.0, 10.0],  # very large — cubes far apart
        [1.0, 0.5, 0.25],
    ]

    all_connected = True
    print(f"Testing complement connectedness for n={n}, grid resolution={resolution}")
    print(f"{'Lengths':<30} {'Connected?':<12} {'Complement pts':<15} {'Reachable'}")
    print("-" * 75)

    for lengths in test_cases:
        centers = build_cube_centers(n, lengths)
        grid, grid_min, step, res, count_int, count_total = make_grid(n, centers, resolution)
        complement_points = {idx for idx, val in grid.items() if val}

        start = tuple([0] * n)
        if not grid.get(start, False):
            start = tuple([resolution] * n)
            if not grid.get(start, False):
                print(f"  {str(lengths):<30} {'???':<12}")
                continue

        reachable = bfs_flood_fill(grid, start, resolution, n)
        connected = (len(reachable) == len(complement_points))

        if not connected:
            all_connected = False

        status = "YES" if connected else "NO  <-- COUNTEREXAMPLE"
        print(f"  {str(lengths):<30} {status:<12} {len(complement_points):<15} {len(reachable)}")

    return all_connected

def test_connectedness_n4(resolution: int = 10) -> bool:
    """Test for n=4 (lower resolution due to exponential grid size)."""
    n = 4
    test_cases = [
        [1.0, 1.0, 1.0, 1.0],
        [0.5, 1.0, 2.0, 0.5],
        [2.0, 2.0, 2.0, 2.0],
    ]

    all_connected = True
    print(f"\nTesting complement connectedness for n={n}, grid resolution={resolution}")
    for lengths in test_cases:
        result = complement_is_connected(n, lengths, resolution)
        status = "YES" if result else ("NO <-- COUNTEREXAMPLE" if result is False else "???")
        print(f"  {str(lengths):<40} {status}")
        if result is False:
            all_connected = False

    return all_connected

def test_connectedness_n2(resolution: int = 20) -> bool:
    """
    Test n=2 — the claim is FALSE here (complement can be disconnected).
    We expect to find counterexamples.
    """
    n = 2
    test_cases = [
        [0.6, 0.6],  # small lengths — cubes may merge and disconnect
        [1.0, 1.0],
        [2.0, 2.0],
        [0.3, 0.3],
    ]

    print(f"\nTesting n={n} (claim should FAIL, expect disconnected complement)")
    for lengths in test_cases:
        result = complement_is_connected(n, lengths, resolution)
        status = "connected" if result else ("DISCONNECTED" if result is False else "???")
        print(f"  {str(lengths):<20} {status}")

    return True  # we don't assert anything about n=2

if __name__ == "__main__":
    # First show the face vertices we use
    print("=== Face vertex selection ===")
    for n in [3, 4, 5]:
        verts = select_n_face_vertices(n)
        print(f"n={n}: {verts}")

    print()

    # Main tests
    result_n3 = test_connectedness_n3(resolution=25)
    print(f"\nn=3 all tests connected: {result_n3}")

    test_connectedness_n2(resolution=20)

    result_n4 = test_connectedness_n4(resolution=8)
    print(f"\nn=4 all tests connected: {result_n4}")
