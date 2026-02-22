"""
Phase 1: Understand the cube-parallelepiped geometry.

Setup:
- C_0: axis-aligned unit cube in R^n centered at origin
- A unit cube in R^n has 2^n vertices at (±1/2, ..., ±1/2)
- A face of C_0 is an (n-1)-dimensional face with 2^(n-1) vertices
- We pick ONE face and select n vertices from it
- Project n rays from origin through these n vertices, extended to lengths l_i
- These n ray endpoints define a parallelepiped with 2^n vertices
- At each parallelepiped vertex, center a unit cube C_i
- Total cubes: 2^n + 1 (including C_0)
"""

import itertools
import math
from typing import List, Tuple

# ---- Vector arithmetic (pure Python) ----

Vec = Tuple[float, ...]

def vadd(a: Vec, b: Vec) -> Vec:
    return tuple(x + y for x, y in zip(a, b))

def vsub(a: Vec, b: Vec) -> Vec:
    return tuple(x - y for x, y in zip(a, b))

def vscale(s: float, v: Vec) -> Vec:
    return tuple(s * x for x in v)

def vnorm(v: Vec) -> float:
    return math.sqrt(sum(x*x for x in v))

def vhat(v: Vec) -> Vec:
    n = vnorm(v)
    return tuple(x / n for x in v)

def vzero(n: int) -> Vec:
    return tuple(0.0 for _ in range(n))

# ---- Geometry primitives ----

def unit_cube_vertices(n: int) -> List[Vec]:
    """All 2^n vertices of the unit cube centered at origin in R^n."""
    return list(itertools.product([-0.5, 0.5], repeat=n))

def faces_of_unit_cube(n: int) -> List[List[Vec]]:
    """
    Each face is defined by fixing one coordinate to ±1/2.
    Returns list of faces; each face is a list of 2^(n-1) vertices.
    """
    verts = unit_cube_vertices(n)
    faces = []
    for coord in range(n):
        for val in [-0.5, 0.5]:
            face = [v for v in verts if v[coord] == val]
            faces.append(face)
    return faces

def select_n_vertices_from_face(face: List[Vec], n: int) -> List[Vec]:
    """
    Pick n vertices from a face (which has 2^(n-1) vertices).
    We want n linearly independent directions.
    Simple approach: take the first n vertices of the face.
    """
    assert len(face) >= n, f"Face has {len(face)} vertices, need {n}"
    return face[:n]

# ---- Parallelepiped construction ----

def parallelepiped_vertices(face_verts: List[Vec], lengths: List[float]) -> List[Vec]:
    """
    Given n face vertices (direction vectors from origin) and n lengths,
    compute the 2^n vertices of the parallelepiped.

    Each edge vector e_i = l_i * hat(face_vert[i]).
    The 2^n vertices are all combinations: sum of s_i * e_i for s_i in {-1, +1}.
    """
    n = len(lengths)
    assert len(face_verts) == n

    edge_vectors = [vscale(lengths[i], vhat(face_verts[i])) for i in range(n)]

    vertices = []
    for signs in itertools.product([-1, 1], repeat=n):
        v = vzero(n)
        for s, e in zip(signs, edge_vectors):
            v = vadd(v, vscale(s, e))
        vertices.append(v)

    return vertices

def build_cube_centers(n: int, face_verts: List[Vec], lengths: List[float]) -> List[Vec]:
    """
    Build all cube centers:
    - C_0 at origin
    - 2^n cubes at parallelepiped vertices
    """
    para_verts = parallelepiped_vertices(face_verts, lengths)
    centers = [vzero(n)] + para_verts
    return centers

# ---- Point-in-cube test ----

def point_in_cube(center: Vec, point: Vec) -> bool:
    """Is point strictly inside axis-aligned unit cube centered at center?"""
    return all(abs(point[i] - center[i]) < 0.5 for i in range(len(center)))

def point_in_any_cube(centers: List[Vec], point: Vec) -> bool:
    return any(point_in_cube(c, point) for c in centers)

# ---- Print examples for n=3 ----

def example_n3(lengths: List[float]):
    n = 3
    # Use the top face (z=+0.5), pick n=3 vertices
    top_face = [v for v in unit_cube_vertices(n) if v[2] == 0.5]
    chosen = select_n_vertices_from_face(top_face, n)

    centers = build_cube_centers(n, chosen, lengths)

    print(f"\n=== n=3 example, lengths={lengths} ===")
    print(f"Direction vertices (from top face): {chosen}")
    print(f"Total cubes: {len(centers)} (expected {2**n + 1})")
    for i, c in enumerate(centers):
        label = "C_0" if i == 0 else f"C_{i}"
        print(f"  {label}: ({', '.join(f'{x:.3f}' for x in c)})")
    return centers

# ---- Sanity checks ----

def check_cube_count(n: int) -> bool:
    """Total cubes should be 2^n + 1."""
    face = faces_of_unit_cube(n)[1]  # positive face
    chosen = select_n_vertices_from_face(face, n)
    lengths = [1.0] * n
    centers = build_cube_centers(n, chosen, lengths)
    expected = 2**n + 1
    actual = len(centers)
    ok = (actual == expected)
    status = "OK" if ok else "FAIL"
    print(f"n={n}: cube count = {actual}, expected {expected}: {status}")
    return ok

def check_independence(face_verts: List[Vec]) -> bool:
    """
    Check that the n face vertices give linearly independent directions.
    Use Gram-Schmidt rank check (pure Python, no numpy).
    """
    n = len(face_verts)
    vecs = [vhat(v) for v in face_verts]
    # Gram-Schmidt
    basis = []
    for v in vecs:
        w = v
        for b in basis:
            dot = sum(w[i]*b[i] for i in range(n))
            w = vsub(w, vscale(dot, b))
        norm = vnorm(w)
        if norm < 1e-10:
            return False  # linearly dependent
        basis.append(vscale(1/norm, w))
    return len(basis) == n

if __name__ == "__main__":
    print("=== Face structure ===")
    for n in [3, 4, 5]:
        faces = faces_of_unit_cube(n)
        face = faces[1]  # positive x face
        chosen = select_n_vertices_from_face(face, n)
        indep = check_independence(chosen)
        print(f"n={n}: face has {len(face)} vertices, pick {n}, independent={indep}")

    print()
    print("=== Cube count checks ===")
    for n in range(2, 6):
        check_cube_count(n)

    print()
    example_n3([1.0, 1.0, 1.0])
    example_n3([0.5, 1.0, 2.0])
    example_n3([0.1, 0.1, 0.1])
    example_n3([3.0, 0.3, 1.5])

    print("""
=== Summary of geometry ===
- n=3: C_0 + 8 unit cubes at parallelepiped vertices = 9 total cubes
- The parallelepiped edges are the scaled direction vectors
- All cubes are axis-aligned regardless of direction vectors
- The direction vectors come from face vertices of C_0, so they
  have a specific structure: one coordinate fixed at ±1/2, rest ±1/2
""")
