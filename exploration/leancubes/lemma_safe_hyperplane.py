"""
LEMMA: Safe Hyperplane Routing

CLAIM: If two points T_A, T_B both have coordinate k equal to S,
where S > M (M = max |cj[k]| + h over all cubes cj), then the
segment T_A -> T_B avoids all cubes.

This is one component of the full connectedness proof. It handles
the "middle segment" in the 3-segment path A -> T_A -> T_B -> B.

DEPENDENCIES: None (pure logical argument + verification).
"""

from typing import List, Tuple

Vec = Tuple[float, ...]


def _cube_contains(center: Vec, cube_half: float, point: Vec) -> bool:
    """True iff point is in the closed cube [c-h, c+h]^n."""
    return all(abs(point[i] - center[i]) <= cube_half for i in range(len(center)))


def _segment_hits_cube_exact(A: Vec, B: Vec, center: Vec, cube_half: float = 0.5) -> bool:
    """
    LEMMA: Exact segment-cube intersection test.

    Does segment A->B (parameterized as gamma(t) = A + t*(B-A), t in [0,1])
    intersect the closed axis-aligned cube [c-h, c+h]^n?

    PROOF: Uses the slab method. For each coordinate i, compute the t-interval
    where gamma_i(t) is in [c[i]-h, c[i]+h]. The segment hits the cube iff the
    intersection of all per-coordinate t-intervals with [0,1] is nonempty.

    Per coordinate i:
      gamma_i(t) = A[i] + t*(B[i]-A[i]) in [c[i]-h, c[i]+h]
      If B[i]-A[i] = 0: check A[i] in [c[i]-h, c[i]+h]. If not, MISS.
      If B[i]-A[i] != 0: t in [(c[i]-h-A[i])/(B[i]-A[i]), (c[i]+h-A[i])/(B[i]-A[i])].
      (Swap if denominator negative.)

    Intersect all t-intervals. If result is [t_lo, t_hi] with t_lo <= t_hi: HIT.
    """
    n = len(A)
    t_lo, t_hi = 0.0, 1.0
    for i in range(n):
        d = B[i] - A[i]
        off = A[i] - center[i]
        if abs(d) < 1e-15:
            if abs(off) > cube_half + 1e-15:
                return False
        else:
            lo_t = (-cube_half - off) / d
            hi_t = (cube_half - off) / d
            if d < 0:
                lo_t, hi_t = hi_t, lo_t
            t_lo = max(t_lo, lo_t)
            t_hi = min(t_hi, hi_t)
            if t_lo > t_hi + 1e-14:
                return False
    return t_lo <= t_hi + 1e-14


def _segment_clear(A: Vec, B: Vec, centers: List[Vec], cube_half: float = 0.5) -> bool:
    """True iff segment A->B avoids all cubes in the list."""
    return not any(_segment_hits_cube_exact(A, B, c, cube_half) for c in centers)


# ============================================================
# MAIN LEMMA
# ============================================================

def lemma_one_coord_safe(seg_A: Vec, seg_B: Vec, coord: int,
                          M: float, cube_centers: List[Vec],
                          cube_half: float = 0.5) -> bool:
    """
    LEMMA: If seg_A[coord] == seg_B[coord] == S and |S - cj[coord]| > cube_half
    for all cubes cj, then the segment seg_A -> seg_B avoids all cubes.

    VERIFIED: problems/Geometry/Leancubes/SafeHyperplane.lean
              theorem segment_avoids_cube_if_coord_separated
    """
    S_val = seg_A[coord]
    if seg_A[coord] != seg_B[coord]:
        return False
    for cj in cube_centers:
        if not (abs(S_val - cj[coord]) > cube_half):
            return False
    return True


# ============================================================
# TESTS
# ============================================================

def run_tests():
    import math, itertools, random

    print("=" * 60)
    print("LEMMA: Safe Hyperplane Routing")
    print("=" * 60)

    # --- Build a test cube configuration ---
    def build_cube_centers_3d(lengths):
        """Build 2^3 + 1 = 9 cube centers for the Leancubes problem in R^3."""
        n = 3
        base = (0.5,) + tuple([-0.5] * (n - 1))
        face_verts = [base]
        for i in range(1, n):
            v = list(base); v[i] = 0.5; face_verts.append(tuple(v))

        def vhat(v):
            nm = math.sqrt(sum(x*x for x in v))
            return tuple(x/nm for x in v)

        edge = [tuple(lengths[i] * x for x in vhat(face_verts[i])) for i in range(n)]
        para_verts = []
        for signs in itertools.product([-1, 1], repeat=n):
            v = tuple(sum(signs[i] * edge[i][j] for i in range(n)) for j in range(n))
            para_verts.append(v)
        return [tuple(0.0 for _ in range(n))] + para_verts

    # Test 1: Basic correctness of _segment_hits_cube_exact
    print("\n--- Test 1: _segment_hits_cube_exact ---")
    assert _segment_hits_cube_exact((0.0, 0.0, 0.0), (0.4, 0.0, 0.0), (0.0, 0.0, 0.0)) == True
    assert _segment_hits_cube_exact((2.0, 0.0, 0.0), (3.0, 0.0, 0.0), (0.0, 0.0, 0.0)) == False
    assert _segment_hits_cube_exact((-1.0, -1.0, -1.0), (1.0, 1.0, 1.0), (0.0, 0.0, 0.0)) == True
    # Segment along face: just barely touching
    assert _segment_hits_cube_exact((0.5, 0.0, 0.0), (0.5, 1.0, 0.0), (0.0, 0.0, 0.0)) == True
    # Segment clearly outside
    assert _segment_hits_cube_exact((0.6, 0.0, 0.0), (0.6, 1.0, 0.0), (0.0, 0.0, 0.0)) == False
    print("  PASS")

    # Test 2: lemma_one_coord_safe with Leancubes configuration
    print("\n--- Test 2: lemma_one_coord_safe ---")
    centers = build_cube_centers_3d([1.0, 1.0, 1.0])
    M = max(abs(c[i]) for c in centers for i in range(3)) + 0.5
    S = M + 1.0

    # Two points with coord 0 = S
    T_A = (S, 0.0, 0.0)
    T_B = (S, 5.0, -3.0)
    proved = lemma_one_coord_safe(T_A, T_B, 0, M, centers)
    verified = _segment_clear(T_A, T_B, centers)
    assert proved, f"Lemma should return True: S={S}, M={M}"
    assert verified, f"Segment should be clear (verified)"
    print(f"  T_A={T_A}, T_B={T_B}")
    print(f"  S={S:.4f}, M={M:.4f}")
    print(f"  Lemma returns: {proved}, Verified clear: {verified}")

    # Test many random pairs on the hyperplane
    random.seed(42)
    n_pairs = 100
    all_ok = True
    for _ in range(n_pairs):
        t_a = tuple(S if i == 0 else random.uniform(-10, 10) for i in range(3))
        t_b = tuple(S if i == 0 else random.uniform(-10, 10) for i in range(3))
        p = lemma_one_coord_safe(t_a, t_b, 0, M, centers)
        v = _segment_clear(t_a, t_b, centers)
        if not p or not v:
            print(f"  FAIL: {t_a} -> {t_b}, proved={p}, clear={v}")
            all_ok = False
    print(f"  Random pairs on hyperplane: {n_pairs}/{n_pairs} {'PASS' if all_ok else 'FAIL'}")
    assert all_ok

    # Test 3: Negative cases (precondition violated)
    print("\n--- Test 3: Negative cases ---")
    # Different coord values
    assert not lemma_one_coord_safe((S, 0.0, 0.0), (S+1, 0.0, 0.0), 0, M, centers)
    # S not > M
    assert not lemma_one_coord_safe((M - 1, 0.0, 0.0), (M - 1, 1.0, 0.0), 0, M, centers)
    print("  PASS")

    # Test 4: Different coord choices
    print("\n--- Test 4: Different coord (coord=1) ---")
    T_C = (0.0, S, 0.0)
    T_D = (5.0, S, -3.0)
    proved2 = lemma_one_coord_safe(T_C, T_D, 1, M, centers)
    verified2 = _segment_clear(T_C, T_D, centers)
    assert proved2 and verified2
    print(f"  coord=1, S={S:.4f}: proved={proved2}, clear={verified2}")
    print("  PASS")

    # Test 5: Larger configurations
    print("\n--- Test 5: Larger configurations ---")
    for lengths, label in [
        ([2.0, 2.0, 2.0], "large"),
        ([0.5, 1.0, 2.0], "mixed"),
        ([10.0, 10.0, 10.0], "very large"),
        ([0.1, 5.0, 3.0], "extreme"),
    ]:
        c = build_cube_centers_3d(lengths)
        m = max(abs(c_i[j]) for c_i in c for j in range(3)) + 0.5
        s = m + 1.0
        ta = (s, 0.0, 0.0)
        tb = (s, 100.0, -50.0)
        p = lemma_one_coord_safe(ta, tb, 0, m, c)
        v = _segment_clear(ta, tb, c)
        status = "PASS" if (p and v) else "FAIL"
        print(f"  {label:<15} M={m:.2f}, S={s:.2f}: {status}")
        assert p and v

    # Test 6: Consistency - lemma True implies segment clear for ALL cubes
    print("\n--- Test 6: Exhaustive verification ---")
    # For every cube in a large config, verify the coord-0 constraint fails
    centers_big = build_cube_centers_3d([5.0, 5.0, 5.0])
    M_big = max(abs(c[i]) for c in centers_big for i in range(3)) + 0.5
    S_big = M_big + 1.0
    for cj in centers_big:
        dist = abs(S_big - cj[0])
        assert dist > 0.5, f"S={S_big}, cj[0]={cj[0]}, dist={dist}"
    print(f"  All {len(centers_big)} cubes: |S - cj[0]| > 0.5 verified")
    print("  PASS")

    print("\n" + "=" * 60)
    print("ALL TESTS PASSED")
    print("=" * 60)
    print("""
PROOF SUMMARY:
  lemma_one_coord_safe(T_A, T_B, coord, M, cubes) -> True

  Precondition: T_A[coord] = T_B[coord] = S > M, where M = max|cj[coord]| + h.

  Proof: gamma(t)[coord] = S for all t in [0,1].
         For any cube cj: |S - cj[coord]| > h (since S > M = max|cj[coord]| + h).
         Cube requires ALL coords in slab. Coord `coord` is NOT in slab. MISS. QED.

  This lemma is UNCONDITIONAL: it holds for ANY cube configuration, ANY dimension,
  ANY S > M, and ANY T_A, T_B with matching coord values. No gaps.
""")


if __name__ == "__main__":
    run_tests()
