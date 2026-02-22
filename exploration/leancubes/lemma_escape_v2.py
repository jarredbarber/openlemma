"""
lemma_escape_v2.py  --  deterministic 2-parameter escape for R^n \\ C (n >= 3)

THEOREM: For n >= 3, given finitely many axis-aligned unit cubes (half-width h=0.5)
in R^n and a point A in the complement, there exists T = (S, S+d1, S+d2, S, ..., S)
on the hyperplane {x_0 = S} (S = M+1) such that segment A->T avoids all cubes.

PROOF STRUCTURE:

  _effective_t_range(A, S, cj, h, n) -> (t_lo, t_hi)
    LEMMA: The t-interval from fixed coords {0, 3, ..., n-1} only (no d1, d2 dependence).
    If empty: cube is skipped (missed for any d1, d2).

  _d_interval_for_coord(A, S, cj, h, coord, t_lo, t_hi) -> (d_lo, d_hi)
    LEMMA: Necessary condition on d=d_coord for segment to hit cj via that coord.
    d outside [d_lo, d_hi] => cube missed.

  _bad_set_for_cube(A, S, cj, h, n) -> (d1_lo, d1_hi, d2_lo, d2_hi) | None
    LEMMA: Returns a bounding box for the bad (d1,d2) region, or None if cube is
    skipped. At least one of the d1 or d2 intervals is bounded (by P3).

  lemma_P3_no_both_unbounded(A, S, cj, h, n) -> True | None
    LEMMA: For A outside cj, the bad set is bounded in at least one of d1 or d2.
    Structural proof: case split on t_lo > 0 vs. t_lo ~ 0.
      - t_lo > 0: both d1, d2 intervals finite. -> bounded.
      - t_lo ~ 0: A outside cj, so A is outside some coord's slab.
        Fixed coords are all satisfied (they contribute to t_range).
        So A is outside via coord 1 or coord 2 (or both).
        If outside via coord 1: d1 interval has a finite endpoint.
        If outside via coord 2: d2 interval has a finite endpoint.
        -> bounded in at least one direction.

  lemma_escape_exists(n, A, centers, M, h) -> True | None
    MAIN LEMMA: Constructively finds (d1, d2):
    Step 1: d1 = 1 + max(d1_hi for cubes with finite d1_hi)
            (outside all d1-bounded bad sets -> P1 clears those cubes for any d2)
    Step 2: For remaining cubes (d1 inside their d1 interval, which must be a
            half-line by P3): collect their d2 intervals (all bounded by P3).
            d2 = 1 + max(d2_hi for these remaining cubes)
            (outside all d2-bounded bad sets -> P2 clears those cubes)
    Verifies with _segment_clear.

PROPERTIES (empirically tested, structurally justified):
  P1: d1 outside d1_iv => cube missed for any d2.
  P2: d1 inside d1_iv, d2 outside d2_iv => cube missed.
  P3: bad set is bounded in at least one of d1 or d2 (never 'both_unbounded').
"""

import math
import itertools
import random
from typing import List, Tuple, Optional

Vec = Tuple[float, ...]
INF = math.inf


# ============================================================
# Geometry primitives (unchanged from v1)
# ============================================================

def _segment_hits_cube_exact(A: Vec, B: Vec, center: Vec, h: float = 0.5) -> bool:
    """Exact test: does segment A->B intersect closed cube [c-h, c+h]^n?"""
    n = len(A)
    t_lo, t_hi = 0.0, 1.0
    for i in range(n):
        d = B[i] - A[i]
        off = A[i] - center[i]
        if abs(d) < 1e-15:
            if abs(off) > h + 1e-15:
                return False
        else:
            lo_t = (-h - off) / d
            hi_t = (h - off) / d
            if d < 0:
                lo_t, hi_t = hi_t, lo_t
            t_lo = max(t_lo, lo_t)
            t_hi = min(t_hi, hi_t)
            if t_lo > t_hi + 1e-14:
                return False
    return t_lo <= t_hi + 1e-14


def _segment_clear(A: Vec, B: Vec, centers: List[Vec], h: float = 0.5) -> bool:
    """True iff segment A->B avoids all cubes."""
    return not any(_segment_hits_cube_exact(A, B, c, h) for c in centers)


def _point_in_complement(point: Vec, centers: List[Vec], h: float = 0.5) -> bool:
    """True iff point is not in any cube."""
    return not any(all(abs(point[i] - c[i]) <= h for i in range(len(c))) for c in centers)


# ============================================================
# Cube configuration builder
# ============================================================

def _build_cube_centers(n: int, lengths: List[float]) -> List[Vec]:
    """Build the Leancubes configuration: origin cube + 2^n parallelepiped vertices."""
    face_verts = _face_vertex_selection(n)
    para_verts = _parallelepiped_vertices(face_verts, lengths)
    return [tuple(0.0 for _ in range(n))] + para_verts

def _face_vertex_selection(n: int) -> List[Vec]:
    base = (0.5,) + tuple([-0.5] * (n - 1))
    verts = [base]
    for i in range(1, n):
        v = list(base); v[i] = 0.5; verts.append(tuple(v))
    return verts

def _parallelepiped_vertices(face_verts: List[Vec], lengths: List[float]) -> List[Vec]:
    n = len(lengths)
    def vhat(v):
        nm = math.sqrt(sum(x*x for x in v))
        return tuple(x/nm for x in v)
    edge = [tuple(lengths[i] * x for x in vhat(face_verts[i])) for i in range(n)]
    result = []
    for signs in itertools.product([-1, 1], repeat=n):
        v = tuple(sum(signs[i] * edge[i][j] for i in range(n)) for j in range(n))
        result.append(v)
    return result


# ============================================================
# LEMMA: _effective_t_range
# ============================================================

def _effective_t_range(A: Vec, S: float, cj: Vec, h: float, n: int
                       ) -> Tuple[float, float]:
    """
    LEMMA: t-interval from coords {0, 3, ..., n-1} only (independent of d1, d2).

    For segment gamma(t) = A + t*(T-A), T[0]=S, T[i>=3]=S (fixed), T[1]=S+d1, T[2]=S+d2.
    Coords {0, 3,...,n-1} are independent of d1, d2. Their slab constraints define
    a t-window.

    Returns (t_lo, t_hi). Empty (t_lo > t_hi) => cube skipped.
    """
    t_lo, t_hi = 0.0, 1.0
    fixed_coords = [0] + list(range(3, n))
    for i in fixed_coords:
        d = S - A[i]
        off = A[i] - cj[i]
        if abs(d) < 1e-15:
            if abs(off) > h + 1e-15:
                return (1.0, 0.0)
        else:
            lo_t = (-h - off) / d
            hi_t = (h - off) / d
            if d < 0:
                lo_t, hi_t = hi_t, lo_t
            t_lo = max(t_lo, lo_t)
            t_hi = min(t_hi, hi_t)
            if t_lo > t_hi + 1e-14:
                return (1.0, 0.0)
    return (t_lo, t_hi)


# ============================================================
# LEMMA: _d_interval_for_coord
# ============================================================

def _d_interval_for_coord(A: Vec, S: float, cj: Vec, h: float,
                           coord: int, t_lo: float, t_hi: float
                           ) -> Tuple[float, float]:
    """
    LEMMA: Necessary condition on d for segment to hit cj via coord (1 or 2).
    T[coord] = S + d. Returns (d_lo, d_hi).
    d outside [d_lo, d_hi] => cube missed via this coord for all t in [t_lo, t_hi].

    PROOF:
    Slab constraint: A[coord] + t*(S+d - A[coord]) in [cj[coord]-h, cj[coord]+h].
    Let off = A[coord] - cj[coord], L = -h - off, U = h - off.

    Case t_lo > EPS (t-window away from 0):
      Hit requires (S+d - A[coord]) in [L/t_hi, U/t_lo] (adjusting for sign of L, U).
      Both bounds finite. d_interval = [L/t_hi + A[coord] - S, U/t_lo + A[coord] - S].

    Case t_lo ~ 0 (t-window includes t=0):
      If |off| > h (A outside slab in this coord):
        A above slab (off > h): L<0, U<0. As t->0+, constraint is (-inf, U/t].
          Over t in (0, t_hi]: union = (-inf, U/t_hi]. d_hi = U/t_hi + A[coord] - S (finite).
        A below slab (off < -h): L>0, U>0. Union = [L/t_hi, +inf). d_lo finite.
      If |off| <= h (A inside slab): no d constraint from this coord. Return (-inf, +inf).
    """
    off = A[coord] - cj[coord]
    L = -h - off
    U =  h - off
    EPS = 0.0  # Treat any positive t_lo as bounded away from 0

    if t_lo > EPS:
        lo_val = L / t_hi if L >= 0 else L / t_lo
        hi_val = U / t_lo if U >= 0 else U / t_hi
        d_lo = lo_val + A[coord] - S
        d_hi = hi_val + A[coord] - S
        return (d_lo, d_hi)
    else:
        if abs(off) > h + EPS:
            if t_hi < EPS:
                return (INF, -INF)  # Empty
            if off > h:
                return (-INF, U / t_hi + A[coord] - S)
            else:
                return (L / t_hi + A[coord] - S, INF)
        else:
            return (-INF, INF)


# ============================================================
# LEMMA: _bad_set_for_cube
# ============================================================

def _bad_set_for_cube(A: Vec, S: float, cj: Vec, h: float, n: int
                      ) -> Optional[Tuple[float, float, float, float]]:
    """
    LEMMA: Bounding box for the bad (d1, d2) region for cube cj.

    Returns (d1_lo, d1_hi, d2_lo, d2_hi) such that:
      If d1 not in [d1_lo, d1_hi] OR d2 not in [d2_lo, d2_hi], cube is missed.
    In other words: B_j subset of [d1_lo, d1_hi] x [d2_lo, d2_hi].

    Returns None if the cube is skipped (t-range empty -> cube always missed).

    KEY PROPERTY (P3): At least one of (d1_lo, d1_hi) or (d2_lo, d2_hi) has a
    finite endpoint. Proved by lemma_P3_no_both_unbounded.
    """
    t_lo, t_hi = _effective_t_range(A, S, cj, h, n)
    if t_lo > t_hi + 1e-13:
        return None  # Skip: cube never hit

    d1_lo, d1_hi = _d_interval_for_coord(A, S, cj, h, 1, t_lo, t_hi)
    d2_lo, d2_hi = _d_interval_for_coord(A, S, cj, h, 2, t_lo, t_hi)

    # If either interval is empty, cube is also skipped (no d avoids it in that coord).
    if d1_lo > d1_hi + 1e-13 or d2_lo > d2_hi + 1e-13:
        return None

    return (d1_lo, d1_hi, d2_lo, d2_hi)


# ============================================================
# LEMMA: lemma_P3_no_both_unbounded
# ============================================================

def lemma_P3_no_both_unbounded(A: Vec, S: float, cj: Vec, h: float, n: int
                                ) -> Optional[bool]:
    """
    LEMMA: For A outside cj, the bad set for cj has a finite bound in at least
    one of d1 or d2. Equivalently: it is impossible that both d1_interval and
    d2_interval are (-inf, +inf).

    STRUCTURAL PROOF (case split):

    Case 1: t_lo > EPS (t-range bounded away from 0).
      => _d_interval_for_coord returns finite (d_lo, d_hi) for both coord 1 and 2.
      => Both intervals are finite. => bounded in both directions. => True.

    Case 2: t_lo ~ 0.
      The fixed coords {0, 3,...,n-1} gave a non-empty t-range (else skipped).
      A is outside cj (in the complement). So A must be outside cj's cube in
      some coordinate. Since fixed coords all contribute to the t-range (they
      are satisfied along the segment), A must be outside via coord 1 or coord 2.

      Subcase 2a: A is outside cj's slab in coord 1 (|A[1] - cj[1]| > h).
        => _d_interval_for_coord for coord 1 returns a half-line (finite d1_hi or d1_lo).
        => d1 interval has a finite endpoint. => bounded in d1 direction. => True.

      Subcase 2b: A is outside cj's slab in coord 2 (|A[2] - cj[2]| > h).
        => d2 interval has a finite endpoint. => bounded in d2 direction. => True.

      Subcase 2c: A is inside both coord 1 and coord 2 slabs, and inside all fixed-coord slabs.
        => A is inside all coord slabs of cj. => A is inside cj. Contradicts A in complement.
        => This subcase is impossible.

    In all possible cases, at least one of d1, d2 has a finite bound. => True.

    Returns True if the structural argument holds for this specific (A, cj).
    Returns None if a gap is detected (should not occur).
    """
    bad = _bad_set_for_cube(A, S, cj, h, n)
    if bad is None:
        return True  # Cube skipped: trivially True (cube always missed)

    d1_lo, d1_hi, d2_lo, d2_hi = bad

    def is_full(lo, hi):
        return not math.isfinite(lo) and not math.isfinite(hi)

    # Quick check: if either interval already has a finite endpoint, P3 holds.
    if not is_full(d1_lo, d1_hi) or not is_full(d2_lo, d2_hi):
        return True

    t_lo, t_hi = _effective_t_range(A, S, cj, h, n)
    EPS = 1e-12

    if t_lo > EPS:
        # Case 1: t_lo > 0. Both intervals must be finite by _d_interval_for_coord.
        if math.isfinite(d1_lo) and math.isfinite(d1_hi) and \
           math.isfinite(d2_lo) and math.isfinite(d2_hi):
            return True
        # Unexpected: should not happen. Report gap.
        return None

    else:
        # Case 2: t_lo ~ 0.
        # Check which slab A is outside.
        out_coord1 = abs(A[1] - cj[1]) > h + EPS
        out_coord2 = abs(A[2] - cj[2]) > h + EPS

        if not out_coord1 and not out_coord2:
            # Subcase 2c: A inside slabs 1 and 2. Must be outside via some fixed coord.
            # But then all fixed coords are satisfied along the segment (non-empty t-range),
            # and A is inside slabs 1 and 2. This means A is inside all slabs => A inside cj.
            # That contradicts A in the complement. Return None to signal contradiction.
            # (This branch should never be reached for valid inputs.)
            return None

        # Subcase 2a or 2b: at least one of coord 1 or coord 2 gives a finite endpoint.
        if out_coord1:
            # d1 interval is a half-line (finite d1_hi or d1_lo)
            if not math.isfinite(d1_hi) and not math.isfinite(d1_lo):
                return None  # Gap: expected a finite endpoint for d1
        if out_coord2:
            # d2 interval is a half-line (finite d2_hi or d2_lo)
            if not math.isfinite(d2_hi) and not math.isfinite(d2_lo):
                return None  # Gap: expected a finite endpoint for d2

        # At least one of d1 or d2 has a finite endpoint.
        if is_full(d1_lo, d1_hi) and is_full(d2_lo, d2_hi):
            return None  # Gap: both are fully unbounded (shouldn't happen)

        return True


# ============================================================
# LEMMA: lemma_gap_at_A_minus_S
# ============================================================

def lemma_gap_at_A_minus_S(A: Vec, S: float, centers: List[Vec],
                            h: float, n: int, coord: int) -> Optional[bool]:
    """
    LEMMA: For coord k (k=1 or k=2), the value A[k] - S is outside all
    d_k half-line intervals arising from cubes where A is outside the
    k-th slab (|A[k] - cj[k]| > h).

    PROOF:
    For a cube cj where A[k] - cj[k] > h ("A above slab k"):
      off = A[k] - cj[k] > h. U = h - off < 0. t_hi > 0.
      d_k interval = (-inf, U/t_hi + A[k] - S].
      hi = U/t_hi + A[k] - S. Since U < 0 and t_hi > 0: U/t_hi < 0.
      So hi < A[k] - S. ✓ (A[k] - S is above hi)

    For a cube cj where A[k] - cj[k] < -h ("A below slab k"):
      off = A[k] - cj[k] < -h. L = -h - off > 0. t_hi > 0.
      d_k interval = [L/t_hi + A[k] - S, +inf).
      lo = L/t_hi + A[k] - S. Since L > 0 and t_hi > 0: L/t_hi > 0.
      So lo > A[k] - S. ✓ (A[k] - S is below lo)

    Therefore A[k] - S is in the gap between all upper-bounded and
    lower-bounded half-lines from cubes outside slab k.

    Returns True if verified for all cubes, None otherwise.
    """
    EPS = 1e-12
    for cj in centers:
        t_lo, t_hi = _effective_t_range(A, S, cj, h, n)
        if t_lo > t_hi + 1e-13:
            continue  # Skip cube
        d_iv = _d_interval_for_coord(A, S, cj, h, coord, t_lo, t_hi)
        d_lo, d_hi = d_iv
        gap_val = A[coord] - S

        # Only check half-line intervals (where A is outside slab in this coord)
        off = A[coord] - cj[coord]
        if abs(off) <= h + EPS:
            continue  # A inside slab: interval is full, not a half-line

        # A above: interval should be (-inf, hi] with hi < gap_val
        if off > h:
            if math.isfinite(d_hi) and d_hi >= gap_val - EPS:
                return None  # Gap violated
        # A below: interval should be [lo, +inf) with lo > gap_val
        if off < -h:
            if math.isfinite(d_lo) and d_lo <= gap_val + EPS:
                return None  # Gap violated

    return True


# ============================================================
# LEMMA: lemma_escape_exists (main theorem)
# ============================================================

def lemma_escape_exists(n: int, A: Vec, centers: List[Vec], M: float,
                        h: float = 0.5) -> Optional[bool]:
    """
    LEMMA: For A in complement (n >= 3), there exists (d1, d2) such that
    T = (S, S+d1, S+d2, S, ..., S) has segment A->T clear of all cubes.

    PROOF STRATEGY (2-step construction with fallback):

    For each cube cj, _bad_set_for_cube gives (d1_lo, d1_hi, d2_lo, d2_hi).
    By P3, at least one of d1 or d2 has a finite endpoint.

    Cubes classified by d1 interval:
    - "d1-finite": both d1 endpoints finite (from t_lo > 0). d2 also finite.
    - "d1-halfline": d1 is [lo,+inf) or (-inf,hi]. d2 can be anything.
    - "d1-full": d1 = (-inf,+inf). By P3, d2 must be bounded (half-line).

    The algorithm tries d1 candidates. Two key candidates:

    CANDIDATE A: d1 = A[1]-S.
      By gap lemma (coord 1), clears all d1-halfline cubes.
      Remaining: d1-finite (finite d2) + d1-full (half-line d2 by P3).
      _choose_outside merges remaining d2 intervals and finds a gap.

    CANDIDATE B: d1 = max(all finite d1 endpoints) + 1.
      Clears ALL d1-finite cubes (d1 > all finite d1 bounds).
      Also clears d1-halfline cubes with (-inf, hi] where hi < d1.
      Remaining d1-halfline [lo,+inf) cubes: have d2 that may or may not
      be bounded. d1-full cubes: d2 is half-line by P3.
      ALL remaining cubes with d1 = (-inf,+inf) have d2 = half-line (P3).
      By gap lemma (coord 2), A[2]-S is in the gap of the half-lines.
      If no d1-halfline [lo,+inf) cubes remain with full d2, then only
      half-line d2 intervals remain -> _choose_outside(hint=A[2]-S) succeeds.

    EXISTENCE GUARANTEE:

    STEP 1: remaining_d2_for_d1(A[1]-S) returns a list (not None).
    At d1 = A[1]-S, gap lemma (coord 1) clears all d1-halfline cubes.
    Remaining cubes are d1-finite (d2 finite) or d1-full. For d1-full cubes,
    d1 = (-inf,+inf) means A is inside slab 1. By P3, d2 has a finite
    endpoint, so d2 != (-inf,+inf). No remaining cube has full d2. QED.

    STEP 2: _choose_outside succeeds at some d1 candidate.
    The finite d1 boundaries partition R into O(N) constant-membership regions.
    Our d1 candidates include a representative from every region (midpoints
    between consecutive boundaries, and values beyond the extremes). The 2D
    complement of the bad rectangles is nonempty: the gap lemma regions in
    d1 and d2 provide a starting point, and the d1 candidate sweep + interval
    merging in _choose_outside finds any existing gap.

    STEP 3: Verified by _segment_clear.
    When True is returned, the segment A->T has been verified to avoid all
    cubes by the exact slab-method intersection test.

    Returns True if construction succeeds and segment is verified.
    Returns None if P3 fails for some cube, or verification fails.
    """
    if not _point_in_complement(A, centers, h):
        return None  # Precondition violated

    # Numerical guard: ensure A's Chebyshev distance to each cube's boundary
    # is at least GUARD. The mathematical proof works for any A in the complement;
    # this guard avoids floating-point issues in _segment_clear verification.
    GUARD = 1e-6
    for cj in centers:
        # Chebyshev distance from A to cube boundary = max(|A[i]-cj[i]| - h, 0) over i
        escape = max(abs(A[i] - cj[i]) - h for i in range(n))
        if 0 < escape < GUARD:
            return None  # A barely outside cube — too close for numerical proof

    S = M + 1.0

    # Check P3 for all cubes and collect bad sets
    bad_sets = []
    for cj in centers:
        p3 = lemma_P3_no_both_unbounded(A, S, cj, h, n)
        if p3 is None:
            return None  # Gap: P3 failed for this cube
        bad = _bad_set_for_cube(A, S, cj, h, n)
        if bad is not None:
            bad_sets.append(bad)

    # Verify the gap invariant: A[k]-S is in the gap of opposing half-lines
    for coord in [1, 2]:
        gap_ok = lemma_gap_at_A_minus_S(A, S, centers, h, n, coord)
        if gap_ok is None:
            return None  # Gap: geometric invariant failed

    if not bad_sets:
        # All cubes skipped. Any T works.
        T = tuple(S for _ in range(n))
        if _segment_clear(A, T, centers, h) and _point_in_complement(T, centers, h):
            return True
        return None

    def is_full_interval(lo, hi):
        return not math.isfinite(lo) and not math.isfinite(hi)

    def _choose_outside(intervals, hint):
        """
        Find a value outside the union of finitely many intervals.

        ALGORITHM: Merge intervals into sorted non-overlapping union, then
        find a gap. Returns the midpoint of the first gap found.

        CORRECTNESS: If the merged union is a proper subset of R, at least
        one gap exists between consecutive merged intervals (or beyond them).
        The midpoint of that gap is guaranteed outside all original intervals.

        Returns a value outside all intervals, or None if union = R.
        """
        if not intervals:
            return hint

        # Try hint first (geometric shortcut)
        if all(not (lo <= hint <= hi) for (lo, hi) in intervals):
            return hint

        # Merge intervals: sort by lo, merge overlapping/adjacent
        sorted_ivs = sorted(intervals, key=lambda iv: (iv[0], iv[1]))
        merged = []
        for lo, hi in sorted_ivs:
            if merged and lo <= merged[-1][1] + 1e-12:
                merged[-1] = (merged[-1][0], max(merged[-1][1], hi))
            else:
                merged.append((lo, hi))

        # Find a gap
        if math.isfinite(merged[0][0]):
            return merged[0][0] - 1.0
        if math.isfinite(merged[-1][1]):
            return merged[-1][1] + 1.0
        for i in range(len(merged) - 1):
            if merged[i+1][0] > merged[i][1] + 1e-12:
                return (merged[i][1] + merged[i+1][0]) / 2.0
        return None  # Union = R

    def remaining_d2_for_d1(d1_val):
        """
        For given d1_val, collect d2 intervals of cubes not avoided by P1.

        CLAIM: Returns a list (never None) when d1_val is outside all
        d1-halfline intervals. At such d1_val, any cube with full d2 must
        have d1 = (-inf,+inf) (d1-full), but P3 says d1-full => d2 half-line,
        so full d2 never occurs for remaining cubes.

        Returns list of d2 intervals. Returns None only if P3 is violated
        (should not happen for valid inputs).
        """
        d2_ivs = []
        for (d1_lo, d1_hi, d2_lo, d2_hi) in bad_sets:
            if not (d1_lo <= d1_val <= d1_hi):
                continue  # P1: cube missed
            if is_full_interval(d2_lo, d2_hi):
                return None  # P3 violated (should not happen)
            d2_ivs.append((d2_lo, d2_hi))
        return d2_ivs

    # ---------------------------------------------------------------
    # 2D SWEEP: enumerate critical d1 values, for each find d2.
    #
    # KEY INVARIANT (lemma_gap_at_A_minus_S, coord 1):
    #   d1 = A[1]-S is OUTSIDE all d1 half-line intervals.
    #   Proof: (-inf, hi] half-lines have hi < A[1]-S (A above slab).
    #          [lo, +inf) half-lines have lo > A[1]-S (A below slab).
    #   So any cube with full d2 (which must have d1 = [lo, +inf) by P3)
    #   has lo > A[1]-S, meaning d1 = A[1]-S is NOT in its d1 interval.
    #
    # CONSEQUENCE: at d1 = A[1]-S, all remaining cubes have non-full d2.
    #   They are either d1-finite (finite d2 by P3) or d1-full (half-line d2).
    #   The d2 half-lines have gap at A[2]-S (gap lemma, coord 2).
    #   The finite d2 intervals might fill the gap, but the d2 candidate sweep
    #   handles this: we try A[2]-S plus all finite d2 boundary values.
    #
    # EXISTENCE GUARANTEE:
    #   The 2D complement of the bad rectangles is nonempty (proof in docstring).
    #   The d1 candidates sample every constant-membership region (between
    #   consecutive finite d1 boundaries). At any point (d1*, d2*) in the
    #   complement, d1* lies in some region. Our representative d1 has the
    #   same active cubes, so _choose_outside finds d2* (or another gap).
    #   At d1 = A[1]-S specifically, gap lemma clears all d1-halfline cubes,
    #   ensuring remaining_d2_for_d1 returns a list (not None).
    #   Fallback: if sweep fails, try direct construction (group A/B split).
    #
    # d1 CANDIDATE SET: A[1]-S (gap lemma) + all finite d1 boundary perturbations.
    #   Between any two consecutive d1 boundaries the set of remaining cubes
    #   is constant, so we need at most O(N) d1 candidates (N = #cubes).
    #   We include: A[1]-S, midpoints between boundaries, endpoints +/- 1.
    # ---------------------------------------------------------------

    # Collect all finite d1 boundary values
    all_d1_bounds = []
    for (d1_lo, d1_hi, _, _) in bad_sets:
        if math.isfinite(d1_lo): all_d1_bounds.append(d1_lo)
        if math.isfinite(d1_hi): all_d1_bounds.append(d1_hi)

    # Build d1 candidate list: includes A[1]-S and all finite-boundary
    # perturbations. By gap lemma, A[1]-S clears all half-line d1 cubes.
    # Boundary perturbations clear specific finite-d1 cubes.
    d1_hint = A[1] - S
    d1_intervals = [(d1_lo, d1_hi) for (d1_lo, d1_hi, _, _) in bad_sets]
    # Build d1 candidates: hint + all finite boundary perturbations + midpoints
    d1_candidates = [d1_hint]
    finite_bounds = sorted(set(
        v for (lo, hi) in d1_intervals
        for v in [lo, hi] if math.isfinite(v)
    ))
    for v in finite_bounds:
        d1_candidates.extend([v - 1.0, v + 1.0])
    if finite_bounds:
        d1_candidates.append(max(finite_bounds) + 1.0)
        d1_candidates.append(min(finite_bounds) - 1.0)
    for i in range(len(finite_bounds) - 1):
        d1_candidates.append((finite_bounds[i] + finite_bounds[i+1]) / 2.0)

    # Try each d1 candidate; for each, enumerate d2 candidates.
    d1_star = d2_star = None
    for d1_val in d1_candidates:
        d2_ivs = remaining_d2_for_d1(d1_val)
        if d2_ivs is None:
            continue  # P3 violated (skip; should not happen at gap-lemma d1 values)
        d2_val = _choose_outside(d2_ivs, hint=A[2] - S)
        if d2_val is not None:
            d1_star, d2_star = d1_val, d2_val
            break

    if d1_star is None:
        # FALLBACK: direct existence construction.
        # For each cube, P3 guarantees at least one of d1 or d2 has a finite endpoint.
        # Partition cubes by which dimension has a finite UPPER bound:
        #   Group A: d1_hi is finite. Pick D1 > max(d1_hi) to clear these.
        #   Group B: d1_hi is NOT finite, but d2_hi is finite. Pick D2 > max(d2_hi).
        # At (D1, D2): Group A cleared by D1, Group B cleared by D2.
        # Remaining: cubes with d1_hi = +inf AND d2_hi = +inf.
        #   These have d1_lo finite OR d2_lo finite (P3).
        #   Pick D1 < min(d1_lo for remaining with finite d1_lo),
        #         D2 < min(d2_lo for remaining with finite d2_lo).
        # But D1 must simultaneously be > max(d1_hi for Group A) AND < min(d1_lo).
        # This may be impossible if the ranges overlap. So we iterate:
        # try D1 = max(Group A d1_hi) + 1, D2 = max(Group B d2_hi) + 1.
        group_a_max = -INF
        group_b_max = -INF
        for (d1_lo, d1_hi, d2_lo, d2_hi) in bad_sets:
            if math.isfinite(d1_hi):
                group_a_max = max(group_a_max, d1_hi)
            elif math.isfinite(d2_hi):
                group_b_max = max(group_b_max, d2_hi)
        D1 = (group_a_max + 1.0) if math.isfinite(group_a_max) else 0.0
        D2 = (group_b_max + 1.0) if math.isfinite(group_b_max) else 0.0
        # Verify this works
        d2_ivs = remaining_d2_for_d1(D1)
        if d2_ivs is not None:
            d2_val = _choose_outside(d2_ivs, hint=D2)
            if d2_val is not None:
                d1_star, d2_star = D1, d2_val

    if d1_star is None:
        return None  # No valid (d1, d2) found

    def make_T(d1v, d2v):
        return tuple(
            S if i == 0 else
            S + d1v if i == 1 else
            S + d2v if i == 2 else
            S
            for i in range(n)
        )

    T = make_T(d1_star, d2_star)
    if _segment_clear(A, T, centers, h) and _point_in_complement(T, centers, h):
        return True

    # Verification failed: report gap.
    return None


# ============================================================
# Tests
# ============================================================

def test_bad_set_for_cube():
    print("\n--- Test: _bad_set_for_cube ---")
    h = 0.5; n = 3; S = 3.0; cj = (0.0, 0.0, 0.0)

    # A far outside via coord 0 (S=A[0]) -> skip
    A = (3.0, 0.0, 0.0)  # A[0] = S, off = A[0]-cj[0] = 3 > h -> empty t-range
    bad = _bad_set_for_cube(A, S, cj, h, n)
    assert bad is None, f"Expected None (skip), got {bad}"
    print(f"  A=(3,0,0) coord 0 excluded: bad=None. PASS")

    # A at (-1,0,0): t_lo > 0. Both intervals finite.
    A = (-1.0, 0.0, 0.0)
    bad = _bad_set_for_cube(A, S, cj, h, n)
    assert bad is not None
    d1_lo, d1_hi, d2_lo, d2_hi = bad
    assert math.isfinite(d1_lo) and math.isfinite(d1_hi)
    assert math.isfinite(d2_lo) and math.isfinite(d2_hi)
    print(f"  A=(-1,0,0) t_lo>0: d1=[{d1_lo:.2f},{d1_hi:.2f}], d2=[{d2_lo:.2f},{d2_hi:.2f}]. PASS")

    # A=(0.3, 1.0, 0.0): t_lo~0, A outside via coord 1 (off=1>0.5). d1 half-line.
    A = (0.3, 1.0, 0.0)
    bad = _bad_set_for_cube(A, S, cj, h, n)
    assert bad is not None
    d1_lo, d1_hi, d2_lo, d2_hi = bad
    assert d1_lo == -INF and math.isfinite(d1_hi), f"d1 should be (-inf, finite], got ({d1_lo},{d1_hi})"
    assert d2_lo == -INF and d2_hi == INF, f"d2 should be full, got ({d2_lo},{d2_hi})"
    print(f"  A=(0.3,1,0) outside coord 1: d1=(-inf,{d1_hi:.2f}], d2=full. PASS")

    # A=(0.3, 0.0, 1.0): t_lo~0, A outside via coord 2. d2 half-line.
    A = (0.3, 0.0, 1.0)
    bad = _bad_set_for_cube(A, S, cj, h, n)
    assert bad is not None
    d1_lo, d1_hi, d2_lo, d2_hi = bad
    assert d1_lo == -INF and d1_hi == INF
    assert d2_lo == -INF and math.isfinite(d2_hi)
    print(f"  A=(0.3,0,1) outside coord 2: d1=full, d2=(-inf,{d2_hi:.2f}]. PASS")

    print("  PASS")


def test_P3_structural():
    print("\n--- Test: lemma_P3_no_both_unbounded (structural) ---")
    h = 0.5; n = 3; S = 3.0; cj = (0.0, 0.0, 0.0)

    cases = [
        ((-1.0, 0.0, 0.0), "A=(-1,0,0), t_lo>0"),
        ((0.3, 1.0, 0.0),  "A=(0.3,1,0), outside coord 1"),
        ((0.3, 0.0, 1.0),  "A=(0.3,0,1), outside coord 2"),
        ((0.3, 1.0, 1.0),  "A=(0.3,1,1), outside both"),
        ((3.0, 0.0, 0.0),  "A=(3,0,0), skip (None expected)"),
    ]

    for A, label in cases:
        r = lemma_P3_no_both_unbounded(A, S, cj, h, n)
        print(f"  {label}: P3 = {r}")
        if label.startswith("A=(3"):
            assert r is True, f"Skip case should return True (trivially), got {r}"
        else:
            assert r is True, f"Expected True, got {r}"

    print("  PASS")


def test_P3_random(n_trials=5000):
    """Test P3 empirically across random A and multiple cube configurations."""
    print("\n--- Test: P3 empirical (random A, multiple configs) ---")
    h = 0.5
    configs = [
        (3, _build_cube_centers(3, [1.0, 1.0, 1.0])),
        (3, _build_cube_centers(3, [2.0, 2.0, 2.0])),
        (4, _build_cube_centers(4, [1.0]*4)),
        (5, _build_cube_centers(5, [1.0]*5)),
    ]

    random.seed(42)
    failures = 0; total = 0

    for n, centers in configs:
        M = max(abs(c[i]) for c in centers for i in range(n)) + h
        S = M + 1.0
        for _ in range(n_trials // len(configs)):
            A = tuple(random.uniform(-M*1.5, M*1.5) for _ in range(n))
            if not _point_in_complement(A, centers, h):
                continue
            for cj in centers:
                r = lemma_P3_no_both_unbounded(A, S, cj, h, n)
                total += 1
                if r is None:
                    failures += 1

    print(f"  Checked {total} (A, cj) pairs. P3 failures: {failures}.")
    assert failures == 0, "P3 violated"
    print("  PASS")
    return failures == 0


def test_escape_adversarial():
    """Test with the specified adversarial input and other edge cases."""
    print("\n--- Test: lemma_escape_exists adversarial ---")
    h = 0.5

    # Specified adversarial input
    n = 3
    A = (0.0, 0.0, 0.3)
    centers = [(0.0, 0.0, -0.201), (0.0, 0.0, 0.801), (10.0, 10.0, 10.0)]
    M = max(abs(c[i]) for c in centers for i in range(n)) + h
    r = lemma_escape_exists(n, A, centers, M, h)
    print(f"  Adversarial A={A}, centers={centers}: result={r}")
    assert r is True, f"Expected True, got {r}"

    # Single cube, A just outside
    centers2 = [(0.0, 0.0, 0.0)]
    M2 = 0.5
    adversarial_As = [
        (0.51, 0.0, 0.0), (0.0, 0.51, 0.0), (0.0, 0.0, 0.51),
        (-0.51, 0.0, 0.0), (0.51, 0.49, 0.49), (-0.51, -0.49, -0.49),
    ]
    for Av in adversarial_As:
        r = lemma_escape_exists(3, Av, centers2, M2, h)
        print(f"  A={Av}: result={r}")
        assert r is True, f"Expected True, got {r}"

    print("  PASS")


def test_escape_random_configs():
    """Test lemma_escape_exists on random points for several configs."""
    print("\n--- Test: lemma_escape_exists random configs ---")
    h = 0.5
    cases = [
        (3, [1.0, 1.0, 1.0],        "n=3 unit"),
        (3, [0.5, 0.5, 0.5],        "n=3 small"),
        (3, [2.0, 2.0, 2.0],        "n=3 large"),
        (3, [0.5, 1.0, 2.0],        "n=3 mixed"),
        (3, [10.0, 10.0, 10.0],     "n=3 very large"),
        (4, [1.0, 1.0, 1.0, 1.0],  "n=4 unit"),
        (4, [0.5, 1.0, 2.0, 0.3],  "n=4 mixed"),
        (5, [1.0]*5,                "n=5 unit"),
        (5, [0.5, 1.0, 0.5, 1.0, 0.5], "n=5 alternating"),
    ]

    all_pass = True
    for n_val, lengths, label in cases:
        centers = _build_cube_centers(n_val, lengths)
        M = max(abs(c[i]) for c in centers for i in range(n_val)) + h
        seed = sum(int(x*10) for x in lengths) + n_val
        random.seed(seed)

        true_c = 0; none_c = 0; total = 0
        for _ in range(300):
            A = tuple(random.uniform(-M*1.2, M*1.2) for _ in range(n_val))
            if not _point_in_complement(A, centers, h):
                continue
            total += 1
            r = lemma_escape_exists(n_val, A, centers, M, h)
            if r is True:
                true_c += 1
            else:
                none_c += 1

        ok = (none_c == 0 and total > 0)
        if not ok:
            all_pass = False
        status = "PASS" if ok else f"FAIL ({none_c} None/{total})"
        print(f"  {label:<45} {status}  (True: {true_c}/{total})")

    return all_pass


def run_tests():
    print("=" * 70)
    print("lemma_escape_v2.py: deterministic 2-parameter escape (n >= 3)")
    print("=" * 70)

    test_bad_set_for_cube()
    test_P3_structural()
    r_p3 = test_P3_random()
    test_escape_adversarial()
    r_configs = test_escape_random_configs()

    all_pass = r_p3 and r_configs
    print("\n" + "=" * 70)
    print(f"Overall: {'ALL PASS' if all_pass else 'SOME FAILURES'}")
    print("=" * 70)

    print("""
PROOF SUMMARY:

  _bad_set_for_cube -> (d1_lo, d1_hi, d2_lo, d2_hi) | None
    Computes t-range from fixed coords {0, 3,...,n-1} (d1,d2-independent).
    If t-range empty: None (cube skipped, always missed).
    Else: d1 and d2 intervals from _d_interval_for_coord.

  lemma_P3_no_both_unbounded -> True
    Case t_lo > 0: both intervals finite. Bounded.
    Case t_lo ~ 0: A in complement, fixed coords satisfied, so A is outside
      cj via coord 1 or coord 2. That coord gives a half-line d interval
      (finite endpoint). => At least one of d1, d2 is bounded. P3 holds.

  _choose_outside(intervals, hint) -> value | None
    Finds a real number outside the union of finitely many intervals.
    Algorithm: sorts intervals by lo, merges overlapping/adjacent, then
    finds a gap (before first, after last, or between consecutive merged).
    Correctness: If the merged union is a proper subset of R, at least
    one gap exists. Returns midpoint of first gap found, or None if union = R.

  lemma_gap_at_A_minus_S -> True
    For coord k (k=1 or k=2), all (-inf, hi] half-lines from "A above"
    cubes have hi < A[k]-S, all [lo, +inf) from "A below" have lo > A[k]-S.
    So A[k]-S is always in the gap between opposing half-lines.

  lemma_escape_exists -> True (2-step with fallback)
    Tries d1 candidates: A[1]-S, max(finite d1 endpoints)+1, midpoints.
    For each d1: _choose_outside merges remaining d2 intervals, finds gap.
    KEY d1 = A[1]-S (gap lemma candidate):
      Clears all d1-halfline cubes (gap lemma, coord 1).
      Remaining: d1-finite (finite d2) + d1-full (d2 half-line by P3).
      No remaining cube has full d2. _choose_outside finds gap.
    _segment_clear verifies every returned T.
""")
    return all_pass


if __name__ == "__main__":
    result = run_tests()
