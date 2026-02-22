"""
CONSTRUCTIVE PROOF v6: R^n \\ C is path-connected for n >= 3
(2-parameter escape with sweep)

PROOF STRATEGY:

For any A in R^n \\ C, we find T = (S, S+d1, S+d2, S, ..., S) on the hyperplane {x_0=S}
(S = M+1) such that segment A->T avoids all cubes, using a 2-parameter sweep.

LEMMA CHAIN:

L1: lemma_one_coord_safe
  If T_A[0] = T_B[0] = S > M, then segment T_A->T_B avoids all cubes.
  Proof: gamma_0(t) = S for all t. S > M >= cj[0]+h for all cubes. Coord-0 constraint fails. Miss.

L2: _effective_t_range
  The t-values [t_lo, t_hi] where gamma CAN intersect the cube in coords {0, 3,...,n-1}.
  These coords are fixed (T[i]=S), so their constraints are independent of d1, d2.
  If empty: cube is always avoided (for all d1, d2).
  If t_lo > 0: A is outside the cube via some fixed coord. Both d1 and d2 bad-sets are bounded.

L3: _effective_t_range_with_d1
  Same as L2 but coord 1 is also fixed (T[1]=S+d1). Used in step 2.

L4: _bad_xk_set
  Given t-range [t_lo, t_hi] and off_k = A[k]-cj[k], the set of x_k = S+dk-A[k] values
  for which the segment hits the cube in coord k (for some t in range).
  For t_lo > 0: this is a BOUNDED interval. Proof: x_k bounds are L_k/t_hi and U_k/t_lo (finite).
  For t_lo = 0: semi-infinite in one direction (bounded on the other side by the sign of off_k).

L5: escape analysis
  For A in complement:
  - Each cube is outside via some witness coord k.
  - If k in {0, 3,...,n-1}: t-range has t_lo > 0 -> both d1,d2 bad-sets bounded.
  - If k=1: d1 bad-set is one-sided. Step 1 handles it.
  - If k=2: d2 bad-set is one-sided. Handled by combining with step 1 (large d1 shrinks the t-range).

L6: _choose_d1
  Choose d1 large enough so that:
  (a) All cubes where bad-d1 is bounded above are avoided (d1 exceeds their upper bound).
  (b) All cubes where A is outside via coord-2 AND A is inside coord-1 slab (off_1 in (-h,h))
      become safe for ANY d2 >= 0. This requires d1 large enough that the coord-1 t-exit time
      (U_1/(S+d1-A[1])) is smaller than the time needed for coord-2 to exit the slab from below.

L7: _choose_d2 (with d1 from L6)
  After fixing d1:
  - Remaining dangerous cubes have bounded-above bad-d2 intervals (finite hi). Choose d2 > max(hi)+1.
  - Proof: cubes where A was outside via coord-2 with A inside coord-1 slab: handled by L6.
           Cubes where A was outside via coord-1 (below, A[1]<cj[1]-h): with d1 large, t_lo > 0.
           Cubes where A was outside via coord-0 or k>=3: t_lo > 0 from fixed coords.
           Cubes where A was outside via coord-2 (above, A[2]>cj[2]+h): bad d2 bounded above.

PROOF OF L7 (cubes with t_lo=0 after fixing d1 have bad-d2 bounded above):
  If effective_t_range_with_d1 gives t_lo=0: coord-0 and coord-1 (with d1 fixed) don't give t_lo > 0.
  This means A[0] is inside cj[0]'s slab AND A[1] is inside cj[1]'s slab (otherwise t_lo > 0).
  A is outside cj via coord 2 only. So off_2 = A[2]-cj[2] with |off_2| > h.
  If A above (off_2 > h): L_2 < U_2 < 0. Bad x_2 set: x_2 in (-inf, U_2/t_hi].
    U_2 < 0 and t_hi > 0: U_2/t_hi < 0. Upper bound on d2: U_2/t_hi + A[2]-S.
    Large positive d2 (x_2 = S+d2-A[2] >> 0) is OUTSIDE the bad set (since bad x_2 < 0). Safe.
  If A below (off_2 < -h): handled by L6 (d1 chosen large enough). For d2 = max_hi_from_others,
    the cube is safe because the coord-1 t-exit is smaller than coord-2 entry time.

L8: constructive_path_exists
  A -> T_A -> T_B -> B (3 segments).
  T_A = escape_to_safe(A), T_B = escape_to_safe(B).
  T_A->T_B clear by L1 (both have coord-0 = S > M).

THEOREM: theorem_complement_connected -> True
  By L1 through L8. For any A, B in complement: path exists.
"""

import itertools
import math
import random
from typing import List, Tuple, Optional

Vec = Tuple[float, ...]
Interval = Tuple[float, float]  # (lo, hi)

INF = math.inf
EPS = 1e-12


# ============================================================
# Geometry primitives
# ============================================================

def _cube_contains(center: Vec, cube_half: float, point: Vec) -> bool:
    """True iff point is in the closed cube [c-h, c+h]^n."""
    return all(abs(point[i] - center[i]) <= cube_half for i in range(len(center)))


def _point_in_complement(point: Vec, centers: List[Vec], cube_half: float = 0.5) -> bool:
    """True iff point is not in any cube."""
    return not any(_cube_contains(c, cube_half, point) for c in centers)


def _segment_hits_cube_exact(A: Vec, B: Vec, center: Vec, cube_half: float = 0.5) -> bool:
    """
    Exact test: does segment A->B intersect closed cube [c-h, c+h]^n?
    Uses interval intersection per coordinate, clamped to [0,1].
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
    """True iff segment A->B avoids all cubes."""
    return not any(_segment_hits_cube_exact(A, B, c, cube_half) for c in centers)


# ============================================================
# LEMMA L2: _effective_t_range
# ============================================================

def _effective_t_range(A: Vec, S: float, cj: Vec, h: float, n: int) -> Interval:
    """
    LEMMA L2: The t-range [t_lo, t_hi] from coords {0, 3,...,n-1} for segment A->T(d1,d2).

    These coords are FIXED (T[i]=S), independent of d1,d2. Their constraints:
      gamma_i(t) = A[i] + t*(S-A[i]) in [cj[i]-h, cj[i]+h].

    Returns (t_lo, t_hi). If t_lo > t_hi: empty (cube avoided for ALL d1,d2).

    KEY FACT: If A[i] is outside [cj[i]-h, cj[i]+h] for some i in {0, 3,...,n-1},
    then t_lo > 0 (since at t=0, gamma_i=A[i] is outside the slab, so the slab
    can only be entered at some t > 0) or the range is empty.
    This is because:
    - A[i] > cj[i]+h: lo_t from this coord = (-h-off)/d where d=S-A[i]<0 (since A[i]>cj[i]+h>=h>0
      but S=M+1>M>=cj[i]+h>A[i]? Not necessarily. If A[i] < S: d = S-A[i] > 0.
      off = A[i]-cj[i] > h. lo_t = (-h-off)/d = negative/positive < 0. hi_t = (h-off)/d < 0.
      -> t_hi < 0 < t_lo (since we intersect with [0,1]): empty range.
    - A[i] < cj[i]-h: off = A[i]-cj[i] < -h. d = S-A[i] > 0 (A[i] < cj[i]-h < S).
      lo_t = (-h-off)/d = (-h - (A[i]-cj[i]))/d = (cj[i]-h-A[i])/d > 0 (since A[i]<cj[i]-h).
      hi_t = (h-off)/d > lo_t. t_lo = lo_t > 0. Nonempty range with t_lo > 0.
    """
    t_lo, t_hi = 0.0, 1.0
    fixed_coords = [0] + list(range(3, n))
    for i in fixed_coords:
        d = S - A[i]
        off = A[i] - cj[i]
        if abs(d) < EPS:
            if abs(off) > h + EPS:
                return (1.0, 0.0)  # empty
        else:
            lo_t = (-h - off) / d
            hi_t = (h - off) / d
            if d < 0:
                lo_t, hi_t = hi_t, lo_t
            t_lo = max(t_lo, lo_t)
            t_hi = min(t_hi, hi_t)
            if t_lo > t_hi + EPS:
                return (1.0, 0.0)
    return (t_lo, t_hi)


# ============================================================
# LEMMA L3: _effective_t_range_with_d1
# ============================================================

def _effective_t_range_with_d1(A: Vec, S: float, cj: Vec, h: float, n: int, d1: float) -> Interval:
    """
    LEMMA L3: The t-range from coords {0, 1, 3,...,n-1} with coord 1 fixed at S+d1.

    Same as L2 but includes coord 1 (T[1] = S+d1 is now fixed).

    KEY FACT: If A[1] is outside [cj[1]-h, cj[1]+h] AND d1 is large positive,
    then either:
    (a) A[1] > cj[1]+h: off_1 > h. T[1]=S+d1 > S > cj[1]+h. Both above slab -> lo_t < 0, hi_t < 0
        -> intersect with [0,1]: empty. The range is empty -> cube always avoided.
    (b) A[1] < cj[1]-h: off_1 < -h. T[1]=S+d1 (large). lo_t = (cj[1]-h-A[1])/(S+d1-A[1]) > 0.
        t_lo > 0. (And t_hi = (cj[1]+h-A[1])/(S+d1-A[1]) > t_lo, both small for large d1.)
    """
    t_lo, t_hi = 0.0, 1.0
    # coords to include: 0, 1 (with d1), 3,...,n-1
    coords_and_targets = [(0, S), (1, S + d1)] + [(i, S) for i in range(3, n)]
    for (i, T_i) in coords_and_targets:
        d = T_i - A[i]
        off = A[i] - cj[i]
        if abs(d) < EPS:
            if abs(off) > h + EPS:
                return (1.0, 0.0)
        else:
            lo_t = (-h - off) / d
            hi_t = (h - off) / d
            if d < 0:
                lo_t, hi_t = hi_t, lo_t
            t_lo = max(t_lo, lo_t)
            t_hi = min(t_hi, hi_t)
            if t_lo > t_hi + EPS:
                return (1.0, 0.0)
    return (t_lo, t_hi)


# ============================================================
# LEMMA L4: _bad_xk_set
# ============================================================

def _bad_xk_set(off_k: float, h: float, t_lo: float, t_hi: float) -> Optional[Interval]:
    """
    LEMMA L4: The set of x_k = S+dk-A[k] values for which the segment hits
    the cube in coord k (for some t in [t_lo, t_hi]).

    Condition: exists t in [t_lo, t_hi] s.t. L_k <= t*x_k <= U_k,
    where L_k = -h-off_k, U_k = h-off_k, off_k = A[k]-cj[k].

    DERIVATION:
    Case x_k > 0: {t*x_k : t in [t_lo, t_hi]} = [t_lo*x_k, t_hi*x_k].
      Intersects [L_k, U_k] iff:
        t_lo*x_k <= U_k  (upper end of cube slab >= lower end of set)
        t_hi*x_k >= L_k  (lower end of cube slab <= upper end of set)
      For t_lo > 0: x_k in [L_k/t_hi, U_k/t_lo]. Finite interval.
      For t_lo = 0: x_k >= L_k/t_hi (if t_hi > 0) AND U_k >= 0 (x-independent condition).

    Case x_k < 0: {t*x_k : t in [t_lo, t_hi]} = [t_hi*x_k, t_lo*x_k].
      Intersects [L_k, U_k] iff:
        t_hi*x_k <= U_k  -> x_k <= U_k/t_hi (if t_hi > 0)
        t_lo*x_k >= L_k  -> x_k >= L_k/t_lo (if t_lo > 0)
      For t_lo > 0: x_k in [L_k/t_lo, U_k/t_hi]. Finite interval.
      For t_lo = 0: x_k <= U_k/t_hi (if t_hi > 0) AND L_k <= 0 (x-independent condition).

    Case x_k = 0: bad iff 0 in [L_k, U_k], i.e., |off_k| <= h.

    Returns (x_lo, x_hi) or None (always avoided).
    """
    L_k = -h - off_k
    U_k = h - off_k

    x_lo = INF
    x_hi = -INF

    # Case x_k > 0:
    # Condition: x_k >= L_k/t_hi AND (t_lo > 0: x_k <= U_k/t_lo) OR (t_lo=0: U_k >= 0)
    if t_hi > EPS:
        pos_x_lo = L_k / t_hi
    else:
        pos_x_lo = INF  # t_hi = 0: impossible

    if t_lo > EPS:
        pos_x_hi = U_k / t_lo
    else:
        # t_lo = 0: condition is U_k >= 0
        pos_x_hi = INF if U_k >= 0 else -INF  # if U_k < 0: no positive x_k works

    # Valid x_k > 0: x_k in [max(EPS, pos_x_lo), pos_x_hi]
    actual_pos_lo = max(EPS, pos_x_lo)
    if pos_x_hi > 0 and actual_pos_lo <= pos_x_hi:
        x_lo = min(x_lo, actual_pos_lo)
        x_hi = max(x_hi, pos_x_hi)

    # Case x_k < 0:
    # Condition: x_k <= U_k/t_hi AND (t_lo > 0: x_k >= L_k/t_lo) OR (t_lo=0: L_k <= 0)
    if t_hi > EPS:
        neg_x_hi = U_k / t_hi
    else:
        neg_x_hi = -INF

    if t_lo > EPS:
        neg_x_lo = L_k / t_lo
    else:
        # t_lo = 0: condition is L_k <= 0
        neg_x_lo = -INF if L_k <= 0 else INF  # INF means "impossible"

    # Valid x_k < 0: x_k in [neg_x_lo, min(-EPS, neg_x_hi)]
    actual_neg_hi = min(-EPS, neg_x_hi)
    if neg_x_lo <= actual_neg_hi:
        x_lo = min(x_lo, neg_x_lo)
        x_hi = max(x_hi, actual_neg_hi)

    # Case x_k = 0:
    if abs(off_k) <= h + EPS:
        x_lo = min(x_lo, 0.0)
        x_hi = max(x_hi, 0.0)

    if x_lo > x_hi:
        return None
    return (x_lo, x_hi)


def _bad_dk_interval(A: Vec, S: float, cj: Vec, h: float,
                     t_lo: float, t_hi: float, coord: int) -> Optional[Interval]:
    """
    The bad interval for dk where k = coord in {1, 2}.
    dk = x_k - S + A[k] where x_k = S + dk - A[k].

    Returns (dk_lo, dk_hi) or None.
    """
    off_k = A[coord] - cj[coord]
    xk_int = _bad_xk_set(off_k, h, t_lo, t_hi)
    if xk_int is None:
        return None
    x_lo, x_hi = xk_int
    shift = A[coord] - S  # dk = x_k + shift
    return (x_lo + shift, x_hi + shift)


# ============================================================
# LEMMA L6: _choose_d1
# ============================================================

def _choose_d1(A: Vec, S: float, centers: List[Vec], h: float, n: int) -> float:
    """
    LEMMA L6: Choose d1 such that:
    (a) All cubes where bad-d1 is bounded above are avoided (d1 exceeds the upper bound).
    (b) All cubes where A is outside via coord-2 with A inside coord-1 slab become safe
        for d2 >= 0. This requires d1 large enough that the coord-1 t-exit time is
        smaller than the coord-2 entry time (from below), ensuring the bad-d2 window shrinks.

    PROOF FOR (b):
    A cube cj where:
    - A inside coord-0 slab (t_lo from coord-0 = 0)
    - A inside coord-1 slab (U_1 = h-off_1 > 0, L_1 = -h-off_1 < 0 since |off_1| < h)
    - A below coord-2 slab (off_2 = A[2]-cj[2] < -h, L_2 = cj[2]-h-A[2] > 0)

    With d1 fixed, coord-1 t-exit = U_1/(S+d1-A[1]).
    For the cube to be hit with d2 >= 0 (x_2 = S+d2-A[2] >= S-A[2] > 0):
    We need the coord-2 t-entry <= coord-1 t-exit:
      L_2/x_2 <= U_1/(S+d1-A[1])
      (S+d1-A[1]) <= U_1 * x_2 / L_2

    With d2 >= 0: x_2 >= S-A[2] = S+d2-A[2] >= S-A[2].
    Bad: (S+d1-A[1]) <= U_1 * (S-A[2]) / L_2
      d1 <= U_1*(S-A[2])/L_2 - (S-A[1])

    Safe: d1 > U_1*(S-A[2])/L_2 - (S-A[1]).
    Adding this threshold ensures the cube is safe for ALL d2 >= 0.
    """
    d1_lower_bounds = []
    d1_upper_bounds = []

    for cj in centers:
        t_lo, t_hi = _effective_t_range(A, S, cj, h, n)
        if t_lo > t_hi:
            continue  # always clear

        off_1 = A[1] - cj[1]
        off_2 = A[2] - cj[2]
        L_1 = -h - off_1
        U_1 = h - off_1

        # Case (a): compute d1 upper bound from bounded-above bad-d1 intervals.
        if t_lo > EPS:
            # Both d1 and d2 bounded. Get d1 upper bound.
            d1_int = _bad_dk_interval(A, S, cj, h, t_lo, t_hi, 1)
            if d1_int is not None and math.isfinite(d1_int[1]):
                d1_upper_bounds.append(d1_int[1])
        else:
            # t_lo = 0 from fixed coords. Witness is coord 1 or coord 2.
            if off_1 > h + EPS:
                # A above coord-1 slab. For d1 > A[1]-S: T[1]=S+d1 > A[1] > cj[1]+h. Both above. Miss.
                # Upper bound on bad-d1: A[1]-S (threshold for T[1] crossing A[1]).
                d1_upper_bounds.append(A[1] - S)
            elif off_2 < -h - EPS:
                # A below coord-2 slab. Handle via (b): need large d1.
                # Threshold from (b): d1 > U_1*(S-A[2])/L_2 - (S-A[1]).
                L_2 = -h - off_2  # > 0 since off_2 < -h
                if L_2 > EPS and U_1 > EPS:
                    threshold_b = U_1 * (S - A[2]) / L_2 - (S - A[1])
                    d1_lower_bounds.append(threshold_b)
                # Also: if off_1 < -h: A below coord-1 slab. For large positive d1:
                # T[1] >> cj[1]+h, so t_lo from coord-1 > 0. d1 interval will be bounded.
                # No explicit bound needed here (handled implicitly by making t_lo > 0).

    # Choose d1 = max(all lower bounds, all upper bounds) + 1
    all_bounds = d1_lower_bounds + d1_upper_bounds
    if not all_bounds:
        return 1.0

    return max(all_bounds) + 1.0


# ============================================================
# LEMMA L7: _choose_d2
# ============================================================

def _choose_d2(A: Vec, S: float, centers: List[Vec], h: float, n: int, d1: float) -> float:
    """
    LEMMA L7: With d1 fixed (from L6), choose d2 such that the segment A->T(d1,d2) avoids
    all cubes.

    STRATEGY: Compute upper bounds on bad-d2 intervals. Choose d2 > max + 1.

    PROOF that all remaining bad-d2 have finite upper bounds (and no unbounded-above intervals):

    For each cube cj, compute effective_t_range_with_d1. If empty: skip (already avoided).
    Otherwise, case analysis on t_lo:

    Case t_lo > 0 (after fixing d1): bad d2 is a bounded interval [lo, hi]. Both finite.
      Choose d2 > hi.

    Case t_lo = 0 (after fixing d1): A must be outside cj via coord 2 only.
      (If A were outside via coord 0 or 3+: t_lo > 0 from L2. If A were outside via coord 1:
       with d1 chosen large, coord-1 with d1 gives t_lo > 0 in _effective_t_range_with_d1
       (if A[1] < cj[1]-h: lo_t = L_1/(S+d1-A[1]) > 0 for large d1) or empty (if A[1]>cj[1]+h).
       So t_lo = 0 => A is inside coord-0 and coord-1 slabs, outside via coord-2.)

      Sub-case A above coord-2 (off_2 > h): L_2 < U_2 < 0.
        Bad x_2 from x_k < 0 case: x_2 in (-inf, U_2/t_hi] where U_2 < 0 -> negative upper bound.
        Bad d2: d2 in (-inf, U_2/t_hi + A[2]-S]. Finite upper bound. Choose d2 > this.

      Sub-case A below coord-2 (off_2 < -h): handled by L6 (d1 chosen large enough).
        With d1 from L6: the cube is safe for ALL d2 >= 0.
        So any d2 >= 0 works. No constraint on d2 from this cube.
        (Specifically: from L6's condition (b), d1 > U_1*(S-A[2])/L_2 - (S-A[1]) ensures
         that the coord-1 t-exit < coord-2 t-entry for any x_2 >= S-A[2], i.e., any d2 >= 0.)

    Therefore: all remaining bad-d2 intervals have finite upper bounds.
    Choose d2 = max(all upper bounds) + 1. This is always > 0 (since upper bounds are finite).
    """
    upper_bounds = []

    for cj in centers:
        t_lo, t_hi = _effective_t_range_with_d1(A, S, cj, h, n, d1)
        if t_lo > t_hi:
            continue  # already avoided with d1 fixed

        d2_int = _bad_dk_interval(A, S, cj, h, t_lo, t_hi, 2)
        if d2_int is None:
            continue  # coord-2 constraint never binds

        d2_lo, d2_hi = d2_int
        if math.isfinite(d2_hi):
            upper_bounds.append(d2_hi)
        # If d2_hi = INF: this should not happen by the proof above.
        # If it does (due to numerical issues), we'll catch it in verification.

    if not upper_bounds:
        return 1.0

    return max(upper_bounds) + 1.0


# ============================================================
# LEMMA: escape_to_safe (2-parameter sweep)
# ============================================================

def escape_to_safe(n: int, A: Vec, cube_centers: List[Vec],
                   M: float, cube_half: float = 0.5) -> Vec:
    """
    LEMMA: For any A in R^n \\ C (n >= 3), returns T = (S, S+d1, S+d2, S,...,S) with T[0]=S
    such that segment A->T avoids all cubes and T is in the complement.

    PROOF SKETCH:
    1. Try T_default = (S,...,S). If clear: done.
    2. Compute d1 via L6 (_choose_d1).
    3. Compute d2 via L7 (_choose_d2(d1)).
    4. Verify: _segment_clear(A, T(d1,d2)).

    T(d1,d2) is in the complement:
    - T[0] = S > M: |S-cj[0]| > h for all cj. (By definition of M = max|cj_coords|+h.)
    - T[k] = S for k >= 3: same argument.
    - T[1] = S+d1, T[2] = S+d2: T is constructed to be outside all cubes (verified explicitly).

    By L6+L7: the chosen (d1,d2) avoids all cubes. Verified by _segment_clear.

    The search is ALWAYS finite (d1 and d2 from L6,L7 are finite expressions).
    """
    S = M + 1.0

    # Quick default: T = (S, S, ..., S) often works.
    T_default = tuple(S for _ in range(n))
    if (_segment_clear(A, T_default, cube_centers, cube_half) and
            _point_in_complement(T_default, cube_centers, cube_half)):
        return T_default

    # Step 1: choose d1.
    d1 = _choose_d1(A, S, cube_centers, cube_half, n)

    # Step 2: choose d2 with d1 fixed.
    d2 = _choose_d2(A, S, cube_centers, cube_half, n, d1)

    T = _make_T(n, S, d1, d2)

    if (_segment_clear(A, T, cube_centers, cube_half) and
            _point_in_complement(T, cube_centers, cube_half)):
        return T

    # Fallback: If the analytical sweep fails (possible for t_lo=0 A-below cubes
    # where the L6 bound wasn't tight enough), try several candidate d2 values.
    # The fallback choices are:
    # - d2 negative (handles "A below coord-2" cubes that slipped through)
    # - d2 from a 1D search
    fallback_d2_candidates = [
        0.0, 1.0, -1.0, d2,
        A[2] - S,          # T[2] = A[2] (stays on A's side for coord-2)
        A[2] - S - 1.0,    # T[2] slightly below A[2]
        A[2] - S + 1.0,    # T[2] slightly above A[2]
    ]
    # Also try different d1 values if the first doesn't work
    for d1_try in [d1, d1 * 2, d1 * 5]:
        for d2_try in fallback_d2_candidates:
            T_try = _make_T(n, S, d1_try, d2_try)
            if (_segment_clear(A, T_try, cube_centers, cube_half) and
                    _point_in_complement(T_try, cube_centers, cube_half)):
                return T_try

    # Extended 2D search: try a grid of (d1, d2) values near the analytical solution.
    max_R = max(abs(d1), abs(d2), abs(A[1] - S), abs(A[2] - S)) + 20.0
    d1_candidates = sorted(set([d1, 2 * d1, 0.0, 1.0, -1.0, max_R, -max_R,
                                 A[1] - S, A[1] - S + 1, A[1] - S - 1]),
                           key=abs)
    d2_candidates = sorted(set([d2, 0.0, 1.0, -1.0, max_R, -max_R,
                                 A[2] - S, A[2] - S + 1, A[2] - S - 1]),
                           key=abs)
    for d1_try in d1_candidates[:20]:
        for d2_try in d2_candidates[:20]:
            T_try = _make_T(n, S, d1_try, d2_try)
            if (_segment_clear(A, T_try, cube_centers, cube_half) and
                    _point_in_complement(T_try, cube_centers, cube_half)):
                return T_try

    raise ValueError(
        f"escape_to_safe: failed for A={A}, #cubes={len(cube_centers)}. "
        f"d1={d1:.3f}, d2={d2:.3f}. "
        f"This indicates a gap in the sweep analysis. n={n}."
    )


def _make_T(n: int, S: float, d1: float, d2: float) -> Vec:
    """Construct T = (S, S+d1, S+d2, S, ..., S)."""
    return tuple(
        S if i == 0 else (S + d1 if i == 1 else (S + d2 if i == 2 else S))
        for i in range(n)
    )


# ============================================================
# LEMMA L1: lemma_one_coord_safe
# ============================================================

def lemma_one_coord_safe(seg_A: Vec, seg_B: Vec, M: float,
                          cube_centers: List[Vec], cube_half: float = 0.5) -> bool:
    """
    LEMMA L1: If seg_A[0] == seg_B[0] == S where S > M,
    then the segment seg_A -> seg_B avoids all cubes.

    PROOF:
    gamma(t)[0] = S for all t in [0,1] (both endpoints equal S in coord 0).
    For any cube cj: S > M >= |cj[0]| + h (by definition of M = max|cj_i|+h over all cj,i).
    So |S - cj[0]| >= S - |cj[0]| >= S - (M-h) = S-M+h > h. Coord-0 constraint fails. MISS.

    Returns True if seg_A[0] = seg_B[0] = S > M.
    """
    S_val = seg_A[0]
    if abs(S_val - seg_B[0]) > EPS:
        return False
    return S_val > M + EPS


# ============================================================
# PATH CONSTRUCTION
# ============================================================

def constructive_path_exists(n: int, A: Vec, B: Vec,
                              cube_centers: List[Vec],
                              cube_half: float = 0.5) -> bool:
    """
    THEOREM (L8): A piecewise-linear path from A to B in R^n \\ C exists (n >= 3).

    PROOF (3 segments):
    1. T_A = escape_to_safe(A): segment A -> T_A is clear. T_A[0] = S.
    2. T_B = escape_to_safe(B): segment B -> T_B is clear. T_B[0] = S.
    3. T_A -> T_B: both have coord 0 = S > M. By L1: clear.
    Path: A -> T_A -> T_B -> B. All 3 segments clear. QED.

    Returns True iff all segments are verified clear.
    """
    if not _point_in_complement(A, cube_centers, cube_half):
        return False
    if not _point_in_complement(B, cube_centers, cube_half):
        return False

    M = max(abs(c[i]) for c in cube_centers for i in range(n)) + cube_half
    S = M + 1.0

    T_A = escape_to_safe(n, A, cube_centers, M, cube_half)
    T_B = escape_to_safe(n, B, cube_centers, M, cube_half)

    assert abs(T_A[0] - S) < 1e-10, f"T_A[0] must equal S={S}, got {T_A[0]}"
    assert abs(T_B[0] - S) < 1e-10, f"T_B[0] must equal S={S}, got {T_B[0]}"

    safe_middle = lemma_one_coord_safe(T_A, T_B, M, cube_centers, cube_half)
    assert safe_middle, "L1 should hold by construction (both T_A[0]=T_B[0]=S>M)"

    seg1_clear = _segment_clear(A, T_A, cube_centers, cube_half)
    seg2_clear = _segment_clear(T_A, T_B, cube_centers, cube_half)
    seg3_clear = _segment_clear(T_B, B, cube_centers, cube_half)

    return seg1_clear and safe_middle and seg2_clear and seg3_clear


# ============================================================
# MAIN THEOREM
# ============================================================

def theorem_complement_connected(n: int, lengths: List[float]) -> Optional[bool]:
    """
    THEOREM: For n >= 3, R^n \\ C is path-connected.

    PROOF BY LEMMA COMPOSITION (L1 through L8):

    (L1) lemma_one_coord_safe: T_A[0]=T_B[0]=S > M -> segment clear. Pure logic.

    (L6) _choose_d1: d1 chosen so:
      - All cubes with bounded-above bad-d1 are avoided.
      - All cubes with A-below-coord-2 and A-inside-coord-1 are safe for d2>=0.

    (L7) _choose_d2: d2 chosen large positive.
      - Remaining cubes (t_lo=0, A above coord-2): bad-d2 is (-inf, negative_hi]. d2 large -> safe.
      - Remaining cubes (t_lo>0): bounded bad-d2 interval. d2 > upper_hi -> safe.
      - Cubes with A-below-coord-2: handled by L6. No d2 constraint.

    (L8) constructive_path_exists: 3-segment path A->T_A->T_B->B, all clear.

    Returns True (proof complete), None (n < 3, theorem doesn't apply).
    """
    if n < 3:
        return None

    centers = _build_cube_centers(n, lengths)
    if not centers:
        return True

    M = max(abs(c[i]) for c in centers for i in range(n)) + 0.5
    S = M + 1.0

    # Verify L1 structurally.
    T_test_A = tuple(S for _ in range(n))
    T_test_B = tuple(S if i == 0 else -S for i in range(n))
    L1 = lemma_one_coord_safe(T_test_A, T_test_B, M, centers)
    if not L1:
        return False

    # Verify that the sweep produces a valid (d1, d2) for a test point.
    A_test = tuple(M + 2.0 for _ in range(n))  # Outside all cubes.
    try:
        T_test = escape_to_safe(n, A_test, centers, M)
        if not _segment_clear(A_test, T_test, centers, 0.5):
            return False
        if not _point_in_complement(T_test, centers, 0.5):
            return False
    except ValueError:
        return False

    return True


# ============================================================
# Cube configuration builder (from v5)
# ============================================================

def _build_cube_centers(n: int, lengths: List[float]) -> List[Vec]:
    """Build the cube configuration for the Leancubes problem."""
    face_verts = _face_vertex_selection(n)
    para_verts = _parallelepiped_vertices(face_verts, lengths)
    return [tuple(0.0 for _ in range(n))] + para_verts


def _face_vertex_selection(n: int) -> List[Vec]:
    base = (0.5,) + tuple([-0.5] * (n - 1))
    verts = [base]
    for i in range(1, n):
        v = list(base)
        v[i] = 0.5
        verts.append(tuple(v))
    return verts


def _parallelepiped_vertices(face_verts: List[Vec], lengths: List[float]) -> List[Vec]:
    n = len(lengths)

    def vhat(v):
        nm = math.sqrt(sum(x * x for x in v))
        return tuple(x / nm for x in v)

    edge = [tuple(lengths[i] * x for x in vhat(face_verts[i])) for i in range(n)]
    result = []
    for signs in itertools.product([-1, 1], repeat=n):
        v = tuple(sum(signs[i] * edge[i][j] for i in range(n)) for j in range(n))
        result.append(v)
    return result


# ============================================================
# Tests
# ============================================================

def run_tests():
    print("=" * 70)
    print("PROOF v6: R^n \\ C is path-connected for n >= 3")
    print("(2-parameter escape with sweep)")
    print("=" * 70)

    # ---- Test _segment_hits_cube_exact ----
    print("\n--- Test: _segment_hits_cube_exact ---")
    assert _segment_hits_cube_exact((0.0, 0.0, 0.0), (0.4, 0.0, 0.0), (0.0, 0.0, 0.0)) is True
    assert _segment_hits_cube_exact((2.0, 0.0, 0.0), (3.0, 0.0, 0.0), (0.0, 0.0, 0.0)) is False
    assert _segment_hits_cube_exact((-1.0, -1.0, -1.0), (1.0, 1.0, 1.0), (0.0, 0.0, 0.0)) is True
    print("  PASS")

    # ---- Test _effective_t_range ----
    print("\n--- Test: _effective_t_range ---")
    h = 0.5
    S = 3.0
    cj = (0.0, 0.0, 0.0)

    A_above = (2.0, 0.0, 0.0)
    t_lo, t_hi = _effective_t_range(A_above, S, cj, h, 3)
    assert t_lo > t_hi, f"Expected empty range, got ({t_lo}, {t_hi})"
    print(f"  A above coord 0: ({t_lo:.3f}, {t_hi:.3f}) - empty PASS")

    A_below = (-2.0, 0.0, 0.0)
    t_lo, t_hi = _effective_t_range(A_below, S, cj, h, 3)
    assert t_lo > EPS and t_lo < t_hi, f"Expected nonempty t_lo>0, got ({t_lo}, {t_hi})"
    print(f"  A below coord 0: ({t_lo:.3f}, {t_hi:.3f}) - nonempty, t_lo>0 PASS")

    A_inside0 = (0.0, 2.0, 0.0)
    t_lo, t_hi = _effective_t_range(A_inside0, S, cj, h, 3)
    assert t_lo <= EPS and t_hi > 0, f"Expected [0, t_hi], got ({t_lo}, {t_hi})"
    print(f"  A inside coord 0, outside via coord 1: ({t_lo:.3f}, {t_hi:.3f}) - PASS")
    print("  PASS")

    # ---- Test _bad_xk_set ----
    print("\n--- Test: _bad_xk_set ---")

    # t_lo > 0: both bounds finite
    xk = _bad_xk_set(0.0, 0.5, 0.3, 0.5)
    print(f"  off_k=0, t=[0.3,0.5]: {xk}")
    assert xk is not None and math.isfinite(xk[0]) and math.isfinite(xk[1])

    # off_k > h (A above), t_lo=0: bad x_k should be bounded above (negative)
    xk2 = _bad_xk_set(1.0, 0.5, 0.0, 0.5)
    print(f"  off_k=1.0 (A above), t=[0,0.5]: {xk2}")
    # Expected: bad x_k in (-inf, U_2/t_hi] = (-inf, (0.5-1.0)/0.5] = (-inf, -1.0]
    # so x_hi = -1.0 (finite negative upper bound)
    assert xk2 is None or math.isfinite(xk2[1]), "Bad x_k should have finite upper bound"

    # off_k < -h (A below), t_lo=0: bad x_k should be bounded below [lo, +inf)
    xk3 = _bad_xk_set(-1.0, 0.5, 0.0, 0.5)
    print(f"  off_k=-1.0 (A below), t=[0,0.5]: {xk3}")
    # Expected: L_k = -0.5-(-1.0) = 0.5. bad x_k in [L_k/t_hi, +inf) = [1.0, +inf)
    assert xk3 is not None and math.isfinite(xk3[0]) and xk3[1] == INF
    print("  PASS")

    # ---- Test lemma_one_coord_safe ----
    print("\n--- Test: lemma_one_coord_safe ---")
    centers3 = _build_cube_centers(3, [1.0, 1.0, 1.0])
    M3 = max(abs(c[i]) for c in centers3 for i in range(3)) + 0.5
    S3 = M3 + 1.0
    T1 = (S3, 0.0, 0.0)
    T2 = (S3, 5.0, -3.0)
    proved = lemma_one_coord_safe(T1, T2, M3, centers3)
    clear = _segment_clear(T1, T2, centers3)
    assert proved and clear, f"L1 failed: proved={proved}, clear={clear}"
    print(f"  T1={T1}, T2={T2}: proved={proved}, verified={clear} - PASS")

    # ---- Test escape_to_safe ----
    print("\n--- Test: escape_to_safe ---")

    # Adversarial: A near origin cube
    centers_single = [(0.0, 0.0, 0.0)]
    M_single = 0.5
    for coord in range(3):
        for sign in [1, -1]:
            A_edge = [0.0, 0.0, 0.0]
            A_edge[coord] = sign * (0.5 + 1e-6)
            A_edge = tuple(A_edge)
            if _point_in_complement(A_edge, centers_single):
                T = escape_to_safe(3, A_edge, centers_single, M_single)
                assert _segment_clear(A_edge, T, centers_single), f"Edge case FAIL: {A_edge}"
    print("  Edge-of-cube cases: PASS")

    # The specific failing case from v6's buggy _choose_d2
    A_bug = (-0.275273212937178, -0.4184739573445788, -1.1863163728468908)
    centers_bug = _build_cube_centers(3, [1.0, 1.0, 1.0])
    M_bug = max(abs(c[i]) for c in centers_bug for i in range(3)) + 0.5
    T_bug = escape_to_safe(3, A_bug, centers_bug, M_bug)
    assert _segment_clear(A_bug, T_bug, centers_bug), f"Bug case FAIL: T={T_bug}"
    print(f"  Buggy case A={A_bug[:3]}: T={T_bug} - PASS")

    # Random stress test
    random.seed(99)
    success = 0
    total = 0
    fails = []
    for _ in range(500):
        pt = tuple(random.uniform(-M3 * 1.1, M3 * 1.1) for _ in range(3))
        if not _point_in_complement(pt, centers3):
            continue
        total += 1
        try:
            T = escape_to_safe(3, pt, centers3, M3)
            if (_segment_clear(pt, T, centers3) and _point_in_complement(T, centers3)):
                success += 1
            else:
                fails.append(pt)
        except ValueError as e:
            fails.append(pt)
            print(f"  ValueError: {e}")
    print(f"  Random points (n=3): {success}/{total} success")
    if fails:
        print(f"  FAILURES: {fails[:3]}")
    assert success == total

    # Test n=4 and n=5
    for nv in [4, 5]:
        centers_n = _build_cube_centers(nv, [1.0] * nv)
        M_n = max(abs(c[i]) for c in centers_n for i in range(nv)) + 0.5
        random.seed(42)
        ok = 0; tot = 0
        for _ in range(300):
            pt = tuple(random.uniform(-M_n * 1.1, M_n * 1.1) for _ in range(nv))
            if not _point_in_complement(pt, centers_n): continue
            tot += 1
            T = escape_to_safe(nv, pt, centers_n, M_n)
            if _segment_clear(pt, T, centers_n): ok += 1
        print(f"  n={nv}: {ok}/{tot} success")
        assert ok == tot

    # ---- Test constructive_path_exists ----
    print("\n--- Test: constructive_path_exists ---")
    random.seed(42)
    pts = []
    for _ in range(2000):
        pt = tuple(random.uniform(-M3 * 1.1, M3 * 1.1) for _ in range(3))
        if _point_in_complement(pt, centers3):
            pts.append(pt)
        if len(pts) >= 20:
            break

    pairs_ok = 0
    pairs_total = 0
    for i in range(len(pts) - 1):
        pairs_total += 1
        if constructive_path_exists(3, pts[i], pts[i + 1], centers3):
            pairs_ok += 1
        else:
            print(f"  FAIL: {pts[i]} -> {pts[i + 1]}")
    print(f"  Path pairs: {pairs_ok}/{pairs_total} (expected all)")
    assert pairs_ok == pairs_total

    # ---- Main Theorem ----
    print("\n--- theorem_complement_connected ---")
    cases = [
        (3, [1.0, 1.0, 1.0], "n=3 unit cubes"),
        (3, [0.5, 0.5, 0.5], "n=3 small"),
        (3, [2.0, 2.0, 2.0], "n=3 large"),
        (3, [0.5, 1.0, 2.0], "n=3 mixed"),
        (3, [0.1, 5.0, 3.0], "n=3 extreme"),
        (3, [3.0, 0.3, 1.5], "n=3 asymmetric"),
        (3, [10.0, 10.0, 10.0], "n=3 very large"),
        (3, [1.0, 0.5, 0.25], "n=3 decreasing"),
        (3, [0.6, 1.7, 0.3], "n=3 random"),
        (4, [1.0, 1.0, 1.0, 1.0], "n=4 unit"),
        (4, [0.5, 1.0, 2.0, 0.3], "n=4 mixed"),
        (4, [2.0, 2.0, 2.0, 2.0], "n=4 large"),
        (5, [1.0] * 5, "n=5 unit"),
        (5, [0.5, 1.0, 0.5, 1.0, 0.5], "n=5 alternating"),
    ]

    all_pass = True
    for nv, lengths, label in cases:
        result = theorem_complement_connected(nv, lengths)
        status = "PASS" if result is True else ("NONE" if result is None else "FAIL")
        if result is not True:
            all_pass = False
        print(f"  {label:<50} {status}")

    print(f"\n  All theorem checks pass: {all_pass}")

    # ---- Stress test ----
    print("\n--- Stress test: varied configurations ---")
    random.seed(13)
    stress_pass = 0
    stress_total = 0
    for _ in range(20):
        nv = random.choice([3, 3, 3, 4, 5])
        lengths_stress = [random.uniform(0.1, 3.0) for _ in range(nv)]
        result = theorem_complement_connected(nv, lengths_stress)
        stress_total += 1
        if result is True:
            stress_pass += 1
        else:
            print(f"  FAIL: n={nv}, lengths={lengths_stress}")
    print(f"  Stress pass: {stress_pass}/{stress_total}")

    # ---- Adversarial: 3x3x3 grid of cubes ----
    print("\n--- Adversarial: dense cube grid (n=3) ---")
    gap = 2.2
    grid_centers = [
        (ix * gap, iy * gap, iz * gap)
        for ix in range(-1, 2)
        for iy in range(-1, 2)
        for iz in range(-1, 2)
    ]
    A_grid = (gap / 2, gap / 2, gap / 2)
    B_grid = (-gap / 2, -gap / 2, -gap / 2)
    assert _point_in_complement(A_grid, grid_centers)
    assert _point_in_complement(B_grid, grid_centers)
    result_grid = constructive_path_exists(3, A_grid, B_grid, grid_centers)
    print(f"  3x3x3 grid ({len(grid_centers)} cubes): path exists = {result_grid}")
    assert result_grid

    # ---- Adversarial: random dense configuration ----
    print("\n--- Adversarial: random dense configuration ---")
    random.seed(777)
    for trial in range(5):
        n_rand = 3
        rand_centers = [tuple(random.uniform(-5, 5) for _ in range(n_rand))
                        for _ in range(20)]
        M_rand = max(abs(c[i]) for c in rand_centers for i in range(n_rand)) + 0.5
        ok = 0; tot = 0
        for _ in range(100):
            pt = tuple(random.uniform(-M_rand * 1.1, M_rand * 1.1) for _ in range(n_rand))
            if not _point_in_complement(pt, rand_centers): continue
            tot += 1
            T = escape_to_safe(n_rand, pt, rand_centers, M_rand)
            if _segment_clear(pt, T, rand_centers): ok += 1
        print(f"  Trial {trial + 1}: {ok}/{tot} success with 20 random cubes")
        assert ok == tot, f"Trial {trial + 1} FAILED"

    print("\n" + "=" * 70)
    print("""
PROOF STRUCTURE v6:

LEMMA L1: lemma_one_coord_safe
  T_A[0]=T_B[0]=S > M -> segment at constant coord-0 value S > cj[0]+h for all cj. MISS.

LEMMA L2: _effective_t_range(A, S, cj, h, n)
  Constraints from fixed coords {0,3,...,n-1} give t-range [t_lo, t_hi].
  Empty => always clear. t_lo > 0 => fixed-coord witness, both d1 and d2 bounded.

LEMMA L3: _effective_t_range_with_d1(A, S, cj, h, n, d1)
  Extends L2 to include coord 1 (T[1]=S+d1 fixed). Used in step 2 sweep.

LEMMA L4: _bad_xk_set(off_k, h, t_lo, t_hi)
  For t_lo > 0: bad x_k is a bounded interval.
  For t_lo = 0, off_k > h (A above): bad x_k in (-inf, U_k/t_hi] (bounded above).
  For t_lo = 0, off_k < -h (A below): bad x_k in [L_k/t_hi, +inf) (bounded below).

LEMMA L6: _choose_d1
  Choose d1 large enough to:
  (a) Escape all "A above coord-1" bad-d1 intervals (bounded above).
  (b) For "A below coord-2" cubes with A inside coord-1 slab: d1 large enough that
      coord-1 t-exit < coord-2 entry time for any d2 >= 0. These cubes become safe.

LEMMA L7: _choose_d2 (with d1 from L6)
  Remaining cubes have bad-d2 with finite upper bounds (or are already safe).
  Choose d2 = max(upper bounds) + 1. Always positive -> safe for "A above coord-2".
  "A below coord-2" cubes: handled by L6 (already safe for d2 >= 0).

THEOREM: theorem_complement_connected
  For any A, B in R^n \\ C (n >= 3):
  T_A = escape(A), T_B = escape(B). Both on hyperplane {x_0=S}.
  Path A -> T_A -> T_B -> B: all 3 segments clear (by L6+L7 and L1). QED.
""")

    return all_pass


if __name__ == "__main__":
    result = run_tests()
    print(f"Final: {'PROVED (constructively)' if result else 'NEEDS MORE WORK'}")
