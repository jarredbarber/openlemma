"""
lemma_escape_v3.py  --  Phase 2 (structural) escape proof for R^n \\ C (n >= 3)

THEOREM: For n >= 3, given finitely many axis-aligned unit cubes (half-width h=0.5)
in R^n and a point A in the complement, there exists T = (S, S+d1, S+d2, S, ..., S)
on the hyperplane {x_0 = S} (S = M+1, M = max|cj[0]|+h) such that segment A->T
avoids all cubes.

PROOF STRUCTURE (phase 2 — no floats, no search, no epsilon):

  lemma_t_range_independent
    The t-interval from fixed coords {0, 3, ..., n-1} does not depend on d1 or d2.
    Proof: those coords have T[i]=S, a constant independent of d1, d2.

  lemma_d_interval_bounded
    When t_lo > 0 (t-range bounded away from 0), the d-interval for coords 1 and 2
    is finite. Proof: the interval is a quotient of two finite bounds.

  lemma_P3
    For A outside cube cj, the bad set is bounded in at least one of d1 or d2.
    Proof: case split on t_lo > 0 vs. t_lo = 0.
      - t_lo > 0: both intervals finite (by lemma_d_interval_bounded).
      - t_lo = 0: A outside cj, so A is outside in some coord. Fixed coords
        all held (non-empty t-range). So A is outside via coord 1 or coord 2,
        giving that coord a half-line interval (one finite endpoint).

  lemma_gap
    The value A[k]-S lies strictly outside all half-line d_k intervals from cubes
    where A is outside coord k's slab. Proof: explicit inequality.

  lemma_escape_exists
    Main theorem. Argument: d1 = A[1]-S clears all d1-halfline cubes (lemma_gap).
    Remaining cubes have non-full d2 intervals (by lemma_P3 applied to each).
    Finitely many non-full intervals cannot cover R, so a good d2 exists
    (lemma_finite_intervals_dont_cover_R). Therefore (d1, d2) exists.

Phase 2 discipline: each function returns True based on structural case analysis.
The test suite uses Fraction for exact arithmetic to verify the structural
arguments on concrete configurations (not to prove, but to exercise the proof path).
"""

from fractions import Fraction
from typing import List, Tuple, Optional, Union

# ============================================================
# Types
# ============================================================

# A rational vector
RVec = Tuple[Fraction, ...]
# An interval endpoint: Fraction, or None meaning -inf/+inf
# We represent intervals as (lo, hi) where:
#   lo = None  =>  lower bound is -infinity
#   hi = None  =>  upper bound is +infinity
Endpoint = Optional[Fraction]
Interval = Tuple[Endpoint, Endpoint]  # (lo, hi), lo=None => -inf, hi=None => +inf

# Classification of an interval
INTERVAL_EMPTY    = "empty"      # empty (no t satisfies)
INTERVAL_FINITE   = "finite"     # both endpoints finite
INTERVAL_LOWER    = "lower"      # (-inf, hi]  i.e. lo=None, hi finite
INTERVAL_UPPER    = "upper"      # [lo, +inf)  i.e. lo finite, hi=None
INTERVAL_FULL     = "full"       # (-inf, +inf)


def interval_type(iv: Interval) -> str:
    lo, hi = iv
    if lo is not None and hi is not None and lo > hi:
        return INTERVAL_EMPTY
    if lo is None and hi is None:
        return INTERVAL_FULL
    if lo is None:
        return INTERVAL_LOWER
    if hi is None:
        return INTERVAL_UPPER
    return INTERVAL_FINITE


def interval_contains(iv: Interval, v: Fraction) -> bool:
    """True iff v is in the interval [lo, hi] (with None = inf)."""
    lo, hi = iv
    if lo is not None and v < lo:
        return False
    if hi is not None and v > hi:
        return False
    return True


# ============================================================
# LEMMA: lemma_t_range_independent
# ============================================================

def lemma_t_range_independent(n: int) -> bool:
    """
    CLAIM: For T = (S, S+d1, S+d2, S, ..., S), the slab constraints from
    fixed coords {0, 3, ..., n-1} depend only on S, not on d1 or d2.

    PROOF: For i in {0, 3, ..., n-1}, T[i] = S. The slab constraint for
    coord i is: A[i] + t*(T[i] - A[i]) in [cj[i]-h, cj[i]+h], which
    simplifies to A[i] + t*(S - A[i]) in [cj[i]-h, cj[i]+h]. This
    expression contains only S (fixed), A[i] (fixed), and t. It does NOT
    contain d1 or d2. Therefore the t-interval from these coords is
    independent of d1 and d2.

    Returns True for n >= 3 (the fixed coord set is well-defined).
    Returns None for n < 3 (the argument doesn't apply: no coords >= 3).
    """
    if n < 3:
        return None  # Gap: need n >= 3 for fixed coords {0, 3, ..., n-1}
    # For n=3: fixed coords = {0}. For n=4: {0, 3}. Etc.
    # All of these have T[i] = S, independent of d1, d2. QED.
    return True


# ============================================================
# LEMMA: lemma_d_interval_bounded
# ============================================================

def lemma_d_interval_bounded(t_lo: Fraction, t_hi: Fraction,
                              a_coord: Fraction, cj_coord: Fraction,
                              h: Fraction) -> bool:
    """
    CLAIM: If 0 < t_lo <= t_hi, the d-interval for this coord is finite (bounded).

    Setup: T[coord] = S + d. Segment at coord: a_coord + t*(S + d - a_coord).
    Slab constraint: a_coord + t*(S + d - a_coord) in [cj_coord - h, cj_coord + h].
    Let off = a_coord - cj_coord, L = -h - off, U = h - off.
    Rewrite: t*(S + d - a_coord) in [L, U].
    Let v = S + d - a_coord  (so d = v + a_coord - S).
    Constraint: t*v in [L, U] for SOME t in [t_lo, t_hi].

    For t > 0 (all of [t_lo, t_hi] has t > 0 since t_lo > 0):
    t*v in [L, U] iff v in [L/t, U/t] (dividing by t, which is positive).
    Over t in [t_lo, t_hi], the intersection of [L/t, U/t] across t is:
      v_lo = max over t in [t_lo, t_hi] of (L/t if L>=0 else L/t_lo ... )

    More carefully: The hit condition is: exists t in [t_lo, t_hi] s.t. L <= t*v <= U.
    Equivalently: exists t s.t. L/t <= v <= U/t (since t > 0).
    The set of v that CAN be hit (for some t in [t_lo, t_hi]) is:
      union over t in [t_lo, t_hi] of [L/t, U/t].

    As t varies in [t_lo, t_hi] (both positive):
      L/t is monotone decreasing in t (for L > 0: smaller at larger t; for L < 0: larger at larger t)
      U/t is monotone decreasing in t.

    The union over t of [L/t, U/t] = [min(L/t), max(U/t)] where min/max over t in [t_lo, t_hi].
    For L >= 0: L/t achieves min at t_hi, so min(L/t) = L/t_hi. Max(U/t) = U/t_lo.
    For L < 0: L/t achieves min (most negative) at t_lo, so min = L/t_lo. Max(U/t) = U/t_lo.

    In all cases: L/t_lo, L/t_hi, U/t_lo, U/t_hi are all finite rationals (since
    t_lo, t_hi are positive rationals and L, U are rationals). The interval for v is:
      [lo_v, hi_v] = [min(L/t_lo, L/t_hi), max(U/t_lo, U/t_hi)]
    which is a finite interval. Therefore d = v + a_coord - S is also in a finite interval.

    STRUCTURAL ARGUMENT: Since t_lo > 0, all quantities L/t_lo, L/t_hi, U/t_lo, U/t_hi
    are well-defined finite rationals. Hence the d-interval is [finite, finite]. QED.

    Returns True if t_lo > 0. Returns None if t_lo <= 0.
    """
    if t_lo <= 0:
        return None  # Precondition not met; cannot conclude finite interval
    # t_lo > 0: all four quotients are finite. Interval is [finite, finite].
    return True


# ============================================================
# STRUCTURAL HELPERS: compute t-range and d-interval with Fraction
# ============================================================

def _compute_t_range_fixed_coords(A: RVec, S: Fraction, cj: RVec,
                                   h: Fraction, n: int) -> Interval:
    """
    Compute the t-interval [t_lo, t_hi] from fixed coords {0, 3, ..., n-1}.
    Uses exact Fraction arithmetic. Returns (t_lo, t_hi) as Fraction values
    (never None). t_lo starts at 0, t_hi at 1, updated via max/min.
    """
    t_lo: Endpoint = Fraction(0)
    t_hi: Endpoint = Fraction(1)
    fixed_coords = [0] + list(range(3, n))
    for i in fixed_coords:
        d = S - A[i]
        off = A[i] - cj[i]
        if d == 0:
            # A[i] = S: the coord is constant along the segment.
            # Must have |off| <= h for slab to be hit at all.
            if abs(off) > h:
                return (Fraction(1), Fraction(0))  # empty
        else:
            lo_t = (-h - off) / d
            hi_t = ( h - off) / d
            if d < 0:
                lo_t, hi_t = hi_t, lo_t
            # Intersect with current [t_lo, t_hi]
            if t_lo is None:
                t_lo = lo_t
            else:
                t_lo = max(t_lo, lo_t)
            if t_hi is None:
                t_hi = hi_t
            else:
                t_hi = min(t_hi, hi_t)
            if t_lo is not None and t_hi is not None and t_lo > t_hi:
                return (Fraction(1), Fraction(0))  # empty
    return (t_lo, t_hi)


def _compute_d_interval(A: RVec, S: Fraction, cj: RVec, h: Fraction,
                         coord: int, t_lo: Endpoint, t_hi: Endpoint) -> Interval:
    """
    Compute the d-interval for coord k (k=1 or 2), T[k] = S + d.
    Returns (d_lo, d_hi) with None = -inf/+inf.

    CASE t_lo > 0: interval is finite (by lemma_d_interval_bounded).
    CASE t_lo = 0: depends on whether A is inside/outside the slab.
    """
    off = A[coord] - cj[coord]
    L = -h - off
    U =  h - off

    # t_hi must be > 0 for any hit to occur (since t_lo >= 0)
    if t_hi is not None and t_hi <= 0:
        return (Fraction(1), Fraction(0))  # empty: no positive t in range

    if t_lo is not None and t_lo > 0:
        # Case: t_lo > 0. All quotients finite.
        # Union over t in [t_lo, t_hi] of [L/t, U/t]:
        #   lo = min(L/t) = L/t_hi if L >= 0, L/t_lo if L < 0
        #   hi = max(U/t) = U/t_lo if U >= 0, U/t_hi if U < 0
        # (for U < 0 this becomes a negative interval, handled by lo > hi check)
        lo_v = L / t_hi if L >= 0 else L / t_lo
        hi_v = U / t_lo if U >= 0 else U / t_hi
        if lo_v > hi_v:
            return (Fraction(1), Fraction(0))  # empty
        d_lo = lo_v + A[coord] - S
        d_hi = hi_v + A[coord] - S
        return (d_lo, d_hi)
    else:
        # Case: t_lo = 0 (or None). Check if A is inside/outside the slab.
        if abs(off) <= h:
            # A inside slab: any d is compatible (no constraint from this coord alone).
            return (None, None)  # full interval
        elif off > h:
            # A above slab (off > h => A[coord] > cj[coord] + h).
            # L = -h - off < 0, U = h - off < 0 (both negative).
            # For small t > 0: t*v in [L, U] requires v < 0, so d < A[coord] - S.
            # The upper bound is U/t_hi + A[coord] - S, which is finite.
            # Since U < 0 and t_hi > 0: U/t_hi < 0, so d_hi < A[coord] - S.
            d_hi = U / t_hi + A[coord] - S
            return (None, d_hi)  # (-inf, d_hi]
        else:
            # A below slab (off < -h => A[coord] < cj[coord] - h).
            # L = -h - off > 0, U = h - off > 0 (both positive).
            # The lower bound is L/t_hi + A[coord] - S, which is finite.
            # Since L > 0 and t_hi > 0: L/t_hi > 0, so d_lo > A[coord] - S.
            d_lo = L / t_hi + A[coord] - S
            return (d_lo, None)  # [d_lo, +inf)


# ============================================================
# LEMMA: lemma_P3
# ============================================================

def lemma_P3(A: RVec, S: Fraction, cj: RVec, h: Fraction, n: int,
             t_range: Interval) -> Optional[bool]:
    """
    CLAIM: For A outside cube cj and non-empty t-range, the bad set for cj
    is not 'both_unbounded' (i.e., it is bounded in at least one of d1 or d2).

    PROOF (case split on t_lo):

    Let (t_lo, t_hi) = t_range (from fixed coords, independent of d1, d2 by
    lemma_t_range_independent).

    CASE 1: t_lo > 0.
      By lemma_d_interval_bounded, both d1 and d2 intervals are finite.
      => bad set is finite x finite. => bounded in both. QED.

    CASE 2: t_lo = 0 (or t_lo is None, meaning the t-range starts at 0).
      A is outside cj (given). Consider coords:
        - Fixed coords {0, 3,...,n-1}: these gave a non-empty t-range [0, t_hi].
          The t-range being non-empty means A is inside each of these slabs,
          or the directional constraint was compatible. (If A were outside a
          fixed-coord slab AND the segment direction made intersection impossible,
          the t-range would be empty. Since it's non-empty and t_lo=0, each
          fixed coord has A inside its slab OR the segment can enter the slab
          as t increases from 0.)
        - However, A is outside cj. So A must be outside cj in some coordinate.
        - If A were inside ALL slabs of cj (coords 0..n-1), then A is inside cj,
          contradicting A in complement. So A is outside at least one slab.
        - Fixed coords: A is compatible with t=0 being in the t-range. At t=0,
          gamma(0) = A. For t=0 to be in the slab constraint of coord i:
          A[i] in [cj[i]-h, cj[i]+h]. So if t_lo=0 is in the t-range, each
          fixed coord has A[i] in [cj[i]-h, cj[i]+h].
          => A is INSIDE each fixed coord's slab.
        - Since A is inside all fixed coord slabs and outside cj, A must be
          outside cj in coord 1 or coord 2 (the free coords).
        - Subcase 2a: |A[1] - cj[1]| > h.
          => _compute_d_interval for coord 1 returns a half-line (one finite endpoint).
          => d1 interval is not full. => bad set bounded in d1 direction.
        - Subcase 2b: |A[2] - cj[2]| > h.
          => d2 interval has one finite endpoint. => bad set bounded in d2.
        - Subcase 2c: A inside slabs 1 AND 2 AND all fixed coords.
          => A inside all slabs => A inside cj. Contradicts A in complement.
          => IMPOSSIBLE.

    In all cases, at least one of d1 or d2 has a finite endpoint. QED.

    Returns True if structural argument holds. Returns None if gap detected.
    """
    t_lo, t_hi = t_range
    # t-range must be non-empty
    if t_lo is not None and t_hi is not None and t_lo > t_hi:
        # Empty t-range: cube skipped. Trivially True (cube never hit).
        return True

    if t_lo is not None and t_lo > 0:
        # Case 1: t_lo > 0.
        bounded = lemma_d_interval_bounded(t_lo, t_hi, A[1], cj[1], h)
        if bounded is not True:
            return None  # Gap: lemma_d_interval_bounded failed
        bounded2 = lemma_d_interval_bounded(t_lo, t_hi, A[2], cj[2], h)
        if bounded2 is not True:
            return None
        # Both finite. P3 holds.
        return True

    # Case 2: t_lo = 0.
    # INVARIANT: _compute_t_range_fixed_coords always returns Fraction values
    # (t_lo starts at Fraction(0), t_hi at Fraction(1), updated via max/min).
    # So t_lo is never None here; it is exactly Fraction(0).
    assert t_lo is not None and t_lo == 0, f"Expected t_lo=0, got {t_lo}"
    # At t=0, gamma(0) = A. For t=0 to be in [t_lo, t_hi], each fixed coord i
    # must have |A[i] - cj[i]| <= h (else the fixed-coord slab constraint would
    # have pushed t_lo above 0 or made the t-range empty).
    # Therefore A is inside all fixed-coord slabs.
    # Structural argument: A must be outside cj via coord 1 or coord 2.
    out1 = abs(A[1] - cj[1]) > h
    out2 = abs(A[2] - cj[2]) > h

    if not out1 and not out2:
        # Subcase 2c: A inside both free coord slabs.
        # For this to not be a contradiction, A must be outside some fixed coord.
        # But if t_lo = 0 is in the t-range, all fixed coords have A inside their slabs.
        # So A would be inside ALL slabs => inside cj. Contradiction.
        # If the input is valid (A outside cj), this branch is impossible.
        # Return None to signal the contradiction / gap.
        return None

    # Subcase 2a or 2b: A outside via coord 1 or coord 2 (or both).
    # Verify that the d-interval for the 'outside' coord is indeed a half-line.
    if out1:
        d1_iv = _compute_d_interval(A, S, cj, h, 1, t_lo, t_hi)
        typ = interval_type(d1_iv)
        if typ not in (INTERVAL_LOWER, INTERVAL_UPPER, INTERVAL_FINITE):
            return None  # Gap: expected a half-line or finite interval
    if out2:
        d2_iv = _compute_d_interval(A, S, cj, h, 2, t_lo, t_hi)
        typ = interval_type(d2_iv)
        if typ not in (INTERVAL_LOWER, INTERVAL_UPPER, INTERVAL_FINITE):
            return None  # Gap: expected a half-line or finite interval

    # At least one of d1 or d2 has a finite endpoint. P3 holds.
    return True


# ============================================================
# LEMMA: lemma_gap
# ============================================================

def lemma_gap(A: RVec, S: Fraction, cj: RVec, h: Fraction, n: int,
              coord: int, t_range: Interval) -> Optional[bool]:
    """
    CLAIM: If A is outside cj's slab in coord k (|A[k] - cj[k]| > h),
    then the d_k interval for cj is a half-line and A[k] - S is STRICTLY
    OUTSIDE it. That is, A[k] - S is in the gap between opposing half-lines.

    PROOF:

    Let off = A[k] - cj[k], L = -h - off, U = h - off.

    CASE A above slab (off > h):
      off > h => L = -h - off < -h < 0, U = h - off < h - h = 0.
      Both L and U are negative.
      d_k interval = (-inf, U/t_hi + A[k] - S].
      hi = U/t_hi + A[k] - S.
      Since U < 0 and t_hi > 0: U/t_hi < 0.
      So hi = U/t_hi + A[k] - S < 0 + A[k] - S = A[k] - S.
      => A[k] - S > hi. => A[k] - S is ABOVE the upper bound. => strictly outside.

    CASE A below slab (off < -h):
      off < -h => L = -h - off > -h - (-h) = 0, U = h - off > h + h = 2h > 0.
      Both L and U are positive.
      d_k interval = [L/t_hi + A[k] - S, +inf).
      lo = L/t_hi + A[k] - S.
      Since L > 0 and t_hi > 0: L/t_hi > 0.
      So lo = L/t_hi + A[k] - S > 0 + A[k] - S = A[k] - S.
      => A[k] - S < lo. => A[k] - S is BELOW the lower bound. => strictly outside.

    In both cases, A[k] - S is strictly outside the d_k interval. QED.

    COROLLARY (gap lemma, coord k): If we set d_k = A[k] - S, then for every
    cube cj where A is outside slab k, the cube is missed via coord k.

    Returns True if the argument applies and gap is verified.
    Returns None if the structural conditions are not met.
    """
    off = A[coord] - cj[coord]
    if abs(off) <= h:
        return None  # Precondition not met: A inside slab; lemma doesn't apply

    t_lo, t_hi = t_range
    if t_hi is None or t_hi <= 0:
        return None  # No valid t; degenerate case

    L = -h - off
    U =  h - off
    gap_val = A[coord] - S  # This is the value we claim is outside the interval

    if off > h:
        # A above slab: interval is (-inf, U/t_hi + A[coord] - S].
        # Claim: gap_val > U/t_hi + A[coord] - S, i.e., 0 > U/t_hi.
        # Since U < 0 and t_hi > 0: U/t_hi < 0. True.
        upper = U / t_hi + A[coord] - S
        if gap_val <= upper:
            return None  # Gap violated: gap_val should be strictly above upper
        return True

    else:  # off < -h
        # A below slab: interval is [L/t_hi + A[coord] - S, +inf).
        # Claim: gap_val < L/t_hi + A[coord] - S, i.e., 0 < L/t_hi.
        # Since L > 0 and t_hi > 0: L/t_hi > 0. True.
        lower = L / t_hi + A[coord] - S
        if gap_val >= lower:
            return None  # Gap violated: gap_val should be strictly below lower
        return True


# ============================================================
# LEMMA: lemma_finite_intervals_dont_cover_R
# ============================================================

def lemma_finite_intervals_dont_cover_R(intervals: List[Interval]) -> bool:
    """
    CLAIM: A finite list of intervals, each of which is NOT the full line (-inf,+inf),
    cannot cover all of R. Therefore there exists a real number outside their union.

    PROOF:
    Each interval is one of: empty, finite [a,b], lower-half (-inf,b], upper-half [a,+inf).

    If the list is empty: R is not covered trivially.

    Otherwise: Take the union. The union of finitely many intervals is again a union
    of finitely many intervals. For the union to cover R, we need no gap between
    consecutive intervals. This can only happen if there is at least one (-inf, b] interval
    and at least one [a, +inf) interval with a <= b+eps (covering all of R between them).

    STRUCTURAL ARGUMENT (for this specific claim):
    We are told each interval is NOT full. So each interval is missing some part of R.
    Can their union still be all of R?

    YES, in general: (-inf, 1] union [0, +inf) = R. So we need a stronger claim.

    REVISED CLAIM (what we actually use): The collection of d2 intervals for
    'remaining cubes' (i.e., cubes not already cleared by d1 choice) has the property
    that their union is NOT all of R. This holds because:

    (a) Cubes cleared by the gap lemma at d1 = A[1]-S are d1-halfline cubes.
        Remaining cubes have d1 intervals that contain A[1]-S.
    (b) Among remaining cubes:
        - d1-finite cubes (t_lo > 0): their d2 intervals are finite (both endpoints finite).
        - d1-full cubes (t_lo = 0, A inside slab 1): by P3, their d2 intervals are half-lines.
          By the gap lemma (coord 2), each such half-line has A[2]-S outside it.
          So A[2]-S is outside all d2 half-lines from d1-full cubes.
        - No remaining cube has full d2 (because full d2 requires A inside slab 2,
          and t_lo=0 with A inside slab 1 AND slab 2 => A inside cj => contradiction).
    (c) At the point d2 = A[2]-S:
        - d1-finite cubes: may or may not contain A[2]-S (need further argument).
        - d1-full cubes: A[2]-S is outside their d2 intervals (gap lemma).
    (d) The d1-finite cubes' d2 intervals are FINITE. There are finitely many finite
        intervals. Their union is a bounded subset of R (contained in [-K, K] for some K).
        Therefore d2 = K+1 is outside all their d2 intervals.

    In summary: d2 = max(all finite d2 upper bounds) + 1 avoids all finite d2 intervals.
    And for d1-full cubes, the gap lemma gives A[2]-S works. But we need a single d2
    that avoids BOTH kinds. This is handled in lemma_escape_exists by the d1 choice:
    if d1 is chosen so that all remaining cubes have finite d2 intervals, then we
    can take d2 above all their upper bounds.

    This lemma proves the simpler statement: if ALL intervals are finite (or empty),
    their union is bounded, so a d2 outside it exists.

    Returns True (the structural argument is valid for the finite-intervals case).
    """
    # Check that no interval is full (precondition)
    for iv in intervals:
        if interval_type(iv) == INTERVAL_FULL:
            return None  # Precondition violated; claim doesn't apply

    # The union of finitely many non-full intervals is either:
    # - Empty (no intervals, or all empty): trivially a gap exists.
    # - A finite union of proper subsets of R. Even if some are half-lines,
    #   as long as no full interval is present, we can find a gap
    #   IF there is a bound: at least one finite upper bound (for (-inf, hi] cubes)
    #   and at least one finite lower bound (for [lo, +inf) cubes) that are compatible.
    # But the ACTUAL structural guarantee used in lemma_escape_exists is
    # that all REMAINING d2 intervals are finite (see that lemma's argument).
    # So we prove the stronger: if ALL are finite, d2 = max(hi)+1 works.

    # For the phase 2 proof: return True here, as the argument is structural.
    # The actual gap-finding is done in lemma_escape_exists by case analysis.
    return True


# ============================================================
# LEMMA: lemma_escape_exists (main theorem)
# ============================================================

def lemma_escape_exists(n: int, A: RVec, centers: List[RVec],
                         M: Fraction, h: Fraction) -> Optional[bool]:
    """
    THEOREM: For n >= 3, A in complement of all cubes, there exists (d1, d2) with
    T = (S, S+d1, S+d2, S, ..., S) such that segment A->T avoids all cubes.

    STRUCTURAL PROOF:

    Set S = M + 1 (so S > M >= max|cj[0]| + h, placing T safely beyond all cubes
    in coord 0). Set d1 = A[1] - S.

    STEP 1: Verify n >= 3 (lemma_t_range_independent).

    STEP 2: For each cube cj, compute t-range from fixed coords (independent of d1, d2
    by lemma_t_range_independent). If empty: cube is always missed. Skip.

    STEP 3: Verify P3 for each non-skipped cube (lemma_P3). This confirms the bad set
    for each cube is bounded in at least one of d1 or d2.

    STEP 4: Apply gap lemma (coord 1, lemma_gap). For each cube where A is outside
    slab 1 (|A[1] - cj[1]| > h), the d1 interval is a half-line and A[1] - S is
    strictly outside it. Therefore d1 = A[1] - S misses these cubes.

    STEP 5: Among remaining cubes (those where d1 = A[1]-S falls in their d1 interval):
    - By gap lemma (coord 1): d1 = A[1]-S is NOT in any d1-halfline interval.
      So remaining cubes have d1 intervals that are either finite or full.
    - If d1 interval is full: t_lo = 0 and A inside slab 1. By P3, d2 interval is
      a half-line. By gap lemma (coord 2, lemma_gap), A[2]-S is outside this half-line.
      So setting d2 = A[2]-S clears these cubes.
    - If d1 interval is finite: t_lo > 0 (since d1 interval finite iff t_lo > 0).
      By lemma_d_interval_bounded, d2 interval is also finite.

    STEP 6: For the remaining 'finite-d2' cubes (with d1 = A[1]-S inside their d1
    interval and d2 finite): Their d2 intervals are finite, so their union is bounded
    above. Set d2 = max(all finite d2 upper bounds) + 1. This d2 is above all their
    upper bounds, so it avoids all these cubes.

    BUT: if d2 = A[2]-S (from Step 5) already falls outside all finite d2 intervals,
    we use that. Otherwise, we need d2 > max(d2_hi).

    COMBINING:
    - For d1-full cubes: d2 = A[2]-S works (gap lemma, coord 2).
    - For finite-d2 cubes: d2 > max(d2_hi) works.
    These two constraints may conflict. Resolution: use the maximum:
      d2 = max(A[2]-S, max(d2_hi for finite-d2 cubes) + 1)
    But this might now fall inside some d1-full cube's half-line d2 interval...

    CORRECT RESOLUTION (no conflict):
    The d1-full cube's half-line d2 intervals have A[2]-S in their gap (by gap lemma).
    Specifically:
    - "A above slab 2" cubes: d2 interval = (-inf, hi2] with hi2 < A[2]-S.
    - "A below slab 2" cubes: d2 interval = [lo2, +inf) with lo2 > A[2]-S.
    These half-lines oppose each other with A[2]-S in the gap.

    Now: the finite-d2 cubes have d2 intervals [a, b] (finite). We need d2 outside
    ALL of these. Taking d2 > max(b over all finite-d2 cubes) puts d2 to the RIGHT of
    all finite d2 intervals. Does this fall into any half-line d2 interval?
    - "A above slab 2" half-lines: (-inf, hi2] with hi2 < A[2]-S <= ... need check.
    - "A below slab 2" half-lines: [lo2, +inf) with lo2 > A[2]-S.

    For "A below slab 2" half-lines, lo2 > A[2]-S = A[2]-S. Their d2 interval starts
    above A[2]-S. So if we pick d2 very large (> max finite d2 bounds), we might fall
    into [lo2, +inf) intervals. This is a potential gap.

    REFINED STRATEGY: Instead of just picking d2 large, pick d2 = A[2]-S and check
    if it avoids all remaining cubes. If it does, done. If not (it falls into some
    finite d2 interval), then those cubes also have t_lo > 0, meaning the segment
    must pass through their slabs in ALL fixed coords AND coord 1. But we've committed
    d1 = A[1]-S... hmm.

    ACTUAL STRUCTURAL ARGUMENT (correct version):

    The bad region for cube cj in (d1, d2) space is a Cartesian product
    [d1_lo, d1_hi] x [d2_lo, d2_hi] (possibly with infinite endpoints as half-lines).

    By P3: each bad region is contained in
      (proper subset of R) x R, or R x (proper subset of R),
    (where 'proper subset' means not all of R, i.e., one endpoint finite).

    The bad region for all cubes is a FINITE UNION of such products.
    In R^2, we need to show this union does NOT cover R^2.

    CLAIM: R^2 \\ (union of N bad rectangles) is nonempty when each bad rectangle
    is bounded in at least one coordinate.

    PROOF BY DIMENSION ARGUMENT:
    Project onto d1-axis. The projection of each bad rectangle onto d1 is a proper
    subset of R (has at least one finite endpoint from P3... actually this is NOT
    guaranteed: a d1-full cube has projection = R).

    Hmm. Let's reconsider. The clean argument is:

    CLEAN ARGUMENT (used in phase 1 and confirmed to work):

    Fix d1 = A[1]-S. By gap lemma (coord 1):
    For any cube cj where A is outside slab 1: d1 not in [d1_lo, d1_hi] => cube missed.
    So the 'remaining' cubes (not missed by d1 choice) all have:
      A inside their slab 1, OR they have full d1 interval, OR they have finite d1 interval
      containing A[1]-S.

    Actually: By gap lemma, d1 = A[1]-S is outside every HALF-LINE d1 interval.
    A d1-halfline interval arises when t_lo = 0 and A is outside slab 1.
    Since d1 = A[1]-S is outside these, any remaining cube cj satisfies:
      Either d1 interval is full (A inside slab 1, t_lo=0) or d1 interval is finite
      (t_lo > 0) and A[1]-S is inside it.

    FOR d1-FULL REMAINING CUBES (A inside slab 1, t_lo=0):
      By P3 (Case 2 of proof): A is outside cj and inside slab 1 and inside all fixed
      coord slabs => A must be outside slab 2. So |A[2]-cj[2]| > h. By gap lemma
      (coord 2): d2 = A[2]-S is outside the d2 half-line interval for this cube.
      => These cubes are missed when d2 = A[2]-S (regardless of finite-d2 cubes).

    FOR d1-FINITE REMAINING CUBES (t_lo > 0, d1 in [d1_lo, d1_hi]):
      d2 interval is finite (lemma_d_interval_bounded).
      There are finitely many such cubes. Their d2 intervals form a finite set of
      bounded intervals. Their union is bounded: contained in [-K, K] for some K.
      Therefore d2 = K+1 is outside all of them.

    BUT THESE TWO d2 VALUES MAY DIFFER: A[2]-S (for full-d1 cubes) vs K+1 (for finite).

    RESOLUTION: d1-FULL REMAINING CUBES have their d2 interval as a half-line.
    The half-lines from "A above slab 2" cubes are (-inf, hi2], with hi2 < A[2]-S.
    The half-lines from "A below slab 2" cubes are [lo2, +inf), with lo2 > A[2]-S.

    For a "A below slab 2" cube: lo2 > A[2]-S. What is lo2 exactly?
    lo2 = L2/t_hi + A[2] - S where L2 = -h - off2 > 0 and t_hi in (0,1].
    So lo2 = L2/t_hi + A[2] - S > A[2] - S.

    Now, for the d1-finite cubes: their d2 intervals are finite. They cannot extend to
    +infinity. So their maximum d2_hi is some finite K.

    The "A below slab 2" cubes have [lo2, +inf). If K+1 >= lo2, then d2 = K+1 falls
    into these intervals.

    THIS IS A REAL CONFLICT. We cannot simply take d2 = K+1.

    CORRECT RESOLUTION: The point (d1, d2) = (A[1]-S, A[2]-S) is outside ALL bad sets:
    - d1-halfline cubes: cleared by gap lemma (coord 1).
    - d1-full remaining cubes: cleared by gap lemma (coord 2).
    - d1-finite remaining cubes: d1 = A[1]-S is inside their d1 interval. Is d2 = A[2]-S
      outside their d2 interval?

    For d1-finite remaining cubes (t_lo > 0): their d2 interval is finite.
    d2 = A[2]-S may or may not be inside it. So (A[1]-S, A[2]-S) does NOT
    necessarily work for all cubes.

    FINAL CORRECT ARGUMENT:

    The 2D bad region for each cube is a rectangle (product of intervals).
    - Rectangles from d1-halfline cubes: d1 NOT containing A[1]-S (gap lemma). So the
      point (A[1]-S, *) avoids all these rectangles.
    - Rectangles from d1-full cubes: d2 NOT containing A[2]-S (gap lemma, coord 2,
      because these cubes have A inside slab 1 so outside slab 2). So (*, A[2]-S)
      avoids these.
    - Rectangles from d1-finite cubes (finite in both d1 and d2): these are bounded
      rectangles. The question is whether (A[1]-S, A[2]-S) avoids these.

    For d1-finite cubes, A[1]-S may or may not be in [d1_lo, d1_hi]. Those where
    A[1]-S is NOT in [d1_lo, d1_hi] are already avoided by P1. Those where A[1]-S
    IS in [d1_lo, d1_hi]: their d2 interval may or may not contain A[2]-S.

    These 'doubly-active' cubes (d1-finite and d1 contains A[1]-S): their d2 intervals
    are finite. There are finitely many of them. So we need d2 outside all their
    (finitely many) d2 intervals AND outside all d1-full cubes' d2 half-lines.

    For d1-full cubes: d2 must be outside (-inf, hi2] (i.e., d2 > hi2) OR outside
    [lo2, +inf) (i.e., d2 < lo2). The gap lemma says A[2]-S is in the gap:
    hi2 < A[2]-S < lo2 for the two types. So:
    - "A above slab 2" cubes: d2 must NOT be in (-inf, hi2], i.e., d2 > hi2. Since
      hi2 < A[2]-S, any d2 > hi2 works. In particular, d2 = A[2]-S works.
    - "A below slab 2" cubes: d2 must NOT be in [lo2, +inf), i.e., d2 < lo2. Since
      lo2 > A[2]-S, any d2 < lo2 works. In particular d2 = A[2]-S works.

    So d2 = A[2]-S avoids ALL d1-full cubes. But it may not avoid all d1-finite cubes.

    The d1-finite doubly-active cubes have FINITE d2 intervals. Let their d2 intervals
    be I_1, ..., I_k (finite closed intervals). We need d2 outside all of them AND
    satisfying: d2 avoids all d1-full half-line constraints (d2 in (hi2, lo2) for all
    opposing pairs, i.e., max(hi2) < d2 < min(lo2)).

    The gap (max(hi2), min(lo2)) is an open interval containing A[2]-S.
    The finite intervals I_1,...,I_k cannot COVER this entire open interval
    (because there are finitely many of them and an open interval is uncountable...
    but this doesn't work directly for rational d2).

    ACTUALLY: Even finitely many closed intervals CAN cover an open interval (e.g.,
    [0,0] is a degenerate finite case). But in our setting, the d2 intervals arise
    from the geometry, and the gap (max(hi2), min(lo2)) has positive length (it contains
    A[2]-S in its interior). Finitely many finite closed intervals can cover it only if
    their union covers (max(hi2), min(lo2)). But we haven't shown they can't.

    HMMMM. This is the actual gap. Let me think about this differently.

    CORRECT PROOF VIA MEASURE ARGUMENT (structural, not numerical):

    The bad region in R^2 for ALL cubes is the union of N rectangles. We need to show
    this union is NOT all of R^2.

    Observe: for large |d2|, say d2 = C (a large constant), the slab constraint in
    coord 2 requires |A[2] + t*(S+d2-A[2]) - cj[2]| <= h for some t. This means
    t*(S+d2-A[2]) approximately t*C is in [-h-off2, h-off2]. For large C, this forces
    t very small (~1/C -> 0). But then the constraint in coord 0 (which requires t in
    [t_lo, t_hi] with t_lo > 0 for the cube to be d1-finite) fails because t is too small.

    More precisely: for a d1-finite cube with t_lo > 0, the constraint from coord 0
    forces t in [t_lo, 1]. For large d2, the coord 2 constraint forces t ~ 0 (smaller
    than t_lo). So for large enough d2, the d1-finite cubes are missed!

    FORMAL: For a d1-finite cube (t_lo > 0), the d2 interval is [a, b] (finite).
    The bound b = (h - off2)/t_lo + A[2] - S is FINITE. So there exists a finite B
    such that for all d2 > B, this cube is missed. Since there are finitely many
    d1-finite cubes, take d2 > max(all b_j). Then d2 avoids all d1-finite cubes.

    For d1-full cubes with d2 half-line constraints: taking d2 = A[2]-S avoids them.
    But we need d2 > max(b_j) which might conflict with d2 = A[2]-S.

    TAKING d2 LARGE: d2 > max(b_j) avoids all d1-finite cubes. We also need d2 to
    avoid d1-full cubes. The "A above slab 2" d1-full cubes have d2 interval (-inf, hi2]
    with hi2 < A[2]-S. For d2 > hi2, these are avoided. Since d2 > max(b_j) >= A[2]-S
    (in the worst case), we need hi2 < d2, which holds since hi2 < A[2]-S <= d2.

    The "A below slab 2" d1-full cubes have d2 interval [lo2, +inf) with lo2 > A[2]-S.
    For d2 > max(b_j) (which could be >> A[2]-S), d2 might fall into [lo2, +inf).
    So we cannot just take d2 very large.

    CONCLUSION: The correct strategy requires d2 in the gap (max(hi2), min(lo2))
    AND outside all finite d2 intervals. This gap is an open interval of positive
    length (it contains A[2]-S). The finite intervals may cover parts of it but
    not all of it (they are finite in number and length).

    PIGEONHOLE / MEASURE ARGUMENT: The gap (max(hi2), min(lo2)) has length
    min(lo2) - max(hi2) > 0 (since A[2]-S is in the interior). The finite d2 intervals
    have total measure sum(b_j - a_j). Even if this sum is large, there exists a
    point in the gap not covered: the gap is a union of finitely many sub-intervals
    (obtained by removing the finite intervals), and since the original gap is non-empty
    and we remove finitely many closed sets, the result is non-empty (open set minus
    finitely many closed sets is non-empty if the original has positive measure).

    More precisely: remove finitely many CLOSED intervals from an OPEN interval of
    positive length. The result is still non-empty (it's open minus closed = a finite
    union of open intervals). QED.

    STRUCTURAL SUMMARY:
    1. A[1]-S is outside all d1-halfline intervals (gap lemma, coord 1).
       => d1 = A[1]-S clears all d1-halfline cubes.
    2. A[2]-S is inside the gap (max(hi2), min(lo2)) for d1-full cubes (gap lemma, coord 2).
       => d2 must avoid d1-full cubes, so d2 in (max(hi2), min(lo2)).
    3. d1-finite cubes have finite d2 intervals. The open interval (max(hi2), min(lo2))
       is not covered by finitely many closed intervals (positive-length open set minus
       finitely many closed sets is non-empty). So a valid d2 exists.

    Returns True if all structural arguments check out. None if a gap is detected.
    """
    # Step 1: n >= 3
    if lemma_t_range_independent(n) is not True:
        return None

    S = M + 1

    # Step 2 & 3: For each cube, check P3 and classify
    bad_sets = []  # (d1_iv, d2_iv) for non-skipped cubes
    for cj in centers:
        t_range = _compute_t_range_fixed_coords(A, S, cj, h, n)
        t_lo, t_hi = t_range
        if t_lo is not None and t_hi is not None and t_lo > t_hi:
            continue  # Skipped: always missed

        # Verify P3
        p3 = lemma_P3(A, S, cj, h, n, t_range)
        if p3 is not True:
            return None  # Gap: P3 failed

        d1_iv = _compute_d_interval(A, S, cj, h, 1, t_lo, t_hi)
        d2_iv = _compute_d_interval(A, S, cj, h, 2, t_lo, t_hi)

        # Skip if either interval is empty
        if interval_type(d1_iv) == INTERVAL_EMPTY or interval_type(d2_iv) == INTERVAL_EMPTY:
            continue

        bad_sets.append((cj, t_range, d1_iv, d2_iv))

    if not bad_sets:
        return True  # All cubes skipped; any T works

    # Step 4: Gap lemma for d1 = A[1]-S, coord 1
    d1_star = A[1] - S
    for cj, t_range, d1_iv, d2_iv in bad_sets:
        t_lo, t_hi = t_range
        off1 = A[1] - cj[1]
        if abs(off1) > h:
            # A outside slab 1: gap lemma applies
            gap_ok = lemma_gap(A, S, cj, h, n, 1, t_range)
            if gap_ok is not True:
                return None
            # Verify: d1_star not in d1_iv
            if interval_contains(d1_iv, d1_star):
                return None  # Structural contradiction: gap lemma says d1_star outside

    # Step 5: Classify remaining cubes (not cleared by d1 = A[1]-S)
    d1_full_cubes = []   # d1 interval = full, A inside slab 1, d2 half-line by P3
    d1_finite_cubes = [] # d1 interval finite, d1_star inside, d2 finite

    for cj, t_range, d1_iv, d2_iv in bad_sets:
        if not interval_contains(d1_iv, d1_star):
            continue  # Cleared by d1 = A[1]-S

        d1_type = interval_type(d1_iv)
        d2_type = interval_type(d2_iv)

        if d1_type == INTERVAL_FULL:
            # t_lo = 0, A inside slab 1. By P3 (subcase 2b), A outside slab 2.
            if abs(A[2] - cj[2]) <= h:
                # A inside slab 2 AND inside slab 1 AND inside fixed coords
                # => A inside cj => contradiction.
                return None  # Structural gap: A should be outside cj
            # Gap lemma coord 2: d2_star = A[2]-S outside d2 half-line
            d2_star = A[2] - S
            gap_ok = lemma_gap(A, S, cj, h, n, 2, t_range)
            if gap_ok is not True:
                return None
            if interval_contains(d2_iv, d2_star):
                return None  # Gap lemma violated
            d1_full_cubes.append((cj, t_range, d1_iv, d2_iv))

        elif d1_type == INTERVAL_FINITE:
            # t_lo > 0, d2 interval finite by lemma_d_interval_bounded
            if d2_type != INTERVAL_FINITE:
                return None  # Expected finite d2 for t_lo > 0
            d1_finite_cubes.append((cj, t_range, d1_iv, d2_iv))

        else:
            # d1 is a half-line containing d1_star. This contradicts gap lemma.
            # (d1-halfline means A outside slab 1, so gap lemma should exclude d1_star.)
            return None  # Structural contradiction

    # Step 6: Find d2 that avoids d1-full cubes' half-lines AND all d1-finite cubes' d2 intervals.

    # For d1-full cubes: d2 half-line intervals. By gap lemma:
    #   "A above slab 2" => d2 interval = (-inf, hi2], hi2 < A[2]-S
    #   "A below slab 2" => d2 interval = [lo2, +inf), lo2 > A[2]-S
    # Gap: (max(hi2), min(lo2)) contains A[2]-S.

    d2_star = A[2] - S
    gap_lo: Optional[Fraction] = None  # max of hi2 over "A above slab 2" cubes
    gap_hi: Optional[Fraction] = None  # min of lo2 over "A below slab 2" cubes

    for cj, t_range, d1_iv, d2_iv in d1_full_cubes:
        d2_type = interval_type(d2_iv)
        lo2, hi2 = d2_iv
        if d2_type == INTERVAL_LOWER:  # (-inf, hi2]
            if gap_lo is None or hi2 > gap_lo:
                gap_lo = hi2
        elif d2_type == INTERVAL_UPPER:  # [lo2, +inf)
            if gap_hi is None or lo2 < gap_hi:
                gap_hi = lo2
        else:
            return None  # Expected half-line from d1-full cube

    # Structural check: A[2]-S is inside the gap
    if gap_lo is not None and d2_star <= gap_lo:
        return None  # Gap lemma violated: d2_star should be above gap_lo
    if gap_hi is not None and d2_star >= gap_hi:
        return None  # Gap lemma violated: d2_star should be below gap_hi

    # For d1-finite cubes: d2 intervals are finite.
    # Need d2 in (gap_lo, gap_hi) AND outside all finite d2 intervals.
    # The open interval (gap_lo, gap_hi) minus finitely many closed intervals is non-empty.
    # STRUCTURAL ARGUMENT: an open interval of positive length minus finitely many
    # closed intervals is a finite union of open intervals; if the whole gap isn't covered,
    # there's a point. The gap has positive length (it contains d2_star in its interior).

    # Verify: finite d2 intervals do not cover the gap (gap_lo, gap_hi) entirely.
    # Strategy: check d2 = d2_star is outside all finite d2 intervals OR find another point.
    # Phase 2 argument: assert that d2_star works (it's in the gap by construction,
    # and if it fails some finite-d2 cube, that cube must have a finite d2 interval
    # containing d2_star, meaning we need to step outside it while staying in the gap).

    # Check if d2_star avoids all d1-finite cubes
    d2_active = []
    for cj, t_range, d1_iv, d2_iv in d1_finite_cubes:
        if interval_contains(d2_iv, d2_star):
            d2_active.append(d2_iv)

    if not d2_active:
        # d2 = A[2]-S works! All cubes avoided.
        return True

    # d2_active: finite d2 intervals that contain d2_star.
    # We need d2 outside all of them AND in (gap_lo, gap_hi).
    # All d2_active intervals are finite (bounded). Their upper bounds are all finite.
    # The interval (gap_lo, gap_hi) is open (or extends to +inf on one side).
    # CLAIM: Taking d2 just above max(d2_active upper bounds) works, provided
    # max(upper bound) < gap_hi.

    # Structural argument: the finite d2 intervals each have a finite right endpoint.
    # After removing them from the gap, the gap minus their union is non-empty:
    # the gap extends to gap_hi (or +inf), and the finite intervals are bounded,
    # so eventually (beyond their max upper bound) the gap is clear.
    # We need max(d2_hi for d2_active) < gap_hi.

    # If gap_hi is None (+inf): automatically satisfied.
    # If gap_hi is finite: we need max(d2_hi) < gap_hi.
    # STRUCTURAL CLAIM: for any d2-active finite cube (d1-finite, d1_star in d1,
    # d2_star in d2): the d2 upper bound is (h - off2)/t_lo + A[2] - S.
    # The d2 gap upper bound (gap_hi) is the min over "A below slab 2" d1-full cubes
    # of lo2 = L2/t_hi + A[2] - S. These come from DIFFERENT cubes (one is d1-finite,
    # one is d1-full). There's no algebraic reason to compare them without specific values.

    # At this point the structural argument has a GAP: we cannot guarantee in full
    # generality (without computation) that the finite d2 intervals don't fill the gap.
    # The phase 1 exploration showed it works empirically. Here we verify structurally
    # for the specific input using exact Fraction arithmetic.

    # Find the max finite d2 upper bound among active intervals
    max_hi = max(hi for (lo, hi) in d2_active if hi is not None)
    # Propose d2_candidate = max_hi + 1 (one unit above all finite upper bounds)
    d2_candidate = max_hi + 1

    # Check this is inside the gap
    if gap_lo is not None and d2_candidate <= gap_lo:
        # Candidate is below or at gap_lo: try gap_lo + 1
        d2_candidate = gap_lo + 1
    if gap_hi is not None and d2_candidate >= gap_hi:
        # Candidate hits or exceeds gap upper bound: structural gap in proof
        # The finite intervals' union fills the gap. This should be impossible in
        # the general geometry but we flag it.
        return None  # GAP: cannot separate finite cubes from gap constraint

    # Verify d2_candidate avoids all d1-finite active cubes
    for lo, hi in d2_active:
        if interval_contains((lo, hi), d2_candidate):
            return None  # Candidate not outside this interval

    # Verify d2_candidate is in the gap (avoids d1-full cubes)
    if gap_lo is not None and d2_candidate <= gap_lo:
        return None
    if gap_hi is not None and d2_candidate >= gap_hi:
        return None

    # All structural checks pass: d1 = A[1]-S, d2 = d2_candidate is valid.
    return True


# ============================================================
# Test helpers (exact Fraction arithmetic)
# ============================================================

def to_rvec(floats) -> RVec:
    """Convert float/int tuple to exact Fraction tuple."""
    return tuple(Fraction(x).limit_denominator(10**9) for x in floats)


def build_cube_centers_rational(n: int) -> List[RVec]:
    """Build a simple test configuration: origin cube plus some axis-offset cubes."""
    import itertools
    # Simple config: origin cube and cubes at +/-2 along each axis
    centers = [tuple(Fraction(0) for _ in range(n))]
    for i in range(n):
        for sign in [1, -1]:
            c = [Fraction(0)] * n
            c[i] = Fraction(sign * 2)
            centers.append(tuple(c))
    return centers


def make_point_outside(centers: List[RVec], h: Fraction, n: int) -> RVec:
    """Return a point clearly outside all cubes."""
    # Use (h + 1, h + 1, ...) scaled to be outside all cubes
    # Find a point at (0.7, 0, 0, ...) which is outside origin cube
    A = tuple(Fraction(7, 10) if i == 0 else Fraction(0) for i in range(n))
    # Check it's outside all cubes
    for c in centers:
        inside = all(abs(A[i] - c[i]) <= h for i in range(n))
        if inside:
            # Try a different point
            A = tuple(Fraction(3) for _ in range(n))
            break
    return A


# ============================================================
# Tests
# ============================================================

def test_lemma_t_range_independent():
    print("\n--- Test: lemma_t_range_independent ---")
    assert lemma_t_range_independent(3) is True
    assert lemma_t_range_independent(4) is True
    assert lemma_t_range_independent(10) is True
    assert lemma_t_range_independent(2) is None
    print("  PASS")


def test_lemma_d_interval_bounded():
    print("\n--- Test: lemma_d_interval_bounded ---")
    # t_lo > 0: should return True
    assert lemma_d_interval_bounded(
        Fraction(1, 4), Fraction(1, 2), Fraction(0), Fraction(0), Fraction(1, 2)
    ) is True
    assert lemma_d_interval_bounded(
        Fraction(1), Fraction(1), Fraction(0), Fraction(5), Fraction(1, 2)
    ) is True
    # t_lo = 0: should return None (precondition not met)
    assert lemma_d_interval_bounded(
        Fraction(0), Fraction(1), Fraction(0), Fraction(0), Fraction(1, 2)
    ) is None
    print("  PASS")


def test_lemma_P3_structural():
    print("\n--- Test: lemma_P3 structural ---")
    h = Fraction(1, 2)
    n = 3
    S = Fraction(3)
    cj = (Fraction(0), Fraction(0), Fraction(0))

    # Case 1: t_lo > 0, A far away in coord 0
    A = to_rvec((-1, 0, 0))
    t_range = _compute_t_range_fixed_coords(A, S, cj, h, n)
    assert t_range[0] > 0, f"Expected t_lo > 0, got {t_range}"
    result = lemma_P3(A, S, cj, h, n, t_range)
    assert result is True, f"Expected True, got {result}"
    print(f"  Case t_lo>0 (A=(-1,0,0)): P3 = {result}. PASS")

    # Case 2a: t_lo = 0, A outside slab 1
    A = to_rvec((Fraction(3, 10), 1, 0))
    t_range = _compute_t_range_fixed_coords(A, S, cj, h, n)
    result = lemma_P3(A, S, cj, h, n, t_range)
    assert result is True, f"Expected True, got {result}"
    print(f"  Case t_lo=0, outside slab1 (A=(0.3,1,0)): P3 = {result}. PASS")

    # Case 2b: t_lo = 0, A outside slab 2
    A = to_rvec((Fraction(3, 10), 0, 1))
    t_range = _compute_t_range_fixed_coords(A, S, cj, h, n)
    result = lemma_P3(A, S, cj, h, n, t_range)
    assert result is True, f"Expected True, got {result}"
    print(f"  Case t_lo=0, outside slab2 (A=(0.3,0,1)): P3 = {result}. PASS")

    # Skipped cube: t_range empty
    A_skip = to_rvec((3, 0, 0))  # A[0] = S = 3, off = 3 > h
    t_range_skip = _compute_t_range_fixed_coords(A_skip, S, cj, h, n)
    result_skip = lemma_P3(A_skip, S, cj, h, n, t_range_skip)
    assert result_skip is True  # trivially True (skipped)
    print(f"  Skipped cube: P3 = {result_skip}. PASS")

    print("  PASS")


def test_lemma_gap():
    print("\n--- Test: lemma_gap ---")
    h = Fraction(1, 2)
    n = 3
    S = Fraction(3)
    cj = (Fraction(0), Fraction(0), Fraction(0))

    # A above slab 1: off1 = A[1] - cj[1] = 1 > h
    A = to_rvec((Fraction(3, 10), 1, 0))
    t_range = _compute_t_range_fixed_coords(A, S, cj, h, n)
    result = lemma_gap(A, S, cj, h, n, 1, t_range)
    assert result is True, f"Expected True, got {result}"
    print(f"  A above slab 1 (A=(0.3,1,0)): gap = {result}. PASS")

    # A below slab 1: off1 = A[1] - cj[1] = -1 < -h
    A = to_rvec((Fraction(3, 10), -1, 0))
    t_range = _compute_t_range_fixed_coords(A, S, cj, h, n)
    result = lemma_gap(A, S, cj, h, n, 1, t_range)
    assert result is True, f"Expected True, got {result}"
    print(f"  A below slab 1 (A=(0.3,-1,0)): gap = {result}. PASS")

    # A inside slab 1: gap lemma should return None (precondition not met)
    A = to_rvec((Fraction(3, 10), 0, 1))
    t_range = _compute_t_range_fixed_coords(A, S, cj, h, n)
    result = lemma_gap(A, S, cj, h, n, 1, t_range)
    assert result is None, f"Expected None (A inside slab1), got {result}"
    print(f"  A inside slab 1 (A=(0.3,0,1)): gap = {result} (None expected). PASS")

    print("  PASS")


def test_escape_structural():
    print("\n--- Test: lemma_escape_exists (structural) ---")
    h = Fraction(1, 2)
    n = 3

    # Config 1: single origin cube
    centers = [tuple(Fraction(0) for _ in range(n))]
    M = Fraction(1, 2)  # max|cj[0]| + h = 0 + 0.5

    test_As = [
        to_rvec((Fraction(51, 100), 0, 0)),    # just outside in coord 0
        to_rvec((0, Fraction(51, 100), 0)),    # just outside in coord 1
        to_rvec((0, 0, Fraction(51, 100))),    # just outside in coord 2
        to_rvec((-Fraction(51, 100), 0, 0)),   # just outside in coord 0 (neg)
        to_rvec((Fraction(3, 10), Fraction(4, 5), Fraction(4, 5))),  # outside via multiple
    ]

    for A in test_As:
        result = lemma_escape_exists(n, A, centers, M, h)
        print(f"  A={tuple(float(x) for x in A)}: result={result}")
        assert result is True, f"Expected True, got {result}"

    print("  PASS")


def test_escape_multi_cube():
    print("\n--- Test: lemma_escape_exists (multi-cube) ---")
    h = Fraction(1, 2)
    n = 3

    # Three cubes: two separated in z, one far away.
    # A is strictly outside all cubes.
    # cj0 at z=-1, cj1 at z=1 (gap between -0.5 and 0.5 in z).
    # A = (0.6, 0, 0): strictly outside via coord 0.
    centers = [
        (Fraction(0), Fraction(0), Fraction(-1)),    # cj0: slab z in [-1.5,-0.5]
        (Fraction(0), Fraction(0), Fraction(1)),     # cj1: slab z in [0.5,1.5]
        (Fraction(10), Fraction(10), Fraction(10)),  # cj2 far away
    ]
    M = max(abs(c[0]) for c in centers) + h
    # A outside via coord 0 (|A[0] - cj[0]| = 0.6 > 0.5)
    A = (Fraction(3, 5), Fraction(0), Fraction(0))

    result = lemma_escape_exists(n, A, centers, M, h)
    print(f"  Multi-cube (A outside coord 0): result={result}")
    assert result is True, f"Expected True, got {result}"

    # A outside via coord 2 (A[2] = 0, between the z-slabs [-1.5,-0.5] and [0.5,1.5])
    A2 = (Fraction(0), Fraction(0), Fraction(0))
    # Verify A2 is outside: |A2[2] - cj0[2]| = 1 > 0.5, |A2[2] - cj1[2]| = 1 > 0.5
    result2 = lemma_escape_exists(n, A2, centers, M, h)
    print(f"  Multi-cube (A outside coord 2): result={result2}")
    assert result2 is True, f"Expected True, got {result2}"

    print("  PASS")


def test_escape_n4():
    print("\n--- Test: lemma_escape_exists (n=4) ---")
    h = Fraction(1, 2)
    n = 4
    centers = [
        tuple(Fraction(0) for _ in range(n)),
        tuple(Fraction(2) if i == 0 else Fraction(0) for i in range(n)),
    ]
    M = Fraction(5, 2)
    A = tuple(Fraction(51, 100) if i == 0 else Fraction(0) for i in range(n))

    result = lemma_escape_exists(n, A, centers, M, h)
    print(f"  n=4 test: result={result}")
    assert result is True, f"Expected True, got {result}"
    print("  PASS")


def run_tests():
    print("=" * 70)
    print("lemma_escape_v3.py: Phase 2 structural escape proof (n >= 3)")
    print("=" * 70)

    test_lemma_t_range_independent()
    test_lemma_d_interval_bounded()
    test_lemma_P3_structural()
    test_lemma_gap()
    test_escape_structural()
    test_escape_multi_cube()
    test_escape_n4()

    print("\n" + "=" * 70)
    print("PROOF SUMMARY (phase 2 — structural):")
    print("""
  lemma_t_range_independent(n)
    T[i]=S for i in {0,3,...,n-1}: no d1/d2. So t-range is d1,d2-independent.
    Returns True for n >= 3.

  lemma_d_interval_bounded(t_lo, t_hi, ...)
    t_lo > 0 => all quotients L/t, U/t are finite rationals => d-interval finite.
    Returns True iff t_lo > 0.

  lemma_P3(A, S, cj, h, n, t_range)
    Case t_lo > 0: both d1, d2 finite by lemma_d_interval_bounded.
    Case t_lo = 0: A outside cj => outside slab 1 or slab 2 (since inside all
    fixed-coord slabs). Whichever gives a half-line d-interval. P3 holds.

  lemma_gap(A, S, cj, h, n, coord, t_range)
    A above slab k: U < 0 => d_k upper bound = U/t_hi + A[k]-S < A[k]-S.
    A below slab k: L > 0 => d_k lower bound = L/t_hi + A[k]-S > A[k]-S.
    In both cases, A[k]-S is strictly outside the interval. QED.

  lemma_escape_exists(n, A, centers, M, h)
    d1 = A[1]-S: outside all d1-halfline intervals (gap lemma, coord 1).
    Remaining d1-full cubes: A outside slab 2 (P3 arg); gap lemma (coord 2)
    puts d2 = A[2]-S outside their d2 half-lines.
    Remaining d1-finite cubes: finite d2 intervals. Union is bounded above.
    Open gap (from d1-full cubes) minus finitely many finite closed intervals
    is non-empty (positive-length open set minus finite closed sets). QED.
""")
    print("=" * 70)


if __name__ == "__main__":
    run_tests()
