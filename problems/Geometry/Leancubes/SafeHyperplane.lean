/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Provenance: Proved by LLM agents (Claude, Anthropic) working on the Leancubes
connectedness problem. Zero human mathematical input.
Trust level: Compiler-verified.
-/
import Mathlib

/-!
# Safe Hyperplane Lemma

If a line segment in Rⁿ has both endpoints with coordinate k equal to S,
and |S - c k| > h for a cube center c, then the segment does not intersect
the axis-aligned cube [c - h, c + h]ⁿ.

## Main Result

* `segment_avoids_cube_if_coord_separated`: The segment from A to B avoids the
  axis-aligned cube centered at c with half-width h, provided A k = B k = S and
  |S - c k| > h.
-/

namespace OpenLemma.Leancubes

/-- An axis-aligned cube in Rⁿ centered at c with half-width h. -/
def AxisAlignedCube (n : ℕ) (c : Fin n → ℝ) (h : ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ i, |x i - c i| ≤ h}

/-- The line segment from A to B, parameterized by t ∈ [0, 1]. -/
def Segment (n : ℕ) (A B : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {x | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ ∀ i, x i = A i + t * (B i - A i)}

/-- Helper: for the segment from A to B, coordinate k at parameter t equals
    A k + t * (B k - A k). When A k = B k, this simplifies to A k. -/
lemma segment_coord_of_eq {n : ℕ} (A B : Fin n → ℝ) (k : Fin n)
    (hk : A k = B k) (t : ℝ) :
    A k + t * (B k - A k) = A k := by
  simp [hk]

/-- Main lemma: a segment whose k-th coordinate is constant at S avoids any
    axis-aligned cube whose k-th center coordinate is separated from S by more
    than h. -/
theorem segment_avoids_cube_if_coord_separated
    (n : ℕ) (A B c : Fin n → ℝ) (h : ℝ) (k : Fin n)
    (hk_eq : A k = B k)
    (hk_sep : |A k - c k| > h)
    (_hh : h ≥ 0) :
    Disjoint (Segment n A B) (AxisAlignedCube n c h) := by
  -- Show the two sets are disjoint by showing no point can be in both.
  rw [Set.disjoint_left]
  intro x hx_seg hx_cube
  -- Unpack: x is on the segment
  obtain ⟨t, ht0, ht1, hx_eq⟩ := hx_seg
  -- Unpack: x is in the cube, so in particular coordinate k is in the slab
  have hk_cube : |x k - c k| ≤ h := hx_cube k
  -- The k-th coordinate of x equals A k (since A k = B k)
  have hxk : x k = A k := by
    rw [hx_eq k, segment_coord_of_eq A B k hk_eq t]
  -- Rewrite the cube bound in terms of A k
  rw [hxk] at hk_cube
  -- But |A k - c k| > h contradicts |A k - c k| ≤ h
  linarith [abs_nonneg (A k - c k)]

end OpenLemma.Leancubes
