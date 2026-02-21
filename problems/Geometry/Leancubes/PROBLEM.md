# Leancubes: Connectedness of Cube Complement

## Statement

Let C_0 be an axis-aligned solid unit cube in R^n, n > 2. Starting at the center of C_0, project n rays through the n distinct vertices of one face. Each ray has length l_i. These rays define a parallelepiped. At each vertex of the parallelepiped, attach an axis-aligned unit cube C_i at its center. Consider the union C = ∪ C_i.

**Conjecture:** For n > 2 and any choice of lengths l_i, the complement R^n \ C is connected.

## Intuition

As we increase the distance between cubes, a hole in the center of mass eventually opens up. The claim is that any point in this hole can always escape outside of the cubes, and since the "outside" is connected, the whole complement is connected.

## Goal

1. A Lean 4 proof with no sorrys
2. A natural language proof of journal quality, following the same strategy as the Lean proof
3. Both should be as minimal as possible

## Notes

- May assume n is not a power of two if that helps
- n > 2 is essential (the conjecture is about dimension 3+)
- The cubes are axis-aligned and solid
- The parallelepiped vertices are determined by the ray lengths l_i
- Source: ~/code/leancubes/
