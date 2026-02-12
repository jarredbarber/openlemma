# Mathlib Audit: Exact Cover and Set Partition

This audit identifies existing Mathlib structures that can be used to formalize **Exact Cover**, **Set Partition**, and **Hitting Set** problems.

## 1. Set Partition

While there is no file named `Mathlib.Combinatorics.SetPartition`, the functionality is primarily located in `Mathlib.Data.Setoid.Partition` and `Mathlib.Order.Partition.Finpartition`.

### Key Definitions:
*   **`Setoid.IsPartition (c : Set (Set α))`**: A collection of sets is a partition of `α` if `∅ ∉ c` and every element of `α` belongs to exactly one set in `c`.
    *   *Path:* `Mathlib/Data/Setoid/Partition.lean`
*   **`Setoid.IndexedPartition (s : ι → Set α)`**: A partition of `α` indexed by `ι`. It includes constructive information like `index : α → ι` and `some : ι → α`.
    *   *Path:* `Mathlib/Data/Setoid/Partition.lean`
*   **`Finpartition (a : α)`**: For a complete lattice `α` (like `Finset V`), a `Finpartition` is a bundled structure for a finite set of pairwise disjoint parts whose supremum is `a`.
    *   *Path:* `Mathlib/Order/Partition/Finpartition.lean`

## 2. Exact Cover

There is no explicit "Exact Cover Problem" definition in Mathlib. However, it can be expressed directly using the partition definitions above.

**Formalization Strategy:**
Given a universe `U` and a collection of subsets `S : Finset (Finset U)`, a subset `S' ⊆ S` is an exact cover if:
```lean
(S' : Set (Set U)).IsPartition
```
Alternatively, for finite universes, we can use `Finpartition (Set.univ : Finset U)`.

## 3. Hitting Set (Transversal)

The concept of a "Hitting Set" is often referred to as a **Transversal** in Mathlib.

### Key Definitions:
*   **`hallMatchingsOn`**: Used in Hall's Marriage Theorem. A matching for `t : ι → Finset α` is an injective function `f : ι → α` such that `∀ i, f i ∈ t i`. This is a "System of Distinct Representatives" (SDR), which is a specific type of hitting set.
    *   *Path:* `Mathlib/Combinatorics/Hall/Basic.lean`
*   **`SimpleGraph.IsVertexCover`**: A set of vertices that hits every edge in a graph.
    *   *Path:* `Mathlib/Combinatorics/SimpleGraph/VertexCover.lean`

## Summary Table

| Problem | Mathlib Equivalent | Suggested Formalization |
| :--- | :--- | :--- |
| **Set Partition** | `Setoid.IsPartition` | Use `Setoid.IsPartition` or `Finpartition`. |
| **Exact Cover** | N/A | `∃ S' ⊆ S, Setoid.IsPartition S'` |
| **Hitting Set** | `Transversal` (SDR context) | `∀ s ∈ S, (H ∩ s).Nonempty` |
| **Set Cover** | N/A | `⋃₀ S' = U` (General cover) |

**Conclusion:** We can leverage `Setoid.IsPartition` and `Finpartition` for Phase 4. We will need to define the "problem" structures ourselves (e.g., in `botlib/Complexity/ExactCover.lean`) as they are not currently in the library.
