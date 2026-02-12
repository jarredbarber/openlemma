# Library Complexity Audit: List Encoding Operations

This audit verifies the time complexity of the primary list operations used in `botlib/Complexity/SAT.lean` for the linear-time `listEncoding`.

## Audited Operations

### 1. `List.flatMap` (used in `encode`)

**Implementation Analysis:**
In Lean 4, `List.flatMap f l` is equivalent to `(l.map f).flatten`. 
- `List.map` visits each element $x \in l$ once, applying $f(x)$.
- `List.flatten` (or the equivalent `++` chain) concatenates the resulting lists.
- For a linked list, `l1 ++ l2` takes $O(\text{length}(l1))$ time.
- Total time for `flatMap` is $O(N + M)$, where $N$ is the number of elements in the input list and $M$ is the total number of elements in the resulting list.

**Conclusion:** 
$O(N_{out})$ where $N_{out}$ is the size of the encoded representation. This is linear work relative to the output size, supporting polynomial-time soundness.

---

### 2. `List.splitOn` (from Batteries, used in `decode`)

**Implementation Analysis:**
`List.splitOn` in the `Batteries` library is implemented using a tail-recursive auxiliary function (`splitOnPTR`).
- It traverses the input list exactly once ($O(N)$ steps).
- It maintains an accumulator (as an `Array` or `List`) for the current chunk.
- When a separator is encountered, the current chunk is "finalized" (converted to a list or reversed).
- The total work performed across all finalization steps is proportional to the sum of the lengths of all chunks, which equals $N$.
- The use of `Array` and `toListAppend` in the optimized version ensures that the total work remains linear.

**Conclusion:** 
$O(N)$ where $N$ is the length of the encoded list. This is optimal for decoding.

---

### 3. Summary of `listEncoding` Complexity

| Operation | Complexity | Note |
| :--- | :--- | :--- |
| `encode` | $O(\sum |ea.encode(x)|)$ | Linear in output size. |
| `decode` | $O(N)$ | Linear in input size (excluding `ea.decode` calls). |

**Final Verdict:** The operations `List.flatMap` and `List.splitOn` are mathematically sound choices for a polynomial-time (and specifically linear-overhead) encoding of lists.
