# Mathlib Lemmas: Natural Number Encoding Length

This document summarizes the lemmas and definitions relating the value of a natural number to the length of its binary encoding in `finEncodingNatBool`.

## Definitions

*   **`Computability.encodeNat n`**: The binary encoding of `n : ℕ` as a `List Bool`.
*   **`Nat.size n`**: The number of bits required to represent `n` in binary.

## Key Lemmas

### 1. Equality of Encoding Length and Size
The length of the list produced by `encodeNat` is exactly the `Nat.size`.
*   **Lemma:** `(Computability.encodeNat n).length = Nat.size n`
*   *Note:* This follows from the definitions in `Mathlib.Computability.Encoding`.

### 2. Logarithmic Bounds
*   **`Nat.size_le`**: `Nat.size m ≤ n ↔ m < 2 ^ n`
    *   This provides the standard $O(\log n)$ upper bound.
*   **`Nat.lt_size_self`**: `n < 2 ^ (Nat.size n)`
    *   Ensures that the size is sufficient to represent the number.
*   **`Nat.size_pos`**: `0 < Nat.size n ↔ 0 < n`
    *   The size is zero if and only if the number is zero.

### 3. Bit Manipulation
*   **`Nat.size_eq_bits_len`**: `n.bits.length = n.size`
    *   Relates the length of the bit list (from `Nat.bits`) to the size.
*   **`Nat.size_bit`**: `size (bit b n) = size n + 1` (for `bit b n ≠ 0`)
    *   Inductive step for bit-by-bit construction.

## Application to SAT Certificate
For a formula with $V$ variables, encoding a variable index $v < V$ takes $\lfloor \log_2 V \rfloor + 1$ bits. Thus, the total encoding length for a certificate of $V$ variables and $C$ clauses is bounded by $O(V \log V)$, which is polynomial in the input size.
