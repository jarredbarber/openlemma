import Mathlib.Computability.Encoding
import Mathlib.Data.Nat.Size

open Computability

example (n : ℕ) : (finEncodingNatBool.encode n).length = n.size := by
  -- dsimp [finEncodingNatBool, encodingNatBool]
  -- rw [Nat.size_eq_bits_len] -- If this exists
  sorry
