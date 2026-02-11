/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Provenance: Originally proved by LLM agents (Claude, Anthropic) working on
Erdős Problem 728, with zero human mathematical input.
Trust level: 🟢 Compiler-verified (zero sorrys, zero axioms).
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic

/-!
# Digit Space Definitions

Common definitions for working with base-p digit spaces as finite product types.
Used as the foundation for Chernoff-style concentration bounds over digit patterns.

## Main Definitions

* `DigitSpace D p` — the space of D-digit numbers in base p (`Fin D → Fin p`)
* `isHigh` — predicate for digits ≥ ⌈p/2⌉
* `highDigitCount` — count of high digits in a digit vector
* `probHigh` — probability that a uniformly random digit is high
-/

namespace OpenLemma.DigitSpace

section CommonDefinitions

variable {D p : ℕ}

/-- The space of D-digit numbers in base p. -/
abbrev DigitSpace (D p : ℕ) := Fin D → Fin p

/-- A digit is "high" if it is at least ⌈p/2⌉. -/
def isHigh (p : ℕ) (d : Fin p) : Prop :=
  d.val ≥ (p + 1) / 2

instance : DecidablePred (isHigh p) := fun _ => Nat.decLe _ _

/-- The number of high digits in a digit vector. -/
def highDigitCount (m : DigitSpace D p) : ℕ :=
  (Finset.univ.filter (fun i => isHigh p (m i))).card

/-- The probability that a uniformly random base-p digit is high. -/
noncomputable def probHigh (p : ℕ) : ℝ :=
  (p / 2 : ℕ) / (p : ℝ)

end CommonDefinitions

end OpenLemma.DigitSpace
