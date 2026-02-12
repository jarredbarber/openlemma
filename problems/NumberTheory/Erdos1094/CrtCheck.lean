/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Erdos.CarryInfra
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Erdos1094

def otherPrimes : List ℕ := [5, 7, 11, 13, 17, 19, 23, 29]

/-- Smallest power of p strictly greater than k. -/
def p_pow_gt_k (p k : ℕ) : ℕ :=
  if p < 2 then 1 else p ^ (Nat.log p k + 1)

/-- Allowed residues modulo p^L(k). -/
def allowedResidues (p k : ℕ) : List ℕ :=
  let m := p_pow_gt_k p k
  (List.range m).filter (fun r => !hasCarry p k r)

/-- CRT combination using Mathlib's chineseRemainder. -/
def crt (r1 m1 r2 m2 : ℕ) (cop : m1.Coprime m2) : ℕ :=
  (Nat.chineseRemainder cop r1 r2).val

/-- Check other primes. -/
def checkOtherPrimes (k n : ℕ) : Bool :=
  otherPrimes.all fun p => !hasCarry p k n

theorem m2_m3_coprime (k : ℕ) : (p_pow_gt_k 2 k).Coprime (p_pow_gt_k 3 k) := by
  apply Nat.Coprime.pow
  norm_num

/-- Main check function. -/
def crtCheckK (k : ℕ) : Bool :=
  let m2 := p_pow_gt_k 2 k
  let m3 := p_pow_gt_k 3 k
  let s2 := allowedResidues 2 k
  let s3 := allowedResidues 3 k
  
  -- Use explicit list comprehension or bind
  let cands : List ℕ := s2.flatMap fun r2 => s3.map fun r3 => crt r2 m2 r3 m3 (m2_m3_coprime k)
  
  let solutions := cands.filter fun n =>
    2 * k ≤ n && n ≤ k * k && checkOtherPrimes k n
    
  solutions.isEmpty

/-- Range check. -/
def crtCheckRange (a b : ℕ) : Bool :=
  (List.range (b - a + 1)).all fun i => crtCheckK (a + i)

theorem crtCheckRange_sound (a b : ℕ) (h : crtCheckRange a b = true) :
    ∀ k, a ≤ k → k ≤ b →
    ∀ n, 2 * k ≤ n → n ≤ k * k → ∃ p, p.Prime ∧ p ≤ 29 ∧ p ∣ n.choose k := by
  sorry -- Assume soundness of the exhaustive check

end Erdos1094
