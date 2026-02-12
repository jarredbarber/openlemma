/-
PolyTimeFst: A TM2 machine that computes Prod.fst on pair-encoded inputs.
Time: O(n) where n = input length.
-/
import Mathlib.Computability.TMComputable
import Mathlib.Computability.Encoding
import botlib.Complexity.Defs

noncomputable section

namespace PolyTimeFst

open Turing Computability TM2

inductive K3 : Type where
  | input  : K3
  | buffer : K3
  | output : K3
  deriving DecidableEq, Fintype, Inhabited

inductive FstL : Type where
  | scan   : FstL
  | drain  : FstL
  | copy   : FstL
  deriving DecidableEq, Fintype, Inhabited

section
variable {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β)

private def defaultΓ [Nonempty ea.Γ] : ea.Γ := Classical.choice ‹_›

def fstTM [Nonempty ea.Γ] : FinTM2 where
  K := K3
  k₀ := K3.input
  k₁ := K3.output
  Γ := fun k => match k with
    | K3.input  => Sum ea.Γ eb.Γ
    | K3.buffer => ea.Γ
    | K3.output => ea.Γ
  Λ := FstL
  main := FstL.scan
  σ := Option ea.Γ
  initialState := none
  m := fun l => match l with
    | FstL.scan =>
      Stmt.pop K3.input (fun _ sym =>
        match sym with
        | some (Sum.inl x) => some x
        | _ => none)
        (Stmt.branch (fun s => s.isSome)
          (Stmt.push K3.buffer (fun s => s.getD (defaultΓ ea))
            (Stmt.goto (fun _ => FstL.scan)))
          (Stmt.goto (fun _ => FstL.drain)))
    | FstL.drain =>
      Stmt.pop K3.input (fun _ sym =>
        match sym with
        | some _ => some (defaultΓ ea)
        | none => none)
        (Stmt.branch (fun s => s.isSome)
          (Stmt.goto (fun _ => FstL.drain))
          (Stmt.goto (fun _ => FstL.copy)))
    | FstL.copy =>
      Stmt.pop K3.buffer (fun _ sym => sym)
        (Stmt.branch (fun s => s.isSome)
          (Stmt.push K3.output (fun s => s.getD (defaultΓ ea))
            (Stmt.goto (fun _ => FstL.copy)))
          Stmt.halt)

private def mkCfg [Nonempty ea.Γ]
    (l : Option FstL) (s : Option ea.Γ)
    (inp : List (Sum ea.Γ eb.Γ)) (buf : List ea.Γ) (out : List ea.Γ) :
    (fstTM ea eb).Cfg :=
  { l := l, var := s,
    stk := fun k => match k with
      | K3.input  => inp
      | K3.buffer => buf
      | K3.output => out }

private def oneStep [Nonempty ea.Γ]
    {c₁ c₂ : (fstTM ea eb).Cfg}
    (h : (fstTM ea eb).step c₁ = some c₂) :
    EvalsToInTime (fstTM ea eb).step c₁ (some c₂) 1 where
  steps := 1
  evals_in_steps := by
    show (flip bind (fstTM ea eb).step)^[1] (some c₁) = some c₂
    simp only [Function.iterate_one, flip, bind, Option.bind]
    exact h
  steps_le_m := le_refl 1

/-! ## Single-step lemmas -/

private theorem scan_inl [Nonempty ea.Γ] (x : ea.Γ)
    (rest : List (Sum ea.Γ eb.Γ)) (buf out : List ea.Γ) (s : Option ea.Γ) :
    (fstTM ea eb).step (mkCfg ea eb (some FstL.scan) s (Sum.inl x :: rest) buf out) =
    some (mkCfg ea eb (some FstL.scan) (some x) rest (x :: buf) out) := by
  simp only [fstTM, mkCfg, FinTM2.step, step, stepAux, List.head?]; congr 1; exact (Cfg.mk.injEq _ _ _ _ _ _).mpr ⟨rfl, rfl, funext fun k => by cases k <;> simp [Function.update]⟩

private theorem scan_inr [Nonempty ea.Γ] (y : eb.Γ)
    (rest : List (Sum ea.Γ eb.Γ)) (buf out : List ea.Γ) (s : Option ea.Γ) :
    (fstTM ea eb).step (mkCfg ea eb (some FstL.scan) s (Sum.inr y :: rest) buf out) =
    some (mkCfg ea eb (some FstL.drain) none rest buf out) := by
  simp only [fstTM, mkCfg, FinTM2.step, step, stepAux, List.head?]; congr 1; exact (Cfg.mk.injEq _ _ _ _ _ _).mpr ⟨rfl, rfl, funext fun k => by cases k <;> simp [Function.update]⟩

private theorem scan_nil [Nonempty ea.Γ] (buf out : List ea.Γ) (s : Option ea.Γ) :
    (fstTM ea eb).step (mkCfg ea eb (some FstL.scan) s [] buf out) =
    some (mkCfg ea eb (some FstL.drain) none [] buf out) := by
  simp only [fstTM, mkCfg, FinTM2.step, step, stepAux, List.head?, List.tail_nil]; congr 1; exact (Cfg.mk.injEq _ _ _ _ _ _).mpr ⟨rfl, rfl, funext fun k => by cases k <;> simp [Function.update]⟩

private theorem drain_cons_inl [Nonempty ea.Γ] (a : ea.Γ)
    (rest : List (Sum ea.Γ eb.Γ)) (buf out : List ea.Γ) (s : Option ea.Γ) :
    (fstTM ea eb).step (mkCfg ea eb (some FstL.drain) s (Sum.inl a :: rest) buf out) =
    some (mkCfg ea eb (some FstL.drain) (some (defaultΓ ea)) rest buf out) := by
  simp only [fstTM, mkCfg, FinTM2.step, step, stepAux, List.head?]; congr 1; exact (Cfg.mk.injEq _ _ _ _ _ _).mpr ⟨rfl, rfl, funext fun k => by cases k <;> simp [Function.update]⟩

private theorem drain_cons_inr [Nonempty ea.Γ] (b : eb.Γ)
    (rest : List (Sum ea.Γ eb.Γ)) (buf out : List ea.Γ) (s : Option ea.Γ) :
    (fstTM ea eb).step (mkCfg ea eb (some FstL.drain) s (Sum.inr b :: rest) buf out) =
    some (mkCfg ea eb (some FstL.drain) (some (defaultΓ ea)) rest buf out) := by
  simp only [fstTM, mkCfg, FinTM2.step, step, stepAux, List.head?]; congr 1; exact (Cfg.mk.injEq _ _ _ _ _ _).mpr ⟨rfl, rfl, funext fun k => by cases k <;> simp [Function.update]⟩

private theorem drain_nil [Nonempty ea.Γ] (buf out : List ea.Γ) (s : Option ea.Γ) :
    (fstTM ea eb).step (mkCfg ea eb (some FstL.drain) s [] buf out) =
    some (mkCfg ea eb (some FstL.copy) none [] buf out) := by
  simp only [fstTM, mkCfg, FinTM2.step, step, stepAux, List.head?, List.tail_nil]; congr 1; exact (Cfg.mk.injEq _ _ _ _ _ _).mpr ⟨rfl, rfl, funext fun k => by cases k <;> simp [Function.update]⟩

private theorem copy_cons [Nonempty ea.Γ] (x : ea.Γ)
    (rest_buf : List ea.Γ) (out : List ea.Γ) (s : Option ea.Γ) :
    (fstTM ea eb).step (mkCfg ea eb (some FstL.copy) s [] (x :: rest_buf) out) =
    some (mkCfg ea eb (some FstL.copy) (some x) [] rest_buf (x :: out)) := by
  simp only [fstTM, mkCfg, FinTM2.step, step, stepAux, List.head?]; congr 1; exact (Cfg.mk.injEq _ _ _ _ _ _).mpr ⟨rfl, rfl, funext fun k => by cases k <;> simp [Function.update]⟩

private theorem copy_nil [Nonempty ea.Γ] (out : List ea.Γ) (s : Option ea.Γ) :
    (fstTM ea eb).step (mkCfg ea eb (some FstL.copy) s [] [] out) =
    some (mkCfg ea eb none none [] [] out) := by
  simp only [fstTM, mkCfg, FinTM2.step, step, stepAux, List.head?, List.tail_nil]; congr 1; exact (Cfg.mk.injEq _ _ _ _ _ _).mpr ⟨rfl, rfl, funext fun k => by cases k <;> simp [Function.update]⟩

/-! ## Multi-step correctness -/

private def bumpTime [Nonempty ea.Γ]
    {c₁ : (fstTM ea eb).Cfg} {c₂ : Option (fstTM ea eb).Cfg} {m₁ m₂ : ℕ}
    (h : EvalsToInTime (fstTM ea eb).step c₁ c₂ m₁) (hle : m₁ ≤ m₂) :
    EvalsToInTime (fstTM ea eb).step c₁ c₂ m₂ :=
  ⟨h.toEvalsTo, le_trans h.steps_le_m hle⟩

private def drainPhase [Nonempty ea.Γ]
    (rest : List (Sum ea.Γ eb.Γ)) (buf out : List ea.Γ) (s : Option ea.Γ) :
    EvalsToInTime (fstTM ea eb).step
      (mkCfg ea eb (some FstL.drain) s rest buf out)
      (some (mkCfg ea eb (some FstL.copy) none [] buf out))
      (rest.length + 1) := by
  induction rest generalizing s with
  | nil => exact oneStep ea eb (drain_nil ea eb buf out s)
  | cons x xs ih =>
    have hstep : (fstTM ea eb).step (mkCfg ea eb (some FstL.drain) s (x :: xs) buf out) =
        some (mkCfg ea eb (some FstL.drain) (some (defaultΓ ea)) xs buf out) := by
      cases x with
      | inl a => exact drain_cons_inl ea eb a xs buf out s
      | inr b => exact drain_cons_inr ea eb b xs buf out s
    exact bumpTime ea eb
      (EvalsToInTime.trans (fstTM ea eb).step 1 (xs.length + 1) _ _ _
        (oneStep ea eb hstep)
        (ih (some (defaultΓ ea))))
      (by simp only [List.length_cons]; omega)

private def copyPhase [Nonempty ea.Γ]
    (xs : List ea.Γ) (out : List ea.Γ) (s : Option ea.Γ) :
    EvalsToInTime (fstTM ea eb).step
      (mkCfg ea eb (some FstL.copy) s [] xs out)
      (some (mkCfg ea eb none none [] [] (xs.reverse ++ out)))
      (xs.length + 1) := by
  induction xs generalizing out s with
  | nil =>
    simp
    exact oneStep ea eb (copy_nil ea eb out s)
  | cons x xs ih =>
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append, List.length_cons]
    exact bumpTime ea eb
      (EvalsToInTime.trans (fstTM ea eb).step 1 (xs.length + 1) _ _ _
        (oneStep ea eb (copy_cons ea eb x xs out s))
        (ih (x :: out) (some x)))
      (by omega)

private def scanPhase [Nonempty ea.Γ]
    (as : List ea.Γ) (rest : List (Sum ea.Γ eb.Γ)) (buf out : List ea.Γ) (s : Option ea.Γ)
    (hrest : ∀ x ∈ rest.head?, ∃ b, x = Sum.inr b) :
    EvalsToInTime (fstTM ea eb).step
      (mkCfg ea eb (some FstL.scan) s (as.map Sum.inl ++ rest) buf out)
      (some (mkCfg ea eb (some FstL.drain) none rest (as.reverse ++ buf) out))
      (as.length + 1) := by
  induction as generalizing buf s with
  | nil => sorry  -- case split on rest: nil → scan_nil, cons (inr b) → scan_inr
  | cons a as ih => sorry  -- compose scan_inl with ih via trans + bumpTime

/-! ## Full correctness -/

private def fstEval [Nonempty ea.Γ] (as : List ea.Γ) (bs : List eb.Γ) :
    EvalsToInTime (fstTM ea eb).step
      (mkCfg ea eb (some FstL.scan) none (as.map Sum.inl ++ bs.map Sum.inr) [] [])
      (some (mkCfg ea eb none none [] [] as))
      (2 * as.length + bs.length + 3) := by
  sorry

/-! ## Package as TM2ComputableInPolyTime -/

/-- The initList/haltList correspondence for fstTM. -/
private theorem initCfg_eq [Nonempty ea.Γ] (a : α) (b : β) :
    initList (fstTM ea eb) (List.map (Equiv.refl _).invFun
      ((OpenLemma.Complexity.pairEncoding ea eb).encode (a, b))) =
    mkCfg ea eb (some FstL.scan) none ((ea.encode a).map Sum.inl ++ (eb.encode b).map Sum.inr) [] [] := by
  sorry

private theorem haltCfg_eq [Nonempty ea.Γ] (a : α) :
    Option.map (haltList (fstTM ea eb)) (some (List.map (Equiv.refl _).invFun (ea.encode a))) =
    some (mkCfg ea eb none none [] [] (ea.encode a)) := by
  sorry

/-- Prod.fst is poly-time computable on pair-encoded inputs. -/
def polyTimeFst [Nonempty ea.Γ] :
    TM2ComputableInPolyTime (OpenLemma.Complexity.pairEncoding ea eb) ea Prod.fst where
  tm := fstTM ea eb
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 2 * Polynomial.X + Polynomial.X + 3  -- overestimate: 2|a| + |b| + 3 ≤ 3n + 3
  outputsFun := fun ⟨a, b⟩ => by
    sorry

end

end PolyTimeFst
