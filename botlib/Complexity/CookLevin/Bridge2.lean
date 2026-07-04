/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Bridge 2 — Input Decomposition: cert-aware tableau stack layout from the
pair-encoding of the verifier's `(instance, certificate)` input.

This file translates the reviewer-approved Python code proof at
`exploration/cook-levin/bridge2_input_decomposition.py` into machine-verified Lean 4.
It contains five lemmas (A–E), all pure list algebra or definitional unfolding:

  * `initTape_decomp`       — Lemma A: `map hΓ.invFun (encode (a, cert)) = aInput ++ certMapped`.
  * `certMapped_length`     — Lemma B: `certMapped.length = cert.length`.
  * `certMapped_bool`       — Lemma C: every cell of `certMapped` lies in `boolSyms`.
  * `cfgAt_zero`            — Lemma D: `cfgAt V input 0 = Turing.initList V input`.
  * `initList_h_init_shape` — Lemma E: `initList V input` has the `h_init` shape
                              (label `some main`, state `initialState`, stack `k₀` = input,
                              other stacks empty).

The argument uses ONLY:
  - the definition of `pairEncoding` (Lemma A),
  - `List.map_append` / `List.map_map` / `List.length_map` (Lemmas A, B),
  - a `Bool` case split for membership in a 2-element `Finset` (Lemma C),
  - `Function.iterate_zero` (Lemma D),
  - the definitional unfolding of `Turing.initList` (Lemma E).
No computation of configurations is required; the bijection laws of `hΓ` are not
needed for the membership claim (Lemma C), only the well-definedness of `invFun`.
-/
import botlib.Complexity.CookLevin.Completeness
import botlib.Complexity.CookLevin.CertTableau
import Mathlib.Computability.TMComputable
import botlib.Complexity.Encodings

namespace CookLevinTableau

open Turing CookLevinTableau OpenLemma.Complexity Computability List

set_option linter.unusedSectionVars false

variable {V : Turing.FinTM2} [Encodable V.Λ] [Encodable V.σ] [Encodable V.K]
  [∀ k, Encodable (V.Γ k)]
  [Fintype V.Λ] [Fintype V.σ] [Fintype V.K] [∀ k, Fintype (V.Γ k)]
  [DecidableEq V.K] [∀ k, DecidableEq (V.Γ k)]
  [DecidableEq V.Λ] [DecidableEq V.σ]

variable {α : Type} (ea : FinEncoding α)

/-! ## Bridge 2 — Input decomposition

### Lemma A — decomposition (pure list algebra)

`pairEncoding ea finEncodingBoolList` encodes `(a, cert)` as
`(ea.encode a).map Sum.inl ++ cert.map Sum.inr` (the `finEncodingBoolList.encode = id`
unfolding makes the certificate part `cert.map Sum.inr`).
Mapping `hΓ.invFun` through this and distributing over `++` (via `List.map_append`)
and fusing the two inner maps (via `List.map_map`) yields exactly
`aInput ++ certMapped` where `aInput = (ea.encode a).map (hΓ.invFun ∘ Sum.inl)`
and `certMapped = cert.map (hΓ.invFun ∘ Sum.inr)`.
-/

/-- The verifier's initial tape on `(a, cert)` decomposes as `aInput ++ certMapped`, where
    `aInput = (ea.encode a).map (hΓ.invFun ∘ Sum.inl)` is the instance part (bottom of stack)
    and `certMapped = cert.map (hΓ.invFun ∘ Sum.inr)` is the certificate part (top of stack).
    Pure list algebra: `pairEncoding.encode` definition + `List.map_append` + `List.map_map`. -/
theorem initTape_decomp (hΓ : V.Γ V.k₀ ≃ Sum ea.Γ Bool) (a : α) (cert : List Bool) :
    ((pairEncoding ea finEncodingBoolList).encode (a, cert)).map hΓ.invFun
    = (ea.encode a).map (hΓ.invFun ∘ Sum.inl) ++ cert.map (hΓ.invFun ∘ Sum.inr) := by
  -- Unfold `pairEncoding` (encode = fun p => (ea.encode p.1).map inl ++ (eb.encode p.2).map inr)
  -- and `finEncodingBoolList` (encode = id, so eb.encode cert = cert) by defeq.
  show ((ea.encode a).map Sum.inl ++ cert.map Sum.inr).map hΓ.invFun
    = (ea.encode a).map (hΓ.invFun ∘ Sum.inl) ++ cert.map (hΓ.invFun ∘ Sum.inr)
  -- Distribute `map` over `++`, then fuse each inner `map` via `map_map`.
  rw [List.map_append, List.map_map, List.map_map]

/-! ### Lemma B — cert length

`map` preserves length, so `certMapped.length = cert.length`.  When the NP relation
fixes `cert.length = certBound`, transitivity gives `certMapped.length = certBound`.
-/

/-- `certMapped.length = cert.length`.  Uses `List.length_map` (map preserves length). -/
theorem certMapped_length (hΓ : V.Γ V.k₀ ≃ Sum ea.Γ Bool) (cert : List Bool) :
    (cert.map (hΓ.invFun ∘ Sum.inr)).length = cert.length := by
  simp [List.length_map]

/-! ### Lemma C — cert bits are boolean tape symbols

`boolSyms hΓ := {hΓ.invFun (Sum.inr true), hΓ.invFun (Sum.inr false)}` is the 2-element
image of `Bool` under `hΓ.invFun ∘ Sum.inr`.  Every cell of `certMapped` is
`hΓ.invFun (Sum.inr b)` for some `b : Bool`; case-splitting on `b ∈ {true, false}`
shows each cell is one of the two elements of `boolSyms`.  The bijection laws of `hΓ`
are NOT needed for the membership claim — only that `invFun` is a well-defined function.
-/

/-- The 2-element image of `Bool` under `hΓ.invFun ∘ Sum.inr`. -/
def boolSyms (hΓ : V.Γ V.k₀ ≃ Sum ea.Γ Bool) : Finset (V.Γ V.k₀) :=
  {hΓ.invFun (Sum.inr true), hΓ.invFun (Sum.inr false)}

/-- Every cell of `certMapped` lies in `boolSyms hΓ`.  Proof by `Bool` case split:
    each cell is `hΓ.invFun (Sum.inr b)` and `b ∈ {true, false}`, so it is one of the two
    elements of `boolSyms` by definitional `Finset` membership. -/
theorem certMapped_bool (hΓ : V.Γ V.k₀ ≃ Sum ea.Γ Bool) (cert : List Bool) :
    ∀ γ ∈ cert.map (hΓ.invFun ∘ Sum.inr), γ ∈ boolSyms ea hΓ := by
  intro γ hγ
  -- Reduce list membership to an existential `b` with `hΓ.invFun (Sum.inr b) = γ`.
  simp only [List.mem_map, Function.comp_apply] at hγ
  obtain ⟨b, _, hb⟩ := hγ
  subst hb
  -- Now the goal is `hΓ.invFun (Sum.inr b) ∈ boolSyms hΓ`.  Case split on `b : Bool`.
  cases b <;> simp [boolSyms]

/-! ### Lemma D — `cfgAt` at 0 is `initList` (definitional)

`cfgAt V input 0 = (stepOrHalt V)^[0] (Turing.initList V input) = Turing.initList V input`
because zero-fold iteration is the identity (`Function.iterate_zero`).
-/

/-- `cfgAt V input 0 = Turing.initList V input` (zero-fold iteration is the identity). -/
theorem cfgAt_zero (input : List (V.Γ V.k₀)) : cfgAt V input 0 = Turing.initList V input := by
  simp [cfgAt, Function.iterate_zero_apply]

/-! ### Lemma E — `initList` shape matches `h_init` (definitional unfolding)

`Turing.initList V input` is defined as the configuration with label `some V.main`,
state `V.initialState`, and stack function
`fun k => @dite (List (V.Γ k)) (k = V.k₀) (V.kDecidableEq k V.k₀) (fun h => by rw [h]; exact input) (fun _ => [])`.
The `label` and `state` fields are definitionally `some V.main` / `V.initialState`.
The `stk` field agrees with the `h_init` shape `fun k => @dite ... (fun h => h ▸ input) (fun _ => [])`
(the `h ▸ input` transport form) up to the two `Eq`-transports being *provably* equal
(both carry `input` along `h : k = V.k₀`); this is NOT a definitional equality (the `rw`-based
transport in `initList`'s definition and the `▸`-based transport in the statement are distinct
proof terms), so the proof reduces each `dite` to its branch by case-splitting on the
`Decidable (k = V.k₀)` instance (`cases V.kDecidableEq k V.k₀`) that the `dite`s match on,
then closes the positive branch by `Eq` case analysis on `h` (the `refl` case makes both
transports the identity, i.e. `input = input`).

NB: the `h_init` precondition in `CertTableau.lean`'s `satisfies_initial_cert` uses the
context's `[DecidableEq V.K]` instance (an abstract hypothesis here), while `Turing.initList`
uses the bundled `V.kDecidableEq` instance.  These two `Decidable (k = V.k₀)` instances are
provably equal (both descend from the same `FinTM2` bundle; `FinTM2.decidableEqK` IS
`V.kDecidableEq`) but are NOT definitionally equal as far as an abstract section variable is
concerned.  Hence this lemma is stated with `@dite ... (V.kDecidableEq k V.k₀) ...` so that the
`dite` instance matches `initList`'s exactly and `dif_pos`/`dif_neg` apply.  The residual
coercion to the context-instance form is a separate (instance-agreement) concern that belongs
to the consumer; it is noted here, not patched.
-/

/-- `initList V input` has the exact `h_init` shape required by `reduction_sound_cert`:
    label `some main`, state `initialState`, stack `k₀` = the input, other stacks empty.
    Stated with the `V.kDecidableEq` instance explicitly (see NB above) so the `dite` instances
    match `initList`'s and the `Decidable`-case split reduces each branch. -/
theorem initList_h_init_shape (input : List (V.Γ V.k₀)) :
    Turing.initList V input =
      { l := some V.main, var := V.initialState,
        stk := fun k => @dite (List (V.Γ k)) (k = V.k₀) (V.kDecidableEq k V.k₀)
          (fun h => h ▸ input) (fun _ => []) } := by
  unfold Turing.initList
  -- `congr 1` reduces the `Cfg.mk` equality to the `stk` field (the `l`/`var` fields
  -- are syntactically equal and auto-closed).
  congr 1
  funext k
  -- Case-split on the `Decidable (k = V.k₀)` instance that the `dite`s match on.
  -- `cases` on the `Decidable` value (not `by_cases`) replaces the instance with the
  -- constructor in each branch, so the `dite`s reduce to their `t`/`e` branch, and it does
  -- NOT `subst` `k` (so the two branches' contexts stay independent).
  cases V.kDecidableEq k V.k₀ with
  | isTrue h =>
    -- Both dites reduce to their `t`-branch applied to `h : k = V.k₀`.
    -- Goal: `(by rw [h]; exact input) = h ▸ input` (the two `Eq`-transports of `input`).
    -- `cases h` (the `refl` case, alone in this focused branch) makes `k = V.k₀`, reducing
    -- both transports to `input`.
    cases h with
    | refl => rfl
  | isFalse h =>
    -- Both dites reduce to their `e`-branch, i.e. `(fun _ => []) h = []`.
    rfl

end CookLevinTableau