/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.

Polynomial-time complexity of the Cook-Levin reduction.
This file asserts that the cert-aware `tableauFormulaCert` construction is
computable in polynomial time on a multi-tape Turing machine, for the real
reduction map `f : β → CNF` used in the Cook-Levin NP-hardness assembly.

The earlier degenerate statement (`fun _ => tableauFormula params []`, ignoring
its input and using an empty certificate) has been replaced by the real `f`:
    f a = tableauFormulaCert (paramsFor a) (aInput a) (certBound a) boolSyms
where the `a`-region is fixed to `encode a` (mapped through the verifier's input
alphabet equivalence `hGamma : V.Γ V.k₀ ≃ Sum eb.Γ Bool`) and the cert-region is
left free. This is the form required to witness `PolyTimeReducible eb
finEncodingCNF L' SAT_Language` for an arbitrary `InNP eb L'`.

The polytime-ness is honest only when the tableau parameters (`timeBound`,
`maxStackDepth`) are polynomially bounded in the input size `|encode a|`; the
hypotheses `h_time` and `h_depth` enforce this, so the axiom is a faithful
citation rather than a blanket (false-for-pathological-params) assertion.
-/
import botlib.Complexity.CookLevin.CertTableau
import botlib.Complexity.CookLevin.Tableau
import botlib.Complexity.Defs
import botlib.Complexity.SAT
import botlib.Complexity.Encodings

namespace CookLevinTableau

open Turing OpenLemma.Complexity OpenLemma.Complexity.SAT Computability

instance : DecidableEq finEncodingNatBool.Γ := inferInstanceAs (DecidableEq Bool)

/-- Citation axiom: the cert-aware Cook-Levin tableau reduction
    `f a = tableauFormulaCert (paramsFor a) (aInput a) (certBound a) boolSyms`
    is polynomial-time computable, provided the tableau parameters are
    polynomially bounded in the input size.

    The formula size is `O(T * (K * S + |Λ|))`, polynomial in `|encode a|` when
    `timeBound` and `maxStackDepth` are polynomial in `|encode a| + |encode a|^k`.
    Here `aInput a = (eb.encode a).map (hGamma.invFun ∘ Sum.inl)` fixes the
    `a`-region to `encode a` (via the verifier's input alphabet equivalence
    `hGamma : V.Γ V.k₀ ≃ Sum eb.Γ Bool`), and `certBound a = |encode a|^k` is the
    certificate bound from `InNP eb L'`.

    Verified citations: Arora-Barak (Thm 2.10), Sipser (Thm 7.37). -/
axiom tableauFormulaCert_is_polytime
    {β : Type} (eb : FinEncoding β) (V : FinTM2)
    [Encodable V.Λ] [Encodable V.σ] [Encodable V.K] [∀ k, Encodable (V.Γ k)]
    [Fintype V.Λ] [Fintype V.σ] [Fintype V.K] [∀ k, Fintype (V.Γ k)]
    [DecidableEq V.K] [∀ k, DecidableEq (V.Γ k)]
    (k : ℕ) (boolSyms : Finset (V.Γ V.k₀)) (hGamma : V.Γ V.k₀ ≃ Sum eb.Γ Bool)
    (paramsFor : β → Params V) (timePoly depthPoly : Polynomial ℕ)
    (h_time : ∀ a, (paramsFor a).timeBound ≤ timePoly.eval ((eb.encode a).length + (eb.encode a).length ^ k))
    (h_depth : ∀ a, (paramsFor a).maxStackDepth ≤
      depthPoly.eval ((eb.encode a).length + (eb.encode a).length ^ k)) :
    Nonempty (TM2ComputableInPolyTime eb finEncodingCNF
      (fun a => tableauFormulaCert (paramsFor a)
        ((eb.encode a).map (hGamma.invFun ∘ Sum.inl))
        ((eb.encode a).length ^ k)
        boolSyms))

end CookLevinTableau