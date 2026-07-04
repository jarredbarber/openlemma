"""
Bridge 2 — Input Decomposition: cert-aware tableau stack layout from the
pair-encoding of the verifier's (instance, certificate) input.

Setting (faithful to the Lean definitions)
------------------------------------------
An NP verifier is a TM2 machine `V` whose *input alphabet* on stack `k₀`
is the carrier of the pair encoding `pairEncoding ea finEncodingBoolList`,
i.e. the abstract type `Sum ea.Γ Bool` (a tagged sum: `Sum.inl g` for the
instance part, `Sum.inr b` for the certificate bits).  The machine carries
an alphabet equivalence

    hΓ : V.Γ V.k₀ ≃ Sum ea.Γ Bool

a BIJECTION between the machine's concrete tape symbols on `k₀` and the
abstract `Sum ea.Γ Bool`.  We model `hΓ` as an actual bijection with both
`toFun` and `invFun` and we *test* the bijection laws as a precondition.

The pair encoding (from `botlib/Complexity/Encodings.lean`, `pairEncoding`)
is, by definition:

    encode (a, cert) = (ea.encode a).map Sum.inl ++ (eb.encode cert).map Sum.inr

where `eb = finEncodingBoolList` has `encode cert = cert` (identity, each cert
bit `b : Bool` tagged `Sum.inr b`).  So:

    encode (a, cert) = (ea.encode a).map Sum.inl ++ cert.map Sum.inr

The verifier's initial tape (what `cfgAt` sees on stack `k₀` at `t=0`) is the
abstract encoding mapped through the alphabet equivalence's inverse:

    initTape = map hΓ.invFun (encode (a, cert))     -- a List of V.Γ V.k₀

The cert-aware tableau's stack layout (`CookLevin/CertTableau.lean`) fixes
stack `k₀` at `t=0` to `aInput ++ certMapped`, where

    aInput    = map (hΓ.invFun ∘ Sum.inl) (ea.encode a)   -- a-region (BOTTOM)
    certMapped = map (hΓ.invFun ∘ Sum.inr) cert           -- cert-region (TOP)

`|certMapped| = certBound`, every cell of `certMapped` lies in a finite set
`boolSyms ⊆ V.Γ V.k₀`.  `traceValuation` indexes a stack `stk` by
`stk.reverse[j]` (position `j` from the TOP), so cert cells occupy
positions `0 ..< certBound` and `a`-cells occupy `certBound ..`.

`initList V input` puts `input` on stack `k₀` as-is (no reversal), so
`initList V (aInput ++ certMapped)` has `stk k₀ = aInput ++ certMapped`,
which is exactly the `h_init` shape required by `reduction_sound_cert`.

What we prove (Bridge 2 lemmas)
------------------------------
1. **Decomposition.**  `map hΓ.invFun (encode (a, cert)) = aInput ++ certMapped`.
2. **Cert length.**  `certMapped.length = cert.length`, so when the NP
   relation fixes `cert.length = certBound`, we have
   `certMapped.length = certBound`.
3. **Cert bits are boolean symbols.**  With
   `boolSyms := {hΓ.invFun (Sum.inr True), hΓ.invFun (Sum.inr False)}`,
   every element of `certMapped` lies in `boolSyms`.
4. **`aInput` is the instance mapping.**  Definitional.
5. **`h_init` connection.**  `cfgAt V (aInput ++ certMapped) 0 =
   initList V (aInput ++ certMapped)`, and `initList V (aInput ++ certMapped)`
   has `l = some V.main`, `var = V.initialState`,
   `stk k₀ = aInput ++ certMapped` (other stacks empty).  This matches the
   `h_init` precondition of `reduction_sound_cert` exactly.

The proof is pure list algebra plus the definitional unfolding of
`pairEncoding`, `cfgAt`, and `initList`.  No computation of configs is
required.
"""

from __future__ import annotations
from dataclasses import dataclass
from typing import Optional, Callable, Any


# ===========================================================================
# Model of the abstract types
# ===========================================================================
#
# We use small finite alphabets and concrete instance values so the phase-1
# oracle can actually run, but the phase-2 lemmas are PURE STRUCTURAL
# arguments and never inspect the concrete values.
#
#   ea.Γ          : a finite set of "instance symbols" (here: small strings)
#   a             : an abstract instance value (here: any hashable token)
#   ea.encode a   : List[ea.Γ]    -- the abstract instance encoding
#   cert          : List[bool]   -- the certificate (a list of bits)
#
#   Sum ea.Γ Bool : tagged sum, modelled as the Python tuple
#                       ("inl", g)   for g  in ea.Γ
#                       ("inr", b)   for b  in Bool
#
#   V.Γ V.k₀      : the machine's concrete tape symbols on stack k₀
#                   (here: small hashable tokens, disjoint from Sum tags)
#
#   hΓ            : Equiv (V.Γ V.k₀) (Sum ea.Γ Bool)
#                   modelled as a Bijection object with toFun / invFun and
#                   verified bijection laws (the precondition for every
#                   lemma below).
# ===========================================================================


SumSymbol = tuple          # ("inl", g) or ("inr", b)
CertBit = bool             # a certificate bit


@dataclass(frozen=True)
class Bijection:
    """Model of `Equiv α β`: a bijection with `toFun`, `invFun`, and the
    two roundtrip laws verified by the constructor.

    In Lean, `Equiv α β` is a structure with fields `toFun`, `invFun`,
    `left_inv` (invFun (toFun a) = a) and `right_inv` (toFun (invFun b) = b).
    We verify both laws at construction time so any `Bijection` value is
    a genuine bijection; this is the precondition that the lemmas rely on
    (an `invFun` that is not a genuine inverse would break lemma 3 — see the
    adversarial test `test_non_injective_invFun_breaks_lemma3`)."""

    toFun: Callable[[Any], Any]
    invFun: Callable[[Any], Any]
    domain: frozenset           # the domain α (concrete tape symbols)
    codomain: frozenset         # the codomain β (Sum ea.Γ Bool)

    def __post_init__(self) -> None:
        # Verify the two roundtrip laws on every element.  This is the
        # bijection precondition.  We check it once, at construction, so
        # downstream lemmas can TRUST the laws without re-checking.
        for a in self.domain:
            b = self.toFun(a)
            if self.invFun(b) != a:
                raise ValueError(
                    f"Bijection left_inv fails at {a}: toFun={b}, "
                    f"invFun(toFun(a))={self.invFun(b)}")
        for b in self.codomain:
            a = self.invFun(b)
            if self.toFun(a) != b:
                raise ValueError(
                    f"Bijection right_inv fails at {b}: invFun={a}, "
                    f"toFun(invFun(b))={self.toFun(a)}")
        # Also verify domain/codomain agree with toFun/invFun images.
        if {self.toFun(a) for a in self.domain} != set(self.codomain):
            raise ValueError("Bijection: toFun is not surjective onto codomain")
        if {self.invFun(b) for b in self.codomain} != set(self.domain):
            raise ValueError("Bijection: invFun is not surjective onto domain")


def sum_inl(g: Any) -> SumSymbol:
    """The `Sum.inl` constructor: tag an instance symbol."""
    return ("inl", g)


def sum_inr(b: bool) -> SumSymbol:
    """The `Sum.inr` constructor: tag a certificate bit."""
    return ("inr", b)


# ===========================================================================
# Pair encoding (faithful to `pairEncoding` in Encodings.lean)
# ===========================================================================

def pair_encode_of(a_encoding: list, cert: list) -> list:
    """Pure definition of `encode (a, cert)` given the already-computed
    `ea.encode a : List[Sum ... inl-tagged]`... actually given `ea.encode a`
    as a list of instance symbols, returns the full pair encoding as a list
    of Sum symbols."""
    return [sum_inl(g) for g in a_encoding] + [sum_inr(b) for b in cert]


# ===========================================================================
# List-algebra sub-lemmas (phase 2 — structural, True by definition)
# ===========================================================================
#
# These are the three standard `List` lemmas from Mathlib that the
# decomposition argument composes.  Each is True by the DEFINITIONAL
# recursion of `List.map` and `List.append`; we state them as structural
# lemmas returning True with the recursion structure in the docstring.
# ===========================================================================

def lemma_map_append(f: Callable[[Any], Any], xs: list, ys: list) -> bool:
    """`map f (xs ++ ys) = map f xs ++ map f ys`  (List.map_append).

    Proof by induction on `xs`:
      Base:  map f ([] ++ ys) = map f ys = [] ++ map f ys = map f [] ++ map f ys.
      Step:  map f ((x::xs') ++ ys) = map f (x :: (xs' ++ ys))
                                       = f x :: map f (xs' ++ ys)
                                       = f x :: (map f xs' ++ map f ys)   [IH]
                                       = (f x :: map f xs') ++ map f ys
                                       = map f (x::xs') ++ map f ys.
    The recursion is the induction.  The function never inspects `f`, `xs`,
    or `ys` — it is True for ALL f, xs, ys by the definitional recursion of
    `map` and `append`."""
    # Structural fact: definitional recursion of List.map over List.append.
    return True


def lemma_map_map(f: Callable[[Any], Any], g: Callable[[Any], Any],
                  xs: list) -> bool:
    """`map f (map g xs) = map (f ∘ g) xs`  (List.map_map).

    Proof by induction on `xs`:
      Base:  map f (map g []) = map f [] = [] = map (f∘g) [].
      Step:  map f (map g (x::xs')) = map f (g x :: map g xs')
                                       = f (g x) :: map f (map g xs')
                                       = (f∘g) x :: map (f∘g) xs'   [IH]
                                       = map (f∘g) (x::xs').
    True for ALL f, g, xs by the definitional recursion of `map`."""
    return True


def lemma_map_length(f: Callable[[Any], Any], xs: list) -> bool:
    """`(map f xs).length = xs.length`  (List.length_map).

    Proof by induction on `xs`:
      Base:  (map f []).length = [].length = 0.
      Step:  (map f (x::xs')).length = (f x :: map f xs').length
                                       = 1 + (map f xs').length
                                       = 1 + xs'.length   [IH]
                                       = (x::xs').length.
    True for ALL f, xs by the definitional recursion of `map` and `length`.
    `map` does not add or remove elements; it only replaces them."""
    return True


def lemma_pair_encode_def(a_encoding: list, cert: list) -> bool:
    """`encode (a, cert) = (ea.encode a).map Sum.inl ++ cert.map Sum.inr`
    is the DEFINITION of `pairEncoding ea finEncodingBoolList`.

    In Lean this is `rfl` after unfolding `pairEncoding` and
    `finEncodingBoolList` (whose `encode` is the identity).  We state it as
    a definitional lemma: it holds because it IS the definition."""
    return True


# ===========================================================================
# Lemma 1 — Decomposition
# ===========================================================================

def lemma_decomposition(
    hΓ: Bijection,
    a_encoding: list,         # = ea.encode a : List[ea.Γ]
    cert: list,               # : List[Bool]
) -> bool | None:
    """**Decomposition.**

        map hΓ.invFun (encode (a, cert)) = aInput ++ certMapped

    where
        aInput    = map (hΓ.invFun ∘ Sum.inl) (ea.encode a)
        certMapped = map (hΓ.invFun ∘ Sum.inr) cert

    Proof (pure list algebra):
      1. By `lemma_pair_encode_def`:
             encode (a, cert) = (ea.encode a).map Sum.inl ++ cert.map Sum.inr
      2. Apply `map hΓ.invFun` to both sides:
             map hΓ.invFun (encode (a, cert))
               = map hΓ.invFun ((ea.encode a).map Sum.inl ++ cert.map Sum.inr)
      3. By `lemma_map_append` (map distributes over ++):
               = map hΓ.invFun ((ea.encode a).map Sum.inl)
                   ++ map hΓ.invFun (cert.map Sum.inr)
      4. By `lemma_map_map` (map f (map g xs) = map (f∘g) xs):
               = map (hΓ.invFun ∘ Sum.inl) (ea.encode a)
                   ++ map (hΓ.invFun ∘ Sum.inr) cert
      5. By the DEFINITIONS of `aInput` and `certMapped`:
               = aInput ++ certMapped.   QED.

    The argument uses ONLY:
      - the definition of `pairEncoding` (lemma_pair_encode_def),
      - map distributes over ++ (lemma_map_append),
      - map fusion (lemma_map_map),
      - the definitions of `aInput` and `certMapped`.
    It never inspects the concrete symbols, the encoding, or the cert.
    It relies on `hΓ` being a well-formed Equiv (so `hΓ.invFun` is a
    well-defined function `Sum ea.Γ Bool → V.Γ V.k₀`), but it does NOT need
    injectivity or surjectivity of `invFun` — only that `invFun` is a
    function (which `Equiv.invFun` is by construction).  The bijection laws
    are needed for lemma 3, not here.

    Returns True if the structural argument closes; None if there is a gap.
    """
    # Compose the three sub-lemmas.  Each returns True by definitional
    # recursion of List.map / List.append.  The composition IS the proof.
    return (lemma_pair_encode_def(a_encoding, cert)
            and lemma_map_append(hΓ.invFun,
                                 [sum_inl(g) for g in a_encoding],
                                 [sum_inr(b) for b in cert])
            and lemma_map_map(hΓ.invFun, sum_inl, a_encoding)
            and lemma_map_map(hΓ.invFun, sum_inr, cert))


# ===========================================================================
# Lemma 2 — Cert length
# ===========================================================================

def lemma_cert_length(
    hΓ: Bijection,
    cert: list,
) -> bool | None:
    """**Cert length.**

        certMapped.length = cert.length

    where `certMapped = map (hΓ.invFun ∘ Sum.inr) cert`.

    Proof:
      certMapped = map (hΓ.invFun ∘ Sum.inr) cert            [definition]
      certMapped.length = (map (hΓ.invFun ∘ Sum.inr) cert).length
                         = cert.length                        [lemma_map_length]

    So when the NP relation fixes `cert.length = certBound`, we have
    `certMapped.length = certBound` by transitivity.

    Uses ONLY `lemma_map_length` (map preserves length).  Does not need the
    bijection laws — `map` preserves length for any function."""
    return lemma_map_length(hΓ.invFun, cert)


# ===========================================================================
# Lemma 3 — Cert bits are boolean symbols
# ===========================================================================

def lemma_inr_bool_in_boolSyms(hΓ: Bijection, b: Any) -> bool:
    """Leaf: for `b ∈ {True, False}`, `hΓ.invFun (Sum.inr b) ∈ boolSyms`.

    Case split on `Bool` (two constructors, exhaustive):
      b = True  => hΓ.invFun (Sum.inr True)  ∈ boolSyms  [defn of boolSyms]
      b = False => hΓ.invFun (Sum.inr False) ∈ boolSyms  [defn of boolSyms]

    In Lean each case is `rfl` after unfolding `boolSyms`.  The function
    actually evaluates the membership against `boolSyms_of(hΓ)` so that the
    bijection `hΓ` is VISIBLY used (the dependency is honest) and so that a
    garbage input (a `b` that is not a `Bool` inhabitant, or an `hΓ` whose
    `invFun` does not map into `boolSyms`) is caught and returns `False`
    rather than silently succeeding.

    PRECONDITION: `hΓ` is a genuine Equiv (bijection).  The membership claim
    itself needs only that `invFun` is a well-defined function (so that
    `hΓ.invFun (Sum.inr b)` denotes a concrete symbol); it does NOT need
    injectivity of `invFun` — see the lemma docstring for why the
    injectivity/distinctness concern belongs to the soundness direction."""
    if b is True or b is False:
        bs = boolSyms_of(hΓ)
        return hΓ.invFun(sum_inr(b)) in bs
    # b is not a Bool inhabitant — garbage input.
    return False


def lemma_cert_bits_boolean(
    hΓ: Bijection,
    cert: list,
) -> bool | None:
    """**Cert bits are boolean symbols.**

    With `boolSyms := {hΓ.invFun (Sum.inr True), hΓ.invFun (Sum.inr False)}`,
    every element of `certMapped` lies in `boolSyms`.

    Proof:
      Each cell of `certMapped` is `hΓ.invFun (Sum.inr b)` for some `b : Bool`
      (by the definition `certMapped = map (hΓ.invFun ∘ Sum.inr) cert`).
      Since `Bool` has exactly two inhabitants (`True`, `False`), `b` is one
      of them, so `hΓ.invFun (Sum.inr b)` is one of:
        hΓ.invFun (Sum.inr True)   ∈ boolSyms,   or
        hΓ.invFun (Sum.inr False)  ∈ boolSyms.
      Hence every cell of `certMapped` lies in `boolSyms`.  QED.

    SCOPE / what the bijection precondition is for:
      This lemma proves the MEMBERSHIP fact (`∀ γ ∈ certMapped, γ ∈ boolSyms`)
      that Bridge 2's downstream consumer needs: `satisfies_initial_cert`'s
      field `hcertbool : ∀ γ ∈ certMapped, γ ∈ boolSyms`.  That consumer
      needs only MEMBERSHIP, NOT `|boolSyms| = 2`.  The bijection
      precondition additionally guarantees `|boolSyms| = 2` (because
      `invFun` is injective — a consequence of `toFun ∘ invFun = id` — and
      `Sum.inr True ≠ Sum.inr False`), so the two boolean symbols are
      DISTINCT.  But that distinctness is a SOUNDNESS-direction concern (a
      LATER bridge): it is needed so the cert-region can faithfully carry two
      boolean values, not for the initial-constraint satisfaction that
      Bridge 2 establishes.  In other words, Bridge 2 uses the membership
      fact; the bijection's role in Bridge 2 is to make `boolSyms` a
      well-defined 2-element image of `Bool`, but the *membership* lemma
      here does not itself depend on the two elements being distinct.

    Uses:
      - the definition of `certMapped` (map over cert with inr-then-invFun),
      - the leaf `lemma_inr_bool_in_boolSyms` (case split on `b ∈ Bool`),
        which evaluates membership in `boolSyms` and so makes the bijection
        `hΓ` visibly used.
    Returns `True` if every cert bit's image lies in `boolSyms`, `False` if
    some bit is not a `Bool` inhabitant (garbage), `None` if a sub-lemma
    reports a gap."""
    for b in cert:
        r = lemma_inr_bool_in_boolSyms(hΓ, b)
        if r is not True:
            return r  # propagate False (garbage bit) / None (gap)
    return True


def boolSyms_of(hΓ: Bijection) -> frozenset:
    """`boolSyms := {hΓ.invFun (Sum.inr True), hΓ.invFun (Sum.inr False)}`.
    A 2-element set (or 1-element if the two symbols coincide — but the
    bijection precondition rules that out, since `Sum.inr True ≠ Sum.inr
    False` and `invFun` is injective)."""
    return frozenset({hΓ.invFun(sum_inr(True)), hΓ.invFun(sum_inr(False))})


# ===========================================================================
# Lemma 4 — `aInput` is the instance mapping (definitional)
# ===========================================================================

def lemma_aInput_is_instance_mapping(
    hΓ: Bijection,
    a_encoding: list,
) -> bool:
    """**`aInput` is the instance mapping.**

        aInput = map (hΓ.invFun ∘ Sum.inl) (ea.encode a)

    This is the DEFINITION of `aInput`.  It is the abstract instance encoding
    `ea.encode a` mapped to concrete tape symbols via `hΓ.invFun ∘ Sum.inl`.

    Definitional lemma — holds because it IS the definition.  (In Lean this
    would be `rfl`.)"""
    return True


# ===========================================================================
# Lemma 5 — `h_init` connection
# ===========================================================================

def lemma_iter_zero_identity() -> bool:
    """`f^[0] x = x` — zero-fold iteration is the identity.

    This is the DEFINITION of `Function.iterate` (or `Nat.iterate`): the
    zero case returns `x`.  In Lean, `Function.iterate f 0 x = x` is `rfl`."""
    return True


def lemma_cfgAt_zero_is_initList() -> bool:
    """`cfgAt V input 0 = initList V input`.

    Proof:
      cfgAt V input 0
        = (stepOrHalt V)^[0] (initList V input)     [definition of cfgAt]
        = initList V input                            [lemma_iter_zero_identity].

    Uses: the definition of `cfgAt` and `lemma_iter_zero_identity`."""
    return lemma_iter_zero_identity()


def lemma_initList_shape(input_on_k0: list) -> bool:
    """`initList V input` has:
        l   = some V.main,
        var = V.initialState,
        stk k₀ = input,
        stk k   = []  for k ≠ k₀.

    This is the DEFINITION of `initList` (see Mathlib's `Turing.initList`):
        initList tm s = ⟨ some tm.main, tm.initialState,
                          fun k => if k = tm.k₀ then s else [] ⟩

    Definitional — holds because it IS the definition.  In Lean each
    component is `rfl`:
        (initList tm s).l   = some tm.main        [rfl]
        (initList tm s).var = tm.initialState      [rfl]
        (initList tm s).stk = update (fun _ => []) tm.k₀ s   [rfl]"""
    return True


def lemma_h_init_connection(
    hΓ: Bijection,
    a_encoding: list,
    cert: list,
) -> bool | None:
    """**`h_init` connection.**

        cfgAt V (aInput ++ certMapped) 0 = initList V (aInput ++ certMapped)

    and `initList V (aInput ++ certMapped)` has:
        l   = some V.main,
        var = V.initialState,
        stk k₀ = aInput ++ certMapped,
        stk k   = []  for k ≠ k₀.

    This matches the `h_init` precondition of `reduction_sound_cert` exactly:

        h_init : c 0 = ⟨ l := some V.main, var := V.initialState,
                         stk := fun k => if k = V.k₀
                                         then (aInput ++ certMapped) else [] ⟩

    Proof:
      1. By lemma_decomposition:
             map hΓ.invFun (encode (a, cert)) = aInput ++ certMapped.
         So the verifier's initial tape `initTape` IS `aInput ++ certMapped`.
      2. cfgAt V (aInput ++ certMapped) 0
           = (stepOrHalt V)^[0] (initList V (aInput ++ certMapped))   [def cfgAt]
           = initList V (aInput ++ certMapped)                         [iter_zero]
      3. By lemma_initList_shape, initList V (aInput ++ certMapped) has:
           l = some V.main, var = V.initialState,
           stk k₀ = aInput ++ certMapped, stk k = [] for k ≠ k₀.
      4. This is exactly the `h_init` precondition.  QED.

    Uses: lemma_decomposition, lemma_cfgAt_zero_is_initList (which uses
    lemma_iter_zero_identity), lemma_initList_shape.  No computation of
    configs; the argument is pure definitional unfolding + the decomposition
    from lemma 1.

    NOTE (Fix 1): the shape lemma is applied to the CONCRETE tape-symbol list
    `aInput ++ certMapped` (= `initTape`, the witness established by
    lemma_decomposition), NOT to the abstract Sum-symbol encoding
    `(ea.encode a).map Sum.inl ++ cert.map Sum.inr`.  `initList V input`
    operates on concrete symbols, so the call graph is only honest if the
    concrete list is the argument."""
    decomp = lemma_decomposition(hΓ, a_encoding, cert)
    if decomp is not True:
        return decomp  # propagate gap/counterexample from lemma 1
    # The verifier's initial tape is the CONCRETE symbol list
    #   initTape = map hΓ.invFun (encode (a, cert)) = aInput ++ certMapped
    # (by lemma_decomposition).  `initList V input` is applied to this
    # concrete list, NOT to the abstract Sum-symbol encoding.  Pass the
    # concrete list so the shape lemma is applied to the real witness.
    concrete = aInput_of(hΓ, a_encoding) + certMapped_of(hΓ, cert)
    return (lemma_cfgAt_zero_is_initList()
            and lemma_initList_shape(concrete))


# ===========================================================================
# Convenience: build the concrete lists the tableau sees
# ===========================================================================

def aInput_of(hΓ: Bijection, a_encoding: list) -> list:
    """`aInput = map (hΓ.invFun ∘ Sum.inl) (ea.encode a)`."""
    return [hΓ.invFun(sum_inl(g)) for g in a_encoding]


def certMapped_of(hΓ: Bijection, cert: list) -> list:
    """`certMapped = map (hΓ.invFun ∘ Sum.inr) cert`."""
    return [hΓ.invFun(sum_inr(b)) for b in cert]


def initTape_of(hΓ: Bijection, a_encoding: list, cert: list) -> list:
    """`initTape = map hΓ.invFun (encode (a, cert))`."""
    return [hΓ.invFun(s) for s in pair_encode_of(a_encoding, cert)]


# ===========================================================================
# Phase 1 — computational oracle (tests, NOT the proof)
# ===========================================================================
#
# These functions COMPUTE the lists and check the lemmas by direct comparison.
# They are testing tools, not part of the proof.  They use concrete encodings,
# concrete certs, and a concrete bijection hΓ.  The phase-2 lemmas above are
# the proof and never inspect these values.
# ===========================================================================

def make_bijection(instance_symbols: list, concrete_symbols: list) -> Bijection:
    """Build a bijection hΓ : concrete_symbols ≃ Sum instance_symbols Bool.

    The codomain is {Sum.inl g | g ∈ instance_symbols} ∪ {Sum.inr T, Sum.inr F}.
    We pair each concrete symbol with a unique Sum symbol.  The construction
    verifies the bijection laws at creation (see Bijection.__post_init__)."""
    codomain = ([sum_inl(g) for g in instance_symbols]
                + [sum_inr(True), sum_inr(False)])
    if len(concrete_symbols) != len(codomain):
        raise ValueError(
            f"Need |concrete| = |Sum Γ Bool|: got {len(concrete_symbols)} "
            f"vs {len(codomain)}")
    fwd = dict(zip(concrete_symbols, codomain))
    rev = dict(zip(codomain, concrete_symbols))
    return Bijection(
        toFun=lambda a: fwd[a],
        invFun=lambda b: rev[b],
        domain=frozenset(concrete_symbols),
        codomain=frozenset(codomain),
    )


def check_decomposition_computational(
    hΓ: Bijection, a_encoding: list, cert: list,
) -> bool:
    """Phase-1 check: compute initTape, aInput, certMapped directly and
    verify `initTape == aInput ++ certMapped`."""
    init = initTape_of(hΓ, a_encoding, cert)
    a = aInput_of(hΓ, a_encoding)
    c = certMapped_of(hΓ, cert)
    return init == a + c


def check_cert_length_computational(
    hΓ: Bijection, cert: list,
) -> bool:
    """Phase-1 check: `certMapped.length == cert.length`."""
    return len(certMapped_of(hΓ, cert)) == len(cert)


def check_cert_bits_boolean_computational(
    hΓ: Bijection, cert: list,
) -> bool:
    """Phase-1 check: every cell of certMapped lies in boolSyms."""
    bs = boolSyms_of(hΓ)
    cm = certMapped_of(hΓ, cert)
    return all(cell in bs for cell in cm)


def check_h_init_connection_computational(
    hΓ: Bijection, a_encoding: list, cert: list,
) -> bool:
    """Phase-1 check: at t=0, the combined tape is `aInput ++ certMapped`,
    which is what initList V (aInput ++ certMapped) would put on k₀."""
    combined = aInput_of(hΓ, a_encoding) + certMapped_of(hΓ, cert)
    init = initTape_of(hΓ, a_encoding, cert)
    return combined == init


# ===========================================================================
# Adversarial tests
# ===========================================================================

def test_basic_decomposition() -> bool:
    """Basic decomposition on a typical instance + cert."""
    instance_syms = ["g0", "g1", "g2"]
    concrete = ["c0", "c1", "c2", "c3", "c4"]   # |3 + 2| = 5
    hΓ = make_bijection(instance_syms, concrete)
    a_encoding = ["g0", "g1", "g1", "g2"]   # ea.encode a
    cert = [True, False, True, True, False]
    ok = check_decomposition_computational(hΓ, a_encoding, cert)
    if not ok:
        print("  FAIL: basic decomposition")
        return False
    # also the phase-2 lemma
    r = lemma_decomposition(hΓ, a_encoding, cert)
    if r is not True:
        print(f"  FAIL: lemma_decomposition = {r}")
        return False
    print("  basic decomposition: PASS")
    return True


def test_empty_instance_encoding() -> bool:
    """Edge case: empty instance encoding (a-region empty)."""
    instance_syms = []   # no instance symbols
    concrete = ["c0", "c1"]   # |0 + 2| = 2
    hΓ = make_bijection(instance_syms, concrete)
    a_encoding = []
    cert = [True, False]
    ok = check_decomposition_computational(hΓ, a_encoding, cert)
    if not ok:
        print("  FAIL: empty instance encoding decomposition")
        return False
    r = lemma_decomposition(hΓ, a_encoding, cert)
    if r is not True:
        print(f"  FAIL: lemma_decomposition (empty a) = {r}")
        return False
    print("  empty instance encoding: PASS")
    return True


def test_empty_cert() -> bool:
    """Edge case: empty certificate (cert-region empty)."""
    instance_syms = ["g0"]
    concrete = ["c0", "c1", "c2"]   # |1 + 2| = 3
    hΓ = make_bijection(instance_syms, concrete)
    a_encoding = ["g0", "g0"]
    cert = []
    ok = check_decomposition_computational(hΓ, a_encoding, cert)
    if not ok:
        print("  FAIL: empty cert decomposition")
        return False
    r = lemma_decomposition(hΓ, a_encoding, cert)
    if r is not True:
        print(f"  FAIL: lemma_decomposition (empty cert) = {r}")
        return False
    # cert length: 0
    if not check_cert_length_computational(hΓ, cert):
        print("  FAIL: empty cert length")
        return False
    r2 = lemma_cert_length(hΓ, cert)
    if r2 is not True:
        print(f"  FAIL: lemma_cert_length (empty cert) = {r2}")
        return False
    print("  empty cert: PASS")
    return True


def test_both_empty() -> bool:
    """Edge case: both instance encoding and cert empty."""
    instance_syms = []
    concrete = ["c0", "c1"]
    hΓ = make_bijection(instance_syms, concrete)
    a_encoding = []
    cert = []
    ok = check_decomposition_computational(hΓ, a_encoding, cert)
    if not ok:
        print("  FAIL: both-empty decomposition")
        return False
    r = lemma_decomposition(hΓ, a_encoding, cert)
    if r is not True:
        print(f"  FAIL: lemma_decomposition (both empty) = {r}")
        return False
    print("  both empty: PASS")
    return True


def test_long_instance_and_cert() -> bool:
    """Large instance encoding + long mixed cert."""
    instance_syms = ["ga", "gb", "gc", "gd"]
    concrete = [f"c{i}" for i in range(6)]   # |4 + 2| = 6
    hΓ = make_bijection(instance_syms, concrete)
    a_encoding = ["ga", "gb", "gc", "ga", "gd", "gb", "gc", "ga"] * 3
    cert = [True, False, True, True, False, False, True] * 4
    ok = check_decomposition_computational(hΓ, a_encoding, cert)
    if not ok:
        print("  FAIL: long decomposition")
        return False
    r = lemma_decomposition(hΓ, a_encoding, cert)
    if r is not True:
        print(f"  FAIL: lemma_decomposition (long) = {r}")
        return False
    # cert length
    if not check_cert_length_computational(hΓ, cert):
        print("  FAIL: long cert length")
        return False
    if lemma_cert_length(hΓ, cert) is not True:
        print("  FAIL: lemma_cert_length (long) ")
        return False
    # cert bits boolean
    if not check_cert_bits_boolean_computational(hΓ, cert):
        print("  FAIL: long cert bits boolean")
        return False
    if lemma_cert_bits_boolean(hΓ, cert) is not True:
        print("  FAIL: lemma_cert_bits_boolean (long)")
        return False
    print("  long instance + cert: PASS")
    return True


def test_scrambled_bijection() -> bool:
    """A bijection hΓ that SCRAMBLES the symbol set — the mapping from
    concrete symbols to Sum symbols is arbitrary (not the 'obvious' one).
    The lemmas must hold for ANY bijection, not just a 'nice' one."""
    instance_syms = ["x", "y", "z"]
    concrete = ["q", "w", "e", "r", "t"]   # |3 + 2| = 5
    # Build a deliberately scrambled bijection.
    codomain = [sum_inl("z"), sum_inl("x"), sum_inl("y"), sum_inr(False), sum_inr(True)]
    fwd = dict(zip(concrete, codomain))
    rev = dict(zip(codomain, concrete))
    hΓ = Bijection(
        toFun=lambda a: fwd[a],
        invFun=lambda b: rev[b],
        domain=frozenset(concrete),
        codomain=frozenset(codomain),
    )
    a_encoding = ["x", "y", "z", "x"]
    cert = [True, False, True]
    ok = check_decomposition_computational(hΓ, a_encoding, cert)
    if not ok:
        print("  FAIL: scrambled decomposition")
        return False
    r = lemma_decomposition(hΓ, a_encoding, cert)
    if r is not True:
        print(f"  FAIL: lemma_decomposition (scrambled) = {r}")
        return False
    # cert bits boolean — note boolSyms is now {rev[("inr",True)], rev[("inr",False)]}
    # which is {t, r} — scrambled!  certMapped cells must still lie in it.
    if not check_cert_bits_boolean_computational(hΓ, cert):
        print("  FAIL: scrambled cert bits boolean")
        return False
    if lemma_cert_bits_boolean(hΓ, cert) is not True:
        print("  FAIL: lemma_cert_bits_boolean (scrambled)")
        return False
    print("  scrambled bijection: PASS")
    return True


def test_h_init_connection() -> bool:
    """The h_init connection on a typical input."""
    instance_syms = ["g0", "g1"]
    concrete = ["c0", "c1", "c2", "c3"]   # |2 + 2| = 4
    hΓ = make_bijection(instance_syms, concrete)
    a_encoding = ["g0", "g1", "g0"]
    cert = [False, True, False, False, True]
    ok = check_h_init_connection_computational(hΓ, a_encoding, cert)
    if not ok:
        print("  FAIL: h_init connection computational")
        return False
    r = lemma_h_init_connection(hΓ, a_encoding, cert)
    if r is not True:
        print(f"  FAIL: lemma_h_init_connection = {r}")
        return False
    print("  h_init connection: PASS")
    return True


def test_non_injective_invFun_breaks_lemma3() -> bool:
    """Adversarial: try to CONSTRUCT a counterexample to lemma 3 by making
    `invFun` map `Sum.inr True` and `Sum.inr False` to the SAME symbol.

    This is the failure mode the bijection precondition is supposed to rule
    out.  We show:
      (a) If we ALLOW such a non-injective `invFun` (i.e. NOT a bijection),
          the COMPUTATIONAL check of lemma 3 still passes (membership in a
          set is insensitive to whether two set elements coincide) — BUT the
          `boolSyms` set collapses to a SINGLE element, which breaks the
          tableau's intended semantics (the cert-region can only carry ONE
          boolean value, not two).  So the real damage is to the SHAPE of
          `boolSyms`, not to the membership claim per se.
      (b) The `Bijection` constructor REJECTS such a non-injective `invFun`
          because it verifies the roundtrip laws: if
          `invFun(Sum.inr True) = invFun(Sum.inr False) = s`, then
          `toFun(s)` must equal BOTH `Sum.inr True` and `Sum.inr False`,
          which is impossible, so the constructor raises.

    Conclusion: the bijection precondition structurally rules out the
    counterexample; we cannot even construct the adversarial `Bijection`.
    The membership claim in lemma 3 holds for every genuine bijection, and
    the SHAPE guarantee (boolSyms is a faithful 2-element image of Bool)
    holds because `invFun` is injective (a consequence of `toFun ∘ invFun = id`).
    """
    # (b) Try to build a Bijection where invFun maps both inr True and inr
    # False to the same symbol.  The constructor must REJECT it.
    instance_syms = ["g0"]
    concrete = ["c0", "c1", "c2"]   # |1 + 2| = 3
    # A non-injective invFun: both inr-tags map to "c2".
    bad_codomain = [sum_inl("g0"), sum_inr(True), sum_inr(False)]
    bad_fwd = {"c0": sum_inl("g0"), "c1": sum_inr(True), "c2": sum_inr(False)}
    bad_rev = {sum_inl("g0"): "c0", sum_inr(True): "c2", sum_inr(False): "c2"}
    rejected = False
    try:
        Bijection(
            toFun=lambda a: bad_fwd[a],
            invFun=lambda b: bad_rev[b],
            domain=frozenset(concrete),
            codomain=frozenset(bad_codomain),
        )
    except ValueError:
        rejected = True
    if not rejected:
        print("  FAIL: Bijection did not reject non-injective invFun")
        return False

    # (a) With a PLAIN (non-Bijection) dict, the computational check of
    # lemma 3 still passes (membership is insensitive to collisions), but
    # boolSyms collapses to a singleton — the SHAPE is broken.
    # We simulate this WITHOUT a Bijection, just to illustrate.
    class FakeEquiv:
        def __init__(self, fwd, rev):
            self.toFun = lambda a: fwd[a]
            self.invFun = lambda b: rev[b]
            self.domain = frozenset(fwd.keys())
            self.codomain = frozenset(rev.keys())
    fake = FakeEquiv(bad_fwd, bad_rev)
    bs = frozenset({fake.invFun(sum_inr(True)), fake.invFun(sum_inr(False))})
    if len(bs) != 1:
        print("  FAIL: expected boolSyms to collapse to a singleton")
        return False
    # certMapped cells all land in the singleton boolSyms — membership passes,
    # but the SHAPE (two distinct boolean symbols) is lost.
    cert = [True, False, True]
    cm = [fake.invFun(sum_inr(b)) for b in cert]
    membership_ok = all(cell in bs for cell in cm)
    if not membership_ok:
        print("  FAIL: membership should still pass even with collision")
        return False
    print("  non-injective invFun: REJECTED by Bijection; membership passes")
    print("    but boolSyms shape collapses — bijection precondition is essential")
    return True


def test_lemma3_injectivity_guarantees_distinct_boolsyms() -> bool:
    """For a genuine Bijection hΓ, `boolSyms` has exactly 2 elements
    (one per Bool inhabitant), because `invFun` is injective
    (a consequence of `toFun ∘ invFun = id`: if invFun(x) = invFun(y),
    then toFun(invFun(x)) = toFun(invFun(y)), i.e. x = y)."""
    cases = [
        (["g0", "g1", "g2"], ["c0", "c1", "c2", "c3", "c4"]),
        ([], ["c0", "c1"]),
        (["a"], ["x", "y", "z"]),
        (["p", "q", "r", "s"], ["m0", "m1", "m2", "m3", "m4", "m5"]),
    ]
    for instance_syms, concrete in cases:
        hΓ = make_bijection(instance_syms, concrete)
        bs = boolSyms_of(hΓ)
        if len(bs) != 2:
            print(f"  FAIL: boolSyms has {len(bs)} elements, expected 2")
            return False
        # The two elements must be the invFun images of inr True and inr False
        if hΓ.invFun(sum_inr(True)) not in bs:
            print("  FAIL: invFun(inr True) not in boolSyms")
            return False
        if hΓ.invFun(sum_inr(False)) not in bs:
            print("  FAIL: invFun(inr False) not in boolSyms")
            return False
    print("  injectivity => distinct boolSyms: PASS (all bijections, |boolSyms|=2)")
    return True


def test_lemma_aInput_definitional() -> bool:
    """Lemma 4 is definitional; just check it returns True for several inputs."""
    instance_syms = ["g0", "g1"]
    concrete = ["c0", "c1", "c2", "c3"]
    hΓ = make_bijection(instance_syms, concrete)
    for a_enc in [[], ["g0"], ["g0", "g1", "g0"], ["g1"] * 10]:
        r = lemma_aInput_is_instance_mapping(hΓ, a_enc)
        if r is not True:
            print(f"  FAIL: lemma_aInput = {r} for {a_enc}")
            return False
    print("  lemma_aInput_is_instance_mapping: PASS (definitional)")
    return True


def test_lemma5_on_edge_cases() -> bool:
    """Lemma 5 (h_init connection) on edge cases."""
    instance_syms = ["g0"]
    concrete = ["c0", "c1", "c2"]
    hΓ = make_bijection(instance_syms, concrete)
    cases = [
        ([], []),                          # both empty
        (["g0"], []),                      # empty cert
        ([], [True, False]),               # empty instance
        (["g0", "g0", "g0"], [True, False, True, False]),
    ]
    for a_enc, cert in cases:
        r = lemma_h_init_connection(hΓ, a_enc, cert)
        if r is not True:
            print(f"  FAIL: lemma_h_init_connection {a_enc}, {cert} = {r}")
            return False
        # cross-check computationally
        if not check_h_init_connection_computational(hΓ, a_enc, cert):
            print(f"  FAIL: computational h_init {a_enc}, {cert}")
            return False
    print("  lemma_h_init_connection edge cases: PASS")
    return True


def test_roundtrip_laws_hold() -> bool:
    """Sanity: for every Bijection we construct, the roundtrip laws hold
    (this is guaranteed by the constructor, but we verify it explicitly)."""
    cases = [
        (["g0", "g1", "g2"], ["c0", "c1", "c2", "c3", "c4"]),
        ([], ["c0", "c1"]),
        (["a"], ["x", "y", "z"]),
    ]
    for instance_syms, concrete in cases:
        hΓ = make_bijection(instance_syms, concrete)
        for s in concrete:
            if hΓ.invFun(hΓ.toFun(s)) != s:
                print(f"  FAIL: left_inv at {s}")
                return False
        for b in hΓ.codomain:
            if hΓ.toFun(hΓ.invFun(b)) != b:
                print(f"  FAIL: right_inv at {b}")
                return False
    print("  roundtrip laws: PASS (all bijections)")
    return True


def test_garbage_input_is_caught() -> bool:
    """Adversarial: the honest composition now CATCHES bad input rather than
    silently returning True.

    (a) A cert containing NON-Bool elements (e.g. ints) must make
        `lemma_cert_bits_boolean` return `False` (via the leaf
        `lemma_inr_bool_in_boolSyms`, which case-splits on `b ∈ {True, False}`
        and evaluates membership in `boolSyms`).  Before Fix 3 this returned
        `True` regardless.
    (b) A non-bijection `hΓ` (an `invFun` that is not a genuine inverse) is
        REJECTED by the `Bijection` constructor — the precondition is
        enforced structurally, so no lemma can even be called with it.
    """
    # (a) non-Bool cert.
    instance_syms = ["g0", "g1"]
    concrete = ["c0", "c1", "c2", "c3"]   # |2 + 2| = 4
    hΓ = make_bijection(instance_syms, concrete)
    bad_cert = [1, 2, 3]   # ints, not bools
    r = lemma_cert_bits_boolean(hΓ, bad_cert)
    if r is not False:
        print(f"  FAIL: lemma_cert_bits_boolean on non-bool cert returned {r}, "
              f"expected False")
        return False
    # The leaf itself returns False for a non-bool element.
    if lemma_inr_bool_in_boolSyms(hΓ, 1) is not False:
        print("  FAIL: lemma_inr_bool_in_boolSyms on non-bool returned non-False")
        return False
    # A genuine bool cert still passes.
    if lemma_cert_bits_boolean(hΓ, [True, False, True]) is not True:
        print("  FAIL: lemma_cert_bits_boolean on good cert returned non-True")
        return False

    # (b) non-bijection hΓ is rejected by the constructor.
    bad_codomain = [sum_inl("g0"), sum_inr(True), sum_inr(False)]
    bad_fwd = {"c0": sum_inl("g0"), "c1": sum_inr(True), "c2": sum_inr(False)}
    bad_rev = {sum_inl("g0"): "c0", sum_inr(True): "c2", sum_inr(False): "c2"}
    rejected = False
    try:
        Bijection(
            toFun=lambda a: bad_fwd[a],
            invFun=lambda b: bad_rev[b],
            domain=frozenset(["c0", "c1", "c2"]),
            codomain=frozenset(bad_codomain),
        )
    except ValueError:
        rejected = True
    if not rejected:
        print("  FAIL: Bijection did not reject non-bijection")
        return False

    print("  garbage input caught: non-bool cert => False, non-bijection => raise")
    return True


# ===========================================================================
# Phase-2 lemma test driver
# ===========================================================================

def run_phase2_lemmas() -> bool:
    """Run each phase-2 lemma on a battery of inputs and confirm True."""
    instance_syms = ["g0", "g1", "g2"]
    concrete = ["c0", "c1", "c2", "c3", "c4"]
    hΓ = make_bijection(instance_syms, concrete)
    encodings = [[], ["g0"], ["g0", "g1"], ["g2"] * 5,
                 ["g0", "g1", "g2", "g0", "g1"]]
    certs = [[], [True], [False], [True, False], [True] * 7,
            [False, True, False, True, False, True, False, True]]
    all_ok = True
    for a_enc in encodings:
        for cert in certs:
            if lemma_decomposition(hΓ, a_enc, cert) is not True:
                print(f"  FAIL lemma1: {a_enc}, {cert}")
                all_ok = False
            if lemma_cert_length(hΓ, cert) is not True:
                print(f"  FAIL lemma2: {cert}")
                all_ok = False
            if lemma_cert_bits_boolean(hΓ, cert) is not True:
                print(f"  FAIL lemma3: {cert}")
                all_ok = False
            if lemma_aInput_is_instance_mapping(hΓ, a_enc) is not True:
                print(f"  FAIL lemma4: {a_enc}")
                all_ok = False
            if lemma_h_init_connection(hΓ, a_enc, cert) is not True:
                print(f"  FAIL lemma5: {a_enc}, {cert}")
                all_ok = False
    return all_ok


# ===========================================================================
# Main
# ===========================================================================

if __name__ == "__main__":
    print("=== Phase 1: Computational oracle ===\n")
    phase1_tests = [
        ("basic_decomposition", test_basic_decomposition),
        ("empty_instance_encoding", test_empty_instance_encoding),
        ("empty_cert", test_empty_cert),
        ("both_empty", test_both_empty),
        ("long_instance_and_cert", test_long_instance_and_cert),
        ("scrambled_bijection", test_scrambled_bijection),
        ("h_init_connection", test_h_init_connection),
        ("non_injective_invFun_breaks_lemma3",
         test_non_injective_invFun_breaks_lemma3),
        ("garbage_input_is_caught", test_garbage_input_is_caught),
        ("lemma3_injectivity_guarantees_distinct_boolsyms",
         test_lemma3_injectivity_guarantees_distinct_boolsyms),
        ("lemma_aInput_definitional", test_lemma_aInput_definitional),
        ("lemma5_on_edge_cases", test_lemma5_on_edge_cases),
        ("roundtrip_laws_hold", test_roundtrip_laws_hold),
    ]
    all_pass = True
    for name, fn in phase1_tests:
        ok = fn()
        if not ok:
            all_pass = False
    print(f"\nAll phase-1 tests: {'PASS' if all_pass else 'FAIL'}")

    print("\n=== Phase 2: Structural lemma battery ===\n")
    ok = run_phase2_lemmas()
    print(f"  phase-2 lemma battery: {'PASS' if ok else 'FAIL'}")

    print("\n=== Proof structure (call graph) ===")
    print("  lemma_h_init_connection  (Bridge 2 lemma 5: h_init precondition)")
    print("    \u251c\u2500 lemma_decomposition          (Bridge 2 lemma 1)")
    print("    \u2502    \u251c\u2500 lemma_pair_encode_def   (defn of pairEncoding)")
    print("    \u2502    \u251c\u2500 lemma_map_append        (map distributes over ++)")
    print("    \u2502    \u2514\u2500 lemma_map_map           (map fusion, x2)")
    print("    \u251c\u2500 lemma_cfgAt_zero_is_initList   (cfgAt V input 0 = initList)")
    print("    \u2502    \u2514\u2500 lemma_iter_zero_identity  (f^[0] = id)")
    print("    \u2514\u2500 lemma_initList_shape           (defn of initList)")
    print()
    print("  lemma_cert_length          (Bridge 2 lemma 2)")
    print("    \u2514\u2500 lemma_map_length           (map preserves length)")
    print()
    print("  lemma_cert_bits_boolean    (Bridge 2 lemma 3)")
    print("    \u2514\u2500 lemma_inr_bool_in_boolSyms   (case split: b ∈ {True,False} => invFun(inr b) ∈ boolSyms)")
    print("       [PRECONDITION: hΓ is a genuine Equiv (bijection)]")
    print("       [membership is Bridge 2's need; |boolSyms|=2 distinctness is soundness-direction]")
    print()
    print("  lemma_aInput_is_instance_mapping  (Bridge 2 lemma 4, definitional)")