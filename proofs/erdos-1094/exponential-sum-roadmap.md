# Exponential Sum Infrastructure Roadmap

## Goal
Eliminate the `large_n_smooth_case` axiom from Erdős 1094 by formalizing enough
analytic machinery to prove: for k ≥ K₀ and n > k² with ⌊n/k⌋ k-smooth,
∃ prime p ≤ ⌊n/k⌋ with p | C(n,k).

This requires beating the √R discrepancy barrier. The only known technique:
exponential sum estimates over digit-constrained sets (Konyagin 1999).

## What Mathlib Already Has (as of v4.27.0)

### ✅ Solid foundations
- **Dirichlet characters**: `DirichletCharacter`, level/conductor, primitivity,
  orthogonality, Gauss sums, bounds (`‖χ a‖ ≤ 1`)
- **Additive characters**: `AddChar`, `stdAddChar` on `ZMod N`, primitive characters
- **Discrete Fourier transform**: `ZMod.dft`, inversion formula (`dft_dft`),
  Parseval, connection to `Fourier.fourierIntegral`
- **Gauss sums**: `gaussSum`, product formula `gaussSum * gaussSum⁻¹ = card`,
  square formula for quadratic characters
- **Lucas' theorem**: `Choose.choose_modEq_choose_mod_mul_choose_div`
- **Nat.digits**: Base representation, digit extraction, reconstruction
- **Smooth numbers**: `Nat.smoothNumbers`, `Nat.factoredNumbers`, cardinality bounds
- **Bertrand's postulate**: `Nat.exists_prime_lt_and_le`
- **L-series**: Convergence, convolution, Dirichlet's theorem (primes in AP!)
- **Fourier analysis**: Transform on ℝ, AddCircle, ZMod; Poisson summation,
  Riemann-Lebesgue, L² theory
- **Pontryagin duality**: For finite abelian groups

### ❌ Missing entirely
- **Exponential sum bounds** (Weyl, van der Corput, Vinogradov)
- **Large sieve inequality**
- **Erdős-Turán discrepancy inequality**
- **Short interval results for primes** (Baker-Harman-Pintz)
- **Bombieri-Vinogradov theorem**
- **Character sums over structured sets** (intervals, digit-constrained sets)
- **Weil bound for character sums**
- **Sieve methods** (Selberg, combinatorial, beta sieve)

## Architecture

```
Layer 0: Foundations (HAVE)        Layer 3: Konyagin's Core
├─ AddChar, DirichletChar          ├─ Char sums over digit sets
├─ ZMod.dft, Gauss sums           ├─ Product set discrepancy
├─ Lucas, Nat.digits               ├─ Short interval primes
└─ smoothNumbers, Bertrand         └─ g(k) ≥ exp(c log²k)
                                         |
Layer 1: Exponential Sums          Layer 4: B3b Closure
├─ Weyl differencing               ├─ Kummer + gap prime density
├─ van der Corput A/B              ├─ Digit-constrained equidistr.
├─ Geometric sum bounds            └─ large_n_smooth_case PROVED
└─ Complete sum estimates                |
                                   Layer 5: Axiom Elimination
Layer 2: Analytic NT Tools         └─ erdos_1094 with 1 axiom
├─ Large sieve inequality               (konyagin_1999 only)
├─ Erdős-Turán inequality               or 0 axioms if Layer 3
├─ Bombieri-Vinogradov                  fully formalized
└─ Character sum bounds
```

## Phase 1: Exponential Sum Foundations (~2-4 weeks)

### 1.1 Geometric sum bounds
**File**: `botlib/Analysis/GeomSum.lean`
**Status**: Partially in Mathlib (`geom_sum_eq`), need complex exponential version

```
-- Target lemmas:
lemma exp_sum_bound (N : ℕ) (θ : ℝ) (hθ : θ ≠ 0) :
    ‖∑ n in range N, cexp (2 * π * I * n * θ)‖ ≤ 1 / ‖Real.sin (π * θ)‖

lemma exp_sum_interval (a b : ℤ) (q : ℕ) (hq : 0 < q) (ξ : ZMod q) (hξ : ξ ≠ 0) :
    ‖∑ n in Icc a b, stdAddChar (ξ * n)‖ ≤ q / (2 * ‖Real.sin (π * ξ.val / q)‖)
```

**Dependencies**: `Mathlib.Analysis.SpecialFunctions.Complex.Circle`, geometric series
**Difficulty**: Low — straightforward complex analysis
**Reuse value**: High — used everywhere in analytic NT

### 1.2 Weyl differencing
**File**: `botlib/Analysis/WeylDifferencing.lean`

```
-- Weyl's inequality: bound exponential sums by differenced sums
theorem weyl_differencing (f : ℕ → ℝ) (N H : ℕ) :
    ‖∑ n in range N, cexp (2 * π * I * f n)‖² ≤
    (N + H) / H * ∑ h in range H, ‖∑ n in range N, cexp (2 * π * I * (f (n+h) - f n))‖
```

**Dependencies**: 1.1
**Difficulty**: Medium — standard but fiddly
**Reuse value**: Very high — fundamental tool

### 1.3 Van der Corput method
**File**: `botlib/Analysis/VanDerCorput.lean`

```
-- Process A (Weyl step) and Process B (Poisson step)
-- Process A: reduce degree of phase function
-- Process B: exploit spacing via Poisson summation

theorem van_der_corput_A (f : ℝ → ℝ) (a b : ℝ) (λ : ℝ) :
    -- If |f''(x)| ~ λ on [a,b], then |Σ e(f(n))| ≤ C * (b-a) * √λ + C / √λ

theorem van_der_corput_B (f : ℝ → ℝ) (a b : ℝ) (λ : ℝ) :
    -- If |f'(x)| ~ λ on [a,b], then |Σ e(f(n))| ≤ C * ((b-a)*λ + 1/λ)
```

**Dependencies**: 1.1, 1.2, Poisson summation (in Mathlib)
**Difficulty**: Medium-hard
**Reuse value**: Very high

## Phase 2: Character Sum Infrastructure (~2-4 weeks)

### 2.1 Complete character sums
**File**: `botlib/NumberTheory/CharacterSumBounds.lean`

```
-- Weil bound for multiplicative character sums
-- (This is deep — may need to axiomatize initially)
axiom weil_bound (p : ℕ) [hp : Fact p.Prime] (χ : MulChar (ZMod p) ℂ)
    (hχ : χ ≠ 1) (f : ZMod p → ℂ) (hf : polynomial of degree d) :
    ‖∑ x, χ x * f x‖ ≤ (d - 1) * Real.sqrt p

-- Pólya-Vinogradov inequality (character sums over intervals)
theorem polya_vinogradov (q : ℕ) [hq : Fact (Nat.Prime q)]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (M N : ℕ) :
    ‖∑ n in Icc M (M + N), χ n‖ ≤ Real.sqrt q * Real.log q
```

**Dependencies**: Gauss sums (in Mathlib), 1.1
**Difficulty**: Pólya-Vinogradov is medium. Full Weil bound is very hard (algebraic geometry).
**Strategy**: Prove Pólya-Vinogradov from Gauss sums. Axiomatize Weil if needed.
**Reuse value**: Extremely high

### 2.2 Character sums over digit-constrained sets
**File**: `botlib/NumberTheory/DigitCharacterSum.lean`

This is the KEY new tool. Konyagin needs bounds on sums like:

```
∑_{n ∈ S_p} χ(n)    where S_p = {n ∈ ZMod(p^d) : digit_i(n) ≥ digit_i(k) ∀i}
```

The digit-constrained set S_p is a Cartesian product of intervals (one per digit
position), so the character sum FACTORS:

```
∑_{n ∈ S_p} e(ξn/p^d) = ∏_{i=0}^{d-1} (∑_{a=k_i}^{p-1} e(ξ a p^i / p^d))
                       = ∏_{i=0}^{d-1} (∑_{a=k_i}^{p-1} e(ξ a / p^{d-i}))
```

Each factor is a partial geometric sum — bounded by 1.1!

```
-- The factorization lemma
theorem digit_constrained_char_sum_eq_prod (p : ℕ) [hp : Fact p.Prime]
    (d : ℕ) (k : ℕ) (ξ : ZMod (p^d)) :
    ∑ n in digitDominators p d k, stdAddChar (ξ * n) =
    ∏ i in range d, ∑ a in Icc (k / p^i % p) (p - 1),
        stdAddChar (ξ * a * p^i)

-- The bound
theorem digit_constrained_char_sum_bound (p : ℕ) [hp : Fact p.Prime]
    (d : ℕ) (k : ℕ) (ξ : ZMod (p^d)) (hξ : ξ ≠ 0) :
    ‖∑ n in digitDominators p d k, stdAddChar (ξ * n)‖ ≤
    ∏ i in range d, min (p - k / p^i % p) (1 / (2 * |sin(π * ξ.val * p^i / p^d)|))
```

**Dependencies**: 1.1, `ZMod.dft`, our `Kummer.lean`
**Difficulty**: Medium — the factorization is the key insight, bounds follow from 1.1
**Reuse value**: Novel contribution — not in literature as a standalone lemma
**THIS IS THE TOOL WE'RE BUILDING**

### 2.3 Product set discrepancy
**File**: `botlib/Analysis/ProductSetDiscrepancy.lean`

Using 2.2, bound the discrepancy of the CRT product set V = ∏ S_p in intervals:

```
-- For V = ∏ S_p ⊂ ℤ/Q (product set via CRT):
-- |V ∩ [a, a+L)| = L * |V|/Q + E
-- where E is bounded using the factored Fourier coefficients

theorem product_set_discrepancy (Q : ℕ) (ps : Finset ℕ) (hcop : pairwise coprime)
    (S : ∀ p ∈ ps, Finset (ZMod p)) (L : ℕ) (a : ZMod Q) :
    |card (productSet S ∩ interval a L) - L * (∏ p, card (S p)) / Q| ≤
    discrepancyBound ps S L
```

The discrepancy bound involves summing over non-zero Fourier modes, where each
mode's contribution factors as a product of digit-constrained character sums.

**Dependencies**: 2.2, CRT (`ZMod.chineseRemainder`)
**Difficulty**: Hard — this is where the real work is
**Reuse value**: Very high — applies to any multi-base digit problem

## Phase 3: Konyagin's Argument (~4-8 weeks)

### 3.1 Baker-Harman short interval primes
**File**: `botlib/NumberTheory/BakerHarman.lean`

```
-- Baker-Harman-Pintz (2001): primes in short intervals
-- For x sufficiently large: π(x + x^{0.525}) - π(x) > 0

-- We axiomatize the effective version needed:
axiom baker_harman_short_intervals (x : ℝ) (hx : x ≥ x₀) :
    ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + x ^ (0.525 : ℝ)
```

**Strategy**: Axiomatize. Full proof requires zero-free regions of ζ(s), which is
a multi-year Mathlib project. The axiom is justified: BHP 2001 is one of the most
verified results in analytic NT.
**Reuse value**: Extremely high

### 3.2 Konyagin's Theorem 2 (rational approximation)
**File**: Already scaffolded in `KonyaginTheorem2.lean`

Schmidt's subspace theorem gives: the number of "good" rational approximations
to digit-constrained sets is bounded. Currently axiomatized.

**Strategy**: Keep as axiom. Schmidt's theorem requires algebraic geometry.
**Reuse value**: High (Diophantine approximation)

### 3.3 Konyagin's Theorem 1 (main bound)
**File**: Already scaffolded in `KonyaginTheorem1.lean` (10 sorrys)

With the tools from Phases 1-2, the 10 sorrys become approachable:
- `digit_dom_rational_approx`: Uses 2.2 (digit char sum factorization)
- `choose_r_threshold`: Uses 2.3 (product set discrepancy)  
- `build_set_S_lower_bound`: Uses 3.1 (short interval primes)
- `bound_term1/2/3`: Uses 1.2-1.3 (Weyl/vdC)
- `key_exponent_bound`: Algebraic manipulation
- `konyagin_theorem1`: Assembly

**Dependencies**: Everything above
**Difficulty**: Hard but tractable — each sorry maps to a specific tool

### 3.4 B3b closure
**File**: `problems/NumberTheory/Erdos1094/SmoothCase.lean` (extend)

With Konyagin's theorem formalized:
1. For k ≥ K₀: g(k) > k², so no exceptions with n ≤ g(k)
2. For n > g(k): Konyagin's construction shows the digit-constrained set
   in [kM, kM+k) is empty (discrepancy bound from 2.3 beats the count)
3. Combined: `large_n_smooth_case` is PROVED

```
-- The final theorem, replacing the axiom
theorem large_n_smooth_case (n k : ℕ) (hk : 2 ≤ k) (hn : k * k < n)
    (hsmooth : n / k ∈ Nat.smoothNumbers (k + 1)) (hndvd : ¬ k ∣ n) :
    (n.choose k).minFac ≤ n / k := by
  -- Use product_set_discrepancy to show digit-domination set
  -- misses [kM, kM+k), then conclude via Kummer
```

## Axiom Budget After Full Completion

| Axiom | Status | Justification |
|-------|--------|---------------|
| `konyagin_1999` | **ELIMINATED** | Proved via Layers 1-3 |
| `large_n_smooth_case` | **ELIMINATED** | Proved via 3.4 |
| `baker_harman_short_intervals` | **NEW** | Citation axiom (BHP 2001) |
| `weil_bound` | **MAYBE** | May be needed, may be avoidable |
| `konyagin_theorem2` | **KEPT** | Citation axiom (Schmidt subspace) |

Net effect: 2 load-bearing axioms → 2-3 citation axioms, but ALL at the level
of major published theorems (not conjectures). The logical chain from axioms to
Erdős 1094 is fully machine-verified.

## What This Contributes to Mathlib/OpenLemma

Independent of Erdős 1094, this roadmap produces:

1. **Exponential sum library** — Weyl, van der Corput, geometric sum bounds
2. **Pólya-Vinogradov inequality** — character sums over intervals
3. **Character sums over digit-constrained sets** — novel, not in literature as standalone
4. **Product set discrepancy bounds** — multi-base digit problems
5. **Large sieve inequality** (if added)

These are **reusable tools** for any analytic NT formalization. They don't exist
in Mathlib today. Building them is a contribution regardless of whether we
finish Erdős 1094.

## Estimated Timeline

| Phase | Duration | Parallelizable | Agent-suitable |
|-------|----------|----------------|----------------|
| 1.1 Geometric sums | 3-5 days | — | Yes |
| 1.2 Weyl differencing | 5-7 days | After 1.1 | Yes |
| 1.3 Van der Corput | 7-10 days | After 1.2 | Partially |
| 2.1 Pólya-Vinogradov | 5-7 days | After 1.1 | Yes |
| 2.2 Digit char sums | 7-10 days | After 1.1 | Yes (key file) |
| 2.3 Product discrepancy | 10-14 days | After 2.2 | Partially |
| 3.1 Baker-Harman axiom | 1 day | Independent | Yes |
| 3.2-3.3 Konyagin | 3-6 weeks | After Phase 2 | With guidance |
| 3.4 B3b closure | 3-5 days | After 3.3 | Yes |

**Total**: 2-4 months with agents. Phase 1 + 2.2 are the highest-value,
most parallelizable, most agent-suitable pieces.

## Recommended First Step

Start with **2.2 (digit-constrained character sums)**. This is:
- The most NOVEL piece (not in literature as a standalone lemma)
- Directly uses our existing `Kummer.lean` infrastructure
- The factorization insight is clean and well-suited to Lean
- It's the core tool that everything downstream depends on
- Only needs 1.1 (geometric sum bounds) as a dependency

Build 1.1 and 2.2 in parallel. That gives us the new mathematical tool
that doesn't exist anywhere — in any proof assistant or any textbook.
We're not just formalizing known math. We're building new infrastructure.
