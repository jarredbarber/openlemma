# Konyagin (1999) Formalization Plan

**Status:** Planning document (NOT for commit to paywalled content)
**Goal:** Identify minimal axiom set and dependency map for formalizing Theorem 1

---

## 0. Paper Structure

```
Theorem 1: g(k) ≥ exp(c₁ log²k)
    │
    ├── Theorem 2: Lattice point bound near smooth curves
    │       │
    │       ├── Lemma 2: Small-coefficient vanishing (THE HARD PART)
    │       │       │
    │       │       ├── Lemma 1: Factorial product bound (elementary)
    │       │       └── Schmidt [9] §4: Rational subspace theory
    │       │               ├── Height of rational subspaces
    │       │               ├── H(U⊥) = H(U)
    │       │               └── Theorem 2E + Lemma 4A: Successive minima bounds
    │       │
    │       └── Taylor approximation (elementary calculus)
    │
    └── Baker-Harman [1]: Primes in short intervals
            └── α = 0.465: for x^(1-α) ≤ y ≤ x, π(x+y) - π(x) ≫ y/log x
```

---

## 1. Layer-by-Layer Analysis

### Layer 1: Lemma 2 (§1, pages 44–48) — Lattice Geometry

**Statement.** For integer r ≥ 1, s = 2r, N ≥ s-1, integers 0 ≤ u₁ < ... < uₛ ≤ N, and positive integers w₁,...,wₛ ≤ W, there exist integers a₁,...,aₛ such that:
- (5): Σᵢ aᵢwᵢuᵢʲ = 0 for j = 0,...,r-1
- (6): Σᵢ aᵢwᵢuᵢʳ ≠ 0 (excess 0)
- Bound: |aᵢ| ≤ (c₉N/r)^(r-1) · W for all i

**Proof ingredients:**
1. **Lemma 1** (page 43-44): log ∏ⱼ₌₀ʳ⁻¹ j! = r(r-1)/2 · log(r/e^c₈). Elementary.
2. **Polynomial basis** pⱼ(u) = (u choose j) = ∏ᵢ₌₀ʲ⁻¹(u-i)/j!. Integer-valued for integer u.
3. **Rational subspace U ⊂ ℝˢ** spanned by vectors (pⱼ(u₁)w₁,...,pⱼ(uₛ)wₛ), j=0,...,r-1. dim U = r.
4. **Height bound** H(U) from product of basis vector norms. Uses (7) and (8).
5. **Annihilator U⊥**: codim r, H(U⊥) = H(U) by Schmidt [9, p.10].
6. **Successive minima** of U⊥ ∩ ℤˢ: Theorem 2E + Lemma 4A of [9, Ch.1] gives ∏|a^(j)|_∞ ≤ c · H(U⊥).
7. **Excess argument**: Among basis vectors a^(1),...,a^(r) of U⊥, at least one has excess 0.
8. **Norm bound propagation** (13): |a^(m)|_∞ ≤ (Nˡ/l!) · |a^(m-l)|_∞ via component-wise multiplication by pₗ(u).

**Schmidt [9] dependencies (specific results used):**
- **Definition of H(U)**: Determinant of lattice U ∩ ℤˢ in U. [9, p.9]
- **H(U⊥) = H(U)**: [9, p.10, eq.(10)]
- **Theorem 2E**: Successive minima bound: ∏ᵢ₌₁ʳ λᵢ ≤ c(s) · H(L) for a lattice L ⊂ ℤˢ of rank r
- **Lemma 4A**: Connects successive minima of basis vectors to lattice determinant
- **Remark 4E**: Direct consequence giving (12)

**Difficulty for Lean:** HIGH. This requires:
- Lattice theory in ℤˢ (sublattices, determinants, successive minima)
- Rational subspaces and their heights
- The duality H(U⊥) = H(U)
- Minkowski-type successive minima bounds

**Mathlib status:** Mathlib has basic lattice theory (`Submodule`, `Module.Free`), but NOT:
- Heights of rational subspaces in the Schmidt sense
- Successive minima (Minkowski's second theorem)
- The specific duality theorem H(U⊥) = H(U)

**Recommendation:** CITATION AXIOM for the full Lemma 2.

### Layer 2: Theorem 2 (§2, pages 48–51) — Lattice Points Near Smooth Curves

**Statement.** Let r ≥ 1, N > 0, W ≥ 1, f ∈ Cʳ⁺¹[0,N], Dᵣ > 0, Dᵣ₊₁ > 0, δ > 0, λ ≥ 1. Suppose |f⁽ʳ⁾(u)| ≥ Dᵣ and |f⁽ʳ⁺¹⁾(u)| ≤ Dᵣ₊₁ for all u ∈ [0,N]. Let S ⊂ [0,N] ∩ ℤ with |f(u) - v/w| < δ for some v ∈ ℤ, w ∈ ℕ, w ≤ W for each u ∈ S. Then:

|S| < c₁₀N((DᵣW²)^(1/(2r-1)) + (δW²/Dᵣ)^(1/(r-1)) + (Dᵣ₊₁W²/Dᵣ)^(1/(2r))) + 2rλ

**Proof structure:**
1. **Case λ = 1, N ≤ N₀:** Assume |S| ≥ 2r. Pick u₁ < ... < u₂ᵣ from S. Apply Lemma 2 to get coefficients a₁,...,a₂ᵣ.
2. **Form I = Σ aᵢwᵢf(uᵢ):** Split into I₁ (Taylor main part) and R (remainder).
3. **Lower bound |I₁|:** By (5), Taylor terms below degree r vanish. The degree-r term is f⁽ʳ⁾(0)/r! · Σ aᵢwᵢpᵣ(uᵢ), which is a nonzero integer (by excess 0). So |I₁| ≥ Dᵣ/2.
4. **Upper bound |R|:** Taylor remainder ≤ Dᵣ₊₁ · Nʳ⁺¹/(r+1)!, plus the δ-approximation error ≤ δ · Σ|aᵢ|.
5. **Contradiction:** For N ≤ N₀ (chosen so |R| < |I₁|): 0 < |I| < 1 but I is an integer.
6. **Case λ = 1, N > N₀:** Cover [0,N] by intervals of length N₀+1, apply to each.
7. **Case λ > 1:** Reduce to λ = 1 by taking arithmetic progressions mod ⌊λ⌋.

**Dependencies on Lemma 2:** Only the bound |aᵢ| ≤ (c₉N/r)^(r-1) · W and the vanishing/non-vanishing conditions (5)+(6).

**Difficulty for Lean:** MEDIUM-HIGH if Lemma 2 is axiomatized. The proof is a carefully-executed chain of inequalities. Needs:
- Taylor's theorem with remainder (Mathlib: `taylor_mean_remainder` or similar)
- Integer-valued polynomial pᵣ at integer points (Mathlib: binomial coefficient integrality)
- Interval covering argument (elementary)
- Arithmetic progression reduction (elementary)

**Mathlib status:**
- Taylor's theorem: Available (`MeanValueTheorem`, `taylor_mean_remainder`)
- Binomial coefficient integrality: Available (`Nat.choose`)
- Real analysis (derivatives, C^r functions): Available
- The specific inequality chain: Must be hand-proved

**Recommendation:** PROVE from Lemma 2 axiom, with possible sub-axiom for specific Taylor remainder forms.

### Layer 3: Theorem 1 (pages 51–54) — Application to g(k)

**Statement.** g(k) ≥ exp(c₁ log²k).

**Proof structure:**
1. **Choose parameters:** β with 0 < β < 0.9α, (3+β)/6 < 1-α. Set γ = β/10, W = k^γ.
2. **Build set S:** For each w ∈ [2, W], primes p ∈ (k/w, (k+k^(1-β))/w), form u = wp ∈ (k, k+k^(1-β)). By Baker-Harman: |S| ≥ c₁₁ k^(1-β).
3. **Apply Theorem 2** with h(u) = n/u, f(u) = h(k+u), δ = k^(-β), N = k^(1-β):
   - Dⱼ = |h⁽ʲ⁾(k)| = nj!/k^(j+1)
   - Choose r = minimal j with Dⱼ ≤ k^(-β). Get 2 ≤ r ≤ 2c₃ log k.
   - From (26): n < exp(c₃ log²k) gives Dᵣ₀ < k^(-β) for r₀ = ⌊2c₃ log k⌋.
4. **Estimate all terms in (4):** Each of the three terms in Theorem 2's bound is ≤ k^(-γ/r). Combined: |S| ≤ c₆Nk^(-γ/r) + 2rλ.
5. **Contradiction:** k^(-γ/r) ≤ k^(-γ/(2c₃ log k)) = c₁₁/5 (by choice of c₃). And rλ ≤ (c₁₁/5)k^(1-β). So |S| ≤ c₁₁k^(1-β), contradicting |S| > c₁₁k^(1-β).

**Dependencies:**
- Theorem 2 (full statement)
- Baker-Harman [1]: For α = 0.465, x^(1-α) ≤ y ≤ x ⟹ π(x+y) - π(x) ≫ y/log x
- Kummer's theorem: minFac C(n,k) > k ⟹ digit domination ⟹ {n/(wp)} ≥ {k/(wp)} ⟹ |n/u - v/w| < k^(-β) for appropriate v
- Erdős-Lacampagne-Selfridge [4]: g(k) > c₂k²/log k (bootstrapping lower bound)

**Difficulty for Lean:** MEDIUM if Theorem 2 and Baker-Harman are axiomatized. The proof is a parameter-optimization argument with explicit inequalities. The key steps are:
- Constructing the set S (counting primes in short intervals)
- Choosing r as the threshold where Dᵣ drops below k^(-β)
- Chain of inequalities (30)–(43) bounding each term in Theorem 2's output

**Mathlib status:**
- Prime counting function: `Nat.Prime` available, `Nat.primeCounting` exists
- Real analysis (exp, log, powers): Available
- The specific inequality chain: Must be hand-proved
- Baker-Harman: NOT in Mathlib (deep analytic number theory)
- ELS93 lower bound g(k) > c₂k²/log k: NOT in Mathlib

---

## 2. Dependency Map

```
                    ┌─────────────────────────┐
                    │     Theorem 1            │
                    │  g(k) ≥ exp(c₁ log²k)   │
                    └────────┬────────────────┘
                             │
              ┌──────────────┼──────────────┐
              │              │              │
              ▼              ▼              ▼
     ┌────────────┐  ┌─────────────┐  ┌──────────────┐
     │ Theorem 2  │  │Baker-Harman │  │ Kummer + ELS │
     │ Lattice pt │  │ α = 0.465   │  │  digit dom   │
     │ near curve │  │CITATION AXIOM│  │ PROVABLE     │
     └─────┬──────┘  └─────────────┘  └──────────────┘
           │
     ┌─────┴─────┐
     │            │
     ▼            ▼
┌─────────┐  ┌──────────┐
│ Lemma 2 │  │  Taylor   │
│ Small   │  │ remainder │
│ coeffs  │  │ MATHLIB   │
│CITE AXIOM│  └──────────┘
└────┬────┘
     │
     ▼
┌──────────────┐
│ Schmidt [9]  │
│ Rational     │
│ subspaces    │
│ NOT IN LEAN  │
└──────────────┘
```

---

## 3. Minimal Axiom Set

### Option A: Axiomatize Theorem 1 directly (1 axiom)

```lean
/-- Konyagin (1999), Theorem 1. -/
axiom konyagin_gk_bound : ∃ c₁ : ℝ, c₁ > 0 ∧
    ∀ k : ℕ, 2 ≤ k → (gFunction k : ℝ) ≥ Real.exp (c₁ * (Real.log k) ^ 2)
```

**Pro:** Minimal, clean, 1 axiom.
**Con:** Hides ALL the proof structure. No intermediate results available.

### Option B: Axiomatize Lemma 2 + Baker-Harman (2 axioms), prove Theorem 2 and Theorem 1

```lean
/-- Konyagin (1999), Lemma 2. Small integer coefficients with vanishing conditions.
    For s = 2r points with weights ≤ W, there exist integer coefficients satisfying
    polynomial vanishing up to degree r-1, non-vanishing at degree r,
    with |aᵢ| ≤ (c₉N/r)^(r-1) · W. -/
axiom konyagin_lemma2 (r : ℕ) (hr : 1 ≤ r) (N : ℕ) (hN : 2 * r ≤ N + 1)
    (u : Fin (2 * r) → ℕ) (hu_mono : StrictMono u) (hu_bound : ∀ i, u i ≤ N)
    (w : Fin (2 * r) → ℕ) (hw_pos : ∀ i, 0 < w i) (hw_bound : ∀ i, w i ≤ W) :
    ∃ a : Fin (2 * r) → ℤ,
      (∀ j : Fin r, ∑ i, a i * w i * (u i : ℤ) ^ (j : ℕ) = 0) ∧  -- vanishing (5)
      (∑ i, a i * w i * (u i : ℤ) ^ r ≠ 0) ∧                      -- non-vanishing (6)
      (∀ i, |a i| ≤ (c₉ * N / r) ^ (r - 1) * W)                   -- size bound

/-- Baker-Harman (1996). Primes in short intervals.
    For α = 0.465: if x is large enough and y ≥ x^(1-α),
    then π(x+y) - π(x) ≫ y/log x. -/
axiom baker_harman_primes_short_interval :
    ∃ (C : ℝ) (x₀ : ℕ), C > 0 ∧ ∀ x : ℕ, x₀ ≤ x → ∀ y : ℝ,
      (x : ℝ) ^ (0.535 : ℝ) ≤ y → y ≤ x →
      C * y / Real.log x ≤ (Nat.primeCounting (x + ⌊y⌋₊) - Nat.primeCounting x : ℝ)
```

**Pro:** Allows proving Theorem 2 and Theorem 1 in Lean. Intermediate results reusable.
**Con:** 2 axioms instead of 1. Lemma 2 signature is complex. Proving Theorem 2 is ~300 lines of careful inequality work.

### Option C: Axiomatize Theorem 2 + Baker-Harman (2 axioms), prove Theorem 1

```lean
/-- Konyagin (1999), Theorem 2. Bound on integer points near a smooth curve
    with rational approximations of bounded denominator. -/
axiom konyagin_theorem2 (r : ℕ) (hr : 1 ≤ r) (N W : ℝ) (hN : 0 < N) (hW : 1 ≤ W)
    (f : ℝ → ℝ) (hf_smooth : ContDiff ℝ (r + 1) f)
    (Dr Dr1 : ℝ) (hDr : 0 < Dr) (hDr1 : 0 < Dr1) (δ : ℝ) (hδ : 0 < δ) (λ : ℝ) (hλ : 1 ≤ λ)
    (hf_lower : ∀ u ∈ Set.Icc 0 N, Dr ≤ |iteratedDeriv r f u|)
    (hf_upper : ∀ u ∈ Set.Icc 0 N, |iteratedDeriv (r + 1) f u| ≤ Dr1)
    (S : Finset ℤ) (hS_range : ∀ u ∈ S, (0 : ℝ) ≤ u ∧ (u : ℝ) ≤ N)
    (hS_approx : ∀ u ∈ S, ∃ v : ℤ, ∃ w : ℕ, 0 < w ∧ w ≤ W ∧ |f u - v / w| < δ) :
    (S.card : ℝ) < c₁₀ * N * ((Dr * W ^ 2) ^ (1 / (2 * r - 1))
        + (δ * W ^ 2 / Dr) ^ (1 / (r - 1))
        + (Dr1 * W ^ 2 / Dr) ^ (1 / (2 * r))) + 2 * r * λ

-- Baker-Harman as above
```

**Pro:** Theorem 2 is the reusable core result (useful beyond Erdős 1094). Proving Theorem 1 from it is ~150 lines.
**Con:** 2 axioms. Theorem 2 signature is complex but self-contained.

---

## 4. Recommendation: Option C (Theorem 2 + Baker-Harman)

**Rationale:**

1. **Theorem 2 is the right abstraction level.** It's a self-contained result about lattice points near smooth curves. It has applications beyond Erdős 1094 (Filaseta-Trifonov type problems). Axiomatizing it preserves the most reusable mathematics.

2. **Proving Theorem 1 from Theorem 2 is feasible.** The proof (pages 51-54) is a parameter optimization with explicit inequalities. No deep theory — just choosing β, γ, W, r and computing bounds. Estimated: ~150-200 lines of Lean.

3. **Lemma 2 is too deep to formalize.** It requires Schmidt's rational subspace theory (heights, successive minima, duality), which is absent from Mathlib and would require 1000+ lines of infrastructure. Not worth building for a single application.

4. **Baker-Harman is standard.** The prime-in-short-intervals result is deep (sieve methods + Weil bound) but well-established. Any α < 1/2 suffices for the proof structure; 0.465 is the current record but even α = 0.499 would work.

---

## 5. What Proving Theorem 1 from the Axioms Looks Like

### 5.1 Definitions needed

```lean
/-- g(k) = least n > k+1 with minFac C(n,k) > k, or 0 if none exists -/
noncomputable def gFunction (k : ℕ) : ℕ := ...  -- already have this or similar

/-- The fractional part connection: minFac > k ⟹ digit domination ⟹ closeness to rationals -/
lemma digit_dom_rational_approx (k n : ℕ) (hk : 2 ≤ k) (hn : k + 1 < n)
    (h_minFac : (Nat.choose n k).minFac > k) (w : ℕ) (hw : 2 ≤ w) (hw' : w ≤ W)
    (p : ℕ) (hp : p.Prime) (hp_range : k / w < p ∧ p ≤ (k + k^(1-β)) / w) :
    ∃ v : ℤ, |n / (w * p : ℝ) - v / w| < k^(-β) := ...
```

### 5.2 Proof outline (~150 lines)

```
-- 1. Fix k large, assume n < exp(c₃ log²k) and minFac > k
-- 2. Define h(u) = n/u, compute Dⱼ = nj!/k^(j+1)
-- 3. Choose r = min{j : Dⱼ ≤ k^(-β)}. Show 2 ≤ r ≤ 2c₃ log k.
-- 4. Build S via Baker-Harman: |S| > c₁₁ k^(1-β)
-- 5. By digit_dom_rational_approx: each u ∈ S has |f(u) - v/w| < δ
-- 6. Apply Theorem 2 with computed Dr, Dr+1, δ, W, λ, N
-- 7. Bound each term: all ≤ k^(-γ/r) (inequalities (36)-(40))
-- 8. Get |S| ≤ c · k^(1-β) · k^(-γ/r) + 2rλ < c₁₁ k^(1-β)
-- 9. Contradiction with step 4
```

### 5.3 Hard spots in the proof of Theorem 1

| Step | Content | Difficulty | Notes |
|------|---------|-----------|-------|
| 2 | Dⱼ computation | Easy | Derivative of n/u |
| 3 | r choice | Easy | Threshold search |
| 4 | |S| lower bound | AXIOM | Baker-Harman |
| 5 | Rational approx | Medium | Kummer + fractional parts |
| 7 | Three-term bound | Medium-Hard | Inequalities (36)-(40), each ~10 lines |
| 8 | Combining | Easy | Arithmetic |

The hardest provable part is step 7: the chain of exponent manipulations in (36)-(40). Each involves expressions like k^(-β/(3r-2)) · k^(β/(5r-5)) and requires careful tracking of exponents. This is tedious but mechanical.

---

## 6. What We Get for Erdős 1094

With the 2 axioms (Theorem 2 + Baker-Harman):

1. **Prove Theorem 1:** g(k) ≥ exp(c₁ log²k) (~150-200 lines)
2. **Derive g(k) > k²:** Elementary from Theorem 1 (already in Lean)
3. **Eliminate axiom 1** (`crt_density_from_asymptotic`): g(k) > k² means no exceptions in [2k, k²] for large k

**Final axiom count for Erdős 1094:** 3 axioms total
- Konyagin Theorem 2 (lattice points near curves)
- Baker-Harman (primes in short intervals)
- `large_n_smooth_case` (the smooth M case, now reduced to k ∈ {2,...,8})

Or, if we use **Option A** (axiomatize Theorem 1 directly): 2 axioms
- Konyagin Theorem 1
- `large_n_smooth_case`

---

## 7. Current State and Path Forward

### Current: Option A (Baseline)

**Already in place:** Theorem 1 is axiomatized as `konyagin_gk_bound` or similar. The corollary g(k) > k² for large k is proved in ~20 lines. This gives us 1 axiom for the k > 700 case.

**Status:** Working baseline. Erdős 1094 uses this axiom to eliminate exceptions for k > 700.

### Path Forward: Adding Proof Structure

The current axiom is from an obscure paper (Konyagin 1999, Mathematika). Making the proof structure explicit in Lean would:
1. Connect Konyagin's technique to standard tools (lattice point counting, smooth approximation)
2. Make Theorem 2 reusable (useful for other Filaseta-Trifonov type problems)
3. Demonstrate the parameter optimization strategy

**Two options for elaboration:**

| | Option B | Option C |
|---|---|---|
| **Axioms added** | Lemma 2 + Baker-Harman | Theorem 2 + Baker-Harman |
| **Lines to add** | ~500 | ~200 |
| **What's proved** | Theorem 2 + Theorem 1 | Theorem 1 only |
| **Reusability** | High (Lemma 2 for lattice work) | High (Theorem 2 for curve problems) |
| **Difficulty** | Very hard (Lemma 2 signature complex) | Medium (inequality chains) |
| **Justification** | Makes lattice geometry explicit | Makes smooth curve technique explicit |

### Recommendation: Option C (if elaboration desired)

**Rationale:**
- **Option C adds the most value per line of code.** Theorem 2 is the reusable abstraction (lattice points near smooth curves with rational approximations). Proving Theorem 1 from it (~200 lines) demonstrates the optimization technique.
- **Lemma 2 (Option B) pushes the black box deeper** but doesn't add proportional value. The lattice geometry in Lemma 2 is a 1-off application of Schmidt's theory. Unless we're building a lattice geometry library, stopping at Theorem 2 is cleaner.
- **Theorem 2 is well-scoped.** Its statement is self-contained (smooth function f, derivatives Dr, Dr+1, approximation δ, bound on |S|). It doesn't leak implementation details.

### Timeline Estimate (Option C)

| Task | Lines | Difficulty | Time |
|------|-------|-----------|------|
| State Theorem 2 axiom | ~20 | Easy | 30 min |
| State Baker-Harman axiom | ~15 | Easy | 30 min |
| Helper: digit_dom_rational_approx | ~50 | Medium | 2-3 hours |
| Compute Dr, Dr+1, choose r | ~40 | Easy | 1-2 hours |
| Bound three terms (inequalities 36-40) | ~60 | Hard | 4-6 hours |
| Combine into contradiction | ~30 | Easy | 1 hour |
| **Total** | **~215** | **Medium-Hard** | **~10-14 hours** |

The hard part is the exponent manipulation in inequalities (36)-(40). Each involves expressions like k^(-β/(3r-2)) · k^(β/(5r-5)) = k^(-β(1/(3r-2) - 1/(5r-5))). This is tedious but mechanical — good omega/linarith target.

### What to Do

**Minimum (status quo):** Keep Option A. We have 1 axiom, Erdős 1094 is resolved for k > 700.

**If resources allow:** Add Option C (Theorem 2 + Baker-Harman), prove Theorem 1. This makes the paper more accessible and gives us a reusable curve-approximation tool.

**Not recommended:** Option B. Lemma 2 is too deep for the value it adds in this context.

---

## 8. Making Konyagin Accessible: What's Provable vs What Needs Citations

The value of formalizing parts of Konyagin is making an obscure paper's techniques explicit and reusable. Here's the accessibility map:

### Layer 1: Lemma 2 (pages 44-48) — MUST CITE

**Why it's hard:** Uses Schmidt [9] Diophantine Approximation theory:
- Rational subspace heights (not in any standard text besides Schmidt)
- The duality H(U⊥) = H(U) (Schmidt's book, Theorem 1C, Chapter 1)
- Successive minima for arbitrary-rank lattices (Minkowski's Second Theorem generalized)

**What we'd need to formalize it:**
- ~500 lines: Lattice theory in ℤˢ (sublattices, determinants, rank)
- ~300 lines: Rational subspaces and heights
- ~200 lines: Successive minima theory
- ~100 lines: The proof of Lemma 2 itself
- **Total: ~1100 lines**, mostly infrastructure with no other use case

**Accessibility gain if we formalized:** Minimal. Schmidt [9] is already the accessible reference for this material. Lemma 2 is a clean application of known theory.

**Citation strategy:** State Lemma 2 as an axiom, cite Schmidt [9] §4 + Konyagin's construction. This is MORE accessible than the current state (where Theorem 1 is a black box).

### Layer 2: Theorem 2 (pages 48-51) — PARTIALLY PROVABLE

**What's elementary (can prove):**
- Taylor remainder bounds (Mathlib has `taylor_mean_remainder`)
- Integer combinations of binomial coefficients (Mathlib has `Nat.choose` integrality)
- The contradiction argument: if I = Σ aᵢwᵢf(uᵢ) is a nonzero integer with |I| < 1, impossible
- Interval covering for N > N₀ (elementary)
- Arithmetic progression reduction for λ > 1 (elementary)

**What needs Lemma 2:**
- The existence of small coefficients a₁,...,a₂ᵣ satisfying (5)+(6)
- The bound |aᵢ| ≤ (c₉N/r)^(r-1) · W

**Accessibility gain if we formalized Theorem 2:**
- **High.** The proof technique (construct a small-coefficient linear combination that's both approximately zero and exactly nonzero) is a classic Diophantine argument. Making it explicit in Lean demonstrates the method.
- The connection to smooth functions and Taylor approximation is clear and reusable.
- Theorem 2 applies to ANY smooth function with rational approximations — useful beyond binomial coefficients.

**Citation strategy:** Axiomatize Lemma 2, prove Theorem 2 from it. This exposes the Diophantine approximation → lattice point bound connection.

### Layer 3: Theorem 1 (pages 51-54) — FULLY PROVABLE (from Theorem 2 + Baker-Harman)

**What's elementary (can prove):**
- The function h(u) = n/u is smooth with computable derivatives Dⱼ = nj!/k^(j+1)
- Choosing r as the threshold where Dⱼ drops below k^(-β)
- The three-term bound (inequalities 36-40) — tedious but mechanical
- The optimization over λ and the final contradiction

**What needs citations:**
- Baker-Harman [1]: primes in short intervals (deep analytic number theory, but standard)
- The digit domination → rational approximation connection (uses Kummer's theorem, provable)

**Accessibility gain if we formalized Theorem 1:**
- **Very high.** The parameter optimization strategy (choose β, γ, r to balance main term vs error terms) is the core technique. This is what makes g(k) grow faster than any polynomial.
- Shows how to apply Theorem 2 to a specific problem (binomial coefficients)
- Connects prime counting to binomial least prime factors (non-obvious)

**Citation strategy:** Axiomatize Theorem 2 + Baker-Harman, prove Theorem 1. This makes the whole strategy explicit.

### Summary: Accessibility Value

| Component | Current (Option A) | With Elaboration (Option C) | Value Added |
|-----------|-------------------|----------------------------|-------------|
| Lattice geometry (Lemma 2) | Hidden in Theorem 1 | Hidden in Theorem 2 axiom | Low (Schmidt is accessible) |
| Smooth curve technique (Theorem 2) | Hidden in Theorem 1 | **Explicit axiom + used** | High (reusable technique) |
| Parameter optimization (Theorem 1 proof) | Hidden | **Fully proved** | Very high (demonstrates method) |

**Conclusion:** Option C maximizes accessibility gain. Theorem 2 + its application to Theorem 1 exposes the key techniques without drowning in lattice geometry details.

---

## 9. Concrete Next Steps (If Pursuing Option C)

### Step 1: State Theorem 2 as an Axiom (~20 lines)

```lean
/-- Konyagin (1999), Theorem 2. 
    For a smooth function f on [0,N] with r-th derivative bounded below by Dr
    and (r+1)-th derivative bounded above by Dr+1, if a set S of integers
    has f(u) close to rationals v/w with denominator w ≤ W and distance < δ,
    then |S| is bounded by a sum of three terms depending on the smoothness
    parameters and the approximation quality.
    
    This is a key tool for bounding integer points near smooth curves. -/
axiom konyagin_theorem2 
    (r : ℕ) (hr : 1 ≤ r) 
    (N W : ℝ) (hN : 0 < N) (hW : 1 ≤ W)
    (f : ℝ → ℝ) (hf_smooth : ContDiff ℝ (r + 1) f)
    (Dr Dr1 : ℝ) (hDr : 0 < Dr) (hDr1 : 0 < Dr1) 
    (δ : ℝ) (hδ : 0 < δ) 
    (λ : ℝ) (hλ : 1 ≤ λ)
    (hf_lower : ∀ u ∈ Set.Icc 0 N, Dr ≤ |iteratedDeriv r f u|)
    (hf_upper : ∀ u ∈ Set.Icc 0 N, |iteratedDeriv (r + 1) f u| ≤ Dr1)
    (S : Finset ℤ) 
    (hS_range : ∀ u ∈ S, (0 : ℝ) ≤ u ∧ (u : ℝ) ≤ N)
    (hS_approx : ∀ u ∈ S, ∃ v : ℤ, ∃ w : ℕ, 0 < w ∧ (w : ℝ) ≤ W ∧ 
                  |f u - v / w| < δ) :
    (S.card : ℝ) < 
      let term1 := (Dr * W^2) ^ (1 / (2*r - 1 : ℝ))
      let term2 := (δ * W^2 / Dr) ^ (1 / (r - 1 : ℝ))
      let term3 := (Dr1 * W^2 / Dr) ^ (1 / (2*r : ℝ))
      c_konyagin * N * (term1 + term2 + term3) + 2 * r * λ
    
/-- The constant c_konyagin from Theorem 2. Can be made explicit as
    c₁₀ = 8e + 64c₉ where c₉ is from Lemma 2. For our purposes any
    c_konyagin > 100 suffices (the exact value doesn't matter). -/
axiom c_konyagin : ℝ
axiom c_konyagin_pos : 0 < c_konyagin
axiom c_konyagin_large : 100 ≤ c_konyagin  -- Conservative bound
```

**File:** `botlib/NumberTheory/Erdos1094/KonyaginTheorem2.lean`

### Step 2: State Baker-Harman (~15 lines)

```lean
/-- Baker-Harman (1996). For α = 0.465, if x is large and y ≥ x^(1-α),
    the interval (x, x+y] contains ≫ y/log(x) primes.
    
    This is the current record for primes in short intervals. Any α < 1/2
    would suffice for the Konyagin argument; 0.465 is sharp. -/
axiom baker_harman_short_intervals :
    ∃ (C : ℝ) (x₀ : ℕ), 0 < C ∧ ∀ (x : ℕ), x₀ ≤ x → ∀ (y : ℝ),
      (x : ℝ) ^ (0.535 : ℝ) ≤ y → y ≤ x →
      C * y / Real.log x ≤ 
        (Nat.primeCounting ⌊(x : ℝ) + y⌋₊ - Nat.primeCounting x : ℝ)
```

**File:** `botlib/NumberTheory/BakerHarman.lean` (may be useful elsewhere)

### Step 3: Prove Theorem 1 (~200 lines)

**Structure:**
1. Fix parameters: β ∈ (0, 0.9α) with (3+β)/6 < 1-α, γ = β/10, W = k^γ
2. Define h(u) = n/u, compute Dⱼ = nj!/k^(j+1)
3. Choose r = min{j : Dⱼ ≤ k^(-β)}. Show 2 ≤ r ≤ 2c₃ log k (from bounds on n)
4. Build S via Baker-Harman + digit domination
5. Apply Theorem 2 with f(u) = h(k+u), δ = k^(-β), N = k^(1-β)
6. Bound the three terms: each ≤ k^(-γ/r) by inequalities (36)-(40)
7. Contradiction: |S| ≤ c · k^(1-β) · k^(-γ/r) + 2rλ < |S|

**Files:**
- `botlib/NumberTheory/Erdos1094/KonyaginTheorem1.lean` — main proof
- `botlib/NumberTheory/Erdos1094/KonyaginHelpers.lean` — digit domination → rational approx

### Step 4: Update Erdos1094 Main Theorem

Replace the Konyagin axiom with the proved Theorem 1. Net change: 1 axiom → 2 axioms, but with ~215 lines of proof content making the technique explicit.

**Timeline:** ~2-3 days for a focused formalization session. Most time is in Step 3 (the inequality chains).
