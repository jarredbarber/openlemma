# Blueprint: `card_KummerValid` Theorem

**Status:** Draft ✏️  
**Target:** `problems/NumberTheory/Erdos1094/Asymptotic.lean`, theorem `card_KummerValid`  
**Statement:**
```lean
theorem card_KummerValid (p k : ℕ) (hp : p.Prime) :
    (KummerValid p k).card = (List.range (L_p p k)).prod (fun j => p - dig p k j)
```
**Dependencies:** `Mathlib.Data.Nat.Digits.Lemmas` (Verified in Mathlib)  
**Confidence:** Certain

---

## 0. The Lean Definitions Under Proof

```lean
def L_p (p k : ℕ) : ℕ := if p > 1 then (digits p k).length else 0

def dig (p k j : ℕ) : ℕ := (digits p k).getD j 0

def KummerValid (p k : ℕ) : Finset ℕ :=
  (Finset.range (p ^ L_p p k)).filter (fun r =>
    ∀ j < L_p p k, dig p k j ≤ (digits p r).getD j 0)
```

**Goal:** Show `(KummerValid p k).card` equals $\prod_{j=0}^{L-1} (p - k_j)$ where $L = L_p(p,k)$ and $k_j = \text{dig}(p,k,j)$.

---

## 1. Proof Architecture

The proof decomposes into four lemmas, applied in sequence:

```
card_KummerValid
├── Step A: Rewrite digit access via getD_digits  (Mathlib)
├── Step B: Establish digit bijection              (Mathlib)
├── Step C: Factor the filter into a product       (combinatorial core)
└── Step D: Compute per-digit cardinality          (arithmetic)
```

---

## 2. Step A — Digit Access Lemma

**Mathlib fact:** `Nat.getD_digits (n i : ℕ) {b : ℕ} (h : 2 ≤ b) : (digits b n).getD i 0 = n / b ^ i % b`

**Application:** Since `p.Prime` implies `p ≥ 2`, we can rewrite:
- `dig p k j = k / p^j % p`
- `(digits p r).getD j 0 = r / p^j % p`

This replaces all `getD`/`digits` calls with pure arithmetic on `ℕ`.

**Reformulated filter predicate:** For `r ∈ Finset.range (p^L)`:
$$r \in \text{KummerValid}(p, k) \iff \forall\, j < L,\; k / p^j \bmod p \;\le\; r / p^j \bmod p$$

**Lean tactic sketch:**
```lean
simp only [KummerValid, Finset.mem_filter, dig, getD_digits (h := hp.two_le)]
```

---

## 3. Step B — Digit Bijection

**Key Mathlib results:**

1. `Nat.bijOn_digitsAppend' (hb : 1 < b) (l : ℕ) : Set.BijOn (digitsAppend b l) (Finset.range (b ^ l)) (fixedLengthDigits hb l)`

2. `List.card_fixedLengthDigits (hb : 1 < b) (l : ℕ) : (fixedLengthDigits hb l).card = b ^ l`

3. `List.mem_fixedLengthDigits_iff (hb : 1 < b) : L ∈ fixedLengthDigits hb l ↔ L.length = l ∧ ∀ x ∈ L, x < b`

**The bijection.** For $L = L_p(p,k)$ and $b = p$ (with $p \ge 2$):

$$\varphi : \{0, 1, \ldots, p^L - 1\} \xrightarrow{\;\sim\;} \{D \in \mathbb{N}^L : \forall i,\; D_i < p\}$$

defined by $\varphi(r) = \text{digitsAppend}(p, L, r)$, i.e., the base-$p$ digits of $r$ padded to length $L$.

Under $\varphi$, the Kummer-validity predicate becomes a **pointwise** condition on digit lists:

$$r \in \text{KummerValid}(p,k) \iff \forall\, j < L,\; k_j \le \varphi(r)_j$$

where $k_j = \text{dig}(p,k,j)$ is the $j$-th digit of $k$.

**Why pointwise?** The $j$-th entry of `digitsAppend p L r` is `(digits p r).getD j 0` (for $j < L$, since `digitsAppend` pads with zeros on the right and `digits` stores LSB-first). By Step A, this equals `r / p^j % p`. The predicate `k / p^j % p ≤ r / p^j % p` depends only on the $j$-th digit of both $k$ and $r$.

**Lean tactic sketch:**
```lean
have hb : 1 < p := hp.one_lt
rw [← Finset.card_image_of_injOn (Nat.bijOn_digitsAppend' hb L).injOn]
-- Transfer the filter from Finset.range to fixedLengthDigits
```

---

## 4. Step C — Product Decomposition (Core)

This is the combinatorial heart of the proof. We show:

$$\left|\{D \in \{0,\ldots,p-1\}^L : \forall j < L,\; k_j \le D_j\}\right| = \prod_{j=0}^{L-1} |\{d \in \{0,\ldots,p-1\} : k_j \le d\}|$$

**Principle:** The constraint decomposes as a conjunction of independent per-coordinate conditions. For a Cartesian product $S = S_0 \times S_1 \times \cdots \times S_{L-1}$ where $S_j = \{d : k_j \le d < p\}$:

$$|S| = \prod_{j=0}^{L-1} |S_j|$$

**Formal argument.** Define the "valid digit lists" as:

$$\mathcal{V} = \{D \in \{0,\ldots,p-1\}^L : \forall j,\; D_j \ge k_j\}$$

Construct an explicit bijection to a product type:

$$\psi : \mathcal{V} \xrightarrow{\;\sim\;} \prod_{j=0}^{L-1} \{k_j, k_j+1, \ldots, p-1\}$$

defined by $\psi(D) = D$ (the identity — the sets are the same). The right-hand side is a product of sets of sizes $p - k_0, p - k_1, \ldots, p - k_{L-1}$.

**Why $k_j < p$?** Each $k_j = k / p^j \bmod p \in \{0, \ldots, p-1\}$, so $p - k_j \ge 1$. This ensures each factor is positive.

**Lean strategy — induction on $L$.** Rather than using the product-type bijection directly (which requires `Finset.pi` machinery), the cleanest Lean approach is induction on $L$:

**Base case ($L = 0$):** `KummerValid p k = Finset.range 1 = {0}`, and the empty product is 1. Both sides equal 1.

**Inductive step ($L = l + 1$):** Decompose each $r \in \{0, \ldots, p^{l+1}-1\}$ as $r = q \cdot p + d$ where $d = r \bmod p$ and $q = r / p$. The Kummer-validity of $r$ decomposes:
- Digit 0: $k_0 \le d$ (i.e., $k \bmod p \le r \bmod p$)
- Digits 1 through $l$: $\forall j < l,\; (k/p)_j \le (q)_j$ — this is exactly `q ∈ KummerValid p (k/p)` at length $l$

So:
$$|\text{KummerValid}(p, k)| = |\{d \in \{0,\ldots,p-1\} : k_0 \le d\}| \times |\text{KummerValid}(p, k/p)|$$

$$= (p - k_0) \times \prod_{j=0}^{l-1} (p - (k/p)_j) = \prod_{j=0}^{l} (p - k_j)$$

where the last equality uses $(k/p)_j = k_{j+1}$ (shifting digits).

**Key auxiliary lemmas needed:**

**Lemma C.1 (Euclidean decomposition of Finset.range).**
```
Finset.range (p^(l+1)) ≃ Finset.range (p^l) ×ˢ Finset.range p
```
via $r \mapsto (r / p,\; r \bmod p)$, with inverse $(q, d) \mapsto q \cdot p + d$.

**Lean sketch:** `Finset.range_eq_prod_of_pow` or direct construction via `Finset.map` with the Euclidean embedding. The key Mathlib fact: `Nat.div_add_mod` gives `r = p * (r / p) + r % p`, and `r < p^(l+1) ↔ r/p < p^l ∧ r%p < p`.

**Lemma C.2 (Filter decomposition).**
```
(KummerValid p k).card = (p - dig p k 0) * (KummerValid p (k / p)).card
```
when `L_p p k = l + 1`.

**Proof:** Under the Euclidean decomposition $r = qp + d$:
- The filter $\forall j < l+1,\; k_j \le r_j$ splits into:
  - $j = 0$: $k_0 \le d$ (where $k_0 = k \bmod p$ and $d = r \bmod p$)
  - $j \ge 1$: $k_{j} \le q_{j-1}$ (where $k_j = (k/p)_{j-1}$ and $q_{j-1} = (r/p)_{j-1}$)
- The second condition is exactly $q \in \text{KummerValid}(p, k/p)$ at length $l$.
- The two conditions are independent (they constrain different components of the pair $(q, d)$).
- So the count is the product of the two individual counts.

**Lean sketch:**
```lean
rw [KummerValid, Finset.filter_product]  -- or manual decomposition
simp [Finset.card_product, Finset.card_filter_le_iff]
```

**Lemma C.3 (Digit shift).**
```
dig p k (j + 1) = dig p (k / p) j
```

**Proof:** By `getD_digits`:
- `dig p k (j+1) = k / p^(j+1) % p = (k/p) / p^j % p = dig p (k/p) j`
- Uses `Nat.div_div_eq_div_mul` and `pow_succ`.

**Lemma C.4 (Length relation).**
```
L_p p k = L_p p (k / p) + 1    (when k ≥ p, equivalently L_p p k ≥ 1)
L_p p k = 0                     (when k = 0)
```

**Proof:** From `digits_of_two_le_of_pos` and `digits_def'`:
- `digits p k = (k % p) :: digits p (k / p)` when `p ≥ 2` and `k > 0`
- So `(digits p k).length = (digits p (k/p)).length + 1`
- For `k = 0`: `digits p 0 = []` so `L_p p 0 = 0`.

---

## 5. Step D — Per-Digit Cardinality

**Lemma D.1.** *For $p \ge 2$ and $0 \le k_0 < p$:*
$$|\{d \in \{0, \ldots, p-1\} : k_0 \le d\}| = p - k_0$$

**Proof.** The set is $\{k_0, k_0 + 1, \ldots, p-1\} = $ `(Finset.range p).filter (fun d => k_0 ≤ d)`. This equals `Finset.Ico k_0 p`, which has cardinality `p - k_0`.

**Lean sketch:**
```lean
rw [Finset.filter_le_eq_Ico, Finset.card_Ico]
```

**Lemma D.2 (Digit bound).** *For $p$ prime and any $k, j$: `dig p k j < p`.*

**Proof.** `dig p k j = (digits p k).getD j 0`. If $j < (digits p k).length$, then the digit is $< p$ by `Nat.digits_lt_base`. If $j \ge$ length, then `getD` returns 0, and $0 < p$. Alternatively, from `getD_digits`: `dig p k j = k / p^j % p < p` by `Nat.mod_lt _ hp.pos`.

---

## 6. Full Proof Assembly

```
card_KummerValid p k hp :=
  by induction on L = L_p p k generalizing k:

  Case L = 0 (k = 0):
    KummerValid p 0 = (Finset.range 1).filter (fun r => True) = {0}
    card = 1 = empty product ✓

  Case L = l + 1 (k > 0):
    card (KummerValid p k)
      = (p - dig p k 0) * card (KummerValid p (k/p))   -- Lemma C.2
      = (p - dig p k 0) * ∏_{j<l} (p - dig p (k/p) j)  -- inductive hypothesis
      = (p - dig p k 0) * ∏_{j<l} (p - dig p k (j+1))   -- Lemma C.3
      = ∏_{j<l+1} (p - dig p k j)                        -- List.prod_cons
      ∎
```

**Complete Lean proof sketch:**
```lean
theorem card_KummerValid (p k : ℕ) (hp : p.Prime) :
    (KummerValid p k).card = (List.range (L_p p k)).prod (fun j => p - dig p k j) := by
  -- Generalize to induction on digit length
  set L := L_p p k with hL_def
  induction L generalizing k with
  | zero =>
    -- k = 0, KummerValid = {0}, product is empty = 1
    simp [KummerValid, L_p, dig, hL_def ▸ show L_p p k = 0 from ‹_›]
  | succ l ih =>
    -- Decompose via Euclidean division
    have hk_pos : 0 < k := by_contra h; simp [L_p, Nat.digits_zero] at hL_def; omega
    have hL_rel : L_p p (k / p) = l := by
      simp [L_p, digits_of_two_le_of_pos hp.two_le hk_pos] at hL_def ⊢; omega
    -- Apply Lemma C.2 (filter decomposition)
    rw [card_kummerValid_succ hp hk_pos]  -- custom lemma
    -- Apply IH to k/p
    rw [ih (k / p) hL_rel]
    -- Apply Lemma C.3 (digit shift) and simplify product
    simp [List.prod_range_succ', dig_shift hp]  -- custom lemma for shift
```

---

## 7. Citation Axiom Review

### 7.1 `stewart_digit_sum_bound`

```lean
axiom stewart_digit_sum_bound (k : ℕ) (h_large : k > 10000) :
  total_density P_S k < 1 / (k : ℝ)^4
```

**Cited sources:**
- Stewart (1980), DOI: `10.1515/crll.1980.319.63` ✅ (valid DOI for *J. reine angew. Math.* 319)
- Bugeaud (2008), Project Euclid link for *Osaka J. Math.* 45 ✅ (valid link, correct volume/year)

**Accuracy assessment: ⚠️ The axiom is STRONGER than what the citations prove.**

- **Stewart (1980)** proves: $s_a(n) + s_b(n) \ge C \cdot \frac{\log n}{(\log \log n)^2}$ for multiplicatively independent bases $a, b$. This is a *qualitative* lower bound on digit sums that grows **sublinearly** in $\log n$.
- **What the axiom needs:** $-\ln(\delta_k) > 4\ln k$, i.e., $\sum_{p \le 29} s_p(k)/p > 4\ln k$. This requires a **linear** lower bound in $\log k$, which is strictly stronger than Stewart's sublinear bound.
- **Bugeaud (2008)** gives asymptotic distribution results on smooth numbers with digital constraints, but provides **no explicit threshold** for $k > 10000$.

**Recommendation:** The axiom docstring should be revised to state honestly:
```
-- The cited references prove the qualitative decay of δ_k → 0, but do NOT
-- establish the explicit bound δ_k < 1/k⁴ for k > 10000.
-- This axiom is justified by exhaustive computation (verified for k ≤ 500000
-- in crt-density-large-k.md) and the super-polynomial decay heuristic.
-- Closing this axiom analytically requires a multi-base generalization of
-- Stewart's theorem with effective constants.
```

**Additional issue:** `total_density` is **used but never defined** in `Asymptotic.lean`. This would cause a build error. It should be defined as:
```lean
noncomputable def total_density (Ps : Finset ℕ) (k : ℕ) : ℝ :=
  Ps.prod (fun p => density_p p k)
```

### 7.2 `mertens_large_prime_bound`

```lean
axiom mertens_large_prime_bound (k : ℕ) (h_large : k > 1000) :
  (P_L k).prod (fun p => (p - k : ℝ) / p) < 2 ^ (-(k : ℝ) / Real.log k)
```

**Cited sources:**
- Rosser & Schoenfeld (1962), Project Euclid link ✅ (correct journal, volume, pages)
- Dusart (2010), arXiv: `1002.0442` ✅ (correct arXiv identifier)

**Accuracy assessment: ✅ The axiom is justified by the cited references**, via the chain:

1. Mertens' Second Theorem: $\sum_{p \le x} 1/p = \ln\ln x + M + O(1/\ln^2 x)$ (Rosser & Schoenfeld provide effective error bounds for $x \ge 286$)
2. Telescoping: $\sum_{k < p \le 2k} 1/p = \ln\ln(2k) - \ln\ln k + O(1/\ln^2 k) \approx \ln 2 / \ln k$
3. Exponential bound: $\prod (1 - k/p) \le \exp(-k \sum 1/p) \approx \exp(-k\ln 2/\ln k) = 2^{-k/\ln k}$

The full derivation is in `mertens-density-bound.md` (Verified ✅), §§2–5.

**Minor note:** The effective Mertens product bound is from Dusart, but the *sum of reciprocals* bound (which is what's actually used) is from Rosser & Schoenfeld. The docstring correctly cites both.

### 7.3 Summary of Citation Review

| Axiom | Claimed bound | Cited references support it? | Status |
|-------|--------------|------------------------------|--------|
| `stewart_digit_sum_bound` | $\delta_k < 1/k^4$ for $k > 10000$ | **No** — Stewart/Bugeaud give sublinear bounds | ⚠️ Overclaimed |
| `mertens_large_prime_bound` | $\prod(p-k)/p < 2^{-k/\ln k}$ | **Yes** — via Mertens + Rosser-Schoenfeld chain | ✅ Accurate |

---

## 8. Additional Issues in `Asymptotic.lean`

### 8.1 Missing definition: `total_density`

Referenced at lines 69, 88, 95 but never defined. **Build-breaking.** Add:

```lean
noncomputable def total_density (Ps : Finset ℕ) (k : ℕ) : ℝ :=
  Ps.prod (fun p => density_p p k)
```

### 8.2 Type mismatch in `P_L` product

Line 95: `(P_L k).prod (fun p => (p - k : ℝ) / p)` — the subtraction `p - k` is in `ℝ` (coerced from `ℕ`). For `p > k` this is positive, but Lean's `ℕ` subtraction would truncate. The cast to `ℝ` before subtraction is correct as written (the coercion `(p - k : ℝ)` is parsed as `(↑p - ↑k : ℝ)`). Verify this is the intended parsing.

### 8.3 Unused import

`Mathlib.NumberTheory.PrimesCongruence` — check whether this is needed. The CRT machinery might come from elsewhere.

---

## References

- `proofs/erdos-1094/kummer-theorem.md` — Kummer's theorem (Verified ✅)
- `proofs/erdos-1094/crt-density-large-k.md` — Citation analysis for Stewart/Bugeaud
- `proofs/erdos-1094/mertens-density-bound.md` — Mertens bound derivation (Verified ✅)
- Mathlib: `Mathlib.Data.Nat.Digits.Lemmas` — `getD_digits`, `bijOn_digitsAppend'`, `card_fixedLengthDigits`
- Mathlib: `Mathlib.Data.Nat.Digits.Defs` — `digits`, `ofDigits`, `digits_of_two_le_of_pos`
