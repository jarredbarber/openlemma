import Problems.SmoothEscape.Lean.Helpers
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Tendsto

/-! # The σ-orbit escapes every finite smooth set

This file formalizes the result from `proofs/smooth-escape.md` (Verified ✅):

**Theorem.** For any integer `n ≥ 2` and any finite set `S` of primes, the orbit
`a₀ = n, a_{k+1} = σ₁(aₖ)` is NOT eventually S-smooth. That is, for infinitely
many `k`, the number `aₖ` has at least one prime factor not in `S`.

## Proof outline

1. The orbit diverges to infinity (from `Helpers.lean`).
2. S-smooth numbers with uniformly bounded exponents are bounded.
3. So some exponent must grow without bound.
4. By pigeonhole on the finite set `S`, one fixed prime `p₀` has unbounded exponent.
5. By Zsygmondy's theorem (cited as an axiom), for large exponent `e`,
   `p₀^(e+1) - 1` has a primitive prime divisor `q` with `q ≥ e + 2`.
6. This `q` divides `σ₁(p₀^e)`, which divides `σ₁(aₖ) = a_{k+1}`.
7. But `a_{k+1}` is S-smooth, so `q ∈ S`. Since `q → ∞`, this contradicts `S` finite.

## Citation axiom

Zsygmondy's theorem (1892, also Birkhoff–Vandiver 1904) is a well-established
result in number theory that is not yet in Mathlib. We state it as an axiom
with a documentation comment citing the original sources.
-/

open ArithmeticFunction Finset Nat Filter

namespace Erdos410.SmoothEscape

/-! ## Definitions -/

/-- A natural number `n` is `S`-smooth if every prime factor of `n` lies in `S`. -/
def IsSmooth (S : Finset ℕ) (n : ℕ) : Prop :=
  ∀ p, p.Prime → p ∣ n → p ∈ S

/-- The orbit is eventually `S`-smooth if there exists `K` such that
    all iterates `a_k` for `k ≥ K` are `S`-smooth. -/
def EventuallySmooth (S : Finset ℕ) (n : ℕ) : Prop :=
  ∃ K, ∀ k, K ≤ k → IsSmooth S ((sigma 1)^[k] n)

/-! ## Zsygmondy's theorem (Citation axiom)

**Zsygmondy's theorem** (K. Zsygmondy, 1892): Let `p` be a prime and `m ≥ 2`.
Then `p^m - 1` has a *primitive prime divisor* — a prime `q` such that
`q ∣ p^m - 1` but `q ∤ p^i - 1` for any `1 ≤ i < m` — except in the cases:
(i) `p = 2, m = 6`; (ii) `p` is a Mersenne prime and `m = 2`.
For `m ≥ 7`, a primitive prime divisor exists unconditionally.

Moreover, the primitive prime divisor `q` satisfies `ord_q(p) = m`, so
`m ∣ (q - 1)` by Fermat's little theorem, giving `q ≥ m + 1`.

**References:**
- K. Zsygmondy, "Zur Theorie der Potenzreste," *Monatsh. Math.* **3** (1892), 265–284.
- G. D. Birkhoff and H. S. Vandiver, "On the integral divisors of aⁿ - bⁿ,"
  *Annals of Mathematics* **5** (1904), 173–180.
-/
axiom zsygmondy_prime_pow (p m : ℕ) (hp : p.Prime) (hm : 7 ≤ m) :
    ∃ q, q.Prime ∧ q ∣ p ^ m - 1 ∧ (∀ i, 1 ≤ i → i < m → ¬(q ∣ p ^ i - 1)) ∧ m + 1 ≤ q

/-! ## Number theory helpers -/

/-- The geometric sum identity for σ₁ on prime powers:
    `(p - 1) * σ₁(p^(m-1)) = p^m - 1` for a prime `p` and `m ≥ 1`. -/
lemma sub_one_mul_sigma_prime_pow (p m : ℕ) (hp : p.Prime) (hm : 1 ≤ m) :
    (p - 1) * sigma 1 (p ^ (m - 1)) = p ^ m - 1 := by
  have h1 : sigma 1 (p ^ (m - 1)) = (p ^ m - 1) / (p - 1) := by
    rw [sigma_one_apply_prime_pow hp, show m - 1 + 1 = m from by omega]
    exact Nat.geomSum_eq hp.two_le m
  rw [h1]
  exact Nat.mul_div_cancel' (Nat.sub_one_dvd_pow_sub_one p m)

/-- If `q` is a prime dividing `p^m - 1` but not `p - 1`, then `q ∣ σ₁(p^(m-1))`.
    This is because `(p - 1) * σ₁(p^(m-1)) = p^m - 1`. -/
lemma prime_dvd_sigma_of_dvd_pow_sub_one (p m q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hm : 1 ≤ m) (hdvd : q ∣ p ^ m - 1) (hndvd : ¬(q ∣ p - 1)) :
    q ∣ sigma 1 (p ^ (m - 1)) := by
  have h := sub_one_mul_sigma_prime_pow p m hp hm
  rw [← h] at hdvd
  exact (hq.dvd_mul.mp hdvd).resolve_left hndvd

/-- **Multiplicativity of σ₁**: if `p` is prime and `e = n.factorization p`,
    then `σ₁(p^e) ∣ σ₁(n)`. -/
lemma sigma_one_prime_pow_dvd (n : ℕ) (hn : n ≠ 0) (p : ℕ) (hp : p.Prime) :
    sigma 1 (p ^ n.factorization p) ∣ sigma 1 n := by
  set e := n.factorization p
  set m := n / p ^ e
  have hmul : p ^ e * m = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hcop : (p ^ e).gcd m = 1 :=
    (Nat.coprime_ordCompl hp hn).pow_left e
  conv_rhs => rw [← hmul]
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop]
  exact dvd_mul_right _ _

/-- **Key divisibility chain**: For `n ≠ 0` with `p` prime and `e = n.factorization p`,
    a Zsygmondy prime of `p^(e+1) - 1` divides `σ₁(n)`, provided `e + 1 ≥ 7`. -/
lemma zsygmondy_prime_dvd_sigma (n p : ℕ) (hp : p.Prime) (hn : n ≠ 0)
    (he : 7 ≤ n.factorization p + 1) :
    ∃ q, q.Prime ∧ q ∣ sigma 1 n ∧ n.factorization p + 2 ≤ q := by
  set e := n.factorization p with he_def
  set m := e + 1
  obtain ⟨q, hqp, hqdvd, hqprim, hqge⟩ := zsygmondy_prime_pow p m hp he
  -- q ∤ p^1 - 1 = p - 1 (since 1 < m and q is primitive)
  have hq_not_dvd_pm1 : ¬(q ∣ p - 1) := by
    have := hqprim 1 le_rfl (by omega : 1 < m)
    simpa [pow_one] using this
  -- q | σ₁(p^e) by the divisibility lemma
  have hq_dvd_sigma_pow : q ∣ sigma 1 (p ^ e) :=
    prime_dvd_sigma_of_dvd_pow_sub_one p m q hp hqp (by omega) hqdvd hq_not_dvd_pm1
  -- σ₁(p^e) | σ₁(n) by multiplicativity
  have hq_dvd_sigma_n : q ∣ sigma 1 n :=
    dvd_trans hq_dvd_sigma_pow (sigma_one_prime_pow_dvd n hn p hp)
  exact ⟨q, hqp, hq_dvd_sigma_n, by omega⟩

/-! ## Orbit helpers -/

/-- Iterates of σ₁ are ≥ 2 when starting from n ≥ 2. -/
lemma iterate_ge_two (n : ℕ) (hn : 2 ≤ n) (k : ℕ) : 2 ≤ (sigma 1)^[k] n := by
  induction k with
  | zero => simp only [Function.iterate_zero, id_eq]; exact hn
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have := Erdos410.sigma_one_ge ((sigma 1)^[k] n) ih
    omega

/-- Iterates of σ₁ are nonzero when starting from n ≥ 2. -/
lemma iterate_ne_zero (n : ℕ) (hn : 2 ≤ n) (k : ℕ) : (sigma 1)^[k] n ≠ 0 := by
  have := iterate_ge_two n hn k; omega

/-- Iterates of σ₁ are not equal to 1 when starting from n ≥ 2. -/
lemma iterate_ne_one (n : ℕ) (hn : 2 ≤ n) (k : ℕ) : (sigma 1)^[k] n ≠ 1 := by
  have := iterate_ge_two n hn k; omega

/-! ## Smooth number bounds and exponent growth (Steps 2–3 of the proof) -/

/-- Equivalence: S-smooth ↔ primeFactors ⊆ S (for nonzero n). -/
lemma isSmooth_iff {S : Finset ℕ} {n : ℕ} (hn : n ≠ 0) :
    IsSmooth S n ↔ n.primeFactors ⊆ S := by
  constructor
  · intro h p hp
    exact h p (Nat.mem_primeFactors.mp hp).1 (Nat.mem_primeFactors.mp hp).2.1
  · intro h p hp hdvd
    exact h (Nat.mem_primeFactors.mpr ⟨hp, hdvd, hn⟩)

/-- An S-smooth number with all factorization exponents ≤ E is bounded by `∏ p ∈ S, p ^ E`. -/
lemma smooth_bounded (S : Finset ℕ) (n : ℕ) (hn : n ≠ 0) (E : ℕ)
    (hSprimes : ∀ p ∈ S, p.Prime)
    (hsmooth : n.primeFactors ⊆ S)
    (hexp : ∀ p ∈ S, n.factorization p ≤ E) :
    n ≤ ∏ p ∈ S, p ^ E := by
  rw [← Nat.factorization_prod_pow_eq_self hn]
  calc ∏ p ∈ n.primeFactors, p ^ n.factorization p
      ≤ ∏ p ∈ S, p ^ n.factorization p := by
        apply Finset.prod_le_prod_of_subset_of_one_le' hsmooth
        intro p _ _
        exact Nat.one_le_pow _ _ (hSprimes p (by assumption)).pos
    _ ≤ ∏ p ∈ S, p ^ E := by
        apply Finset.prod_le_prod (fun p _ => Nat.zero_le _)
        intro p hp
        exact Nat.pow_le_pow_right (hSprimes p hp).pos (hexp p hp)

/-- If the orbit is eventually S-smooth, then for any exponent bound E,
    there exist k ≥ K and p ∈ S with factorization exponent > E.

    **Proof:** By contradiction. If all exponents are ≤ E for all k ≥ K, then
    each a_k ≤ ∏ p ∈ S, p^E (by `smooth_bounded`). But a_k → ∞, contradiction. -/
lemma exponent_growth (n : ℕ) (hn : 2 ≤ n) (S : Finset ℕ) (K : ℕ)
    (hSprimes : ∀ p ∈ S, p.Prime)
    (hK : ∀ k, K ≤ k → IsSmooth S ((sigma 1)^[k] n)) :
    ∀ E : ℕ, ∃ p ∈ S, ∃ k, K ≤ k ∧ E < ((sigma 1)^[k] n).factorization p := by
  by_contra hc
  push_neg at hc
  obtain ⟨E, hE⟩ := hc
  -- Uniform bound: for all k ≥ K, a_k ≤ B
  set B := ∏ p ∈ S, p ^ E
  have hbound : ∀ k, K ≤ k → (sigma 1)^[k] n ≤ B := by
    intro k hk
    have hne := iterate_ne_zero n hn k
    have hsmooth := (isSmooth_iff hne).mp (hK k hk)
    exact smooth_bounded S _ hne E hSprimes hsmooth (fun p hp => hE p hp k hk)
  -- But the orbit diverges to infinity
  have hdiv := Erdos410.sigma_one_iterate_tendsto_atTop n hn
  rw [tendsto_atTop_atTop] at hdiv
  obtain ⟨N, hN⟩ := hdiv (B + 1)
  have hle := hbound (max K N) (le_max_left K N)
  have hge := hN (max K N) (le_max_right K N)
  omega

/-! ## Pigeonhole (Step 4)

If for every E there is some p ∈ S witnessing large exponent, then by the
pigeonhole principle on the finite set S, some fixed prime p₀ witnesses
arbitrarily large exponents.
-/

/-- **Finite pigeonhole**: if for every `n : ℕ` there exists `s ∈ S`
    satisfying `P n s`, then some fixed `s₀ ∈ S` satisfies `P` for
    arbitrarily large `n`. -/
lemma finset_pigeonhole (S : Finset ℕ) (hS : S.Nonempty)
    (P : ℕ → ℕ → Prop)
    (h : ∀ n, ∃ s ∈ S, P n s) :
    ∃ s ∈ S, ∀ n, ∃ m, n ≤ m ∧ P m s := by
  -- By contradiction: if every s ∈ S only works for finitely many n,
  -- then we can find n large enough that none works, contradicting h.
  by_contra hc
  push_neg at hc
  -- hc : ∀ s ∈ S, ∃ n₀, ∀ m ≥ n₀, ¬P m s
  -- Make the choice function total (defined for all ℕ, not just S members)
  have htotal : ∀ s, ∃ Ns, s ∈ S → ∀ m, Ns ≤ m → ¬P m s := by
    intro s
    by_cases hs : s ∈ S
    · obtain ⟨Ns, hNs⟩ := hc s hs
      exact ⟨Ns, fun _ => hNs⟩
    · exact ⟨0, fun h => absurd h hs⟩
  choose N hN using htotal
  -- Take N₀ = max over S of N(s). For m ≥ N₀, no s works.
  set N₀ := S.sup' hS N
  obtain ⟨s, hsS, hPs⟩ := h N₀
  exact (hN s) hsS N₀ (Finset.le_sup' N hsS) hPs

/-! ## Main theorem -/

/-- **Smooth escape lemma**: The σ₁-orbit of any `n ≥ 2` is not eventually `S`-smooth
    for any finite set `S` of primes.

    This is the main result of this file, following the proof in `proofs/smooth-escape.md`.
    The only non-Mathlib dependency is `zsygmondy_prime_pow` (citation axiom).
    All other steps are fully proved. -/
theorem orbit_not_eventually_smooth (n : ℕ) (hn : 2 ≤ n) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) :
    ¬EventuallySmooth S n := by
  intro ⟨K, hK⟩
  -- Case split on whether S is nonempty
  by_cases hSe : S.Nonempty
  · -- Steps 2–3: for any E, some prime in S has exponent > E
    have hgrowth := exponent_growth n hn S K hS hK
    -- Step 4: Pigeonhole — one fixed prime p₀ ∈ S has unbounded exponent
    obtain ⟨p₀, hp₀S, hunb⟩ := finset_pigeonhole S hSe
      (fun E p => ∃ k, K ≤ k ∧ E < ((sigma 1)^[k] n).factorization p)
      hgrowth
    have hp₀ : p₀.Prime := hS p₀ hp₀S
    -- Step 5: Pick E large enough for Zsygmondy and to exceed max S
    set E₀ := max 6 (S.max' hSe)
    obtain ⟨E, hEge, k, hkK, hfact⟩ := hunb E₀
    -- factorization(a_k)(p₀) > E ≥ E₀ ≥ 6, so factorization(a_k)(p₀) + 1 ≥ 7
    have hak_ne : (sigma 1)^[k] n ≠ 0 := iterate_ne_zero n hn k
    have he_ge : 7 ≤ ((sigma 1)^[k] n).factorization p₀ + 1 := by omega
    -- By Zsygmondy, ∃ q prime with q | σ₁(a_k) and q ≥ factorization(a_k)(p₀) + 2
    obtain ⟨q, hqprime, hqdvd, hqge⟩ :=
      zsygmondy_prime_dvd_sigma ((sigma 1)^[k] n) p₀ hp₀ hak_ne he_ge
    -- σ₁(a_k) = a_{k+1} (by definition of the orbit)
    have hiter : (sigma 1)^[k + 1] n = sigma 1 ((sigma 1)^[k] n) :=
      Function.iterate_succ_apply' (sigma 1) k n
    rw [← hiter] at hqdvd
    -- a_{k+1} is S-smooth (since k+1 ≥ K)
    have hsmooth : IsSmooth S ((sigma 1)^[k + 1] n) := hK (k + 1) (by omega)
    -- Therefore q ∈ S
    have hqS : q ∈ S := hsmooth q hqprime hqdvd
    -- But q ≥ factorization(a_k)(p₀) + 2 > E + 2 > max' S ≥ any element of S
    have hqbig : S.max' hSe < q := by
      have : S.max' hSe ≤ E₀ := le_max_right _ _
      omega
    -- Contradiction: q ∈ S but q > max' S
    exact absurd (Finset.le_max' S q hqS) (not_le.mpr hqbig)
  · -- S is empty: a_K has no prime factors, but a_K ≥ 2, contradiction
    rw [Finset.not_nonempty_iff_eq_empty] at hSe
    have hsmooth : IsSmooth S ((sigma 1)^[K] n) := hK K le_rfl
    rw [hSe] at hsmooth
    -- a_K ≥ 2, so it has a prime factor
    have ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (iterate_ne_one n hn K)
    exact absurd (hsmooth p hp hpdvd) (by simp)

end Erdos410.SmoothEscape
