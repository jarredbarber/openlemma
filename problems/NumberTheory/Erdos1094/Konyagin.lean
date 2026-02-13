import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Topology.Order.Basic

open Real Nat Classical

/-! ## Definition of g(k) -/

/-- The Erdős-Selfridge function: smallest n ≥ k+2 with minFac(C(n,k)) > k,
or 0 if no such n exists (meaning no exceptions exist for this k). -/
noncomputable def erdosG (k : ℕ) : ℕ :=
  if h : ∃ n, k + 2 ≤ n ∧ k < (n.choose k).minFac
  then Nat.find h
  else 0

/-- Key property: if n < g(k) and n ≥ k+2, then minFac(C(n,k)) ≤ k. -/
lemma erdosG_spec {k n : ℕ} (hk2 : k + 2 ≤ n) (hn : n < erdosG k) :
    (n.choose k).minFac ≤ k := by
  by_contra h
  push_neg at h
  have hex : ∃ m, k + 2 ≤ m ∧ k < (m.choose k).minFac := ⟨n, hk2, h⟩
  have : erdosG k ≤ n := by
    show (if h : ∃ m, k + 2 ≤ m ∧ k < (m.choose k).minFac then Nat.find h else 0) ≤ n
    rw [dif_pos hex]
    exact Nat.find_min' hex ⟨hk2, h⟩
  omega

/-! ## Konyagin citation axiom -/

/-- **Citation axiom** (Konyagin, 1999, Theorem 1):
There exist absolute constants c > 0 and K₀ such that for all k > K₀,
the Erdős-Selfridge function satisfies g(k) ≥ exp(c · (log k)²).

Reference: S. V. Konyagin, "Estimates of the least prime factor of a
binomial coefficient," Mathematika 46 (1999), no. 1, 41–55. -/
axiom konyagin_1999 : ∃ c : ℝ, 0 < c ∧
    ∃ K₀ : ℕ, ∀ k : ℕ, K₀ < k → (erdosG k : ℝ) ≥ Real.exp (c * (Real.log k) ^ 2)

/-! ## Corollary: g(k) > k² for large k -/

/-- For large enough k, exp(c · log²k) > k². -/
private lemma exp_c_log_sq_gt_sq (c : ℝ) (hc : 0 < c) :
    ∃ K : ℕ, ∀ k : ℕ, K < k → (k : ℝ) ^ 2 < Real.exp (c * (Real.log k) ^ 2) := by
  -- exp(c log²k) > k² when c log k > 2, i.e., k > exp(2/c)
  use Nat.ceil (Real.exp (2 / c)) + 1
  intro k hk
  have hk_one : (1 : ℝ) < k := by exact_mod_cast (show 2 ≤ k by omega)
  have hlog_pos : 0 < Real.log (k : ℝ) := Real.log_pos hk_one
  -- Key: c * log k > 2
  have hk_gt : Real.exp (2 / c) < (k : ℝ) := by
    calc Real.exp (2 / c)
        ≤ ↑(Nat.ceil (Real.exp (2 / c))) := by exact_mod_cast Nat.le_ceil _
      _ < ↑(Nat.ceil (Real.exp (2 / c)) + 1) := by exact_mod_cast Nat.lt_succ_of_le le_rfl
      _ ≤ ↑k := by exact_mod_cast Nat.le_of_lt_succ (by omega)
  have hc_log : 2 < c * Real.log (k : ℝ) := by
    have h1 : 2 / c < Real.log (k : ℝ) := by
      rw [← Real.log_exp (2 / c)]
      exact Real.log_lt_log (Real.exp_pos _) hk_gt
    have := mul_lt_mul_of_pos_left h1 hc
    rwa [mul_div_cancel₀ _ (ne_of_gt hc)] at this
  -- c * log²k > 2 * log k
  have key : 2 * Real.log (k : ℝ) < c * (Real.log (k : ℝ)) ^ 2 := by
    rw [sq]; nlinarith
  -- k² = exp(2 log k) < exp(c log²k)
  calc (k : ℝ) ^ 2
      = Real.exp (Real.log ((k : ℝ) ^ 2)) := (Real.exp_log (by positivity)).symm
    _ = Real.exp (2 * Real.log (k : ℝ)) := by congr 1; rw [Real.log_pow]; ring
    _ < Real.exp (c * (Real.log (k : ℝ)) ^ 2) := Real.exp_strictMono key

/-- **Corollary of Konyagin**: g(k) > k² for all sufficiently large k.
Proved from the axiom: exp(c log²k) grows faster than k². -/
theorem g_exceeds_k_sq : ∃ K₁ : ℕ, ∀ k : ℕ, K₁ < k → k ^ 2 < erdosG k := by
  obtain ⟨c, hc, K₀, hK⟩ := konyagin_1999
  obtain ⟨K, hK'⟩ := exp_c_log_sq_gt_sq c hc
  use max K₀ K
  intro k hk
  have hg : (erdosG k : ℝ) ≥ Real.exp (c * (Real.log k) ^ 2) :=
    hK k (lt_of_le_of_lt (le_max_left _ _) hk)
  have hexp : (k : ℝ) ^ 2 < Real.exp (c * (Real.log k) ^ 2) :=
    hK' k (lt_of_le_of_lt (le_max_right _ _) hk)
  exact_mod_cast hexp.trans_le hg

/-- **Bridge**: g(k) > k² implies no exceptions with n ∈ [k+2, k²]. -/
theorem no_exceptions_le_sq {k : ℕ} (hg : k ^ 2 < erdosG k) (n : ℕ)
    (hk2 : k + 2 ≤ n) (hn : n ≤ k ^ 2) :
    (n.choose k).minFac ≤ k :=
  erdosG_spec hk2 (lt_of_le_of_lt hn hg)
