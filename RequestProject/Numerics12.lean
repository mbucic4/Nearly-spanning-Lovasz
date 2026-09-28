module
public import RequestProject.MainCase
public import RequestProject.LinkingWhp

/-!
# Numerical facts for the proof of Theorem 1.2

The interval length is `t = ⌊n^a⌋`, so that the number of intervals `X = 2 ⌊(n-2)/t⌋` lies
between `n^(1-a)` and `n`.
-/

@[expose] public section


open Filter Real

namespace Lovasz

/-- `(log log log x)^2 / log log x ≤ 1/2` for large `x`. -/
lemma ev_coverage :
    ∀ᶠ x : ℝ in atTop, Real.log (Real.log (Real.log x)) ^ 2 / Real.log (Real.log x) ≤ 1 / 2 := by
  have h : ∀ᶠ y : ℝ in atTop, Real.log y ^ 2 / y ≤ 1 / 2 := by
    have h := (Real.isLittleO_pow_log_id_atTop (n := 2)).bound (show (0 : ℝ) < 1 / 2 by norm_num)
    filter_upwards [h, eventually_gt_atTop 1] with y hy hy1
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by simp; linarith)] at hy
    rw [div_le_iff₀ (by linarith)]; simpa using hy
  exact (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually h

/-- The facts about the number of intervals needed in the proof, for large `x`. -/
lemma ev_X_facts (N : ℕ) {e : ℝ} (he : 0 < e) :
    ∀ᶠ x : ℝ in atTop, (N : ℝ) ≤ x ∧ 3 ≤ x ∧ 6 * Real.log x ^ 56 ≤ x ∧
      2 * Real.log x ≤ x ^ e ∧
      Real.log (Real.log (Real.log x)) ^ 2 / Real.log (Real.log x) ≤ 1 / 2 := by
  have h56 : ∀ᶠ x : ℝ in atTop, 6 * Real.log x ^ 56 ≤ x := by
    filter_upwards [ev_logpow_rpow_le 56 (show (0 : ℝ) < 1 by norm_num) 6,
      eventually_gt_atTop 1] with x hx hx1
    rw [Real.rpow_zero, mul_one, Real.rpow_one, show (56 : ℝ) = ((56 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast] at hx
    exact hx
  have hl : ∀ᶠ x : ℝ in atTop, 2 * Real.log x ≤ x ^ e := by
    filter_upwards [ev_logpow_rpow_le 1 he 2, eventually_gt_atTop 1] with x hx hx1
    rw [Real.rpow_zero, mul_one, Real.rpow_one] at hx
    exact hx
  filter_upwards [eventually_ge_atTop (N : ℝ), eventually_ge_atTop (3 : ℝ), h56, hl,
    ev_coverage] with x h1 h2 h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩

/-- `6 (C x^b + 1) ≤ x^α` for large `x`, when `b < α` and `0 < α`. -/
lemma ev_k_bound (C : ℝ) {b α : ℝ} (h : b < α) (hα : 0 < α) :
    ∀ᶠ x : ℝ in atTop, 6 * (C * x ^ b + 1) ≤ x ^ α := by
  filter_upwards [ev_rpow_le_rpow h (12 * C), ev_rpow_ge hα 12] with x h1 h2
  nlinarith

/-- The interval length `t = ⌊n^a⌋` and the number of intervals `X = 2 ⌊(n-2)/t⌋`. -/
lemma floors {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : ∀ᶠ n : ℕ in atTop,
    2 ≤ ⌊(n : ℝ) ^ a⌋₊ ∧ (n : ℝ) ^ a / 2 ≤ (⌊(n : ℝ) ^ a⌋₊ : ℝ) ∧
    (⌊(n : ℝ) ^ a⌋₊ : ℝ) ≤ (n : ℝ) ^ a ∧ 0 < Conc.nQ n ⌊(n : ℝ) ^ a⌋₊ ∧
    (n : ℝ) ^ (1 - a) ≤ ((2 * Conc.nQ n ⌊(n : ℝ) ^ a⌋₊ : ℕ) : ℝ) ∧
    ((2 * Conc.nQ n ⌊(n : ℝ) ^ a⌋₊ : ℕ) : ℝ) ≤ n ∧ 0 < n ∧
    n ≤ Conc.nQ n ⌊(n : ℝ) ^ a⌋₊ * ⌊(n : ℝ) ^ a⌋₊ + ⌊(n : ℝ) ^ a⌋₊ + 1 := by
  filter_upwards [ev_nat (ev_rpow_ge ha0 4), ev_nat (ev_rpow_ge (show 0 < 1 - a by linarith) 8),
    eventually_ge_atTop 1] with n hT hU hn1
  set T := (n : ℝ) ^ a with hTdef
  set U := (n : ℝ) ^ (1 - a) with hUdef
  set t := ⌊T⌋₊ with htdef
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hTU : T * U = n := by
    rw [hTdef, hUdef, ← Real.rpow_add hn0]; simp
  have ht1 : (t : ℝ) ≤ T := Nat.floor_le (by linarith)
  have ht2 : T < t + 1 := Nat.lt_floor_add_one T
  have ht3 : (3 : ℝ) < t := by linarith
  have ht4 : 2 ≤ t := by
    have : (2 : ℝ) < t := by linarith
    exact_mod_cast this.le
  have htpos : 0 < t := by omega
  have hnR : (32 : ℝ) ≤ n := by nlinarith
  have hn32 : 32 ≤ n := by exact_mod_cast hnR
  have hQt : Conc.nQ n t * t ≤ n - 2 := Nat.div_mul_le_self _ _
  have hQt' : n - 2 < Conc.nQ n t * t + t := Nat.lt_div_mul_add htpos
  have hnt : t + 2 ≤ n := by
    have : (t : ℝ) + 2 ≤ n := by nlinarith
    exact_mod_cast this
  have hQpos : 0 < Conc.nQ n t := Nat.div_pos (by omega) htpos
  refine ⟨ht4, by linarith, ht1, hQpos, ?_, ?_, by omega, by omega⟩
  · have h1 : ((n - 2 : ℕ) : ℝ) < (Conc.nQ n t : ℝ) * t + t := by exact_mod_cast hQt'
    rw [Nat.cast_sub (by omega)] at h1
    push_cast at h1
    have hQ0 : (0 : ℝ) ≤ Conc.nQ n t := Nat.cast_nonneg _
    have h2 : (n : ℝ) - 2 < ((Conc.nQ n t : ℝ) + 1) * T := by
      have : ((Conc.nQ n t : ℝ) + 1) * t ≤ ((Conc.nQ n t : ℝ) + 1) * T :=
        mul_le_mul_of_nonneg_left ht1 (by positivity)
      linarith
    have h3 : U - 1 - 2 / T < (Conc.nQ n t : ℝ) := by
      rw [← hTU] at h2
      have hT0 : 0 < T := by linarith
      have : T * U - 2 < ((Conc.nQ n t : ℝ) + 1) * T := h2
      have e : U - 1 - 2 / T = (T * U - 2) / T - 1 := by field_simp; ring
      rw [e, sub_lt_iff_lt_add, div_lt_iff₀ hT0]; linarith
    have h4 : 2 / T ≤ 1 / 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    push_cast
    linarith
  · have h5 : Conc.nQ n t * 2 ≤ Conc.nQ n t * t := Nat.mul_le_mul_left _ ht4
    have : 2 * Conc.nQ n t ≤ n := by omega
    exact_mod_cast this

/-- The final count in the dense case. -/
lemma ev_dense_final {ε a : ℝ} (h : 1 - ε < 1 - 2 * a) :
    ∀ᶠ n : ℕ in atTop, 2 * Real.log n ^ 56 * (n : ℝ) ^ (1 - ε) ≤ (n : ℝ) ^ (1 - 2 * a) := by
  filter_upwards [ev_nat (ev_logpow_rpow_le 56 h 2)] with n hn
  rwa [show (56 : ℝ) = ((56 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hn

/-- The final count in the sparse case. -/
lemma ev_sparse_final {ε e : ℝ} (h : 1 - ε < e) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, 4 * ((n : ℝ) ^ (1 - ε) + 1) ≤ (n : ℝ) ^ e := by
  filter_upwards [ev_nat (ev_rpow_le_rpow h 8), ev_nat (ev_rpow_ge he 8)] with n h1 h2
  linarith

/-- `n^(a/2) ≤ n^a / 2` for large `n`. -/
lemma ev_E {a : ℝ} (ha : 0 < a) : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (a / 2) ≤ (n : ℝ) ^ a / 2 := by
  filter_upwards [ev_nat (ev_rpow_le_rpow (show a / 2 < a by linarith) 2)] with n hn
  linarith

end Lovasz
