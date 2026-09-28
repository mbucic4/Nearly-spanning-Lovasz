module
public import Mathlib

/-!
# Elementary asymptotic estimates used for "sufficiently large `n`"
-/

@[expose] public section


open Filter Real

namespace Lovasz

/-- `C (log x)^k x^a ≤ x^b` for large `x` when `a < b`. -/
lemma ev_logpow_rpow_le (k : ℝ) {a b : ℝ} (hab : a < b) (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, C * Real.log x ^ k * x ^ a ≤ x ^ b := by
  have h := (isLittleO_log_rpow_rpow_atTop k (sub_pos.2 hab)).bound
    (c := 1 / (|C| + 1)) (by positivity)
  filter_upwards [h, eventually_gt_atTop 1] with x hx hx1
  have hx0 : 0 < x := by linarith
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx1.le
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hl _),
    Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)] at hx
  have hxa : 0 < x ^ a := Real.rpow_pos_of_pos hx0 _
  have hsplit : x ^ b = x ^ (b - a) * x ^ a := by
    rw [← Real.rpow_add hx0]; ring_nf
  have hC : C ≤ |C| + 1 := by linarith [le_abs_self C]
  have hlk : 0 ≤ Real.log x ^ k := Real.rpow_nonneg hl _
  calc C * Real.log x ^ k * x ^ a ≤ (|C| + 1) * Real.log x ^ k * x ^ a := by gcongr
    _ ≤ (|C| + 1) * (1 / (|C| + 1) * x ^ (b - a)) * x ^ a := by gcongr
    _ = x ^ b := by rw [hsplit]; field_simp

/-- Transfer of an eventual statement along the natural numbers. -/
lemma ev_nat {P : ℝ → Prop} (h : ∀ᶠ x : ℝ in atTop, P x) : ∀ᶠ n : ℕ in atTop, P n :=
  tendsto_natCast_atTop_atTop.eventually h

/-- `x^k exp(-c x^s) ≤ 1` for large `x`. -/
lemma ev_rpow_mul_exp_le (k : ℝ) {c s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    ∀ᶠ x : ℝ in atTop, x ^ k * Real.exp (-(c * x ^ s)) ≤ 1 := by
  have h1 := (isLittleO_rpow_exp_pos_mul_atTop (k / s) hc).bound (c := 1) one_pos
  have h2 := (tendsto_rpow_atTop hs).eventually h1
  filter_upwards [h2, eventually_gt_atTop 1] with x hx hx1
  have hx0 : 0 < x := by linarith
  have hxs : 0 < x ^ s := Real.rpow_pos_of_pos hx0 _
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hxs.le _), Real.norm_of_nonneg (Real.exp_pos _).le,
    one_mul, ← Real.rpow_mul hx0.le, show s * (k / s) = k by field_simp] at hx
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
  exact hx

end Lovasz
