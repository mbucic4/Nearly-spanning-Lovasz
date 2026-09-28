module
public import RequestProject.LinkingCore
public import RequestProject.Asymp

/-!
# The linking lemma (Lemma 2.6) for all sufficiently large `n`
-/

@[expose] public section


open scoped BigOperators
open Classical Filter Real

namespace Lovasz

noncomputable section

lemma ev_rpow_le_rpow {a b : ℝ} (hab : a < b) (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, C * x ^ a ≤ x ^ b := by
  filter_upwards [ev_logpow_rpow_le 0 hab C] with x hx
  simpa using hx

lemma log_pow_nat_eq {x : ℝ} (k : ℕ) : Real.log x ^ k = Real.log x ^ (k : ℝ) :=
  (Real.rpow_natCast _ _).symm

/-- `x · exp(-c x^s) ≤ x^(-4)` eventually. -/
lemma ev_mul_exp_small {c s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    ∀ᶠ x : ℝ in atTop, x * Real.exp (-(c * x ^ s)) ≤ x ^ (-4 : ℝ) := by
  filter_upwards [ev_rpow_mul_exp_le 5 hc hs, eventually_gt_atTop 0] with x hx hx0
  have h5 : x ^ (5 : ℝ) = x ^ (4 : ℝ) * x := by
    rw [show (5 : ℝ) = 4 + 1 by norm_num, Real.rpow_add hx0, Real.rpow_one]
  have h4 : 0 < x ^ (4 : ℝ) := Real.rpow_pos_of_pos hx0 _
  rw [Real.rpow_neg hx0.le, le_inv_comm₀ (by positivity) h4]
  · rw [h5] at hx
    have hp := mul_pos hx0 (Real.exp_pos (-(c * x ^ s)))
    rw [inv_eq_one_div, le_div_iff₀ hp]; linarith

lemma ev_rpow_ge {a : ℝ} (ha : 0 < a) (C : ℝ) : ∀ᶠ x : ℝ in atTop, C ≤ x ^ a :=
  (tendsto_rpow_atTop ha).eventually (eventually_ge_atTop C)

lemma rpow_div_nat_pow {x : ℝ} (hx : 0 < x) (a : ℝ) (K m : ℕ) :
    (x ^ a / K) ^ m = x ^ (a * m) / (K : ℝ) ^ m := by
  rw [div_pow, ← Real.rpow_natCast (x ^ a), ← Real.rpow_mul hx.le]

/-- The numerical conditions of `linking_core`, for all large `x`. -/
lemma linking_numeric (c N₀ K : ℕ) {ε₀ γ α : ℝ} (hε : 0 < ε₀) (hγ : 0 < γ) (hα : 0 ≤ α)
    (hαγ : α + γ < ε₀) (h10 : 10 * γ < 7 * ε₀) (hK : 4 < ε₀ * K) (hK1 : 1 ≤ K) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ x ∧ 10 * x ^ (-γ) + 3 * x ^ (-γ / 7) ≤ 1 ∧ x ^ (-γ / 7) < 1 ∧
      100 * Real.log x ^ (7 * c + 19) / (x ^ (-γ / 7) / K) ^ 6 ≤ 31 / 32 / (120 * x ^ (-γ)) - 1 ∧
      ∀ E : ℝ, x ^ ε₀ ≤ E → x ^ α ≤ E / 128 ∧ 13 ≤ E ∧ 4 * c * Real.log 2 ≤ Real.log (E / 4) ∧
        Real.log 2 ≤ Real.log (E / 4) ∧ 48 * Real.log x ^ c * x ^ α ≤ E / 4 ∧ (N₀ : ℝ) ≤ E / 8 ∧
        2 * Real.log x ^ (9 * c + 21) / (x ^ (-γ / 7) / K) ^ 10 ≤ E / (8 * Real.log x ^ c) ∧
        2 * Real.log x ^ (9 * c + 21) / (x ^ (-γ / 7) / K) ^ 10 ≤ E / 64 ∧
        x * Real.exp (-(12 * x ^ (-γ) * E)) + x * Real.exp (2 * x ^ α - x ^ (-γ) * E / 13) +
          Real.exp (1 - x ^ (-γ) * E / 2) + 3 * (8 / E) ^ K ≤ x ^ (-3 : ℝ) ∧
        4 ≤ x ^ (-γ) * E := by
  have hσ : 0 < ε₀ - γ := by linarith
  have hlog : ∀ᶠ x : ℝ in atTop, max (4 * c * Real.log 2) (Real.log 2) + Real.log 4 ≤ ε₀ * Real.log x :=
    (Real.tendsto_log_atTop.const_mul_atTop hε).eventually (eventually_ge_atTop _)
  filter_upwards [eventually_ge_atTop (4 : ℝ), eventually_ge_atTop (Real.exp 1), hlog,
    ev_rpow_le_rpow (show α < ε₀ by linarith) 128, ev_rpow_ge hε 13, ev_rpow_ge hε (8 * N₀),
    ev_logpow_rpow_le ((c : ℝ)) (show α < ε₀ by linarith) 192,
    ev_logpow_rpow_le ((10 * c + 21 : ℕ) : ℝ) (show 10 * γ / 7 < ε₀ by linarith) (16 * (K : ℝ) ^ 10),
    ev_logpow_rpow_le ((9 * c + 21 : ℕ) : ℝ) (show 10 * γ / 7 < ε₀ by linarith) (128 * (K : ℝ) ^ 10),
    ev_logpow_rpow_le ((7 * c + 19 : ℕ) : ℝ) (show 6 * γ / 7 < γ by linarith)
      (2 * 3840 / 31 * 100 * (K : ℝ) ^ 6),
    ev_rpow_ge hγ (7680 / 31), ev_rpow_ge hγ 20, ev_rpow_ge (show 0 < γ / 7 by linarith) 6,
    ev_rpow_le_rpow (show α < ε₀ - γ by linarith) 52, ev_rpow_ge hσ 4,
    ev_mul_exp_small (show (0 : ℝ) < 12 by norm_num) hσ,
    ev_mul_exp_small (show (0 : ℝ) < 1 / 26 by norm_num) hσ,
    ev_mul_exp_small (show (0 : ℝ) < 1 / 2 by norm_num) hσ,
    ev_rpow_le_rpow (show (4 : ℝ) < ε₀ * K by linarith) (3 * 8 ^ K),
    eventually_gt_atTop (1 : ℝ)]
    with x hx4 hxe hlx f1 f2 f6 f5 f7 f7' f8 f8' fr fq f9b f10 e1 e2 e3 fK hx1
  have hx0 : 0 < x := by linarith
  have hL1 : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hxe
  have hL0 : 0 < Real.log x := by linarith
  have hnat : ∀ k : ℕ, Real.log x ^ (k : ℝ) = Real.log x ^ k := fun k => Real.rpow_natCast _ _
  rw [hnat] at f7 f7' f8
  rw [Real.rpow_natCast] at f5
  have hr : x ^ (-γ) = (x ^ γ)⁻¹ := Real.rpow_neg hx0.le _
  have hq : x ^ (-γ / 7) = (x ^ (γ / 7))⁻¹ := by rw [neg_div, Real.rpow_neg hx0.le]
  have hxg : 0 < x ^ γ := Real.rpow_pos_of_pos hx0 _
  have hxq : 0 < x ^ (γ / 7) := Real.rpow_pos_of_pos hx0 _
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
  have hr20 : x ^ (-γ) ≤ 1 / 20 := by
    rw [hr, inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) fr
  have hq6 : x ^ (-γ / 7) ≤ 1 / 6 := by
    rw [hq, inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) fq
  have hr0 : 0 < x ^ (-γ) := Real.rpow_pos_of_pos hx0 _
  have hpow : ∀ m : ℕ, (x ^ (-γ / 7) / K) ^ m = 1 / ((K : ℝ) ^ m * x ^ (m * γ / 7)) := by
    intro m
    rw [rpow_div_nat_pow hx0, show -γ / 7 * (m : ℝ) = -(m * γ / 7) by ring, Real.rpow_neg hx0.le]
    field_simp
  refine ⟨hx1.le, by linarith, by linarith, ?_, ?_⟩
  · rw [hpow, div_div_eq_mul_div, div_one, hr,
      show 31 / 32 / (120 * (x ^ γ)⁻¹) = 31 / 3840 * x ^ γ by field_simp; ring]
    push_cast
    have : 100 * Real.log x ^ (7 * c + 19) * ((K : ℝ) ^ 6 * x ^ (6 * γ / 7)) =
        31 / 7680 * (2 * 3840 / 31 * 100 * (K : ℝ) ^ 6 * Real.log x ^ (7 * c + 19) *
          x ^ (6 * γ / 7)) := by ring
    rw [this]; linarith
  intro E hE
  have hxe0 : 0 < x ^ ε₀ := Real.rpow_pos_of_pos hx0 _
  have hE0 : 0 < E := by linarith
  have hlogE : ε₀ * Real.log x - Real.log 4 ≤ Real.log (E / 4) := by
    rw [Real.log_div hE0.ne' (by norm_num), ← Real.log_rpow hx0]
    linarith [Real.log_le_log hxe0 hE]
  have hy : x ^ (ε₀ - γ) ≤ x ^ (-γ) * E := by
    rw [show ε₀ - γ = -γ + ε₀ by ring, Real.rpow_add hx0]
    exact mul_le_mul_of_nonneg_left hE hr0.le
  have hyp : 0 < x ^ (ε₀ - γ) := Real.rpow_pos_of_pos hx0 _
  have hLc : 0 < Real.log x ^ c := pow_pos hL0 _
  refine ⟨by linarith, by linarith, by linarith [le_max_left (4 * c * Real.log 2) (Real.log 2)],
    by linarith [le_max_right (4 * c * Real.log 2) (Real.log 2)], by linarith, by linarith,
    ?_, ?_, ?_, by linarith⟩
  · rw [hpow, div_div_eq_mul_div, div_one, le_div_iff₀ (by positivity)]
    push_cast
    have : 2 * Real.log x ^ (9 * c + 21) * ((K : ℝ) ^ 10 * x ^ (10 * γ / 7)) *
        (8 * Real.log x ^ c) = 16 * (K : ℝ) ^ 10 * Real.log x ^ (10 * c + 21) * x ^ (10 * γ / 7) := by
      rw [show 10 * c + 21 = (9 * c + 21) + c by ring, pow_add]; ring
    rw [this]; linarith
  · rw [hpow, div_div_eq_mul_div, div_one]
    push_cast
    have : 2 * Real.log x ^ (9 * c + 21) * ((K : ℝ) ^ 10 * x ^ (10 * γ / 7)) =
      (128 * (K : ℝ) ^ 10 * Real.log x ^ (9 * c + 21) * x ^ (10 * γ / 7)) / 64 := by ring
    rw [this]; linarith
  · have t1 : x * Real.exp (-(12 * x ^ (-γ) * E)) ≤ x ^ (-4 : ℝ) := by
      refine le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hx0.le) e1
      linarith only [hy]
    have t2 : x * Real.exp (2 * x ^ α - x ^ (-γ) * E / 13) ≤ x ^ (-4 : ℝ) := by
      refine le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hx0.le) e2
      linarith only [hy, f9b]
    have t3 : Real.exp (1 - x ^ (-γ) * E / 2) ≤ x ^ (-4 : ℝ) := by
      refine le_trans ?_ e3
      rw [sub_eq_add_neg, Real.exp_add]
      exact mul_le_mul hxe (Real.exp_le_exp.2 (by linarith only [hy])) (Real.exp_pos _).le hx0.le
    have t4 : 3 * (8 / E) ^ K ≤ x ^ (-4 : ℝ) := by
      have h1 : (8 / E) ^ K ≤ (8 / x ^ ε₀) ^ K := by
        gcongr
      have h2 : (8 / x ^ ε₀) ^ K = 8 ^ K / x ^ (ε₀ * K) := by
        rw [div_pow, ← Real.rpow_natCast (x ^ ε₀), ← Real.rpow_mul hx0.le]
      have hx4p : 0 < x ^ (4 : ℝ) := Real.rpow_pos_of_pos hx0 _
      have hxK : 0 < x ^ (ε₀ * K) := Real.rpow_pos_of_pos hx0 _
      have h3 : 3 * (8 ^ K / x ^ (ε₀ * K)) ≤ (x ^ (4 : ℝ))⁻¹ := by
        rw [← one_div, le_div_iff₀ hx4p, show 3 * (8 ^ K / x ^ (ε₀ * K)) * x ^ (4 : ℝ) =
          (3 * 8 ^ K * x ^ (4 : ℝ)) / x ^ (ε₀ * K) by ring, div_le_one hxK]
        exact fK
      rw [Real.rpow_neg hx0.le]; rw [h2] at h1
      linarith only [h1, h3]
    have h34 : 4 * x ^ (-4 : ℝ) ≤ x ^ (-3 : ℝ) := by
      rw [show (-3 : ℝ) = -4 + 1 by norm_num, Real.rpow_add hx0, Real.rpow_one]
      have := Real.rpow_pos_of_pos hx0 (-4 : ℝ)
      nlinarith
    linarith only [t1, t2, t3, t4, h34]

end

end Lovasz
