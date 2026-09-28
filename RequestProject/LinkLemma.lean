module
public import RequestProject.LinkNumerics

/-!
# Lemma 2.4 (Lemma 5.1 of the cited work on sublinear expanders)

`linking_lemma c` proves the statement `LinkingLemma c` that was previously used as a
hypothesis, for every constant `c`.
-/

@[expose] public section


open scoped BigOperators
open Classical

namespace Lovasz

noncomputable section

/-- **Lemma 2.4**, with the explicit threshold `N₀ = ⌈exp(10⁴ (c + 1))⌉ + 3`. -/
theorem linking_body (c : ℕ) : LinkingBody c (⌈Real.exp (10 ^ 4 * ((c : ℝ) + 1))⌉₊ + 3) := by
  intro V _ G U q s hN hq0 hq1 hs hexp
  set n := U.card with hn_def
  have hn3 : 3 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hL : 10 ^ 4 * ((c : ℝ) + 1) ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hn0]
    refine (Nat.le_ceil _).trans ?_
    exact_mod_cast (by omega : ⌈Real.exp (10 ^ 4 * ((c : ℝ) + 1))⌉₊ ≤ n)
  set L := Real.log n with hL_def
  have hsn : s < n := hexp.s_lt_card (by norm_num) (by omega)
  have hqn : 2 * L ^ (9 * c + 21) < q ^ 10 * n := by
    have h1 : 2 * L ^ (9 * c + 21) / q ^ 10 < n := lt_of_le_of_lt hs hsn
    rw [div_lt_iff₀ (by positivity)] at h1
    linarith
  have hq1' : q ≤ 1 := hq1.le
  obtain ⟨hθ, hT3n, hnx, hsum⟩ := num_tail (by omega) hL hq0 hq1' hqn
  have hk := num_k (c := c) (by omega) hL
  have hΛ := num_Λ hL (c := c) hk
  have hΛ0 : (0 : ℝ) ≤ ((2 * (1 + (1 + ellN c L) + (Nat.log 2 n + 1) * (1 + ellN c L)) + 1 : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  refine linking_whp (p := pN c L q) (ℓ := ellN c L) (k := Nat.log 2 n + 1)
    (E := L ^ (4 * c + 10) / q ^ 5) (D := L ^ (5 * c + 11) / q ^ 5)
    (x := Real.exp (-(3 * L + 3))) hexp hq0 hq1' (pN_pos hq0) (pN_le_one hq1') (ellN_one hL)
    (le_of_eq (pN_mul hq0)) (num_K1 hL) (num_hrL hL hq0 hq1') ((num_hs hL hq0 hq1').trans hs)
    (num_hEq hL hq0 hq1') (num_grow (by omega) hL) hn3 (Real.exp_pos _).le hnx
    (num_hκ hL hq0 hq1') (by rw [num_hDs hq0]; exact hs) (num_hDE hL hq0 hq1') (by positivity)
    (Nat.lt_pow_succ_log_self (by norm_num) n) hθ (by have := num_L1 hL; positivity)
    (num_Λ1 hL hq0 hq1' hΛ hΛ0) (num_Λ2 hL hq0 hΛ hΛ0 hn0.le) hT3n hsum

/-- **Lemma 2.4** (Lemma 5.1 of the cited work on sublinear expanders, with `ε = 1/16`), proved
for every constant `c`. -/
theorem linking_lemma (c : ℕ) : LinkingLemma c := ⟨_, linking_body c⟩

end

end Lovasz
