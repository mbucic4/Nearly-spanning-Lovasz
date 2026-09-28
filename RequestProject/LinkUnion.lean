module
public import RequestProject.LinkT1

/-!
# Union bounds for the proof of Lemma 5.1

* `explore_simple`: Lemma 5.5 with its error term simplified to `5 ℓ r³ exp(-a)`;
* summation lemmas over subsets and pairs of subsets;
* the probability bounds for the three good events: (T1'), (T3) and `|R| < 1.1 q n`.
-/

@[expose] public section


open scoped BigOperators
open Classical

namespace Lovasz

noncomputable section

section sums

variable {V : Type*}

lemma one_add_pow_sub_one_le {x : ℝ} (n : ℕ) (hx : 0 ≤ x) (h : n * x ≤ 1) :
    (1 + x) ^ n - 1 ≤ 2 * n * x := by
  have h1 : (1 + x) ^ n ≤ Real.exp (n * x) := by
    calc (1 + x) ^ n ≤ Real.exp x ^ n := pow_le_pow_left₀ (by linarith) (by
          have := Real.add_one_le_exp x; linarith) n
      _ = Real.exp (n * x) := by rw [← Real.exp_nat_mul]
  have hnx : 0 ≤ (n : ℝ) * x := by positivity
  have h2 := Real.abs_exp_sub_one_sub_id_le (x := n * x) (by rw [abs_of_nonneg hnx]; exact h)
  have h3 := (abs_le.1 h2).2
  nlinarith

lemma sum_nonempty_pow (U : Finset V) (x : ℝ) :
    ∑ X ∈ U.powerset.filter (fun X => X.Nonempty), x ^ X.card = (1 + x) ^ U.card - 1 := by
  have h := Finset.sum_filter_add_sum_filter_not U.powerset (fun X => X.Nonempty)
    (fun X => x ^ X.card)
  have h2 : U.powerset.filter (fun X => ¬ X.Nonempty) = {∅} := by
    ext X
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.not_nonempty_iff_eq_empty,
      Finset.mem_singleton]
    constructor
    · rintro ⟨-, h⟩; exact h
    · rintro rfl; exact ⟨Finset.empty_subset _, rfl⟩
  rw [h2, Finset.sum_singleton, Finset.card_empty, pow_zero] at h
  have h3 := Finset.sum_pow_mul_eq_add_pow x 1 U
  simp only [one_pow, mul_one] at h3
  rw [add_comm x 1] at h3
  linarith

lemma sum_nonempty_pow_le (U : Finset V) {x : ℝ} (hx : 0 ≤ x) (h : U.card * x ≤ 1) :
    ∑ X ∈ U.powerset.filter (fun X => X.Nonempty), x ^ X.card ≤ 2 * U.card * x := by
  rw [sum_nonempty_pow]; exact one_add_pow_sub_one_le _ hx h

lemma card_small_subsets_le (U : Finset V) (hn : 1 ≤ U.card) (u : ℕ) :
    ((U.powerset.filter (fun Z => Z.card ≤ u)).card : ℝ) ≤ 3 * (U.card : ℝ) ^ u := by
  set n := U.card
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : ((U.powerset.filter (fun Z => Z.card ≤ u)).card : ℝ) ≤
      ∑ Z ∈ U.powerset, (n : ℝ) ^ u * (1 / n) ^ Z.card := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    push_cast
    refine Finset.sum_le_sum fun Z _ => ?_
    split_ifs with h
    · rw [one_div, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
      exact pow_le_pow_right₀ hn' h
    · positivity
  have h2 : ∑ Z ∈ U.powerset, (n : ℝ) ^ u * (1 / n) ^ Z.card = (n : ℝ) ^ u * (1 + 1 / n) ^ n := by
    rw [← Finset.mul_sum]
    congr 1
    have h3 := Finset.sum_pow_mul_eq_add_pow (1 / (n : ℝ)) 1 U
    simp only [one_pow, mul_one] at h3
    rw [h3, add_comm]
  have h4 : (1 + 1 / (n : ℝ)) ^ n ≤ 3 := by
    calc (1 + 1 / (n : ℝ)) ^ n ≤ Real.exp (1 / n) ^ n := pow_le_pow_left₀ (by positivity) (by
          have := Real.add_one_le_exp (1 / (n : ℝ)); linarith) n
      _ = Real.exp 1 := by rw [← Real.exp_nat_mul]; congr 1; field_simp
      _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  rw [h2] at h1
  have : (0 : ℝ) ≤ (n : ℝ) ^ u := by positivity
  nlinarith

/-- The sum of `x^|S|` over pairs `(S, Z)` of subsets of `U` with `S` nonempty and
`|Z| ≤ |S|`. -/
lemma sum_pairs_le (U : Finset V) (hn : 1 ≤ U.card) {x : ℝ} (hx : 0 ≤ x)
    (h : (U.card : ℝ) ^ 2 * x ≤ 1) :
    ∑ S ∈ U.powerset.filter (fun S => S.Nonempty),
      ∑ _ ∈ U.powerset.filter (fun Z => Z.card ≤ S.card), x ^ S.card ≤
        6 * (U.card : ℝ) ^ 2 * x := by
  set n := U.card
  have h1 : ∀ S ∈ U.powerset.filter (fun S => S.Nonempty),
      ∑ _ ∈ U.powerset.filter (fun Z => Z.card ≤ S.card), x ^ S.card ≤ 3 * (n * x) ^ S.card := by
    intro S _
    rw [Finset.sum_const, nsmul_eq_mul, mul_pow]
    have := card_small_subsets_le U hn S.card
    have : (0 : ℝ) ≤ x ^ S.card := by positivity
    nlinarith
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← Finset.mul_sum]
  have h2 := sum_nonempty_pow_le U (x := n * x) (by positivity) (by nlinarith)
  nlinarith

end sums

section union

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- A union bound over a nested family of events. -/
lemma ppr_exists2_le {μ : V → Bool → ℝ} (hμ : IsPD μ) {α β : Type*} (A : Finset α)
    (B : α → Finset β) (P : α → β → (V → Bool) → Prop) :
    ppr μ (fun y => ∃ a ∈ A, ∃ b ∈ B a, P a b y) ≤ ∑ a ∈ A, ∑ b ∈ B a, ppr μ (P a b) := by
  refine (ppr_exists_le hμ A _).trans (Finset.sum_le_sum fun a _ => ppr_exists_le hμ _ _)

set_option maxHeartbeats 800000 in
/-- **Lemma 5.5** with a simplified error term. -/
theorem explore_simple {U W Z : Finset V} {c : ℕ} {s q p : ℝ} (hexp : IsExpander G U (1 / 16) c s)
    (hW : W ⊆ U) (hq0 : 0 < q) (hq1 : q ≤ 1) (hp0 : 0 < p) (hp1 : p ≤ 1) {ℓ : ℕ} (hℓ1 : 1 ≤ ℓ)
    (hℓp : (ℓ + 2) * p ≤ q / 20) (hL : 1 ≤ Real.log U.card ^ c)
    (hrL : 13 * Real.log U.card ^ c ≤ (⌈1 / p⌉₊ : ℝ)) (hs : 4 * (⌈1 / p⌉₊ : ℝ) ^ 3 ≤ s)
    (hWq : 50 ≤ q * W.card) (hZ : 100000 * Real.log U.card ^ c * Z.card ≤ q * W.card)
    (hgrow : 2 * (U.card : ℝ) / 3 <
      (1 + 1 / (1000 * Real.log U.card ^ c)) ^ ℓ * (q * W.card / 50)) :
    1 - 5 * ℓ * (⌈1 / p⌉₊ : ℝ) ^ 3 * Real.exp (-(q * W.card /
        (200000 * (⌈1 / p⌉₊ : ℝ) ^ 3 * Real.log U.card ^ c))) ≤
      ppr (fun _ : V => bern q)
        (fun y => 0.55 * q * U.card ≤ (ballY G U Z y ℓ (W ∩ allowed U Z y)).card) := by
  have h := explore hexp hW hq0 hq1 hp0 hp1 hℓp hL hrL hs hWq hZ hgrow
  set K := Real.log U.card ^ c
  set r : ℝ := (⌈1 / p⌉₊ : ℝ)
  set a := q * W.card / (200000 * r ^ 3 * K)
  have hr1 : 1 ≤ r := by
    have : (1 : ℝ) ≤ 1 / p := by rw [le_div_iff₀ hp0]; linarith
    exact this.trans (Nat.le_ceil _)
  have hpr : 1 ≤ p * r := by
    have := Nat.le_ceil (1 / p)
    rw [div_le_iff₀ hp0] at this
    linarith
  have hW0 : (0 : ℝ) ≤ q * W.card := by positivity
  have hWn : (W.card : ℝ) ≤ U.card := by exact_mod_cast Finset.card_le_card hW
  have hr3 : 1 ≤ r ^ 3 := one_le_pow₀ hr1
  have hden : 0 < 200000 * r ^ 3 * K := by positivity
  have ha : a ≤ q * W.card / 160 := by
    simp only [a]
    rw [div_le_div_iff₀ hden (by norm_num)]
    have : 160 ≤ 200000 * r ^ 3 * K := by nlinarith
    nlinarith
  have hb : a ≤ p * (q * W.card / 50) / (100 * r) := by
    simp only [a]
    rw [div_le_div_iff₀ hden (by positivity)]
    have h1 : q * W.card * (100 * r) ≤ q * W.card * (100 * r) * (p * r) :=
      le_mul_of_one_le_right (by positivity) hpr
    have h2 : 5000 * r ^ 2 ≤ 200000 * r ^ 3 * K := by nlinarith
    have h3 : 0 ≤ p * q * W.card := by positivity
    nlinarith
  have hc : (q * W.card / 50) / (4000 * r ^ 3 * K) = a := by
    simp only [a]; field_simp; ring
  have hd : a ≤ 0.00036 * q * U.card := by
    simp only [a]
    rw [div_le_iff₀ hden]
    have : 1 ≤ 0.00036 * (200000 * r ^ 3 * K) := by nlinarith
    have h4 : q * W.card ≤ q * U.card := mul_le_mul_of_nonneg_left hWn hq0.le
    nlinarith
  have e1 := Real.exp_le_exp.2 (neg_le_neg ha)
  have e2 := Real.exp_le_exp.2 (neg_le_neg hb)
  have e4 := Real.exp_le_exp.2 (neg_le_neg hd)
  rw [hc] at h
  have hℓ1' : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ1
  have hea := Real.exp_pos (-a)
  have : Real.exp (-(q * W.card / 160)) + ℓ * (Real.exp (-(p * (q * W.card / 50) / (100 * r))) +
      2 * r ^ 3 * Real.exp (-a)) + Real.exp (-(0.00036 * q * U.card)) ≤
      5 * ℓ * r ^ 3 * Real.exp (-a) := by
    have h5 : ℓ * Real.exp (-(p * (q * W.card / 50) / (100 * r))) ≤ ℓ * Real.exp (-a) :=
      mul_le_mul_of_nonneg_left e2 (by positivity)
    have h6 : (2 : ℝ) + ℓ + 2 * ℓ * r ^ 3 ≤ 5 * ℓ * r ^ 3 := by nlinarith
    have h7 : (2 + ℓ + 2 * ℓ * r ^ 3) * Real.exp (-a) ≤ 5 * ℓ * r ^ 3 * Real.exp (-a) :=
      mul_le_mul_of_nonneg_right h6 hea.le
    nlinarith
  linarith

/-- The good event of Corollary 5.6 for well-expanding sets holds with high probability. -/
theorem goodE_fail_le {U : Finset V} {c : ℕ} {s q p E x : ℝ} (hexp : IsExpander G U (1 / 16) c s)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hp0 : 0 < p) (hp1 : p ≤ 1) {ℓ : ℕ} (hℓ1 : 1 ≤ ℓ)
    (hℓp : (ℓ + 2) * p ≤ q / 20) (hL : 1 ≤ Real.log U.card ^ c)
    (hrL : 13 * Real.log U.card ^ c ≤ (⌈1 / p⌉₊ : ℝ)) (hs : 4 * (⌈1 / p⌉₊ : ℝ) ^ 3 ≤ s)
    (hEq : 100000 * Real.log U.card ^ c + 50 ≤ q * E)
    (hgrowN : (U.card : ℝ) ≤ (1 + 1 / (1000 * Real.log U.card ^ c)) ^ ℓ)
    (hn : 1 ≤ U.card) (hx : 0 ≤ x) (hnx : (U.card : ℝ) ^ 2 * x ≤ 1)
    (hκ : ∀ u : ℕ, 1 ≤ u → 5 * ℓ * (⌈1 / p⌉₊ : ℝ) ^ 3 * Real.exp (-(q * (E * u) /
        (200000 * (⌈1 / p⌉₊ : ℝ) ^ 3 * Real.log U.card ^ c))) ≤ x ^ u) :
    ppr (fun _ : V => bern q) (fun y => ¬ GoodEProp G U y (0.55 * q * U.card) E (1 + ℓ)) ≤
      6 * (U.card : ℝ) ^ 2 * x := by
  set K := Real.log U.card ^ c
  set r : ℝ := (⌈1 / p⌉₊ : ℝ)
  set θ := 0.55 * q * U.card
  have hμ := isPD_bern (ι := V) hq0.le hq1
  set A := U.powerset.filter (fun S => S.Nonempty ∧ 3 * S.card ≤ 2 * U.card ∧
    E * S.card ≤ (extNb G U S ∅).card)
  set B : Finset V → Finset (Finset V) := fun S => U.powerset.filter (fun Z => Z.card ≤ S.card)
  have hsub : ∀ y, ¬ GoodEProp G U y θ E (1 + ℓ) → ∃ S ∈ A, ∃ Z ∈ B S,
      ¬ θ ≤ (ballY G U Z y ℓ (extNb G U S ∅ ∩ allowed U Z y)).card := by
    intro y hy
    simp only [GoodEProp, not_forall, not_le] at hy
    obtain ⟨S, hSU, Z, hZU, hSn, hS3, hZS, hSE, hlt⟩ := hy
    refine ⟨S, Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hSU, hSn, hS3, hSE⟩, Z,
      Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hZU, hZS⟩, fun hle => ?_⟩
    have hsub1 : extNb G U S ∅ ∩ allowed U Z y ⊆ ballY G U Z y 1 S := by
      intro v hv
      obtain ⟨hvN, hvA⟩ := Finset.mem_inter.1 hv
      refine Finset.mem_inter.2 ⟨nbr_subset_reach_one _ _ (Finset.mem_filter.2 ⟨hvA, ?_⟩), hvA⟩
      simp only [extNb, Finset.mem_filter] at hvN
      obtain ⟨u, hu, hadj, -⟩ := hvN.2
      exact ⟨u, hu, hadj⟩
    have := Finset.card_le_card (ballY_trans (b := ℓ) hsub1)
    have : θ ≤ (ballY G U Z y (1 + ℓ) S).card := hle.trans (by exact_mod_cast this)
    linarith
  have h1 : ppr (fun _ : V => bern q) (fun y => ¬ GoodEProp G U y θ E (1 + ℓ)) ≤
      ∑ S ∈ A, ∑ Z ∈ B S, ppr (fun _ : V => bern q)
        (fun y => ¬ θ ≤ (ballY G U Z y ℓ (extNb G U S ∅ ∩ allowed U Z y)).card) :=
    (ppr_mono hμ hsub).trans (ppr_exists2_le hμ A B _)
  have h2 : ∀ S ∈ A, ∀ Z ∈ B S, ppr (fun _ : V => bern q)
      (fun y => ¬ θ ≤ (ballY G U Z y ℓ (extNb G U S ∅ ∩ allowed U Z y)).card) ≤ x ^ S.card := by
    intro S hS Z hZ
    obtain ⟨hSU', hSn, hS3, hSE⟩ := Finset.mem_filter.1 hS
    obtain ⟨hZU', hZS⟩ := Finset.mem_filter.1 hZ
    set W := extNb G U S ∅
    have hWU : W ⊆ U := fun v hv => (Finset.mem_sdiff.1 (Finset.mem_filter.1 hv).1).1
    have hS1 : (1 : ℝ) ≤ S.card := by exact_mod_cast hSn.card_pos
    have hK0 : 0 ≤ K := by linarith
    have hqW : q * E * S.card ≤ q * W.card := by
      have := mul_le_mul_of_nonneg_left hSE hq0.le; linarith
    have hqE0 : 0 ≤ q * E := by linarith
    have hWq : 50 ≤ q * W.card := by nlinarith
    have hZc : (Z.card : ℝ) ≤ S.card := by exact_mod_cast hZS
    have hZ : 100000 * K * Z.card ≤ q * W.card := by nlinarith
    have hgrow : 2 * (U.card : ℝ) / 3 < (1 + 1 / (1000 * K)) ^ ℓ * (q * W.card / 50) := by
      have hn' : (1 : ℝ) ≤ U.card := by exact_mod_cast hn
      have : (1 + 1 / (1000 * K)) ^ ℓ * 1 ≤ (1 + 1 / (1000 * K)) ^ ℓ * (q * W.card / 50) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    have he : 1 - 5 * ℓ * r ^ 3 * Real.exp (-(q * W.card / (200000 * r ^ 3 * K))) ≤
        ppr (fun _ : V => bern q)
          (fun y => θ ≤ (ballY G U Z y ℓ (W ∩ allowed U Z y)).card) :=
      explore_simple (Z := Z) hexp hWU hq0 hq1 hp0 hp1 hℓ1 hℓp hL hrL hs hWq hZ hgrow
    rw [ppr_not hμ]
    have hr0 : 0 < r := by
      have : (0 : ℝ) < 1 / p := by positivity
      exact this.trans_le (Nat.le_ceil _)
    have hmono : Real.exp (-(q * W.card / (200000 * r ^ 3 * K))) ≤
        Real.exp (-(q * (E * S.card) / (200000 * r ^ 3 * K))) := by
      refine Real.exp_le_exp.2 (neg_le_neg (div_le_div_of_nonneg_right ?_ (by positivity)))
      linarith
    have := hκ S.card hSn.card_pos
    have : 5 * ℓ * r ^ 3 * Real.exp (-(q * W.card / (200000 * r ^ 3 * K))) ≤
        5 * ℓ * r ^ 3 * Real.exp (-(q * (E * S.card) / (200000 * r ^ 3 * K))) :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    linarith
  refine h1.trans ((Finset.sum_le_sum fun S hS => Finset.sum_le_sum fun Z hZ => h2 S hS Z hZ).trans
    ?_)
  refine le_trans ?_ (sum_pairs_le U hn hx hnx)
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun S _ _ => ?_)
  · intro S hS
    obtain ⟨h1, h2, -⟩ := Finset.mem_filter.1 hS
    exact Finset.mem_filter.2 ⟨h1, h2⟩
  · exact Finset.sum_nonneg fun Z _ => by positivity

/-- (T3) holds with high probability. -/
theorem t3_fail_le {U : Finset V} {q Kx : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hn : (U.card : ℝ) * Real.exp (-(0.13 * q * Kx)) ≤ 1) :
    ppr (fun _ : V => bern q) (fun y => ¬ T3Prop G U y q Kx) ≤
      2 * U.card * Real.exp (-(0.13 * q * Kx)) := by
  have hμ := isPD_bern (ι := V) hq0.le hq1
  set x := Real.exp (-(0.13 * q * Kx))
  set A := U.powerset.filter (fun X => X.Nonempty ∧ Kx * X.card ≤ (extNb G U X ∅).card)
  have hsub : ∀ y, ¬ T3Prop G U y q Kx → ∃ X ∈ A,
      (cntT (extNb G U X ∅) y : ℝ) ≤ q * (extNb G U X ∅).card / 2 := by
    intro y hy
    simp only [T3Prop, not_forall, not_le] at hy
    obtain ⟨X, hXU, hXn, hXK, hlt⟩ := hy
    exact ⟨X, Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hXU, hXn, hXK⟩, hlt.le⟩
  refine (ppr_mono hμ hsub).trans ((ppr_exists_le hμ A _).trans ?_)
  have h2 : ∀ X ∈ A, ppr (fun _ : V => bern q)
      (fun y => (cntT (extNb G U X ∅) y : ℝ) ≤ q * (extNb G U X ∅).card / 2) ≤ x ^ X.card := by
    intro X hX
    obtain ⟨-, -, hXK⟩ := Finset.mem_filter.1 hX
    refine (chernoff_lower hq0.le hq1 _ _).trans ?_
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.2 ?_
    have he := exp_neg_one_bounds
    have h1 : q * (Kx * X.card) ≤ q * (extNb G U X ∅).card := mul_le_mul_of_nonneg_left hXK hq0.le
    have h0 : (0 : ℝ) ≤ q * (extNb G U X ∅).card := by positivity
    nlinarith
  refine (Finset.sum_le_sum h2).trans (le_trans ?_ (sum_nonempty_pow_le U (by positivity) hn))
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun X hX => ?_) (fun X _ _ => by positivity)
  obtain ⟨h1, h2, -⟩ := Finset.mem_filter.1 hX
  exact Finset.mem_filter.2 ⟨h1, h2⟩

/-- The random set is not too large. -/
theorem R_fail_le {U : Finset V} {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) :
    ppr (fun _ : V => bern q)
      (fun y => ¬ ((U.filter (fun v => y v = true)).card : ℝ) < 2 * (0.55 * q * U.card)) ≤
      Real.exp (-(0.0025 * q * U.card)) := by
  have hμ := isPD_bern (ι := V) hq0.le hq1
  refine (ppr_mono hμ (Q := fun y => 1.1 * q * U.card ≤ cntT U y) fun y hy => ?_).trans ?_
  · simp only [not_lt] at hy; simp only [cntT]; linarith
  refine (chernoff_upper_lam hq0.le hq1 U _ (l := 0.05) (by norm_num)).trans
    (Real.exp_le_exp.2 ?_)
  have h1 := Real.abs_exp_sub_one_sub_id_le (x := 0.05) (by norm_num [abs_of_pos])
  have h2 := (abs_le.1 h1).2
  have h0 : (0 : ℝ) ≤ q * U.card := by positivity
  nlinarith

end union

end

end Lovasz
