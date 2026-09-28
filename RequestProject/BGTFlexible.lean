module
public import RequestProject.BGTGleason

/-!
# Flexible trapping: parameterised Gleason estimates

This file generalises the escape-norm estimates of Theorem 8.1 of Breuillard–Green–Tao (proved in
`BGTEscape.lean` and `BGTGleason.lean` for the fixed trapping times `1000` and `⌈10⁶K³⌉`) to an
arbitrary first-trapping time `p ≥ 1`, an arbitrary second-trapping time `m ≥ 1` and an arbitrary
conjugated-product length `N ≥ 3 p κ`.

* `Lovasz.BGT.HasFlexibleTrapping`: the flexible trapping data;
* `Lovasz.BGT.escNorm_conj_le_flex`: `‖h⁻¹ g h‖ ≤ p ‖g‖` for `h ∈ B⁴⁹`;
* `Lovasz.BGT.escNorm_list_prod_le_flex`: `‖g₁ ⋯ gₙ‖ ≤ 4 p κ m (‖g₁‖ + ⋯ + ‖gₙ‖)`;
* `Lovasz.BGT.escNorm_commutator_le_flex`:
  `‖g⁻¹ h⁻¹ g h‖ ≤ 4 p² κ (4 p κ m)² ‖g‖ ‖h‖` for `g, h ∈ B¹⁰`.
-/

@[expose] public section

open scoped Pointwise
open Finset Function

namespace Lovasz.BGT

variable {G : Type*} [Group G]

/-- **Flexible trapping data** (a variant of Definition 7.1 of Breuillard–Green–Tao with free
trapping times).  `B` is a `κ`-approximate group with `κ ≥ 2`, `p, m ≥ 1`, `3 p κ ≤ N`, and `S`
is a symmetric set such that
1. `(S^{B⁴})^N ⊆ B`;
2. (first trapping) if `g, …, g^p ∈ B¹⁰⁰` then `g ∈ B`;
3. (second trapping) if `g, …, g^m ∈ B` then `g ∈ S`. -/
def HasFlexibleTrapping (κ p m N : ℕ) (B S : Set G) : Prop :=
  IsBGTApproxGroup (κ : ℝ) B ∧ 2 ≤ κ ∧ 1 ≤ p ∧ 1 ≤ m ∧ 3 * p * κ ≤ N ∧ S⁻¹ = S ∧
    conjSet S (B ^ 4) ^ N ⊆ B ∧
    (∀ g : G, (∀ i : ℕ, 1 ≤ i → i ≤ p → g ^ i ∈ B ^ 100) → g ∈ B) ∧
    (∀ g : G, (∀ i : ℕ, 1 ≤ i → i ≤ m → g ^ i ∈ B) → g ∈ S)

/-! ### First-trapping consequences -/

/-- The first trapping condition with time `p`, iterated: if `g⁰, …, gⁿ ∈ A¹⁰⁰`, then `gʲ ∈ A`
whenever `p j ≤ n`. -/
lemma pow_mem_of_trapping {A : Set G} {p : ℕ}
    (htrap : ∀ g : G, (∀ i : ℕ, 1 ≤ i → i ≤ p → g ^ i ∈ A ^ 100) → g ∈ A)
    {g : G} {n : ℕ} (h : ∀ i ≤ n, g ^ i ∈ A ^ 100) {j : ℕ} (hj : p * j ≤ n) : g ^ j ∈ A := by
  apply htrap
  intro i _ hi
  rw [← pow_mul]
  exact h _ (le_trans (by rw [Nat.mul_comm j i]; exact Nat.mul_le_mul_right j hi) hj)

/-- If `g⁰, …, gⁿ ∈ A¹⁰⁰` then `‖g‖ ≤ p/(n+1)`. -/
lemma escNorm_le_of_trapping {A : Set G} {p : ℕ} (hp : 1 ≤ p)
    (htrap : ∀ g : G, (∀ i : ℕ, 1 ≤ i → i ≤ p → g ^ i ∈ A ^ 100) → g ∈ A)
    {g : G} {n : ℕ} (h : ∀ i ≤ n, g ^ i ∈ A ^ 100) : escNorm A g ≤ p / (n + 1) := by
  have h1 := escNorm_le_of_forall (A := A) (g := g) (n := n / p)
    (fun i hi => pow_mem_of_trapping htrap h (le_trans (Nat.mul_le_mul_left p hi)
      (Nat.mul_div_le n p)))
  refine h1.trans ?_
  have : (n : ℝ) + 1 ≤ p * ((n / p : ℕ) + 1) := by
    have : n + 1 ≤ p * (n / p + 1) := by
      have := Nat.lt_div_mul_add (a := n) (b := p) (by omega)
      rw [mul_comm] at this ⊢
      linarith
    exact_mod_cast this
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/-- If `t ≤ c/(n+1)` whenever `n δ < 1`, then `t ≤ c δ` (for `c > 0`). -/
lemma le_of_forall_nat_mul_lt_mul {t δ c : ℝ} (hc : 0 < c) (hδ : 0 ≤ δ)
    (h : ∀ n : ℕ, n * δ < 1 → t ≤ c / (n + 1)) : t ≤ c * δ := by
  rcases hδ.lt_or_eq with hpos | rfl
  · set m := ⌈1 / δ⌉₊ with hm
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (by
      rw [hm]; exact (Nat.ceil_pos.2 (by positivity)).ne')
    have hmle : 1 / δ ≤ m := Nat.le_ceil _
    have hmlt : (m : ℝ) < 1 / δ + 1 := Nat.ceil_lt_add_one (by positivity)
    have hcast : ((m - 1 : ℕ) : ℝ) = m - 1 := by rw [Nat.cast_sub hm1, Nat.cast_one]
    have hn : ((m - 1 : ℕ) : ℝ) * δ < 1 := by
      rw [hcast]
      have : ((m : ℝ) - 1) < 1 / δ := by linarith
      calc ((m : ℝ) - 1) * δ < 1 / δ * δ := mul_lt_mul_of_pos_right this hpos
        _ = 1 := by field_simp
    refine (h _ hn).trans ?_
    rw [hcast, sub_add_cancel, div_le_iff₀ (by linarith)]
    have : 1 ≤ δ * m := by rw [div_le_iff₀ hpos] at hmle; linarith
    nlinarith
  · rw [mul_zero]
    by_contra hc'
    push_neg at hc'
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < t / c by positivity)
    have := h n (by simp)
    have e : c / ((n : ℝ) + 1) = c * (1 / (n + 1)) := by ring
    rw [lt_div_iff₀ hc] at hn
    linarith

/-- The escape-norm consequence (8.8) of the first trapping condition with time `p`: if
`F(1) ≥ 1`, `F` is positive only on `A¹⁰⁰`, and `|∂_g F| ≤ δ`, then `‖g‖ ≤ p δ`. -/
lemma escNorm_le_of_abs_dif_le_flex {A : Set G} {p : ℕ} (hp : 1 ≤ p) (hAinv : A⁻¹ = A)
    (htrap : ∀ g : G, (∀ i : ℕ, 1 ≤ i → i ≤ p → g ^ i ∈ A ^ 100) → g ∈ A)
    {F : G → ℝ} (hF1 : 1 ≤ F 1) (hFpos : ∀ x, 0 < F x → x ∈ A ^ 100) {g : G} {δ : ℝ}
    (hδ : 0 ≤ δ) (h : ∀ x, |dif g F x| ≤ δ) : escNorm A g ≤ p * δ := by
  have key : ∀ i : ℕ, 1 - i * δ ≤ F (g⁻¹ ^ i) := by
    intro i
    induction i with
    | zero => simpa using hF1
    | succ i ih =>
      have := h (g⁻¹ ^ i)
      rw [abs_le] at this
      simp only [dif] at this
      rw [pow_succ', Nat.cast_succ]
      linarith [this.1]
  rw [← escNorm_inv hAinv]
  refine le_of_forall_nat_mul_lt_mul (by exact_mod_cast hp) hδ fun n hn => ?_
  refine escNorm_le_of_trapping hp htrap fun i hi => hFpos _ ?_
  have : (i : ℝ) * δ < 1 := lt_of_le_of_lt (by gcongr) hn
  linarith [key i]

/-- **Theorem 8.1 (i)** with first-trapping time `p`: `‖h⁻¹ g h‖ ≤ p ‖g‖` for `h ∈ A⁴⁹`. -/
theorem escNorm_conj_le_flex {A : Set G} (hA1 : (1 : G) ∈ A) (hAinv : A⁻¹ = A) {p : ℕ}
    (hp : 1 ≤ p) (htrap : ∀ g : G, (∀ i : ℕ, 1 ≤ i → i ≤ p → g ^ i ∈ A ^ 100) → g ∈ A)
    {g h : G} (hh : h ∈ A ^ 49) : escNorm A (h⁻¹ * g * h) ≤ p * escNorm A g := by
  have hh' : h⁻¹ ∈ A ^ 49 := by
    have : (A ^ 49)⁻¹ = A ^ 49 := by rw [← inv_pow, hAinv]
    rw [← this]; exact Set.inv_mem_inv.2 hh
  have hconj : ∀ i : ℕ, g ^ i ∈ A → (h⁻¹ * g * h) ^ i ∈ A ^ 100 := by
    intro i hi
    have e : (h⁻¹ * g * h) ^ i = h⁻¹ * g ^ i * h := by
      simpa using conj_pow (a := h⁻¹) (b := g) (i := i)
    rw [e]
    have : h⁻¹ * g ^ i * h ∈ A ^ 49 * A * A ^ 49 :=
      Set.mul_mem_mul (Set.mul_mem_mul hh' hi) hh
    rw [← pow_succ, ← pow_add] at this
    exact Set.pow_subset_pow_right hA1 (by norm_num) this
  refine le_of_forall_nat_mul_lt_mul (by exact_mod_cast hp) (escNorm_nonneg hA1) fun n hn => ?_
  exact escNorm_le_of_trapping hp htrap fun i hi =>
    hconj i (pow_mem_of_mul_escNorm_lt hA1 hn i hi)

/-! ### The parameterised bootstrapping core -/

/-- Parameterised core of Theorem 8.1 (ii): with first-trapping time `p` and second-trapping time
`M`, the escape norm is bounded by `4 p K M` times the word metric of `‖·‖ + ε`. -/
theorem escNorm_le_wdist_core_flex [DecidableEq G] {A : Finset G} (hA1 : (1 : G) ∈ A)
    (hAinv : A⁻¹ = A) {K : ℝ} (hK : 2 ≤ K) (hAA : (#(A * A) : ℝ) ≤ K * #A) {S : Set G}
    (hSinv : S⁻¹ = S) {p N M : ℕ} (hp : 1 ≤ p) (hN : 3 * p * K ≤ N) (hM : 1 ≤ M)
    (hQN : conjSet S ((A : Set G) ^ 4) ^ N ⊆ (A : Set G))
    (htrap1 : ∀ g : G, (∀ i : ℕ, 1 ≤ i → i ≤ p → g ^ i ∈ (A : Set G) ^ 100) → g ∈ (A : Set G))
    (htrap2 : ∀ g : G, (∀ i : ℕ, 1 ≤ i → i ≤ M → g ^ i ∈ (A : Set G)) → g ∈ S)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (g : G) :
    escNorm (A : Set G) g ≤ (p : ℝ) * (4 * (K * M)) * wdist (fun g => escNorm (A : Set G) g + ε) g := by
  have hA : A.Nonempty := ⟨1, hA1⟩
  have hA1' : (1 : G) ∈ (A : Set G) := hA1
  have hAinv' : (A : Set G)⁻¹ = A := by rw [← coe_inv, hAinv]
  set w : G → ℝ := fun g => escNorm (A : Set G) g + ε with hw
  have hw0 : ∀ g, 0 ≤ w g := fun g => by
    simp only [hw]; linarith [escNorm_nonneg (g := g) hA1']
  have hwinv : ∀ g, w g⁻¹ = w g := fun g => by simp only [hw, escNorm_inv hAinv']
  have hwε : ∀ g, ε ≤ w g := fun g => by
    simp only [hw]; linarith [escNorm_nonneg (g := g) hA1']
  have hwesc : ∀ g, escNorm (A : Set G) g ≤ w g := fun g => by simp only [hw]; linarith
  set Q := conjSet S ((A : Set G) ^ 4) with hQ
  have hS1 : (1 : G) ∈ S := htrap2 1 (fun i _ _ => by simpa using hA1')
  have hQ1 : (1 : G) ∈ Q := ⟨1, hS1, 1, Set.one_mem_pow hA1', by simp⟩
  have hQinv : Q⁻¹ = Q := conjSet_inv hSinv
  have hK0 : (0 : ℝ) < K := by linarith
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpK : (0 : ℝ) < p * K := by positivity
  have hN0 : 0 < N := by
    have : (0 : ℝ) < N := by linarith
    exact_mod_cast this
  have hSA : ∀ s ∈ S, s ∈ A := by
    intro s hs
    have h1 : s ∈ Q := ⟨s, hs, 1, Set.one_mem_pow hA1', by simp⟩
    have h2 : Q ⊆ Q ^ N := by
      simpa using Set.pow_subset_pow_right hQ1 (show 1 ≤ N from hN0)
    exact hQN (h2 h1)
  have hD : ε ≤ wD w A := wD_pos_of hw0 hε1 hwε hA1
  have hD0 : 0 < wD w A := lt_of_lt_of_le hε0 hD
  set Ψ := bigPsi hA w Q N with hΨ
  have hΨ1 : 1 ≤ Ψ 1 := one_le_bigPsi hA hw0 hD0 hQ1 hN0 hAinv hA1
  have hΨ0 : ∀ x, 0 ≤ Ψ x := bigPsi_nonneg hA hw0 hD0
  have hΨK : ∀ x, Ψ x ≤ K := bigPsi_le hA hw0 hD0 hAA
  have hΨpos : ∀ x, 0 < Ψ x → x ∈ (A : Set G) ^ 100 := fun x hx =>
    Set.pow_subset_pow_right hA1' (by norm_num) (bigPsi_pos_mem hA hw0 hD0 hQ1 hQN hx)
  have esc88 : ∀ g : G, ∀ δ : ℝ, 0 ≤ δ → (∀ x, |dif g Ψ x| ≤ δ) →
      escNorm (A : Set G) g ≤ p * δ :=
    fun g δ hδ h => escNorm_le_of_abs_dif_le_flex hp hAinv' htrap1 hΨ1 hΨpos hδ h
  have hdK : ∀ g x, |dif g Ψ x| ≤ K := by
    intro g x
    simp only [dif]
    rw [abs_le]
    constructor <;> linarith [hΨ0 x, hΨK x, hΨ0 (g⁻¹ * x), hΨK (g⁻¹ * x)]
  -- the bootstrapping hypothesis
  let P : ℝ → Prop := fun X => ∀ g x, |dif g Ψ x| ≤ X * wdist w g
  have Pmono : ∀ X Y, X ≤ Y → P X → P Y := fun X Y hXY hX g x =>
    (hX g x).trans (mul_le_mul_of_nonneg_right hXY (wdist_nonneg hw0 g))
  have P0 : P (K / ε) := by
    intro g x
    refine (abs_dif_bigPsi_le hA hw0 hD0 hAA hwinv hQ1 hQN g x).trans ?_
    rw [div_mul_eq_mul_div, mul_div_assoc]
    gcongr
    exact wdist_nonneg hw0 g
  have hr : 2 * K * p / (N : ℝ) ≤ 2 / 3 := by
    rw [div_le_iff₀ (by exact_mod_cast hN0)]; linarith
  have step : ∀ X, 1 / (p : ℝ) ≤ X → P X → P (K * M + 2 / 3 * X) := by
    intro X hX hPX
    have hX0 : 0 < X := lt_of_lt_of_le (by positivity) hX
    have hpX : 1 ≤ (p : ℝ) * X := by
      rw [div_le_iff₀ (by positivity)] at hX; linarith
    -- lower bound on `D`
    have hDX : 1 / ((p : ℝ) * X) ≤ wD w A := by
      refine le_wD (by rw [div_le_one (by positivity)]; exact hpX) fun z hz => ?_
      by_contra hc
      push_neg at hc
      have h1 := esc88 z (X * wdist w z) (mul_nonneg hX0.le (wdist_nonneg hw0 z)) (hPX z)
      have h2 : (p : ℝ) * (X * wdist w z) < 1 := by
        rw [lt_div_iff₀ (by positivity)] at hc; linarith
      exact hz (mem_of_escNorm_lt_one (A := (A : Set G)) hA1' (by linarith))
    have hLip : ∀ g y, |dif g (phi w A hA) y| ≤ (p : ℝ) * X * wdist w g := by
      intro g y
      refine (abs_dif_phi_le hA hw0 hwinv hD0 g y).trans ?_
      rw [div_le_iff₀ hD0]
      have h1 : 1 ≤ (p : ℝ) * X * wD w A := by
        rw [div_le_iff₀ (by positivity)] at hDX; linarith
      nlinarith [wdist_nonneg hw0 g]
    have hbound : ∀ g x, |dif g Ψ x| ≤ (K * M + 2 / 3 * X) * w g := by
      intro g x
      by_cases hgS : g ∈ S
      · have hgA := hSA g hgS
        -- second derivatives
        have hsec : ∀ h ∈ S, ∀ x, |dif h (dif g Ψ) x| ≤ 2 / 3 * X * wdist w g := by
          intro h hh x
          refine (abs_dif_dif_bigPsi_le hA hw0 hD0 hA1 hAA subset_rfl hQinv hgA hh
            (hLip g) x).trans ?_
          have := mul_le_mul_of_nonneg_right hr (mul_nonneg hX0.le (wdist_nonneg hw0 g))
          calc 2 * K * ((p : ℝ) * X * wdist w g) / N = 2 * K * p / N * (X * wdist w g) := by
                ring
            _ ≤ 2 / 3 * (X * wdist w g) := this
            _ = 2 / 3 * X * wdist w g := by ring
        -- Taylor expansion
        have htaylor : ∀ n : ℕ, 1 ≤ n → (∀ i < n, g ^ i ∈ S) →
            |dif g Ψ x| ≤ K / n + 2 / 3 * X * wdist w g := by
          intro n hn hpow
          have hn' : (0 : ℝ) < n := by exact_mod_cast hn
          have e := dif_pow g Ψ x n
          have h1 : |∑ i ∈ range n, dif (g ^ i) (dif g Ψ) x| ≤ n * (2 / 3 * X * wdist w g) := by
            calc |∑ i ∈ range n, dif (g ^ i) (dif g Ψ) x|
                ≤ ∑ i ∈ range n, |dif (g ^ i) (dif g Ψ) x| := abs_sum_le_sum_abs _ _
              _ ≤ ∑ _i ∈ range n, 2 / 3 * X * wdist w g :=
                  sum_le_sum fun i hi => hsec _ (hpow i (mem_range.1 hi)) x
              _ = n * (2 / 3 * X * wdist w g) := by rw [sum_const, card_range, nsmul_eq_mul]
          have h2 : n * |dif g Ψ x| ≤ K + n * (2 / 3 * X * wdist w g) := by
            have : (n : ℝ) * dif g Ψ x = dif (g ^ n) Ψ x - ∑ i ∈ range n, dif (g ^ i) (dif g Ψ) x := by
              rw [e]; ring
            calc (n : ℝ) * |dif g Ψ x| = |(n : ℝ) * dif g Ψ x| := by
                  rw [abs_mul, abs_of_pos hn']
              _ ≤ |dif (g ^ n) Ψ x| + |∑ i ∈ range n, dif (g ^ i) (dif g Ψ) x| := by
                  rw [this]; exact abs_sub _ _
              _ ≤ K + n * (2 / 3 * X * wdist w g) := add_le_add (hdK _ _) h1
          rw [div_add' _ _ _ hn'.ne', le_div_iff₀ hn']
          linarith
        have hmain : |dif g Ψ x| ≤ K * M * escNorm (A : Set G) g + 2 / 3 * X * wdist w g := by
          rcases (escNorm_nonneg (g := g) hA1').lt_or_eq with hpos | hzero
          · set n := ⌈1 / (M * escNorm (A : Set G) g)⌉₊ with hn
            have hM' : (0 : ℝ) < M := by exact_mod_cast hM
            have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (by
              rw [hn]; exact (Nat.ceil_pos.2 (by positivity)).ne')
            have hnle : 1 / (M * escNorm (A : Set G) g) ≤ n := Nat.le_ceil _
            have hnlt : (n : ℝ) < 1 / (M * escNorm (A : Set G) g) + 1 :=
              Nat.ceil_lt_add_one (by positivity)
            have hpow : ∀ i < n, g ^ i ∈ S := by
              intro i hi
              apply htrap2
              intro k _ hk
              rw [← pow_mul]
              refine pow_mem_of_mul_escNorm_lt hA1' (n := (n - 1) * M) ?_ _ ?_
              · have hcast : (((n - 1) * M : ℕ) : ℝ) = (n - 1) * M := by
                  rw [Nat.cast_mul, Nat.cast_sub hn1, Nat.cast_one]
                rw [hcast]
                have : ((n : ℝ) - 1) < 1 / (M * escNorm (A : Set G) g) := by linarith
                have h3 : ((n : ℝ) - 1) * (M * escNorm (A : Set G) g) < 1 := by
                  rw [lt_div_iff₀ (by positivity)] at this; exact this
                nlinarith
              · exact Nat.mul_le_mul (by omega) hk
            have h1 := htaylor n hn1 hpow
            have h2 : K / n ≤ K * M * escNorm (A : Set G) g := by
              rw [div_le_iff₀ (by exact_mod_cast hn1)]
              have : 1 ≤ M * escNorm (A : Set G) g * n := by
                rw [div_le_iff₀ (by positivity)] at hnle; linarith
              nlinarith
            linarith
          · rw [← hzero, mul_zero, zero_add]
            have hall : ∀ i : ℕ, g ^ i ∈ S := fun i => htrap2 _ fun k _ _ => by
              rw [← pow_mul]; exact pow_mem_of_escNorm_eq_zero hA1' hzero.symm _
            refine le_of_forall_pos_lt_add fun δ hδ => ?_
            obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < δ / K by positivity)
            have h1 := htaylor (n + 1) (by omega) (fun i _ => hall i)
            have h2 : K / ((n + 1 : ℕ) : ℝ) < δ := by
              have := (lt_div_iff₀ hK0).1 hn
              push_cast
              calc K / ((n : ℝ) + 1) = 1 / ((n : ℝ) + 1) * K := by ring
                _ < δ := this
            linarith
        calc |dif g Ψ x| ≤ K * M * escNorm (A : Set G) g + 2 / 3 * X * wdist w g := hmain
          _ ≤ K * M * w g + 2 / 3 * X * w g := by
              gcongr
              · exact hwesc g
              · exact wdist_le hw0 g
          _ = (K * M + 2 / 3 * X) * w g := by ring
      · -- `g ∉ S`: the escape norm of `g` is at least `1/M`
        have hge : 1 ≤ M * escNorm (A : Set G) g := by
          by_contra hc
          push_neg at hc
          exact hgS (htrap2 g fun i _ hi => pow_mem_of_mul_escNorm_lt hA1' hc i hi)
        have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
        calc |dif g Ψ x| ≤ K := hdK g x
          _ ≤ K * (M * escNorm (A : Set G) g) := by nlinarith
          _ = K * M * escNorm (A : Set G) g := by ring
          _ ≤ K * M * w g := mul_le_mul_of_nonneg_left (hwesc g) (by positivity)
          _ ≤ K * M * w g + 2 / 3 * X * w g := by
              have := hw0 g
              have : 0 ≤ 2 / 3 * X * w g := by positivity
              linarith
          _ = (K * M + 2 / 3 * X) * w g := by ring
    exact abs_dif_le_wdist (by positivity) hbound
  -- iterate the bootstrapping step
  have hKM : (1 : ℝ) ≤ K * M := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  have iter : ∀ k : ℕ, P (3 * (K * M) + K / ε * (2 / 3) ^ k) := by
    intro k
    induction k with
    | zero =>
      refine Pmono _ _ ?_ P0
      simp only [pow_zero, mul_one]; linarith
    | succ k ih =>
      have hX : 1 / (p : ℝ) ≤ 3 * (K * M) + K / ε * (2 / 3) ^ k := by
        have : 0 ≤ K / ε * (2 / 3) ^ k := by positivity
        have h1p : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one (by positivity)]; exact hp1
        linarith
      have := step _ hX ih
      convert this using 1
      rw [pow_succ]; ring
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show 0 < (K * M) / (K / ε) by positivity)
    (show (2 / 3 : ℝ) < 1 by norm_num)
  have hk' : K / ε * (2 / 3) ^ k ≤ K * M := by
    rw [lt_div_iff₀ (by positivity)] at hk; linarith
  have P4 : P (4 * (K * M)) := Pmono _ _ (by linarith) (iter k)
  have := esc88 g (4 * (K * M) * wdist w g) (by
    have := wdist_nonneg hw0 g; positivity) (P4 g)
  calc escNorm (A : Set G) g ≤ (p : ℝ) * (4 * (K * M) * wdist w g) := this
    _ = (p : ℝ) * (4 * (K * M)) * wdist w g := by ring

end Lovasz.BGT
