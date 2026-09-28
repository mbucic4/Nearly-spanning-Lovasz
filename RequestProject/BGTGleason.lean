module
public import RequestProject.BGTGleasonTools

/-!
# Gleason's lemmas for strong approximate groups (Theorem 8.1 of Breuillard–Green–Tao)

* `Lovasz.BGT.escNorm_list_prod_le`: Theorem 8.1 (ii), the product property of the escape norm;
* `Lovasz.BGT.escNorm_commutator_le`: Theorem 8.1 (iii), the commutator property.

Theorem 8.1 (i) is `Lovasz.BGT.escNorm_conj_le`.
-/

@[expose] public section

open scoped Pointwise
open Finset Function

namespace Lovasz.BGT

variable {G : Type*} [Group G]

/-! ### Generic lemmas -/

/-- If `t ≤ 1000/(n+1)` whenever `n δ < 1`, then `t ≤ 1000 δ`. -/
lemma le_of_forall_nat_mul_lt {t δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ n : ℕ, n * δ < 1 → t ≤ 1000 / (n + 1)) : t ≤ 1000 * δ := by
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
    by_contra hc
    push_neg at hc
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < t / 1000 by positivity)
    have := h n (by simp)
    have e : 1000 / ((n : ℝ) + 1) = 1000 * (1 / (n + 1)) := by ring
    linarith

/-- The escape-norm consequence (8.8) of the first trapping condition: if `F(1) ≥ 1`, `F` is
positive only on `A¹⁰⁰`, and `|∂_g F| ≤ δ`, then `‖g‖ ≤ 1000 δ`. -/
lemma escNorm_le_of_abs_dif_le {A : Set G} (hAinv : A⁻¹ = A)
    (htrap : ∀ g : G, (∀ i : ℕ, 1 ≤ i → i ≤ 1000 → g ^ i ∈ A ^ 100) → g ∈ A)
    {F : G → ℝ} (hF1 : 1 ≤ F 1) (hFpos : ∀ x, 0 < F x → x ∈ A ^ 100) {g : G} {δ : ℝ}
    (hδ : 0 ≤ δ) (h : ∀ x, |dif g F x| ≤ δ) : escNorm A g ≤ 1000 * δ := by
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
  refine le_of_forall_nat_mul_lt hδ fun n hn => ?_
  refine escNorm_le_of_first_trapping htrap fun i hi => hFpos _ ?_
  have : (i : ℝ) * δ < 1 := lt_of_le_of_lt (by gcongr) hn
  linarith [key i]

/-- Passing from a bound in terms of a weight to a bound in terms of the associated word metric
(the last step of the bootstrapping argument). -/
lemma abs_dif_le_wdist {w : G → ℝ} {F : G → ℝ} {Y : ℝ} (hY : 0 ≤ Y)
    (h : ∀ g x, |dif g F x| ≤ Y * w g) (g x : G) : |dif g F x| ≤ Y * wdist w g := by
  have hl : ∀ l : List G, ∀ x, |dif l.prod F x| ≤ Y * (l.map w).sum := by
    intro l
    induction l with
    | nil => intro x; simp [dif_one]
    | cons a l ih =>
      intro x
      simp only [List.prod_cons, List.map_cons, List.sum_cons]
      rw [dif_mul]
      calc |dif l.prod F (a⁻¹ * x) + dif a F x| ≤ |dif l.prod F (a⁻¹ * x)| + |dif a F x| :=
            abs_add_le _ _
        _ ≤ Y * (l.map w).sum + Y * w a := add_le_add (ih _) (h a x)
        _ = Y * (w a + (l.map w).sum) := by ring
  rcases hY.lt_or_eq with hpos | rfl
  · have : |dif g F x| / Y ≤ wdist w g :=
      le_wdist fun l hl' => by rw [div_le_iff₀ hpos, mul_comm]; simpa [hl'] using hl l x
    rwa [div_le_iff₀ hpos, mul_comm] at this
  · simpa using hl [g] x

/-! ### The auxiliary function `Ψ = |A|⁻¹ φ * ψ` -/

omit [Group G] in
lemma finsum_eq_sum_of_support {f : G → ℝ} {U : Finset G} (h : support f ⊆ U) :
    ∑ᶠ y, f y = ∑ y ∈ U, f y := finsum_eq_sum_of_support_subset f h

section Core

variable [DecidableEq G] {A : Finset G} (hA : A.Nonempty)

/-- The convolution `Ψ(x) = |A|⁻¹ ∑_y φ(y) ψ(y⁻¹ x)` of the proof of Theorem 8.1. -/
noncomputable def bigPsi (w : G → ℝ) (Q : Set G) (N : ℕ) : G → ℝ :=
  fun x => (1 / #A) * conv (phi w A hA) (psi Q (A : Set G) N) x

variable {w : G → ℝ} (hw0 : ∀ g, 0 ≤ w g) (hD : 0 < wD w A) {Q : Set G} {N : ℕ}
include hw0 hD

lemma support_phi_subset : support (phi w A hA) ⊆ ((A * A : Finset G) : Set G) :=
  fun x hx => by rw [mem_coe]; exact phi_mem hA hw0 hD hx

lemma conv_phi_eq_sum (k : G → ℝ) (x : G) :
    conv (phi w A hA) k x = ∑ y ∈ A * A, phi w A hA y * k (y⁻¹ * x) :=
  finsum_eq_sum_of_support fun _ hy =>
    support_phi_subset hA hw0 hD (support_mul_subset_left _ _ hy)

lemma one_le_bigPsi (hQ1 : (1 : G) ∈ Q) (hN : 0 < N) (hAinv : A⁻¹ = A)
    (hA1 : (1 : G) ∈ A) : 1 ≤ bigPsi hA w Q N 1 := by
  have hA' : (0 : ℝ) < #A := by exact_mod_cast hA.card_pos
  simp only [bigPsi]
  rw [conv_phi_eq_sum hA hw0 hD]
  have h1 : ∑ y ∈ A, phi w A hA y * psi Q (A : Set G) N (y⁻¹ * 1) = #A := by
    rw [← nsmul_one, ← sum_const]
    refine sum_congr rfl fun y hy => ?_
    have hy' : y⁻¹ ∈ A := by rw [← hAinv]; exact inv_mem_inv hy
    rw [phi_eq_one hA hw0 hy, mul_one, psi_eq_one hQ1 hN (by simpa using hy'), mul_one]
  have h2 : ∑ y ∈ A, phi w A hA y * psi Q (A : Set G) N (y⁻¹ * 1) ≤
      ∑ y ∈ A * A, phi w A hA y * psi Q (A : Set G) N (y⁻¹ * 1) :=
    sum_le_sum_of_subset_of_nonneg (subset_mul_left A hA1)
      (fun y _ _ => mul_nonneg (phi_nonneg hA _) (psi_nonneg _))
  rw [h1] at h2
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hA', one_mul]
  exact h2

lemma bigPsi_nonneg (x : G) : 0 ≤ bigPsi hA w Q N x := by
  simp only [bigPsi]
  rw [conv_phi_eq_sum hA hw0 hD]
  exact mul_nonneg (by positivity)
    (sum_nonneg fun y _ => mul_nonneg (phi_nonneg hA _) (psi_nonneg _))

lemma bigPsi_le {K : ℝ} (hAA : (#(A * A) : ℝ) ≤ K * #A) (x : G) : bigPsi hA w Q N x ≤ K := by
  have hA' : (0 : ℝ) < #A := by exact_mod_cast hA.card_pos
  simp only [bigPsi]
  rw [conv_phi_eq_sum hA hw0 hD]
  have h1 : ∑ y ∈ A * A, phi w A hA y * psi Q (A : Set G) N (y⁻¹ * x) ≤ #(A * A) := by
    rw [← nsmul_one, ← sum_const]
    refine sum_le_sum fun y _ => ?_
    exact mul_le_one₀ (phi_le_one hA hw0 hD _) (psi_nonneg _) (psi_le_one _)
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hA']
  linarith

lemma bigPsi_pos_mem (hQ1 : (1 : G) ∈ Q) (hQN : Q ^ N ⊆ (A : Set G)) {x : G}
    (hx : 0 < bigPsi hA w Q N x) : x ∈ (A : Set G) ^ 4 := by
  simp only [bigPsi] at hx
  rw [conv_phi_eq_sum hA hw0 hD] at hx
  have hsum : 0 < ∑ y ∈ A * A, phi w A hA y * psi Q (A : Set G) N (y⁻¹ * x) := by
    by_contra hc
    push_neg at hc
    have : (1 / (#A : ℝ)) * ∑ y ∈ A * A, phi w A hA y * psi Q (A : Set G) N (y⁻¹ * x) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hc
    linarith
  obtain ⟨y, hy, hpos⟩ := exists_lt_of_sum_lt (f := fun _ => (0 : ℝ)) (by simpa using hsum)
  have hpsi : psi Q (A : Set G) N (y⁻¹ * x) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hpos; exact lt_irrefl _ hpos
  have h1 := psi_mem hQ1 hQN hpsi
  have hy' : y ∈ (A : Set G) * A := by rw [← coe_mul]; exact hy
  have : y * (y⁻¹ * x) ∈ ((A : Set G) * A) * ((A : Set G) * A) := Set.mul_mem_mul hy' h1
  rw [mul_inv_cancel_left] at this
  have e : ((A : Set G) * A) * ((A : Set G) * A) = (A : Set G) ^ 4 := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rwa [e] at this

lemma finite_support_phi : (support (phi w A hA)).Finite :=
  (A * A).finite_toSet.subset (support_phi_subset hA hw0 hD)

lemma dif_bigPsi (g x : G) : dif g (bigPsi hA w Q N) x =
    (1 / #A) * conv (dif g (phi w A hA)) (psi Q (A : Set G) N) x := by
  have := dif_conv_left (finite_support_phi hA hw0 hD) (psi Q (A : Set G) N) g x
  simp only [dif, bigPsi] at this ⊢
  rw [← mul_sub, this]

lemma abs_dif_bigPsi_le {K : ℝ} (hAA : (#(A * A) : ℝ) ≤ K * #A)
    (hwinv : ∀ g, w g⁻¹ = w g) (hQ1 : (1 : G) ∈ Q) (hQN : Q ^ N ⊆ (A : Set G)) (g x : G) :
    |dif g (bigPsi hA w Q N) x| ≤ K * (wdist w g / wD w A) := by
  have hA' : (0 : ℝ) < #A := by exact_mod_cast hA.card_pos
  rw [dif_bigPsi hA hw0 hD, abs_mul, abs_of_pos (by positivity)]
  set U := (A * A).image (fun z => x * z⁻¹) with hU
  have hsupp : support (fun y => dif g (phi w A hA) y * psi Q (A : Set G) N (y⁻¹ * x)) ⊆ U := by
    intro y hy
    have hpsi : psi Q (A : Set G) N (y⁻¹ * x) ≠ 0 := right_ne_zero_of_mul hy
    have h1 := psi_mem hQ1 hQN hpsi
    rw [← coe_mul, mem_coe] at h1
    rw [mem_coe, hU, mem_image]
    exact ⟨y⁻¹ * x, h1, by group⟩
  have hbound := abs_finsum_le U hsupp (B := wdist w g / wD w A) (fun y _ => by
    rw [abs_mul, abs_of_nonneg (psi_nonneg _)]
    calc |dif g (phi w A hA) y| * psi Q (A : Set G) N (y⁻¹ * x)
        ≤ (wdist w g / wD w A) * 1 :=
          mul_le_mul (abs_dif_phi_le hA hw0 hwinv hD g y) (psi_le_one _) (psi_nonneg _)
            (div_nonneg (wdist_nonneg hw0 g) hD.le)
      _ = wdist w g / wD w A := mul_one _)
  have hUc : (#U : ℝ) ≤ K * #A := le_trans (by exact_mod_cast card_image_le) hAA
  have hnn : 0 ≤ wdist w g / wD w A := div_nonneg (wdist_nonneg hw0 g) hD.le
  calc 1 / (#A : ℝ) * |conv (dif g (phi w A hA)) (psi Q (A : Set G) N) x|
      ≤ 1 / #A * (#U * (wdist w g / wD w A)) := by gcongr; exact hbound
    _ ≤ 1 / #A * ((K * #A) * (wdist w g / wD w A)) := by gcongr
    _ = K * (wdist w g / wD w A) := by field_simp

lemma abs_dif_dif_bigPsi_le {K : ℝ} (hA1 : (1 : G) ∈ A) (hAA : (#(A * A) : ℝ) ≤ K * #A)
    {S : Set G} (hSQ : conjSet S ((A : Set G) ^ 4) ⊆ Q) (hQinv : Q⁻¹ = Q) {g h : G}
    (hg : g ∈ A) (hh : h ∈ S) {L : ℝ} (hL : ∀ y, |dif g (phi w A hA) y| ≤ L) (x : G) :
    |dif h (dif g (bigPsi hA w Q N)) x| ≤ 2 * K * L / N := by
  have hA' : (0 : ℝ) < #A := by exact_mod_cast hA.card_pos
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL 1)
  have hfun : dif g (bigPsi hA w Q N) =
      fun x => (1 / #A) * conv (dif g (phi w A hA)) (psi Q (A : Set G) N) x :=
    funext fun x => dif_bigPsi hA hw0 hD g x
  have hfin := support_dif_finite (finite_support_phi hA hw0 hD) g
  have hdd : dif h (dif g (bigPsi hA w Q N)) x = (1 / #A) *
      ∑ᶠ y, dif g (phi w A hA) y * dif (y⁻¹ * h * y) (psi Q (A : Set G) N) (y⁻¹ * x) := by
    rw [hfun, ← dif_conv_right hfin]
    simp only [dif]
    ring
  rw [hdd, abs_mul, abs_of_pos (by positivity)]
  set U := (A * A) ∪ (A * A).image (fun z => g * z) with hU
  have hsuppF : ∀ y, dif g (phi w A hA) y ≠ 0 → y ∈ U := by
    intro y hy
    rw [hU, mem_union, mem_image]
    by_cases h0 : phi w A hA y = 0
    · right
      have : phi w A hA (g⁻¹ * y) ≠ 0 := by
        intro h1; apply hy; simp [dif, h0, h1]
      exact ⟨g⁻¹ * y, phi_mem hA hw0 hD this, by group⟩
    · left; exact phi_mem hA hw0 hD h0
  have hU4 : ∀ y ∈ U, y ∈ (A : Set G) ^ 4 := by
    intro y hy
    have hAA4 : (A : Set G) * A ⊆ (A : Set G) ^ 4 := by
      rw [← sq]; exact Set.pow_subset_pow_right (by simpa using hA1) (by norm_num)
    have hA3 : (A : Set G) * ((A : Set G) * A) ⊆ (A : Set G) ^ 4 := by
      rw [← sq, ← pow_succ']; exact Set.pow_subset_pow_right (by simpa using hA1) (by norm_num)
    rw [hU, mem_union, mem_image] at hy
    rcases hy with hy | ⟨z, hz, rfl⟩
    · exact hAA4 (by rw [← coe_mul]; exact hy)
    · exact hA3 (Set.mul_mem_mul (by simpa using hg) (by rw [← coe_mul]; exact hz))
  have hsupp : support (fun y => dif g (phi w A hA) y *
      dif (y⁻¹ * h * y) (psi Q (A : Set G) N) (y⁻¹ * x)) ⊆ U :=
    fun y hy => hsuppF y (left_ne_zero_of_mul hy)
  have hbound := abs_finsum_le U hsupp (B := L * (1 / N)) (fun y hy => by
    rw [abs_mul]
    have hq : y⁻¹ * h * y ∈ Q := hSQ ⟨h, hh, y, hU4 y hy, rfl⟩
    exact mul_le_mul (hL y) (abs_dif_psi_le hQinv hq _) (abs_nonneg _) hL0)
  have hUc : (#U : ℝ) ≤ 2 * K * #A := by
    have h1 : #U ≤ #(A * A) + #(A * A) :=
      (card_union_le _ _).trans (Nat.add_le_add_left card_image_le _)
    have h2 : (#U : ℝ) ≤ #(A * A) + #(A * A) := by exact_mod_cast h1
    linarith
  calc 1 / (#A : ℝ) * |∑ᶠ y, dif g (phi w A hA) y *
        dif (y⁻¹ * h * y) (psi Q (A : Set G) N) (y⁻¹ * x)|
      ≤ 1 / #A * (#U * (L * (1 / N))) := by gcongr
    _ ≤ 1 / #A * ((2 * K * #A) * (L * (1 / N))) := by gcongr
    _ = 2 * K * L / N := by field_simp

end Core

/-! ### The bootstrapping argument for the product estimate -/

/-- The conjugation set `S^{A⁴}` is symmetric if `S` is. -/
lemma conjSet_inv {S B : Set G} (hS : S⁻¹ = S) : (conjSet S B)⁻¹ = conjSet S B := by
  ext x
  simp only [Set.mem_inv, conjSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨s, hs, b, hb, e⟩
    refine ⟨s⁻¹, by rw [← hS]; simpa using hs, b, hb, ?_⟩
    rw [← inv_inv x, e]; group
  · rintro ⟨s, hs, b, hb, rfl⟩
    refine ⟨s⁻¹, by rw [← hS]; simpa using hs, b, hb, ?_⟩
    group

/-- The core of the proof of Theorem 8.1 (ii) (the estimate (8.7)): for the regularised escape
norm `‖·‖ + ε`, the escape norm is bounded by `4000 K M` times the associated word metric. -/
theorem escNorm_le_wdist_core [DecidableEq G] {A : Finset G} (hA1 : (1 : G) ∈ A)
    (hAinv : A⁻¹ = A) {K : ℝ} (hK : 2 ≤ K) (hAA : (#(A * A) : ℝ) ≤ K * #A) {S : Set G}
    (hSinv : S⁻¹ = S) {N M : ℕ} (hN : 3000 * K ≤ N) (hM : 1 ≤ M)
    (hQN : conjSet S ((A : Set G) ^ 4) ^ N ⊆ (A : Set G))
    (htrap1 : ∀ g : G, (∀ i : ℕ, 1 ≤ i → i ≤ 1000 → g ^ i ∈ (A : Set G) ^ 100) → g ∈ (A : Set G))
    (htrap2 : ∀ g : G, (∀ i : ℕ, 1 ≤ i → i ≤ M → g ^ i ∈ (A : Set G)) → g ∈ S)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (g : G) :
    escNorm (A : Set G) g ≤ 1000 * (4 * (K * M)) * wdist (fun g => escNorm (A : Set G) g + ε) g := by
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
      escNorm (A : Set G) g ≤ 1000 * δ :=
    fun g δ hδ h => escNorm_le_of_abs_dif_le hAinv' htrap1 hΨ1 hΨpos hδ h
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
  have hr : 2 * K * 1000 / (N : ℝ) ≤ 2 / 3 := by
    rw [div_le_iff₀ (by exact_mod_cast hN0)]; linarith
  have step : ∀ X, 1 / 1000 ≤ X → P X → P (K * M + 2 / 3 * X) := by
    intro X hX hPX
    have hX0 : 0 < X := by linarith
    -- lower bound on `D`
    have hDX : 1 / (1000 * X) ≤ wD w A := by
      refine le_wD (by rw [div_le_one (by positivity)]; linarith) fun z hz => ?_
      by_contra hc
      push_neg at hc
      have h1 := esc88 z (X * wdist w z) (mul_nonneg hX0.le (wdist_nonneg hw0 z)) (hPX z)
      have h2 : 1000 * (X * wdist w z) < 1 := by
        rw [lt_div_iff₀ (by positivity)] at hc; linarith
      exact hz (mem_of_escNorm_lt_one (A := (A : Set G)) hA1' (by linarith))
    have hLip : ∀ g y, |dif g (phi w A hA) y| ≤ 1000 * X * wdist w g := by
      intro g y
      refine (abs_dif_phi_le hA hw0 hwinv hD0 g y).trans ?_
      rw [div_le_iff₀ hD0]
      have h1 : 1 ≤ 1000 * X * wD w A := by
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
          calc 2 * K * (1000 * X * wdist w g) / N = 2 * K * 1000 / N * (X * wdist w g) := by
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
      have hX : 1 / 1000 ≤ 3 * (K * M) + K / ε * (2 / 3) ^ k := by
        have : 0 ≤ K / ε * (2 / 3) ^ k := by positivity
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
  calc escNorm (A : Set G) g ≤ 1000 * (4 * (K * M) * wdist w g) := this
    _ = 1000 * (4 * (K * M)) * wdist w g := by ring

/-- An approximate group has covering parameter at least `1`. -/
lemma one_le_of_isBGTApproxGroup {K : ℝ} {A : Set G} (hA : IsBGTApproxGroup K A) : 1 ≤ K := by
  obtain ⟨-, hA1, -, X, -, -, hXK, hcov⟩ := hA
  have : (1 : G) ∈ (X : Set G) * A := hcov (by simpa using Set.mul_mem_mul hA1 hA1)
  obtain ⟨x, hx, -, -, -⟩ := this
  have : 1 ≤ X.card := Finset.card_pos.2 ⟨x, hx⟩
  exact le_trans (by exact_mod_cast this) hXK

/-- **Theorem 8.1 (ii)** of Breuillard–Green–Tao (product property of the escape norm): if `A` is
a strong `K`-approximate group, then `‖g₁ ⋯ gₙ‖ ≤ 10¹⁰ K⁴ (‖g₁‖ + ⋯ + ‖gₙ‖)` for all
`g₁, …, gₙ` (the paper states this for `gᵢ ∈ A¹⁰` with an unspecified constant `K^{O(1)}`). -/
theorem escNorm_list_prod_le {K : ℝ} {A : Set G} (hA : IsStrongApproxGroup K A) (l : List G) :
    escNorm A l.prod ≤ 10 ^ 10 * K ^ 4 * (l.map (escNorm A)).sum := by
  classical
  have hK1 := one_le_of_isBGTApproxGroup hA.1
  obtain ⟨hApp, S, hSinv, hQN, htrap1, htrap2⟩ := hA
  obtain ⟨A', rfl⟩ := hApp.1.exists_finset_coe
  obtain ⟨-, hA1, hAinv, X, hXinv, hX3, hXK, hcov⟩ := hApp
  have hA1' : (1 : G) ∈ A' := hA1
  have hAinv' : A'⁻¹ = A' := by rw [← coe_inj, coe_inv]; exact hAinv
  have hnn : ∀ y ∈ l.map (escNorm (A' : Set G)), 0 ≤ y := by
    simp only [List.mem_map]; rintro _ ⟨a, -, rfl⟩; exact escNorm_nonneg hA1
  have hsum0 : 0 ≤ (l.map (escNorm (A' : Set G))).sum := List.sum_nonneg hnn
  by_cases hX1 : X.card ≤ 1
  · -- `A` is a genuine subgroup
    have hcov' : A' * A' ⊆ X * A' := by rw [← coe_subset, coe_mul, coe_mul]; exact hcov
    have hcard : #(A' * A') ≤ #A' :=
      (card_le_card hcov').trans (card_mul_le.trans (by nlinarith))
    have heq : A' * A' = A' := (eq_of_subset_of_card_le (subset_mul_left A' hA1') hcard).symm
    have hmul : ∀ a ∈ A', ∀ b ∈ A', a * b ∈ A' := fun a ha b hb => heq ▸ mul_mem_mul ha hb
    by_cases hall : ∀ x ∈ l, x ∈ A'
    · have hprodmem : ∀ l : List G, (∀ x ∈ l, x ∈ A') → l.prod ∈ A' := by
        intro l hl
        induction l with
        | nil => simpa using hA1'
        | cons a l ih =>
          simp only [List.prod_cons]
          exact hmul _ (hl a (by simp)) _ (ih fun x hx => hl x (by simp [hx]))
      have hprod := hprodmem l hall
      have hpow : ∀ i : ℕ, l.prod ^ i ∈ (A' : Set G) := by
        intro i
        induction i with
        | zero => simpa using hA1'
        | succ i ih => rw [pow_succ]; exact hmul _ ih _ hprod
      rw [escNorm_eq_zero_of_forall hA1 hpow]
      positivity
    · push_neg at hall
      obtain ⟨x, hx, hxA⟩ := hall
      have h1 : escNorm (A' : Set G) x = 1 := escNorm_eq_one_of_notMem hA1 hxA
      have h2 : 1 ≤ (l.map (escNorm (A' : Set G))).sum := by
        rw [← h1]
        exact List.single_le_sum hnn _ (List.mem_map_of_mem hx)
      have h3 : (1 : ℝ) ≤ 10 ^ 10 * K ^ 4 := by
        have : 1 ≤ K ^ 4 := one_le_pow₀ hK1
        nlinarith
      calc escNorm (A' : Set G) l.prod ≤ 1 := escNorm_le_one hA1
        _ ≤ 10 ^ 10 * K ^ 4 * 1 := by linarith
        _ ≤ 10 ^ 10 * K ^ 4 * (l.map (escNorm (A' : Set G))).sum := by gcongr
  · -- the main case `K ≥ 2`
    push_neg at hX1
    have hK2 : 2 ≤ K := le_trans (by exact_mod_cast hX1) hXK
    have hAA : (#(A' * A') : ℝ) ≤ K * #A' := by
      have := card_pow_succ_le_of_approx ⟨finite_toSet _, hA1, hAinv, X, hXinv, hX3, hXK, hcov⟩ 1
      rwa [pow_one, one_add_one_eq_two, sq] at this
    set N := ⌊1000 * K ^ 3⌋₊ with hNdef
    set M := ⌈10 ^ 6 * K ^ 3⌉₊ with hMdef
    have hN : 3000 * K ≤ N := by
      have h1 : 1000 * K ^ 3 < N + 1 := Nat.lt_floor_add_one _
      have h2 : 4 * K ≤ K ^ 3 := by
        have : 0 ≤ K * (K ^ 2 - 4) := mul_nonneg (by linarith) (by nlinarith)
        nlinarith
      linarith
    have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by positivity)).ne'
    have hMle : (M : ℝ) ≤ 10 ^ 6 * K ^ 3 + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    have hK0 : (0 : ℝ) < K := by linarith
    set C0 : ℝ := 1000 * (4 * (K * M)) with hC0def
    have hC0nn : 0 ≤ C0 := by positivity
    have hcore : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → escNorm (A' : Set G) l.prod ≤
        C0 * ((l.map (escNorm (A' : Set G))).sum + ε * l.length) := by
      intro ε hε0 hε1
      have h1 := escNorm_le_wdist_core hA1' hAinv' hK2 hAA hSinv hN hM1 hQN htrap1 htrap2
        hε0 hε1 l.prod
      have hw0 : ∀ g, 0 ≤ escNorm (A' : Set G) g + ε := fun g => by
        linarith [escNorm_nonneg (g := g) hA1]
      have h2 := wdist_le_list hw0 l rfl
      have h3 : (l.map (fun g => escNorm (A' : Set G) g + ε)).sum =
          (l.map (escNorm (A' : Set G))).sum + ε * l.length := by
        simp [List.sum_map_add, mul_comm]
      rw [h3] at h2
      exact h1.trans (mul_le_mul_of_nonneg_left h2 hC0nn)
    have hC0 : C0 ≤ 10 ^ 10 * K ^ 4 := by
      have hK4 : K ≤ K ^ 4 := by
        have : 1 ≤ K ^ 3 := one_le_pow₀ hK1
        nlinarith
      rw [hC0def]
      nlinarith
    refine le_trans ?_ (mul_le_mul_of_nonneg_right hC0 hsum0)
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    set ε := min 1 (δ / (C0 * (l.length + 1) + 1)) with hε
    have hε0 : 0 < ε := lt_min one_pos (by positivity)
    have hε1 : ε ≤ 1 := min_le_left _ _
    have hεδ : ε * (C0 * (l.length + 1) + 1) ≤ δ := by
      have := min_le_right 1 (δ / (C0 * (l.length + 1) + 1))
      rw [← hε, le_div_iff₀ (by positivity)] at this
      exact this
    have := hcore ε hε0 hε1
    have hlen : C0 * (ε * l.length) ≤ δ := by
      have : C0 * (ε * l.length) ≤ ε * (C0 * (l.length + 1) + 1) := by
        nlinarith [hε0.le, hC0nn]
      linarith
    nlinarith

/-! ### The commutator estimate -/

section Commutator

variable [DecidableEq G] {A : Finset G} (hA : A.Nonempty) {w : G → ℝ} (hw0 : ∀ g, 0 ≤ w g)
  (hD : 0 < wD w A)
include hw0 hD

/-- The auxiliary function `Φ = |A|⁻¹ φ * φ` used for the commutator estimate. -/
noncomputable def bigPhi (A : Finset G) (hA : A.Nonempty) (w : G → ℝ) : G → ℝ :=
  fun x => (1 / #A) * conv (phi w A hA) (phi w A hA) x

lemma one_le_bigPhi (hAinv : A⁻¹ = A) (hA1 : (1 : G) ∈ A) : 1 ≤ bigPhi A hA w 1 := by
  have hA' : (0 : ℝ) < #A := by exact_mod_cast hA.card_pos
  simp only [bigPhi]
  rw [conv_phi_eq_sum hA hw0 hD]
  have h1 : ∑ y ∈ A, phi w A hA y * phi w A hA (y⁻¹ * 1) = #A := by
    rw [← nsmul_one, ← sum_const]
    refine sum_congr rfl fun y hy => ?_
    have hy' : y⁻¹ ∈ A := by rw [← hAinv]; exact inv_mem_inv hy
    rw [phi_eq_one hA hw0 hy, mul_one, phi_eq_one hA hw0 hy', mul_one]
  have h2 : ∑ y ∈ A, phi w A hA y * phi w A hA (y⁻¹ * 1) ≤
      ∑ y ∈ A * A, phi w A hA y * phi w A hA (y⁻¹ * 1) :=
    sum_le_sum_of_subset_of_nonneg (subset_mul_left A hA1)
      (fun y _ _ => mul_nonneg (phi_nonneg hA _) (phi_nonneg hA _))
  rw [h1] at h2
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hA', one_mul]
  exact h2

lemma bigPhi_pos_mem {x : G} (hx : 0 < bigPhi A hA w x) : x ∈ (A : Set G) ^ 4 := by
  simp only [bigPhi] at hx
  rw [conv_phi_eq_sum hA hw0 hD] at hx
  have hsum : 0 < ∑ y ∈ A * A, phi w A hA y * phi w A hA (y⁻¹ * x) := by
    by_contra hc
    push_neg at hc
    have : (1 / (#A : ℝ)) * ∑ y ∈ A * A, phi w A hA y * phi w A hA (y⁻¹ * x) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hc
    linarith
  obtain ⟨y, hy, hpos⟩ := exists_lt_of_sum_lt (f := fun _ => (0 : ℝ)) (by simpa using hsum)
  have hphi : phi w A hA (y⁻¹ * x) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hpos; exact lt_irrefl _ hpos
  have h1 := phi_mem hA hw0 hD hphi
  have hy' : y ∈ (A : Set G) * A := by rw [← coe_mul]; exact hy
  have h1' : y⁻¹ * x ∈ (A : Set G) * A := by rw [← coe_mul]; exact h1
  have : y * (y⁻¹ * x) ∈ ((A : Set G) * A) * ((A : Set G) * A) := Set.mul_mem_mul hy' h1'
  rw [mul_inv_cancel_left] at this
  have e : ((A : Set G) * A) * ((A : Set G) * A) = (A : Set G) ^ 4 := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rwa [e] at this

/-- The second-derivative bound for `Φ`: `|∂_h ∂_g Φ| ≤ 2K · sup|∂_g φ| · sup_{y ∈ A¹²} |∂_{h^y} φ|`. -/
lemma abs_dif_dif_bigPhi_le {K : ℝ} (hA1 : (1 : G) ∈ A) (hAA : (#(A * A) : ℝ) ≤ K * #A)
    {g h : G} (hg : g ∈ (A : Set G) ^ 10) {L L' : ℝ} (hL : ∀ y, |dif g (phi w A hA) y| ≤ L)
    (hL' : ∀ y ∈ (A : Set G) ^ 12, ∀ z, |dif (y⁻¹ * h * y) (phi w A hA) z| ≤ L') (x : G) :
    |dif h (dif g (bigPhi A hA w)) x| ≤ 2 * K * L * L' := by
  have hA' : (0 : ℝ) < #A := by exact_mod_cast hA.card_pos
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL 1)
  have hfin := finite_support_phi hA hw0 hD
  have hfun : dif g (bigPhi A hA w) =
      fun x => (1 / #A) * conv (dif g (phi w A hA)) (phi w A hA) x := by
    funext x
    have := dif_conv_left hfin (phi w A hA) g x
    simp only [dif, bigPhi] at this ⊢
    rw [← mul_sub, this]
  have hfin' := support_dif_finite hfin g
  have hdd : dif h (dif g (bigPhi A hA w)) x = (1 / #A) *
      ∑ᶠ y, dif g (phi w A hA) y * dif (y⁻¹ * h * y) (phi w A hA) (y⁻¹ * x) := by
    rw [hfun, ← dif_conv_right hfin']
    simp only [dif]
    ring
  rw [hdd, abs_mul, abs_of_pos (by positivity)]
  set U := (A * A) ∪ (A * A).image (fun z => g * z) with hU
  have hsuppF : ∀ y, dif g (phi w A hA) y ≠ 0 → y ∈ U := by
    intro y hy
    rw [hU, mem_union, mem_image]
    by_cases h0 : phi w A hA y = 0
    · right
      have : phi w A hA (g⁻¹ * y) ≠ 0 := by
        intro h1; apply hy; simp [dif, h0, h1]
      exact ⟨g⁻¹ * y, phi_mem hA hw0 hD this, by group⟩
    · left; exact phi_mem hA hw0 hD h0
  have hA1' : (1 : G) ∈ (A : Set G) := hA1
  have hU12 : ∀ y ∈ U, y ∈ (A : Set G) ^ 12 := by
    intro y hy
    rw [hU, mem_union, mem_image] at hy
    rcases hy with hy | ⟨z, hz, rfl⟩
    · have : y ∈ (A : Set G) ^ 2 := by rw [sq, ← coe_mul]; exact hy
      exact Set.pow_subset_pow_right hA1' (by norm_num) this
    · have : g * z ∈ (A : Set G) ^ 10 * (A : Set G) ^ 2 :=
        Set.mul_mem_mul hg (by rw [sq, ← coe_mul]; exact hz)
      rwa [← pow_add] at this
  have hsupp : support (fun y => dif g (phi w A hA) y *
      dif (y⁻¹ * h * y) (phi w A hA) (y⁻¹ * x)) ⊆ U :=
    fun y hy => hsuppF y (left_ne_zero_of_mul hy)
  have hbound := abs_finsum_le U hsupp (B := L * L') (fun y hy => by
    rw [abs_mul]
    exact mul_le_mul (hL y) (hL' y (hU12 y hy) _) (abs_nonneg _) hL0)
  have hUc : (#U : ℝ) ≤ 2 * K * #A := by
    have h1 : #U ≤ #(A * A) + #(A * A) :=
      (card_union_le _ _).trans (Nat.add_le_add_left card_image_le _)
    have h2 : (#U : ℝ) ≤ #(A * A) + #(A * A) := by exact_mod_cast h1
    linarith
  have hLL : 0 ≤ L * L' :=
    mul_nonneg hL0 ((abs_nonneg _).trans (hL' 1 (Set.one_mem_pow hA1') 1))
  calc 1 / (#A : ℝ) * |∑ᶠ y, dif g (phi w A hA) y *
        dif (y⁻¹ * h * y) (phi w A hA) (y⁻¹ * x)|
      ≤ 1 / #A * (#U * (L * L')) := by gcongr
    _ ≤ 1 / #A * ((2 * K * #A) * (L * L')) := by gcongr
    _ = 2 * K * L * L' := by field_simp

end Commutator

/-- **Theorem 8.1 (iii)** of Breuillard–Green–Tao (commutator property of the escape norm): if `A`
is a strong `K`-approximate group and `g, h ∈ A¹⁰`, then
`‖[g, h]‖ ≤ 10²⁷ K⁹ ‖g‖ ‖h‖`, where `[g, h] = g⁻¹ h⁻¹ g h` (the paper states `K^{O(1)}`). -/
theorem escNorm_commutator_le {K : ℝ} {A : Set G} (hA : IsStrongApproxGroup K A) {g h : G}
    (hg : g ∈ A ^ 10) (hh : h ∈ A ^ 10) :
    escNorm A (g⁻¹ * h⁻¹ * g * h) ≤ 10 ^ 27 * K ^ 9 * escNorm A g * escNorm A h := by
  classical
  have hK1 := one_le_of_isBGTApproxGroup hA.1
  have hprod := escNorm_list_prod_le hA
  have hconj := fun {x y : G} (hy : y ∈ A ^ 49) => escNorm_conj_le (g := x) hA hy
  obtain ⟨hApp, S, hSinv, hQN, htrap1, htrap2⟩ := hA
  obtain ⟨A', rfl⟩ := hApp.1.exists_finset_coe
  have hAA : (#(A' * A') : ℝ) ≤ K * #A' := by
    have := card_pow_succ_le_of_approx hApp 1
    rwa [pow_one, one_add_one_eq_two, sq] at this
  obtain ⟨-, hA1, hAinv, -⟩ := hApp
  have hA1' : (1 : G) ∈ A' := hA1
  have hAinv' : A'⁻¹ = A' := by rw [← coe_inj, coe_inv]; exact hAinv
  have hAne : A'.Nonempty := ⟨1, hA1'⟩
  set C : ℝ := 10 ^ 10 * K ^ 4 with hC
  have hC1 : 1 ≤ C := by
    have : 1 ≤ K ^ 4 := one_le_pow₀ hK1
    rw [hC]; nlinarith
  have hC0 : 0 < C := by linarith
  set w : G → ℝ := escNorm (A' : Set G) with hw
  have hw0 : ∀ u, 0 ≤ w u := fun u => escNorm_nonneg hA1
  have hwinv : ∀ u, w u⁻¹ = w u := fun u => escNorm_inv hAinv
  -- lower bounds on the word metric and on `D`
  have hdlow : ∀ z, w z / C ≤ wdist w z := fun z => le_wdist fun l hl => by
    rw [div_le_iff₀ hC0, mul_comm]
    have := hprod l
    rw [hl] at this
    exact this
  have hD : 1 / C ≤ wD w A' := le_wD (by rw [div_le_one hC0]; exact hC1) fun z hz => by
    have := hdlow z
    rwa [show w z = 1 from escNorm_eq_one_of_notMem hA1 hz] at this
  have hD0 : 0 < wD w A' := lt_of_lt_of_le (by positivity) hD
  have hLip : ∀ u y, |dif u (phi w A' hAne) y| ≤ C * w u := by
    intro u y
    refine (abs_dif_phi_le hAne hw0 hwinv hD0 u y).trans ?_
    rw [div_le_iff₀ hD0]
    have h1 : 1 ≤ C * wD w A' := by rw [div_le_iff₀ hC0] at hD; linarith
    have h2 := wdist_le hw0 u
    have h3 := wdist_nonneg hw0 u
    nlinarith [hw0 u]
  have hconjL : ∀ v : G, ∀ y ∈ (A' : Set G) ^ 12, ∀ z,
      |dif (y⁻¹ * v * y) (phi w A' hAne) z| ≤ C * (1000 * w v) := by
    intro v y hy z
    refine (hLip _ z).trans ?_
    gcongr
    exact hconj (Set.pow_subset_pow_right hA1 (by norm_num) hy)
  set Φ := bigPhi A' hAne w with hΦ
  have hdd1 : ∀ x, |dif h (dif g Φ) x| ≤ 2 * K * (C * w g) * (C * (1000 * w h)) :=
    fun x => abs_dif_dif_bigPhi_le hAne hw0 hD0 hA1' hAA hg (hLip g) (hconjL h) x
  have hdd2 : ∀ x, |dif g (dif h Φ) x| ≤ 2 * K * (C * w h) * (C * (1000 * w g)) :=
    fun x => abs_dif_dif_bigPhi_le hAne hw0 hD0 hA1' hAA hh (hLip h) (hconjL g) x
  have hc : ∀ z, |dif (g⁻¹ * h⁻¹ * g * h) Φ z| ≤ 4000 * K * C ^ 2 * (w g * w h) := by
    intro z
    have e := dif_comm g h Φ (h * g * z)
    rw [show g⁻¹ * h⁻¹ * (h * g * z) = z by group] at e
    rw [← e]
    calc |dif g (dif h Φ) (h * g * z) - dif h (dif g Φ) (h * g * z)|
        ≤ |dif g (dif h Φ) (h * g * z)| + |dif h (dif g Φ) (h * g * z)| := abs_sub _ _
      _ ≤ 2 * K * (C * w h) * (C * (1000 * w g)) + 2 * K * (C * w g) * (C * (1000 * w h)) :=
          add_le_add (hdd2 _) (hdd1 _)
      _ = 4000 * K * C ^ 2 * (w g * w h) := by ring
  have hΦ1 : 1 ≤ Φ 1 := one_le_bigPhi hAne hw0 hD0 hAinv' hA1'
  have hΦpos : ∀ x, 0 < Φ x → x ∈ (A' : Set G) ^ 100 := fun x hx =>
    Set.pow_subset_pow_right hA1 (by norm_num) (bigPhi_pos_mem hAne hw0 hD0 hx)
  have hnn : 0 ≤ 4000 * K * C ^ 2 * (w g * w h) := by
    have := hw0 g; have := hw0 h; positivity
  have h1 := escNorm_le_of_abs_dif_le hAinv htrap1 hΦ1 hΦpos hnn hc
  calc escNorm (A' : Set G) (g⁻¹ * h⁻¹ * g * h) ≤ 1000 * (4000 * K * C ^ 2 * (w g * w h)) := h1
    _ = 4 * 10 ^ 26 * K ^ 9 * w g * w h := by rw [hC]; ring
    _ ≤ 10 ^ 27 * K ^ 9 * w g * w h := by
        have := hw0 g; have := hw0 h
        have : 0 ≤ K ^ 9 * w g * w h := by positivity
        nlinarith

/-- Consequence of Theorem 8.1 (i) and (ii) noted in the paper: for a strong approximate group
`A`, the elements of escape norm zero form a (genuine) subgroup `H ⊆ A`, normalised by `A¹⁰`. -/
theorem exists_subgroup_escNorm_eq_zero {K : ℝ} {A : Set G} (hA : IsStrongApproxGroup K A) :
    ∃ H : Subgroup G, (H : Set G) = {g | escNorm A g = 0} ∧ (H : Set G) ⊆ A ∧
      ∀ a ∈ A ^ 10, ∀ g ∈ H, a⁻¹ * g * a ∈ H := by
  have hA1 : (1 : G) ∈ A := hA.1.2.1
  have hAinv : A⁻¹ = A := hA.1.2.2.1
  let H : Subgroup G :=
    { carrier := {g | escNorm A g = 0}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        have := escNorm_list_prod_le hA [a, b]
        simp only [List.prod_cons, List.prod_nil, mul_one, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, ha, hb, add_zero, mul_zero] at this
        exact le_antisymm this (escNorm_nonneg hA1)
      one_mem' := escNorm_one hA1
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [escNorm_inv hAinv, ha] }
  refine ⟨H, rfl, fun g hg => mem_of_escNorm_lt_one hA1 (by
    change escNorm A g = 0 at hg; rw [hg]; norm_num), fun a ha g hg => ?_⟩
  change escNorm A g = 0 at hg
  change escNorm A (a⁻¹ * g * a) = 0
  have := escNorm_conj_le (g := g) hA (Set.pow_subset_pow_right hA1 (by norm_num) ha)
  rw [hg, mul_zero] at this
  exact le_antisymm this (escNorm_nonneg hA1)

end Lovasz.BGT
