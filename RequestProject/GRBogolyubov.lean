module
public import Mathlib
public import RequestProject.GRFourier

/-!
# Green–Ruzsa, pointwise phase control and a weak Bogolyubov lemma
-/

@[expose] public section

open Finset ComplexConjugate

namespace GreenRuzsa

variable {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]

lemma norm_sub_sq_le_two (u v z : ℂ) : ‖u - v‖ ^ 2 ≤ 2 * ‖u - z‖ ^ 2 + 2 * ‖v - z‖ ^ 2 := by
  have h : ‖u - v‖ ≤ ‖u - z‖ + ‖v - z‖ := by
    calc ‖u - v‖ = ‖(u - z) - (v - z)‖ := by ring_nf
      _ ≤ ‖u - z‖ + ‖v - z‖ := norm_sub_le _ _
  have h0 : 0 ≤ ‖u - v‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖u - z‖ - ‖v - z‖)]

/-- **Average concentration on `A + A` gives pointwise control on `A`.** -/
theorem norm_sub_one_sq_le (A : Finset G) (h0 : (0 : G) ∈ A) (hneg : ∀ a ∈ A, -a ∈ A)
    (κ : ℝ) (hD : ((ksum 2 A).card : ℝ) ≤ κ * A.card) (ε : ℝ) (χ : AddChar G ℂ)
    (hχ : (1 - ε) * (ksum 2 A).card < ‖csum (ksum 2 A) χ‖) :
    ∀ a ∈ A, ‖χ a - 1‖ ^ 2 ≤ 8 * κ * ε := by
  intro a ha
  set D := ksum 2 A with hDdef
  set S := csum D χ with hSdef
  have hAD : A ⊆ D := subset_ksum_two h0
  have hApos : (0 : ℝ) < A.card := by exact_mod_cast card_pos.2 ⟨0, h0⟩
  have hDpos : (0 : ℝ) < D.card := by exact_mod_cast card_pos.2 ⟨0, hAD h0⟩
  -- a unit complex number with the phase of `S`
  set z : ℂ := if S = 0 then 1 else S / (‖S‖ : ℂ) with hz
  have hz1 : ‖z‖ = 1 := by
    rw [hz]
    split_ifs with h
    · simp
    · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self (norm_ne_zero_iff.2 h)]
  have hSz : (S * conj z).re = ‖S‖ := by
    rw [hz]
    split_ifs with h
    · simp [h]
    · have hn : (‖S‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 h
      rw [map_div₀, Complex.conj_ofReal, ← mul_div_assoc, Complex.mul_conj,
        Complex.normSq_eq_norm_sq]
      rw [show ((‖S‖ ^ 2 : ℝ) : ℂ) / (‖S‖ : ℂ) = ((‖S‖ : ℝ) : ℂ) by
        field_simp; push_cast; ring]
      simp
  -- the phase energy
  set E := ∑ d ∈ D, ‖χ d - z‖ ^ 2 with hE
  have hEeq : E = 2 * D.card - 2 * ‖S‖ := by
    have : ∀ d, ‖χ d - z‖ ^ 2 = 2 - 2 * (χ d * conj z).re := by
      intro d
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.normSq_eq_norm_sq,
        Complex.normSq_eq_norm_sq, AddChar.norm_apply, hz1]
      ring
    rw [hE, sum_congr rfl fun d _ => this d, sum_sub_distrib, sum_const, nsmul_eq_mul,
      ← mul_sum, ← Complex.re_sum, ← sum_mul]
    rw [hSdef, csum] at hSz
    rw [hSz]
    simp only [hSdef, csum]
    ring
  have hEle : E ≤ 2 * ε * D.card := by
    rw [hEeq]
    nlinarith
  have hE0 : 0 ≤ E := sum_nonneg fun _ _ => sq_nonneg _
  have hε : 0 ≤ ε := by
    by_contra h
    push_neg at h
    nlinarith
  -- translate by `a`
  have hshift : ∀ c, ‖χ c - χ (c - a)‖ = ‖χ a - 1‖ := by
    intro c
    have : χ c = χ (c - a) * χ a := by rw [← AddChar.map_add_eq_mul, sub_add_cancel]
    rw [this, show χ (c - a) * χ a - χ (c - a) = χ (c - a) * (χ a - 1) by ring, norm_mul,
      AddChar.norm_apply, one_mul]
  have h1 : ∑ c ∈ A, ‖χ c - z‖ ^ 2 ≤ E :=
    sum_le_sum_of_subset_of_nonneg hAD fun _ _ _ => sq_nonneg _
  have h2 : ∑ c ∈ A, ‖χ (c - a) - z‖ ^ 2 ≤ E := by
    have hinj : Set.InjOn (fun c => c - a) (A : Set G) := fun x _ y _ h => by
      simpa using h
    rw [← sum_image (f := fun d => ‖χ d - z‖ ^ 2) hinj]
    refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => sq_nonneg _
    intro d hd
    obtain ⟨c, hc, rfl⟩ := mem_image.1 hd
    exact mem_ksum_two.2 ⟨c, hc, -a, hneg a ha, by abel⟩
  have hmain : (A.card : ℝ) * ‖χ a - 1‖ ^ 2 ≤ 4 * E := by
    calc (A.card : ℝ) * ‖χ a - 1‖ ^ 2 = ∑ c ∈ A, ‖χ c - χ (c - a)‖ ^ 2 := by
          simp [hshift]
      _ ≤ ∑ c ∈ A, (2 * ‖χ c - z‖ ^ 2 + 2 * ‖χ (c - a) - z‖ ^ 2) :=
          sum_le_sum fun c _ => norm_sub_sq_le_two _ _ _
      _ = 2 * ∑ c ∈ A, ‖χ c - z‖ ^ 2 + 2 * ∑ c ∈ A, ‖χ (c - a) - z‖ ^ 2 := by
          rw [sum_add_distrib, mul_sum, mul_sum]
      _ ≤ 4 * E := by linarith
  have : (A.card : ℝ) * ‖χ a - 1‖ ^ 2 ≤ (A.card : ℝ) * (8 * κ * ε) := by
    calc (A.card : ℝ) * ‖χ a - 1‖ ^ 2 ≤ 4 * E := hmain
      _ ≤ 8 * ε * D.card := by linarith
      _ ≤ 8 * ε * (κ * A.card) := by gcongr
      _ = (A.card : ℝ) * (8 * κ * ε) := by ring
  exact le_of_mul_le_mul_left this hApos

/-! ### The weak Bogolyubov lemma -/

/-- The large spectrum `{χ : |∑_A χ|² ≥ |A|³ / (4|G|)}`. -/
noncomputable def largeSpec (A : Finset G) : Finset (AddChar G ℂ) :=
  univ.filter fun χ => (A.card : ℝ) ^ 3 / (4 * Fintype.card G) ≤ ‖csum A χ‖ ^ 2

lemma card_largeSpec_mul_le (A : Finset G) (hA : A.Nonempty) :
    ((largeSpec A).card : ℝ) * (A.card : ℝ) ^ 2 ≤ 4 * (Fintype.card G : ℝ) ^ 2 := by
  have hApos : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hGpos : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have h1 : ((largeSpec A).card : ℝ) * ((A.card : ℝ) ^ 3 / (4 * Fintype.card G)) ≤
      ∑ χ ∈ largeSpec A, ‖csum A χ‖ ^ 2 := by
    rw [← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum fun χ hχ => (mem_filter.1 hχ).2
  have h2 : ∑ χ ∈ largeSpec A, ‖csum A χ‖ ^ 2 ≤ Fintype.card G * A.card := by
    rw [← sum_norm_sq_csum]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => sq_nonneg _
  have h3 := h1.trans h2
  rw [mul_div_assoc', div_le_iff₀ (by positivity)] at h3
  nlinarith

omit [DecidableEq G] in
lemma zero_mem_largeSpec (A : Finset G) : (0 : AddChar G ℂ) ∈ largeSpec A := by
  rw [largeSpec, mem_filter, csum_zero, Complex.norm_natCast]
  refine ⟨mem_univ _, ?_⟩
  have hle : (A.card : ℝ) ≤ Fintype.card G := by exact_mod_cast card_le_univ A
  rcases Nat.eq_zero_or_pos A.card with h | h
  · simp [h]
  · have hApos : (0 : ℝ) < A.card := by exact_mod_cast h
    rw [div_le_iff₀ (by positivity)]
    nlinarith

/-- **Weak Bogolyubov lemma.** The Bohr set of the large spectrum lies in `4A`. -/
theorem mem_ksum_four_of_bohr (A : Finset G) (hA : A.Nonempty) (hneg : ∀ a ∈ A, -a ∈ A)
    (x : G) (hx : ∀ χ ∈ largeSpec A, 1 / 2 ≤ (χ x).re) : x ∈ ksum 4 A := by
  by_contra hx4
  set r : G → ℕ := fun y => ((A ×ˢ A).filter fun p => p.1 + p.2 = y).card with hr
  have hS2 : ∀ χ : AddChar G ℂ, csum A χ ^ 2 = ∑ y, (r y : ℂ) * χ y := by
    intro χ
    rw [← sum_family_eq, sq, csum, sum_mul_sum, sum_product]
    simp [AddChar.map_add_eq_mul]
  have hshift : ∀ χ : AddChar G ℂ, ∑ y, (r (y - x) : ℂ) * χ y = χ x * csum A χ ^ 2 := by
    intro χ
    rw [hS2, mul_sum]
    refine Fintype.sum_equiv (Equiv.subRight x) _ _ fun y => ?_
    simp only [Equiv.subRight_apply]
    rw [show χ y = χ (y - x) * χ x by rw [← AddChar.map_add_eq_mul, sub_add_cancel]]
    ring
  have horth := sum_char_mul_conj (fun y => (r y : ℂ)) (fun y => (r (y - x) : ℂ))
  have hzero : ∀ y, (r y : ℂ) * conj (r (y - x) : ℂ) = 0 := by
    intro y
    by_contra hne
    rcases mul_ne_zero_iff.1 hne with ⟨h1, h2⟩
    have h1' : r y ≠ 0 := by exact_mod_cast h1
    have h2' : r (y - x) ≠ 0 := by
      intro h
      apply h2
      simp [h]
    obtain ⟨⟨a, b⟩, hab⟩ := card_ne_zero.1 h1'
    obtain ⟨⟨c, e⟩, hce⟩ := card_ne_zero.1 h2'
    simp only [mem_filter, mem_product] at hab hce
    apply hx4
    rw [mem_ksum]
    refine ⟨![a, b, -c, -e], ?_, ?_⟩
    · intro i
      fin_cases i
      · exact hab.1.1
      · exact hab.1.2
      · exact hneg c hce.1.1
      · exact hneg e hce.1.2
    · simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      have : x = (a + b) - (c + e) := by rw [hab.2, hce.2]; abel
      rw [this]
      abel
  simp_rw [hzero, sum_const_zero, mul_zero] at horth
  simp_rw [← hS2, hshift] at horth
  -- take real parts
  have hre : ∑ χ : AddChar G ℂ, ‖csum A χ‖ ^ 4 * (χ x).re = 0 := by
    have : ∀ χ : AddChar G ℂ, csum A χ ^ 2 * conj (χ x * csum A χ ^ 2) =
        ((‖csum A χ‖ ^ 4 : ℝ) : ℂ) * conj (χ x) := by
      intro χ
      rw [map_mul, map_pow, show csum A χ ^ 2 * (conj (χ x) * conj (csum A χ) ^ 2) =
        (csum A χ * conj (csum A χ)) ^ 2 * conj (χ x) by ring, Complex.mul_conj,
        Complex.normSq_eq_norm_sq]
      push_cast
      ring
    simp_rw [this] at horth
    have := congrArg Complex.re horth
    rw [Complex.re_sum] at this
    simp only [Complex.re_ofReal_mul, Complex.conj_re, Complex.zero_re] at this
    exact this
  -- lower bound
  have hApos : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hGpos : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  set τ : ℝ := (A.card : ℝ) ^ 3 / (4 * Fintype.card G) with hτ
  rw [← sum_filter_add_sum_filter_not univ
    (fun χ : AddChar G ℂ => τ ≤ ‖csum A χ‖ ^ 2)] at hre
  have hin : (A.card : ℝ) ^ 4 / 2 ≤
      ∑ χ ∈ univ.filter (fun χ : AddChar G ℂ => τ ≤ ‖csum A χ‖ ^ 2),
        ‖csum A χ‖ ^ 4 * (χ x).re := by
    calc (A.card : ℝ) ^ 4 / 2 = ‖csum A 0‖ ^ 4 * (1 / 2) := by
          rw [csum_zero, Complex.norm_natCast]; ring
      _ ≤ ∑ χ ∈ largeSpec A, ‖csum A χ‖ ^ 4 * (1 / 2) :=
          single_le_sum (f := fun χ => ‖csum A χ‖ ^ 4 * (1 / 2))
            (fun _ _ => by positivity) (zero_mem_largeSpec A)
      _ ≤ _ := sum_le_sum fun χ hχ =>
          mul_le_mul_of_nonneg_left (hx χ hχ) (by positivity)
  have hout : -((A.card : ℝ) ^ 4 / 4) ≤
      ∑ χ ∈ univ.filter (fun χ : AddChar G ℂ => ¬ τ ≤ ‖csum A χ‖ ^ 2),
        ‖csum A χ‖ ^ 4 * (χ x).re := by
    have hb : ∀ χ ∈ univ.filter (fun χ : AddChar G ℂ => ¬ τ ≤ ‖csum A χ‖ ^ 2),
        -(τ * ‖csum A χ‖ ^ 2) ≤ ‖csum A χ‖ ^ 4 * (χ x).re := by
      intro χ hχ
      have hlt : ‖csum A χ‖ ^ 2 < τ := lt_of_not_ge (mem_filter.1 hχ).2
      have hre1 : -1 ≤ (χ x).re := by
        have := Complex.abs_re_le_norm (χ x)
        rw [AddChar.norm_apply] at this
        linarith [neg_abs_le (χ x).re]
      have h4 : ‖csum A χ‖ ^ 4 ≤ τ * ‖csum A χ‖ ^ 2 := by
        rw [show ‖csum A χ‖ ^ 4 = ‖csum A χ‖ ^ 2 * ‖csum A χ‖ ^ 2 by ring]
        exact mul_le_mul_of_nonneg_right hlt.le (sq_nonneg _)
      nlinarith [pow_nonneg (norm_nonneg (csum A χ)) 4]
    calc -((A.card : ℝ) ^ 4 / 4) = -(τ * (Fintype.card G * A.card)) := by
          rw [hτ]; field_simp
      _ ≤ -(τ * ∑ χ ∈ univ.filter (fun χ : AddChar G ℂ => ¬ τ ≤ ‖csum A χ‖ ^ 2),
            ‖csum A χ‖ ^ 2) := by
          rw [neg_le_neg_iff]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [← sum_norm_sq_csum]
          exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => sq_nonneg _
      _ = ∑ χ ∈ univ.filter (fun χ : AddChar G ℂ => ¬ τ ≤ ‖csum A χ‖ ^ 2),
            -(τ * ‖csum A χ‖ ^ 2) := by rw [mul_sum, ← sum_neg_distrib]
      _ ≤ _ := sum_le_sum hb
  have : (0 : ℝ) < (A.card : ℝ) ^ 4 / 4 := by positivity
  linarith

end GreenRuzsa
