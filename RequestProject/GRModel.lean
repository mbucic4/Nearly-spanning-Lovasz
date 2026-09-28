module
public import Mathlib
public import RequestProject.GRBogolyubov
public import RequestProject.GRRoots
public import RequestProject.GRCompress

/-!
# Green–Ruzsa, a dense finite Freiman model

Every `κ`-approximate group `A` in a finite abelian group has a normalized Freiman
`8`-isomorphic copy in a finite abelian group `G'` with `|G'| ≤ modelBound κ · |A|`.
Among all such models we take one of minimal ambient cardinality; if it were too sparse,
polynomial growth and a Fourier moment estimate would produce a character that is uniformly
close to `1` on the model set, and compressing the corresponding cyclic coordinate would give a
strictly smaller model.
-/

@[expose] public section

open Finset Filter

namespace GreenRuzsa

/-- Exponential decay beats polynomial growth. -/
lemma exists_decay (κ : ℕ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ k : ℕ, 8 * (2 * ((k : ℝ) + 1)) ^ κ * (1 - ε) ^ (2 * k) ≤ 1 := by
  set r : ℝ := (1 - ε) ^ 2 with hr
  have hr0 : 0 ≤ r := sq_nonneg _
  have hr1 : r < 1 := by rw [hr]; nlinarith
  have ht := tendsto_pow_const_mul_const_pow_of_abs_lt_one κ (r := r)
    (by rw [abs_of_nonneg hr0]; exact hr1)
  have hc : (0 : ℝ) < 1 / (8 * 4 ^ κ) := by positivity
  obtain ⟨k, hk, hk1⟩ := (((tendsto_order.1 ht).2 _ hc).and (eventually_ge_atTop 1)).exists
  refine ⟨k, ?_⟩
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have h1 : (2 * ((k : ℝ) + 1)) ^ κ ≤ 4 ^ κ * (k : ℝ) ^ κ := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have h2 : (1 - ε) ^ (2 * k) = r ^ k := by rw [hr, pow_mul]
  rw [h2]
  have hrk : 0 ≤ r ^ k := pow_nonneg hr0 _
  calc 8 * (2 * ((k : ℝ) + 1)) ^ κ * r ^ k ≤ 8 * (4 ^ κ * (k : ℝ) ^ κ) * r ^ k := by gcongr
    _ = 8 * 4 ^ κ * ((k : ℝ) ^ κ * r ^ k) := by ring
    _ ≤ 8 * 4 ^ κ * (1 / (8 * 4 ^ κ)) := by gcongr
    _ = 1 := by field_simp

/-- The Fourier threshold `ε = 1 / (8192 · 8² · (κ + 1))`. -/
noncomputable def grEps (κ : ℕ) : ℝ := 1 / (524288 * ((κ : ℝ) + 1))

lemma grEps_pos (κ : ℕ) : 0 < grEps κ := by unfold grEps; positivity

lemma grEps_lt_one (κ : ℕ) : grEps κ < 1 := by
  unfold grEps
  rw [div_lt_one (by positivity)]
  have : (0 : ℝ) ≤ κ := Nat.cast_nonneg _
  nlinarith

/-- The moment parameter (the iterated sumset has `grK κ + 1` summands). -/
noncomputable def grK (κ : ℕ) : ℕ :=
  Classical.choose (exists_decay κ (grEps κ) (grEps_pos κ) (grEps_lt_one κ))

lemma grK_spec (κ : ℕ) :
    8 * (2 * ((grK κ : ℝ) + 1)) ^ κ * (1 - grEps κ) ^ (2 * grK κ) ≤ 1 :=
  Classical.choose_spec (exists_decay κ (grEps κ) (grEps_pos κ) (grEps_lt_one κ))

/-- The uniform model bound. -/
noncomputable def modelBound (κ : ℕ) : ℕ := 8 * κ * (2 * (grK κ + 1)) ^ κ

variable {G' : Type} [AddCommGroup G'] [Fintype G'] [DecidableEq G']

/-- **Reduction step.** A sparse approximate group admits a Freiman `8`-model in a strictly
smaller group. -/
theorem exists_smaller_model (κ : ℕ) (hκ : 1 ≤ κ) (A : Finset G') (hA : AddApprox κ A)
    (hbig : modelBound κ * A.card < Fintype.card G') :
    ∃ (G'' : Type) (_ : AddCommGroup G'') (_ : Fintype G''),
      Fintype.card G'' < Fintype.card G' ∧ ∃ c : G' → G'', IsFIso 8 A c ∧ c 0 = 0 := by
  set k := grK κ with hk
  set ε := grEps κ with hε
  set D := ksum 2 A with hDdef
  have h0 := hA.zero_mem
  have hAD : A ⊆ D := subset_ksum_two h0
  have hDne : D.Nonempty := ⟨0, hAD h0⟩
  have hApos : (0 : ℝ) < A.card := by exact_mod_cast card_pos.2 ⟨0, h0⟩
  have hDcard : (D.card : ℝ) ≤ κ * A.card := by exact_mod_cast hA.card_ksum_two_le
  have hADc : (A.card : ℝ) ≤ D.card := by exact_mod_cast card_le_card hAD
  set R : ℝ := (2 * ((k : ℝ) + 1)) ^ κ with hR
  have hRpos : 0 < R := by positivity
  have hgrowth : ((ksum (k + 1) D).card : ℝ) ≤ R * D.card := by
    have h1 : ksum (k + 1) D ⊆ ksum ((k + 1) * 2) A := ksum_ksum_subset A (k + 1) 2
    have h2 := hA.card_ksum_le ((k + 1) * 2) (by omega)
    have h3 : ((ksum (k + 1) D).card : ℝ) ≤ (((k + 1) * 2 : ℕ) : ℝ) ^ κ * A.card := by
      exact_mod_cast (card_le_card h1).trans h2
    calc ((ksum (k + 1) D).card : ℝ) ≤ (((k + 1) * 2 : ℕ) : ℝ) ^ κ * A.card := h3
      _ = R * A.card := by rw [hR]; push_cast; ring
      _ ≤ R * D.card := by gcongr
  have hGpos : (0 : ℝ) < Fintype.card G' := by exact_mod_cast Fintype.card_pos
  have hbig' : 8 * κ * R * A.card < Fintype.card G' := by
    have : ((modelBound κ * A.card : ℕ) : ℝ) < Fintype.card G' := by exact_mod_cast hbig
    rw [modelBound] at this
    push_cast at this
    rw [hR, hk]
    linarith
  have hκ' : (1 : ℝ) ≤ κ := by exact_mod_cast hκ
  have hnum : R * (D.card / Fintype.card G' + (1 - ε) ^ (2 * k)) < 1 := by
    have hdec := grK_spec κ
    rw [← hk, ← hε, ← hR] at hdec
    have h1 : R * (D.card / Fintype.card G') < 1 / 8 := by
      rw [mul_div_assoc', div_lt_iff₀ hGpos]
      nlinarith
    nlinarith
  obtain ⟨χ, hχ0, hχ⟩ := exists_char_large D hDne k R ε hgrowth (grEps_lt_one κ).le hnum
  -- pointwise control
  have hpt := norm_sub_one_sq_le A h0 hA.neg_mem κ hDcard ε χ hχ
  have h8 : 8 * (κ : ℝ) * ε ≤ 1 / 65536 := by
    rw [hε, grEps]
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hpt' : ∀ a ∈ A, ‖χ a - 1‖ ≤ 1 / 256 := by
    intro a ha
    have := (hpt a ha).trans h8
    nlinarith [norm_nonneg (χ a - 1)]
  -- a nontrivial character
  have hχne : ∃ g, χ g ≠ 1 := by
    by_contra h
    push_neg at h
    exact hχ0 (AddChar.ext χ 0 fun g => by simp [h g])
  obtain ⟨q, ψ, hq2, hψ, hparam⟩ := addChar_param_surj χ hχne
  haveI : NeZero q := ⟨by omega⟩
  refine exists_compression A 8 q hq2 ψ hψ fun a ha => ?_
  set t := (ψ a).valMinAbs with ht
  have hχa : χ a = expQ q t := hparam a t (ZMod.coe_valMinAbs _)
  have ht2 : 2 * |t| ≤ q := by
    have := ZMod.natAbs_valMinAbs_le (ψ a)
    rw [← ht] at this
    have : (t.natAbs : ℤ) ≤ ((q / 2 : ℕ) : ℤ) := by exact_mod_cast this
    rw [Int.natCast_natAbs] at this
    have : ((q / 2 : ℕ) : ℤ) * 2 ≤ q := by exact_mod_cast Nat.div_mul_le_self q 2
    linarith
  have hchord := four_mul_abs_div_le_norm_expQ_sub_one (by omega : 0 < q) ht2
  rw [← hχa] at hchord
  have hq' : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have : 4 * |(t : ℝ)| / q ≤ 1 / 256 := hchord.trans (hpt' a ha)
  rw [div_le_iff₀ hq'] at this
  have : (1024 : ℝ) * |(t : ℝ)| ≤ q := by linarith
  have : (1024 : ℤ) * |t| ≤ q := by
    have h := this
    rw [← Int.cast_abs] at h
    exact_mod_cast h
  push_cast
  linarith [abs_nonneg t]

/-- **The dense Freiman model.** -/
theorem exists_dense_model (κ : ℕ) (hκ : 1 ≤ κ) (G : Type) [AddCommGroup G] [Fintype G]
    [DecidableEq G] (A : Finset G) (hA : AddApprox κ A) :
    ∃ (G' : Type) (_ : AddCommGroup G') (_ : Fintype G') (φ : G → G'),
      IsFIso 8 A φ ∧ φ 0 = 0 ∧ Fintype.card G' ≤ modelBound κ * A.card := by
  classical
  have hP : ∃ m : ℕ, ∃ (G' : Type) (_ : AddCommGroup G') (_ : Fintype G') (φ : G → G'),
      IsFIso 8 A φ ∧ φ 0 = 0 ∧ Fintype.card G' = m :=
    ⟨Fintype.card G, G, inferInstance, inferInstance, id, fun _ _ _ _ => Iff.rfl, rfl, rfl⟩
  obtain ⟨G', i1, i2, φ, hφ, hφ0, hcard⟩ := Nat.find_spec hP
  refine ⟨G', i1, i2, φ, hφ, hφ0, ?_⟩
  by_contra hbig
  push_neg at hbig
  have h0 := hA.zero_mem
  have hcardA : (A.image φ).card = A.card := hφ.card_image (by norm_num) h0 hφ0
  have hA' : AddApprox κ (A.image φ) := hA.image hφ (by norm_num) hφ0
  rw [← hcardA] at hbig
  obtain ⟨G'', j1, j2, hlt, c, hc, hc0⟩ := exists_smaller_model κ hκ (A.image φ) hA' hbig
  have hmin := Nat.find_min hP (m := Fintype.card G'') (by rw [← hcard]; exact hlt)
  exact hmin ⟨G'', j1, j2, c ∘ φ, hφ.comp hc, by simp [hφ0, hc0], rfl⟩

end GreenRuzsa
