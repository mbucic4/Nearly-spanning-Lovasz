module
public import RequestProject.DecompBasic

/-!
# Extracting one `λ`-expander (Lemma 4.5 of the cited work on sublinear expanders)
-/

@[expose] public section


open scoped BigOperators
open Classical

namespace Lovasz

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

/-- A piece of the decomposition: a non-empty `λ`-expander whose minimum degree is at least half
its average degree. -/
def GoodPiece (W : Finset V) (lam : ℝ) : Prop :=
  W.Nonempty ∧ IsLamExp G W lam ∧ ∀ v ∈ W, avgDeg G W / 2 ≤ degIn G W v

variable {G}

lemma dsum_singleton (v : V) : dsum G {v} = 0 := by
  unfold dsum degIn
  simp

lemma dsum_erase {W : Finset V} {v : V} (hv : v ∈ W) :
    dsum G (W.erase v) + 2 * degIn G W v = dsum G W := by
  have hsub : ({v} : Finset V) ⊆ W := Finset.singleton_subset_iff.2 hv
  have h := dsum_split (G := G) hsub
  rw [Finset.sdiff_singleton_eq_erase, dsum_singleton, eCut_eq_sum, Finset.sum_singleton] at h
  have h2 := degIn_split (G := G) hsub v
  rw [Finset.sdiff_singleton_eq_erase] at h2
  have h3 : degIn G {v} v = 0 := by unfold degIn; simp
  rw [h3, zero_add] at h2
  rw [h2]; omega

lemma exists_lamExp_aux {lam : ℝ} (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1 / 2) :
    ∀ n : ℕ, ∀ W : Finset V, W.card = n → W.Nonempty →
      ∃ H ⊆ W, GoodPiece G H lam ∧
        avgDeg G W * (1 - 2 * lam) ^ (Nat.log 2 W.card) ≤ avgDeg G H := by
  have hq0 : 0 ≤ 1 - 2 * lam := by linarith
  have hq1 : 1 - 2 * lam ≤ 1 := by linarith
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W hWn hW
  have hWpos : (0 : ℝ) < W.card := by exact_mod_cast hW.card_pos
  have haW := avgDeg_mul_card (G := G) hW
  have ha0 := avgDeg_nonneg (G := G) W
  by_cases hA : GoodPiece G W lam
  · refine ⟨W, subset_rfl, hA, ?_⟩
    have : (1 - 2 * lam) ^ (Nat.log 2 W.card) ≤ 1 := pow_le_one₀ hq0 hq1
    nlinarith
  by_cases hB : ∃ v ∈ W, (degIn G W v : ℝ) < avgDeg G W / 2
  · obtain ⟨v, hv, hdv⟩ := hB
    set W' := W.erase v
    have hcard : W'.card + 1 = W.card := Finset.card_erase_add_one hv
    have hW' : W'.Nonempty := by
      rw [← Finset.card_pos]
      by_contra h0
      have h1 : W.card = 1 := by omega
      obtain ⟨u, hu⟩ := Finset.card_eq_one.1 h1
      have : v = u := by rw [hu] at hv; simpa using hv
      subst this
      have : dsum G W = 0 := by rw [hu]; exact dsum_singleton v
      rw [this, h1] at haW
      simp at haW
      rw [haW] at hdv
      have : (0 : ℝ) ≤ degIn G W v := Nat.cast_nonneg _
      linarith
    have hsum := dsum_erase (G := G) hv
    have hW'pos : (0 : ℝ) < W'.card := by exact_mod_cast hW'.card_pos
    have haW' := avgDeg_mul_card (G := G) hW'
    have hle : avgDeg G W ≤ avgDeg G W' := by
      have hc : (W'.card : ℝ) + 1 = W.card := by exact_mod_cast hcard
      have hs : (dsum G W' : ℝ) + 2 * degIn G W v = dsum G W := by exact_mod_cast hsum
      by_contra hlt
      push_neg at hlt
      have : avgDeg G W' * W'.card < avgDeg G W * W'.card :=
        mul_lt_mul_of_pos_right hlt hW'pos
      nlinarith
    obtain ⟨H, hHW, hH, hbound⟩ := ih W'.card (by omega) W' rfl hW'
    refine ⟨H, hHW.trans (Finset.erase_subset _ _), hH, le_trans ?_ hbound⟩
    have hpow : (1 - 2 * lam) ^ (Nat.log 2 W.card) ≤ (1 - 2 * lam) ^ (Nat.log 2 W'.card) :=
      pow_le_pow_of_le_one hq0 hq1 (Nat.log_mono_right (by omega))
    exact mul_le_mul hle hpow (pow_nonneg hq0 _) (avgDeg_nonneg _)
  push_neg at hB
  have hnexp : ¬ IsLamExp G W lam := fun h => hA ⟨hW, h, hB⟩
  unfold IsLamExp at hnexp
  push_neg at hnexp
  obtain ⟨X, hXW, hX2, hcut⟩ := hnexp
  have hXne : X.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    simp [eCut] at hcut
  set Y := W \ X
  have hcardXY : Y.card + X.card = W.card := Finset.card_sdiff_add_card_eq_card hXW
  have hXpos := hXne.card_pos
  have hYne : Y.Nonempty := by rw [← Finset.card_pos]; omega
  have hsplit := dsum_split (G := G) hXW
  have haX := avgDeg_mul_card (G := G) hXne
  have haY := avgDeg_mul_card (G := G) hYne
  have hX0 : (0 : ℝ) < X.card := by exact_mod_cast hXpos
  have hY0 : (0 : ℝ) < Y.card := by exact_mod_cast hYne.card_pos
  have hdich : avgDeg G W ≤ avgDeg G Y ∨ (1 - 2 * lam) * avgDeg G W ≤ avgDeg G X := by
    by_contra hc
    push_neg at hc
    obtain ⟨h1, h2⟩ := hc
    have hs : (dsum G W : ℝ) = dsum G X + dsum G Y + 2 * eCut G X Y := by exact_mod_cast hsplit
    have hc' : (Y.card : ℝ) + X.card = W.card := by exact_mod_cast hcardXY
    have e1 : avgDeg G Y * Y.card < avgDeg G W * Y.card := mul_lt_mul_of_pos_right h1 hY0
    have e2 : avgDeg G X * X.card < (1 - 2 * lam) * avgDeg G W * X.card :=
      mul_lt_mul_of_pos_right h2 hX0
    nlinarith
  rcases hdich with hY | hX
  · obtain ⟨H, hHY, hH, hbound⟩ := ih Y.card (by omega) Y rfl hYne
    refine ⟨H, hHY.trans Finset.sdiff_subset, hH, le_trans ?_ hbound⟩
    have hpow : (1 - 2 * lam) ^ (Nat.log 2 W.card) ≤ (1 - 2 * lam) ^ (Nat.log 2 Y.card) :=
      pow_le_pow_of_le_one hq0 hq1 (Nat.log_mono_right (by omega))
    exact mul_le_mul hY hpow (pow_nonneg hq0 _) (avgDeg_nonneg _)
  · obtain ⟨H, hHX, hH, hbound⟩ := ih X.card (by omega) X rfl hXne
    refine ⟨H, hHX.trans hXW, hH, le_trans ?_ hbound⟩
    have hlog : Nat.log 2 X.card + 1 ≤ Nat.log 2 W.card := by
      rw [← Nat.log_mul_base (by norm_num) hXpos.ne']
      exact Nat.log_mono_right (by omega)
    have hpow : (1 - 2 * lam) ^ (Nat.log 2 W.card) ≤ (1 - 2 * lam) ^ (Nat.log 2 X.card + 1) :=
      pow_le_pow_of_le_one hq0 hq1 hlog
    rw [pow_succ] at hpow
    calc avgDeg G W * (1 - 2 * lam) ^ Nat.log 2 W.card
        ≤ avgDeg G W * ((1 - 2 * lam) ^ Nat.log 2 X.card * (1 - 2 * lam)) :=
          mul_le_mul_of_nonneg_left hpow ha0
      _ = ((1 - 2 * lam) * avgDeg G W) * (1 - 2 * lam) ^ Nat.log 2 X.card := by ring
      _ ≤ avgDeg G X * (1 - 2 * lam) ^ Nat.log 2 X.card :=
          mul_le_mul_of_nonneg_right hX (pow_nonneg hq0 _)

lemma nat_log_two_le (n : ℕ) (hn : n ≠ 0) : (Nat.log 2 n : ℝ) ≤ 3 / 2 * Real.log n := by
  have h1 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn
  have h2 : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast h1)
  have h3 := Real.log_two_gt_d9
  have h4 : (0 : ℝ) ≤ Nat.log 2 n := Nat.cast_nonneg _
  nlinarith

/-- **Lemma 4.5** (of the cited work): every non-empty vertex set contains a `λ`-expander with
minimum degree at least half its average degree, whose average degree is at least
`d(W) (1 - 3 λ log |W|)`. -/
theorem exists_lamExp {W : Finset V} (hW : W.Nonempty) {lam : ℝ} (hl0 : 0 ≤ lam)
    (hl1 : lam ≤ 1 / 2) :
    ∃ H ⊆ W, GoodPiece G H lam ∧ avgDeg G W * (1 - 3 * lam * Real.log W.card) ≤ avgDeg G H := by
  obtain ⟨H, hHW, hH, hb⟩ := exists_lamExp_aux (G := G) hl0 hl1 W.card W rfl hW
  refine ⟨H, hHW, hH, le_trans ?_ hb⟩
  refine mul_le_mul_of_nonneg_left ?_ (avgDeg_nonneg _)
  have hb1 := one_add_mul_le_pow (show (-2 : ℝ) ≤ -(2 * lam) by linarith) (Nat.log 2 W.card)
  have hk := nat_log_two_le W.card hW.card_pos.ne'
  have : (1 - 2 * lam) = 1 + -(2 * lam) := by ring
  rw [this]
  nlinarith

end

end Lovasz
