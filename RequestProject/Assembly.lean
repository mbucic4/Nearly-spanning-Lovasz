module
public import RequestProject.Dense

/-!
# Assembling the proof of Theorem 1.2 (the sparse case)

From the expander decomposition of the interval graph we build the blocks of the concrete
geometry, check the hypotheses of the probabilistic core and apply it to the initial circuit.
-/

@[expose] public section


open Classical

namespace Lovasz

section smallblocks

variable {ι : Type*}

lemma log_three_gt : (1.0264 : ℝ) < Real.log 3 := by
  have h2 := Real.log_two_gt_d9
  have h15 : (1 : ℝ) / 3 ≤ Real.log (3 / 2) := by
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 3 / 2 by norm_num)
    norm_num at this ⊢; linarith
  have : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
    rw [← Real.log_mul] <;> norm_num
  linarith

lemma two_le_log_pow {w : ℝ} (hw : 3 ≤ w) : 2 ≤ Real.log w ^ 28 := by
  have h1 : Real.log 3 ≤ Real.log w := Real.log_le_log (by norm_num) hw
  have h2 := log_three_gt
  calc (2 : ℝ) ≤ 1.0264 ^ 28 := by norm_num
    _ ≤ Real.log w ^ 28 := pow_le_pow_left₀ (by norm_num) (by linarith) _

lemma log_rpow_neg_le {w : ℝ} (hw : 3 ≤ w) : Real.log w ^ (-(28 : ℝ)) ≤ 1 / 2 := by
  have hpos : 0 < Real.log w := Real.log_pos (by linarith)
  rw [Real.rpow_neg hpos.le, show (28 : ℝ) = ((28 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have := two_le_log_pow hw
  rw [inv_le_comm₀ (by positivity) (by norm_num)]
  linarith

/-- Blocks of the decomposition have at least three vertices. -/
lemma three_le_card_block {H : SimpleGraph ι} {W : Finset ι} {d s : ℝ} (hd : 0 < d) (hs : 0 ≤ s)
    (hexp : IsExpander H W (1 / 8) 114 s)
    (havg : d * (1 - Real.log W.card ^ (-(28 : ℝ))) * W.card ≤ ∑ v ∈ W, (degIn H W v : ℝ))
    (hne : W.Nonempty) : 3 ≤ W.card := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨v, hv⟩ := hne
  have h1 : 1 ≤ W.card := Finset.card_pos.2 ⟨v, hv⟩
  rcases (show W.card = 1 ∨ W.card = 2 by omega) with h | h
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 h
    have hdeg : degIn H {a} a = 0 := by
      unfold degIn
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x hx; rw [Finset.mem_singleton] at hx; subst hx; exact H.loopless.irrefl _
    rw [Finset.sum_singleton, hdeg, h] at havg
    simp [Real.zero_rpow (show (-(28 : ℝ)) ≠ 0 by norm_num)] at havg
    linarith
  · have hX := hexp {v} (Finset.singleton_subset_iff.2 hv) ∅ (by simp) (by simp; omega)
      (by simp; positivity)
    have hle : (extNb H W {v} ∅).card ≤ 1 := by
      have : extNb H W {v} ∅ ⊆ W \ {v} := Finset.filter_subset _ _
      have := Finset.card_le_card this
      rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.2 hv), h] at this
      simpa using this
    rw [h] at hX
    have hl2 : Real.log 2 < 0.7 := by have := Real.log_two_lt_d9; linarith
    have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hp : Real.log 2 ^ 114 < 1 / 8 := by
      calc Real.log 2 ^ 114 < 0.7 ^ 114 := pow_lt_pow_left₀ hl2 hl0.le (by norm_num)
        _ ≤ 1 / 8 := by norm_num
    have hle' : ((extNb H W {v} ∅).card : ℝ) ≤ 1 := by exact_mod_cast hle
    have : (1 : ℝ) < 1 / 8 / Real.log (↑(2 : ℕ)) ^ 114 * (({v} : Finset ι).card : ℝ) := by
      rw [Finset.card_singleton, Nat.cast_one, mul_one, Nat.cast_ofNat, lt_div_iff₀ (by positivity)]
      linarith
    linarith

/-- The minimum degree of a block is at least `d / 4`. -/
lemma min_deg_block {H : SimpleGraph ι} {W : Finset ι} {d : ℝ} (hd : 0 < d) (h3 : 3 ≤ W.card)
    (havg : d * (1 - Real.log W.card ^ (-(28 : ℝ))) * W.card ≤ ∑ v ∈ W, (degIn H W v : ℝ))
    (hmin : ∀ v ∈ W, (∑ u ∈ W, (degIn H W u : ℝ)) / W.card / 2 ≤ degIn H W v) :
    ∀ v ∈ W, d / 4 ≤ degIn H W v := by
  intro v hv
  refine le_trans ?_ (hmin v hv)
  have hW : (3 : ℝ) ≤ W.card := by exact_mod_cast h3
  have hr := log_rpow_neg_le hW
  rw [le_div_iff₀ (by norm_num), le_div_iff₀ (by linarith)]
  have : d * (1 / 2) * W.card ≤ d * (1 - Real.log W.card ^ (-(28 : ℝ))) * W.card := by
    gcongr; linarith
  linarith

end smallblocks

namespace Conc

variable {n t : ℕ} {f : Fin n → Fin n} {m : ℕ}

section blocks

variable (W : Fin m → Finset (Fin (2 * nQ n t)))

/-- The nonempty blocks. -/
abbrev Blk := {i : Fin m // (W i).Nonempty}

/-- The block containing an interval. -/
noncomputable def blkOf (J : Fin (2 * nQ n t)) : Option (Blk W) :=
  if h : ∃ G : Blk W, J ∈ W G.1 then some h.choose else none

variable {W}

lemma blkOf_eq_some (hW : ∀ i j, i ≠ j → Disjoint (W i) (W j)) {J : Fin (2 * nQ n t)}
    {G : Blk W} : blkOf W J = some G ↔ J ∈ W G.1 := by
  unfold blkOf
  constructor
  · intro h
    split_ifs at h with h'
    · rw [Option.some.injEq] at h; subst h; exact h'.choose_spec
  · intro hJ
    have h' : ∃ G : Blk W, J ∈ W G.1 := ⟨G, hJ⟩
    rw [dif_pos h', Option.some.injEq]
    by_contra hne
    have hne' : h'.choose.1 ≠ G.1 := fun e => hne (Subtype.ext e)
    exact Finset.disjoint_left.1 (hW _ _ hne') h'.choose_spec hJ

variable (t f)

/-- The chosen edge of `M` between two intervals. -/
noncomputable def meOf (hn : 0 < n) (I I' : Fin (2 * nQ n t)) : Fin (2 * n) × Fin (2 * n) :=
  if h : (mpairs t f I I').Nonempty then h.choose else (fv n hn 0, fv n hn 0)

variable {t f}

lemma meOf_mem (hn : 0 < n) {I I' : Fin (2 * nQ n t)} (h : mult t f I I' = 1) :
    meOf t f hn I I' ∈ mpairs t f I I' := by
  have hne : (mpairs t f I I').Nonempty := Finset.card_pos.1 (by unfold mult at h; omega)
  unfold meOf; rw [dif_pos hne]; exact hne.choose_spec

lemma meOf_swap (hn : 0 < n) {I I' : Fin (2 * nQ n t)} (h : mult t f I I' = 1) :
    meOf t f hn I' I = ((meOf t f hn I I').2, (meOf t f hn I I').1) := by
  have h' : mult t f I' I = 1 := by rw [mult_symm]; exact h
  have h1 := meOf_mem hn h
  have h2 := meOf_mem hn h'
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 h'
  rw [ha, Finset.mem_singleton] at h2
  rw [h2]
  have hsw : (meOf t f hn I I').swap ∈ mpairs t f I' I := by
    rw [mem_mpairs] at h1 ⊢; exact ⟨h1.2.1, h1.1, Mrel_symm h1.2.2⟩
  rw [ha, Finset.mem_singleton] at hsw
  rw [← hsw]; rfl

end blocks

/-- The blocks satisfy the hypotheses of the linking step. -/
lemma blockOK (hn : 0 < n) (ht : 2 ≤ t) (hQ : 0 < nQ n t) (hf : Function.Injective f)
    {W : Fin m → Finset (Fin (2 * nQ n t))} {H : Fin m → SimpleGraph (Fin (2 * nQ n t))}
    (hW : ∀ i j, i ≠ j → Disjoint (W i) (W j)) (hH : ∀ i, H i ≤ IG t f) (G : Blk W) :
    (cgeo n t hn ht hQ f hf (blkOf W)).BlockOK G (H G.1) (W G.1) (meOf t f hn) where
  blk_U I hI := (blkOf_eq_some hW).2 hI
  me_iv1 {I I'} h := by
    have := meOf_mem (f := f) hn ((hH G.1) h).2
    rw [mem_mpairs] at this; exact this.1
  me_iv2 {I I'} h := by
    have := meOf_mem (f := f) hn ((hH G.1) h).2
    rw [mem_mpairs] at this; exact this.2.1
  me_M {I I'} h := by
    have := meOf_mem (f := f) hn ((hH G.1) h).2
    rw [mem_mpairs] at this; exact this.2.2
  me_swap {I I'} h := meOf_swap hn ((hH G.1) h).2

end Conc

end Lovasz
