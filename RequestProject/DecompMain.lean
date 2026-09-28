module
public import RequestProject.DecompRefine

/-!
# Lemma 2.3: the expander decomposition

We prove `ExpanderDecomposition` (Lemma 2.3 of the paper, i.e. Lemma 4.1 of the cited work on
sublinear expanders with `α = 1`, `C = 57`, `c = 114`), so that it is no longer an assumption.
-/

@[expose] public section


open scoped BigOperators
open Classical

namespace Lovasz

noncomputable section

variable {V : Type*} {G : SimpleGraph V}

/-- The properties required by Lemma 2.3 for a final piece. -/
lemma piece_props {U H : Finset V} {d L : ℝ} (hd : 0 < d)
    (hdeg : ∀ v ∈ U, (degIn G U v : ℝ) ≤ d) (hHU : H ⊆ U) (hL1 : 1 ≤ L) {j : ℕ}
    (hMj : 4 ≤ Mseq L j) (hgood : GoodPiece G H (1 / Mseq L j ^ 57))
    (hreg : d * (1 - 1 / Mseq L j ^ 28) * H.card ≤ dsum G H)
    (hlogj : Real.log H.card ≤ Mseq L j) (hlt : Mseq L (j + 1) < Real.log H.card) :
    IsExpander G H (1 / 8) 114 (d / (4 * Real.log H.card ^ 114)) ∧
      d * (1 - Real.log H.card ^ (-(28 : ℝ))) * H.card ≤ ∑ v ∈ H, (degIn G H v : ℝ) ∧
      ∀ v ∈ H, (∑ u ∈ H, (degIn G H u : ℝ)) / H.card / 2 ≤ degIn G H v := by
  have hdsum : (dsum G H : ℝ) = ∑ v ∈ H, (degIn G H v : ℝ) := by
    unfold dsum; push_cast; rfl
  have hM1 : 1 ≤ Mseq L (j + 1) := one_le_Mseq hL1 (j + 1)
  have hlogpos : 0 < Real.log H.card := by linarith
  have hsq : Mseq L (j + 1) ^ 2 = Mseq L j := Mseq_succ_sq hL1 j
  have hpos : (0 : ℝ) < H.card := by exact_mod_cast hgood.1.card_pos
  have hM28 : (4 : ℝ) ≤ Mseq L j ^ 28 := le_trans hMj (le_self_pow₀ (by linarith) (by norm_num))
  have hinv : 1 / Mseq L j ^ 28 ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hM28
  refine ⟨?_, ?_, ?_⟩
  · set lam := 1 / Real.log H.card ^ 114 with hlam
    have hlam0 : 0 ≤ lam := by positivity
    have hle : lam ≤ 1 / Mseq L j ^ 57 := by
      rw [hlam, ← hsq, ← pow_mul]
      refine one_div_le_one_div_of_le (by positivity) ?_
      exact pow_le_pow_left₀ (by linarith) hlt.le _
    have hexp := hgood.2.1.mono hle
    have havg : d * (3 / 4) ≤ avgDeg G H := by
      rw [avgDeg, le_div_iff₀ hpos]
      have : d * (3 / 4) * H.card ≤ d * (1 - 1 / Mseq L j ^ 28) * H.card :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hd.le) hpos.le
      linarith
    intro X hX F _ h3 hF
    have hF' : (F.card : ℝ) ≤ lam * d / 4 * X.card := by
      refine le_trans hF (le_of_eq ?_)
      rw [hlam]; field_simp
    have := lamExp_vertex_expansion hd hlam0 (degIn_le_of_subset hHU hdeg) havg hexp X hX F h3 hF'
    refine le_trans (le_of_eq ?_) this
    rw [hlam]; ring
  · rw [← hdsum]
    refine le_trans ?_ hreg
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hd.le) hpos.le
    rw [Real.rpow_neg hlogpos.le, show ((28 : ℝ)) = ((28 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      ← one_div]
    have : Real.log H.card ^ 28 ≤ Mseq L j ^ 28 := pow_le_pow_left₀ hlogpos.le hlogj 28
    have := one_div_le_one_div_of_le (by positivity) this
    linarith
  · intro v hv
    have := hgood.2.2 v hv
    rw [avgDeg, hdsum] at this
    exact this

/-- Bounding the number of refining steps. -/
lemma steps_bound {L : ℝ} (hL : Real.exp (Real.exp 3) ≤ L) (t : ℕ)
    (ht : t = 0 ∨ 4 < Mseq L t) : (t : ℝ) + 1 ≤ Real.log (Real.log L) ^ 2 := by
  have hL1 : 1 ≤ L := le_trans (Real.one_le_exp (Real.exp_pos 3).le) hL
  have hlogL : Real.exp 3 ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le (by linarith)]; exact hL
  have hx : 3 ≤ Real.log (Real.log L) := by
    rw [Real.le_log_iff_exp_le (by linarith [Real.exp_pos 3])]; exact hlogL
  rcases ht with h0 | h4
  · rw [h0]; push_cast; nlinarith
  · have hlog4 : 1 < Real.log (Mseq L t) := by
      have : Real.log 4 < Real.log (Mseq L t) := Real.log_lt_log (by norm_num) h4
      have h4e : 1 < Real.log 4 := by
        rw [Real.lt_log_iff_exp_lt (by norm_num)]
        have := Real.exp_one_lt_d9
        linarith
      linarith
    rw [log_Mseq hL1] at hlog4
    have h2t : (2 : ℝ) ^ t < Real.log L := by
      rw [lt_div_iff₀ (by positivity)] at hlog4; linarith
    have ht2 : (t : ℝ) * Real.log 2 < Real.log (Real.log L) := by
      rw [← Real.log_pow]
      exact Real.log_lt_log (by positivity) h2t
    have hl2 := Real.log_two_gt_d9
    have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
    nlinarith

/-- **Lemma 2.3** of the paper (Lemma 4.1 of the cited work on sublinear expanders with `α = 1`,
`C = 57`), proved. -/
theorem expander_decomposition : ExpanderDecomposition := by
  refine ⟨⌈Real.exp (Real.exp (Real.exp 3))⌉₊, ?_⟩
  intro V _ G U d ε hN hd hε0 hε hdeg havg
  set L := Real.log U.card with hLdef
  have hUpos : (0 : ℝ) < U.card := by
    have : (0 : ℝ) < ⌈Real.exp (Real.exp (Real.exp 3))⌉₊ := by
      have := Nat.le_ceil (Real.exp (Real.exp (Real.exp 3)))
      linarith [Real.exp_pos (Real.exp (Real.exp 3))]
    exact lt_of_lt_of_le this (by exact_mod_cast hN)
  have hL : Real.exp (Real.exp 3) ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le hUpos]
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast hN)
  have he3 : (4 : ℝ) < Real.exp 3 := by
    have := Real.add_one_lt_exp (show (3 : ℝ) ≠ 0 by norm_num)
    linarith
  have hee : Real.exp 3 ≤ Real.exp (Real.exp 3) := by
    rw [Real.exp_le_exp]; linarith [Real.add_one_le_exp (3 : ℝ)]
  have hL2 : Real.exp 2 ≤ L := le_trans (le_trans (Real.exp_le_exp.2 (by norm_num)) hee) hL
  have hL4 : 4 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hdpos : 0 < d := by linarith
  have hεL : ε ≤ 1 / L ^ 56 := by
    rw [Real.rpow_neg (by linarith), show ((56 : ℝ)) = ((56 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, ← one_div] at hε
    exact hε
  have havg' : d * (1 - ε) * U.card ≤ dsum G U := by
    unfold dsum; push_cast; exact havg
  -- the number of refining steps
  have hex : ∃ k : ℕ, Mseq L (k + 1) ≤ 4 := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (Real.log L) (show (1 : ℝ) < 2 by norm_num)
    refine ⟨k, ?_⟩
    have hpos : 0 < Mseq L (k + 1) := by linarith [one_le_Mseq hL1 (k + 1)]
    rw [← Real.log_le_log_iff hpos (by norm_num), log_Mseq hL1]
    have h4 : (1 : ℝ) ≤ Real.log 4 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have := Real.exp_one_lt_d9
      linarith
    rw [div_le_iff₀ (by positivity), pow_succ]
    nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) k]
  set t := Nat.find hex
  have hbig : ∀ k < t, 4 < Mseq L (k + 1) := by
    intro k hk
    have := Nat.find_min hex hk
    push_neg at this; exact this
  have hMj : ∀ j ≤ t, 4 < Mseq L j := by
    intro j hj
    rcases Nat.eq_zero_or_pos t with h0 | hpos
    · have : j = 0 := by omega
      rw [this, Mseq_zero]; exact hL4
    · have := hbig (t - 1) (by omega)
      rw [Nat.sub_add_cancel hpos] at this
      exact lt_of_lt_of_le this (Mseq_anti hL1 hj)
  have hstage : ∀ k ≤ t, Stage G U d L k := by
    intro k
    induction k with
    | zero => intro _; exact stage_zero hdpos hL2 hLdef hεL hdeg havg'
    | succ k ih =>
      intro hk
      exact stage_succ hdpos hd hL2 hdeg (le_of_lt (lt_trans (by norm_num) (hbig k (by omega))))
        (ih (by omega))
  obtain ⟨𝓗, hdisj, hmem, hcov⟩ := hstage t le_rfl
  -- every final piece has left the refining procedure
  have hfinal : ∀ H ∈ 𝓗, ∃ j ≤ t, GoodPiece G H (1 / Mseq L j ^ 57) ∧
      d * (1 - 1 / Mseq L j ^ 28) * H.card ≤ dsum G H ∧
      Real.log H.card ≤ Mseq L j ∧ Mseq L (j + 1) < Real.log H.card := by
    intro H hH
    obtain ⟨hHU, j, hj, hgood, hreg, hlogj, hor⟩ := hmem H hH
    refine ⟨j, hj, hgood, hreg, hlogj, ?_⟩
    rcases hor with h | h
    · exact h
    · have hM4 : Mseq L (j + 1) ≤ 4 := by rw [h]; exact Nat.find_spec hex
      have hpos : (0 : ℝ) < H.card := by exact_mod_cast hgood.1.card_pos
      have hM28 : (4 : ℝ) ≤ Mseq L j ^ 28 :=
        le_trans (hMj j hj).le (le_self_pow₀ (by linarith [hMj j hj]) (by norm_num))
      have hinv : 1 / Mseq L j ^ 28 ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hM28
      have havgH : L ≤ avgDeg G H := by
        rw [avgDeg, le_div_iff₀ hpos]
        have : d * (3 / 4) * H.card ≤ d * (1 - 1 / Mseq L j ^ 28) * H.card :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hdpos.le) hpos.le
        nlinarith
      have hHL : L < H.card := lt_of_le_of_lt havgH (avgDeg_lt_card hgood.1)
      have : Real.exp 3 < Real.log H.card := by
        rw [Real.lt_log_iff_exp_lt hpos]
        exact lt_of_le_of_lt hL hHL
      linarith
  -- index the pieces
  set e := 𝓗.equivFin
  refine ⟨𝓗.card, fun i => (e.symm i : Finset V), fun _ => G, ?_, ?_, fun _ => le_rfl, ?_, ?_, ?_,
    ?_⟩
  · intro i
    exact (hmem _ (e.symm i).2).1
  · intro i j hij
    refine hdisj (e.symm i).2 (e.symm j).2 ?_
    intro h
    exact hij (e.symm.injective (Subtype.ext h))
  · intro i
    obtain ⟨j, hj, hgood, hreg, hlogj, hlt⟩ := hfinal _ (e.symm i).2
    exact (piece_props hdpos hdeg (hmem _ (e.symm i).2).1 hL1 (hMj j hj).le hgood hreg hlogj
      hlt).1
  · intro i
    obtain ⟨j, hj, hgood, hreg, hlogj, hlt⟩ := hfinal _ (e.symm i).2
    exact (piece_props hdpos hdeg (hmem _ (e.symm i).2).1 hL1 (hMj j hj).le hgood hreg hlogj
      hlt).2.1
  · intro i
    obtain ⟨j, hj, hgood, hreg, hlogj, hlt⟩ := hfinal _ (e.symm i).2
    exact (piece_props hdpos hdeg (hmem _ (e.symm i).2).1 hL1 (hMj j hj).le hgood hreg hlogj
      hlt).2.2
  · have hsum : ∑ i, (((e.symm i : Finset V)).card : ℝ) = (cover 𝓗).card := by
      rw [Equiv.sum_comp e.symm (fun x : 𝓗 => ((x : Finset V).card : ℝ)),
        Finset.sum_coe_sort 𝓗 (fun H => (H.card : ℝ)),
        show (cover 𝓗).card = ∑ H ∈ 𝓗, H.card from card_biUnion_eq hdisj]
      push_cast; rfl
    rw [hsum]
    refine le_trans ?_ hcov
    refine mul_le_mul_of_nonneg_right ?_ hUpos.le
    have hsteps := steps_bound hL t (by
      rcases Nat.eq_zero_or_pos t with h0 | hpos
      · exact Or.inl h0
      · exact Or.inr (hMj t le_rfl))
    have hlogL : 0 < Real.log L := Real.log_pos (by linarith)
    have : ((t : ℝ) + 1) / Real.log L ≤ Real.log (Real.log L) ^ 2 / Real.log L :=
      div_le_div_of_nonneg_right hsteps hlogL.le
    linarith

end

end Lovasz
