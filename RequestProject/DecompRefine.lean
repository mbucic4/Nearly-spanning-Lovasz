module
public import RequestProject.DecompPack

/-!
# The refining procedure (Lemma 4.3 of the cited work on sublinear expanders)

We work with natural logarithms and the instance `α = 1`, `C = 57` (so `γ = 1/2` and
`c = 114`).  With `L = log n`, the thresholds are `M 0 = L`, `M (k+1) = √(M k)`, and a piece of
level `j` is a `(M j)^(-57)`-expander with average degree at least `d (1 - (M j)^(-28))` and
`log |H| ≤ M j`.
-/

@[expose] public section


open scoped BigOperators
open Classical

namespace Lovasz

noncomputable section

/-- The thresholds `log n_k`: `M L 0 = L`, `M L (k+1) = √(M L k)`. -/
def Mseq (L : ℝ) : ℕ → ℝ
  | 0 => L
  | k + 1 => Real.sqrt (Mseq L k)

section Mseq

variable {L : ℝ}

lemma Mseq_zero : Mseq L 0 = L := rfl

lemma Mseq_succ (k : ℕ) : Mseq L (k + 1) = Real.sqrt (Mseq L k) := rfl

lemma one_le_Mseq (hL : 1 ≤ L) (k : ℕ) : 1 ≤ Mseq L k := by
  induction k with
  | zero => exact hL
  | succ k ih => rw [Mseq_succ]; exact Real.one_le_sqrt.2 ih

lemma Mseq_succ_sq (hL : 1 ≤ L) (k : ℕ) : Mseq L (k + 1) ^ 2 = Mseq L k := by
  rw [Mseq_succ, Real.sq_sqrt (by linarith [one_le_Mseq hL k])]

lemma Mseq_succ_le (hL : 1 ≤ L) (k : ℕ) : Mseq L (k + 1) ≤ Mseq L k := by
  have h1 := one_le_Mseq hL (k + 1)
  have h2 := Mseq_succ_sq hL k
  nlinarith

lemma Mseq_anti (hL : 1 ≤ L) : Antitone (Mseq L) :=
  antitone_nat_of_succ_le (Mseq_succ_le hL)

lemma log_Mseq (hL : 1 ≤ L) (k : ℕ) : Real.log (Mseq L k) = Real.log L / 2 ^ k := by
  induction k with
  | zero => simp [Mseq_zero]
  | succ k ih =>
    rw [Mseq_succ, Real.log_sqrt (by linarith [one_le_Mseq hL k]), ih, pow_succ]
    ring

end Mseq

variable {V : Type*} (G : SimpleGraph V)

/-- A piece of level at most `k`: for some `j ≤ k` it is a `(M j)^(-57)`-expander with minimum
degree at least half its average degree, average degree at least `d (1 - (M j)^(-28))`,
`log |H| ≤ M j`, and either `log |H| > M (j+1)` (it will never be refined again) or `j = k`. -/
def Lev (d L : ℝ) (k : ℕ) (H : Finset V) : Prop :=
  ∃ j ≤ k, GoodPiece G H (1 / Mseq L j ^ 57) ∧
    d * (1 - 1 / Mseq L j ^ 28) * H.card ≤ dsum G H ∧
    Real.log H.card ≤ Mseq L j ∧ (Mseq L (j + 1) < Real.log H.card ∨ j = k)

/-- The state after `k` refining steps. -/
def Stage (U : Finset V) (d L : ℝ) (k : ℕ) : Prop :=
  ∃ 𝓗 : Finset (Finset V), (𝓗 : Set (Finset V)).PairwiseDisjoint id ∧
    (∀ H ∈ 𝓗, H ⊆ U ∧ Lev G d L k H) ∧
    (1 - (k + 1) / Real.log L) * U.card ≤ (cover 𝓗).card

variable {G}

/-- Replacing each member of a disjoint family by a disjoint family inside it. -/
lemma refine_family {𝓗 : Finset (Finset V)} (hdisj : (𝓗 : Set (Finset V)).PairwiseDisjoint id)
    (Q : Finset V → Prop) {a : ℝ}
    (hfam : ∀ H ∈ 𝓗, ∃ 𝓕 : Finset (Finset V), (𝓕 : Set (Finset V)).PairwiseDisjoint id ∧
      (∀ F ∈ 𝓕, F ⊆ H ∧ Q F) ∧ (1 - a) * H.card ≤ (cover 𝓕).card) :
    ∃ 𝓗' : Finset (Finset V), (𝓗' : Set (Finset V)).PairwiseDisjoint id ∧
      (∀ F ∈ 𝓗', ∃ H ∈ 𝓗, F ⊆ H ∧ Q F) ∧
      (1 - a) * (cover 𝓗).card ≤ (cover 𝓗').card := by
  choose! f hf using hfam
  have hsubH : ∀ H ∈ 𝓗, cover (f H) ⊆ H := by
    intro H hH v hv
    obtain ⟨F, hF, hvF⟩ := Finset.mem_biUnion.1 hv
    exact ((hf H hH).2.1 F hF).1 hvF
  refine ⟨𝓗.biUnion f, ?_, ?_, ?_⟩
  · intro A hA B hB hAB
    simp only [Finset.coe_biUnion, Finset.mem_coe, Set.mem_iUnion] at hA hB
    obtain ⟨H1, hH1, hA⟩ := hA
    obtain ⟨H2, hH2, hB⟩ := hB
    by_cases h12 : H1 = H2
    · subst h12; exact (hf H1 hH1).1 hA hB hAB
    · exact Finset.disjoint_of_subset_left ((hf H1 hH1).2.1 A hA).1
        (Finset.disjoint_of_subset_right ((hf H2 hH2).2.1 B hB).1 (hdisj hH1 hH2 h12))
  · intro F hF
    obtain ⟨H, hH, hFH⟩ := Finset.mem_biUnion.1 hF
    exact ⟨H, hH, (hf H hH).2.1 F hFH⟩
  · have hcov : cover (𝓗.biUnion f) = 𝓗.biUnion (fun H => cover (f H)) := by
      unfold cover; rw [Finset.biUnion_biUnion]
    have hpd : (𝓗 : Set (Finset V)).PairwiseDisjoint (fun H => cover (f H)) := by
      intro H1 h1 H2 h2 hne
      exact Finset.disjoint_of_subset_left (hsubH H1 h1)
        (Finset.disjoint_of_subset_right (hsubH H2 h2) (hdisj h1 h2 hne))
    rw [hcov, Finset.card_biUnion hpd,
      show (cover 𝓗).card = ∑ H ∈ 𝓗, H.card from card_biUnion_eq hdisj]
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun H hH => (hf H hH).2.2

/-- The average degree is less than the number of vertices. -/
lemma avgDeg_lt_card {H : Finset V} (hH : H.Nonempty) : avgDeg G H < H.card := by
  have hpos : (0 : ℝ) < H.card := by exact_mod_cast hH.card_pos
  rw [avgDeg, div_lt_iff₀ hpos, dsum]
  push_cast
  calc ∑ v ∈ H, (degIn G H v : ℝ) < ∑ v ∈ H, (H.card : ℝ) :=
        Finset.sum_lt_sum_of_nonempty hH fun v hv => by exact_mod_cast degIn_lt_card hv
    _ = H.card * H.card := by rw [Finset.sum_const, nsmul_eq_mul]

/-- One member of a stage-`k` family is refined into stage-`(k+1)` pieces. -/
lemma refine_member {U : Finset V} {d L : ℝ} (hd : 0 < d) (hLd : 2 * L ≤ d)
    (hL : Real.exp 2 ≤ L) (hdeg : ∀ v ∈ U, (degIn G U v : ℝ) ≤ d) {k : ℕ}
    (hk : 2 ≤ Mseq L (k + 1)) {H : Finset V} (hHU : H ⊆ U) (hH : Lev G d L k H) :
    ∃ 𝓕 : Finset (Finset V), (𝓕 : Set (Finset V)).PairwiseDisjoint id ∧
      (∀ F ∈ 𝓕, F ⊆ H ∧ Lev G d L (k + 1) F) ∧
      (1 - 1 / Real.log L) * H.card ≤ (cover 𝓕).card := by
  obtain ⟨j, hjk, hgood, hreg, hlogj, hdisj⟩ := hH
  have hexp2 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hL1 : 1 ≤ L := by linarith
  have hanti := Mseq_anti hL1
  have hMj2 : 2 ≤ Mseq L j := le_trans hk (hanti (by omega))
  have hMj28 : (2 : ℝ) ^ 28 ≤ Mseq L j ^ 28 := pow_le_pow_left₀ (by norm_num) hMj2 28
  have hinv28 : 1 / Mseq L j ^ 28 ≤ 1 / 2 ^ 28 :=
    one_div_le_one_div_of_le (by positivity) hMj28
  have hHne := hgood.1
  have hpos : (0 : ℝ) < H.card := by exact_mod_cast hHne.card_pos
  have havgH : L ≤ avgDeg G H := by
    rw [avgDeg, le_div_iff₀ hpos]
    have : d * (1 / 2) * H.card ≤ d * (1 - 1 / Mseq L j ^ 28) * H.card := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hd.le) hpos.le
      norm_num at hinv28 ⊢; linarith
    nlinarith
  have hHL : L < H.card := lt_of_le_of_lt havgH (avgDeg_lt_card hHne)
  have hlogL : 2 ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le (by linarith)]; exact hL
  have hlogH : Real.log L < Real.log H.card := Real.log_lt_log (by linarith) hHL
  have hlogH0 : 0 ≤ Real.log H.card := by linarith
  by_cases hsmall : Real.log H.card ≤ Mseq L (k + 1)
  · have hjk' : j = k := by
      rcases hdisj with h | h
      · exfalso; have := hanti (show j + 1 ≤ k + 1 by omega); linarith
      · exact h
    subst hjk'
    set a := Mseq L (j + 1) with ha_def
    have ha2 : a ^ 2 = Mseq L j := Mseq_succ_sq hL1 j
    have ha0 : 0 < a := by linarith
    have hlam : 1 / a ^ 57 * Real.log H.card ≤ 1 / Mseq L j ^ 28 := by
      rw [← ha2, ← pow_mul]
      calc 1 / a ^ 57 * Real.log H.card ≤ 1 / a ^ 57 * a :=
            mul_le_mul_of_nonneg_left hsmall (by positivity)
        _ = 1 / a ^ (2 * 28) := by field_simp
    have hlam2 : 1 / a ^ 57 ≤ 1 / 2 := by
      have : a ≤ a ^ 57 := le_self_pow₀ (by linarith) (by norm_num)
      exact one_div_le_one_div_of_le (by norm_num) (by linarith)
    have hdegH := degIn_le_of_subset hHU hdeg
    obtain ⟨𝓕, h𝓕, hcov⟩ := pack_most (G := G) (S := H) (d := d) (ε := 1 / Mseq L j ^ 28)
      (lam := 1 / a ^ 57) hd.le (by positivity) (by positivity) hlam2
      (by norm_num at hinv28 hlam ⊢; linarith) hlam (by linarith) hdegH hreg
    have he : 1 / Mseq L j ^ 28 * Real.log H.card ^ 28 ≤ 1 / a ^ 28 := by
      rw [← ha2, ← pow_mul]
      have : Real.log H.card ^ 28 ≤ a ^ 28 := pow_le_pow_left₀ hlogH0 hsmall 28
      calc 1 / a ^ (2 * 28) * Real.log H.card ^ 28 ≤ 1 / a ^ (2 * 28) * a ^ 28 :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = 1 / a ^ 28 := by field_simp
    refine ⟨𝓕, h𝓕.1, fun F hF => ?_, ?_⟩
    · obtain ⟨hFH, hFgood, hFreg⟩ := h𝓕.2 F hF
      refine ⟨hFH, j + 1, le_rfl, hFgood, ?_, ?_, Or.inr rfl⟩
      · refine le_trans ?_ hFreg
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hd.le)
          (Nat.cast_nonneg _)
      · exact le_trans (Real.log_le_log (by exact_mod_cast hFgood.1.card_pos)
          (by exact_mod_cast Finset.card_le_card hFH)) hsmall
    · refine le_trans ?_ hcov
      refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
      have : 1 / Real.log H.card ≤ 1 / Real.log L :=
        one_div_le_one_div_of_le (by linarith) hlogH.le
      linarith
  · refine ⟨{H}, by simp, fun F hF => ?_, ?_⟩
    · rw [Finset.mem_singleton] at hF
      subst hF
      refine ⟨subset_rfl, j, by omega, hgood, hreg, hlogj, Or.inl ?_⟩
      rcases hdisj with h | h
      · exact h
      · subst h; push_neg at hsmall; exact hsmall
    · have hc : cover ({H} : Finset (Finset V)) = H := by simp [cover]
      rw [hc]
      have : 0 ≤ 1 / Real.log L := by positivity
      nlinarith

lemma stage_zero {U : Finset V} {d ε L : ℝ} (hd : 0 < d) (hL : Real.exp 2 ≤ L)
    (hLU : L = Real.log U.card) (hεL : ε ≤ 1 / L ^ 56)
    (hdeg : ∀ v ∈ U, (degIn G U v : ℝ) ≤ d) (havg : d * (1 - ε) * U.card ≤ dsum G U) :
    Stage G U d L 0 := by
  have hexp2 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hL2 : 2 ≤ L := by linarith
  have hlogL : 2 ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le (by linarith)]; exact hL
  have hL0 : 0 < L := by linarith
  have hlam2 : 1 / L ^ 57 ≤ 1 / 2 := by
    have : L ≤ L ^ 57 := le_self_pow₀ (by linarith) (by norm_num)
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hlamL : 1 / L ^ 57 * Real.log U.card = 1 / L ^ 56 := by
    rw [← hLU]; field_simp
  have hL56 : 1 / L ^ 56 ≤ 1 / 3 := by
    have : L ≤ L ^ 56 := le_self_pow₀ (by linarith) (by norm_num)
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have havg' : d * (1 - 1 / L ^ 56) * U.card ≤ dsum G U := by
    refine le_trans ?_ havg
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hd.le)
      (Nat.cast_nonneg _)
  obtain ⟨𝒞, h𝒞, hcov⟩ := pack_most (G := G) (S := U) (d := d) (ε := 1 / L ^ 56)
    (lam := 1 / L ^ 57) hd.le (by positivity) (by positivity) hlam2 (by linarith) hlamL.le
    (by rw [← hLU]; exact hL2) hdeg havg'
  have he : 1 / L ^ 56 * Real.log U.card ^ 28 = 1 / L ^ 28 := by
    rw [← hLU]; field_simp
  rw [he] at h𝒞
  rw [← hLU] at hcov
  refine ⟨𝒞, h𝒞.1, fun H hH => ?_, ?_⟩
  · obtain ⟨hHU, hHgood, hHreg⟩ := h𝒞.2 H hH
    refine ⟨hHU, 0, le_rfl, by simpa [Mseq_zero] using hHgood, by simpa [Mseq_zero] using hHreg,
      ?_, Or.inr rfl⟩
    rw [Mseq_zero, hLU]
    exact Real.log_le_log (by exact_mod_cast hHgood.1.card_pos)
      (by exact_mod_cast Finset.card_le_card hHU)
  · refine le_trans ?_ hcov
    refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
    have : 1 / L ≤ 1 / Real.log L :=
      one_div_le_one_div_of_le (by linarith) (Real.log_le_self hL0.le)
    push_cast
    linarith

lemma stage_succ {U : Finset V} {d L : ℝ} (hd : 0 < d) (hLd : 2 * L ≤ d)
    (hL : Real.exp 2 ≤ L) (hdeg : ∀ v ∈ U, (degIn G U v : ℝ) ≤ d) {k : ℕ}
    (hk : 2 ≤ Mseq L (k + 1)) (h : Stage G U d L k) : Stage G U d L (k + 1) := by
  have hexp2 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hlogL : 2 ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le (by linarith)]; exact hL
  obtain ⟨𝓗, hdisj, hmem, hcov⟩ := h
  obtain ⟨𝓗', h1, h2, h3⟩ := refine_family hdisj (fun F => F ⊆ U ∧ Lev G d L (k + 1) F)
    (a := 1 / Real.log L) (fun H hH => by
      obtain ⟨𝓕, f1, f2, f3⟩ := refine_member hd hLd hL hdeg hk (hmem H hH).1 (hmem H hH).2
      exact ⟨𝓕, f1, fun F hF => ⟨(f2 F hF).1, (f2 F hF).1.trans (hmem H hH).1, (f2 F hF).2⟩,
        f3⟩)
  refine ⟨𝓗', h1, fun F hF => ?_, ?_⟩
  · obtain ⟨H, -, -, hQ⟩ := h2 F hF
    exact hQ
  · set a := 1 / Real.log L
    have ha0 : 0 ≤ a := by positivity
    have ha1 : a ≤ 1 := by
      simp only [a]; rw [div_le_one (by linarith)]; linarith
    have e1 : (1 - a) * ((1 - (k + 1) * a) * U.card) ≤ (1 - a) * (cover 𝓗).card := by
      refine mul_le_mul_of_nonneg_left ?_ (by linarith)
      have : (1 - ((k : ℝ) + 1) / Real.log L) = 1 - (k + 1) * a := by simp only [a]; ring
      rw [← this]; exact hcov
    have e2 : 0 ≤ ((k : ℝ) + 1) * a * a * U.card := by positivity
    have : (1 - (((k + 1 : ℕ) : ℝ) + 1) / Real.log L) = 1 - (k + 2) * a := by
      simp only [a]; push_cast; ring
    rw [this]
    nlinarith

end

end Lovasz
