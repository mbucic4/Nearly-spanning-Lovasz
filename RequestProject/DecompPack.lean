module
public import RequestProject.DecompOne

/-!
# Packing with `λ`-expanders (Lemmas 4.6 and 4.4 of the cited work on sublinear expanders)
-/

@[expose] public section


open scoped BigOperators
open Classical

namespace Lovasz

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

/-- A packing of `S`: pairwise disjoint pieces inside `S`, each a `λ`-expander with minimum degree
at least half its average degree and with average degree at least `d (1 - e)`. -/
def IsPacking (S : Finset V) (lam e d : ℝ) (𝒞 : Finset (Finset V)) : Prop :=
  (𝒞 : Set (Finset V)).PairwiseDisjoint id ∧
    ∀ W ∈ 𝒞, W ⊆ S ∧ GoodPiece G W lam ∧ d * (1 - e) * W.card ≤ dsum G W

/-- The vertices covered by a family of sets. -/
def cover (𝒞 : Finset (Finset V)) : Finset V := 𝒞.biUnion id

variable {G}

lemma mem_cover {𝒞 : Finset (Finset V)} {W : Finset V} {v : V} (hW : W ∈ 𝒞) (hv : v ∈ W) :
    v ∈ cover 𝒞 :=
  Finset.mem_biUnion.2 ⟨W, hW, hv⟩

lemma IsPacking.mono {S : Finset V} {lam e e' d : ℝ} {𝒞 : Finset (Finset V)}
    (h : IsPacking G S lam e d 𝒞) (hd : 0 ≤ d) (he : e ≤ e') : IsPacking G S lam e' d 𝒞 := by
  refine ⟨h.1, fun W hW => ⟨(h.2 W hW).1, (h.2 W hW).2.1, le_trans ?_ (h.2 W hW).2.2⟩⟩
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hd)
    (Nat.cast_nonneg _)

lemma cover_subset {S : Finset V} {lam e d : ℝ} {𝒞 : Finset (Finset V)}
    (h : IsPacking G S lam e d 𝒞) : cover 𝒞 ⊆ S := by
  intro v hv
  obtain ⟨W, hW, hvW⟩ := Finset.mem_biUnion.1 hv
  exact (h.2 W hW).1 hvW

lemma card_cover {S : Finset V} {lam e d : ℝ} {𝒞 : Finset (Finset V)}
    (h : IsPacking G S lam e d 𝒞) : (cover 𝒞).card = ∑ W ∈ 𝒞, W.card :=
  card_biUnion_eq h.1

lemma dsum_cover_ge {S : Finset V} {lam e d : ℝ} {𝒞 : Finset (Finset V)}
    (h : IsPacking G S lam e d 𝒞) : ∑ W ∈ 𝒞, dsum G W ≤ dsum G (cover 𝒞) :=
  sum_dsum_le h.1 fun _ hW _ hv => mem_cover hW hv

/-- The degree sum of the complement of `T ⊆ S`. -/
lemma dsum_sdiff_ge {S T : Finset V} (hT : T ⊆ S) {d : ℝ}
    (hdeg : ∀ v ∈ S, (degIn G S v : ℝ) ≤ d) :
    (dsum G S : ℝ) + dsum G T - 2 * d * T.card ≤ dsum G (S \ T) := by
  have hs := dsum_split (G := G) hT
  have h1 : ∑ v ∈ T, degIn G S v = dsum G T + eCut G T (S \ T) := by
    rw [eCut_eq_sum, dsum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => degIn_split hT v
  have h2 : (∑ v ∈ T, (degIn G S v : ℝ)) ≤ d * T.card := by
    calc (∑ v ∈ T, (degIn G S v : ℝ)) ≤ ∑ v ∈ T, d := Finset.sum_le_sum fun v hv => hdeg v (hT hv)
      _ = d * T.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hs' : (dsum G S : ℝ) = dsum G T + dsum G (S \ T) + 2 * eCut G T (S \ T) := by
    exact_mod_cast hs
  have h1' : (∑ v ∈ T, (degIn G S v : ℝ)) = dsum G T + eCut G T (S \ T) := by
    exact_mod_cast h1
  linarith

lemma degIn_le_of_subset {S R : Finset V} (hR : R ⊆ S) {d : ℝ}
    (hdeg : ∀ v ∈ S, (degIn G S v : ℝ) ≤ d) : ∀ v ∈ R, (degIn G R v : ℝ) ≤ d :=
  fun v hv => le_trans (by exact_mod_cast degIn_mono hR v) (hdeg v (hR hv))

/-- Adding a packing of the uncovered part to a packing. -/
lemma IsPacking.union {S : Finset V} {lam e d : ℝ} {𝒞 𝒟 : Finset (Finset V)}
    (h𝒞 : IsPacking G S lam e d 𝒞) (h𝒟 : IsPacking G (S \ cover 𝒞) lam e d 𝒟) :
    IsPacking G S lam e d (𝒞 ∪ 𝒟) ∧ Disjoint 𝒞 𝒟 ∧
      cover (𝒞 ∪ 𝒟) = cover 𝒞 ∪ cover 𝒟 ∧ Disjoint (cover 𝒞) (cover 𝒟) := by
  have hdisjC : Disjoint (cover 𝒞) (cover 𝒟) :=
    Finset.disjoint_of_subset_right (cover_subset h𝒟) Finset.disjoint_sdiff
  have hWD : ∀ W ∈ 𝒞, ∀ W' ∈ 𝒟, Disjoint W W' := by
    intro W hW W' hW'
    refine Finset.disjoint_of_subset_left (fun v hv => mem_cover hW hv) ?_
    exact Finset.disjoint_of_subset_right (fun v hv => mem_cover hW' hv) hdisjC
  have hdisj : Disjoint 𝒞 𝒟 := by
    rw [Finset.disjoint_left]
    intro W hW hW'
    obtain ⟨v, hv⟩ := (h𝒞.2 W hW).2.1.1
    exact Finset.disjoint_left.1 (hWD W hW W hW') hv hv
  have hcov : cover (𝒞 ∪ 𝒟) = cover 𝒞 ∪ cover 𝒟 := by
    ext v; simp only [cover, Finset.mem_biUnion, Finset.mem_union, id]
    constructor
    · rintro ⟨W, hW | hW, hv⟩
      · exact Or.inl ⟨W, hW, hv⟩
      · exact Or.inr ⟨W, hW, hv⟩
    · rintro (⟨W, hW, hv⟩ | ⟨W, hW, hv⟩)
      · exact ⟨W, Or.inl hW, hv⟩
      · exact ⟨W, Or.inr hW, hv⟩
  refine ⟨⟨?_, ?_⟩, hdisj, hcov, hdisjC⟩
  · rw [Finset.coe_union]
    refine Set.PairwiseDisjoint.union h𝒞.1 h𝒟.1 ?_
    intro W hW W' hW' _
    exact hWD W hW W' hW'
  · intro W hW
    rcases Finset.mem_union.1 hW with hW | hW
    · exact h𝒞.2 W hW
    · obtain ⟨h1, h2, h3⟩ := h𝒟.2 W hW
      exact ⟨h1.trans Finset.sdiff_subset, h2, h3⟩

/-- **Lemma 4.6** (of the cited work): a nearly regular graph can be packed with `λ`-expanders of
nearly the same average degree covering at least a quarter of its vertices. -/
theorem pack_quarter {S : Finset V} {d ε lam : ℝ} (hd : 0 ≤ d) (hε : 0 ≤ ε) (hl0 : 0 ≤ lam)
    (hl1 : lam ≤ 1 / 2) (hlS : lam * Real.log S.card ≤ 1 / 3) (hlε : lam * Real.log S.card ≤ ε)
    (hdeg : ∀ v ∈ S, (degIn G S v : ℝ) ≤ d) (havg : d * (1 - ε) * S.card ≤ dsum G S) :
    ∃ 𝒞, IsPacking G S lam (8 * ε) d 𝒞 ∧ S.card ≤ 4 * (cover 𝒞).card := by
  set Pk := (S.powerset.powerset).filter (IsPacking G S lam (8 * ε) d)
  have hPk : Pk.Nonempty := ⟨∅, Finset.mem_filter.2 ⟨Finset.empty_mem_powerset _,
    by simp [IsPacking]⟩⟩
  obtain ⟨𝒞, h𝒞mem, hmax⟩ := Finset.exists_max_image Pk (fun 𝒞 => (cover 𝒞).card) hPk
  have h𝒞 := (Finset.mem_filter.1 h𝒞mem).2
  refine ⟨𝒞, h𝒞, ?_⟩
  by_contra hlt
  push_neg at hlt
  set T := cover 𝒞
  have hTS : T ⊆ S := cover_subset h𝒞
  set R := S \ T
  have hRT : R.card + T.card = S.card := Finset.card_sdiff_add_card_eq_card hTS
  have hRne : R.Nonempty := by rw [← Finset.card_pos]; omega
  have hR0 : (0 : ℝ) < R.card := by exact_mod_cast hRne.card_pos
  -- the degree sum of `T`
  have hdT : d * (1 - 8 * ε) * T.card ≤ dsum G T := by
    have h1 := dsum_cover_ge h𝒞
    have h2 : d * (1 - 8 * ε) * T.card = ∑ W ∈ 𝒞, d * (1 - 8 * ε) * W.card := by
      rw [card_cover h𝒞, Nat.cast_sum, Finset.mul_sum]
    rw [h2]
    refine le_trans (Finset.sum_le_sum fun W hW => (h𝒞.2 W hW).2.2) ?_
    exact_mod_cast h1
  have hR : (dsum G S : ℝ) + dsum G T - 2 * d * T.card ≤ dsum G R := dsum_sdiff_ge hTS hdeg
  have hc : (R.card : ℝ) + T.card = S.card := by exact_mod_cast hRT
  have hlt' : 4 * (T.card : ℝ) < S.card := by exact_mod_cast hlt
  have hRavg : d * (1 - 4 * ε) ≤ avgDeg G R := by
    rw [avgDeg, le_div_iff₀ hR0]
    have hεd : 0 ≤ ε * d := mul_nonneg hε hd
    have := mul_nonneg hεd (show (0 : ℝ) ≤ 4 * R.card - S.card - 8 * T.card by linarith)
    nlinarith
  -- a new expander in `R`
  have hl1' : lam ≤ 1 / 2 := hl1
  obtain ⟨H, hHR, hH, hHavg⟩ := exists_lamExp (G := G) hRne hl0 hl1'
  have hlogR : Real.log R.card ≤ Real.log S.card :=
    Real.log_le_log hR0 (by exact_mod_cast Finset.card_le_card Finset.sdiff_subset)
  have hlogR0 : 0 ≤ Real.log R.card := Real.log_nonneg (by exact_mod_cast hRne.card_pos)
  set x := 3 * lam * Real.log R.card
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by nlinarith
  have hx2 : x ≤ 3 * ε := by nlinarith
  have hHavg' : d * (1 - 8 * ε) ≤ avgDeg G H := by
    have e1 : d * (1 - 4 * ε) * (1 - x) ≤ avgDeg G R * (1 - x) :=
      mul_le_mul_of_nonneg_right hRavg (by linarith)
    have e2 : 0 ≤ d * (4 * ε) * x := by positivity
    nlinarith
  have hHne := hH.1
  have hdsumH : d * (1 - 8 * ε) * H.card ≤ dsum G H := by
    rw [← avgDeg_mul_card hHne]
    exact mul_le_mul_of_nonneg_right hHavg' (Nat.cast_nonneg _)
  have h𝒟 : IsPacking G R lam (8 * ε) d {H} := by
    refine ⟨by simp, fun W hW => ?_⟩
    rw [Finset.mem_singleton] at hW
    subst hW
    exact ⟨hHR, hH, hdsumH⟩
  obtain ⟨hU, -, hcov, hdisj⟩ := h𝒞.union h𝒟
  have hmem : 𝒞 ∪ {H} ∈ Pk := by
    refine Finset.mem_filter.2 ⟨?_, hU⟩
    rw [Finset.mem_powerset]
    intro W hW
    exact Finset.mem_powerset.2 (hU.2 W hW).1
  have h1 := hmax _ hmem
  rw [hcov, Finset.card_union_of_disjoint hdisj] at h1
  have h2 : (cover {H}).card = H.card := by simp [cover]
  have h3 : (cover 𝒞).card = T.card := rfl
  have := hHne.card_pos
  omega

lemma pack_num (i : ℕ) : (8 : ℝ) * (16 ^ i * (4 / 3) ^ (i + 1)) ≤ 32 ^ (i + 1) := by
  have e1 : (64 / 3 : ℝ) ^ i = 16 ^ i * (4 / 3) ^ i := by rw [← mul_pow]; norm_num
  have e2 : (64 / 3 : ℝ) ^ i ≤ 32 ^ i := pow_le_pow_left₀ (by norm_num) (by norm_num) i
  rw [pow_succ, pow_succ]
  calc (8 : ℝ) * (16 ^ i * ((4 / 3) ^ i * (4 / 3))) = 32 / 3 * (64 / 3 : ℝ) ^ i := by
        rw [e1]; ring
    _ ≤ 32 / 3 * 32 ^ i := mul_le_mul_of_nonneg_left e2 (by norm_num)
    _ ≤ 32 ^ i * 32 := by linarith [pow_nonneg (show (0 : ℝ) ≤ 32 by norm_num) i]

/-- One stage of the iteration proving Lemma 4.4. -/
lemma pack_stage {S : Finset V} {d ε lam : ℝ} (hd : 0 ≤ d) (hε : 0 ≤ ε) (hl0 : 0 ≤ lam)
    (hl1 : lam ≤ 1 / 2) (hlS : lam * Real.log S.card ≤ 1 / 3) (hlε : lam * Real.log S.card ≤ ε)
    (hdeg : ∀ v ∈ S, (degIn G S v : ℝ) ≤ d) (havg : d * (1 - ε) * S.card ≤ dsum G S) :
    ∀ i : ℕ, ∃ 𝒞, IsPacking G S lam (32 ^ i * ε) d 𝒞 ∧
      (S.card : ℝ) - (cover 𝒞).card ≤ (3 / 4) ^ i * S.card ∧
      ∑ W ∈ 𝒞, (d * W.card - dsum G W) ≤ (16 ^ i - 1) * ε * d * S.card := by
  intro i
  induction i with
  | zero =>
    refine ⟨∅, ⟨by simp, by simp⟩, by simp, by simp⟩
  | succ i ih =>
    obtain ⟨𝒞, h𝒞, hcovi, hdef⟩ := ih
    have h32 : (32 : ℝ) ^ i * ε ≤ 32 ^ (i + 1) * ε := by
      have : (32 : ℝ) ^ i ≤ 32 ^ (i + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      nlinarith
    have h16 : (16 : ℝ) ^ i ≤ 16 ^ (i + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hεdS : 0 ≤ ε * d * S.card := by positivity
    set T := cover 𝒞
    have hTS : T ⊆ S := cover_subset h𝒞
    set R := S \ T
    have hRT : R.card + T.card = S.card := Finset.card_sdiff_add_card_eq_card hTS
    have hc : (R.card : ℝ) + T.card = S.card := by exact_mod_cast hRT
    have hq : (0 : ℝ) < (3 / 4) ^ (i + 1) := by positivity
    by_cases hsmall : (R.card : ℝ) ≤ (3 / 4) ^ (i + 1) * S.card
    · refine ⟨𝒞, h𝒞.mono hd h32, by linarith, le_trans hdef ?_⟩
      nlinarith
    push_neg at hsmall
    have hRne : R.Nonempty := by
      rw [← Finset.card_pos]
      have : (0 : ℝ) < R.card := lt_of_le_of_lt (by positivity) hsmall
      exact_mod_cast this
    have hR0 : (0 : ℝ) < R.card := by exact_mod_cast hRne.card_pos
    -- regularity of the uncovered part
    set D := ∑ W ∈ 𝒞, (d * W.card - dsum G W)
    have hdT : d * T.card - D ≤ dsum G T := by
      have h1 := dsum_cover_ge h𝒞
      have hTc : (T.card : ℝ) = ∑ W ∈ 𝒞, (W.card : ℝ) := by
        simp only [T]; rw [card_cover h𝒞, Nat.cast_sum]
      have h2 : d * T.card - D = ∑ W ∈ 𝒞, (dsum G W : ℝ) := by
        rw [hTc, Finset.mul_sum]; simp only [D]; rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun W _ => by ring
      rw [h2]; exact_mod_cast h1
    have hRd := dsum_sdiff_ge hTS hdeg
    obtain ⟨e', he'⟩ : ∃ e' : ℝ, e' = ε * 16 ^ i * (4 / 3) ^ (i + 1) := ⟨_, rfl⟩
    have hq43 : (3 / 4 : ℝ) ^ (i + 1) * (4 / 3) ^ (i + 1) = 1 := by
      rw [← mul_pow]; norm_num
    have hSR : (S.card : ℝ) ≤ (4 / 3) ^ (i + 1) * R.card := by
      have : (3 / 4 : ℝ) ^ (i + 1) * S.card * (4 / 3) ^ (i + 1) ≤ R.card * (4 / 3) ^ (i + 1) :=
        mul_le_mul_of_nonneg_right hsmall.le (by positivity)
      nlinarith
    have hRavg : d * (1 - e') * R.card ≤ dsum G R := by
      have : ε * d * 16 ^ i * S.card ≤ ε * d * 16 ^ i * ((4 / 3) ^ (i + 1) * R.card) :=
        mul_le_mul_of_nonneg_left hSR (by positivity)
      rw [he']
      nlinarith
    have hone : (1 : ℝ) ≤ 16 ^ i * (4 / 3) ^ (i + 1) :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num))
    have hεe' : ε ≤ e' := by rw [he']; nlinarith
    have he'0 : 0 ≤ e' := le_trans hε hεe'
    have hlogR : Real.log R.card ≤ Real.log S.card :=
      Real.log_le_log hR0 (by exact_mod_cast Finset.card_le_card Finset.sdiff_subset)
    have hlogR0 : 0 ≤ Real.log R.card := Real.log_nonneg (by exact_mod_cast hRne.card_pos)
    have hlRS : lam * Real.log R.card ≤ lam * Real.log S.card :=
      mul_le_mul_of_nonneg_left hlogR hl0
    have hdegR : ∀ v ∈ R, (degIn G R v : ℝ) ≤ d := degIn_le_of_subset Finset.sdiff_subset hdeg
    obtain ⟨𝒟, h𝒟, h𝒟cov⟩ := pack_quarter (G := G) (S := R) hd (by linarith) hl0 hl1
      (by linarith) (by linarith) hdegR hRavg
    have h8 : 8 * e' ≤ 32 ^ (i + 1) * ε := by
      have := mul_le_mul_of_nonneg_left (pack_num i) hε
      rw [he']
      linarith
    obtain ⟨hU, hdisj, hcov, hdisjc⟩ := (h𝒞.mono hd h32).union (h𝒟.mono hd h8)
    refine ⟨𝒞 ∪ 𝒟, hU, ?_, ?_⟩
    · rw [hcov, Finset.card_union_of_disjoint hdisjc]
      have : (R.card : ℝ) ≤ 4 * (cover 𝒟).card := by exact_mod_cast h𝒟cov
      push_cast
      have : (R.card : ℝ) ≤ (3 / 4) ^ i * S.card := by linarith
      rw [pow_succ]
      linarith
    · rw [Finset.sum_union hdisj]
      have hD' : ∑ W ∈ 𝒟, (d * W.card - dsum G W) ≤ 8 * e' * d * R.card := by
        calc ∑ W ∈ 𝒟, (d * W.card - dsum G W) ≤ ∑ W ∈ 𝒟, 8 * e' * d * W.card := by
              refine Finset.sum_le_sum fun W hW => ?_
              have := (h𝒟.2 W hW).2.2
              linarith
          _ = 8 * e' * d * (cover 𝒟).card := by
              rw [card_cover h𝒟, Nat.cast_sum, Finset.mul_sum]
          _ ≤ 8 * e' * d * R.card := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (mul_nonneg (by norm_num) he'0) hd)
              exact_mod_cast Finset.card_le_card (cover_subset h𝒟)
      have hRi : (R.card : ℝ) ≤ (3 / 4) ^ i * S.card := by linarith
      have hkey : 8 * e' * d * R.card ≤ 32 / 3 * 16 ^ i * ε * d * S.card := by
        have e1 : 8 * e' * d * R.card ≤ 8 * e' * d * ((3 / 4) ^ i * S.card) :=
          mul_le_mul_of_nonneg_left hRi (mul_nonneg (mul_nonneg (by norm_num) he'0) hd)
        have e2 : 8 * e' * d * ((3 / 4) ^ i * S.card) = 32 / 3 * 16 ^ i * ε * d * S.card := by
          rw [he']
          have : (4 / 3 : ℝ) ^ (i + 1) * (3 / 4) ^ i = 4 / 3 := by
            rw [pow_succ, mul_comm, ← mul_assoc, ← mul_pow]; norm_num
          calc 8 * (ε * 16 ^ i * (4 / 3) ^ (i + 1)) * d * ((3 / 4) ^ i * S.card)
              = 8 * ε * 16 ^ i * ((4 / 3) ^ (i + 1) * (3 / 4) ^ i) * d * S.card := by ring
            _ = _ := by rw [this]; ring
        linarith
      have : (16 : ℝ) ^ (i + 1) = 16 * 16 ^ i := by ring
      rw [this]
      have : 0 ≤ (16 : ℝ) ^ i * ε * d * S.card := by positivity
      linarith

/-- **Lemma 4.4** (of the cited work): a nearly regular graph on `n` vertices can be packed with
`λ`-expanders of average degree at least `d (1 - ε (log n)^28)` covering all but `n / log n` of
its vertices. -/
theorem pack_most {S : Finset V} {d ε lam : ℝ} (hd : 0 ≤ d) (hε : 0 ≤ ε) (hl0 : 0 ≤ lam)
    (hl1 : lam ≤ 1 / 2) (hlS : lam * Real.log S.card ≤ 1 / 3) (hlε : lam * Real.log S.card ≤ ε)
    (hS : 2 ≤ Real.log S.card)
    (hdeg : ∀ v ∈ S, (degIn G S v : ℝ) ≤ d) (havg : d * (1 - ε) * S.card ≤ dsum G S) :
    ∃ 𝒞, IsPacking G S lam (ε * Real.log S.card ^ 28) d 𝒞 ∧
      (1 - 1 / Real.log S.card) * S.card ≤ (cover 𝒞).card := by
  set L := Real.log S.card
  have hex : ∃ t : ℕ, L ≤ (4 / 3 : ℝ) ^ t := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt L (show (1 : ℝ) < 4 / 3 by norm_num)
    exact ⟨n, hn.le⟩
  set t := Nat.find hex
  have ht : L ≤ (4 / 3 : ℝ) ^ t := Nat.find_spec hex
  have h32 : (32 : ℝ) ^ t ≤ L ^ 28 := by
    rcases Nat.eq_zero_or_pos t with h0 | hpos
    · rw [h0, pow_zero]; exact one_le_pow₀ (by linarith)
    · have hlt : (4 / 3 : ℝ) ^ (t - 1) < L := by
        have := Nat.find_min hex (show t - 1 < t by omega)
        push_neg at this; exact this
      have e1 : (32 : ℝ) ^ t ≤ ((4 / 3) ^ 13) ^ t := pow_le_pow_left₀ (by norm_num) (by norm_num) t
      have e2 : ((4 / 3 : ℝ) ^ 13) ^ t = ((4 / 3) ^ (t - 1) * (4 / 3)) ^ 13 := by
        rw [← pow_succ, ← pow_mul, ← pow_mul, Nat.sub_add_cancel hpos, mul_comm]
      have e3 : ((4 / 3 : ℝ) ^ (t - 1) * (4 / 3)) ^ 13 ≤ (L * L) ^ 13 :=
        pow_le_pow_left₀ (by positivity)
          (mul_le_mul hlt.le (by linarith) (by norm_num) (by linarith)) 13
      have e4 : (L * L) ^ 13 ≤ L ^ 28 := by
        rw [← pow_two, ← pow_mul]
        exact pow_le_pow_right₀ (by linarith) (by norm_num)
      linarith
  obtain ⟨𝒞, h𝒞, hcov, -⟩ := pack_stage (G := G) hd hε hl0 hl1 hlS hlε hdeg havg t
  refine ⟨𝒞, h𝒞.mono hd (by nlinarith), ?_⟩
  have hq : (3 / 4 : ℝ) ^ t ≤ 1 / L := by
    rw [le_div_iff₀ (by linarith)]
    have : (3 / 4 : ℝ) ^ t * (4 / 3) ^ t = 1 := by rw [← mul_pow]; norm_num
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ 3 / 4 by norm_num) t]
  have hS0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  nlinarith

end

end Lovasz
