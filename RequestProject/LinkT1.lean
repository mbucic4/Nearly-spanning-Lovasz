module
public import RequestProject.LinkConnect

/-!
# From well-expanding sets to all sets (the second half of Corollary 5.6)

If every set `S` that expands well (`|N(S)| ≥ E |S|`) reaches `θ` allowed vertices whenever
`|Z| ≤ |S|`, then every set `S` of moderate size reaches `θ` allowed vertices whenever
`D |Z| ≤ |S|`: either `S` itself expands well (Proposition 5.2 (a)), or many vertices have at
least `D` neighbours in `S`, and a random subset of `S` of density `1/D`, padded if necessary,
expands well and is at least as large as `Z`.
-/

@[expose] public section


open scoped BigOperators
open Classical

namespace Lovasz

noncomputable section

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

omit [Fintype V] in
lemma pex_ite_ppr {ι κ : Type*} [Fintype ι] [Fintype κ] (μ : ι → κ → ℝ)
    (P : (ι → κ) → Prop) (inst : DecidablePred P) :
    pex μ (fun x => @ite _ (P x) (inst x) (1 : ℝ) 0) = ppr μ P := by
  unfold ppr; congr 1; funext x; by_cases h : P x <;> simp [h]

lemma pex_cntT {q : ℝ} (S : Finset V) :
    pex (fun _ : V => bern q) (fun x => (cntT S x : ℝ)) = q * S.card := by
  have hμ := fun (h0 : 0 ≤ q) (h1 : q ≤ 1) => isPD_bern (ι := V) h0 h1
  have e : (fun x : V → Bool => (cntT S x : ℝ)) =
      fun x => ∑ i ∈ S, (if x i = true then (1 : ℝ) else 0) := by
    funext x
    simp only [cntT, Finset.card_filter]
    push_cast; rfl
  rw [e, pex_sum]
  have hi : ∀ i : V, pex (fun _ : V => bern q) (fun x => if x i = true then (1 : ℝ) else 0) = q := by
    intro i
    have h1 := ppr_none_true (q := q) ({i} : Finset V)
    have h2 : ∀ x : V → Bool, (if x i = true then (1 : ℝ) else 0) =
        1 - (if (∀ j ∈ ({i} : Finset V), x j = false) then 1 else 0) := by
      intro x
      cases h : x i <;> simp [h]
    simp only [h2]
    rw [pex_sub]
    rw [pex_ite_ppr, h1, Finset.card_singleton]
    unfold pex pwt
    simp only [mul_one]
    rw [← Fintype.prod_sum (fun _ k => bern q k)]
    simp [bern]
  simp only [hi, Finset.sum_const, nsmul_eq_mul]
  ring

lemma one_sub_inv_pow_le {d : ℝ} (hd : 1 ≤ d) {n : ℕ} (hn : d ≤ n) :
    (1 - 1 / d) ^ n ≤ Real.exp (-1) := by
  have h0 : 0 ≤ 1 - 1 / d := by
    have : 1 / d ≤ 1 := by rw [div_le_one (by linarith)]; exact hd
    linarith
  have h1 : 1 - 1 / d ≤ Real.exp (-(1 / d)) := by
    have := Real.add_one_le_exp (-(1 / d)); linarith
  calc (1 - 1 / d) ^ n ≤ Real.exp (-(1 / d)) ^ n := pow_le_pow_left₀ h0 h1 n
    _ = Real.exp (-(n / d)) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ Real.exp (-1) := Real.exp_le_exp.2 (by
      rw [neg_le_neg_iff, le_div_iff₀ (by linarith)]; linarith)

/-- A random subset of `S` of density `1/d` is small on average and leaves few vertices of `W`
uncovered, if every vertex of `W` has at least `d` neighbours in `S`. -/
lemma exists_sub_cover (S W : Finset V) {d E : ℝ} (hd : 1 ≤ d) (hWn : W.Nonempty)
    (hW : ∀ w ∈ W, d ≤ nbCnt G S w) :
    ∃ S' ⊆ S, E * S'.card + (W.filter (fun w => ∀ u ∈ S', ¬ G.Adj w u)).card <
      E * S.card / d + 0.3679 * W.card := by
  have hq0 : 0 ≤ 1 / d := by positivity
  have hq1 : 1 / d ≤ 1 := by rw [div_le_one (by linarith)]; exact hd
  have hμ := isPD_bern (ι := V) hq0 hq1
  set f : (V → Bool) → ℝ := fun x => E * cntT S x +
    ∑ w ∈ W, (if (∀ u ∈ S.filter (G.Adj w), x u = false) then (1 : ℝ) else 0)
  have hpex : pex (fun _ : V => bern (1 / d)) f < E * S.card / d + 0.3679 * W.card := by
    simp only [f]
    rw [pex_add, pex_const_mul, pex_cntT, pex_sum]
    have h1 : ∀ w ∈ W, pex (fun _ : V => bern (1 / d))
        (fun x => if (∀ u ∈ S.filter (G.Adj w), x u = false) then (1 : ℝ) else 0) ≤
          Real.exp (-1) := by
      intro w hw
      rw [pex_ite_ppr, ppr_none_true]
      exact one_sub_inv_pow_le hd (hW w hw)
    have h2 := Finset.sum_le_sum h1
    rw [Finset.sum_const, nsmul_eq_mul] at h2
    have he := exp_neg_one_bounds
    have hW0 : (0 : ℝ) < W.card := by exact_mod_cast hWn.card_pos
    have : Real.exp (-1) * W.card < 0.3679 * W.card := mul_lt_mul_of_pos_right he.2 hW0
    have : E * (1 / d * S.card) = E * S.card / d := by ring
    linarith
  obtain ⟨x, hx⟩ := exists_lt_of_pex_lt hμ hpex
  refine ⟨S.filter (fun u => x u = true), Finset.filter_subset _ _, lt_of_le_of_lt ?_ hx⟩
  simp only [f, cntT]
  have : ((W.filter (fun w => ∀ u ∈ S.filter (fun u => x u = true), ¬ G.Adj w u)).card : ℝ) ≤
      ∑ w ∈ W, (if (∀ u ∈ S.filter (G.Adj w), x u = false) then (1 : ℝ) else 0) := by
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_le_sum fun w _ => ?_
    split_ifs with h1 h2 <;> try norm_num
    exact h2 fun u hu => by
      obtain ⟨huS, hadj⟩ := Finset.mem_filter.1 hu
      by_contra hxu
      exact h1 u (Finset.mem_filter.2 ⟨huS, by simpa using hxu⟩) hadj
  linarith

/-- The hypothesis of Corollary 5.6 for well-expanding sets. -/
def GoodEProp (G : SimpleGraph V) (U : Finset V) (y : V → Bool) (θ E : ℝ) (ρ : ℕ) : Prop :=
  ∀ S ⊆ U, ∀ Z ⊆ U, S.Nonempty → 3 * S.card ≤ 2 * U.card → Z.card ≤ S.card →
    E * S.card ≤ (extNb G U S ∅).card → θ ≤ (ballY G U Z y ρ S).card

omit [Fintype V] in
lemma extNb_sdiff_sub (U S P : Finset V) :
    extNb G U S ∅ \ P ⊆ extNb G U (S ∪ P) ∅ := by
  intro v hv
  obtain ⟨hv1, hvP⟩ := Finset.mem_sdiff.1 hv
  simp only [extNb, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_union] at hv1 ⊢
  obtain ⟨⟨hvU, hvS⟩, u, hu, hadj, hF⟩ := hv1
  exact ⟨⟨hvU, not_or.2 ⟨hvS, hvP⟩⟩, u, Or.inl hu, hadj, hF⟩

/-- **Corollary 5.6, deterministic part**: (T1) follows from the property for well-expanding
sets. -/
theorem t1_of_goodE {U : Finset V} {y : V → Bool} {c : ℕ} {s θ E D : ℝ} {ρ : ℕ}
    (hexp : IsExpander G U (1 / 16) c s) (hgood : GoodEProp G U y θ E ρ)
    (hE : 0 ≤ E) (hK : 0 < Real.log U.card ^ c) (hDs : 2 * D * E ≤ s)
    (hDE : 100 * (E + 1) * Real.log U.card ^ c ≤ D) (hD1 : 1 ≤ D) :
    T1Prop G U y θ D ρ := by
  set K := Real.log U.card ^ c
  intro S hSU Z hZU hS1 hS2 hDZ
  have hS1' : (1 : ℝ) ≤ S.card := by exact_mod_cast hS1
  have hZS : (Z.card : ℝ) ≤ S.card := by
    have : (Z.card : ℝ) ≤ D * Z.card := le_mul_of_one_le_left (by positivity) hD1
    linarith
  have hs0 : 0 ≤ s := le_trans (by positivity) hDs
  rcases highNb_large hexp hSU hS1 hS2 (by linarith : 0 < D) hs0 with ha | hb
  · -- `S` expands well
    refine hgood S hSU Z hZU (Finset.card_pos.1 (by omega)) hS2 (by exact_mod_cast hZS) ?_
    have : 2 * D * (E * S.card) ≤ 2 * D * (extNb G U S ∅).card := by
      have : 2 * D * E * S.card ≤ s * S.card := mul_le_mul_of_nonneg_right hDs (by positivity)
      nlinarith
    exact le_of_mul_le_mul_left this (by linarith)
  · -- many vertices have at least `D` neighbours in `S`
    set W := highNb G U S D
    have hWc : S.card / (16 * K) ≤ W.card := by
      have : 1 / 16 / K * S.card = S.card / (16 * K) := by field_simp
      linarith
    have hWn : W.Nonempty := by
      rw [← Finset.card_pos]
      have : (0 : ℝ) < S.card / (16 * K) := by positivity
      exact_mod_cast this.trans_le hWc
    obtain ⟨S', hS'S, hS'⟩ := exists_sub_cover (G := G) S W hD1 (E := E) hWn
      (fun w hw => (Finset.mem_filter.1 hw).2)
    -- the covered part of `W` lies in `N(S')`
    have hcov : W.card - (W.filter (fun w => ∀ u ∈ S', ¬ G.Adj w u)).card ≤
        (extNb G U S' ∅).card := by
      have hsub : W \ W.filter (fun w => ∀ u ∈ S', ¬ G.Adj w u) ⊆ extNb G U S' ∅ := by
        intro w hw
        obtain ⟨hwW, hwn⟩ := Finset.mem_sdiff.1 hw
        simp only [Finset.mem_filter, not_and, not_forall, not_not] at hwn
        obtain ⟨u, hu, hadj⟩ := hwn hwW
        simp only [W, highNb, Finset.mem_filter, Finset.mem_sdiff] at hwW
        simp only [extNb, Finset.mem_filter, Finset.mem_sdiff]
        exact ⟨⟨hwW.1.1, fun h => hwW.1.2 (hS'S h)⟩, u, hu, hadj.symm, Finset.notMem_empty _⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_sdiff_of_subset (Finset.filter_subset _ _)] at this
      omega
    have hcov' : (W.card : ℝ) - (W.filter (fun w => ∀ u ∈ S', ¬ G.Adj w u)).card ≤
        (extNb G U S' ∅).card := by
      have hle := Finset.card_le_card (Finset.filter_subset (fun w => ∀ u ∈ S', ¬ G.Adj w u) W)
      have h1 : (((W.card - (W.filter (fun w => ∀ u ∈ S', ¬ G.Adj w u)).card : ℕ)) : ℝ) ≤
          (extNb G U S' ∅).card := by exact_mod_cast hcov
      rw [Nat.cast_sub hle] at h1
      exact h1
    -- the excess of `S'`
    have hED : E * S.card / D ≤ 0.01 * (S.card / K) := by
      rw [← mul_div_assoc, div_le_div_iff₀ (by linarith) hK]
      have : E * K ≤ 0.01 * D := by nlinarith
      have hS0 : (0 : ℝ) ≤ S.card := by positivity
      have := mul_le_mul_of_nonneg_left this hS0
      linarith
    have hE1D : (E + 1) * S.card / D ≤ 0.01 * (S.card / K) := by
      rw [← mul_div_assoc, div_le_div_iff₀ (by linarith) hK]
      have : (E + 1) * K ≤ 0.01 * D := by nlinarith
      have hS0 : (0 : ℝ) ≤ S.card := by positivity
      have := mul_le_mul_of_nonneg_left this hS0
      linarith
    have hexc : 0.0295 * (S.card / K) < (extNb G U S' ∅).card - E * S'.card := by
      have : 0.632 * W.card ≥ 0.632 * (S.card / (16 * K)) := by linarith
      have e : 0.632 * (S.card / (16 * K)) = 0.0395 * (S.card / K) := by field_simp; ring
      have : (0 : ℝ) ≤ S.card / (16 * K) := by positivity
      linarith
    -- padding
    have hZS' : Z.card ≤ S.card := by exact_mod_cast hZS
    obtain ⟨P, hPS, hPc⟩ := Finset.exists_subset_card_eq
      (show Z.card - S'.card ≤ (S \ S').card by
        rw [Finset.card_sdiff_of_subset hS'S]; omega)
    set S'' := S' ∪ P
    have hdisj : Disjoint S' P := Finset.disjoint_of_subset_right hPS Finset.disjoint_sdiff
    have hS''c : S''.card = S'.card + (Z.card - S'.card) := by
      rw [Finset.card_union_of_disjoint hdisj, hPc]
    have hS''S : S'' ⊆ S := Finset.union_subset hS'S (hPS.trans Finset.sdiff_subset)
    have hPZ : ((Z.card - S'.card : ℕ) : ℝ) ≤ Z.card := by exact_mod_cast Nat.sub_le _ _
    have hZD : (Z.card : ℝ) ≤ S.card / D := by rw [le_div_iff₀ (by linarith)]; linarith
    have hN'' : ((extNb G U S' ∅).card : ℝ) - (Z.card - S'.card : ℕ) ≤ (extNb G U S'' ∅).card := by
      have h1 := Finset.card_le_card (extNb_sdiff_sub (G := G) U S' P)
      have h2 := Finset.le_card_sdiff P (extNb G U S' ∅)
      rw [hPc] at h2
      have h3 : (extNb G U S' ∅).card ≤ (extNb G U S' ∅ \ P).card + (Z.card - S'.card) := by
        omega
      have : ((extNb G U S' ∅).card : ℝ) - (Z.card - S'.card : ℕ) ≤
          (extNb G U S' ∅ \ P).card := by
        have : ((extNb G U S' ∅).card : ℝ) ≤ (extNb G U S' ∅ \ P).card + (Z.card - S'.card : ℕ) := by
          exact_mod_cast h3
        linarith
      exact this.trans (by exact_mod_cast h1)
    have hS''pos : 0 < S''.card := by
      by_contra h0
      push_neg at h0
      have h0' : S'.card = 0 := by omega
      have hS'e : S' = ∅ := Finset.card_eq_zero.1 h0'
      have : (extNb G U S' ∅).card = 0 := by
        rw [hS'e]; simp [extNb]
      rw [this, h0'] at hexc
      push_cast at hexc
      have : 0 ≤ 0.0295 * ((S.card : ℝ) / K) := by positivity
      linarith
    have hgoodS : E * S''.card ≤ (extNb G U S'' ∅).card := by
      rw [hS''c]; push_cast
      have hE1 : (E + 1) * ((Z.card - S'.card : ℕ) : ℝ) ≤ 0.01 * (S.card / K) := by
        have : (E + 1) * ((Z.card - S'.card : ℕ) : ℝ) ≤ (E + 1) * (S.card / D) :=
          mul_le_mul_of_nonneg_left (hPZ.trans hZD) (by linarith)
        have e : (E + 1) * (S.card / D) = (E + 1) * S.card / D := by ring
        linarith
      have : 0 ≤ 0.0195 * ((S.card : ℝ) / K) := by positivity
      linarith
    have hb := hgood S'' (hS''S.trans hSU) Z hZU (Finset.card_pos.1 hS''pos)
      (le_trans (by have := Finset.card_le_card hS''S; omega) hS2) (by omega) hgoodS
    exact hb.trans (Nat.cast_le.2 (Finset.card_le_card (ballY_mono_S hS''S)))

end

end Lovasz
