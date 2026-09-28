module
public import RequestProject.LinkingProb

/-!
# The linking lemma (Lemma 2.6): the probabilistic argument
-/

@[expose] public section


open scoped BigOperators
open Classical Filter

namespace Lovasz

noncomputable section

set_option maxHeartbeats 1000000 in
/-- The core of Lemma 2.6, for fixed numerical parameters. -/
theorem linking_core {ι : Type} [Fintype ι] {c N₀ Kc : ℕ} (hL : LinkingBody c N₀)
    {x E A r q D s : ℝ} (H : SimpleGraph ι) (U Vs : Finset ι) (hKc : 1 ≤ Kc)
    (hr : 0 < r) (hq : 0 < q) (hq1 : q < 1) (hcol : 10 * r + 3 * q ≤ 1)
    (hE : E ≤ 4 * D) (hmin : ∀ v ∈ U, D ≤ degIn H U v) (hmax : ∀ v ∈ U, (degIn H U v : ℝ) ≤ 4 * D)
    (hUx : (U.card : ℝ) ≤ x) (hexp : IsExpander H U (1 / 8) c s)
    (hs : E / (8 * Real.log x ^ c) ≤ s) (hVsU : Vs ⊆ U) (hVs : (Vs.card : ℝ) ≤ A)
    (n1 : A ≤ E / 128) (n2 : 13 ≤ E) (n3 : 4 * c * Real.log 2 ≤ Real.log (E / 4))
    (n4 : Real.log 2 ≤ Real.log (E / 4)) (n5 : 48 * Real.log x ^ c * A ≤ E / 4)
    (n6 : (N₀ : ℝ) ≤ E / 8)
    (n7 : 2 * Real.log x ^ (9 * c + 21) / (q / Kc) ^ 10 ≤ E / (8 * Real.log x ^ c))
    (n7' : 2 * Real.log x ^ (9 * c + 21) / (q / Kc) ^ 10 ≤ E / 64)
    (n8 : 100 * Real.log x ^ (7 * c + 19) / (q / Kc) ^ 6 ≤ 31 / 32 / (120 * r) - 1)
    (n9 : x * Real.exp (-(12 * r * E)) + x * Real.exp (2 * A - r * E / 13) +
      Real.exp (1 - r * E / 2) + 3 * (8 / E) ^ Kc ≤ x ^ (-3 : ℝ))
    (n10 : 4 ≤ r * E) (hx1 : 1 ≤ x) :
    1 - x ^ (-3 : ℝ) ≤ ppr (fun _ : ι => bern r)
      (fun y => LinkEvent H U Vs (Finset.univ.filter (fun v => y v = true)) (r * U.card)) := by
  have hA0 : 0 ≤ A := le_trans (Nat.cast_nonneg _) hVs
  have hx3 : 0 ≤ x ^ (-3 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hμr : IsPD (fun _ : ι => bern r) := isPD_bern hr.le (by linarith)
  -- the trivial case
  by_cases hU : U = ∅
  · subst hU
    have : ∀ y : ι → Bool, LinkEvent H ∅ Vs (Finset.univ.filter (fun v => y v = true))
        (r * (∅ : Finset ι).card) := by
      intro y Jn hJn _ hent
      obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil Jn hJn
      exact absurd (hent j.1 (mem_jEntries.2 ⟨j, hj, Or.inl rfl⟩)).1 (Finset.notMem_empty _)
    have h1 : ppr (fun _ : ι => bern r) (fun y => LinkEvent H ∅ Vs
        (Finset.univ.filter (fun v => y v = true)) (r * (∅ : Finset ι).card)) = 1 := by
      rw [← ppr_true hμr]; congr 1; funext y; exact propext ⟨fun _ => trivial, fun _ => this y⟩
    rw [h1]; linarith
  have hUne : U.Nonempty := Finset.nonempty_iff_ne_empty.2 hU
  obtain ⟨u0, hu0⟩ := hUne
  have hD : E / 4 ≤ D := by linarith
  have hUD : D ≤ U.card := (hmin u0 hu0).trans (by exact_mod_cast card_le_of_degIn)
  have hD0 : 0 < D := by linarith
  set U' := U \ Vs with hU'def
  have hU'card : (U.card : ℝ) - A ≤ U'.card := by
    rw [hU'def, Finset.card_sdiff_of_subset hVsU, Nat.cast_sub (Finset.card_le_card hVsU)]; linarith
  have hAD : A ≤ D / 32 := by linarith
  have hU'big : 31 / 32 * (U.card : ℝ) ≤ U'.card := by linarith
  have hU'E : E / 8 ≤ (U'.card : ℝ) := by linarith
  have hU'pos : (0 : ℝ) < U'.card := by linarith
  have hU'x : (U'.card : ℝ) ≤ x :=
    le_trans (by exact_mod_cast Finset.card_le_card Finset.sdiff_subset) hUx
  have hdeg' : ∀ v ∈ U', D - A ≤ degIn H U' v := by
    intro v hv
    have h1 := hmin v (Finset.mem_sdiff.1 hv).1
    have h2 : (degIn H U v : ℝ) ≤ degIn H U' v + Vs.card := by
      exact_mod_cast degIn_sdiff_le H U Vs v
    linarith
  -- the expander `U'`
  set s' := min s (D / 16)
  have hlogD : Real.log (E / 4) ≤ Real.log D := Real.log_le_log (by linarith) hD
  have hexp' : IsExpander H U' (1 / 16) c s' :=
    expander_delete (hexp.mono_s (min_le_left _ _)) hmin (min_le_right _ _) hVsU hVs
      (by linarith) (by linarith) (n3.trans hlogD) (n4.trans hlogD) hUx (by linarith)
  -- the linking property for one colour class
  set q' := q / Kc
  have hKc0 : (0 : ℝ) < Kc := by exact_mod_cast hKc
  have hq'0 : 0 < q' := div_pos hq hKc0
  have hq'1 : q' < 1 := lt_of_le_of_lt (div_le_self hq.le (by exact_mod_cast hKc)) hq1
  have hlogU' : 0 ≤ Real.log U'.card := Real.log_nonneg (by linarith)
  have hlogU'x : Real.log U'.card ≤ Real.log x := Real.log_le_log hU'pos hU'x
  have hLq : 2 * Real.log U'.card ^ (9 * c + 21) / q' ^ 10 ≤ s' := by
    have : 2 * Real.log U'.card ^ (9 * c + 21) / q' ^ 10 ≤
        2 * Real.log x ^ (9 * c + 21) / q' ^ 10 := by
      gcongr
    refine le_min (this.trans (n7.trans hs)) (this.trans (n7'.trans (by linarith)))
  set KL := 100 * Real.log U'.card ^ (7 * c + 19) / q' ^ 6
  have hKL : KL ≤ 31 / 32 / (120 * r) - 1 := by
    refine le_trans ?_ n8
    simp only [KL]
    gcongr
  have hlink0 := hL ι H U' q' s' (by exact_mod_cast (show (N₀ : ℝ) ≤ U'.card by linarith))
    hq'0 hq'1 hLq hexp'
  have hamp := ppr_amplify Kc hq'0.le hq'1.le (by
      simp only [q']; rw [mul_div_cancel₀ _ hKc0.ne']; exact hq1.le)
    (fun A' => LinkProp H U' (U'.filter (fun v => v ∈ A')) KL)
    (fun A1 A2 h12 h => h.mono_R fun v hv =>
      Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hv).1, h12 (Finset.mem_filter.1 hv).2⟩)
    (η := 1 / U'.card) (by
      have e : (fun y : ι → Bool => (fun A' => LinkProp H U' (U'.filter (fun v => v ∈ A')) KL)
          (Finset.univ.filter (fun v => y v = true))) =
          (fun y => LinkProp H U' (U'.filter (fun v => y v = true)) KL) := by
        funext y; simp
      rw [e]; exact hlink0)
  -- the colouring space
  have hμc : IsPD (fun _ : ι => colD r q) := isPD_colD hr.le hq.le hcol
  have hcs := colD_sum r q
  have hc0 : ∀ k, 0 ≤ colD r q k := hμc.1 u0
  have he1 : Real.exp 1 - 1 ≤ 1.72 := by have := Real.exp_one_lt_d9; linarith
  have he2 : 0.632 ≤ 1 - Real.exp (-1) := by have := Real.exp_neg_one_lt_d9; linarith
  have hT3 : ∑ k ∈ ({0, 4, 5} : Finset (Fin 7)), colD r q k = 10 * r := by simp [colD]; ring
  have pDeg : ∀ v ∈ U', ppr (fun _ : ι => colD r q) (fun x => 120 * r * D ≤
      (((U'.filter (H.Adj v)).filter (fun w => x w ∈ ({0, 4, 5} : Finset (Fin 7)))).card : ℝ)) ≤
      Real.exp (-(12 * r * E)) := by
    intro v hv
    refine (colour_upper hc0 hcs _ _ _).trans (Real.exp_le_exp.2 ?_)
    rw [hT3]
    have hS : (((U'.filter (H.Adj v))).card : ℝ) ≤ 4 * D := by
      refine le_trans ?_ (hmax v (Finset.mem_sdiff.1 hv).1)
      exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset)
    have h0 : 0 ≤ Real.exp 1 - 1 := by have := Real.add_one_le_exp 1; linarith
    have h1 : (Real.exp 1 - 1) * (10 * r) * ((U'.filter (H.Adj v)).card : ℝ) ≤
        1.72 * (10 * r) * (4 * D) :=
      mul_le_mul (mul_le_mul_of_nonneg_right he1 (by positivity)) hS (Nat.cast_nonneg _)
        (by positivity)
    have h2 : r * E ≤ r * (4 * D) := mul_le_mul_of_nonneg_left hE hr.le
    linarith
  have pPriv : ∀ v ∈ Vs, ppr (fun _ : ι => colD r q) (fun x =>
      (((U'.filter (H.Adj v)).filter (fun w => x w ∈ ({4} : Finset (Fin 7)))).card : ℝ) ≤ 2 * A) ≤
      Real.exp (2 * A - r * E / 13) := by
    intro v hv
    refine (colour_lower hc0 hcs {4} _ _).trans (Real.exp_le_exp.2 ?_)
    have h4 : ∑ k ∈ ({4} : Finset (Fin 7)), colD r q k = r := by simp [colD]
    rw [h4]
    have hS : D - A ≤ (((U'.filter (H.Adj v))).card : ℝ) := by
      have h1 := hmin v (hVsU hv)
      have h2 : (degIn H U v : ℝ) ≤ degIn H U' v + Vs.card := by
        exact_mod_cast degIn_sdiff_le H U Vs v
      unfold degIn at h1 h2; linarith
    have k1 : 0.632 * r * ((U'.filter (H.Adj v)).card : ℝ) ≤
        (1 - Real.exp (-1)) * r * ((U'.filter (H.Adj v)).card : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he2 hr.le) (Nat.cast_nonneg _)
    have k2 : r * (D - A) ≤ r * ((U'.filter (H.Adj v)).card : ℝ) :=
      mul_le_mul_of_nonneg_left hS hr.le
    have k3 : r * A ≤ r * (D / 32) := mul_le_mul_of_nonneg_left hAD hr.le
    have k4 : r * E ≤ r * (4 * D) := mul_le_mul_of_nonneg_left hE hr.le
    linarith
  have p5 : ppr (fun _ : ι => colD r q) (fun x =>
      ((U'.filter (fun w => x w ∈ ({5} : Finset (Fin 7)))).card : ℝ) ≤ r * U.card + 1) ≤
      Real.exp (1 - r * E / 2) := by
    refine (colour_lower hc0 hcs {5} _ _).trans (Real.exp_le_exp.2 ?_)
    have h5 : ∑ k ∈ ({5} : Finset (Fin 7)), colD r q k = 8 * r := by simp [colD]
    rw [h5]
    have k1 : 0.632 * (8 * r) * (U'.card : ℝ) ≤ (1 - Real.exp (-1)) * (8 * r) * (U'.card : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he2 (by positivity))
        (Nat.cast_nonneg _)
    have k2 : r * (31 / 32 * (U.card : ℝ)) ≤ r * U'.card := mul_le_mul_of_nonneg_left hU'big hr.le
    have k3 : r * D ≤ r * U.card := mul_le_mul_of_nonneg_left hUD hr.le
    have k4 : r * E ≤ r * (4 * D) := mul_le_mul_of_nonneg_left hE hr.le
    linarith
  have pLink : ∀ k ∈ ({1, 2, 3} : Finset (Fin 7)), ppr (fun _ : ι => colD r q)
      (fun x => ¬ LinkProp H U' (U'.filter (fun v => x v = k)) KL) ≤ (8 / E) ^ Kc := by
    intro k hk
    have hq' : ∑ j ∈ ({k} : Finset (Fin 7)), colD r q j = q := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl <;> simp [colD]
    have e := ppr_colour (ι := ι) (colD r q) hcs {k}
      (fun y => ¬ LinkProp H U' (U'.filter (fun v => v ∈ Finset.univ.filter
        (fun v => y v = true))) KL)
    rw [hq'] at e
    have e2 : (fun x : ι → Fin 7 => ¬ LinkProp H U' (U'.filter (fun v => v ∈ Finset.univ.filter
        (fun v => decide (x v ∈ ({k} : Finset (Fin 7))) = true))) KL) =
        (fun x => ¬ LinkProp H U' (U'.filter (fun v => x v = k)) KL) := by
      funext x; simp
    rw [e2] at e
    rw [e, ppr_not (isPD_bern hq.le hq1.le)]
    have hKq : (Kc : ℝ) * q' = q := by simp only [q']; rw [mul_div_cancel₀ _ hKc0.ne']
    rw [hKq] at hamp
    have h1 : (1 / (U'.card : ℝ)) ^ Kc ≤ (8 / E) ^ Kc := by
      refine pow_le_pow_left₀ (by positivity) ?_ _
      rw [div_le_div_iff₀ hU'pos (by linarith)]; linarith
    linarith
  -- the union bound
  have hU'x' : (U'.card : ℝ) ≤ x := hU'x
  have hVsx : (Vs.card : ℝ) ≤ x :=
    le_trans (by exact_mod_cast Finset.card_le_card hVsU) hUx
  have hB1 := ppr_exists_le hμc U' (fun v x => 120 * r * D ≤
      (((U'.filter (H.Adj v)).filter (fun w => x w ∈ ({0, 4, 5} : Finset (Fin 7)))).card : ℝ))
  have hB2 := ppr_exists_le hμc Vs (fun v x =>
      (((U'.filter (H.Adj v)).filter (fun w => x w ∈ ({4} : Finset (Fin 7)))).card : ℝ) ≤ 2 * A)
  have hB4 := ppr_exists_le hμc ({1, 2, 3} : Finset (Fin 7))
      (fun k x => ¬ LinkProp H U' (U'.filter (fun v => x v = k)) KL)
  have s1 : ∑ v ∈ U', ppr (fun _ : ι => colD r q) (fun x => 120 * r * D ≤
      (((U'.filter (H.Adj v)).filter (fun w => x w ∈ ({0, 4, 5} : Finset (Fin 7)))).card : ℝ)) ≤
      x * Real.exp (-(12 * r * E)) := by
    refine (Finset.sum_le_sum pDeg).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hU'x' (Real.exp_pos _).le
  have s2 : ∑ v ∈ Vs, ppr (fun _ : ι => colD r q) (fun x =>
      (((U'.filter (H.Adj v)).filter (fun w => x w ∈ ({4} : Finset (Fin 7)))).card : ℝ) ≤ 2 * A) ≤
      x * Real.exp (2 * A - r * E / 13) := by
    refine (Finset.sum_le_sum pPriv).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hVsx (Real.exp_pos _).le
  have s4 : ∑ k ∈ ({1, 2, 3} : Finset (Fin 7)), ppr (fun _ : ι => colD r q)
      (fun x => ¬ LinkProp H U' (U'.filter (fun v => x v = k)) KL) ≤ 3 * (8 / E) ^ Kc := by
    refine (Finset.sum_le_sum pLink).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]; simp
  have hBad := (ppr_or_le hμc _ _).trans (add_le_add hB1 ((ppr_or_le hμc _ _).trans
    (add_le_add hB2 ((ppr_or_le hμc _ _).trans (add_le_add p5 hB4)))))
  -- the good event implies the conclusion
  have hgood : ∀ x' : ι → Fin 7, ¬ ((∃ v ∈ U', 120 * r * D ≤
      (((U'.filter (H.Adj v)).filter (fun w => x' w ∈ ({0, 4, 5} : Finset (Fin 7)))).card : ℝ)) ∨
      (∃ v ∈ Vs, (((U'.filter (H.Adj v)).filter
        (fun w => x' w ∈ ({4} : Finset (Fin 7)))).card : ℝ) ≤ 2 * A) ∨
      ((U'.filter (fun w => x' w ∈ ({5} : Finset (Fin 7)))).card : ℝ) ≤ r * U.card + 1 ∨
      (∃ k ∈ ({1, 2, 3} : Finset (Fin 7)), ¬ LinkProp H U' (U'.filter (fun v => x' v = k)) KL)) →
      LinkEvent H U Vs (Finset.univ.filter (fun v => decide (x' v ∈ ({0} : Finset (Fin 7))) = true))
        (r * U.card) := by
    intro x' hx'
    simp only [not_or, not_exists, not_and, not_le, not_not] at hx'
    obtain ⟨g1, g2, g3, g4⟩ := hx'
    have hrU : 1 ≤ r * U.card := by
      have := mul_le_mul_of_nonneg_left hUD hr.le
      have := mul_le_mul_of_nonneg_left hE hr.le
      linarith
    have ht0 : 0 < 120 * r * D := by positivity
    refine colour_good H U Vs x' (t := 120 * r * D) (D' := D - A) g4 (fun v hv => (g1 v hv).le)
      (fun v hv => le_trans (by linarith) (g2 v hv).le) g3 hrU hdeg' ht0 ?_
    refine hKL.trans ?_
    rw [le_div_iff₀ ht0, sub_mul, div_mul_eq_mul_div, div_mul_eq_mul_div, one_mul]
    have h1 : 31 * (120 * r * D) / 32 / (120 * r) = 31 / 32 * D := by field_simp
    rw [h1]
    linarith
  have e := ppr_colour (ι := ι) (colD r q) hcs {0}
    (fun y => LinkEvent H U Vs (Finset.univ.filter (fun v => y v = true)) (r * U.card))
  have h0 : ∑ k ∈ ({0} : Finset (Fin 7)), colD r q k = r := by simp [colD]
  rw [h0] at e
  rw [← e]
  refine le_trans ?_ (ppr_mono hμc hgood)
  rw [ppr_not hμc]
  linarith

end

end Lovasz
