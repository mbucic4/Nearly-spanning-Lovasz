module
public import RequestProject.Assembly

/-!
# The sparse case of Theorem 1.2

Given an expander decomposition of the interval graph `IG` and the numerical conditions of the
probabilistic core, the core yields a path using many edges of `M`.
-/

@[expose] public section


open Classical

namespace Lovasz

namespace Conc

variable {n t : ℕ} {f : Fin n → Fin n} {m : ℕ}

lemma sum_card_le_of_disjoint {ι : Type*} [Fintype ι] {W : Fin m → Finset ι}
    (hW : ∀ i j, i ≠ j → Disjoint (W i) (W j)) : ∑ i, (W i).card ≤ Fintype.card ι := by
  rw [← Finset.card_biUnion (fun i _ j _ hij => hW i j hij)]
  exact Finset.card_le_univ _

lemma prob_bound {C S X δ : ℝ} (hC : C ≤ S) (hSX : S ≤ X) (hS1 : 1 ≤ S) (hX3 : 3 ≤ X)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) : C * X ^ (-3 : ℝ) < S ^ (-δ) / 2 := by
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have e3 : X ^ (-3 : ℝ) = 1 / X ^ 3 := by
    rw [Real.rpow_neg hX0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    simp
  have h1 : X ^ (-δ) ≤ S ^ (-δ) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hSX (by linarith)
  have h2 : X ^ (-1 : ℝ) ≤ X ^ (-δ) :=
    Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have e1 : X ^ (-1 : ℝ) = 1 / X := by rw [Real.rpow_neg_one]; simp
  have h4 : C * X ^ (-3 : ℝ) ≤ 1 / X ^ 2 := by
    rw [e3]
    have hCX : C ≤ X := hC.trans hSX
    have : C * (1 / X ^ 3) ≤ X * (1 / X ^ 3) :=
      mul_le_mul_of_nonneg_right hCX (by positivity)
    refine this.trans (le_of_eq ?_)
    field_simp
  have h5 : 1 / X ^ 2 < (1 / X) / 2 := by
    rw [div_div, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

/-- **The sparse case of Theorem 1.2.** -/
theorem main_case {N₀ : ℕ} (hL : LinkingBody 114 N₀) (hn : 0 < n) (ht : 2 ≤ t)
    (hQ : 0 < nQ n t) (hf : Function.Bijective f)
    (W : Fin m → Finset (Fin (2 * nQ n t))) (H : Fin m → SimpleGraph (Fin (2 * nQ n t)))
    (hW : ∀ i j, i ≠ j → Disjoint (W i) (W j)) (hH : ∀ i, H i ≤ IG t f)
    (hexp : ∀ i, IsExpander (H i) (W i) (1 / 8) 114 ((t : ℝ) / (4 * Real.log (W i).card ^ 114)))
    (havg : ∀ i, (t : ℝ) * (1 - Real.log (W i).card ^ (-(28 : ℝ))) * (W i).card ≤
      ∑ v ∈ W i, (degIn (H i) (W i) v : ℝ))
    (hmin : ∀ i, ∀ v ∈ W i, (∑ u ∈ W i, (degIn (H i) (W i) u : ℝ)) / (W i).card / 2 ≤
      degIn (H i) (W i) v)
    (hne : ∃ i, (W i).Nonempty)
    {A r q δ : ℝ} {k Kc : ℕ} (hk : 1 ≤ k) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hkp : (k : ℝ) ^ (-δ) ≤ r ^ 2 / 4) (hkA : 6 * (k : ℝ) ≤ A)
    (hKc : 1 ≤ Kc) (hr : 0 < r) (hq : 0 < q) (hq1 : q < 1) (hcol : 10 * r + 3 * q ≤ 1)
    (n1 : A ≤ (t : ℝ) / 128) (n2 : 13 ≤ (t : ℝ))
    (n3 : 4 * 114 * Real.log 2 ≤ Real.log ((t : ℝ) / 4))
    (n5 : 48 * Real.log ((2 * nQ n t : ℕ) : ℝ) ^ 114 * A ≤ (t : ℝ) / 4)
    (n6 : (N₀ : ℝ) ≤ (t : ℝ) / 8)
    (n7 : 2 * Real.log ((2 * nQ n t : ℕ) : ℝ) ^ (9 * 114 + 21) / (q / Kc) ^ 10 ≤
      (t : ℝ) / (8 * Real.log ((2 * nQ n t : ℕ) : ℝ) ^ 114))
    (n7' : 2 * Real.log ((2 * nQ n t : ℕ) : ℝ) ^ (9 * 114 + 21) / (q / Kc) ^ 10 ≤ (t : ℝ) / 64)
    (n8 : 100 * Real.log ((2 * nQ n t : ℕ) : ℝ) ^ (7 * 114 + 19) / (q / Kc) ^ 6 ≤
      31 / 32 / (120 * r) - 1)
    (n9 : ((2 * nQ n t : ℕ) : ℝ) * Real.exp (-(12 * r * t)) +
      ((2 * nQ n t : ℕ) : ℝ) * Real.exp (2 * A - r * t / 13) +
      Real.exp (1 - r * t / 2) + 3 * (8 / (t : ℝ)) ^ Kc ≤ ((2 * nQ n t : ℕ) : ℝ) ^ (-3 : ℝ))
    (n10 : 4 ≤ r * t) (hx3 : (3 : ℝ) ≤ ((2 * nQ n t : ℕ) : ℝ)) :
    ∃ l, IsPathL (cycleMatchGraph n f) l ∧
      r * ((∑ i, ((W i).card : ℝ)) ^ (1 - δ) / 2) ≤ countPairs (Mrel n f) l + 1 := by
  set X : ℝ := ((2 * nQ n t : ℕ) : ℝ) with hX
  set L := Real.log X with hLdef
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hL1 : 0 < L := Real.log_pos (by linarith)
  have htR : (0 : ℝ) < t := by linarith
  set g := cgeo n t hn ht hQ f hf.1 (blkOf W) with hg
  -- blocks are large, and have large minimum degree
  have hcardX : ∀ i, ((W i).card : ℝ) ≤ X := by
    intro i
    have := Finset.card_le_univ (W i)
    simp only [Fintype.card_fin] at this
    rw [hX]; exact_mod_cast this
  have hs0 : ∀ i, (0 : ℝ) ≤ (t : ℝ) / (4 * Real.log (W i).card ^ 114) := fun i =>
    div_nonneg htR.le (mul_nonneg (by norm_num) (pow_nonneg (Real.log_natCast_nonneg _) _))
  have h3 : ∀ G : Blk W, 3 ≤ (W G.1).card := fun G =>
    three_le_card_block htR (hs0 G.1) (hexp G.1) (havg G.1) G.2
  have hminD : ∀ G : Blk W, ∀ v ∈ W G.1, (t : ℝ) / 4 ≤ degIn (H G.1) (W G.1) v := fun G =>
    min_deg_block htR (h3 G) (havg G.1) (hmin G.1)
  have hmaxD : ∀ G : Blk W, ∀ v ∈ W G.1, (degIn (H G.1) (W G.1) v : ℝ) ≤ 4 * ((t : ℝ) / 4) := by
    intro G v _
    have h1 : degIn (H G.1) (W G.1) v ≤ degIn (IG t f) Finset.univ v := by
      unfold degIn
      refine Finset.card_le_card fun u hu => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      exact hH G.1 hu.2
    have h2 := degIn_IG_le (f := f) hf.1 v
    have : (degIn (H G.1) (W G.1) v : ℝ) ≤ t := by exact_mod_cast h1.trans h2
    linarith
  have hexp' : ∀ G : Blk W, IsExpander (H G.1) (W G.1) (1 / 8) 114
      ((t : ℝ) / (8 * L ^ 114)) := by
    intro G
    refine (hexp G.1).mono_s ?_
    have hw3 : (3 : ℝ) ≤ (W G.1).card := by exact_mod_cast h3 G
    have hlw : 0 < Real.log (W G.1).card := Real.log_pos (by linarith)
    have hlwL : Real.log (W G.1).card ≤ L := Real.log_le_log (by linarith) (hcardX G.1)
    apply div_le_div_of_nonneg_left htR.le (by positivity)
    have : Real.log (W G.1).card ^ 114 ≤ L ^ 114 := pow_le_pow_left₀ hlw.le hlwL _
    have : 0 < L ^ 114 := by positivity
    linarith
  -- the initial circuit
  have hneb : ∃ J G, blkOf W J = some G := by
    obtain ⟨i, v, hv⟩ := hne
    exact ⟨v, ⟨i, v, hv⟩, (blkOf_eq_some hW).2 hv⟩
  obtain ⟨hcs, hjump⟩ := initCirc_circ (hn := hn) f hf.1 ht hQ (blkOf W) hneb
  have hjumpG : ∀ G : Blk W, g.JumpAt (g.actI {J | ∃ G, g.blk J = some G ∧ True})
      (initCirc t hQ (blkOf W) hn) G := by
    intro G
    obtain ⟨v, hv⟩ := G.2
    exact hjump v G ((blkOf_eq_some hW).2 hv)
  have hfilt : Finset.univ.filter (g.JumpAt (g.actI {J | ∃ G, g.blk J = some G ∧ True})
      (initCirc t hQ (blkOf W) hn)) = Finset.univ := by
    exact Finset.filter_true_of_mem (fun G _ => hjumpG G)
  -- the total size of the blocks
  have hsum : ∑ G : Blk W, ((W G.1).card : ℝ) = ∑ i, ((W i).card : ℝ) := by
    rw [← Finset.sum_subtype (Finset.univ.filter (fun i => (W i).Nonempty))
      (p := fun i => (W i).Nonempty) (by simp) (fun i => ((W i).card : ℝ))]
    refine Finset.sum_filter_of_ne fun i _ hi => ?_
    exact Finset.card_pos.1 (by exact_mod_cast Nat.pos_of_ne_zero (by exact_mod_cast hi))
  set S := ∑ i, ((W i).card : ℝ) with hS
  have hSX : S ≤ X := by
    have := sum_card_le_of_disjoint (ι := Fin (2 * nQ n t)) hW
    simp only [Fintype.card_fin] at this
    rw [hS, hX]; exact_mod_cast this
  have hS1 : 1 ≤ S := by
    obtain ⟨i, hi⟩ := hne
    have : ((W i).card : ℝ) ≤ S :=
      Finset.single_le_sum (f := fun i => ((W i).card : ℝ)) (fun _ _ => Nat.cast_nonneg _)
        (Finset.mem_univ i)
    have : (1 : ℝ) ≤ (W i).card := by exact_mod_cast Finset.card_pos.2 hi
    linarith
  have hcardβ : (Fintype.card (Blk W) : ℝ) ≤ S := by
    rw [← hsum, Fintype.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_le_sum fun G _ => ?_
    exact_mod_cast Finset.card_pos.2 G.2
  have hprob := prob_bound hcardβ hSX hS1 hx3 hδ0 hδ1
  have hmain := core_path g (c := 114) (N₀ := N₀) (Kc := Kc) hL (fun G => H G.1)
    (fun G => W G.1) (fun _ => meOf t f hn) (fun G => blockOK hn ht hQ hf.1 hW hH G)
    (fun J G h => (blkOf_eq_some hW).1 h) (initCirc t hQ (blkOf W) hn) hcs
    ⟨hneb.choose_spec.choose, hjumpG _⟩
    (x := X) (E := t) (A := A) (r := r) (q := q) (D := (t : ℝ) / 4)
    (s := (t : ℝ) / (8 * L ^ 114)) (δ := δ) (k := k)
    hk hδ0 hδ1 hkp hkA hKc hr hq hq1 hcol (by linarith) hminD hmaxD (fun G => hcardX G.1) hexp'
    le_rfl n1 n2 n3 (by have : 0 < Real.log 2 := Real.log_pos (by norm_num); linarith) n5 n6 n7
    n7' n8 n9 n10 hX1 (by rw [hfilt, hsum]; exact hprob)
  rw [hfilt, hsum] at hmain
  exact hmain

end Conc

end Lovasz
