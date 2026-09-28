module
public import RequestProject.Loaded

/-!
# The loaded induction: Lemma 2.9 and Lemma 2.8
-/

@[expose] public section


open scoped BigOperators
open Classical

namespace Lovasz

noncomputable section

variable {ι V : Type*} {Vs : ι → Finset V} {w : V → ℕ} {C R : Finset ι}

/-- `K_i^-`: the `i`-th greedy part without its cycle of `R`. -/
def Km [Nonempty ι] (Vs : ι → Finset V) (w : V → ℕ) (C R : Finset ι) (i : ℕ) : Finset ι :=
  (Kseq Vs w C R i).erase (Rr Vs w C R i)

section helpers

lemma cov_union (A B : Finset ι) : cov Vs (A ∪ B) = cov Vs A ∪ cov Vs B := by
  unfold cov; exact Finset.union_biUnion

lemma cov_used_succ (i : ℕ) :
    cov Vs (used Vs w C R (i + 1)) = cov Vs (used Vs w C R i) ∪ cov Vs (Kseq Vs w C R i) := by
  rw [used_succ, cov_union]

lemma mem_cov_used {i : ℕ} {v : V} (hv : v ∈ cov Vs (used Vs w C R i)) :
    ∃ j < i, v ∈ cov Vs (Kseq Vs w C R j) := by
  induction i with
  | zero => simp [used, cov] at hv
  | succ i ih =>
    rw [cov_used_succ, Finset.mem_union] at hv
    rcases hv with hv | hv
    · obtain ⟨j, hj, hv⟩ := ih hv; exact ⟨j, by omega, hv⟩
    · exact ⟨i, by omega, hv⟩

lemma sum_Yset (w : V → ℕ) (i : ℕ) :
    wsum w (cov Vs (used Vs w C R i)) = ∑ j ∈ Finset.range i, wsum w (Yset Vs w C R j) := by
  induction i with
  | zero => simp [used, cov, wsum]
  | succ i ih =>
    rw [Finset.sum_range_succ, ← ih, cov_used_succ, ← Finset.union_sdiff_self_eq_union]
    exact wsum_union w Finset.disjoint_sdiff

lemma Yset_disjoint_cov_used {i j : ℕ} (hij : i ≤ j) :
    Disjoint (Yset Vs w C R j) (cov Vs (used Vs w C R i)) := by
  unfold Yset
  exact Finset.disjoint_of_subset_right (cov_mono (used_mono hij)) Finset.sdiff_disjoint

lemma used_eq_C (hR : R ⊆ C) (hconn : ∀ c ∈ C, ∃ r ∈ R, ReachC Vs C r c) :
    used Vs w C R R.card = C :=
  Finset.Subset.antisymm (used_invariant Vs w C R R.card le_rfl hR).1 (C_subset_used hR hconn)

lemma filter_update_of_notMem (S : Finset ι) (x : ι → Bool) {r : ι} (hr : r ∉ S) (b : Bool) :
    S.filter (fun c => Function.update x r b c = true) = S.filter (fun c => x c = true) := by
  ext c
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hc, h⟩; refine ⟨hc, ?_⟩
    have : c ≠ r := fun h' => hr (h' ▸ hc)
    simpa [Function.update, this] using h
  · rintro ⟨hc, h⟩; refine ⟨hc, ?_⟩
    have : c ≠ r := fun h' => hr (h' ▸ hc)
    simpa [Function.update, this] using h

variable [Nonempty ι]

lemma mem_Km {i : ℕ} {c : ι} :
    c ∈ Km Vs w C R i ↔ c ≠ Rr Vs w C R i ∧ c ∈ Kseq Vs w C R i := Finset.mem_erase

lemma Km_subset (i : ℕ) : Km Vs w C R i ⊆ Kseq Vs w C R i := Finset.erase_subset _ _

lemma Rr_notMem_Km (i : ℕ) : Rr Vs w C R i ∉ Km Vs w C R i := Finset.notMem_erase _ _

lemma cov_Kseq_disjoint_Km {i j : ℕ} (hij : i < j) (hj : j < R.card) (hR : R ⊆ C) :
    Disjoint (cov Vs (Kseq Vs w C R i)) (cov Vs (Km Vs w C R j)) := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  obtain ⟨c, hc, hvc⟩ := mem_cov.1 hv'
  have hc' := mem_Km.1 hc
  exact Finset.disjoint_left.1 (Kseq_cov_disjoint (Vs := Vs) (w := w) hij hj hR hc'.2 hc'.1) hv hvc

lemma not_meets_Kseq_Km {i j : ℕ} (hij : i < j) (hj : j < R.card) (hR : R ⊆ C) {c c' : ι}
    (hc : c ∈ Kseq Vs w C R i) (hc' : c' ∈ Km Vs w C R j) : ¬ Meets Vs c c' := by
  rintro ⟨v, hv⟩
  rw [Finset.mem_inter] at hv
  exact Finset.disjoint_left.1 (cov_Kseq_disjoint_Km (Vs := Vs) (w := w) hij hj hR)
    (mem_cov.2 ⟨c, hc, hv.1⟩) (mem_cov.2 ⟨c', hc', hv.2⟩)

lemma Km_reach {i : ℕ} (hi : i < R.card) (hR : R ⊆ C) :
    ∀ c ∈ Km Vs w C R i, ∃ r ∈ (Km Vs w C R i).filter (fun c => Meets Vs c (Rr Vs w C R i)),
      ReachC Vs (Km Vs w C R i) r c := by
  intro c hc
  obtain ⟨hne, hcK⟩ := mem_Km.1 hc
  have hreach := Kseq_conn (Vs := Vs) (w := w) hi hR _ (Rr_mem_Kseq hi hR) c hcK
  obtain ⟨c', hc'K, hc'ne, hm, hr⟩ := hreach.exists_first hne
  refine ⟨c', Finset.mem_filter.2 ⟨mem_Km.2 ⟨hc'ne, hc'K⟩, meets_comm.1 hm⟩, hr⟩

end helpers

/-- **Lemma 2.9** (the loaded induction). -/
theorem loaded_induction [Fintype ι] (w : V → ℕ) {k : ℕ} (hk : 1 ≤ k) {δ p : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (hp : (k : ℝ) ^ (-δ) ≤ p) (hp1 : p ≤ 1) :
    ∀ (C R : Finset ι), R ⊆ C → (∀ c ∈ C, ∃ r ∈ R, ReachC Vs C r c) →
    ∃ H ⊆ C, (H ∩ R).card ≤ k ∧ (∀ c ∈ H ∩ R, meetCount Vs H c ≤ 2 * k) ∧
      (∀ c ∈ H, meetCount Vs H c ≤ 3 * k) ∧
      wsum w (cov Vs C) ^ (1 - δ) ≤
        pex (fun _ => bern p) (fun x => wsum w (compV Vs (C.filter (fun c => x c = true) ∪ H) R)) := by
  have hp0 : 0 ≤ p := le_trans (Real.rpow_nonneg (Nat.cast_nonneg k) _) hp
  have hμ : IsPD (fun (_ : ι) => bern p) := isPD_bern hp0 hp1
  intro C
  induction' hn : C.card using Nat.strong_induction_on with n ih generalizing C
  intro R hR hconn
  rcases C.eq_empty_or_nonempty with hC | hCne
  · subst hC
    refine ⟨∅, Finset.Subset.refl _, by simp, by simp, by simp, ?_⟩
    have : wsum w (cov Vs (∅ : Finset ι)) = 0 := by simp [cov, wsum]
    rw [this, Real.zero_rpow (by linarith)]
    exact pex_nonneg hμ fun x => wsum_nonneg _ _
  haveI : Nonempty ι := ⟨hCne.choose⟩
  set t := R.card with ht_def
  have ht : 1 ≤ t := by
    obtain ⟨c, hc⟩ := hCne
    obtain ⟨r, hr, -⟩ := hconn c hc
    exact Finset.card_pos.2 ⟨r, hr⟩
  set S := min k t with hS_def
  have hS1 : 1 ≤ S := le_min hk ht
  have hSk : S ≤ k := min_le_left _ _
  have hSt : S ≤ t := min_le_right _ _
  set K := Kseq Vs w C R with hK_def
  set Rr' := Rr Vs w C R with hRr_def
  set Km' := Km Vs w C R with hKm_def
  set Kle := (Finset.range S).biUnion Km' with hKle_def
  set Rle := Kle.filter (fun c => ∃ i < S, Meets Vs c (Rr' i)) with hRle_def
  set Rm := fun i => (Km' i).filter (fun c => Meets Vs c (Rr' i)) with hRm_def
  -- basic facts
  have hKC : ∀ i < t, K i ⊆ C := fun i hi =>
    (Kseq_subset (Vs := Vs) (w := w) hi hR).trans Finset.sdiff_subset
  have hRrK : ∀ i < t, Rr' i ∈ K i := fun i hi => Rr_mem_Kseq hi hR
  have hRrR : ∀ i < t, Rr' i ∈ R := fun i hi => Rr_mem_R hi hR
  have hRrC : ∀ i < t, Rr' i ∈ C := fun i hi => hKC i hi (hRrK i hi)
  have hKmC : ∀ i < t, Km' i ⊆ C := fun i hi => (Km_subset i).trans (hKC i hi)
  have hKleC : Kle ⊆ C := by
    intro c hc
    obtain ⟨i, hi, hc⟩ := Finset.mem_biUnion.1 hc
    exact hKmC i (by rw [Finset.mem_range] at hi; omega) hc
  have hKmR : ∀ i < t, ∀ c ∈ Km' i, c ∉ R := fun i hi c hc hcR =>
    (mem_Km.1 hc).1 (mem_R_of_mem_Kseq hi hR (mem_Km.1 hc).2 hcR)
  have hKle_lt : Kle.card < n := by
    rw [← hn]
    refine Finset.card_lt_card ⟨hKleC, fun h => ?_⟩
    have h0 : Rr' 0 ∈ Kle := h (hRrC 0 (by omega))
    obtain ⟨i, hi, hc⟩ := Finset.mem_biUnion.1 h0
    rw [Finset.mem_range] at hi
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · exact Rr_notMem_Km 0 hc
    · exact Finset.disjoint_left.1 (Kseq_disjoint (Vs := Vs) (w := w) hipos (by omega) hR)
        (hRrK 0 (by omega)) (Km_subset i hc)
  have hKm_lt : ∀ i < t, (Km' i).card < n := fun i hi => by
    rw [← hn]
    exact Finset.card_lt_card ⟨hKmC i hi, fun h => Rr_notMem_Km i (h (hRrC i hi))⟩
  -- apply the induction hypothesis
  have hRle_reach : ∀ c ∈ Kle, ∃ r ∈ Rle, ReachC Vs Kle r c := by
    intro c hc
    obtain ⟨i, hi, hc⟩ := Finset.mem_biUnion.1 hc
    rw [Finset.mem_range] at hi
    obtain ⟨r, hr, hreach⟩ := Km_reach (Vs := Vs) (w := w) (by omega : i < t) hR c hc
    have hsub : Km' i ⊆ Kle := Finset.subset_biUnion_of_mem Km' (Finset.mem_range.2 hi)
    refine ⟨r, Finset.mem_filter.2 ⟨hsub (Finset.mem_filter.1 hr).1, i, hi,
      (Finset.mem_filter.1 hr).2⟩, hreach.mono hsub⟩
  obtain ⟨Hle, hHleC, hHle1, hHle2, hHle3, hHle4⟩ :=
    ih Kle.card hKle_lt Kle rfl Rle (Finset.filter_subset _ _) hRle_reach
  have hIHi : ∀ i, S ≤ i → i < t → ∃ H ⊆ Km' i, (H ∩ Rm i).card ≤ k ∧
      (∀ c ∈ H ∩ Rm i, meetCount Vs H c ≤ 2 * k) ∧ (∀ c ∈ H, meetCount Vs H c ≤ 3 * k) ∧
      wsum w (cov Vs (Km' i)) ^ (1 - δ) ≤ pex (fun _ => bern p)
        (fun x => wsum w (compV Vs ((Km' i).filter (fun c => x c = true) ∪ H) (Rm i))) :=
    fun i _ hi => ih _ (hKm_lt i hi) (Km' i) rfl (Rm i) (Finset.filter_subset _ _)
      (Km_reach (Vs := Vs) (w := w) hi hR)
  choose! Hi hHiC hHi1 hHi2 hHi3 hHi4 using hIHi
  set H := (Finset.range S).image Rr' ∪ Hle ∪ (Finset.Ico S t).biUnion Hi with hH_def
  have hmemH : ∀ c, c ∈ H ↔ (∃ i < S, Rr' i = c) ∨ c ∈ Hle ∨ ∃ i, S ≤ i ∧ i < t ∧ c ∈ Hi i := by
    intro c
    simp only [hH_def, Finset.mem_union, Finset.mem_image, Finset.mem_range, Finset.mem_biUnion,
      Finset.mem_Ico]
    constructor
    · rintro ((⟨i, hi, h⟩ | h) | ⟨i, ⟨h1, h2⟩, h⟩)
      · exact Or.inl ⟨i, hi, h⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨i, h1, h2, h⟩)
    · rintro (⟨i, hi, h⟩ | h | ⟨i, h1, h2, h⟩)
      · exact Or.inl (Or.inl ⟨i, hi, h⟩)
      · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨i, ⟨h1, h2⟩, h⟩
  have hHleKm : ∀ c ∈ Hle, ∃ i < S, c ∈ Km' i := by
    intro c hc
    obtain ⟨i, hi, hc⟩ := Finset.mem_biUnion.1 (hHleC hc)
    exact ⟨i, Finset.mem_range.1 hi, hc⟩
  have hHC : H ⊆ C := by
    intro c hc
    rcases (hmemH c).1 hc with ⟨i, hi, rfl⟩ | h | ⟨i, _, h2, h⟩
    · exact hRrC i (by omega)
    · exact hKleC (hHleC h)
    · exact hKmC i h2 (hHiC i ‹_› h2 h)
  -- (C1)
  have hHR : H ∩ R ⊆ (Finset.range S).image Rr' := by
    intro c hc
    obtain ⟨hcH, hcR⟩ := Finset.mem_inter.1 hc
    rcases (hmemH c).1 hcH with ⟨i, hi, rfl⟩ | h | ⟨i, h1, h2, h⟩
    · exact Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩
    · obtain ⟨i, hi, hc'⟩ := hHleKm c h
      exact absurd hcR (hKmR i (by omega) c hc')
    · exact absurd hcR (hKmR i h2 c (hHiC i h1 h2 h))
  have hC1 : (H ∩ R).card ≤ k :=
    (Finset.card_le_card hHR).trans (Finset.card_image_le.trans (by simp [hSk]))
  -- (C2)
  have hC2' : ∀ i < S, meetCount Vs H (Rr' i) ≤ 2 * k := by
    intro i hi
    have hsub : H.filter (Meets Vs (Rr' i)) ⊆ (Finset.range S).image Rr' ∪ (Hle ∩ Rle) := by
      intro c hc
      obtain ⟨hcH, hm⟩ := Finset.mem_filter.1 hc
      rcases (hmemH c).1 hcH with ⟨j, hj, rfl⟩ | h | ⟨j, h1, h2, h⟩
      · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨j, Finset.mem_range.2 hj, rfl⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨h, Finset.mem_filter.2
          ⟨hHleC h, i, hi, meets_comm.1 hm⟩⟩)
      · exact absurd hm (not_meets_Kseq_Km (Vs := Vs) (w := w) (by omega) h2 hR
          (hRrK i (by omega)) (hHiC j h1 h2 h))
    unfold meetCount
    calc (H.filter (Meets Vs (Rr' i))).card
        ≤ ((Finset.range S).image Rr' ∪ (Hle ∩ Rle)).card := Finset.card_le_card hsub
      _ ≤ ((Finset.range S).image Rr').card + (Hle ∩ Rle).card := Finset.card_union_le _ _
      _ ≤ S + k := add_le_add (Finset.card_image_le.trans (by simp)) hHle1
      _ ≤ 2 * k := by omega
  have hC2 : ∀ c ∈ H ∩ R, meetCount Vs H c ≤ 2 * k := by
    intro c hc
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 (hHR hc)
    exact hC2' i (Finset.mem_range.1 hi)
  -- (C3)
  have hC3 : ∀ c ∈ H, meetCount Vs H c ≤ 3 * k := by
    intro c hcH
    rcases (hmemH c).1 hcH with ⟨i, hi, rfl⟩ | hcle | ⟨j0, hj1, hj2, hcj⟩
    · exact (hC2' i hi).trans (by omega)
    · obtain ⟨i0, hi0, hci0⟩ := hHleKm c hcle
      have hnotHi : ∀ c' ∈ H, Meets Vs c c' → (∃ i < S, Rr' i = c') ∨ c' ∈ Hle := by
        intro c' hc' hm
        rcases (hmemH c').1 hc' with h | h | ⟨j, h1, h2, h⟩
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd hm (not_meets_Kseq_Km (Vs := Vs) (w := w) (by omega) h2 hR
            (Km_subset i0 hci0) (hHiC j h1 h2 h))
      by_cases hcR : c ∈ Rle
      · have hsub : H.filter (Meets Vs c) ⊆ (Finset.range S).image Rr' ∪ Hle.filter (Meets Vs c) := by
          intro c' hc'
          obtain ⟨hc'H, hm⟩ := Finset.mem_filter.1 hc'
          rcases hnotHi c' hc'H hm with ⟨j, hj, rfl⟩ | h
          · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨j, Finset.mem_range.2 hj, rfl⟩)
          · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨h, hm⟩)
        unfold meetCount
        calc (H.filter (Meets Vs c)).card
            ≤ ((Finset.range S).image Rr' ∪ Hle.filter (Meets Vs c)).card :=
              Finset.card_le_card hsub
          _ ≤ ((Finset.range S).image Rr').card + (Hle.filter (Meets Vs c)).card :=
              Finset.card_union_le _ _
          _ ≤ S + 2 * k := add_le_add (Finset.card_image_le.trans (by simp))
              (hHle2 c (Finset.mem_inter.2 ⟨hcle, hcR⟩))
          _ ≤ 3 * k := by omega
      · have hsub : H.filter (Meets Vs c) ⊆ Hle.filter (Meets Vs c) := by
          intro c' hc'
          obtain ⟨hc'H, hm⟩ := Finset.mem_filter.1 hc'
          rcases hnotHi c' hc'H hm with ⟨j, hj, rfl⟩ | h
          · exact absurd (Finset.mem_filter.2 ⟨hHleC hcle, j, hj, hm⟩) hcR
          · exact Finset.mem_filter.2 ⟨h, hm⟩
        exact (Finset.card_le_card hsub).trans (hHle3 c hcle)
    · have hcKm : c ∈ Km' j0 := hHiC j0 hj1 hj2 hcj
      have hsub : H.filter (Meets Vs c) ⊆ (Hi j0).filter (Meets Vs c) := by
        intro c' hc'
        obtain ⟨hc'H, hm⟩ := Finset.mem_filter.1 hc'
        refine Finset.mem_filter.2 ⟨?_, hm⟩
        rcases (hmemH c').1 hc'H with ⟨i, hi, rfl⟩ | h | ⟨j, h1, h2, h⟩
        · exact absurd (meets_comm.1 hm) (not_meets_Kseq_Km (Vs := Vs) (w := w) (by omega) hj2 hR
            (hRrK i (by omega)) hcKm)
        · obtain ⟨i, hi, hci⟩ := hHleKm c' h
          exact absurd (meets_comm.1 hm) (not_meets_Kseq_Km (Vs := Vs) (w := w) (by omega) hj2 hR
            (Km_subset i hci) hcKm)
        · have hc'Km : c' ∈ Km' j := hHiC j h1 h2 h
          rcases lt_trichotomy j j0 with hlt | heq | hgt
          · exact absurd (meets_comm.1 hm) (not_meets_Kseq_Km (Vs := Vs) (w := w) hlt hj2 hR
              (Km_subset j hc'Km) hcKm)
          · exact heq ▸ h
          · exact absurd hm (not_meets_Kseq_Km (Vs := Vs) (w := w) hgt h2 hR
              (Km_subset j0 hcKm) hc'Km)
      exact (Finset.card_le_card hsub).trans (hHi3 j0 hj1 hj2 c hcj)
  -- (C4)
  have hC4 : wsum w (cov Vs C) ^ (1 - δ) ≤
      pex (fun _ => bern p) (fun x => wsum w (compV Vs (C.filter (fun c => x c = true) ∪ H) R)) := by
    set P1 : (ι → Bool) → Finset V :=
      fun x => compV Vs (Kle.filter (fun c => x c = true) ∪ Hle) Rle with hP1
    set P2 : ℕ → (ι → Bool) → Finset V :=
      fun i x => compV Vs ((Km' i).filter (fun c => x c = true) ∪ Hi i) (Rm i) with hP2
    set Q0 : Finset V := cov Vs (used Vs w C R S) \ cov Vs Kle with hQ0
    set Q : ℕ → Finset V := fun i => Yset Vs w C R i \ cov Vs (Km' i) with hQ
    set Fi : (ι → Bool) → ℕ → Finset V :=
      fun x i => if x (Rr' i) = true then P2 i x ∪ Q i else ∅ with hFi
    -- geometric facts
    have hcovKle : cov Vs Kle ⊆ cov Vs (used Vs w C R S) := by
      refine cov_mono fun c hc => ?_
      obtain ⟨i, hi, hc⟩ := Finset.mem_biUnion.1 hc
      exact Kseq_subset_used (Finset.mem_range.1 hi) (Km_subset i hc)
    have hP1sub : ∀ x, P1 x ⊆ cov Vs Kle := fun x =>
      (compV_subset_cov _ _).trans (by
        rw [cov_union]; exact Finset.union_subset
          (cov_mono (Finset.filter_subset _ _)) (cov_mono hHleC))
    have hP2sub : ∀ i, S ≤ i → i < t → ∀ x, P2 i x ⊆ cov Vs (Km' i) := fun i h1 h2 x =>
      (compV_subset_cov _ _).trans (by
        rw [cov_union]; exact Finset.union_subset
          (cov_mono (Finset.filter_subset _ _)) (cov_mono (hHiC i h1 h2)))
    have hYsub : ∀ i, Yset Vs w C R i ⊆ cov Vs (K i) := fun i => Finset.sdiff_subset
    have hFisub1 : ∀ x i, S ≤ i → i < t → Fi x i ⊆ cov Vs (Km' i) ∪ Yset Vs w C R i := by
      intro x i h1 h2
      simp only [hFi]; split_ifs
      · exact Finset.union_subset_union (hP2sub i h1 h2 x) Finset.sdiff_subset
      · exact Finset.empty_subset _
    have hFisub2 : ∀ x i, S ≤ i → i < t → Fi x i ⊆ cov Vs (K i) := fun x i h1 h2 =>
      (hFisub1 x i h1 h2).trans (Finset.union_subset (cov_mono (Km_subset i)) (hYsub i))
    have hdisj1 : ∀ i, S ≤ i → i < t →
        Disjoint (cov Vs (used Vs w C R S)) (cov Vs (Km' i) ∪ Yset Vs w C R i) := by
      intro i h1 h2
      rw [Finset.disjoint_union_right]
      refine ⟨Finset.disjoint_left.2 fun v hv hv' => ?_,
        (Yset_disjoint_cov_used (Vs := Vs) (w := w) h1).symm⟩
      obtain ⟨j, hj, hvj⟩ := mem_cov_used hv
      exact Finset.disjoint_left.1 (cov_Kseq_disjoint_Km (Vs := Vs) (w := w) (by omega) h2 hR)
        hvj hv'
    have hdisj2 : ∀ i j, S ≤ i → i < j → j < t →
        Disjoint (cov Vs (K i)) (cov Vs (Km' j) ∪ Yset Vs w C R j) := by
      intro i j h1 hij h2
      rw [Finset.disjoint_union_right]
      exact ⟨cov_Kseq_disjoint_Km (Vs := Vs) (w := w) hij h2 hR,
        Finset.disjoint_of_subset_left (cov_mono (Kseq_subset_used hij))
          (Yset_disjoint_cov_used (Vs := Vs) (w := w) le_rfl).symm⟩
    -- the pointwise inequality
    have hpt : ∀ x, wsum w (P1 x) + wsum w Q0 + ∑ i ∈ Finset.Ico S t,
        (if x (Rr' i) = true then wsum w (P2 i x) + wsum w (Q i) else 0) ≤
        wsum w (compV Vs (C.filter (fun c => x c = true) ∪ H) R) := by
      intro x
      set B := C.filter (fun c => x c = true) ∪ H with hB
      have hHB : H ⊆ B := Finset.subset_union_right
      have hAB : C.filter (fun c => x c = true) ⊆ B := Finset.subset_union_left
      have hRrV : ∀ i < t, Rr' i ∈ B → Vs (Rr' i) ⊆ compV Vs B R := fun i hi hRB v hv =>
        mem_compV.2 ⟨Rr' i, hRB, ⟨Rr' i, hRrR i hi, hRB, Relation.ReflTransGen.refl⟩, hv⟩
      have hRrH : ∀ i < S, Rr' i ∈ B := fun i hi => hHB ((hmemH _).2 (Or.inl ⟨i, hi, rfl⟩))
      have hP1V : P1 x ⊆ compV Vs B R := by
        intro v hv
        obtain ⟨c, hc, ⟨r, hr, hrB1, hrc⟩, hvc⟩ := mem_compV.1 hv
        obtain ⟨hrKle, i, hi, hm⟩ := Finset.mem_filter.1 hr
        have hsub : Kle.filter (fun c => x c = true) ∪ Hle ⊆ B :=
          Finset.union_subset (fun c hc => hAB (Finset.mem_filter.2
            ⟨hKleC (Finset.mem_filter.1 hc).1, (Finset.mem_filter.1 hc).2⟩))
            (fun c hc => hHB ((hmemH c).2 (Or.inr (Or.inl hc))))
        exact mem_compV.2 ⟨c, hsub hc, ⟨Rr' i, hRrR i (by omega), hRrH i hi,
          (ReachC.single (hRrH i hi) (hsub hrB1) (meets_comm.1 hm)).trans (hrc.mono hsub)⟩, hvc⟩
      have hQ0V : Q0 ⊆ compV Vs B R := by
        intro v hv
        obtain ⟨hv1, hv2⟩ := Finset.mem_sdiff.1 hv
        obtain ⟨i, hi, hvi⟩ := mem_cov_used hv1
        obtain ⟨c, hc, hvc⟩ := mem_cov.1 hvi
        by_cases hcr : c = Rr' i
        · rw [hcr] at hvc; exact hRrV i (by omega) (hRrH i hi) hvc
        · exact absurd (mem_cov.2 ⟨c, Finset.mem_biUnion.2 ⟨i, Finset.mem_range.2 hi,
            mem_Km.2 ⟨hcr, hc⟩⟩, hvc⟩) hv2
      have hFiV : ∀ i, S ≤ i → i < t → Fi x i ⊆ compV Vs B R := by
        intro i h1 h2 v hv
        simp only [hFi] at hv
        split_ifs at hv with hxr
        · have hRB : Rr' i ∈ B := hAB (Finset.mem_filter.2 ⟨hRrC i h2, hxr⟩)
          rcases Finset.mem_union.1 hv with hv | hv
          · obtain ⟨c, hc, ⟨r, hr, hrB1, hrc⟩, hvc⟩ := mem_compV.1 hv
            obtain ⟨hrKm, hm⟩ := Finset.mem_filter.1 hr
            have hsub : (Km' i).filter (fun c => x c = true) ∪ Hi i ⊆ B :=
              Finset.union_subset (fun c hc => hAB (Finset.mem_filter.2
                ⟨hKmC i h2 (Finset.mem_filter.1 hc).1, (Finset.mem_filter.1 hc).2⟩))
                (fun c hc => hHB ((hmemH c).2 (Or.inr (Or.inr ⟨i, h1, h2, hc⟩))))
            exact mem_compV.2 ⟨c, hsub hc, ⟨Rr' i, hRrR i h2, hRB,
              (ReachC.single hRB (hsub hrB1) (meets_comm.1 hm)).trans (hrc.mono hsub)⟩, hvc⟩
          · obtain ⟨hv1, hv2⟩ := Finset.mem_sdiff.1 hv
            obtain ⟨c, hc, hvc⟩ := mem_cov.1 (hYsub i hv1)
            by_cases hcr : c = Rr' i
            · rw [hcr] at hvc; exact hRrV i h2 hRB hvc
            · exact absurd (mem_cov.2 ⟨c, mem_Km.2 ⟨hcr, hc⟩, hvc⟩) hv2
        · simp at hv
      set Z := (P1 x ∪ Q0) ∪ (Finset.Ico S t).biUnion (Fi x) with hZ
      have hZV : Z ⊆ compV Vs B R :=
        Finset.union_subset (Finset.union_subset hP1V hQ0V) (Finset.biUnion_subset.2
          fun i hi => hFiV i (Finset.mem_Ico.1 hi).1 (Finset.mem_Ico.1 hi).2)
      have hPQ : Disjoint (P1 x) Q0 :=
        Finset.disjoint_of_subset_left (hP1sub x) Finset.disjoint_sdiff
      have hfirst : P1 x ∪ Q0 ⊆ cov Vs (used Vs w C R S) :=
        Finset.union_subset ((hP1sub x).trans hcovKle) Finset.sdiff_subset
      have hdisjA : Disjoint (P1 x ∪ Q0) ((Finset.Ico S t).biUnion (Fi x)) := by
        rw [Finset.disjoint_biUnion_right]
        intro i hi
        obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hi
        exact Finset.disjoint_of_subset_left hfirst
          (Finset.disjoint_of_subset_right (hFisub1 x i h1 h2) (hdisj1 i h1 h2))
      have hpair : (↑(Finset.Ico S t) : Set ℕ).PairwiseDisjoint (Fi x) := by
        intro i hi j hj hij
        simp only [Finset.coe_Ico, Set.mem_Ico] at hi hj
        rcases lt_or_gt_of_ne hij with h | h
        · exact Finset.disjoint_of_subset_left (hFisub2 x i hi.1 hi.2)
            (Finset.disjoint_of_subset_right (hFisub1 x j hj.1 hj.2) (hdisj2 i j hi.1 h hj.2))
        · exact (Finset.disjoint_of_subset_left (hFisub2 x j hj.1 hj.2)
            (Finset.disjoint_of_subset_right (hFisub1 x i hi.1 hi.2)
              (hdisj2 j i hj.1 h hi.2))).symm
      have hsumZ : wsum w Z = wsum w (P1 x) + wsum w Q0 +
          ∑ i ∈ Finset.Ico S t, wsum w (Fi x i) := by
        rw [hZ, wsum_union w hdisjA, wsum_union w hPQ]
        unfold wsum; rw [Finset.sum_biUnion hpair]
      have hFi_w : ∀ i ∈ Finset.Ico S t, wsum w (Fi x i) =
          if x (Rr' i) = true then wsum w (P2 i x) + wsum w (Q i) else 0 := by
        intro i hi
        obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hi
        simp only [hFi]; split_ifs
        · exact wsum_union w (Finset.disjoint_of_subset_left (hP2sub i h1 h2 x)
            Finset.disjoint_sdiff)
        · simp [wsum]
      calc _ = wsum w Z := by rw [hsumZ, Finset.sum_congr rfl hFi_w]
        _ ≤ _ := wsum_mono w hZV
    -- expectations
    have hindep : ∀ i, S ≤ i → i < t →
        pex (fun _ => bern p) (fun x => if x (Rr' i) = true then wsum w (P2 i x) + wsum w (Q i)
          else 0) = p * (pex (fun _ => bern p) (fun x => wsum w (P2 i x)) + wsum w (Q i)) := by
      intro i h1 h2
      have hind : IndepOf (fun x => wsum w (P2 i x) + wsum w (Q i)) (Rr' i) := by
        intro x b
        have hr : Rr' i ∉ Km' i := Rr_notMem_Km i
        simp only [hP2]
        rw [filter_update_of_notMem _ x hr b]
      have := pex_indep_mul hμ hind (fun b => if b = true then (1 : ℝ) else 0)
      have e1 : (∑ k, bern p k * (if k = true then (1:ℝ) else 0)) = p := by simp [bern]
      rw [e1, pex_add (fun x => wsum w (P2 i x)) (fun _ => wsum w (Q i)), pex_const hμ] at this
      rw [← this]
      congr 1; funext x
      split_ifs <;> simp
    -- the numerical part
    set X := wsum w (cov Vs (used Vs w C R S)) with hX
    set a := wsum w (cov Vs Kle) with ha
    set y : ℕ → ℝ := fun i => wsum w (Yset Vs w C R i) with hy
    have hXsum : X = ∑ j ∈ Finset.range S, y j := sum_Yset w S
    have htot : wsum w (cov Vs C) = X + ∑ i ∈ Finset.Ico S t, y i := by
      rw [← used_eq_C (Vs := Vs) (w := w) hR hconn, sum_Yset w t, hXsum,
        Finset.sum_range_add_sum_Ico _ hSt]
    have hQ0w : wsum w Q0 = X - a := wsum_sdiff w hcovKle
    have hA : X ^ (1 - δ) ≤ a ^ (1 - δ) + wsum w Q0 := by
      have h := rpow_one_sub_add_le hδ0 hδ1 (wsum_nonneg w (cov Vs Kle)) (∑ v ∈ Q0, w v)
      rw [← wsum_eq_nat] at h
      rw [hQ0w] at h ⊢
      rw [← ha, add_sub_cancel] at h
      exact h
    have hBi : ∀ i ∈ Finset.Ico S t, y i ^ (1 - δ) ≤
        pex (fun _ => bern p) (fun x => wsum w (P2 i x)) + wsum w (Q i) := by
      intro i hi
      obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hi
      have hsub : Yset Vs w C R i ⊆ cov Vs (Km' i) ∪ Q i := by
        intro v hv
        by_cases h : v ∈ cov Vs (Km' i)
        · exact Finset.mem_union_left _ h
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hv, h⟩)
      have hle : y i ≤ wsum w (cov Vs (Km' i)) + wsum w (Q i) := by
        refine (wsum_mono w hsub).trans ?_
        rw [wsum_union w (Finset.disjoint_sdiff)]
      have h3 := rpow_one_sub_add_le hδ0 hδ1 (wsum_nonneg w (cov Vs (Km' i))) (∑ v ∈ Q i, w v)
      rw [← wsum_eq_nat] at h3
      calc y i ^ (1 - δ) ≤ (wsum w (cov Vs (Km' i)) + wsum w (Q i)) ^ (1 - δ) :=
            Real.rpow_le_rpow (wsum_nonneg _ _) hle (by linarith)
        _ ≤ wsum w (cov Vs (Km' i)) ^ (1 - δ) + wsum w (Q i) := h3
        _ ≤ _ := by linarith [hHi4 i h1 h2]
    have hanti : ∀ i, i < t → ∀ j ≤ i, y i ≤ y j := by
      intro i hi j hj
      induction i with
      | zero => rw [Nat.le_zero.1 hj]
      | succ i ih =>
        rcases Nat.lt_or_ge j (i + 1) with hji | hji
        · refine le_trans ?_ (ih (by omega) (by omega))
          simp only [hy, wsum_eq_nat]
          exact_mod_cast Yset_antitone (Vs := Vs) (w := w) hi hR
        · rw [le_antisymm hj hji]
    have hyk : ∀ i ∈ Finset.Ico S t, y i ≤ X / k := by
      intro i hi
      obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hi
      have hSk' : S = k := by
        rcases le_total k t with h | h
        · exact min_eq_left h
        · exfalso; have : S = t := min_eq_right h; omega
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
      rw [le_div_iff₀ hk0, hXsum, hSk']
      calc y i * k = ∑ j ∈ Finset.range k, y i := by simp [mul_comm]
        _ ≤ ∑ j ∈ Finset.range k, y j := Finset.sum_le_sum fun j hj =>
            hanti i h2 j (by rw [Finset.mem_range] at hj; omega)
    have hF := fact_2_11 (Finset.Ico S t) hk hδ0 hδ1 hp (wsum_nonneg w _) y
      (fun i _ => wsum_nonneg w _) hyk
    have hE : pex (fun _ => bern p) (fun x => wsum w (P1 x) + wsum w Q0 + ∑ i ∈ Finset.Ico S t,
        (if x (Rr' i) = true then wsum w (P2 i x) + wsum w (Q i) else 0)) =
        pex (fun _ => bern p) (fun x => wsum w (P1 x)) + wsum w Q0 + ∑ i ∈ Finset.Ico S t,
          p * (pex (fun _ => bern p) (fun x => wsum w (P2 i x)) + wsum w (Q i)) := by
      rw [pex_add, pex_add, pex_const hμ, pex_sum]
      congr 1
      exact Finset.sum_congr rfl fun i hi =>
        hindep i (Finset.mem_Ico.1 hi).1 (Finset.mem_Ico.1 hi).2
    calc wsum w (cov Vs C) ^ (1 - δ) = (X + ∑ i ∈ Finset.Ico S t, y i) ^ (1 - δ) := by rw [htot]
      _ ≤ X ^ (1 - δ) + p * ∑ i ∈ Finset.Ico S t, y i ^ (1 - δ) := hF
      _ ≤ a ^ (1 - δ) + wsum w Q0 + ∑ i ∈ Finset.Ico S t,
            p * (pex (fun _ => bern p) (fun x => wsum w (P2 i x)) + wsum w (Q i)) := by
          rw [Finset.mul_sum]
          have := Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hBi i hi) hp0
          linarith
      _ ≤ pex (fun _ => bern p) (fun x => wsum w (P1 x)) + wsum w Q0 + ∑ i ∈ Finset.Ico S t,
            p * (pex (fun _ => bern p) (fun x => wsum w (P2 i x)) + wsum w (Q i)) := by
          linarith [hHle4]
      _ = _ := hE.symm
      _ ≤ _ := pex_mono hμ hpt
  exact ⟨H, hHC, hC1, hC2, hC3, hC4⟩

/-- **Lemma 2.8** (in the form used in the proof of Theorem 1.2).  For a connected collection
`C` of cycles there is a subcollection `H` in which every vertex lies on at most `3k` cycles
such that, with probability at least `w(C)^(-δ)/2`, the component of `c₀` in `Cp ∪ H` has
weight at least `w(C)^(1-δ)/2`. -/
theorem heavy_component [Fintype ι] (w : V → ℕ) {k : ℕ} (hk : 1 ≤ k) {δ p : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (hp : (k : ℝ) ^ (-δ) ≤ p) (hp1 : p ≤ 1) (C : Finset ι) (c₀ : ι)
    (hc₀ : c₀ ∈ C) (hconn : ∀ c ∈ C, ReachC Vs C c₀ c) (hW : 0 < wsum w (cov Vs C)) :
    ∃ H ⊆ C, (∀ v, (H.filter (fun c => v ∈ Vs c)).card ≤ 3 * k) ∧
      wsum w (cov Vs C) ^ (-δ) / 2 ≤ ppr (fun _ => bern p) (fun x =>
        wsum w (cov Vs C) ^ (1 - δ) / 2 ≤
          wsum w (compV Vs (C.filter (fun c => x c = true) ∪ H) {c₀})) := by
  have hp0 : 0 ≤ p := le_trans (Real.rpow_nonneg (Nat.cast_nonneg k) _) hp
  have hμ : IsPD (fun (_ : ι) => bern p) := isPD_bern hp0 hp1
  obtain ⟨H, hHC, -, -, hH3, hH4⟩ := loaded_induction (Vs := Vs) w hk hδ0 hδ1 hp hp1 C {c₀}
    (Finset.singleton_subset_iff.2 hc₀) (fun c hc => ⟨c₀, Finset.mem_singleton_self _, hconn c hc⟩)
  refine ⟨H, hHC, fun v => ?_, ?_⟩
  · by_cases hne : (H.filter (fun c => v ∈ Vs c)).Nonempty
    · obtain ⟨c, hc⟩ := hne
      obtain ⟨hcH, hvc⟩ := Finset.mem_filter.1 hc
      refine le_trans (Finset.card_le_card fun c' hc' => ?_) (hH3 c hcH)
      obtain ⟨hc'H, hvc'⟩ := Finset.mem_filter.1 hc'
      exact Finset.mem_filter.2 ⟨hc'H, v, Finset.mem_inter.2 ⟨hvc, hvc'⟩⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at hne; rw [hne]; simp
  · set W := wsum w (cov Vs C) with hWdef
    set f : (ι → Bool) → ℝ := fun x => wsum w (compV Vs (C.filter (fun c => x c = true) ∪ H) {c₀})
    have hfW : ∀ x, f x ≤ W := fun x =>
      wsum_mono w ((compV_subset_cov _ _).trans (cov_mono (Finset.union_subset
        (Finset.filter_subset _ _) hHC)))
    have hpt : ∀ x, f x ≤ W * (if W ^ (1 - δ) / 2 ≤ f x then 1 else 0) + W ^ (1 - δ) / 2 := by
      intro x
      have : 0 ≤ W ^ (1 - δ) := Real.rpow_nonneg hW.le _
      split_ifs with h
      · linarith [hfW x]
      · push_neg at h; linarith
    have hE := pex_mono hμ hpt
    rw [pex_add, pex_const hμ, pex_const_mul] at hE
    have h1 : W ^ (1 - δ) / 2 ≤ W * ppr (fun _ => bern p) (fun x => W ^ (1 - δ) / 2 ≤ f x) := by
      unfold ppr; linarith
    have h2 : W ^ (1 - δ) = W * W ^ (-δ) := by
      rw [sub_eq_add_neg, Real.rpow_add hW, Real.rpow_one]
    have h3 : W * (W ^ (-δ) / 2) ≤ W * ppr (fun _ => bern p) (fun x => W ^ (1 - δ) / 2 ≤ f x) := by
      rw [show W * (W ^ (-δ) / 2) = W ^ (1 - δ) / 2 by rw [h2]; ring]; exact h1
    exact le_of_mul_le_mul_left h3 hW

end

end Lovasz
