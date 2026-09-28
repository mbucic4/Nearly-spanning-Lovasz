module
public import RequestProject.NilAssembly

/-!
# From the layer data in `G` to the downward induction in `C`

Transport the output of the preliminary layer construction (`Tointon.exists_layerData`, stated in
the ambient group `G`) into the subgroup `C`, viewed as a group in its own right, and run the
downward induction there.  The result (`Tointon.exists_large_piece_bounded_lcs`) gives a subgroup
`C` with `|A| ≤ κ^(18κ⁶) |A² ∩ C|` and `γ_{κ⁶}(C) ⊆ A^R`, where `R` depends only on `κ`.
-/

@[expose] public section

open scoped Pointwise

namespace Tointon

variable {G : Type} [Group G]

/-- The filtration `m ↦ A^m ∩ C`, as subsets of `C`. -/
lemma filt_preimage {κ : ℕ} {A : Set G} (hA : IsApproximateSubgroup (κ : ℝ) A) (C : Subgroup G) :
    Filt κ (fun m => ((↑) : C → G) ⁻¹' (A ^ m)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp
  · intro m n h
    exact Set.preimage_mono (Set.pow_subset_pow_right hA.one_mem h)
  · intro m n
    rintro _ ⟨x, hx, y, hy, rfl⟩
    show ((x * y : C) : G) ∈ A ^ (m + n)
    rw [Subgroup.coe_mul, pow_add]
    exact Set.mul_mem_mul hx hy
  · intro m
    ext x
    simp only [Set.mem_inv, Set.mem_preimage, InvMemClass.coe_inv]
    rw [← Set.mem_inv, inv_pow_eq_self hA.inv_eq_self]
  · intro E m hm
    set E' : Subgroup G := E.map C.subtype with hE'
    have h1 := hA.pow_inter_pow (IsApproximateSubgroup.subgroup (H := E')) hm (le_refl 2)
    rw [coe_set_pow (by norm_num) E'] at h1
    have hsub : A ^ m ∩ (E' : Set G) ⊆ C := by
      rintro _ ⟨-, ⟨y, -, rfl⟩⟩; exact y.2
    have h2 := isApproximateSubgroup_preimage_subtype h1 hsub
    have hset : ((↑) : C → G) ⁻¹' (A ^ m ∩ (E' : Set G)) = ((↑) : C → G) ⁻¹' (A ^ m) ∩ E := by
      ext x
      simp only [Set.mem_preimage, Set.mem_inter_iff, SetLike.mem_coe, hE']
      exact Iff.and Iff.rfl (Subgroup.mem_map_iff_mem C.subtype_injective)
    rw [hset] at h2
    convert h2 using 1
    push_cast
    ring

open Classical in
/-- Transport of the layer data into `C`. -/
lemma layersIn_of_layerData {κ : ℕ} {A : Set G} {k : ℕ} {C : Subgroup G} {D : ℕ → Subgroup G}
    {z : ℕ → G} (hLD : IsLayerData A κ k C D z) :
    LayersIn (fun m => ((↑) : C → G) ⁻¹' (A ^ m)) k (fun i => (D i).subgroupOf C)
      (fun i => if h : z i ∈ C then ⟨z i, h⟩ else 1) := by
  classical
  have hzC : ∀ i, 1 ≤ i → i ≤ k → z i ∈ C := fun i h1 h2 =>
    hLD.hDC (i + 1) (by omega) (by omega) (hLD.hzD i h1 h2)
  have hz' : ∀ i (h1 : 1 ≤ i) (h2 : i ≤ k),
      (if h : z i ∈ C then (⟨z i, h⟩ : C) else 1) = ⟨z i, hzC i h1 h2⟩ := fun i h1 h2 =>
    dif_pos (hzC i h1 h2)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hLD.hDtop, Subgroup.subgroupOf_self]
  · intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hx
    exact hLD.hD1 hx
  · intro i h1 h2 x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hLD.hmono i h1 h2 hx
  · intro i h1 h2
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    push_cast
    exact hLD.hDn i h1 h2 g g.2 n hn
  · intro i h1 h2
    rw [hz' i h1 h2]
    exact hLD.hz6 i h1 h2
  · intro i h1 h2
    rw [hz' i h1 h2, Subgroup.mem_subgroupOf]
    exact hLD.hzD i h1 h2
  · intro i h1 h2 c
    rw [hz' i h1 h2, Subgroup.mem_subgroupOf]
    exact hLD.hcent i h1 h2 c c.2
  · intro i h1 h2 x hx
    rw [hz' i h1 h2]
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨a, ha, y, hy, hxy⟩ := hLD.hstep i h1 h2 hx
    have hnorm : Subgroup.zpowers (z i) ≤ Subgroup.normalizer (D i : Set _) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
      intro h
      have hn := hLD.hDn i (by omega) (by omega)
      refine ⟨fun hh => hn (z i) (hzC i h1 h2) h hh, fun hh => ?_⟩
      have := hn (z i)⁻¹ (C.inv_mem (hzC i h1 h2)) _ hh
      simpa [mul_assoc] using this
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm] at hy
    obtain ⟨w, hw, d, hd, rfl⟩ := hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    have hdC : d ∈ C := hLD.hDC i (by omega) (by omega) hd
    have hwC : z i ^ n ∈ C := C.zpow_mem (hzC i h1 h2) n
    have haC : a ∈ C := by
      have : a = (x : G) * (z i ^ n * d)⁻¹ := by rw [← hxy]; group
      rw [this]; exact C.mul_mem x.2 (C.inv_mem (C.mul_mem hwC hdC))
    refine ⟨⟨a, haC⟩, ha, n, ⟨d, hdC⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]; exact hd
    · apply Subtype.ext
      simp only [Subgroup.coe_mul, SubgroupClass.coe_zpow]
      rw [← hxy, mul_assoc]

/-- **Nilpotent core with explicit uniform bounds.**  Assuming the rank form of the Green–Ruzsa
theorem, every `κ`-approximate subgroup `A` of a finite nilpotent group has a subgroup `C` with
`|A| ≤ κ^(18κ⁶) |A² ∩ C|` and `γ_{κ⁶}(C) ⊆ A^R`, with `R` depending only on `κ`. -/
theorem exists_large_piece_bounded_lcs (hGR : GreenRuzsaRank) {κ : ℕ} (hκ : 1 ≤ κ)
    [Finite G] [Group.IsNilpotent G] {A : Set G} (hA : IsApproximateSubgroup (κ : ℝ) A) :
    ∃ C : Subgroup G, A.ncard ≤ κ ^ (18 * κ ^ 6) * (A ^ 2 ∩ (C : Set G)).ncard ∧
       ((((⊤ : Subgroup C).lowerCentralSeries (κ ^ 6)).map C.subtype : Subgroup G) : Set G) ⊆
        A ^ ((Finset.range (κ ^ 6 + 1)).sup (fun t => (sched hGR κ t).1) + 2) := by
  obtain ⟨k, C, D, z, hLD⟩ := exists_layerData hA
  refine ⟨C, ?_, ?_⟩
  · refine hLD.hcard.trans (Nat.mul_le_mul_right _ ?_)
    exact Nat.pow_le_pow_right hκ (by have := hLD.hk; omega)
  · have hlcs := lcs_subset_of_layers hGR hκ (filt_preimage hA C) (layersIn_of_layerData hLD)
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ (⊤ : Subgroup C).lowerCentralSeries k :=
      (⊤ : Subgroup C).lowerCentralSeries_antitone hLD.hk hy
    have := hlcs hy'
    simp only [Set.mem_preimage] at this
    refine Set.pow_subset_pow_right hA.one_mem ?_ this
    have : (sched hGR κ k).1 ≤ (Finset.range (κ ^ 6 + 1)).sup (fun t => (sched hGR κ t).1) :=
      Finset.le_sup (f := fun t => (sched hGR κ t).1) (Finset.mem_range.2 (by have := hLD.hk; omega))
    omega

end Tointon
