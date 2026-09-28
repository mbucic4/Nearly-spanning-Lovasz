module
public import Mathlib
public import RequestProject.CompactCovariance
public import RequestProject.NSSAssembly

/-!
# Weak Peter–Weyl for compact groups, and compact NSS quotients

* `Lovasz.PeterWeyl.leftReg`: the left regular representation of a compact group on `L²(H, μ)`,
  `(leftReg μ g f)(x) = f (g⁻¹ x)`, by linear isometries.  Its strong continuity is Mathlib's
  continuity of the `Hᵈᵐᵃ`-action on `Lp`.
* `Lovasz.PeterWeyl.leftReg_moves`: the regular representation is faithful.
* `Lovasz.PeterWeyl.exists_invariant_subspace_fixer_subset`: for an open `O ∋ 1` there is a
  finite-dimensional invariant subspace of `L²(H, μ)` whose pointwise fixer lies in `O`
  (covariance operators + single-element detection + compactness of `Oᶜ`).
* `Lovasz.PeterWeyl.weak_peter_weyl`: every compact Hausdorff group has, for each open `O ∋ 1`,
  a continuous orthogonal finite-dimensional representation whose kernel lies in `O`.
* `Lovasz.PeterWeyl.exists_normal_nss_quotient`: there is a closed normal `N ⊆ O` such that `H ⧸ N`
  has no small subgroups, together with the concrete "subgroups near `N` lie in `N`" form used
  in `NSSAssembly.lean`.
-/

@[expose] public section

open scoped ENNReal Pointwise Topology
open MeasureTheory DomMulAct Filter

namespace Lovasz.PeterWeyl

/-! ### Restricting an isometric action to an invariant subspace -/

section Restrict

variable {H : Type*} [Group H] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (π : H →* (E ≃ₗᵢ[ℝ] E)) (V : Submodule ℝ E) (hV : ∀ h : H, ∀ y ∈ V, π h y ∈ V)

/-- The restriction of `π h` to an invariant subspace, as a continuous linear map. -/
noncomputable def restrictCLM (h : H) : V →L[ℝ] V :=
  (((π h).toContinuousLinearEquiv : E →L[ℝ] E).comp V.subtypeL).codRestrict V
    (fun y => hV h y y.2)

@[simp] lemma coe_restrictCLM_apply (h : H) (y : V) :
    ((restrictCLM π V hV h y : V) : E) = π h y := rfl

/-- The restricted representation `H →* (V →L[ℝ] V)ˣ`. -/
noncomputable def restrictRep : H →* (V →L[ℝ] V)ˣ where
  toFun h :=
    { val := restrictCLM π V hV h
      inv := restrictCLM π V hV h⁻¹
      val_inv := by
        ext y
        change π h (π h⁻¹ y) = y
        rw [show π h (π h⁻¹ y) = (π h * π h⁻¹) y from rfl, ← map_mul, mul_inv_cancel, map_one]
        rfl
      inv_val := by
        ext y
        change π h⁻¹ (π h y) = y
        rw [show π h⁻¹ (π h y) = (π h⁻¹ * π h) y from rfl, ← map_mul, inv_mul_cancel, map_one]
        rfl }
  map_one' := by
    ext y
    change π 1 y = y
    rw [map_one]; rfl
  map_mul' g h := by
    ext y
    change π (g * h) y = π g (π h y)
    rw [map_mul]; rfl

lemma restrictRep_apply (h : H) (y : V) :
    (((restrictRep π V hV h : V →L[ℝ] V) y : V) : E) = π h y := rfl

lemma norm_restrictRep_apply (h : H) (y : V) :
    ‖(restrictRep π V hV h : V →L[ℝ] V) y‖ = ‖y‖ := by
  rw [← Submodule.norm_coe, restrictRep_apply, LinearIsometryEquiv.norm_map, Submodule.norm_coe]

lemma restrictRep_eq_one_iff (h : H) :
    restrictRep π V hV h = 1 ↔ ∀ y ∈ V, π h y = y := by
  constructor
  · intro hh y hy
    have := congrArg (fun u : (V →L[ℝ] V)ˣ => (((u : V →L[ℝ] V) ⟨y, hy⟩ : V) : E)) hh
    simpa [restrictRep_apply] using this
  · intro hh
    ext y
    simp [restrictRep_apply, hh y y.2]

lemma continuous_restrictRep [TopologicalSpace H] [IsTopologicalGroup H] [FiniteDimensional ℝ V]
    (hπ : ∀ x : E, Continuous fun h => π h x) : Continuous (restrictRep π V hV) := by
  have hval : ∀ f : H → H, Continuous f →
      Continuous fun h => (restrictCLM π V hV (f h) : V →L[ℝ] V) := by
    intro f hf
    rw [continuous_clm_apply]
    intro y
    exact ((hπ y).comp hf).subtype_mk _
  rw [Units.continuous_iff]
  exact ⟨hval id continuous_id, hval (·⁻¹) continuous_inv⟩

end Restrict

/-! ### The left regular representation -/

section Regular

local instance fact_two_ne_top : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [T2Space H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsHaarMeasure]

/-- The left regular representation of `H` on `L²(H, μ)`: `(leftReg μ g f)(x) = f (g⁻¹ x)`. -/
noncomputable def leftReg : H →* (Lp ℝ 2 μ ≃ₗᵢ[ℝ] Lp ℝ 2 μ) where
  toFun g :=
    { DistribMulAction.toLinearEquiv ℝ (Lp ℝ 2 μ) (mk g⁻¹) with
      norm_map' := norm_smul_Lp _ }
  map_one' := by
    ext1 f
    simp
  map_mul' g h := by
    ext1 f
    simp
    letI : SemigroupAction Hᵈᵐᵃ (Lp ℝ 2 μ) :=
      (inferInstance : MulAction Hᵈᵐᵃ (Lp ℝ 2 μ)).toSemigroupAction
    exact mul_smul ((mk g)⁻¹) ((mk h)⁻¹) f

omit [CompactSpace H] [T2Space H] in
lemma leftReg_apply (g : H) (f : Lp ℝ 2 μ) : leftReg μ g f = mk g⁻¹ • f := rfl

/-- Strong continuity of the left regular representation. -/
lemma continuous_leftReg (f : Lp ℝ 2 μ) : Continuous fun g => leftReg μ g f := by
  simp only [leftReg_apply]
  exact (continuous_mk.comp continuous_inv).smul continuous_const

/-- The left regular representation is faithful. -/
lemma leftReg_moves [IsFiniteMeasure μ] {g : H} (hg : g ≠ 1) : ∃ f, leftReg μ g f ≠ f := by
  obtain ⟨u, hu, hu1, hug⟩ := CompletelyRegularSpace.completely_regular (1 : H) {g⁻¹}
    isClosed_singleton (by simpa [eq_comm] using hg)
  set F : C(H, ℝ) := ⟨fun x => (u x : ℝ), continuous_subtype_val.comp hu⟩ with hF
  set G : C(H, ℝ) := F.comp ⟨fun x => g⁻¹ * x, continuous_const.mul continuous_id⟩ with hG
  refine ⟨ContinuousMap.toLp 2 μ ℝ F, fun heq => ?_⟩
  have htrans : leftReg μ g (ContinuousMap.toLp 2 μ ℝ F) = ContinuousMap.toLp 2 μ ℝ G := by
    apply Lp.ext
    rw [leftReg_apply]
    refine (smul_Lp_ae_eq _ _).trans ?_
    refine EventuallyEq.trans ?_ (ContinuousMap.coeFn_toLp μ G).symm
    have := (measurePreserving_smul g⁻¹ μ).quasiMeasurePreserving.ae_eq_comp
      (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ F)
    simpa [Function.comp_def, hG] using this
  rw [htrans] at heq
  have hGF : G = F := ContinuousMap.toLp_injective μ heq
  have := congrArg (fun k : C(H, ℝ) => k 1) hGF
  simp only [hG, hF, ContinuousMap.comp_apply, ContinuousMap.coe_mk, mul_one] at this
  rw [hug (Set.mem_singleton _), hu1] at this
  simp at this

/-- **Finite-dimensional invariant subspace with small fixer.**  For an open `O ∋ 1` there is a
finite-dimensional subspace of `L²(H, μ)`, invariant under the left regular representation,
such that every `h` fixing it pointwise lies in `O`. -/
theorem exists_invariant_subspace_fixer_subset [IsProbabilityMeasure μ] {O : Set H}
    (hO : IsOpen O) (h1 : (1 : H) ∈ O) :
    ∃ V : Submodule ℝ (Lp ℝ 2 μ), FiniteDimensional ℝ V ∧
      (∀ h : H, ∀ y ∈ V, leftReg μ h y ∈ V) ∧
      ∀ h : H, (∀ y ∈ V, leftReg μ h y = y) → h ∈ O := by
  have hdet : ∀ g : (Oᶜ : Set H), ∃ V : Submodule ℝ (Lp ℝ 2 μ), FiniteDimensional ℝ V ∧
      (∀ h : H, ∀ y ∈ V, leftReg μ h y ∈ V) ∧ ∃ w ∈ V, leftReg μ g w ≠ w := by
    intro g
    have hg : (g : H) ≠ 1 := fun h => g.2 (h ▸ h1)
    obtain ⟨f, hf⟩ := leftReg_moves μ hg
    exact Covariance.exists_finiteDimensional_invariant_moved μ (continuous_leftReg μ) hf
  choose V hVfd hVinv hVmove using hdet
  set W : (Oᶜ : Set H) → Set H := fun g => {h | ∃ w ∈ V g, leftReg μ h w ≠ w} with hW
  have hWo : ∀ g, IsOpen (W g) := by
    intro g
    have : W g = ⋃ w ∈ V g, {h | leftReg μ h w ≠ w} := by ext h; simp [hW]
    rw [this]
    exact isOpen_biUnion fun w _ => isOpen_ne_fun (continuous_leftReg μ w) continuous_const
  have hcover : (Oᶜ : Set H) ⊆ ⋃ g, W g := fun g hg =>
    Set.mem_iUnion.2 ⟨⟨g, hg⟩, hVmove ⟨g, hg⟩⟩
  obtain ⟨t, ht⟩ := hO.isClosed_compl.isCompact.elim_finite_subcover W hWo hcover
  haveI : ∀ g, FiniteDimensional ℝ (V g) := hVfd
  refine ⟨t.sup V, Submodule.finiteDimensional_finset_sup t V, ?_, ?_⟩
  · intro h
    have hle : t.sup V ≤ (t.sup V).comap (leftReg μ h).toLinearEquiv.toLinearMap := by
      refine Finset.sup_le fun g hg => ?_
      intro y hy
      exact Finset.le_sup (f := V) hg (hVinv g h y hy)
    exact fun y hy => hle hy
  · intro h hfix
    by_contra hhO
    obtain ⟨g, hgt, hhg⟩ := Set.mem_iUnion₂.1 (ht hhO)
    obtain ⟨w, hwV, hw⟩ := hhg
    exact hw (hfix w (Finset.le_sup (f := V) hgt hwV))

end Regular

/-! ### Weak Peter–Weyl and the compact NSS quotient -/

section Main

universe u

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [T2Space H]

/-- **Weak Peter–Weyl.**  For every open neighbourhood `O` of the identity in a compact Hausdorff
group `H`, there is a continuous orthogonal representation of `H` on a finite-dimensional real
inner product space whose kernel is contained in `O`. -/
theorem weak_peter_weyl {O : Set H} (hO : IsOpen O) (h1 : (1 : H) ∈ O) :
    ∃ (V : Type u) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℝ V)
      (_ : FiniteDimensional ℝ V) (ρ : H →* (V →L[ℝ] V)ˣ),
      Continuous ρ ∧ (∀ h v, ‖(ρ h : V →L[ℝ] V) v‖ = ‖v‖) ∧ ∀ h, ρ h = 1 → h ∈ O := by
  borelize H
  set μ : Measure H := Measure.haarMeasure ⊤ with hμ
  haveI : IsProbabilityMeasure μ := ⟨by simpa using Measure.haarMeasure_self (G := H) (K₀ := ⊤)⟩
  obtain ⟨V, hfd, hinv, hfix⟩ := exists_invariant_subspace_fixer_subset μ hO h1
  exact ⟨V, inferInstance, inferInstance, hfd, restrictRep (leftReg μ) V hinv,
    continuous_restrictRep _ _ _ (continuous_leftReg μ), norm_restrictRep_apply _ _ _,
    fun h hh => hfix h ((restrictRep_eq_one_iff _ _ _ h).1 hh)⟩

/-- **Compact NSS quotient.**  For every open neighbourhood `O` of the identity in a compact
Hausdorff group `H` there is a closed normal subgroup `N ⊆ O` such that `H ⧸ N` has no small
subgroups.  Concretely, there is an open `O₁` with `N ⊆ O₁ ⊆ O` such that every subgroup contained
in `O₁` lies in `N`. -/
theorem exists_normal_nss_quotient {O : Set H} (hO : IsOpen O) (h1 : (1 : H) ∈ O) :
    ∃ N : Subgroup H, ∃ _ : N.Normal, IsClosed (N : Set H) ∧ (N : Set H) ⊆ O ∧
      NSS.HasNoSmallSubgroups (H ⧸ N) ∧
      ∃ O₁ : Set H, IsOpen O₁ ∧ (N : Set H) ⊆ O₁ ∧ O₁ ⊆ O ∧
        ∀ P : Subgroup H, (P : Set H) ⊆ O₁ → P ≤ N := by
  obtain ⟨V, _, _, _, ρ, hρ, -, hker⟩ := weak_peter_weyl hO h1
  obtain ⟨W, hW, hWsub⟩ := NSS.units_hasNoSmallSubgroups (E := V →L[ℝ] V)
  have hmap : ∀ P : Subgroup H, (P : Set H) ⊆ ρ ⁻¹' W → P ≤ ρ.ker := by
    intro P hP
    have : P.map ρ = ⊥ := hWsub _ (by
      rintro _ ⟨p, hp, rfl⟩
      exact hP hp)
    exact (Subgroup.map_eq_bot_iff P).1 this
  refine ⟨ρ.ker, inferInstance, ?_, fun n hn => hker n hn, ?_, ?_⟩
  · have : (ρ.ker : Set H) = ρ ⁻¹' {1} := by ext; simp
    rw [this]
    exact isClosed_singleton.preimage hρ
  · set ρbar := QuotientGroup.kerLift ρ
    have hρbar : Continuous ρbar :=
      (QuotientGroup.isQuotientMap_mk ρ.ker).continuous_iff.2 hρ
    refine ⟨ρbar ⁻¹' W, hρbar.continuousAt.preimage_mem_nhds (by simpa using hW), ?_⟩
    intro Q hQ
    have : Q.map ρbar = ⊥ := hWsub _ (by
      rintro _ ⟨q, hq, rfl⟩
      exact hQ hq)
    exact (Subgroup.map_eq_bot_iff_of_injective Q (QuotientGroup.kerLift_injective ρ)).1 this
  · refine ⟨ρ ⁻¹' interior W ∩ O, isOpen_interior.preimage hρ |>.inter hO, ?_,
      Set.inter_subset_right, ?_⟩
    · intro n hn
      refine ⟨?_, hker n hn⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker] at hn
      rw [Set.mem_preimage, hn]
      exact mem_interior_iff_mem_nhds.2 hW
    · intro P hP
      exact hmap P fun p hp => interior_subset (s := W) (hP hp).1

end Main

/-! ### Compact subgroups of an ambient group -/

section Ambient

variable {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L] [T2Space L]

/-- **Compact NSS quotient, ambient form.**  Let `H` be a compact subgroup of a Hausdorff
topological group `L` and `O` an open identity neighbourhood of `L`.  There is a compact subgroup
`N ≤ H`, normalised by `H`, with `N ⊆ O`, and an open `O₁` with `N ⊆ O₁ ⊆ O`, such that every
subgroup `P ≤ H` contained in `O₁` lies in `N` (i.e. `H ⧸ N` has no small subgroups).  This is the
compact-group input of `NSS.exists_open_subgroup_nss_quotient`. -/
theorem exists_compact_normal_nss_of_compact_subgroup {H : Subgroup L}
    (hHc : IsCompact (H : Set L)) {O : Set L} (hO : IsOpen O) (h1 : (1 : L) ∈ O) :
    ∃ N : Subgroup L, N ≤ H ∧ IsCompact (N : Set L) ∧ (∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) ∧
      (N : Set L) ⊆ O ∧ ∃ O₁ : Set L, IsOpen O₁ ∧ (N : Set L) ⊆ O₁ ∧ O₁ ⊆ O ∧
        ∀ P : Subgroup L, P ≤ H → (P : Set L) ⊆ O₁ → P ≤ N := by
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 hHc
  obtain ⟨N', hN'n, hN'c, hN'O, -, O₁', hO₁'o, hN'O₁', -, hP'⟩ :=
    exists_normal_nss_quotient (H := H) (O := Subtype.val ⁻¹' O)
      (hO.preimage continuous_subtype_val) h1
  obtain ⟨t, ht, htO₁'⟩ := isOpen_induced_iff.1 hO₁'o
  refine ⟨N'.map H.subtype, Subgroup.map_subtype_le N', ?_, ?_, ?_, t ∩ O, ht.inter hO, ?_,
    Set.inter_subset_right, ?_⟩
  · rw [Subgroup.coe_map]
    exact hN'c.isCompact.image continuous_subtype_val
  · rintro h hh _ ⟨n, hn, rfl⟩
    exact ⟨⟨h, hh⟩ * n * ⟨h, hh⟩⁻¹, hN'n.conj_mem n hn _, by simp⟩
  · rintro _ ⟨n, hn, rfl⟩
    exact hN'O hn
  · rintro _ ⟨n, hn, rfl⟩
    refine ⟨?_, hN'O hn⟩
    have : n ∈ Subtype.val ⁻¹' t := htO₁' ▸ hN'O₁' hn
    exact this
  · intro P hPH hPO₁ p hp
    have hle := hP' (P.subgroupOf H) (by
      intro q hq
      rw [← htO₁']
      exact (hPO₁ (Subgroup.mem_subgroupOf.1 hq)).1)
    exact ⟨⟨p, hPH hp⟩, hle (Subgroup.mem_subgroupOf.2 hp), rfl⟩

/-- **NSS quotient from subgroup trapping.**  If every subgroup contained in an open identity
neighbourhood `U` lies in a compact subgroup `H`, then there are a compact subgroup `N ⊆ U` and an
open subgroup `L₀ ⊇ N`, normalising `N`, such that `L₀ ⧸ N` has no small subgroups.  The only
remaining input is the subgroup-trapping hypothesis `htrap`. -/
theorem exists_open_subgroup_nss_quotient_of_trapping {U : Set L} {H : Subgroup L}
    (hHc : IsCompact (H : Set L)) (hU : IsOpen U) (h1 : (1 : L) ∈ U)
    (htrap : ∀ P : Subgroup L, (P : Set L) ⊆ U → P ≤ H) :
    ∃ N : Subgroup L, IsCompact (N : Set L) ∧ (N : Set L) ⊆ U ∧
      ∃ L₀ : Subgroup L, IsOpen (L₀ : Set L) ∧ N ≤ L₀ ∧
        ∃ _ : (N.subgroupOf L₀).Normal, NSS.HasNoSmallSubgroups (L₀ ⧸ N.subgroupOf L₀) := by
  obtain ⟨N, hNH, hNc, hNn, hNU, O₁, hO₁, hNO₁, hO₁U, hnss⟩ :=
    exists_compact_normal_nss_of_compact_subgroup hHc hU h1
  exact ⟨N, hNc, hNU, NSS.exists_open_subgroup_nss_quotient hNc hNH hNn htrap hO₁ hNO₁ hO₁U hnss⟩

end Ambient

end Lovasz.PeterWeyl
