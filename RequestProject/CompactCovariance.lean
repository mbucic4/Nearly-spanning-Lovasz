module
public import Mathlib
public import RequestProject.CompactPositiveEigen

/-!
# Covariance operators of an orbit, and detection of a single group element

Let `H` be a compact group with a Haar probability measure `μ`, acting on a real
Hilbert space `E` by linear isometries `π : H →* (E ≃ₗᵢ[ℝ] E)`, assumed only *strongly* continuous
(`h ↦ π h x` continuous for every `x`).

For a vector `v` the covariance operator `covariance μ π v = ∫ h, R (π h v) dμ` averages the
rank-one operators `R w = ⟪w, ·⟫ • w` along the orbit of `v`.  It is compact, symmetric,
nonnegative, positive at `v` (if `v ≠ 0`) and commutes with every `π k`.

The main result is `Lovasz.Covariance.exists_finiteDimensional_invariant_moved`: if `π g ≠ 1`,
there is a finite-dimensional `H`-invariant subspace on which `π g` acts nontrivially.
-/

@[expose] public section

open scoped InnerProductSpace
open MeasureTheory Filter Topology Metric

namespace Lovasz.Covariance

section RankOne

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The rank-one operator `x ↦ ⟪w, x⟫ • w`. -/
noncomputable def rankOne (w : E) : E →L[ℝ] E := (innerSL ℝ w).smulRight w

@[simp] lemma rankOne_apply (w x : E) : rankOne w x = ⟪w, x⟫_ℝ • w := by
  simp [rankOne]

lemma continuous_rankOne : Continuous (rankOne : E → E →L[ℝ] E) := by
  unfold rankOne; fun_prop

/-- `‖R a - R b‖ ≤ (‖a‖ + ‖b‖) ‖a - b‖`. -/
lemma rankOne_norm_sub_le (a b : E) : ‖rankOne a - rankOne b‖ ≤ (‖a‖ + ‖b‖) * ‖a - b‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  have e : (rankOne a - rankOne b) x = ⟪a - b, x⟫_ℝ • a + ⟪b, x⟫_ℝ • (a - b) := by
    simp only [ContinuousLinearMap.sub_apply, rankOne_apply, inner_sub_left, sub_smul, smul_sub]
    abel
  rw [e]
  calc ‖⟪a - b, x⟫_ℝ • a + ⟪b, x⟫_ℝ • (a - b)‖
      ≤ ‖⟪a - b, x⟫_ℝ • a‖ + ‖⟪b, x⟫_ℝ • (a - b)‖ := norm_add_le _ _
    _ ≤ (‖a - b‖ * ‖x‖) * ‖a‖ + (‖b‖ * ‖x‖) * ‖a - b‖ := by
        rw [norm_smul, norm_smul]
        gcongr
        · exact abs_real_inner_le_norm _ _
        · exact abs_real_inner_le_norm _ _
    _ = (‖a‖ + ‖b‖) * ‖a - b‖ * ‖x‖ := by ring

/-- Rank-one operators are compact. -/
lemma isCompactOperator_rankOne (w : E) : IsCompactOperator (rankOne w) := by
  refine (isCompactOperator_iff_image_closedBall_subset_compact
    (rankOne w : E →ₗ[ℝ] E) one_pos).2 ?_
  refine ⟨(fun t : ℝ => t • w) '' Set.Icc (-‖w‖) ‖w‖,
    isCompact_Icc.image (continuous_id.smul continuous_const), ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_closedBall_zero_iff] at hx
  refine ⟨⟪w, x⟫_ℝ, ?_, by simp⟩
  have h1 := abs_real_inner_le_norm w x
  have h2 : ‖w‖ * ‖x‖ ≤ ‖w‖ := by nlinarith [norm_nonneg w]
  exact abs_le.1 (h1.trans h2)

end RankOne

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [MeasurableSpace H] [BorelSpace H]
  (μ : Measure H) [IsProbabilityMeasure μ] [μ.IsHaarMeasure]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (π : H →* (E ≃ₗᵢ[ℝ] E))

/-- The covariance operator `∫ h, R (π h v) dμ(h)` of the orbit of `v`. -/
noncomputable def covariance (v : E) : E →L[ℝ] E := ∫ h, rankOne (π h v) ∂μ

variable {π}

section Continuity

variable (hπ : ∀ x : E, Continuous fun h => π h x)
include hπ

omit [IsTopologicalGroup H] [CompactSpace H] [MeasurableSpace H]
  [BorelSpace H] [CompleteSpace E] in
lemma continuous_rankOne_orbit (v : E) : Continuous fun h => rankOne (π h v) :=
  continuous_rankOne.comp (hπ v)

omit [IsTopologicalGroup H] [IsProbabilityMeasure μ]
  [CompleteSpace E] in
lemma integrable_rankOne_orbit (v : E) : Integrable (fun h => rankOne (π h v)) μ :=
  (continuous_rankOne_orbit hπ v).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

omit [IsTopologicalGroup H] [IsProbabilityMeasure μ] [CompleteSpace E] in
lemma covariance_apply (v x : E) :
    covariance μ π v x = ∫ h, ⟪π h v, x⟫_ℝ • π h v ∂μ := by
  rw [covariance, ContinuousLinearMap.integral_apply (integrable_rankOne_orbit μ hπ v)]
  simp

omit [IsTopologicalGroup H] [IsProbabilityMeasure μ] [CompleteSpace E] in
lemma integrable_orbit_smul (v x : E) :
    Integrable (fun h => ⟪π h v, x⟫_ℝ • π h v) μ := by
  have := (integrable_rankOne_orbit μ hπ v).apply_continuousLinearMap x
  simpa using this

omit [IsTopologicalGroup H] [IsProbabilityMeasure μ] in
lemma covariance_inner (v x y : E) :
    ⟪covariance μ π v x, y⟫_ℝ = ∫ h, ⟪π h v, x⟫_ℝ * ⟪π h v, y⟫_ℝ ∂μ := by
  rw [real_inner_comm, covariance_apply μ hπ, ← integral_inner (integrable_orbit_smul μ hπ v x)]
  congr 1
  ext h
  rw [inner_smul_right, real_inner_comm (π h v) y]

omit [IsTopologicalGroup H] [IsProbabilityMeasure μ] in
lemma covariance_isSymmetric (v x y : E) :
    ⟪covariance μ π v x, y⟫_ℝ = ⟪x, covariance μ π v y⟫_ℝ := by
  rw [covariance_inner μ hπ, real_inner_comm, covariance_inner μ hπ]
  congr 1; ext h; ring

omit [IsTopologicalGroup H] [IsProbabilityMeasure μ] in
lemma covariance_nonneg (v x : E) : 0 ≤ ⟪covariance μ π v x, x⟫_ℝ := by
  rw [covariance_inner μ hπ]
  exact integral_nonneg fun h => mul_self_nonneg _

omit [IsTopologicalGroup H] [IsProbabilityMeasure μ] in
lemma covariance_pos_on_self {v : E} (hv : v ≠ 0) : 0 < ⟪covariance μ π v v, v⟫_ℝ := by
  rw [covariance_inner μ hπ]
  have hc : Continuous fun h => ⟪π h v, v⟫_ℝ * ⟪π h v, v⟫_ℝ := by
    have := Continuous.inner (𝕜 := ℝ) (hπ v) (continuous_const (y := v))
    exact this.mul this
  refine hc.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1)
    (HasCompactSupport.of_compactSpace _) (fun h => mul_self_nonneg _) ?_
  simp only [map_one, LinearIsometryEquiv.coe_one, id_eq, real_inner_self_eq_norm_sq]
  positivity

omit [IsProbabilityMeasure μ] in
lemma covariance_commutes (v x : E) (k : H) :
    π k (covariance μ π v x) = covariance μ π v (π k x) := by
  rw [covariance_apply μ hπ, covariance_apply μ hπ]
  have h1 : π k (∫ h, ⟪π h v, x⟫_ℝ • π h v ∂μ) = ∫ h, π k (⟪π h v, x⟫_ℝ • π h v) ∂μ :=
    ((π k).toLinearIsometry.integral_comp_comm _).symm
  rw [h1, ← integral_mul_left_eq_self (fun h => ⟪π h v, π k x⟫_ℝ • π h v) k]
  congr 1
  ext h
  simp only [map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply, map_smul,
    LinearIsometryEquiv.inner_map_map]

omit [IsTopologicalGroup H] in
lemma covariance_isCompact (v : E) : IsCompactOperator (covariance μ π v) := by
  have hconv : Convex ℝ {T : E →L[ℝ] E | IsCompactOperator T} := by
    intro S hS T hT a b _ _ _
    exact (hS.smul a).add (hT.smul b)
  exact hconv.integral_mem isClosed_setOf_isCompactOperator
    (Filter.Eventually.of_forall fun h => isCompactOperator_rankOne _)
    (integrable_rankOne_orbit μ hπ v)

include μ in
/-- **Single-element detection.**  If `π g` moves some vector, there is a finite-dimensional
subspace, invariant under every `π h`, on which `π g` acts nontrivially. -/
theorem exists_finiteDimensional_invariant_moved {g : H} {x : E} (hx : π g x ≠ x) :
    ∃ V : Submodule ℝ E, FiniteDimensional ℝ V ∧ (∀ h : H, ∀ y ∈ V, π h y ∈ V) ∧
      ∃ w ∈ V, π g w ≠ w := by
  set U := π g with hU
  -- the fixed space of `U` and its orthogonal complement
  set F : Submodule ℝ E :=
    Module.End.eigenspace ((U.toContinuousLinearEquiv : E →L[ℝ] E) : E →ₗ[ℝ] E) 1 with hF
  have hmemF : ∀ y, y ∈ F ↔ U y = y := by
    intro y; simp [hF]
  set M : Submodule ℝ E := Fᗮ with hM
  set v : E := U x - x with hv
  have hv0 : v ≠ 0 := sub_ne_zero.2 hx
  have hvM : v ∈ M := by
    rw [hM, Submodule.mem_orthogonal]
    intro f hf
    have hUf : U f = f := (hmemF f).1 hf
    have : ⟪f, U x⟫_ℝ = ⟪f, x⟫_ℝ := by
      conv_lhs => rw [← hUf]
      exact U.inner_map_map f x
    rw [hv, inner_sub_right, this, sub_self]
  set C := covariance μ π v with hC
  -- `C` preserves `F`, hence (being symmetric) preserves `M`
  have hCF : ∀ f ∈ F, C f ∈ F := by
    intro f hf
    rw [hmemF] at hf ⊢
    rw [hC, hU, covariance_commutes μ hπ, ← hU, hf]
  have hCM : ∀ y ∈ M, C y ∈ M := by
    intro y hy
    rw [hM, Submodule.mem_orthogonal] at hy ⊢
    intro f hf
    rw [← covariance_isSymmetric μ hπ]
    exact hy _ (hCF f hf)
  -- the restriction of `C` to `M`
  set CM : M →L[ℝ] M := (C.comp M.subtypeL).codRestrict M (fun y => hCM y y.2) with hCMdef
  have hCMapply : ∀ y : M, (CM y : E) = C y := fun y => rfl
  have hCMc : IsCompactOperator CM := by
    have h1 : IsCompactOperator (C.comp M.subtypeL) :=
      (covariance_isCompact μ hπ v).comp_clm M.subtypeL
    exact h1.codRestrict (fun y => hCM y y.2) (Submodule.isClosed_orthogonal F)
  obtain ⟨c, hc, w, hw0, hw⟩ := Lovasz.CompactOp.exists_pos_eigenvalue_of_compact_positive CM
    hCMc
    (fun a b => by
      simp only [Submodule.coe_inner, hCMapply]
      exact covariance_isSymmetric μ hπ v a b)
    (fun a => by
      simp only [Submodule.coe_inner, hCMapply]
      exact covariance_nonneg μ hπ v a)
    ⟨⟨v, hvM⟩, by
      simp only [Submodule.coe_inner, hCMapply]
      exact covariance_pos_on_self μ hπ hv0⟩
  have hCw : C w = c • (w : E) := by
    have := congrArg Subtype.val hw
    simpa [hCMapply] using this
  refine ⟨Module.End.eigenspace (C : E →ₗ[ℝ] E) c,
    Lovasz.CompactOp.finiteDimensional_eigenspace_of_compact_ne_zero C
      (covariance_isCompact μ hπ v) hc.ne', ?_, w, ?_, ?_⟩
  · intro h y hy
    rw [Module.End.mem_eigenspace_iff] at hy ⊢
    change C (π h y) = c • π h y
    change C y = c • y at hy
    rw [hC, ← covariance_commutes μ hπ, ← hC, hy, map_smul]
  · rw [Module.End.mem_eigenspace_iff]; exact hCw
  · intro hUw
    have hwF : (w : E) ∈ F := (hmemF w).2 hUw
    have hwM : (w : E) ∈ M := w.2
    have : ⟪(w : E), (w : E)⟫_ℝ = 0 := (Submodule.mem_orthogonal _ _).1 hwM _ hwF
    rw [inner_self_eq_zero] at this
    exact hw0 (Subtype.ext this)

end Continuity

end Lovasz.Covariance
