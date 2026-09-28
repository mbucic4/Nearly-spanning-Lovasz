module
public import Mathlib

/-!
# Two small facts about compact operators

The pinned Mathlib has no spectral theorem for compact operators (in particular neither the
Fredholm alternative `IsCompactOperator.hasEigenvalue_iff_mem_spectrum` nor a real-scalar
spectral-radius/norm identity is available), so the two facts needed for weak Peter–Weyl are proved
directly here.

* `Lovasz.CompactOp.exists_pos_eigenvalue_of_compact_positive`: a compact symmetric operator on a
  real Hilbert space whose quadratic form is nonnegative and somewhere positive has a positive
  eigenvalue (proved with a maximizing sequence for the quadratic form on the unit sphere).
* `Lovasz.CompactOp.finiteDimensional_eigenspace_of_compact_ne_zero`: the eigenspace of a compact
  operator at a nonzero eigenvalue is finite-dimensional.
-/

@[expose] public section

open scoped InnerProductSpace Pointwise
open Filter Topology Metric

namespace Lovasz.CompactOp

section Eigenspace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

omit [CompleteSpace 𝕜] in
/-- The eigenspace `{v | T v = c • v}` of a continuous linear map is closed. -/
lemma isClosed_eigenspace (T : E →L[𝕜] E) (c : 𝕜) :
    IsClosed ((Module.End.eigenspace (T : E →ₗ[𝕜] E) c : Submodule 𝕜 E) : Set E) := by
  have : ((Module.End.eigenspace (T : E →ₗ[𝕜] E) c : Submodule 𝕜 E) : Set E) =
      {v | T v = c • v} := by
    ext v; simp
  rw [this]
  exact isClosed_eq T.continuous (continuous_const_smul c)

/-- **A nonzero eigenspace of a compact operator is finite-dimensional.** -/
theorem finiteDimensional_eigenspace_of_compact_ne_zero (T : E →L[𝕜] E)
    (hT : IsCompactOperator T) {c : 𝕜} (hc : c ≠ 0) :
    FiniteDimensional 𝕜 (Module.End.eigenspace (T : E →ₗ[𝕜] E) c) := by
  set V := Module.End.eigenspace (T : E →ₗ[𝕜] E) c
  obtain ⟨K, hK, hTK⟩ := hT.image_closedBall_subset_compact (1 : ℝ)
  have hKc : IsCompact (closedBall (0 : E) 1 ∩ (c⁻¹ • K)) :=
    (hK.smul c⁻¹).inter_left isClosed_closedBall
  have hemb : Topology.IsClosedEmbedding (Subtype.val : V → E) :=
    (isClosed_eigenspace T c).isClosedEmbedding_subtypeVal
  have hball : closedBall (0 : V) 1 = Subtype.val ⁻¹' (closedBall (0 : E) 1 ∩ (c⁻¹ • K)) := by
    ext ⟨v, hv⟩
    simp only [mem_closedBall, dist_zero_right, Set.mem_preimage, Set.mem_inter_iff]
    constructor
    · intro h
      refine ⟨by simpa using h, ?_⟩
      have hTv : T v = c • v := Module.End.mem_eigenspace_iff.1 hv
      refine ⟨T v, hTK ⟨v, by simpa using h, rfl⟩, ?_⟩
      simp [hTv, smul_smul, inv_mul_cancel₀ hc]
    · rintro ⟨h, -⟩
      simpa using h
  have : IsCompact (closedBall (0 : V) 1) := by
    rw [hball]; exact hemb.isCompact_preimage hKc
  exact FiniteDimensional.of_isCompact_closedBall₀ 𝕜 one_pos this

end Eigenspace

section Positive

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Cauchy–Schwarz for the nonnegative symmetric form `(x, y) ↦ ⟪T x, y⟫`. -/
lemma inner_sq_le_of_nonneg (T : E →L[ℝ] E) (hsym : ∀ x y, ⟪T x, y⟫_ℝ = ⟪x, T y⟫_ℝ)
    (hpos : ∀ x, 0 ≤ ⟪T x, x⟫_ℝ) (x y : E) :
    ⟪T x, y⟫_ℝ ^ 2 ≤ ⟪T x, x⟫_ℝ * ⟪T y, y⟫_ℝ := by
  have key : ∀ t : ℝ, 0 ≤ ⟪T y, y⟫_ℝ * (t * t) + 2 * ⟪T x, y⟫_ℝ * t + ⟪T x, x⟫_ℝ := by
    intro t
    have h := hpos (x + t • y)
    have hyx : ⟪T y, x⟫_ℝ = ⟪T x, y⟫_ℝ := by
      rw [hsym, real_inner_comm]
    simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, RCLike.conj_to_real] at h
    rw [hyx] at h
    nlinarith [h]
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith [this]

/-- **A positive compact operator with a positive quadratic value has a positive eigenvalue.**

Let `T` be a compact symmetric operator on a real Hilbert space with `⟪T x, x⟫ ≥ 0` for all `x`
and `⟪T x₀, x₀⟫ > 0` for some `x₀`.  Then `T v = c • v` for some `c > 0` and `v ≠ 0`. -/
theorem exists_pos_eigenvalue_of_compact_positive (T : E →L[ℝ] E) (hT : IsCompactOperator T)
    (hsym : ∀ x y, ⟪T x, y⟫_ℝ = ⟪x, T y⟫_ℝ) (hpos : ∀ x, 0 ≤ ⟪T x, x⟫_ℝ)
    (hx₀ : ∃ x, 0 < ⟪T x, x⟫_ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∃ v : E, v ≠ 0 ∧ T v = c • v := by
  set q : E → ℝ := fun x => ⟪T x, x⟫_ℝ with hq
  set S : Set ℝ := q '' sphere (0 : E) 1 with hS
  have hqbound : ∀ x, q x ≤ ‖T‖ * ‖x‖ ^ 2 := by
    intro x
    calc q x ≤ ‖T x‖ * ‖x‖ := real_inner_le_norm _ _
      _ ≤ ‖T‖ * ‖x‖ * ‖x‖ := by gcongr; exact T.le_opNorm x
      _ = ‖T‖ * ‖x‖ ^ 2 := by ring
  have hbdd : BddAbove S := ⟨‖T‖, by
    rintro _ ⟨x, hx, rfl⟩
    have := hqbound x
    rw [mem_sphere_zero_iff_norm] at hx
    simpa [hx] using this⟩
  have hqscale : ∀ (x : E) (t : ℝ), q (t • x) = t ^ 2 * q x := by
    intro x t
    simp only [hq, map_smul, inner_smul_left, inner_smul_right, RCLike.conj_to_real]; ring
  -- normalizing
  have hnorm : ∀ x : E, x ≠ 0 → (‖x‖⁻¹ • x) ∈ sphere (0 : E) 1 := by
    intro x hx
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 hx)]
  obtain ⟨x₀, hx₀⟩ := hx₀
  have hx₀ne : x₀ ≠ 0 := by rintro rfl; simp at hx₀
  set c := sSup S with hc
  have hSne : S.Nonempty := ⟨_, ‖x₀‖⁻¹ • x₀, hnorm x₀ hx₀ne, rfl⟩
  have hcpos : 0 < c := by
    have h1 : q (‖x₀‖⁻¹ • x₀) ≤ c := le_csSup hbdd ⟨_, hnorm x₀ hx₀ne, rfl⟩
    have h2 : 0 < q (‖x₀‖⁻¹ • x₀) := by
      rw [hqscale]
      exact mul_pos (by positivity) hx₀
    linarith
  have hqle : ∀ x : E, q x ≤ c * ‖x‖ ^ 2 := by
    intro x
    by_cases hx : x = 0
    · simp [hq, hx]
    have h1 : q (‖x‖⁻¹ • x) ≤ c := le_csSup hbdd ⟨_, hnorm x hx, rfl⟩
    rw [hqscale] at h1
    have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
    rw [inv_pow] at h1
    have := (inv_mul_le_iff₀ (by positivity : (0 : ℝ) < ‖x‖ ^ 2)).1 h1
    linarith
  -- `‖T x‖² ≤ c * q x`
  have hTx : ∀ x : E, ‖T x‖ ^ 2 ≤ c * q x := by
    intro x
    have hcs := inner_sq_le_of_nonneg T hsym hpos x (T x)
    rw [real_inner_self_eq_norm_sq] at hcs
    have h2 := hqle (T x)
    have hq0 := hpos x
    by_cases h0 : ‖T x‖ = 0
    · rw [h0]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact mul_nonneg hcpos.le hq0
    have hpos' : 0 < ‖T x‖ ^ 2 := by positivity
    have : (‖T x‖ ^ 2) ^ 2 ≤ q x * (c * ‖T x‖ ^ 2) :=
      hcs.trans (mul_le_mul_of_nonneg_left h2 hq0)
    nlinarith
  -- the defect estimate on the unit sphere
  have hdefect : ∀ x : E, ‖x‖ = 1 → ‖T x - c • x‖ ^ 2 ≤ c * (c - q x) := by
    intro x hx
    rw [← real_inner_self_eq_norm_sq]
    have hsx : ⟪x, T x⟫_ℝ = q x := by rw [real_inner_comm]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      RCLike.conj_to_real, real_inner_self_eq_norm_sq, hx, hsx]
    have := hTx x
    simp only [hq] at this ⊢
    nlinarith
  -- a maximizing sequence
  have hseq : ∀ n : ℕ, ∃ x : E, ‖x‖ = 1 ∧ c - 1 / ((n : ℝ) + 1) < q x := by
    intro n
    obtain ⟨_, ⟨x, hx, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hSne
      (show c - 1 / ((n : ℝ) + 1) < c by
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith)
    exact ⟨x, by simpa using hx, hlt⟩
  choose x hxn hxq using hseq
  have hdef0 : Tendsto (fun n => T (x n) - c • x n) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hsq : Tendsto (fun n => ‖T (x n) - c • x n‖ ^ 2) atTop (𝓝 0) := by
      have hbnd : Tendsto (fun n : ℕ => c * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
        simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul c
      refine squeeze_zero (fun n => by positivity) (fun n => ?_) hbnd
      have h1 := hdefect (x n) (hxn n)
      have h2 : q (x n) ≤ c := le_csSup hbdd ⟨x n, by simpa using hxn n, rfl⟩
      have h3 := hxq n
      calc ‖T (x n) - c • x n‖ ^ 2 ≤ c * (c - q (x n)) := h1
        _ ≤ c * (1 / ((n : ℝ) + 1)) := by gcongr; linarith
    have := (Real.continuous_sqrt.tendsto 0).comp hsq
    simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this
  -- compactness
  obtain ⟨K, hK, hTK⟩ := hT.image_closedBall_subset_compact (1 : ℝ)
  obtain ⟨y, -, φ, hφ, hy⟩ := hK.tendsto_subseq (x := fun n => T (x n))
    (fun n => hTK ⟨x n, by simp [hxn n], rfl⟩)
  set v : E := c⁻¹ • y with hv
  have hxv : Tendsto (fun n => x (φ n)) atTop (𝓝 v) := by
    have h1 : Tendsto (fun n => T (x (φ n)) - (T (x (φ n)) - c • x (φ n))) atTop (𝓝 (y - 0)) :=
      hy.sub (hdef0.comp hφ.tendsto_atTop)
    have h2 : Tendsto (fun n => c⁻¹ • (T (x (φ n)) - (T (x (φ n)) - c • x (φ n)))) atTop
        (𝓝 (c⁻¹ • (y - 0))) := h1.const_smul c⁻¹
    simpa [smul_smul, inv_mul_cancel₀ hcpos.ne', hv] using h2
  have hTv : T v = c • v := by
    have h1 : Tendsto (fun n => T (x (φ n))) atTop (𝓝 (T v)) :=
      (T.continuous.tendsto v).comp hxv
    have h2 : T v = y := tendsto_nhds_unique h1 hy
    rw [h2, hv, smul_smul, mul_inv_cancel₀ hcpos.ne', one_smul]
  have hvnorm : ‖v‖ = 1 := by
    have h1 : Tendsto (fun n => ‖x (φ n)‖) atTop (𝓝 ‖v‖) := hxv.norm
    have h2 : Tendsto (fun n => ‖x (φ n)‖) atTop (𝓝 1) := by simp [hxn]
    exact tendsto_nhds_unique h1 h2
  exact ⟨c, hcpos, v, fun h => by rw [h] at hvnorm; simp at hvnorm, hTv⟩

end Positive

end Lovasz.CompactOp
