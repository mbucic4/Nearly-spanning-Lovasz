module
public import Mathlib

/-!
# Ultralimits of sets

For an ultrafilter `𝒰` on an index type `ι` and sets `S i` in a topological space, the
*ultralimit* `ultraLimSet 𝒰 S` is the set of points `x` such that every open neighbourhood of `x`
meets `S i` for `𝒰`-almost every `i`.  (Equivalently it is `⋂_{I ∈ 𝒰} closure (⋃_{i ∈ I} S i)`.)
This replaces Hausdorff-distance limits of compact sets: no hyperspace and no metric are used.

Main facts:
* `ultraLimSet_isClosed`;
* `mem_ultraLimSet_of_tendsto`: ultrafilter limits of points `x i ∈ S i` lie in the ultralimit;
* `ultraLimSet_subset_of_eventually`: if `S i ⊆ C` eventually with `C` closed then the ultralimit
  lies in `C`;
* `eventually_subset_of_ultraLimSet_subset`: if all `S i` lie in a compact `K` and the ultralimit
  lies in an open `O`, then `S i ⊆ O` eventually;
* group facts: `one_mem_ultraLimSet`, `inv_mem_ultraLimSet`, `mul_mem_ultraLimSet`, and
  `ultraLimSet_pow_subset` (`S i ^ j ⊆ C` eventually, `C` closed ⇒ `E ^ j ⊆ C`).
-/

@[expose] public section

open scoped Pointwise Topology
open Filter

namespace Lovasz.Ultralimit

variable {ι X : Type*} [TopologicalSpace X]

/-- The ultralimit of a family of sets along an ultrafilter. -/
def ultraLimSet (𝒰 : Ultrafilter ι) (S : ι → Set X) : Set X :=
  {x | ∀ O : Set X, IsOpen O → x ∈ O → ∀ᶠ i in (𝒰 : Filter ι), (S i ∩ O).Nonempty}

variable {𝒰 : Ultrafilter ι} {S : ι → Set X}

lemma ultraLimSet_isClosed (𝒰 : Ultrafilter ι) (S : ι → Set X) :
    IsClosed (ultraLimSet 𝒰 S) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  simp only [ultraLimSet, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] at hx
  obtain ⟨O, hO, hxO, hev⟩ := hx
  exact ⟨O, fun y hyO hy => hev (hy O hO hyO), hO, hxO⟩

/-- Ultrafilter limits of points of `S i` lie in the ultralimit. -/
lemma mem_ultraLimSet_of_tendsto {x : ι → X} {y : X}
    (hx : ∀ᶠ i in (𝒰 : Filter ι), x i ∈ S i) (hy : Tendsto x (𝒰 : Filter ι) (𝓝 y)) :
    y ∈ ultraLimSet 𝒰 S := by
  intro O hO hyO
  filter_upwards [hx, hy (hO.mem_nhds hyO)] with i hi hi' using ⟨x i, hi, hi'⟩

/-- If eventually `S i ⊆ C` with `C` closed, the ultralimit lies in `C`. -/
lemma ultraLimSet_subset_of_eventually {C : Set X} (hC : IsClosed C)
    (hS : ∀ᶠ i in (𝒰 : Filter ι), S i ⊆ C) : ultraLimSet 𝒰 S ⊆ C := by
  intro x hx
  by_contra hxC
  have := hx Cᶜ hC.isOpen_compl hxC
  obtain ⟨i, hi, hi'⟩ := (this.and hS).exists
  obtain ⟨y, hyS, hyC⟩ := hi
  exact hyC (hi' hyS)

/-- Monotonicity of the ultralimit under eventual inclusion. -/
lemma ultraLimSet_mono {T : ι → Set X} (h : ∀ᶠ i in (𝒰 : Filter ι), S i ⊆ T i) :
    ultraLimSet 𝒰 S ⊆ ultraLimSet 𝒰 T := by
  intro x hx O hO hxO
  filter_upwards [hx O hO hxO, h] with i hi hi'
  obtain ⟨y, hyS, hyO⟩ := hi
  exact ⟨y, hi' hyS, hyO⟩

/-- Points chosen in the `S i` inside a compact set have an ultrafilter limit in the
ultralimit. -/
lemma exists_tendsto_of_isCompact {K : Set X} (hK : IsCompact K) {x : ι → X}
    (hx : ∀ᶠ i in (𝒰 : Filter ι), x i ∈ K) :
    ∃ y ∈ K, Tendsto x (𝒰 : Filter ι) (𝓝 y) := by
  have hle : (𝒰.map x : Filter X) ≤ 𝓟 K := by
    rw [Ultrafilter.coe_map, le_principal_iff]; exact hx
  obtain ⟨y, hyK, hy⟩ := hK.ultrafilter_le_nhds (𝒰.map x) hle
  exact ⟨y, hyK, hy⟩

/-- If the `S i` eventually lie in a compact `K` and the ultralimit lies in an open `O`, then
eventually `S i ⊆ O`. -/
lemma eventually_subset_of_ultraLimSet_subset {K O : Set X} (hK : IsCompact K) (hO : IsOpen O)
    (hSK : ∀ᶠ i in (𝒰 : Filter ι), S i ⊆ K) (hEO : ultraLimSet 𝒰 S ⊆ O) :
    ∀ᶠ i in (𝒰 : Filter ι), S i ⊆ O := by
  by_contra hcon
  have hbad : ∀ᶠ i in (𝒰 : Filter ι), ¬ S i ⊆ O := Ultrafilter.eventually_not.2 hcon
  obtain ⟨i₀, hi₀⟩ := (hbad.and hSK).exists
  have hne : ∀ i, ¬ S i ⊆ O → ∃ z, z ∈ S i ∧ z ∉ O := fun i hi => by
    simpa [Set.not_subset] using hi
  obtain ⟨z₀, -, -⟩ := hne i₀ hi₀.1
  classical
  let x : ι → X := fun i => if h : ¬ S i ⊆ O then (hne i h).choose else z₀
  have hxS : ∀ᶠ i in (𝒰 : Filter ι), x i ∈ S i ∧ x i ∉ O := by
    filter_upwards [hbad] with i hi
    simp only [x, dif_pos hi]
    exact (hne i hi).choose_spec
  have hxK : ∀ᶠ i in (𝒰 : Filter ι), x i ∈ K ∩ Oᶜ := by
    filter_upwards [hxS, hSK] with i hi hi' using ⟨hi' hi.1, hi.2⟩
  obtain ⟨y, hyKO, hy⟩ := exists_tendsto_of_isCompact (hK.inter_right hO.isClosed_compl) hxK
  exact hyKO.2 (hEO (mem_ultraLimSet_of_tendsto (hxS.mono fun i hi => hi.1) hy))

/-! ### Group facts -/

section Group

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {S T : ι → Set G}

omit [IsTopologicalGroup G] in
lemma one_mem_ultraLimSet (h : ∀ᶠ i in (𝒰 : Filter ι), (1 : G) ∈ S i) :
    (1 : G) ∈ ultraLimSet 𝒰 S := fun _ _ h1O => h.mono fun _ hi => ⟨1, hi, h1O⟩

lemma inv_mem_ultraLimSet (h : ∀ᶠ i in (𝒰 : Filter ι), (S i)⁻¹ = S i) {x : G}
    (hx : x ∈ ultraLimSet 𝒰 S) : x⁻¹ ∈ ultraLimSet 𝒰 S := by
  intro O hO hxO
  filter_upwards [hx O⁻¹ hO.inv (by simpa using hxO), h] with i hi hi'
  obtain ⟨y, hyS, hyO⟩ := hi
  refine ⟨y⁻¹, ?_, hyO⟩
  rw [← hi']; simpa using hyS

lemma ultraLimSet_inv_eq (h : ∀ᶠ i in (𝒰 : Filter ι), (S i)⁻¹ = S i) :
    (ultraLimSet 𝒰 S)⁻¹ = ultraLimSet 𝒰 S := by
  ext x
  refine ⟨fun hx => by simpa using inv_mem_ultraLimSet h hx, fun hx => ?_⟩
  simpa using inv_mem_ultraLimSet h hx

lemma mul_mem_ultraLimSet {x y : G} (hx : x ∈ ultraLimSet 𝒰 S) (hy : y ∈ ultraLimSet 𝒰 T) :
    x * y ∈ ultraLimSet 𝒰 (fun i => S i * T i) := by
  intro O hO hxyO
  have hmem : (fun p : G × G => p.1 * p.2) ⁻¹' O ∈ 𝓝 (x, y) :=
    (continuous_mul.isOpen_preimage O hO).mem_nhds hxyO
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.1 hmem
  obtain ⟨A', hA'A, hA'o, hxA'⟩ := mem_nhds_iff.1 hA
  obtain ⟨B', hB'B, hB'o, hyB'⟩ := mem_nhds_iff.1 hB
  filter_upwards [hx A' hA'o hxA', hy B' hB'o hyB'] with i hi hi'
  obtain ⟨a, haS, haA⟩ := hi
  obtain ⟨b, hbT, hbB⟩ := hi'
  exact ⟨a * b, Set.mul_mem_mul haS hbT, hAB (Set.mk_mem_prod (hA'A haA) (hB'B hbB))⟩

lemma ultraLimSet_pow_subset_ultraLimSet_pow (j : ℕ) :
    ultraLimSet 𝒰 S ^ j ⊆ ultraLimSet 𝒰 (fun i => S i ^ j) := by
  induction j with
  | zero =>
    intro x hx
    rw [pow_zero, Set.mem_one] at hx
    subst hx
    exact one_mem_ultraLimSet (Eventually.of_forall fun i => by simp)
  | succ j ih =>
    rintro _ ⟨x, hx, y, hy, rfl⟩
    have := mul_mem_ultraLimSet (ih hx) hy
    simpa [pow_succ] using this

/-- **Power bounds pass to the ultralimit.**  If `S i ^ j ⊆ C` eventually with `C` closed, then
`E ^ j ⊆ C` for the ultralimit `E`. -/
lemma ultraLimSet_pow_subset {C : Set G} (hC : IsClosed C) (j : ℕ)
    (h : ∀ᶠ i in (𝒰 : Filter ι), S i ^ j ⊆ C) : ultraLimSet 𝒰 S ^ j ⊆ C :=
  (ultraLimSet_pow_subset_ultraLimSet_pow j).trans (ultraLimSet_subset_of_eventually hC h)

end Group

end Lovasz.Ultralimit
