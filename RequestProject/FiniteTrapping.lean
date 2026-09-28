module
public import Mathlib
public import RequestProject.FiniteTrappingLayers
public import RequestProject.NSSConj

/-!
# Finite trapping by a pointwise integral argument

`Lovasz.Trapping.finite_trapping`: let `G` be a Hausdorff topological group with a left Haar
measure and `U` a symmetric open identity neighbourhood with compact closure.  For every `a ≥ 0`
there is an open identity neighbourhood `V ⊆ U` such that, whenever `Q` is symmetric, contains
`1`, is contained in the union `Q(V)` of all subgroups inside `V`, and `Qⁿ ⊆ U` with `n ≥ 1`, then
`Q^(a n) ⊆ U⁴`.

The proof uses the finite averages of layer indicators
`ψ = (1/n) ∑_{j<n} 1_{Qʲ U}` and `η = (1/M) ∑_{j<M} 1_{Wʲ U}` (`FiniteTrappingLayers.lean`), and
the function `φ(x) = ∫ ψ(y) η(y⁻¹x) dμ(y)`.  All estimates are pointwise; no continuity of the
convolution and no measurability of `Q` is used.
-/

@[expose] public section

open scoped Pointwise Topology
open MeasureTheory

namespace Lovasz.Trapping

variable {G : Type*} [Group G]

/-- The union `Q(V)` of all subgroups contained in `V`. -/
def smallSubgroupUnion (V : Set G) : Set G :=
  {g | ∃ H : Subgroup G, (H : Set G) ⊆ V ∧ g ∈ H}

lemma pow_mem_of_mem_smallSubgroupUnion {V : Set G} {g : G} (hg : g ∈ smallSubgroupUnion V)
    (i : ℕ) : g ^ i ∈ V := by
  obtain ⟨H, hHV, hgH⟩ := hg
  exact hHV (H.pow_mem hgH i)

/-! ### Bounded compactly supported integrands -/

variable [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

section Integrals

variable (μ : Measure G) [IsFiniteMeasureOnCompacts μ]

omit [Group G] [IsTopologicalGroup G] in
/-- A measurable function bounded by `c` on a compact set `K` and vanishing off `K` is integrable,
with `|∫ F| ≤ c μ(K)`. -/
lemma integrable_and_abs_integral_le {F : G → ℝ} (hF : Measurable F) {K : Set G}
    (hK : IsCompact K) {c : ℝ} (hbound : ∀ y ∈ K, |F y| ≤ c) (hzero : ∀ y ∉ K, F y = 0) :
    Integrable F μ ∧ |∫ y, F y ∂μ| ≤ c * μ.real K := by
  have hKm : MeasurableSet K := hK.measurableSet
  have hle : ∀ y, ‖F y‖ ≤ K.indicator (fun _ => c) y := by
    intro y
    by_cases hy : y ∈ K
    · rw [Set.indicator_of_mem hy, Real.norm_eq_abs]; exact hbound y hy
    · rw [Set.indicator_of_notMem hy, hzero y hy, norm_zero]
  have hint : Integrable (K.indicator fun _ => c) μ :=
    (integrableOn_const (hK.measure_lt_top.ne)).integrable_indicator hKm
  refine ⟨hint.mono' hF.aestronglyMeasurable (Filter.Eventually.of_forall hle), ?_⟩
  have := norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall hle)
  rw [integral_indicator_const _ hKm, smul_eq_mul, Real.norm_eq_abs] at this
  linarith

/-- The convolution-type integral `φ(x) = ∫ ψ(y) η(y⁻¹x) dμ(y)`. -/
noncomputable def conv (ψ η : G → ℝ) (x : G) : ℝ := ∫ y, ψ y * η (y⁻¹ * x) ∂μ

variable {μ}

omit [T2Space G] in
lemma measurable_conv_integrand {ψ η : G → ℝ} (hψ : Measurable ψ) (hη : Measurable η) (x : G) :
    Measurable fun y => ψ y * η (y⁻¹ * x) :=
  hψ.mul (hη.comp (continuous_inv.mul continuous_const).measurable)

lemma integrable_conv_integrand {ψ η : G → ℝ} (hψ : Measurable ψ) (hη : Measurable η)
    {K : Set G} (hK : IsCompact K) {A : ℝ} (hψb : ∀ y, |ψ y| ≤ A) (hηb : ∀ z, |η z| ≤ 1)
    (hψK : ∀ y ∉ K, ψ y = 0) (x : G) : Integrable (fun y => ψ y * η (y⁻¹ * x)) μ := by
  refine (integrable_and_abs_integral_le μ (measurable_conv_integrand hψ hη x) hK
    (c := A) (fun y _ => ?_) (fun y hy => by simp [hψK y hy])).1
  rw [abs_mul]
  calc |ψ y| * |η (y⁻¹ * x)| ≤ A * 1 :=
        mul_le_mul (hψb y) (hηb _) (abs_nonneg _) ((abs_nonneg _).trans (hψb y))
    _ = A := mul_one A

/-- Pointwise estimate for differences of `φ`: if the two `η`-values differ by at most `c`
whenever `y ∈ K`, then `|φ(x) - φ(x')| ≤ A c μ(K)`. -/
lemma abs_conv_sub_le {ψ η : G → ℝ} (hψ : Measurable ψ) (hη : Measurable η)
    {K : Set G} (hK : IsCompact K) {A : ℝ} (hψb : ∀ y, |ψ y| ≤ A) (hηb : ∀ z, |η z| ≤ 1)
    (hψK : ∀ y ∉ K, ψ y = 0) (x x' : G) {c : ℝ}
    (hη' : ∀ y ∈ K, |η (y⁻¹ * x) - η (y⁻¹ * x')| ≤ c) :
    |conv μ ψ η x - conv μ ψ η x'| ≤ A * c * μ.real K := by
  unfold conv
  rw [← integral_sub (integrable_conv_integrand hψ hη hK hψb hηb hψK x)
    (integrable_conv_integrand hψ hη hK hψb hηb hψK x')]
  have hm : Measurable fun y => ψ y * η (y⁻¹ * x) - ψ y * η (y⁻¹ * x') :=
    (measurable_conv_integrand hψ hη x).sub (measurable_conv_integrand hψ hη x')
  refine (integrable_and_abs_integral_le μ hm hK (c := A * c) (fun y hy => ?_)
    (fun y hy => by simp [hψK y hy])).2
  rw [← mul_sub, abs_mul]
  exact mul_le_mul (hψb y) (hη' y hy) (abs_nonneg _) ((abs_nonneg _).trans (hψb y))

variable [μ.IsMulLeftInvariant]

/-- Left invariance: `φ(q⁻¹x) - φ` is the convolution of the difference `ψ - ψ(q⁻¹ ·)`. -/
lemma conv_sub_conv_translate {ψ η : G → ℝ} (hψ : Measurable ψ) (hη : Measurable η)
    {K : Set G} (hK : IsCompact K) {A : ℝ} (hψb : ∀ y, |ψ y| ≤ A) (hηb : ∀ z, |η z| ≤ 1)
    (hψK : ∀ y ∉ K, ψ y = 0) (q x : G) {K' : Set G} (hK' : IsCompact K')
    (hψK' : ∀ y ∉ K', ψ (q⁻¹ * y) = 0) :
    conv μ ψ η x - conv μ ψ η (q⁻¹ * x) = conv μ (fun y => ψ y - ψ (q⁻¹ * y)) η x := by
  have htr : conv μ ψ η (q⁻¹ * x) = ∫ y, ψ (q⁻¹ * y) * η (y⁻¹ * x) ∂μ := by
    unfold conv
    rw [← integral_mul_left_eq_self (fun z => ψ (q⁻¹ * z) * η (z⁻¹ * x)) q]
    congr 1; ext y
    simp only [inv_mul_cancel_left, mul_inv_rev, mul_assoc]
  have hψq : Measurable fun y => ψ (q⁻¹ * y) := hψ.comp (measurable_const_mul q⁻¹)
  rw [htr]
  unfold conv
  rw [← integral_sub (integrable_conv_integrand hψ hη hK hψb hηb hψK x)
    (integrable_conv_integrand hψq hη hK' (fun y => hψb _) hηb hψK' x)]
  congr 1; ext y; ring

end Integrals

/-! ### The core estimate -/

section Core

variable (μ : Measure G) [μ.IsHaarMeasure]

omit [T2Space G] [MeasurableSpace G] [BorelSpace G] in
lemma isCompact_pow {K : Set G} (hK : IsCompact K) : ∀ n : ℕ, IsCompact (K ^ n)
  | 0 => by rw [pow_zero]; exact isCompact_singleton
  | n + 1 => by rw [pow_succ]; exact (isCompact_pow hK n).mul hK

/-- **Core finite-trapping estimate.**  Let `U` be a symmetric open identity neighbourhood, `K` a
compact set containing `U⁴`, `V ⊆ U`, `W = {k⁻¹ v k : v ∈ V, k ∈ K}` and `M ≥ 1` with `W^M ⊆ U`.
If `Q` is symmetric, contains `1`, lies in `Q(V)`, and `Qⁿ ⊆ U` with `n ≥ 1`, then every
`g ∈ Q^k` satisfies `g ∈ U⁴` as soon as `2 k μ(K) / (n M) < μ(U)`. -/
theorem core_trapping {U K V Q : Set G} (hUo : IsOpen U) (hU1 : (1 : G) ∈ U) (hUinv : U⁻¹ = U)
    (hK : IsCompact K) (hUK : U ^ 4 ⊆ K) (hVU : V ⊆ U) (hVinv : V⁻¹ = V) {M : ℕ} (hM : 1 ≤ M)
    (hWM : BGT.conjSet V K ^ M ⊆ U) (hQinv : Q⁻¹ = Q) (hQ1 : (1 : G) ∈ Q)
    (hQV : Q ⊆ smallSubgroupUnion V) {n : ℕ} (hn : 1 ≤ n) (hQn : Q ^ n ⊆ U) {k : ℕ}
    (hk : 2 * k * μ.real K / (n * M) < μ.real U) : Q ^ k ⊆ U ^ 4 := by
  classical
  set W := BGT.conjSet V K with hWdef
  set ψ := layerAvg (fun j => Q ^ j * U) n with hψdef
  set η := layerAvg (fun j => W ^ j * U) M with hηdef
  set b := μ.real K with hb
  have hU2K : U ^ 2 ⊆ K := (Set.pow_subset_pow_right hU1 (by norm_num)).trans hUK
  have hU3K : U ^ 3 ⊆ K := (Set.pow_subset_pow_right hU1 (by norm_num)).trans hUK
  have hqV : ∀ q ∈ Q, ∀ i : ℕ, q ^ i ∈ V := fun q hq i =>
    pow_mem_of_mem_smallSubgroupUnion (hQV hq) i
  have hV1 : (1 : G) ∈ V := by simpa using hqV 1 hQ1 0
  have hQi : ∀ q ∈ Q, q⁻¹ ∈ Q := fun q hq => hQinv ▸ Set.inv_mem_inv.2 hq
  have hVi : ∀ v ∈ V, v⁻¹ ∈ V := fun v hv => hVinv ▸ Set.inv_mem_inv.2 hv
  have hUi : ∀ u ∈ U, u⁻¹ ∈ U := fun u hu => hUinv ▸ Set.inv_mem_inv.2 hu
  have hWmem : ∀ v ∈ V, ∀ y ∈ K, y⁻¹ * v * y ∈ W := fun v hv y hy => ⟨v, hv, y, hy, rfl⟩
  have hWi : ∀ w ∈ W, w⁻¹ ∈ W := by
    rintro _ ⟨v, hv, y, hy, rfl⟩
    exact ⟨v⁻¹, hVi v hv, y, hy, by group⟩
  have hK1 : (1 : G) ∈ K := hUK (Set.one_mem_pow hU1)
  have hW1 : (1 : G) ∈ W := ⟨1, hV1, 1, hK1, by group⟩
  -- the layer function `ψ`
  have hψm : Measurable ψ :=
    measurable_layerAvg (fun j => (hUo.mul_left (s := Q ^ j)).measurableSet) n
  have hψb : ∀ y, |ψ y| ≤ 1 := abs_layerAvg_le_one _ _
  have hψsupp : ∀ y ∉ U ^ 2, ψ y = 0 := by
    intro y hy
    refine layerAvg_eq_zero fun j hj hyj => hy ?_
    rw [pow_two]
    exact Set.mul_subset_mul_right
      ((Set.pow_subset_pow_right hQ1 hj.le).trans hQn) hyj
  have hψK : ∀ y ∉ K, ψ y = 0 := fun y hy => hψsupp y fun h => hy (hU2K h)
  have hψ1 : ∀ y ∈ U, ψ y = 1 := fun y hy =>
    layerAvg_eq_one hn fun j _ => ⟨1, Set.one_mem_pow hQ1, y, hy, one_mul y⟩
  have hψQ : ∀ q ∈ Q, ∀ y, |ψ y - ψ (q⁻¹ * y)| ≤ (n : ℝ)⁻¹ := by
    intro q hq y
    refine abs_layerAvg_sub_le n (fun j hj => ?_) (fun j hj => ?_)
    · rw [pow_succ', mul_assoc]; exact Set.mul_mem_mul (hQi q hq) hj
    · have := Set.mul_mem_mul hq hj
      rw [mul_inv_cancel_left, ← mul_assoc, ← pow_succ'] at this
      exact this
  -- the layer function `η`
  have hηm : Measurable η :=
    measurable_layerAvg (fun j => (hUo.mul_left (s := W ^ j)).measurableSet) M
  have hηb : ∀ z, |η z| ≤ 1 := abs_layerAvg_le_one _ _
  have hηsupp : ∀ z ∉ U ^ 2, η z = 0 := by
    intro z hz
    refine layerAvg_eq_zero fun j hj hzj => hz ?_
    rw [pow_two]
    exact Set.mul_subset_mul_right
      ((Set.pow_subset_pow_right hW1 hj.le).trans hWM) hzj
  have hη1 : ∀ z ∈ U, η z = 1 := fun z hz =>
    layerAvg_eq_one hM fun j _ => ⟨1, Set.one_mem_pow hW1, z, hz, one_mul z⟩
  have hηW : ∀ w ∈ W, ∀ z, |η z - η (w⁻¹ * z)| ≤ (M : ℝ)⁻¹ := by
    intro w hw z
    refine abs_layerAvg_sub_le M (fun j hj => ?_) (fun j hj => ?_)
    · rw [pow_succ', mul_assoc]; exact Set.mul_mem_mul (hWi w hw) hj
    · have := Set.mul_mem_mul hw hj
      rw [mul_inv_cancel_left, ← mul_assoc, ← pow_succ'] at this
      exact this
  have hηconj : ∀ h ∈ V, ∀ y ∈ K, ∀ x,
      |η (y⁻¹ * x) - η (y⁻¹ * (h⁻¹ * x))| ≤ (M : ℝ)⁻¹ := by
    intro h hh y hy x
    have := hηW _ (hWmem h hh y hy) (y⁻¹ * x)
    convert this using 4
    group
  -- the function `φ`
  set φ := conv μ ψ η with hφdef
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hb0 : 0 ≤ b := measureReal_nonneg
  have hφh : ∀ h ∈ V, ∀ x, |φ x - φ (h⁻¹ * x)| ≤ b / M := by
    intro h hh x
    have := abs_conv_sub_le (μ := μ) hψm hηm hK hψb hηb hψK x (h⁻¹ * x)
      (fun y hy => hηconj h hh y hy x)
    calc _ ≤ 1 * (M : ℝ)⁻¹ * b := this
      _ = b / M := by ring
  have hΦ : ∀ q ∈ Q, ∀ h ∈ V, ∀ x,
      |(φ x - φ (q⁻¹ * x)) - (φ (h⁻¹ * x) - φ (q⁻¹ * (h⁻¹ * x)))| ≤ b / (n * M) := by
    intro q hq h hh x
    have hψqK : ∀ y ∉ K, ψ (q⁻¹ * y) = 0 := by
      intro y hy
      refine hψsupp _ fun hy2 => hy (hU3K ?_)
      have := Set.mul_mem_mul (hVU (by simpa using hqV q hq 1)) hy2
      rwa [mul_inv_cancel_left, ← pow_succ'] at this
    rw [conv_sub_conv_translate hψm hηm hK hψb hηb hψK q x hK hψqK,
      conv_sub_conv_translate hψm hηm hK hψb hηb hψK q (h⁻¹ * x) hK hψqK]
    have hDm : Measurable fun y => ψ y - ψ (q⁻¹ * y) :=
      hψm.sub (hψm.comp (measurable_const_mul q⁻¹))
    have hDK : ∀ y ∉ K, ψ y - ψ (q⁻¹ * y) = 0 := fun y hy => by
      rw [hψK y hy, hψqK y hy, sub_zero]
    have := abs_conv_sub_le (μ := μ) hDm hηm hK (hψQ q hq) hηb hDK x (h⁻¹ * x)
      (fun y hy => hηconj h hh y hy x)
    calc _ ≤ (n : ℝ)⁻¹ * (M : ℝ)⁻¹ * b := this
      _ = b / (n * M) := by field_simp
  -- telescoping over the powers of `q`
  have hstep : ∀ q ∈ Q, ∀ x, |φ x - φ (q⁻¹ * x)| ≤ 2 * b / (n * M) := by
    intro q hq x
    set Φ : G → ℝ := fun z => φ z - φ (q⁻¹ * z) with hΦdef
    set f : ℕ → ℝ := fun i => φ ((q ^ i)⁻¹ * x) with hfdef
    have hΦf : ∀ i, Φ ((q ^ i)⁻¹ * x) = f i - f (i + 1) := by
      intro i
      simp only [hΦdef, hfdef, pow_succ, mul_inv_rev, mul_assoc]
    have hkey : (n : ℝ) * Φ x = (f 0 - f n) +
        ∑ i ∈ Finset.range n, (Φ x - Φ ((q ^ i)⁻¹ * x)) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        Finset.sum_congr rfl fun i _ => hΦf i, Finset.sum_range_sub']
      ring
    have hf0 : f 0 = φ x := by simp [hfdef]
    have h1 : |f 0 - f n| ≤ b / M := by rw [hf0]; exact hφh _ (hqV q hq n) x
    have h2 : |∑ i ∈ Finset.range n, (Φ x - Φ ((q ^ i)⁻¹ * x))| ≤ n * (b / (n * M)) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i ∈ Finset.range n, |Φ x - Φ ((q ^ i)⁻¹ * x)|
          ≤ ∑ _i ∈ Finset.range n, b / (n * M) :=
            Finset.sum_le_sum fun i _ => hΦ q hq _ (hqV q hq i) x
        _ = n * (b / (n * M)) := by simp
    have h3 : |(n : ℝ) * Φ x| ≤ 2 * b / M := by
      rw [hkey]
      refine (abs_add_le _ _).trans ?_
      calc |f 0 - f n| + |∑ i ∈ Finset.range n, (Φ x - Φ ((q ^ i)⁻¹ * x))|
          ≤ b / M + n * (b / (n * M)) := add_le_add h1 h2
        _ = 2 * b / M := by field_simp; ring
    rw [abs_mul, abs_of_pos hnpos] at h3
    change |Φ x| ≤ _
    rw [le_div_iff₀ (by positivity)]
    calc |Φ x| * (n * M) = (n * |Φ x|) * M := by ring
      _ ≤ (2 * b / M) * M := by gcongr
      _ = 2 * b := by field_simp
  -- words of length `j`
  have hword : ∀ j : ℕ, ∀ g ∈ Q ^ j, ∀ x, |φ x - φ (g⁻¹ * x)| ≤ j * (2 * b / (n * M)) := by
    intro j
    induction j with
    | zero =>
      intro g hg x
      rw [pow_zero, Set.mem_one] at hg
      subst hg
      simp
    | succ j ih =>
      intro g hg x
      rw [pow_succ] at hg
      obtain ⟨g', hg', q, hq, rfl⟩ := hg
      have e : (g' * q)⁻¹ * x = q⁻¹ * (g'⁻¹ * x) := by group
      rw [e]
      calc |φ x - φ (q⁻¹ * (g'⁻¹ * x))|
          ≤ |φ x - φ (g'⁻¹ * x)| + |φ (g'⁻¹ * x) - φ (q⁻¹ * (g'⁻¹ * x))| := abs_sub_le _ _ _
        _ ≤ j * (2 * b / (n * M)) + 2 * b / (n * M) := add_le_add (ih g' hg' x) (hstep q hq _)
        _ = ((j + 1 : ℕ) : ℝ) * (2 * b / (n * M)) := by push_cast; ring
  -- `φ(1) ≥ μ(U)` and the support of `φ`
  have hφ1 : μ.real U ≤ φ 1 := by
    have hint := integrable_conv_integrand (μ := μ) hψm hηm hK hψb hηb hψK 1
    have hUint : Integrable (U.indicator fun _ => (1 : ℝ)) μ :=
      (integrableOn_const ((measure_mono (hU2K.trans' (by
        rw [pow_two]; exact Set.subset_mul_left U hU1))).trans_lt
          hK.measure_lt_top).ne).integrable_indicator hUo.measurableSet
    have := integral_mono hUint hint (fun y => by
      by_cases hy : y ∈ U
      · rw [Set.indicator_of_mem hy, hψ1 y hy, mul_one, hη1 _ (hUi y hy), mul_one]
      · rw [Set.indicator_of_notMem hy]
        exact mul_nonneg (layerAvg_nonneg _ _ _) (layerAvg_nonneg _ _ _))
    rwa [integral_indicator_const _ hUo.measurableSet, smul_eq_mul, mul_one] at this
  have hφsupp : ∀ x, φ x ≠ 0 → x ∈ U ^ 4 := by
    intro x hx
    by_contra hxU
    apply hx
    have : (fun y => ψ y * η (y⁻¹ * x)) = fun _ => 0 := by
      funext y
      by_contra hne
      rcases mul_ne_zero_iff.1 hne with ⟨h1, h2⟩
      have hy := not_not.1 (mt (hψsupp y) h1)
      have hy' := not_not.1 (mt (hηsupp _) h2)
      apply hxU
      have := Set.mul_mem_mul hy hy'
      rwa [mul_inv_cancel_left, ← pow_add] at this
    change ∫ y, ψ y * η (y⁻¹ * x) ∂μ = 0
    rw [this, integral_zero]
  -- conclusion
  intro g hg
  have hbound := hword k g hg 1
  have hlt : (k : ℝ) * (2 * b / (n * M)) < μ.real U := by
    calc (k : ℝ) * (2 * b / (n * M)) = 2 * k * b / (n * M) := by ring
      _ < μ.real U := hk
  have hpos : 0 < φ (g⁻¹ * 1) := by
    have := (abs_le.1 hbound).2
    linarith
  have hmem := hφsupp _ hpos.ne'
  rw [mul_one] at hmem
  have : g ∈ (U ^ 4)⁻¹ := Set.inv_mem_inv.1 (by simpa using hmem)
  rwa [← inv_pow, hUinv] at this

include μ in
/-- **Finite trapping** (measure form).  Let `U` be a symmetric open identity neighbourhood with
compact closure in a Hausdorff topological group carrying a left Haar measure `μ`.  For every `a` there is a
symmetric open identity neighbourhood `V ⊆ U` such that, whenever `Q` is symmetric, contains `1`,
is contained in the union `Q(V)` of all subgroups inside `V`, `n ≥ 1` and `Qⁿ ⊆ U`, one has
`Q^(a n) ⊆ U⁴`. -/
theorem finite_trapping_of_haar {U : Set G} (hUo : IsOpen U) (hU1 : (1 : G) ∈ U) (hUinv : U⁻¹ = U)
    (hUc : IsCompact (closure U)) (a : ℕ) :
    ∃ V : Set G, IsOpen V ∧ (1 : G) ∈ V ∧ V⁻¹ = V ∧ V ⊆ U ∧
      ∀ Q : Set G, Q⁻¹ = Q → (1 : G) ∈ Q → Q ⊆ smallSubgroupUnion V →
        ∀ n : ℕ, 1 ≤ n → Q ^ n ⊆ U → Q ^ (a * n) ⊆ U ^ 4 := by
  set K := closure U ^ 4 with hKdef
  have hK : IsCompact K := isCompact_pow hUc 4
  have hUK : U ^ 4 ⊆ K := Set.pow_subset_pow_left subset_closure
  have hu : 0 < μ.real U := by
    have h1 : 0 < μ U := hUo.measure_pos μ ⟨1, hU1⟩
    have h2 : μ U < ⊤ := (measure_mono subset_closure).trans_lt hUc.measure_lt_top
    exact ENNReal.toReal_pos h1.ne' h2.ne
  set b := μ.real K with hb
  have hb0 : 0 ≤ b := measureReal_nonneg
  set M : ℕ := ⌈2 * a * b / μ.real U⌉₊ + 1 with hMdef
  have hM : 1 ≤ M := by omega
  have hMgt : 2 * a * b / μ.real U < M := by
    rw [hMdef]; push_cast
    exact (Nat.le_ceil _).trans_lt (lt_add_one _)
  obtain ⟨W, hWo, hW1, hWinv, hWM⟩ :=
    NSS.exists_open_conjSet_pow_subset hK (hUo.mem_nhds hU1) M
  refine ⟨W ∩ U, hWo.inter hUo, ⟨hW1, hU1⟩, by rw [Set.inter_inv, hWinv, hUinv],
    Set.inter_subset_right, ?_⟩
  intro Q hQinv hQ1 hQV n hn hQn
  refine core_trapping μ hUo hU1 hUinv hK hUK Set.inter_subset_right
    (by rw [Set.inter_inv, hWinv, hUinv]) hM ?_ hQinv hQ1 hQV hn hQn ?_
  · refine (Set.pow_subset_pow_left ?_).trans hWM
    rintro _ ⟨v, hv, y, hy, rfl⟩
    exact ⟨v, hv.1, y, hy, rfl⟩
  · have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have : 2 * a * b < μ.real U * M := by rw [div_lt_iff₀ hu] at hMgt; linarith
    rw [div_lt_iff₀ (by positivity)]
    push_cast
    nlinarith

end Core

/-- **Finite trapping.**  Let `U` be a symmetric open identity neighbourhood with compact closure
in a locally compact Hausdorff group.  For every `a` there is a symmetric open identity
neighbourhood `V ⊆ U` such that, whenever `Q` is symmetric, contains `1`, is contained in the union
`Q(V)` of all subgroups inside `V`, `n ≥ 1` and `Qⁿ ⊆ U`, one has `Q^(a n) ⊆ U⁴`. -/
theorem finite_trapping {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] {U : Set G} (hUo : IsOpen U) (hU1 : (1 : G) ∈ U)
    (hUinv : U⁻¹ = U) (hUc : IsCompact (closure U)) (a : ℕ) :
    ∃ V : Set G, IsOpen V ∧ (1 : G) ∈ V ∧ V⁻¹ = V ∧ V ⊆ U ∧
      ∀ Q : Set G, Q⁻¹ = Q → (1 : G) ∈ Q → Q ⊆ smallSubgroupUnion V →
        ∀ n : ℕ, 1 ≤ n → Q ^ n ⊆ U → Q ^ (a * n) ⊆ U ^ 4 := by
  borelize G
  exact finite_trapping_of_haar (Measure.haar : Measure G) hUo hU1 hUinv hUc a

end Lovasz.Trapping
