module
public import Mathlib

/-!
# Finite-indicator layer functions

For a sequence of sets `L : ℕ → Set G` and `n ≥ 1`, `layerAvg L n x = (1/n) ∑_{j<n} 1_{L j}(x)`.
These are the bounded measurable functions used in the pointwise-integral proof of finite trapping
(`FiniteTrapping.lean`).  The key estimate `abs_layerAvg_sub_le` is the finite-layer counting
lemma: if membership of `x` in a layer forces membership of `x'` in the next layer and vice versa,
then the two averages differ by at most `1/n`.
-/

@[expose] public section

open scoped Pointwise

namespace Lovasz.Trapping

variable {α : Type*}

/-- The finite average `(1/n) ∑_{j<n} 1_{L j}` of layer indicators. -/
noncomputable def layerAvg (L : ℕ → Set α) (n : ℕ) (x : α) : ℝ :=
  (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, (L j).indicator (fun _ => (1 : ℝ)) x

lemma layerAvg_nonneg (L : ℕ → Set α) (n : ℕ) (x : α) : 0 ≤ layerAvg L n x := by
  unfold layerAvg
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => ?_)
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

lemma sum_indicator_le_card (L : ℕ → Set α) (n : ℕ) (x : α) :
    ∑ j ∈ Finset.range n, (L j).indicator (fun _ => (1 : ℝ)) x ≤ n := by
  calc ∑ j ∈ Finset.range n, (L j).indicator (fun _ => (1 : ℝ)) x
      ≤ ∑ _j ∈ Finset.range n, (1 : ℝ) :=
        Finset.sum_le_sum fun j _ => Set.indicator_le_self' (fun _ _ => zero_le_one) x
    _ = n := by simp

lemma layerAvg_le_one (L : ℕ → Set α) (n : ℕ) (x : α) : layerAvg L n x ≤ 1 := by
  unfold layerAvg
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [inv_mul_le_iff₀ hn', mul_one]
    exact sum_indicator_le_card L n x

lemma abs_layerAvg_le_one (L : ℕ → Set α) (n : ℕ) (x : α) : |layerAvg L n x| ≤ 1 := by
  rw [abs_of_nonneg (layerAvg_nonneg L n x)]; exact layerAvg_le_one L n x

/-- A layer average is `1` at a point lying in all layers `L j`, `j < n`, when `n ≥ 1`. -/
lemma layerAvg_eq_one {L : ℕ → Set α} {n : ℕ} (hn : 1 ≤ n) {x : α}
    (hx : ∀ j < n, x ∈ L j) : layerAvg L n x = 1 := by
  unfold layerAvg
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ)) fun j hj =>
    Set.indicator_of_mem (hx j (Finset.mem_range.1 hj)) _]
  simp [hn']

/-- A layer average vanishes at a point lying in none of the layers `L j`, `j < n`. -/
lemma layerAvg_eq_zero {L : ℕ → Set α} {n : ℕ} {x : α}
    (hx : ∀ j < n, x ∉ L j) : layerAvg L n x = 0 := by
  unfold layerAvg
  rw [Finset.sum_eq_zero fun j hj => Set.indicator_of_notMem (hx j (Finset.mem_range.1 hj)) _]
  simp

lemma mem_of_layerAvg_ne_zero {L : ℕ → Set α} {n : ℕ} {x : α} (hx : layerAvg L n x ≠ 0) :
    ∃ j < n, x ∈ L j := by
  by_contra h
  push_neg at h
  exact hx (layerAvg_eq_zero h)

/-- One-sided finite-layer counting: if `x ∈ L j` forces `x' ∈ L (j+1)`, then the layer count of
`x` exceeds that of `x'` by at most one. -/
lemma sum_indicator_le_succ {L : ℕ → Set α} (n : ℕ) {x x' : α}
    (h : ∀ j, x ∈ L j → x' ∈ L (j + 1)) :
    ∑ j ∈ Finset.range n, (L j).indicator (fun _ => (1 : ℝ)) x ≤
      ∑ j ∈ Finset.range n, (L j).indicator (fun _ => (1 : ℝ)) x' + 1 := by
  have hstep : ∀ j, (L j).indicator (fun _ => (1 : ℝ)) x ≤
      (L (j + 1)).indicator (fun _ => (1 : ℝ)) x' := by
    intro j
    by_cases hj : x ∈ L j
    · rw [Set.indicator_of_mem hj, Set.indicator_of_mem (h j hj)]
    · rw [Set.indicator_of_notMem hj]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have h0 : 0 ≤ (L 0).indicator (fun _ => (1 : ℝ)) x' :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hn1 : (L n).indicator (fun _ => (1 : ℝ)) x' ≤ 1 :=
    Set.indicator_le_self' (fun _ _ => zero_le_one) x'
  calc ∑ j ∈ Finset.range n, (L j).indicator (fun _ => (1 : ℝ)) x
      ≤ ∑ j ∈ Finset.range n, (L (j + 1)).indicator (fun _ => (1 : ℝ)) x' :=
        Finset.sum_le_sum fun j _ => hstep j
    _ = ∑ j ∈ Finset.range (n + 1), (L j).indicator (fun _ => (1 : ℝ)) x' -
          (L 0).indicator (fun _ => (1 : ℝ)) x' := by
        rw [Finset.sum_range_succ']; ring
    _ = ∑ j ∈ Finset.range n, (L j).indicator (fun _ => (1 : ℝ)) x' +
          (L n).indicator (fun _ => (1 : ℝ)) x' - (L 0).indicator (fun _ => (1 : ℝ)) x' := by
        rw [Finset.sum_range_succ]
    _ ≤ _ := by linarith

/-- **Finite-layer counting lemma.**  If `x ∈ L j → x' ∈ L (j+1)` and `x' ∈ L j → x ∈ L (j+1)`
for all `j`, then `|layerAvg L n x - layerAvg L n x'| ≤ 1/n`. -/
lemma abs_layerAvg_sub_le {L : ℕ → Set α} (n : ℕ) {x x' : α}
    (h : ∀ j, x ∈ L j → x' ∈ L (j + 1)) (h' : ∀ j, x' ∈ L j → x ∈ L (j + 1)) :
    |layerAvg L n x - layerAvg L n x'| ≤ (n : ℝ)⁻¹ := by
  have h1 := sum_indicator_le_succ n h
  have h2 := sum_indicator_le_succ n h'
  unfold layerAvg
  rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)]
  calc (n : ℝ)⁻¹ * |_| ≤ (n : ℝ)⁻¹ * 1 := by
        gcongr
        rw [abs_le]; constructor <;> linarith
    _ = _ := mul_one _

/-- Layer averages of measurable layers are measurable. -/
lemma measurable_layerAvg [MeasurableSpace α] {L : ℕ → Set α} (hL : ∀ j, MeasurableSet (L j))
    (n : ℕ) : Measurable (layerAvg L n) := by
  unfold layerAvg
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum _ fun j _ => ?_
  exact measurable_const.indicator (hL j)

end Lovasz.Trapping
