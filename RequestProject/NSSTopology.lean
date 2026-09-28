module
public import Mathlib

/-!
# Elementary no-small-subgroups (NSS) lemmas

* `Lovasz.NSS.HasNoSmallSubgroups`: a topological group is NSS if some identity neighbourhood
  contains no nontrivial subgroup.
* `Lovasz.NSS.exists_power_trapping_of_compact_no_subgroup`: in a Hausdorff topological group, if
  a compact symmetric set `C ∋ 1` contains no nontrivial subgroup, then for every open identity
  neighbourhood `U` there is a finite trapping time `p ≥ 1` such that `g, g², …, g^p ∈ C`
  forces `g ∈ U`.
* `Lovasz.NSS.units_no_small_subgroups`: in the group of units of a real normed algebra, the ball
  `‖u - 1‖ < 1/2` contains no nontrivial subgroup; hence `Eˣ` is NSS
  (`Lovasz.NSS.units_hasNoSmallSubgroups`).
-/

@[expose] public section

open scoped Pointwise Topology

namespace Lovasz.NSS

/-- A topological group has **no small subgroups** (is NSS) if some neighbourhood of the identity
contains no nontrivial subgroup. -/
def HasNoSmallSubgroups (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∃ U ∈ 𝓝 (1 : G), ∀ H : Subgroup G, (H : Set G) ⊆ U → H = ⊥

section PowerTrapping

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

/-- **Compact power trapping.**  Let `C` be a compact symmetric subset of a Hausdorff topological
group, containing `1`, that contains no nontrivial subgroup.  Then for every open neighbourhood
`U` of the identity there is `p ≥ 1` such that, whenever `g, g², …, g^p ∈ C`, we have `g ∈ U`. -/
theorem exists_power_trapping_of_compact_no_subgroup {C U : Set G} (hC : IsCompact C)
    (hCinv : C⁻¹ = C) (hC1 : (1 : G) ∈ C)
    (hno : ∀ H : Subgroup G, (H : Set G) ⊆ C → H = ⊥) (hU : IsOpen U) (hU1 : (1 : G) ∈ U) :
    ∃ p : ℕ, 1 ≤ p ∧ ∀ g : G, (∀ i : ℕ, 1 ≤ i → i ≤ p → g ^ i ∈ C) → g ∈ U := by
  by_contra hcon
  push_neg at hcon
  -- the decreasing closed sets `E n = {g ∉ U : g, …, g^(n+1) ∈ C}`
  set E : ℕ → Set G := fun n => {g | ∀ i : ℕ, 1 ≤ i → i ≤ n + 1 → g ^ i ∈ C} ∩ Uᶜ with hE
  have hEmono : ∀ n, E (n + 1) ⊆ E n := fun n g hg =>
    ⟨fun i hi1 hi2 => hg.1 i hi1 (by omega), hg.2⟩
  have hEne : ∀ n, (E n).Nonempty := fun n => by
    obtain ⟨g, hg, hgU⟩ := hcon (n + 1) (by omega)
    exact ⟨g, hg, hgU⟩
  have hCc : IsClosed C := hC.isClosed
  have hEcl : ∀ n, IsClosed (E n) := by
    intro n
    refine IsClosed.inter ?_ hU.isClosed_compl
    have : {g : G | ∀ i : ℕ, 1 ≤ i → i ≤ n + 1 → g ^ i ∈ C} =
        ⋂ i : ℕ, ⋂ (_ : 1 ≤ i), ⋂ (_ : i ≤ n + 1), (fun g : G => g ^ i) ⁻¹' C := by
      ext g; simp
    rw [this]
    exact isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      hCc.preimage (continuous_pow i)
  have hE0 : IsCompact (E 0) :=
    hC.of_isClosed_subset (hEcl 0) fun g hg => by simpa using hg.1 1 le_rfl le_rfl
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed E hEmono
    hEne hE0 hEcl
  rw [Set.mem_iInter] at hg
  have hpos : ∀ n : ℕ, g ^ n ∈ C := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using hC1
    · exact (hg n).1 n hn (by omega)
  have hsub : ((Subgroup.zpowers g : Subgroup G) : Set G) ⊆ C := by
    rintro _ ⟨k, rfl⟩
    rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
    · simpa using hpos n
    · have : (g ^ n)⁻¹ ∈ C⁻¹ := by simpa using hpos n
      rw [hCinv] at this
      simpa using this
  have hbot := hno _ hsub
  have hg1 : g = 1 := by
    have : g ∈ Subgroup.zpowers g := Subgroup.mem_zpowers g
    rw [hbot] at this
    exact (Subgroup.mem_bot).1 this
  exact (hg 0).2 (hg1 ▸ hU1)

end PowerTrapping

section Units

variable {E : Type*} [NormedRing E] [NormedAlgebra ℝ E]

/-- The key inequality: if `‖x‖ ≤ 1/2` then `‖(1 + x)² - 1‖ ≥ (3/2) ‖x‖`. -/
lemma norm_sq_sub_one_ge {x : E} (hx : ‖x‖ ≤ 1 / 2) :
    3 / 2 * ‖x‖ ≤ ‖(1 + x) * (1 + x) - 1‖ := by
  have e : (1 + x) * (1 + x) - 1 = (2 : ℝ) • x + x * x := by
    rw [two_smul]; noncomm_ring
  rw [e]
  have h1 : ‖(2 : ℝ) • x‖ = 2 * ‖x‖ := by rw [norm_smul]; norm_num
  have h2 : ‖x * x‖ ≤ ‖x‖ * ‖x‖ := norm_mul_le _ _
  have h3 : ‖(2 : ℝ) • x‖ - ‖x * x‖ ≤ ‖(2 : ℝ) • x + x * x‖ := by
    have := norm_sub_le ((2 : ℝ) • x + x * x) (x * x)
    rw [add_sub_cancel_right] at this
    linarith
  have h4 : ‖x‖ * ‖x‖ ≤ 1 / 2 * ‖x‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg _)
  linarith

/-- **Units of a real normed algebra have no small subgroups.**  A subgroup of `Eˣ` all of whose
elements satisfy `‖u - 1‖ < 1/2` is trivial. -/
theorem units_no_small_subgroups (H : Subgroup Eˣ) (hH : ∀ u ∈ H, ‖(u : E) - 1‖ < 1 / 2) :
    H = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot]
  set a : ℕ → ℝ := fun j => ‖((u ^ (2 ^ j) : Eˣ) : E) - 1‖ with ha
  have hlt : ∀ j, a j < 1 / 2 := fun j => hH _ (H.pow_mem hu _)
  have hstep : ∀ j, 3 / 2 * a j ≤ a (j + 1) := by
    intro j
    have := norm_sq_sub_one_ge (x := ((u ^ (2 ^ j) : Eˣ) : E) - 1) (hlt j).le
    simp only [add_sub_cancel] at this
    have e : a (j + 1) = ‖((u ^ (2 ^ j) : Eˣ) : E) * ((u ^ (2 ^ j) : Eˣ) : E) - 1‖ := by
      simp only [ha]; rw [pow_succ, pow_mul, sq, Units.val_mul]
    rw [e]; exact this
  have hgrow : ∀ j, (3 / 2 : ℝ) ^ j * a 0 ≤ a j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc (3 / 2 : ℝ) ^ (j + 1) * a 0 = 3 / 2 * ((3 / 2) ^ j * a 0) := by ring
        _ ≤ 3 / 2 * a j := by gcongr
        _ ≤ a (j + 1) := hstep j
  have ha0 : a 0 = 0 := by
    by_contra hne
    have hpos : 0 < a 0 := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (1 / 2 / a 0) (show (1 : ℝ) < 3 / 2 by norm_num)
    have := hgrow j
    have := hlt j
    rw [div_lt_iff₀ hpos] at hj
    linarith
  have : ((u : Eˣ) : E) - 1 = 0 := by
    simpa [ha] using ha0
  exact Units.ext (sub_eq_zero.1 this)

/-- The group of units of a real normed algebra is NSS. -/
theorem units_hasNoSmallSubgroups : HasNoSmallSubgroups Eˣ := by
  refine ⟨Units.val ⁻¹' {x : E | ‖x - 1‖ < 1 / 2}, ?_, fun H hH =>
    units_no_small_subgroups H fun u hu => hH hu⟩
  apply Units.continuous_val.continuousAt.preimage_mem_nhds
  apply IsOpen.mem_nhds
  · exact isOpen_lt (continuous_id.sub continuous_const).norm continuous_const
  · simp

end Units

end Lovasz.NSS
