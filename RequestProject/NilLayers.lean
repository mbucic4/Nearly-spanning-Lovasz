module
public import RequestProject.NilLayersBasic

/-!
# Preliminary layers of an approximate group in a finite nilpotent group

A finite version of Tointon's Proposition 3.1 (*Approximate subgroups of residually nilpotent
groups*).  For a `κ`-approximate subgroup `A` of a finite nilpotent group we construct `k ≤ κ⁶`,
a subgroup `C`, subgroups `D₁ ≤ ⋯ ≤ D_{k+1} = C` normalised by `C`, and elements `zᵢ ∈ A⁶` with

* `D₁ ⊆ A²`, `D_{i+1} ⊆ A² ⟨zᵢ⟩ Dᵢ`, `zᵢ ∈ D_{i+1}`;
* `zᵢ` central in `C` modulo `Dᵢ`;
* `|A| ≤ κ^(18k) |A² ∩ C|`.

The centraliser step uses a variant of Tointon's argument which gives the exponent `18` in
place of `35`.  The construction keeps the generation invariant `C = ⟨A² ∩ C⟩ Hⱼ` and the escaping
elements `zⱼ ∉ A² H_{j-1}`, which bound the number of steps by the packing lemma.
-/

@[expose] public section

open scoped Pointwise
open scoped commutatorElement

namespace Tointon

variable {G : Type*} [Group G]

/-- `H₀ = ⊥` and `Hᵢ = ⟨zᵢ⟩ Dᵢ` for `i ≥ 1`. -/
def layerH (D : ℕ → Subgroup G) (z : ℕ → G) (i : ℕ) : Subgroup G :=
  if i = 0 then ⊥ else Subgroup.zpowers (z i) ⊔ D i

/-- The invariants maintained at stage `j` of the layer construction. -/
structure LayerState (A : Set G) (κ j : ℕ) (C : Subgroup G) (D : ℕ → Subgroup G) (z : ℕ → G) :
    Prop where
  hHC : layerH D z j ≤ C
  hHn : NormalIn (layerH D z j) C
  hgen : C ≤ Subgroup.closure (A ^ 2 ∩ (C : Set G)) ⊔ layerH D z j
  hcard : A.ncard ≤ κ ^ (18 * j) * (A ^ 2 ∩ (C : Set G)).ncard
  hHD : ∀ i, 1 ≤ i → i ≤ j → layerH D z (i - 1) ≤ D i
  hDsub : ∀ i, 1 ≤ i → i ≤ j → (D i : Set G) ⊆ A ^ 2 * (layerH D z (i - 1) : Set G)
  hDn : ∀ i, 1 ≤ i → i ≤ j → NormalIn (D i) C
  hcent : ∀ i, 1 ≤ i → i ≤ j → ∀ c ∈ C, ⁅z i, c⁆ ∈ D i
  hz6 : ∀ i, 1 ≤ i → i ≤ j → z i ∈ A ^ 6
  hzesc : ∀ i, 1 ≤ i → i ≤ j → z i ∉ A ^ 2 * (layerH D z (i - 1) : Set G)

/-- The output of the layer construction. -/
structure IsLayerData (A : Set G) (κ k : ℕ) (C : Subgroup G) (D : ℕ → Subgroup G) (z : ℕ → G) :
    Prop where
  hk : k ≤ κ ^ 6
  hDtop : D (k + 1) = C
  hD1 : (D 1 : Set G) ⊆ A ^ 2
  hmono : ∀ i, 1 ≤ i → i ≤ k → D i ≤ D (i + 1)
  hDC : ∀ i, 1 ≤ i → i ≤ k + 1 → D i ≤ C
  hDn : ∀ i, 1 ≤ i → i ≤ k + 1 → NormalIn (D i) C
  hz6 : ∀ i, 1 ≤ i → i ≤ k → z i ∈ A ^ 6
  hzD : ∀ i, 1 ≤ i → i ≤ k → z i ∈ D (i + 1)
  hcent : ∀ i, 1 ≤ i → i ≤ k → ∀ c ∈ C, ⁅z i, c⁆ ∈ D i
  hstep : ∀ i, 1 ≤ i → i ≤ k →
    (D (i + 1) : Set G) ⊆ A ^ 2 * ((Subgroup.zpowers (z i) ⊔ D i : Subgroup G) : Set G)
  hcard : A.ncard ≤ κ ^ (18 * k) * (A ^ 2 ∩ (C : Set G)).ncard

variable {A : Set G} {κ j : ℕ} {C : Subgroup G} {D : ℕ → Subgroup G} {z : ℕ → G}

lemma layerH_zero : layerH D z 0 = ⊥ := by simp [layerH]

lemma layerH_of_ne {i : ℕ} (hi : i ≠ 0) : layerH D z i = Subgroup.zpowers (z i) ⊔ D i := by
  simp [layerH, hi]

lemma mem_layerH_self {i : ℕ} (hi : i ≠ 0) : z i ∈ layerH D z i := by
  rw [layerH_of_ne hi]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)

lemma LayerState.layerH_mono (hS : LayerState A κ j C D z) :
    ∀ i i', i ≤ i' → i' ≤ j → layerH D z i ≤ layerH D z i' := by
  intro i i' hii' hi'
  induction i', hii' using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih =>
    refine (ih (by omega)).trans ?_
    have h1 := hS.hHD (k + 1) (by omega) hi'
    simp only [Nat.add_sub_cancel] at h1
    rw [layerH_of_ne (Nat.succ_ne_zero k)]
    exact h1.trans le_sup_right

/-- The number of steps is at most `κ⁶`, by the packing lemma applied to the escaping elements. -/
lemma LayerState.le_pow [Finite G] (hA : IsApproximateSubgroup (κ : ℝ) A)
    (hS : LayerState A κ j C D z) : j ≤ κ ^ 6 := by
  classical
  -- `z i` lies in `layerH (i-1)` for no `i`; earlier `z`'s do
  have hfar : ∀ i i', 1 ≤ i' → i' < i → i ≤ j → z i * (z i')⁻¹ ∉ A ^ 2 := by
    intro i i' hi' hii' hij hmem
    apply hS.hzesc i (by omega) hij
    have hz' : z i' ∈ layerH D z (i - 1) :=
      hS.layerH_mono i' (i - 1) (by omega) (by omega) (mem_layerH_self (by omega))
    exact ⟨z i * (z i')⁻¹, hmem, z i', hz', by group⟩
  have hinj : Set.InjOn z (Finset.Icc 1 j : Set ℕ) := by
    intro i hi i' hi' he
    simp only [Finset.coe_Icc, Set.mem_Icc] at hi hi'
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · apply hfar i' i hi.1 h hi'.2
      rw [he, mul_inv_cancel]; exact Set.one_mem_pow hA.one_mem
    · apply hfar i i' hi'.1 h hi.2
      rw [he, mul_inv_cancel]; exact Set.one_mem_pow hA.one_mem
  set U := (Finset.Icc 1 j).image z
  have hU : (U : Set G) ⊆ A ^ 6 := by
    intro x hx
    simp only [U, Finset.coe_image, Finset.coe_Icc, Set.mem_image, Set.mem_Icc] at hx
    obtain ⟨i, ⟨h1, h2⟩, rfl⟩ := hx
    exact hS.hz6 i h1 h2
  have hsep : Separated A U := by
    intro u hu v hv huv
    simp only [U, Finset.mem_image, Finset.mem_Icc] at hu hv
    obtain ⟨i, ⟨hi1, hi2⟩, rfl⟩ := hu
    obtain ⟨i', ⟨hi1', hi2'⟩, rfl⟩ := hv
    have hne : i ≠ i' := fun h => huv (h ▸ rfl)
    rcases lt_or_gt_of_ne hne with h | h
    · intro hmem
      apply hfar i' i hi1 h hi2'
      rw [← inv_pow_eq_self hA.inv_eq_self 2]
      simpa using hmem
    · exact hfar i i' hi1' h hi2
  have hcard := card_le_natPow_of_separated hA hU hsep
  rw [Finset.card_image_of_injOn hinj, Nat.card_Icc, Nat.add_sub_cancel] at hcard
  exact hcard

/-- The initial state: `C₀ = ⟨A²⟩`, `H₀ = ⊥`. -/
lemma layerState_init [Finite G] (hA : IsApproximateSubgroup (κ : ℝ) A) :
    LayerState A κ 0 (Subgroup.closure (A ^ 2)) (fun _ => ⊥) (fun _ => 1) := by
  have hsub : A ^ 2 ∩ ((Subgroup.closure (A ^ 2) : Subgroup G) : Set G) = A ^ 2 :=
    Set.inter_eq_left.2 Subgroup.subset_closure
  refine ⟨by simp [layerH_zero], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [layerH_zero]; intro c _ h hh
    rw [Subgroup.mem_bot] at hh ⊢; rw [hh]; group
  · rw [hsub]; exact le_sup_left
  · rw [hsub]
    simp only [mul_zero, pow_zero, one_mul]
    refine Set.ncard_le_ncard (fun a ha => ?_) (Set.toFinite _)
    rw [pow_two]; exact ⟨a, ha, 1, hA.one_mem, mul_one a⟩
  all_goals intro i h1 h2; omega

/-- Stopping: if `C ⊆ A² Hⱼ`, put `D_{j+1} = C`. -/
lemma LayerState.finish (hS : LayerState A κ j C D z) (hj : j ≤ κ ^ 6)
    (hstop : (C : Set G) ⊆ A ^ 2 * (layerH D z j : Set G)) :
    IsLayerData A κ j C (Function.update D (j + 1) C) z := by
  classical
  have hne : ∀ i, i ≤ j → Function.update D (j + 1) C i = D i := fun i hi =>
    Function.update_of_ne (by omega) _ _
  have hDH : ∀ i, 1 ≤ i → i ≤ j → D i ≤ layerH D z i := fun i hi _ => by
    rw [layerH_of_ne (by omega)]; exact le_sup_right
  have hHC : ∀ i, i ≤ j → layerH D z i ≤ C := fun i hi =>
    (hS.layerH_mono i j hi le_rfl).trans hS.hHC
  refine ⟨hj, Function.update_self _ _ _, ?_, ?_, ?_, ?_, hS.hz6, ?_, ?_, ?_, hS.hcard⟩
  · rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0
      rw [Function.update_self]
      simpa [layerH_zero] using hstop
    · rw [hne 1 hpos]
      simpa [layerH_zero] using hS.hDsub 1 le_rfl hpos
  · intro i hi1 hi2
    rw [hne i hi2]
    rcases eq_or_lt_of_le hi2 with rfl | hlt
    · rw [Function.update_self]; exact (hDH i hi1 le_rfl).trans hS.hHC
    · rw [hne (i + 1) hlt]
      have := hS.hHD (i + 1) (by omega) hlt
      simp only [Nat.add_sub_cancel] at this
      exact (hDH i hi1 hi2).trans this
  · intro i hi1 hi2
    rcases eq_or_lt_of_le hi2 with rfl | hlt
    · rw [Function.update_self]
    · rw [hne i (by omega)]; exact (hDH i hi1 (by omega)).trans (hHC i (by omega))
  · intro i hi1 hi2
    rcases eq_or_lt_of_le hi2 with rfl | hlt
    · rw [Function.update_self]
      intro c hc x hx; exact C.mul_mem (C.mul_mem hc hx) (C.inv_mem hc)
    · rw [hne i (by omega)]; exact hS.hDn i hi1 (by omega)
  · intro i hi1 hi2
    rcases eq_or_lt_of_le hi2 with rfl | hlt
    · rw [Function.update_self]; exact hS.hHC (mem_layerH_self (by omega))
    · rw [hne (i + 1) hlt]
      have := hS.hHD (i + 1) (by omega) hlt
      simp only [Nat.add_sub_cancel] at this
      exact this (mem_layerH_self (by omega))
  · intro i hi1 hi2
    rw [hne i hi2]; exact hS.hcent i hi1 hi2
  · intro i hi1 hi2
    rw [hne i hi2, ← layerH_of_ne (by omega)]
    rcases eq_or_lt_of_le hi2 with rfl | hlt
    · rw [Function.update_self]; exact hstop
    · rw [hne (i + 1) hlt]
      have := hS.hDsub (i + 1) (by omega) hlt
      simpa using this

/-- One step of the construction, when `C ⊄ A² Hⱼ`. -/
lemma LayerState.step [Finite G] [Group.IsNilpotent G] (hA : IsApproximateSubgroup (κ : ℝ) A)
    (hS : LayerState A κ j C D z) (hnot : ¬ (C : Set G) ⊆ A ^ 2 * (layerH D z j : Set G)) :
    ∃ C' D' z', LayerState A κ (j + 1) C' D' z' := by
  classical
  set H := layerH D z j with hHdef
  set P := A ^ 2 ∩ (C : Set G) with hPdef
  have hP1 : (1 : G) ∈ P := ⟨Set.one_mem_pow hA.one_mem, C.one_mem⟩
  have hPinv : P⁻¹ = P := by
    rw [hPdef, Set.inter_inv, inv_pow_eq_self hA.inv_eq_self, inv_coe_set]
  have hPC : P ⊆ C := Set.inter_subset_right
  have hHC : H ≤ C := hS.hHC
  have hHn : NormalIn H C := hS.hHn
  set W := relSeries C H with hW
  let Q : ℕ → Prop := fun l => ∃ g ∈ P ^ 3, g ∈ W l ∧ g ∉ P * (H : Set G)
  obtain ⟨s, hs⟩ := exists_relSeries_le hHC hHn
  have hQs : ¬ Q s := by
    rintro ⟨g, -, hgW, hgn⟩; exact hgn ⟨1, hP1, g, hs hgW, one_mul g⟩
  have hQ0 : Q 0 := by
    by_contra hQ0
    have htrap : ∀ g ∈ P ^ 3, g ∈ W 0 → g ∈ P * (H : Set G) := by
      intro g hg hgW; by_contra hn; exact hQ0 ⟨g, hg, hgW, hn⟩
    set X := trapSubgroup hP1 hPinv hPC (le_relSeries hHC 0) hHn htrap
    have hCX : C ≤ X := hS.hgen.trans (sup_le
      ((Subgroup.closure_le _).2 fun p hp => ⟨⟨p, hp, 1, H.one_mem, mul_one p⟩, hPC hp⟩)
      (fun h hh => ⟨⟨1, hP1, h, hh, one_mul h⟩, hHC hh⟩))
    apply hnot
    intro c hc
    obtain ⟨p, hp, h, hh, e⟩ := (hCX hc).1
    exact ⟨p, hp.1, h, hh, e⟩
  obtain ⟨l, hl⟩ : ∃ l, l = Nat.findGreatest Q s := ⟨_, rfl⟩
  have hQl : Q l := hl ▸ Nat.findGreatest_spec (Nat.zero_le s) hQ0
  have hls : l < s := by
    rcases lt_or_eq_of_le (hl ▸ Nat.findGreatest_le (P := Q) s) with h | h
    · exact h
    · exact absurd (h ▸ hQl) hQs
  have hQl1 : ¬ Q (l + 1) :=
    Nat.findGreatest_is_greatest (P := Q) (n := s) (k := l + 1) (by omega) (by omega)
  have htrap : ∀ g ∈ P ^ 3, g ∈ W (l + 1) → g ∈ P * (H : Set G) := by
    intro g hg hgW; by_contra hn; exact hQl1 ⟨g, hg, hgW, hn⟩
  set D1 := trapSubgroup hP1 hPinv hPC (le_relSeries hHC (l + 1)) hHn htrap with hD1
  have hD1n : NormalIn D1 C :=
    normalIn_trapSubgroup hP1 hPinv hPC _ hHn htrap (relSeries_le hHC _)
      (normalIn_relSeries hHn _) hS.hgen
  have hD1C : D1 ≤ C := fun x hx => relSeries_le hHC (l + 1) hx.2
  obtain ⟨γ, hγ3, hγW, hγn⟩ := hQl
  have hγC : γ ∈ C := relSeries_le hHC l hγW
  have hγ6 : γ ∈ A ^ 6 := by
    have : P ^ 3 ⊆ (A ^ 2) ^ 3 := Set.pow_subset_pow_left Set.inter_subset_left
    rw [← pow_mul] at this
    exact this hγ3
  set G' := centMod C D1 hD1n γ with hG'
  set Hn : Subgroup G := Subgroup.zpowers γ ⊔ D1 with hHn'
  set C' : Subgroup G := Subgroup.closure (A ^ 2 ∩ (G' : Set G)) ⊔ Hn with hC'
  set D' := Function.update D (j + 1) D1 with hD'
  set z' := Function.update z (j + 1) γ with hz'
  have hD'ne : ∀ i, i ≤ j → D' i = D i := fun i hi => Function.update_of_ne (by omega) _ _
  have hz'ne : ∀ i, i ≤ j → z' i = z i := fun i hi => Function.update_of_ne (by omega) _ _
  have hlayer_eq : ∀ i, i ≤ j → layerH D' z' i = layerH D z i := by
    intro i hi
    unfold layerH
    rw [hD'ne i hi, hz'ne i hi]
  have hlayer_new : layerH D' z' (j + 1) = Hn := by
    rw [layerH_of_ne (Nat.succ_ne_zero j), hD', hz', Function.update_self, Function.update_self]
  have hD1G' : D1 ≤ G' := by
    intro d hd
    refine ⟨hD1C hd, ?_⟩
    rw [commutatorElement_def]
    exact D1.mul_mem (hD1n γ hγC d hd) (D1.inv_mem hd)
  have hγG' : γ ∈ G' := ⟨hγC, by simp [D1.one_mem]⟩
  have hHnG' : Hn ≤ G' := sup_le (Subgroup.zpowers_le.2 hγG') hD1G'
  have hC'G' : C' ≤ G' := sup_le ((Subgroup.closure_le _).2 Set.inter_subset_right) hHnG'
  have hC'C : C' ≤ C := fun g hg => (hC'G' hg).1
  have hset : A ^ 2 ∩ (C' : Set G) = A ^ 2 ∩ (G' : Set G) := by
    apply Set.Subset.antisymm
    · exact fun x hx => ⟨hx.1, hC'G' hx.2⟩
    · exact fun x hx => ⟨hx.1, Subgroup.mem_sup_left (Subgroup.subset_closure hx)⟩
  have hHD1 : H ≤ D1 := fun h hh => ⟨⟨1, hP1, h, hh, one_mul h⟩, le_relSeries hHC (l + 1) hh⟩
  refine ⟨C', D', z', ?_⟩
  constructor
  · rw [hlayer_new]; exact le_sup_right
  · rw [hlayer_new]
    refine normalIn_sup ?_ ?_ rfl
    · intro c hc x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [← conj_zpow]
      refine Subgroup.zpow_mem _ ?_ k
      have hc' := (hC'G' hc).2
      have e : c * γ * c⁻¹ = ⁅γ, c⁆⁻¹ * γ := by simp only [commutatorElement_def]; group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (D1.inv_mem hc'))
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers γ))
    · intro c hc x hx
      exact Subgroup.mem_sup_right (hD1n c (hC'C hc) x hx)
  · rw [hlayer_new, hset]
  · have h1 := hS.hcard
    have h2 := card_le_centMod hA hD1n (W := W (l + 1))
      (fun x hx => ⟨⟨x, ⟨hx.1, relSeries_le hHC (l + 1) hx.2⟩, 1, H.one_mem, mul_one x⟩, hx.2⟩)
      hγ6 (fun x hx => commutator_mem_relSeries hγW hx.2)
    rw [← hset] at h2
    calc A.ncard ≤ κ ^ (18 * j) * P.ncard := h1
      _ ≤ κ ^ (18 * j) * (κ ^ 18 * (A ^ 2 ∩ (C' : Set G)).ncard) := Nat.mul_le_mul_left _ h2
      _ = κ ^ (18 * (j + 1)) * (A ^ 2 ∩ (C' : Set G)).ncard := by ring
  · intro i hi1 hi2
    rcases eq_or_lt_of_le hi2 with rfl | hlt
    · rw [Nat.add_sub_cancel, hlayer_eq j le_rfl, hD', Function.update_self]; exact hHD1
    · rw [hlayer_eq (i - 1) (by omega), hD'ne i (by omega)]; exact hS.hHD i hi1 (by omega)
  · intro i hi1 hi2
    rcases eq_or_lt_of_le hi2 with rfl | hlt
    · rw [Nat.add_sub_cancel, hlayer_eq j le_rfl, hD', Function.update_self]
      rintro x ⟨⟨p, hp, h, hh, rfl⟩, -⟩
      exact ⟨p, hp.1, h, hh, rfl⟩
    · rw [hlayer_eq (i - 1) (by omega), hD'ne i (by omega)]; exact hS.hDsub i hi1 (by omega)
  · intro i hi1 hi2
    rcases eq_or_lt_of_le hi2 with rfl | hlt
    · rw [hD', Function.update_self]; exact hD1n.mono hC'C
    · rw [hD'ne i (by omega)]; exact (hS.hDn i hi1 (by omega)).mono hC'C
  · intro i hi1 hi2 c hc
    rcases eq_or_lt_of_le hi2 with rfl | hlt
    · rw [hD', hz', Function.update_self, Function.update_self]; exact (hC'G' hc).2
    · rw [hD'ne i (by omega), hz'ne i (by omega)]; exact hS.hcent i hi1 (by omega) c (hC'C hc)
  · intro i hi1 hi2
    rcases eq_or_lt_of_le hi2 with rfl | hlt
    · rw [hz', Function.update_self]; exact hγ6
    · rw [hz'ne i (by omega)]; exact hS.hz6 i hi1 (by omega)
  · intro i hi1 hi2
    rcases eq_or_lt_of_le hi2 with rfl | hlt
    · rw [Nat.add_sub_cancel, hlayer_eq j le_rfl, hz', Function.update_self]
      rintro ⟨a, ha, h, hh, rfl⟩
      have haC : a ∈ C := by
        have : a = a * h * h⁻¹ := by group
        rw [this]; exact C.mul_mem hγC (C.inv_mem (hHC hh))
      exact hγn ⟨a, ⟨ha, haC⟩, h, hh, rfl⟩
    · rw [hlayer_eq (i - 1) (by omega), hz'ne i (by omega)]; exact hS.hzesc i hi1 (by omega)

/-- **Preliminary layers** (finite form of Tointon's Proposition 3.1). -/
theorem exists_layerData [Finite G] [Group.IsNilpotent G] (hA : IsApproximateSubgroup (κ : ℝ) A) :
    ∃ k C D z, IsLayerData A κ k C D z := by
  classical
  have key : ∀ n, (∃ k C D z, IsLayerData A κ k C D z) ∨ ∃ C D z, LayerState A κ n C D z := by
    intro n
    induction n with
    | zero => exact Or.inr ⟨_, _, _, layerState_init hA⟩
    | succ n ih =>
      rcases ih with h | ⟨C, D, z, hS⟩
      · exact Or.inl h
      · by_cases hc : (C : Set G) ⊆ A ^ 2 * (layerH D z n : Set G)
        · exact Or.inl ⟨n, C, _, z, hS.finish (hS.le_pow hA) hc⟩
        · exact Or.inr (hS.step hA hc)
  rcases key (κ ^ 6 + 1) with h | ⟨C, D, z, hS⟩
  · exact h
  · have := hS.le_pow hA; omega

end Tointon
