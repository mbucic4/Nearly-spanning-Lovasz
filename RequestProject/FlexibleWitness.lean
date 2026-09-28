module
public import Mathlib
public import RequestProject.UltraModel
public import RequestProject.NSSRelativeTools

/-!
# Flexible trapping witnesses in the ultraproduct

Given tower data `T` on an ultraproduct, the model `L = T.L` is a first-countable locally compact
Hausdorff group.  Subgroup trapping and the compact NSS quotient give the compact kernel `N` and an
open `W ⊇ N` with "`⟨W⟩ ⧸ N` NSS" (`NSS.exists_compact_kernel_data`).  We then choose, in this
order (Section 10 of the note, with every neighbourhood of the identity replaced by an
`N`-neighbourhood, i.e. working modulo the compact kernel):

1. a compact symmetric `V ⊇ N` (`N ⊆ interior V`) with `V¹⁰⁰ ⊆ W`;
2. a compact symmetric `F`, `N ⊆ interior F`, `F ⊆ interior V`, and by the full-fibre sandwich an
   internal symmetric `B*` with `π⁻¹(F) ⊆ B* ⊆ π⁻¹(interior V)`;
3. the first trapping time `p` (relative power trapping for `V¹⁰⁰` and `interior F`);
4. a finite cover `B*² ⊆ ⋃ tᵢ B*` with `tᵢ ∈ B*²`, from compactness of `π(B*)`; `κ = max 2 (2k)`;
5. `N_len = 3 p κ` and an open symmetric `O_S ⊇ N` with `(conjSet O_S (V⁴))^{N_len} ⊆ interior F`;
6. a compact symmetric `F_S`, `N ⊆ interior F_S ⊆ F_S ⊆ O_S`, and an internal symmetric `S*` with
   `π⁻¹(F_S) ⊆ S* ⊆ π⁻¹(O_S)`;
7. the second trapping time `m` (relative power trapping for `V` and `interior F_S`).

All word inclusions lift because the lower sandwich contains full fibres.  The size comparison
uses a scale `B j ⊆ B*` of the tower and the tower's finite cover of `A*` by translates of `B j`.
The result `exists_internal_flexible_data` is the internal form of the flexible trapping data,
ready for `Ultra.hasFlexibleTrapping_transfer`.
-/

@[expose] public section

open Filter Topology
open scoped Pointwise

namespace Lovasz.UltraModel

open Ultra

variable {G : ℕ → Type*} [∀ n, Group (G n)] {U : Ultrafilter ℕ}

namespace TowerData

variable (T : TowerData U G)

lemma pow_subset_Γ_of_subset {D : Set (UProd (G := G) U)} (hD : D ⊆ T.Γ) (k : ℕ) :
    D ^ k ⊆ T.Γ := by
  induction k with
  | zero => intro x hx; rw [pow_zero, Set.mem_one] at hx; subst hx; exact T.Γ.one_mem
  | succ k ih =>
    rintro _ ⟨a, ha, d, hd, rfl⟩
    exact T.Γ.mul_mem (ih ha) (hD hd)

/-- Images of products: if `π` maps the elements of `D ⊆ Γ` into `E`, it maps the elements of
`Dᵏ` into `Eᵏ`. -/
lemma π_mem_pow {D : Set (UProd (G := G) U)} (hD : D ⊆ T.Γ) {E : Set T.L}
    (h : ∀ g : T.Γ, (g : UProd (G := G) U) ∈ D → T.π g ∈ E) (k : ℕ) :
    ∀ g : T.Γ, (g : UProd (G := G) U) ∈ D ^ k → T.π g ∈ E ^ k := by
  induction k with
  | zero =>
    intro g hg
    rw [pow_zero, Set.mem_one] at hg
    have : g = 1 := Subtype.ext hg
    subst this
    simp
  | succ k ih =>
    intro g hg
    rw [pow_succ] at hg
    obtain ⟨a, ha, d, hd, hgad⟩ := hg
    have hdΓ : d ∈ T.Γ := hD hd
    have haΓ : a ∈ T.Γ := T.pow_subset_Γ_of_subset hD k ha
    have e : g = ⟨a, haΓ⟩ * ⟨d, hdΓ⟩ := Subtype.ext hgad.symm
    rw [e, map_mul, pow_succ]
    exact Set.mul_mem_mul (ih _ ha) (h _ hd)

/-- **Internal flexible trapping data.**  From tower data one obtains internal sets
`B* = internal U Bs`, `S* = internal U Ss` and numbers `κ, p, m, N_len, k, q, r` satisfying all
hypotheses of `Ultra.hasFlexibleTrapping_transfer`, together with the localisation `B* ⊆ A*^q` and
a cover of `A*` by `r` translates of `B*`. -/
theorem exists_internal_flexible_data :
    ∃ (Bs Ss : ∀ n, Set (G n)) (κ p m Nlen k q r : ℕ) (t : Fin k → ∀ n, G n)
      (y : Fin r → ∀ n, G n),
      2 ≤ κ ∧ 1 ≤ p ∧ 1 ≤ m ∧ 3 * p * κ ≤ Nlen ∧ 2 * k ≤ κ ∧
      (1 : UProd (G := G) U) ∈ internal U Bs ∧ (internal U Bs)⁻¹ = internal U Bs ∧
      (∀ i, Ultra.mk (t i) ∈ internal U Bs ^ 3) ∧
      internal U Bs * internal U Bs ⊆ ⋃ i, {Ultra.mk (t i)} * internal U Bs ∧
      (internal U Ss)⁻¹ = internal U Ss ∧
      BGT.conjSet (internal U Ss) (internal U Bs ^ 4) ^ Nlen ⊆ internal U Bs ∧
      (∀ g, (∀ i : ℕ, 1 ≤ i → i ≤ p → g ^ i ∈ internal U Bs ^ 100) → g ∈ internal U Bs) ∧
      (∀ g, (∀ i : ℕ, 1 ≤ i → i ≤ m → g ^ i ∈ internal U Bs) → g ∈ internal U Ss) ∧
      internal U Bs ⊆ T.A ^ q ∧
      T.A ⊆ ⋃ i, {Ultra.mk (y i)} * internal U Bs := by
  classical
  set rep : UProd (G := G) U → ∀ n, G n := Function.surjInv (Ultra.mk_surjective (G := G) (U := U))
    with hrep
  have hmkrep : ∀ q, Ultra.mk (rep q) = q := Function.surjInv_eq _
  -- the compact kernel
  obtain ⟨N, hNc, W, hWo, hNW, -, hWsub, hWnorm⟩ := NSS.exists_compact_kernel_data (G := T.L)
  have h1N : (1 : T.L) ∈ N := N.one_mem
  -- step 1: `V`
  obtain ⟨C, hCo, hNC, hC100⟩ := NSS.exists_open_superset_pow_subset hNc 100 hWo hNW
  obtain ⟨V, hVc, hVinv, hNV, hVC⟩ := NSS.exists_compact_symm_nbhd hNc hCo hNC
  have h1V : (1 : T.L) ∈ V := interior_subset (hNV h1N)
  have hV100 : V ^ 100 ⊆ W := (Set.pow_subset_pow_left hVC).trans hC100
  have hVW : V ⊆ W := fun x hx => hV100 (by
    simpa using Set.pow_subset_pow_right h1V (by norm_num : 1 ≤ 100) (by simpa using hx))
  -- step 2: `F` and `B*`
  obtain ⟨F, hFc, hFinv, hNF, hFV⟩ := NSS.exists_compact_symm_nbhd hNc isOpen_interior hNV
  obtain ⟨Bset, hBint, hBinv, ⟨q, hBq⟩, hBlow, hBup⟩ :=
    T.sandwich_symm hFc isOpen_interior hFV hFinv
  obtain ⟨Bs, rfl⟩ := hBint
  have hBΓ : internal U Bs ⊆ T.Γ := hBq.trans (T.pow_subset_Γ q)
  have h1F : (1 : T.L) ∈ F := interior_subset (hNF h1N)
  have h1B : (1 : UProd (G := G) U) ∈ internal U Bs := by
    have := hBlow 1 (by rw [map_one]; exact h1F)
    simpa using this
  have hBV : ∀ (k : ℕ) (g : T.Γ), (g : UProd (G := G) U) ∈ internal U Bs ^ k → T.π g ∈ V ^ k :=
    fun k g hg => Set.pow_subset_pow_left interior_subset (T.π_mem_pow hBΓ hBup k g hg)
  -- step 3: the first trapping time
  obtain ⟨p, hp, htrapP⟩ := NSS.exists_power_trapping_rel (NSS.isCompact_set_pow hVc 100)
    (by rw [← inv_pow, hVinv]) (Set.one_mem_pow h1V) isOpen_interior
    (fun P hP => (SetLike.coe_subset_coe.2 (hWsub P (hP.trans hV100))).trans hNF)
  -- step 4: covering `B*²`
  set KB : Set T.L := T.π '' {g : T.Γ | (g : UProd (G := G) U) ∈ internal U Bs} with hKB
  have hKBc : IsCompact KB := T.isCompact_image_of_internal (isInternal_internal Bs) hBq
  have hlift : ∀ z : T.L, ∃ b : T.Γ, z ∈ KB * KB →
      (b : UProd (G := G) U) ∈ internal U Bs ^ 2 ∧ T.π b = z := by
    intro z
    by_cases hz : z ∈ KB * KB
    · obtain ⟨_, ⟨b₁, hb₁, rfl⟩, _, ⟨b₂, hb₂, rfl⟩, rfl⟩ := hz
      refine ⟨b₁ * b₂, fun _ => ⟨?_, by rw [map_mul]⟩⟩
      rw [pow_two]
      exact Set.mul_mem_mul hb₁ hb₂
    · exact ⟨1, fun h => absurd h hz⟩
  choose bb hbb using hlift
  have hnb : ∀ z ∈ KB * KB, (fun w => z⁻¹ * w) ⁻¹' interior F ∈ 𝓝 z := by
    intro z _
    refine (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds ?_
    simpa using isOpen_interior.mem_nhds (hNF h1N)
  obtain ⟨t₀, ht₀, hcov₀⟩ := (hKBc.mul hKBc).elim_nhds_subcover _ hnb
  set k := t₀.card with hk
  set e := t₀.equivFin with he
  set t : Fin k → ∀ n, G n := fun i => rep (bb (e.symm i)) with htdef
  have hmkt : ∀ i, Ultra.mk (t i) = (bb (e.symm i) : UProd (G := G) U) := fun i => hmkrep _
  have ht3 : ∀ i, Ultra.mk (t i) ∈ internal U Bs ^ 3 := by
    intro i
    rw [hmkt]
    have := (hbb _ (ht₀ _ (e.symm i).2)).1
    exact Set.pow_subset_pow_right h1B (by norm_num) this
  have hcovB : internal U Bs * internal U Bs ⊆ ⋃ i, {Ultra.mk (t i)} * internal U Bs := by
    rintro _ ⟨g₁, hg₁, g₂, hg₂, rfl⟩
    set x : T.Γ := ⟨g₁, hBΓ hg₁⟩ * ⟨g₂, hBΓ hg₂⟩ with hx
    have hxK : T.π x ∈ KB * KB := by
      rw [hx, map_mul]
      exact Set.mul_mem_mul ⟨_, hg₁, rfl⟩ ⟨_, hg₂, rfl⟩
    obtain ⟨z, hzt, hz⟩ := Set.mem_iUnion₂.1 (hcov₀ hxK)
    have hbz := hbb z (ht₀ z hzt)
    have hmem : T.π ((bb z)⁻¹ * x) ∈ F := by
      rw [map_mul, map_inv, hbz.2]; exact interior_subset hz
    have hlow := hBlow _ hmem
    refine Set.mem_iUnion.2 ⟨e ⟨z, hzt⟩, Ultra.mk (t (e ⟨z, hzt⟩)), rfl, _, hlow, ?_⟩
    rw [hmkt, Equiv.symm_apply_apply]
    simp [hx]
  set κ := max 2 (2 * k) with hκ
  -- step 5: `N_len` and `O_S`
  set Nlen := 3 * p * κ with hNlen
  have hV4norm : ∀ x ∈ V ^ 4, ∀ n ∈ N, x⁻¹ * n * x ∈ N :=
    NSS.conj_mem_of_mem_pow (fun w hw => hWnorm w (hVW hw)) 4
  obtain ⟨OS, hOSo, hNOS, -, hOSconj⟩ := NSS.exists_open_conjSet_pow_subset_rel hNc
    (NSS.isCompact_set_pow hVc 4) hV4norm isOpen_interior hNF Nlen
  -- step 6: `F_S` and `S*`
  obtain ⟨FS, hFSc, hFSinv, hNFS, hFSOS⟩ := NSS.exists_compact_symm_nbhd hNc hOSo hNOS
  obtain ⟨Sset, hSint, hSinv, ⟨qS, hSq⟩, hSlow, hSup⟩ := T.sandwich_symm hFSc hOSo hFSOS hFSinv
  obtain ⟨Ss, rfl⟩ := hSint
  have hSΓ : internal U Ss ⊆ T.Γ := hSq.trans (T.pow_subset_Γ qS)
  -- step 7: the second trapping time
  obtain ⟨m, hm, htrapM⟩ := NSS.exists_power_trapping_rel hVc hVinv h1V isOpen_interior
    (fun P hP => (SetLike.coe_subset_coe.2 (hWsub P (hP.trans hVW))).trans hNFS)
  -- the size comparison
  obtain ⟨j, hj⟩ := T.exists_B_subset_preimage (isOpen_interior.mem_nhds (hNF h1N))
  have hBjB : T.B j ⊆ internal U Bs := fun b hb => by
    have := hBlow ⟨b, T.B_subset_Γ j hb⟩ (interior_subset (hj _ hb))
    exact this
  obtain ⟨F₁, -, hF₁cov⟩ := T.cover 1 j
  set r := F₁.card with hr
  set y : Fin r → ∀ n, G n := fun i => rep (F₁.equivFin.symm i) with hydef
  have hcovA : T.A ⊆ ⋃ i, {Ultra.mk (y i)} * internal U Bs := by
    intro a ha
    obtain ⟨f, hf, b, hb, rfl⟩ := hF₁cov (by simpa using ha)
    refine Set.mem_iUnion.2 ⟨F₁.equivFin ⟨f, hf⟩, f, ?_, b, hBjB hb, rfl⟩
    simp [hydef, hmkrep]
  -- the conjugated-product condition
  have hconjΓ : BGT.conjSet (internal U Ss) (internal U Bs ^ 4) ⊆ T.Γ := by
    rintro _ ⟨s, hs, b, hb, rfl⟩
    have hbΓ := T.pow_subset_Γ_of_subset hBΓ 4 hb
    exact T.Γ.mul_mem (T.Γ.mul_mem (T.Γ.inv_mem hbΓ) (hSΓ hs)) hbΓ
  have hconjπ : ∀ g : T.Γ, (g : UProd (G := G) U) ∈ BGT.conjSet (internal U Ss)
      (internal U Bs ^ 4) → T.π g ∈ BGT.conjSet OS (V ^ 4) := by
    rintro g ⟨s, hs, b, hb, hg⟩
    have hbΓ := T.pow_subset_Γ_of_subset hBΓ 4 hb
    have e : g = (⟨b, hbΓ⟩ : T.Γ)⁻¹ * ⟨s, hSΓ hs⟩ * ⟨b, hbΓ⟩ := Subtype.ext hg
    refine ⟨T.π ⟨s, hSΓ hs⟩, hSup _ hs, T.π ⟨b, hbΓ⟩, hBV 4 _ hb, ?_⟩
    rw [e, map_mul, map_mul, map_inv]
  have hconj : BGT.conjSet (internal U Ss) (internal U Bs ^ 4) ^ Nlen ⊆ internal U Bs := by
    intro x hx
    have hxΓ := T.pow_subset_Γ_of_subset hconjΓ Nlen hx
    have := T.π_mem_pow hconjΓ hconjπ Nlen ⟨x, hxΓ⟩ hx
    exact hBlow ⟨x, hxΓ⟩ (interior_subset (hOSconj this))
  refine ⟨Bs, Ss, κ, p, m, Nlen, k, q, r, t, y, le_max_left _ _, hp, hm, le_rfl, le_max_right _ _,
    h1B, hBinv, ht3, hcovB, hSinv, hconj, ?_, ?_, hBq, hcovA⟩
  · -- first trapping
    intro g hg
    have hgΓ : g ∈ T.Γ := T.pow_subset_Γ_of_subset hBΓ 100 (by simpa using hg 1 le_rfl hp)
    have hπ : T.π ⟨g, hgΓ⟩ ∈ interior F := htrapP _ fun i hi1 hip => by
      rw [← map_pow]; exact hBV 100 _ (by simpa using hg i hi1 hip)
    exact hBlow ⟨g, hgΓ⟩ (interior_subset hπ)
  · -- second trapping
    intro g hg
    have hgΓ : g ∈ T.Γ := hBΓ (by simpa using hg 1 le_rfl hm)
    have hπ : T.π ⟨g, hgΓ⟩ ∈ interior FS := htrapM _ fun i hi1 him => by
      rw [← map_pow]
      have := hBV 1 (⟨g, hgΓ⟩ ^ i) (by simpa using hg i hi1 him)
      simpa using this
    exact hSlow ⟨g, hgΓ⟩ (interior_subset hπ)

end TowerData

end Lovasz.UltraModel
