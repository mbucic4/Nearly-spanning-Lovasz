module
public import Mathlib
public import RequestProject.NSSAssembly

/-!
# Buffered relative power trapping

`Lovasz.NSS.exists_buffered_power_trapping`: let `H` be a compact subgroup of a locally compact
Hausdorff group, `N ≤ H` a compact subgroup, `U ⊇ N` open, and `O₁ ⊇ N` open such that every
subgroup `P ≤ H` contained in `O₁` lies in `N` (this is what "`H ⧸ N` is NSS" provides, see
`PeterWeyl.exists_compact_normal_nss_of_compact_subgroup`).  Then there are a symmetric open `R`
with compact closure, `N ⊆ R ⊆ U`, and `k ≥ 1` such that for every `h ∈ H`,
`h, h², …, h^k ∈ closure (R⁸)` implies `h ∈ R`.

The proof chooses `R` with `closure (R⁸) ⊆ O₁` and then finds `k` by a compactness argument
along an ultrafilter: a limit `h` of counterexamples would have all its powers in
`closure (R⁸) ∩ H ⊆ O₁`, so the cyclic group it generates lies in `N ⊆ R`, while `h ∉ R`.
No quotient topology is needed.
-/

@[expose] public section

open scoped Pointwise Topology
open Filter

namespace Lovasz.NSS

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

lemma isCompact_set_pow {K : Set G} (hK : IsCompact K) : ∀ n : ℕ, IsCompact (K ^ n)
  | 0 => by rw [pow_zero]; exact isCompact_singleton
  | n + 1 => by rw [pow_succ]; exact (isCompact_set_pow hK n).mul hK

/-- A compact subgroup `N` inside an open set `O` has an open neighbourhood `C ⊇ N` with
`C⁸ ⊆ O`. -/
lemma exists_open_superset_pow_eight_subset {N : Subgroup G} (hNc : IsCompact (N : Set G))
    {O : Set G} (hO : IsOpen O) (hNO : (N : Set G) ⊆ O) :
    ∃ C : Set G, IsOpen C ∧ (N : Set G) ⊆ C ∧ C ^ 8 ⊆ O := by
  have hNN : (N : Set G) * N ⊆ N := by
    rintro _ ⟨a, ha, b, hb, rfl⟩; exact N.mul_mem ha hb
  obtain ⟨A, hA, hNA, hAA⟩ := exists_open_superset_mul_subset hNc hO (hNN.trans hNO)
  obtain ⟨B, hB, hNB, hBB⟩ := exists_open_superset_mul_subset hNc hA (hNN.trans hNA)
  obtain ⟨C, hC, hNC, hCC⟩ := exists_open_superset_mul_subset hNc hB (hNN.trans hNB)
  refine ⟨C, hC, hNC, ?_⟩
  have e : C ^ 8 = ((C ^ 2) ^ 2) ^ 2 := by rw [← pow_mul, ← pow_mul]
  have h2 : C ^ 2 ⊆ B := by rw [pow_two]; exact hCC
  have h4 : (C ^ 2) ^ 2 ⊆ A := by
    rw [pow_two]; exact (Set.mul_subset_mul h2 h2).trans hBB
  rw [e, pow_two]
  exact (Set.mul_subset_mul h4 h4).trans hAA

variable [T2Space G] [LocallyCompactSpace G]

/-- **Buffered relative power trapping.**  See the module docstring. -/
theorem exists_buffered_power_trapping {H N : Subgroup G} (hHc : IsCompact (H : Set G))
    (hNc : IsCompact (N : Set G)) {U O₁ : Set G} (hU : IsOpen U) (hNU : (N : Set G) ⊆ U)
    (hO₁ : IsOpen O₁) (hNO₁ : (N : Set G) ⊆ O₁)
    (hnss : ∀ P : Subgroup G, P ≤ H → (P : Set G) ⊆ O₁ → P ≤ N) :
    ∃ R : Set G, IsOpen R ∧ R⁻¹ = R ∧ IsCompact (closure R) ∧ (N : Set G) ⊆ R ∧ R ⊆ U ∧
      ∃ k : ℕ, 1 ≤ k ∧ ∀ h ∈ H,
        (∀ j : ℕ, 1 ≤ j → j ≤ k → h ^ j ∈ closure (R ^ 8)) → h ∈ R := by
  -- the buffer `R`
  obtain ⟨C, hC, hNC, hC8⟩ := exists_open_superset_pow_eight_subset hNc hO₁ hNO₁
  obtain ⟨R₀, hR₀, hNR₀, hR₀cl, hR₀c⟩ :=
    exists_open_between_and_isCompact_closure hNc (hC.inter hU) (Set.subset_inter hNC hNU)
  set R := R₀ ∩ R₀⁻¹ with hRdef
  have hRo : IsOpen R := hR₀.inter hR₀.inv
  have hRinv : R⁻¹ = R := by rw [hRdef, Set.inter_inv, inv_inv, Set.inter_comm]
  have hNR : (N : Set G) ⊆ R := fun n hn => ⟨hNR₀ hn, by simpa using hNR₀ (N.inv_mem hn)⟩
  have hRcl : closure R ⊆ closure R₀ := closure_mono Set.inter_subset_left
  have hRc : IsCompact (closure R) := hR₀c.of_isClosed_subset isClosed_closure hRcl
  have hRU : R ⊆ U := fun x hx => ((hR₀cl (subset_closure hx.1)).2)
  have hR8 : closure (R ^ 8) ⊆ O₁ := by
    have hc8 : IsCompact (closure R ^ 8) := isCompact_set_pow hRc 8
    refine (closure_minimal (Set.pow_subset_pow_left subset_closure) hc8.isClosed).trans ?_
    refine (Set.pow_subset_pow_left (hRcl.trans ?_)).trans hC8
    exact hR₀cl.trans Set.inter_subset_left
  refine ⟨R, hRo, hRinv, hRc, hNR, hRU, ?_⟩
  -- the trapping time `k`, by compactness
  by_contra hcon
  push_neg at hcon
  have hbad : ∀ k : ℕ, ∃ h ∈ H, (∀ j : ℕ, 1 ≤ j → j ≤ k + 1 → h ^ j ∈ closure (R ^ 8)) ∧
      h ∉ R := fun k => hcon (k + 1) (by omega)
  choose x hxH hxpow hxR using hbad
  set 𝒰 := hyperfilter ℕ
  have hle : (𝒰.map x : Filter G) ≤ 𝓟 (H : Set G) := by
    rw [Ultrafilter.coe_map]
    exact le_principal_iff.2 (mem_map.2 (univ_mem' fun k => hxH k))
  obtain ⟨h, hhH, hlim⟩ := hHc.ultrafilter_le_nhds (𝒰.map x) hle
  have hlim' : Tendsto x (𝒰 : Filter ℕ) (𝓝 h) := hlim
  -- `h ∉ R`
  have hhR : h ∉ R := fun hh => by
    obtain ⟨k, hk⟩ := (hlim'.eventually (hRo.mem_nhds hh)).exists
    exact hxR k hk
  -- all positive powers of `h` lie in `closure (R⁸)`
  have hpow : ∀ j : ℕ, 1 ≤ j → h ^ j ∈ closure (R ^ 8) := by
    intro j hj
    have hev : ∀ᶠ k in (𝒰 : Filter ℕ), x k ^ j ∈ closure (R ^ 8) := by
      have : ∀ᶠ k in (cofinite : Filter ℕ), j ≤ k + 1 := by
        rw [Nat.cofinite_eq_atTop]
        exact eventually_atTop.2 ⟨j, fun k hk => by omega⟩
      filter_upwards [hyperfilter_le_cofinite this] with k hk using hxpow k j hj hk
    exact isClosed_closure.mem_of_tendsto (hlim'.pow j) hev
  -- the cyclic group generated by `h` lies in `O₁`, hence in `N`
  have hR8inv : (closure (R ^ 8))⁻¹ = closure (R ^ 8) := by
    rw [inv_closure, ← inv_pow, hRinv]
  have h1R : (1 : G) ∈ R := hNR N.one_mem
  have hzp : (Subgroup.zpowers h : Set G) ⊆ O₁ := by
    rintro _ ⟨m, rfl⟩
    apply hR8
    rcases Int.eq_nat_or_neg m with ⟨j, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp only [Int.natCast_zero, zpow_zero]
        exact subset_closure (Set.one_mem_pow h1R)
      · simpa using hpow j hj
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp only [Int.natCast_zero, neg_zero, zpow_zero]
        exact subset_closure (Set.one_mem_pow h1R)
      · rw [← hR8inv]
        simpa using hpow j hj
  have hzH : Subgroup.zpowers h ≤ H := (Subgroup.zpowers_le).2 hhH
  exact hhR (hNR (hnss _ hzH hzp (Subgroup.mem_zpowers h)))

end Lovasz.NSS
