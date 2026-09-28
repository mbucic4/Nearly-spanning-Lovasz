module
public import Mathlib
public import RequestProject.SubgroupTrapping

/-!
# Working modulo a compact kernel

Let `L` be a first-countable locally compact Hausdorff group.  Subgroup trapping and the compact
NSS quotient provide a compact subgroup `N` and an open symmetric `W ⊇ N` such that every subgroup
inside `W` lies in `N` and every element of `W` normalises `N` (`exists_compact_kernel_data`): this
is the statement "`⟨W⟩ ⧸ N` has no small subgroups", pulled back to `L`.  All witnesses for
flexible trapping are then chosen among `N`-neighbourhoods in `L`, which is equivalent to working
in the quotient by the compact kernel `N`.

* `exists_power_trapping_rel`: compact power trapping modulo subgroups (`C` compact symmetric; if
  every subgroup inside `C` lies in an open `U`, then `g, …, g^p ∈ C ⇒ g ∈ U`);
* `exists_open_superset_pow_subset`: a compact subgroup `N ⊆ O` has an open `C ⊇ N` with
  `C^m ⊆ O`;
* `exists_open_conjSet_pow_subset_rel`: for `N` normalised by a compact `K`, an open `W ⊇ N` with
  `(conjSet W K)^m ⊆ O`;
* `exists_compact_symm_nbhd`: a compact symmetric `F` with `N ⊆ interior F` and `F ⊆ O`.
-/

@[expose] public section

open scoped Pointwise Topology
open Filter

namespace Lovasz.NSS

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A compact subgroup `N` inside an open set `O` has an open neighbourhood `C ⊇ N` with
`C^m ⊆ O`. -/
lemma exists_open_superset_pow_subset {N : Subgroup G} (hNc : IsCompact (N : Set G)) (m : ℕ) :
    ∀ {O : Set G}, IsOpen O → (N : Set G) ⊆ O → ∃ C : Set G, IsOpen C ∧ (N : Set G) ⊆ C ∧
      C ^ m ⊆ O := by
  have hNN : (N : Set G) * N ⊆ N := by
    rintro _ ⟨a, ha, b, hb, rfl⟩; exact N.mul_mem ha hb
  induction m with
  | zero =>
    intro O hO hNO
    exact ⟨O, hO, hNO, by simpa using hNO N.one_mem⟩
  | succ m ih =>
    intro O hO hNO
    obtain ⟨A, hA, hNA, hAA⟩ := exists_open_superset_mul_subset hNc hO (hNN.trans hNO)
    obtain ⟨C, hC, hNC, hCm⟩ := ih hA hNA
    refine ⟨C ∩ A, hC.inter hA, Set.subset_inter hNC hNA, ?_⟩
    rw [pow_succ]
    exact (Set.mul_subset_mul ((Set.pow_subset_pow_left Set.inter_subset_left).trans hCm)
      Set.inter_subset_right).trans hAA

/-- Conjugation-small neighbourhoods of a compact subgroup: if `N` is compact and normalised by a
compact set `K` (`k⁻¹ n k ∈ N`), then for every open `O ⊇ N` and `m` there is an open symmetric
`W ⊇ N` with `(conjSet W K)^m ⊆ O`. -/
theorem exists_open_conjSet_pow_subset_rel {N : Subgroup G} (hNc : IsCompact (N : Set G))
    {K : Set G} (hK : IsCompact K) (hKN : ∀ k ∈ K, ∀ n ∈ N, k⁻¹ * n * k ∈ N)
    {O : Set G} (hO : IsOpen O) (hNO : (N : Set G) ⊆ O) (m : ℕ) :
    ∃ W : Set G, IsOpen W ∧ (N : Set G) ⊆ W ∧ W⁻¹ = W ∧ BGT.conjSet W K ^ m ⊆ O := by
  obtain ⟨O', hO', hNO', hO'm⟩ := exists_open_superset_pow_subset hNc m hO hNO
  set n : Set (G × G) := {p | p.1⁻¹ * p.2 * p.1 ∈ O'} with hn
  have hno : IsOpen n := hO'.preimage
    ((continuous_fst.inv.mul continuous_snd).mul continuous_fst)
  have hsub : K ×ˢ (N : Set G) ⊆ n := by
    rintro ⟨k, x⟩ ⟨hk, hx⟩
    exact hNO' (hKN k hk x hx)
  obtain ⟨u, v, -, hv, hKu, hNv, huv⟩ := generalized_tube_lemma hK hNc hno hsub
  refine ⟨v ∩ v⁻¹, hv.inter hv.inv, fun x hx => ⟨hNv hx, by simpa using hNv (N.inv_mem hx)⟩,
    by rw [Set.inter_inv, inv_inv, Set.inter_comm], ?_⟩
  refine (Set.pow_subset_pow_left ?_).trans hO'm
  rintro _ ⟨w, hw, k, hk, rfl⟩
  exact huv (Set.mk_mem_prod (hKu hk) hw.1)

variable [T2Space G]

/-- **Compact power trapping modulo subgroups.**  Let `C` be compact and symmetric with `1 ∈ C`,
and `U` open, such that every subgroup contained in `C` is contained in `U`.  Then there is
`p ≥ 1` such that `g, g², …, g^p ∈ C` implies `g ∈ U`. -/
theorem exists_power_trapping_rel {C U : Set G} (hC : IsCompact C) (hCinv : C⁻¹ = C)
    (hC1 : (1 : G) ∈ C) (hU : IsOpen U) (hno : ∀ P : Subgroup G, (P : Set G) ⊆ C → (P : Set G) ⊆ U) :
    ∃ p : ℕ, 1 ≤ p ∧ ∀ g : G, (∀ i : ℕ, 1 ≤ i → i ≤ p → g ^ i ∈ C) → g ∈ U := by
  by_contra hcon
  push_neg at hcon
  have hbad : ∀ k : ℕ, ∃ g, (∀ i : ℕ, 1 ≤ i → i ≤ k + 1 → g ^ i ∈ C) ∧ g ∉ U :=
    fun k => hcon (k + 1) (by omega)
  choose x hxpow hxU using hbad
  set 𝒰 := hyperfilter ℕ
  have hle : (𝒰.map x : Filter G) ≤ 𝓟 C := by
    rw [Ultrafilter.coe_map]
    exact le_principal_iff.2 (mem_map.2 (univ_mem' fun k => by
      simpa using hxpow k 1 le_rfl (by omega)))
  obtain ⟨g, hgC, hlim⟩ := hC.ultrafilter_le_nhds (𝒰.map x) hle
  have hlim' : Tendsto x (𝒰 : Filter ℕ) (𝓝 g) := hlim
  have hgU : g ∉ U := fun hg => by
    obtain ⟨k, hk⟩ := (hlim'.eventually (hU.mem_nhds hg)).exists
    exact hxU k hk
  have hpow : ∀ j : ℕ, 1 ≤ j → g ^ j ∈ C := by
    intro j hj
    have hev : ∀ᶠ k in (𝒰 : Filter ℕ), x k ^ j ∈ C := by
      have : ∀ᶠ k in (cofinite : Filter ℕ), j ≤ k + 1 := by
        rw [Nat.cofinite_eq_atTop]
        exact eventually_atTop.2 ⟨j, fun k hk => by omega⟩
      filter_upwards [hyperfilter_le_cofinite this] with k hk using hxpow k j hj hk
    exact hC.isClosed.mem_of_tendsto (hlim'.pow j) hev
  have hzp : (Subgroup.zpowers g : Set G) ⊆ C := by
    rintro _ ⟨m, rfl⟩
    rcases Int.eq_nat_or_neg m with ⟨j, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · simpa using hC1
      · simpa using hpow j hj
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · simpa using hC1
      · rw [← hCinv]; simpa using hpow j hj
  exact hgU (hno _ hzp (Subgroup.mem_zpowers g))

omit [T2Space G] in
/-- A compact symmetric neighbourhood of a compact subgroup `N` inside an open set `O`. -/
lemma exists_compact_symm_nbhd [LocallyCompactSpace G] {N : Subgroup G}
    (hNc : IsCompact (N : Set G)) {O : Set G} (hO : IsOpen O) (hNO : (N : Set G) ⊆ O) :
    ∃ F : Set G, IsCompact F ∧ F⁻¹ = F ∧ (N : Set G) ⊆ interior F ∧ F ⊆ O := by
  obtain ⟨V, hV, hNV, hVcl, hVc⟩ := exists_open_between_and_isCompact_closure hNc hO hNO
  refine ⟨closure (V ∩ V⁻¹), hVc.of_isClosed_subset isClosed_closure
    (closure_mono Set.inter_subset_left), ?_, ?_, (closure_mono Set.inter_subset_left).trans hVcl⟩
  · rw [inv_closure, Set.inter_inv, inv_inv, Set.inter_comm]
  · refine subset_trans ?_ (interior_mono (subset_closure (s := V ∩ V⁻¹)))
    rw [(hV.inter hV.inv).interior_eq]
    exact fun x hx => ⟨hNV hx, by simpa using hNV (N.inv_mem hx)⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] in
/-- Products of elements normalising `N` normalise `N`. -/
lemma conj_mem_of_mem_pow {N : Subgroup G} {W : Set G}
    (hW : ∀ w ∈ W, ∀ n ∈ N, w⁻¹ * n * w ∈ N) (m : ℕ) :
    ∀ k ∈ W ^ m, ∀ n ∈ N, k⁻¹ * n * k ∈ N := by
  induction m with
  | zero =>
    intro k hk n hn
    rw [pow_zero, Set.mem_one] at hk; subst hk; simpa using hn
  | succ m ih =>
    intro k hk n hn
    rw [pow_succ] at hk
    obtain ⟨k', hk', w, hw, rfl⟩ := hk
    have := hW w hw _ (ih k' hk' n hn)
    simpa [mul_assoc] using this

variable [LocallyCompactSpace G] [FirstCountableTopology G]

/-- **Compact-kernel data.**  In a first-countable locally compact Hausdorff group there are a
compact subgroup `N` and an open symmetric `W ⊇ N` such that every subgroup contained in `W` lies
in `N`, and every element of `W` normalises `N`. -/
theorem exists_compact_kernel_data :
    ∃ N : Subgroup G, IsCompact (N : Set G) ∧ ∃ W : Set G, IsOpen W ∧ (N : Set G) ⊆ W ∧
      W⁻¹ = W ∧ (∀ P : Subgroup G, (P : Set G) ⊆ W → P ≤ N) ∧
      (∀ w ∈ W, ∀ n ∈ N, w⁻¹ * n * w ∈ N) := by
  obtain ⟨V₁, hV₁o, hV₁1, -, H, hHc, -, htrap⟩ :=
    Trapping.subgroup_trapping (G := G) isOpen_univ (Set.mem_univ 1)
  obtain ⟨N, hNH, hNc, -, -, O₁, hO₁, hNO₁, hO₁V₁, hnss⟩ :=
    PeterWeyl.exists_compact_normal_nss_of_compact_subgroup hHc hV₁o hV₁1
  obtain ⟨C, hC, hNC, hC3⟩ := exists_open_superset_pow_subset hNc 3 hO₁ hNO₁
  set W := C ∩ C⁻¹ with hWdef
  have hNW : (N : Set G) ⊆ W := fun x hx => ⟨hNC hx, by simpa using hNC (N.inv_mem hx)⟩
  have hW1 : (1 : G) ∈ W := hNW N.one_mem
  have hW3 : W ^ 3 ⊆ O₁ := (Set.pow_subset_pow_left Set.inter_subset_left).trans hC3
  have hWO₁ : W ⊆ O₁ := fun x hx => hW3 (by
    rw [pow_succ, pow_two]; simpa using Set.mul_mem_mul (Set.mul_mem_mul hx hW1) hW1)
  have hsub : ∀ P : Subgroup G, (P : Set G) ⊆ O₁ → P ≤ N := fun P hP =>
    hnss P (htrap P (hP.trans hO₁V₁)) hP
  refine ⟨N, hNc, W, hC.inter hC.inv, hNW, by rw [hWdef, Set.inter_inv, inv_inv, Set.inter_comm],
    fun P hP => hsub P (hP.trans hWO₁), ?_⟩
  intro w hw n hn
  have hwi : w⁻¹ ∈ W := ⟨hw.2, by simpa using hw.1⟩
  have hle := hsub (N.map (MulAut.conj w⁻¹).toMonoidHom) (by
    rintro _ ⟨x, hx, rfl⟩
    apply hW3
    have : (MulAut.conj w⁻¹).toMonoidHom x = w⁻¹ * x * w⁻¹⁻¹ := by
      simp
    rw [this, pow_succ, pow_two]
    exact Set.mul_mem_mul (Set.mul_mem_mul hwi (hNW hx)) (by simpa using hw))
  exact hle ⟨n, hn, by simp⟩

end Lovasz.NSS
