module
public import RequestProject.BGTEscape
public import RequestProject.NSSTopology

/-!
# Small conjugation-invariant neighbourhoods

`Lovasz.NSS.exists_open_conjSet_pow_subset`: in a topological group, for a compact set `K`, a
neighbourhood `U` of the identity and `N ∈ ℕ`, there is an open symmetric identity neighbourhood
`W` with `(W^K)^N ⊆ U`, where `W^K = {k⁻¹ w k : w ∈ W, k ∈ K}` is `BGT.conjSet W K`.  This is the
topological input for the conjugated-product condition of flexible trapping (step 3 of the
construction of trapping data from an NSS model).
-/

@[expose] public section

open scoped Pointwise Topology

namespace Lovasz.NSS

variable {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]

/-- For every identity neighbourhood `U` and every `N` there is an identity neighbourhood `V`
with `V^N ⊆ U`. -/
lemma exists_nhds_one_pow_subset (N : ℕ) {U : Set L} (hU : U ∈ 𝓝 (1 : L)) :
    ∃ V ∈ 𝓝 (1 : L), V ^ N ⊆ U := by
  induction N generalizing U with
  | zero => exact ⟨U, hU, by simpa using mem_of_mem_nhds hU⟩
  | succ N ih =>
    obtain ⟨V₁, hV₁o, hV₁1, hV₁⟩ := exists_open_nhds_one_mul_subset hU
    obtain ⟨V₂, hV₂, hV₂N⟩ := ih (hV₁o.mem_nhds hV₁1)
    refine ⟨V₁ ∩ V₂, Filter.inter_mem (hV₁o.mem_nhds hV₁1) hV₂, ?_⟩
    rw [pow_succ]
    refine (Set.mul_subset_mul ((Set.pow_subset_pow_left Set.inter_subset_right).trans hV₂N)
      Set.inter_subset_left).trans hV₁

/-- **Small conjugation-invariant neighbourhoods.**  For compact `K`, an identity neighbourhood
`U` and `N ∈ ℕ`, there is an open symmetric identity neighbourhood `W` with `(W^K)^N ⊆ U`. -/
theorem exists_open_conjSet_pow_subset {K U : Set L} (hK : IsCompact K) (hU : U ∈ 𝓝 (1 : L))
    (N : ℕ) : ∃ W : Set L, IsOpen W ∧ (1 : L) ∈ W ∧ W⁻¹ = W ∧ BGT.conjSet W K ^ N ⊆ U := by
  obtain ⟨U', hU', hU'N⟩ := exists_nhds_one_pow_subset N hU
  set n : Set (L × L) := {p | p.1⁻¹ * p.2 * p.1 ∈ interior U'} with hn
  have hno : IsOpen n := isOpen_interior.preimage
    ((continuous_fst.inv.mul continuous_snd).mul continuous_fst)
  have hsub : K ×ˢ ({1} : Set L) ⊆ n := by
    rintro ⟨k, w⟩ ⟨-, hw⟩
    simp only [Set.mem_singleton_iff] at hw
    subst hw
    simpa [hn] using mem_interior_iff_mem_nhds.2 hU'
  obtain ⟨u, v, -, hv, hKu, h1v, huv⟩ := generalized_tube_lemma hK isCompact_singleton hno hsub
  refine ⟨v ∩ v⁻¹, hv.inter hv.inv, ⟨h1v rfl, by simpa using h1v rfl⟩, by
    rw [Set.inter_inv, inv_inv, Set.inter_comm], ?_⟩
  refine (Set.pow_subset_pow_left ?_).trans hU'N
  rintro _ ⟨w, hw, k, hk, rfl⟩
  exact interior_subset (huv (Set.mk_mem_prod (hKu hk) hw.1))

end Lovasz.NSS
