module
public import RequestProject.BGTMain

/-!
# A reduced, rank-free finite structure theorem sufficient for the graph argument

The long-path theorems only use a weak consequence of Breuillard–Green–Tao Theorem 1.6: for
finite groups, no rank bound, no nilprogressions, and any containment `H ⊆ A^(radius·m)` with
`radius` bounded in terms of `K`.  This file isolates that consequence.

* `FiniteBGTCore`: every finite `K`-approximate group `A` is covered by a bounded number of left
  cosets of a subgroup `L` whose `step`-th lower-central-series term lies in `A^radius`
  (`L` need not be normal, nothing is assumed about its size).
* `finiteBGTCore_of_main`: Theorem 1.6 implies `FiniteBGTCore` (sanity check).
* `bgtBoundedPower_of_finiteCore`: `FiniteBGTCore` implies `BGTBoundedPower`, the relaxed form of
  the statement used by Tessera–Tointon, by the normal-core argument of BGT Section 11.
-/

@[expose] public section


open scoped Pointwise

namespace Lovasz

/-- **Finite, rank-free structural core of Breuillard–Green–Tao.**  The constants `cover`, `step`
and `radius` depend only on `K`: every `K`-approximate subgroup `A` of a finite group is covered
by at most `cover` left cosets of a subgroup `L` (not necessarily normal) with
`γ_step(L) ⊆ A^radius`. -/
def FiniteBGTCore : Prop :=
  ∀ K : ℝ, 1 ≤ K → ∃ cover step radius : ℕ,
    ∀ (G : Type) [Group G] [Finite G] (A : Set G),
      IsApproximateSubgroup K A → ∃ L : Subgroup G,
        (∃ T : Finset G, T.card ≤ cover ∧ A ⊆ ⋃ t ∈ T, t • (L : Set G)) ∧
        (((((⊤ : Subgroup L).lowerCentralSeries step).map L.subtype : Subgroup G)) : Set G) ⊆ A ^ radius

/-- Theorem 1.6 of Breuillard–Green–Tao implies the reduced core statement. -/
theorem finiteBGTCore_of_main (hM : BGTMainTheorem) : FiniteBGTCore := by
  intro K hK
  obtain ⟨C, hC⟩ := hM (2 * K) (by linarith)
  refine ⟨C, C, 4, fun G _ _ A hA => ?_⟩
  obtain ⟨G₀, H, -, -, -, hcov, hlcs, -, hH4, -⟩ :=
    hC G A (isBGTApproxGroup_of_isApproximateSubgroup hA)
  refine ⟨G₀, hcov, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact hH4 (hlcs hx)

/-- The lower central series is monotone along an inclusion of subgroups, viewed in the
ambient group. -/
lemma lowerCentralSeries_map_subtype_mono {G : Type*} [Group G] {L₁ L₂ : Subgroup G}
    (h : L₁ ≤ L₂) (s : ℕ) :
    ((⊤ : Subgroup L₁).lowerCentralSeries s).map L₁.subtype ≤
      ((⊤ : Subgroup L₂).lowerCentralSeries s).map L₂.subtype := by
  have hinc := lowerCentralSeries_map_subtype_le (L₁.subgroupOf L₂) s
  rintro _ ⟨x, hx, rfl⟩
  have hx' : (⟨⟨(x : G), h x.2⟩, x.2⟩ : L₁.subgroupOf L₂) ∈
      (⊤ : Subgroup (L₁.subgroupOf L₂)).lowerCentralSeries s := by
    have e : (Subgroup.subgroupOfEquivOfLe h).symm x =
        (⟨⟨(x : G), h x.2⟩, x.2⟩ : L₁.subgroupOf L₂) := rfl
    rw [← e]
    have hchar := lowerCentralSeries_map_of_surjective
      ((Subgroup.subgroupOfEquivOfLe h).symm : L₁ →* L₁.subgroupOf L₂)
      (Subgroup.subgroupOfEquivOfLe h).symm.surjective s
    rw [← hchar]
    exact Subgroup.mem_map_of_mem _ hx
  exact ⟨_, hinc (Subgroup.mem_map_of_mem _ hx'), rfl⟩

/-- The reduced core statement implies the relaxed Breuillard–Green–Tao statement used in the
graph argument (normal-core argument of BGT Section 11). -/
theorem bgtBoundedPower_of_finiteCore (hC : FiniteBGTCore) : BGTBoundedPower := by
  intro K hK
  obtain ⟨cover, step, radius, hcore⟩ := hC K hK
  refine ⟨cover, cover.factorial, step, radius, ?_⟩
  intro G _ _ A m h1 hinv hcl hm happ
  obtain ⟨L, ⟨T, hTc, hcov⟩, hlcs⟩ := hcore G (A ^ m) happ
  have hidx : L.index ≤ cover := by
    refine index_le_of_pow_covered A h1 hinv hcl L cover T hTc ?_
    exact (Set.pow_subset_pow_right h1 hm).trans hcov
  set G₁ := L.normalCore with hG₁
  have hG₁le : G₁ ≤ L := L.normalCore_le
  have hidx₁ : G₁.index ≤ cover.factorial := by
    have h : G₁.index ∣ L.index.factorial := by
      rw [hG₁, Subgroup.normalCore_eq_ker, Subgroup.index_ker, Subgroup.index_eq_card,
        ← Nat.card_perm]
      exact Subgroup.card_subgroup_dvd_card _
    exact (Nat.le_of_dvd (Nat.factorial_pos _) h).trans (Nat.factorial_le hidx)
  refine ⟨((⊤ : Subgroup G₁).lowerCentralSeries step).map G₁.subtype, G₁,
    lowerCentralSeries_map_subtype_normal G₁ step, L.normalCore_normal, ?_, ?_, hidx₁, le_rfl⟩
  · rintro _ ⟨x, -, rfl⟩; exact x.2
  · intro x hx
    have := hlcs (lowerCentralSeries_map_subtype_mono hG₁le step hx)
    rwa [← pow_mul, mul_comm] at this

end Lovasz
