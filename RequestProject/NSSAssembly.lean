module
public import RequestProject.NSSTopology

/-!
# From subgroup trapping and an NSS quotient of `H` to an NSS quotient of an open subgroup

This is the algebra/topology assembly step (Section 9 of the NSS-route notes, following the
NSS-reduction part of the Gleason–Yamabe argument).  Its inputs are stated concretely:

* (subgroup trapping) every subgroup contained in `U` lies in the subgroup `H`;
* (NSS quotient of `H`) `N ≤ H` is a compact subgroup normalised by `H`, and every subgroup
  `P ≤ H` contained in an open set `O₁ ⊇ N` (with `O₁ ⊆ U`) lies in `N`.

The conclusion (`exists_open_subgroup_nss_quotient`) is that some open subgroup `L₀ ⊇ N`
normalises `N` and `L₀ ⧸ N` has no small subgroups.  No Lie theory is used.

The inputs are supplied by weak Peter–Weyl (`WeakPeterWeyl.lean`) and subgroup trapping
(`SubgroupTrapping.lean`).
-/

@[expose] public section

open scoped Pointwise Topology

namespace Lovasz.NSS

variable {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]

/-- If `K` is compact with `K * K ⊆ O` for an open `O`, there is an open `A ⊇ K` with
`A * A ⊆ O`. -/
lemma exists_open_superset_mul_subset {K O : Set L} (hK : IsCompact K) (hO : IsOpen O)
    (hKO : K * K ⊆ O) : ∃ A : Set L, IsOpen A ∧ K ⊆ A ∧ A * A ⊆ O := by
  have hn : IsOpen ((fun p : L × L => p.1 * p.2) ⁻¹' O) := hO.preimage continuous_mul
  have hsub : K ×ˢ K ⊆ (fun p : L × L => p.1 * p.2) ⁻¹' O := fun p hp =>
    hKO (Set.mul_mem_mul hp.1 hp.2)
  obtain ⟨u, v, hu, hv, hKu, hKv, huv⟩ := generalized_tube_lemma hK hK hn hsub
  refine ⟨u ∩ v, hu.inter hv, Set.subset_inter hKu hKv, ?_⟩
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact huv (Set.mk_mem_prod ha.1 hb.2)

/-- The product `P N` of a subgroup `P` normalising a subgroup `N` is a subgroup. -/
def mulOfNormalizes (P N : Subgroup L) (hPN : ∀ p ∈ P, ∀ n ∈ N, p * n * p⁻¹ ∈ N) :
    Subgroup L where
  carrier := {x | ∃ p ∈ P, ∃ n ∈ N, x = p * n}
  one_mem' := ⟨1, P.one_mem, 1, N.one_mem, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨p₁, hp₁, n₁, hn₁, rfl⟩ ⟨p₂, hp₂, n₂, hn₂, rfl⟩
    refine ⟨p₁ * p₂, P.mul_mem hp₁ hp₂, p₂⁻¹ * n₁ * p₂⁻¹⁻¹ * n₂,
      N.mul_mem (hPN _ (P.inv_mem hp₂) _ hn₁) hn₂, by group⟩
  inv_mem' := by
    rintro _ ⟨p, hp, n, hn, rfl⟩
    exact ⟨p⁻¹, P.inv_mem hp, p * n⁻¹ * p⁻¹, hPN _ hp _ (N.inv_mem hn), by group⟩

omit [TopologicalSpace L] [IsTopologicalGroup L] in
lemma le_mulOfNormalizes (P N : Subgroup L) (hPN : ∀ p ∈ P, ∀ n ∈ N, p * n * p⁻¹ ∈ N) :
    P ≤ mulOfNormalizes P N hPN :=
  fun p hp => ⟨p, hp, 1, N.one_mem, by simp⟩

/-- **Assembly of an NSS quotient.**  Let `U` be a set such that every subgroup contained in `U`
lies in `H` (subgroup trapping).  Let `N ≤ H` be a compact subgroup normalised by `H`, and let
`O₁ ⊆ U` be an open set containing `N` such that every subgroup `P ≤ H` contained in `O₁` lies in
`N` (this is what "`H ⧸ N` is NSS" gives).  Then there is an open subgroup `L₀ ⊇ N` normalising
`N` such that `L₀ ⧸ N` has no small subgroups. -/
theorem exists_open_subgroup_nss_quotient {U O₁ : Set L} {H N : Subgroup L}
    (hNc : IsCompact (N : Set L)) (hNH : N ≤ H) (hNn : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N)
    (htrap : ∀ P : Subgroup L, (P : Set L) ⊆ U → P ≤ H)
    (hO₁ : IsOpen O₁) (hNO₁ : (N : Set L) ⊆ O₁) (hO₁U : O₁ ⊆ U)
    (hnss : ∀ P : Subgroup L, P ≤ H → (P : Set L) ⊆ O₁ → P ≤ N) :
    ∃ L₀ : Subgroup L, IsOpen (L₀ : Set L) ∧ N ≤ L₀ ∧
      ∃ _ : (N.subgroupOf L₀).Normal, HasNoSmallSubgroups (L₀ ⧸ N.subgroupOf L₀) := by
  have hNN : (N : Set L) * N ⊆ N := by
    rintro _ ⟨a, ha, b, hb, rfl⟩; exact N.mul_mem ha hb
  -- an open symmetric `W ⊇ N` with `W⁴ ⊆ O₁`
  obtain ⟨A, hA, hNA, hAA⟩ := exists_open_superset_mul_subset hNc hO₁ (hNN.trans hNO₁)
  obtain ⟨B, hB, hNB, hBB⟩ := exists_open_superset_mul_subset hNc hA (hNN.trans hNA)
  set W : Set L := B ∩ B⁻¹ with hW
  have hWo : IsOpen W := hB.inter hB.inv
  have hNW : (N : Set L) ⊆ W := fun n hn =>
    ⟨hNB hn, by simpa using hNB (N.inv_mem hn)⟩
  have hWinv : ∀ w ∈ W, w⁻¹ ∈ W := fun w hw => ⟨hw.2, by simpa using hw.1⟩
  have hW1 : (1 : L) ∈ W := hNW N.one_mem
  have hW4 : ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W, ∀ d ∈ W, a * b * c * d ∈ O₁ := by
    intro a ha b hb c hc d hd
    have h1 : a * b ∈ A := hBB (Set.mul_mem_mul ha.1 hb.1)
    have h2 : c * d ∈ A := hBB (Set.mul_mem_mul hc.1 hd.1)
    have := hAA (Set.mul_mem_mul h1 h2)
    simpa [mul_assoc] using this
  -- key claim: subgroups inside `W³` lie in `N`
  have hkey : ∀ P : Subgroup L, (∀ x ∈ P, ∃ a ∈ W, ∃ b ∈ W, ∃ c ∈ W, x = a * b * c) → P ≤ N := by
    intro P hP
    have hPO : (P : Set L) ⊆ O₁ := by
      intro x hx
      obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := hP x hx
      simpa using hW4 a ha b hb c hc 1 hW1
    have hPH : P ≤ H := htrap P (hPO.trans hO₁U)
    have hPN : ∀ p ∈ P, ∀ n ∈ N, p * n * p⁻¹ ∈ N := fun p hp n hn => hNn p (hPH hp) n hn
    set Q := mulOfNormalizes P N hPN
    have hQH : Q ≤ H := by
      rintro _ ⟨p, hp, n, hn, rfl⟩; exact H.mul_mem (hPH hp) (hNH hn)
    have hQO : (Q : Set L) ⊆ O₁ := by
      rintro _ ⟨p, hp, n, hn, rfl⟩
      obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := hP p hp
      exact hW4 a ha b hb c hc n (hNW hn)
    exact (le_mulOfNormalizes P N hPN).trans (hnss Q hQH hQO)
  -- elements of `W` normalise `N`
  have hconj : ∀ w ∈ W, ∀ n ∈ N, w * n * w⁻¹ ∈ N := by
    intro w hw n hn
    have hle := hkey (N.map (MulAut.conj w).toMonoidHom) (by
      rintro _ ⟨m, hm, rfl⟩
      exact ⟨w, hw, m, hNW hm, w⁻¹, hWinv w hw, by simp [MulAut.conj_apply]⟩)
    exact hle ⟨n, hn, by simp [MulAut.conj_apply]⟩
  set L₀ := Subgroup.closure W with hL₀
  have hWL₀ : W ⊆ L₀ := Subgroup.subset_closure
  have hL₀o : IsOpen (L₀ : Set L) :=
    Subgroup.isOpen_of_mem_nhds L₀ (g := 1) (Filter.mem_of_superset (hWo.mem_nhds hW1) hWL₀)
  have hNL₀ : N ≤ L₀ := fun n hn => hWL₀ (hNW hn)
  have hnorm : L₀ ≤ Subgroup.normalizer (N : Set L) := by
    rw [hL₀, Subgroup.closure_le]
    intro w hw
    rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · exact hconj w hw n
    · intro h
      have := hconj w⁻¹ (hWinv w hw) _ h
      simpa [mul_assoc] using this
  have hNn₀ : (N.subgroupOf L₀).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNL₀).2 hnorm
  refine ⟨L₀, hL₀o, hNL₀, hNn₀, ?_⟩
  -- the quotient `L₀ ⧸ N` is NSS
  set N' := N.subgroupOf L₀
  set V : Set (L₀ ⧸ N') := (QuotientGroup.mk : L₀ → L₀ ⧸ N') '' (Subtype.val ⁻¹' W) with hV
  have hVo : IsOpen V :=
    QuotientGroup.isOpenMap_coe _ (hWo.preimage continuous_subtype_val)
  have hV1 : (1 : L₀ ⧸ N') ∈ V := ⟨1, hW1, rfl⟩
  refine ⟨V, hVo.mem_nhds hV1, fun Q hQ => ?_⟩
  rw [eq_bot_iff]
  intro q hq
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  set P : Subgroup L := (Q.comap (QuotientGroup.mk' N')).map L₀.subtype with hP
  have hPN : P ≤ N := hkey P (by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hzy⟩ := hQ hy
    have hzy' : z⁻¹ * y ∈ N' := QuotientGroup.eq.1 hzy
    refine ⟨z, hz, ((z⁻¹ * y : L₀) : L), hNW hzy', 1, hW1, ?_⟩
    simp)
  have hxP : (x : L) ∈ P := ⟨x, hq, rfl⟩
  rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
  exact hPN hxP

end Lovasz.NSS
