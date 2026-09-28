module
public import RequestProject.BGTFiniteCore
public import RequestProject.BGTFiniteNilpotence

/-!
# Reducing `FiniteBGTCore` to two isolated finite inputs

`finiteBGTCore_of_regularization` proves the reduced structure theorem `FiniteBGTCore` from two
precisely stated inputs, neither of which is proved in this project:

* `StrongRegularization` (regularization): every finite `K`-approximate group `A` contains a
  strong `M`-approximate group `B ⊆ A^q` (Definition 7.1 of Breuillard–Green–Tao) with
  `|B| ≥ η |A|`, where `M ≥ 1`, `q`, `η > 0` depend only on `K`.  In BGT this is obtained from
  the Lie model (Section 6) and Propositions 7.2/7.3.
* `NilpotentFiniteCore` (uniformization): `FiniteBGTCore` restricted to finite *nilpotent*
  ambient groups, of arbitrary nilpotency class; i.e. a step-independent structure theorem for
  approximate groups in finite nilpotent groups (in the spirit of Tointon's theorem on
  approximate subgroups of arbitrary nilpotent groups).

The proof combines them with the finitary nilpotence theorem `BGT.finite_nilpotent_mod_zeroEsc`
(commutator contraction for the escape norm, proved in `BGTFiniteNilpotence.lean`): the large
approximate group `S` it produces lies in a subgroup `Γ` which is nilpotent modulo a subgroup
`H ⊆ B`; `NilpotentFiniteCore` is applied to the image of `S` in `Γ/H`, and a covering argument
transfers the resulting subgroup back to `A`.
-/

@[expose] public section


open scoped Pointwise

namespace Lovasz

/-- **Regularization** (isolated, not proved here).  For every `K ≥ 1` there are `M ≥ 1`, `q` and
`η > 0` such that every `K`-approximate subgroup `A` of a finite group contains a strong
`M`-approximate group `B ⊆ A^q` (Definition 7.1 of Breuillard–Green–Tao) with `|B| ≥ η |A|`. -/
def StrongRegularization : Prop :=
  ∀ K : ℝ, 1 ≤ K → ∃ (M : ℝ) (q : ℕ) (η : ℝ), 1 ≤ M ∧ 0 < η ∧
    ∀ (G : Type) [Group G] [Finite G] (A : Set G), IsApproximateSubgroup K A →
      ∃ B : Set G, BGT.IsStrongApproxGroup M B ∧ B ⊆ A ^ q ∧ η * A.ncard ≤ B.ncard

/-- **Uniformization for nilpotent groups** (isolated, not proved here).  `FiniteBGTCore`
restricted to finite nilpotent ambient groups: the constants depend only on `K`, not on the
nilpotency class of the ambient group. -/
def NilpotentFiniteCore : Prop :=
  ∀ K : ℝ, 1 ≤ K → ∃ cover step radius : ℕ,
    ∀ (G : Type) [Group G] [Finite G] [Group.IsNilpotent G] (A : Set G),
      IsApproximateSubgroup K A → ∃ L : Subgroup G,
        (∃ T : Finset G, T.card ≤ cover ∧ A ⊆ ⋃ t ∈ T, t • (L : Set G)) ∧
        (((((⊤ : Subgroup L).lowerCentralSeries step).map L.subtype : Subgroup G)) : Set G) ⊆ A ^ radius

/-- Sanity check: `NilpotentFiniteCore` is a special case of `FiniteBGTCore` (hence follows from
Theorem 1.6 of Breuillard–Green–Tao by `finiteBGTCore_of_main`). -/
theorem nilpotentFiniteCore_of_finiteCore (hC : FiniteBGTCore) : NilpotentFiniteCore := by
  intro K hK
  obtain ⟨cover, step, radius, h⟩ := hC K hK
  exact ⟨cover, step, radius, fun G _ _ _ A hA => h G A hA⟩

section Aux

/-- Covering by cosets: if `P ⊆ L`, then `A` is covered by `T.card` left cosets of `L` where
`T.card * |P| ≤ |A P|`. -/
lemma exists_coset_cover_card_mul_le {G : Type*} [Group G] [DecidableEq G]
    (A P : Finset G) (L : Subgroup G) (hP : (P : Set G) ⊆ L) :
    ∃ T : Finset G, (A : Set G) ⊆ ⋃ t ∈ T, t • (L : Set G) ∧ T.card * P.card ≤ (A * P).card := by
  classical
  let r : G ⧸ L → G := fun c => if h : ∃ a ∈ A, (a : G ⧸ L) = c then h.choose else 1
  have hr : ∀ a ∈ A, r (a : G ⧸ L) ∈ A ∧ ((r (a : G ⧸ L) : G) : G ⧸ L) = (a : G ⧸ L) := by
    intro a ha
    have hex : ∃ a' ∈ A, (a' : G ⧸ L) = (a : G ⧸ L) := ⟨a, ha, rfl⟩
    have e : r (a : G ⧸ L) = hex.choose := dif_pos hex
    rw [e]; exact hex.choose_spec
  let T := (A.image (QuotientGroup.mk : G → G ⧸ L)).image r
  have hT : ∀ t ∈ T, ∃ a ∈ A, t = r (a : G ⧸ L) := by
    intro t ht
    simp only [T, Finset.mem_image] at ht
    obtain ⟨c, ⟨a, ha, rfl⟩, rfl⟩ := ht
    exact ⟨a, ha, rfl⟩
  refine ⟨T, ?_, ?_⟩
  · intro a ha
    simp only [Set.mem_iUnion]
    refine ⟨r a, Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ ha), ?_⟩
    have h2 := (hr a ha).2
    rw [QuotientGroup.eq] at h2
    exact ⟨_, h2, by simp⟩
  · have hsub : T.biUnion (fun t => t • P) ⊆ A * P := by
      intro x hx
      simp only [Finset.mem_biUnion] at hx
      obtain ⟨t, ht, hx⟩ := hx
      obtain ⟨a, ha, rfl⟩ := hT t ht
      obtain ⟨p, hp, rfl⟩ := Finset.mem_smul_finset.1 hx
      exact Finset.mul_mem_mul (hr a ha).1 hp
    have hdisj : (T : Set G).PairwiseDisjoint (fun t => t • P) := by
      intro t ht t' ht' hne
      rw [Function.onFun, Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨a, ha, rfl⟩ := hT t ht
      obtain ⟨a', ha', rfl⟩ := hT t' ht'
      obtain ⟨p, hp, rfl⟩ := Finset.mem_smul_finset.1 hx
      obtain ⟨p', hp', hpp⟩ := Finset.mem_smul_finset.1 hx'
      apply hne
      have hq : ((r (a : G ⧸ L) : G) : G ⧸ L) = ((r (a' : G ⧸ L) : G) : G ⧸ L) := by
        rw [QuotientGroup.eq]
        have : (r (a : G ⧸ L))⁻¹ * r (a' : G ⧸ L) = p * p'⁻¹ := by
          simp only [smul_eq_mul] at hpp
          calc (r (a : G ⧸ L))⁻¹ * r (a' : G ⧸ L)
              = (r (a : G ⧸ L))⁻¹ * (r (a' : G ⧸ L) * p') * p'⁻¹ := by group
            _ = p * p'⁻¹ := by rw [hpp]; group
        rw [this]
        exact L.mul_mem (hP hp) (L.inv_mem (hP hp'))
      rw [(hr a ha).2, (hr a' ha').2] at hq
      rw [hq]
    calc T.card * P.card = (T.biUnion (fun t => t • P)).card := by
          rw [Finset.card_biUnion hdisj]
          simp [Finset.card_smul_finset]
      _ ≤ (A * P).card := Finset.card_le_card hsub

/-- A Breuillard–Green–Tao approximate group contained in a subgroup `Γ` is an approximate
subgroup of `Γ`. -/
lemma isApproximateSubgroup_preimage_of_isBGT {G : Type*} [Group G] {K : ℝ} {S : Set G}
    (hS : IsBGTApproxGroup K S) (Γ : Subgroup G) (hSΓ : S ⊆ Γ) :
    IsApproximateSubgroup K (((↑) : Γ → G) ⁻¹' S) := by
  classical
  obtain ⟨-, h1, hinv, X, -, hX3, hXK, hcov⟩ := hS
  have hpow : ∀ n : ℕ, S ^ n ⊆ (Γ : Set G) := by
    intro n; induction n with
    | zero => intro x hx; rw [pow_zero, Set.mem_one] at hx; rw [hx]; exact Γ.one_mem
    | succ n ih =>
      rw [pow_succ]; rintro _ ⟨a, ha, b, hb, rfl⟩; exact Γ.mul_mem (ih ha) (hSΓ hb)
  refine ⟨h1, ?_, ?_⟩
  · ext x
    simp only [Set.mem_inv, Set.mem_preimage, Subgroup.coe_inv]
    rw [← Set.mem_inv, hinv]
  · refine ⟨X.subtype (· ∈ Γ), ?_, ?_⟩
    · calc ((X.subtype (· ∈ Γ)).card : ℝ) ≤ X.card := by
            exact_mod_cast (Finset.card_subtype _ _).trans_le (Finset.card_filter_le _ _)
        _ ≤ K := hXK
    · intro y hy
      rw [pow_two] at hy
      obtain ⟨a, ha, b, hb, rfl⟩ := hy
      have hab : (a : G) * b ∈ S * S := Set.mul_mem_mul ha hb
      obtain ⟨x, hx, s, hs, hxs⟩ := hcov hab
      have hxΓ : x ∈ Γ := hpow 3 (hX3 hx)
      have hsΓ : s ∈ Γ := hSΓ hs
      refine ⟨⟨x, hxΓ⟩, Finset.mem_subtype.2 hx, ⟨s, hsΓ⟩, hs, ?_⟩
      apply Subtype.ext
      simpa using hxs

end Aux

/-- **Reduction.**  Regularization (`StrongRegularization`) and step-independent uniformization for
finite nilpotent groups (`NilpotentFiniteCore`) together imply the reduced structure theorem
`FiniteBGTCore`, using the finitary nilpotence theorem proved in `BGTFiniteNilpotence.lean`. -/
theorem finiteBGTCore_of_regularization (hR : StrongRegularization)
    (hN : NilpotentFiniteCore) : FiniteBGTCore := by
  intro K hK
  obtain ⟨M, q, η, hM, hη, hReg⟩ := hR K hK
  obtain ⟨K', c, hc, hFN⟩ := BGT.finite_nilpotent_mod_zeroEsc.{0} M hM
  obtain ⟨cover₀, step, radius₀, hNil⟩ := hN (max K' 1) (le_max_right _ _)
  refine ⟨⌊K ^ (8 * q) * cover₀ / (c * η)⌋₊, step, 4 * q * radius₀ + q, ?_⟩
  intro G _ _ A hA
  classical
  haveI := Fintype.ofFinite G
  obtain ⟨B, hBs, hBA, hBcard⟩ := hReg G A hA
  obtain ⟨S, H, Γ, j, hSapp, hScard, hSB, hSΓ, -, hHB, hHΓ, hHn, hlcs⟩ := hFN B hBs
  have hA1 : (1 : G) ∈ A := hA.one_mem
  have hAinv : A⁻¹ = A := hA.inv_eq_self
  have hS1 : (1 : G) ∈ S := hSapp.2.1
  have hSinv : S⁻¹ = S := hSapp.2.2.1
  -- containments in powers of `A`
  have hSA : S ⊆ A ^ (4 * q) := by
    rw [mul_comm, pow_mul]; exact hSB.trans (Set.pow_subset_pow_left hBA)
  have hSinvA : S⁻¹ ⊆ A ^ (4 * q) := by rw [hSinv]; exact hSA
  -- the nilpotent quotient `Γ/H`
  set N := H.subgroupOf Γ with hNdef
  set π : Γ →* Γ ⧸ N := QuotientGroup.mk' N with hπ
  haveI : Group.IsNilpotent (Γ ⧸ N) := nilpotent_iff_lowerCentralSeries.2 ⟨j, by
    rw [← lowerCentralSeries_map_of_surjective π (QuotientGroup.mk'_surjective N), eq_bot_iff]
    rintro _ ⟨y, hy, rfl⟩
    exact (QuotientGroup.eq_one_iff _).2 (hlcs hy)⟩
  set SΓ : Set Γ := ((↑) : Γ → G) ⁻¹' S with hSΓdef
  have hSΓapp : IsApproximateSubgroup (max K' 1) SΓ :=
    (isApproximateSubgroup_preimage_of_isBGT hSapp Γ hSΓ).mono (le_max_left _ _)
  obtain ⟨Lb, ⟨Tb, hTb, hcovb⟩, hlcsb⟩ := hNil (Γ ⧸ N) (π '' SΓ) (hSΓapp.image π)
  set LΓ : Subgroup Γ := Lb.comap π with hLΓ
  set L : Subgroup G := LΓ.map Γ.subtype with hL
  refine ⟨L, ?_, ?_⟩
  · -- pigeonhole over the cosets `t • Lb` covering the image of `S`
    set SF : Finset Γ := SΓ.toFinset with hSF
    let f : Γ → Γ ⧸ N := fun y =>
      if h : ∃ t ∈ Tb, π y ∈ t • (Lb : Set (Γ ⧸ N)) then h.choose else 1
    have hf : ∀ y ∈ SF, f y ∈ Tb ∧ π y ∈ f y • (Lb : Set (Γ ⧸ N)) := by
      intro y hy
      have hy' : π y ∈ ⋃ t ∈ Tb, t • (Lb : Set (Γ ⧸ N)) :=
        hcovb ⟨y, Set.mem_toFinset.1 hy, rfl⟩
      simp only [Set.mem_iUnion] at hy'
      obtain ⟨t, ht, hyt⟩ := hy'
      have hex : ∃ t ∈ Tb, π y ∈ t • (Lb : Set (Γ ⧸ N)) := ⟨t, ht, hyt⟩
      have e : f y = hex.choose := dif_pos hex
      rw [e]; exact hex.choose_spec
    have hSF1 : (1 : Γ) ∈ SF := by
      rw [hSF, Set.mem_toFinset]; exact hS1
    have hTbne : Tb.Nonempty := ⟨f 1, (hf 1 hSF1).1⟩
    have hTbpos : (0 : ℝ) < Tb.card := by exact_mod_cast hTbne.card_pos
    obtain ⟨t0, -, hfib⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
      (fun y hy => (hf y hy).1) hTbne (b := (SF.card : ℝ) / Tb.card)
      (by rw [nsmul_eq_mul, mul_div_cancel₀ _ hTbpos.ne'])
    set F := SF.filter (fun y => f y = t0) with hF
    have hSFpos : (0 : ℝ) < SF.card := by exact_mod_cast Finset.card_pos.2 ⟨1, hSF1⟩
    have hFne : F.Nonempty := by
      rw [← Finset.card_pos]
      have : (0 : ℝ) < SF.card / Tb.card := by positivity
      exact_mod_cast this.trans_le hfib
    obtain ⟨s0, hs0⟩ := hFne
    have hFmem : ∀ y ∈ F, (y : G) ∈ S ∧ π y ∈ t0 • (Lb : Set (Γ ⧸ N)) := by
      intro y hy
      rw [hF, Finset.mem_filter] at hy
      have := (hf y hy.1).2
      rw [hy.2] at this
      exact ⟨(Set.mem_toFinset (s := SΓ)).1 hy.1, this⟩
    set P : Finset G := F.image (fun y => ((s0⁻¹ * y : Γ) : G)) with hP
    have hPL : (P : Set G) ⊆ L := by
      intro x hx
      rw [hP, Finset.coe_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      refine ⟨s0⁻¹ * y, ?_, rfl⟩
      show π (s0⁻¹ * y) ∈ Lb
      obtain ⟨a, ha, hya⟩ := (hFmem y hy).2
      obtain ⟨b, hb, hsb⟩ := (hFmem s0 hs0).2
      simp only [smul_eq_mul] at hya hsb
      rw [map_mul, map_inv, ← hya, ← hsb]
      have : (t0 * b)⁻¹ * (t0 * a) = b⁻¹ * a := by group
      rw [this]
      exact Lb.mul_mem (Lb.inv_mem hb) ha
    have hPcard : P.card = F.card := by
      rw [hP]
      apply Finset.card_image_of_injective
      intro y y' h
      exact mul_left_cancel (Subtype.val_injective h)
    have hAP : A.toFinset * P ⊆ A.toFinset ^ (8 * q + 1) := by
      intro x hx
      obtain ⟨a, ha, p, hp, rfl⟩ := Finset.mem_mul.1 hx
      rw [hP, Finset.mem_image] at hp
      obtain ⟨y, hy, rfl⟩ := hp
      rw [← Finset.mem_coe, Finset.coe_pow, Set.coe_toFinset, pow_succ',
        show 8 * q = 4 * q + 4 * q by ring, pow_add]
      refine Set.mul_mem_mul (Set.mem_toFinset.1 ha) (Set.mul_mem_mul ?_ ?_)
      · exact hSinvA (by simpa using (hFmem s0 hs0).1)
      · exact hSA (hFmem y hy).1
    obtain ⟨T, hTcov, hTcard⟩ := exists_coset_cover_card_mul_le A.toFinset P L hPL
    refine ⟨T, ?_, by simpa using hTcov⟩
    -- the counting estimate
    have hA' : IsApproximateSubgroup K (A.toFinset : Set G) := by rwa [Set.coe_toFinset]
    have hpowc := hA'.card_pow_le (n := 8 * q + 1)
    rw [Nat.add_sub_cancel] at hpowc
    have hAcard : (A.toFinset.card : ℝ) = A.ncard := by
      rw [Set.ncard_eq_toFinset_card']
    have hSFcard : (SF.card : ℝ) = S.ncard := by
      rw [hSF, ← Set.ncard_eq_toFinset_card', hSΓdef,
        Set.ncard_preimage_of_injective_subset_range Subtype.val_injective (by simpa using hSΓ)]
    have hApos : (0 : ℝ) < A.ncard := by
      rw [← hAcard]; exact_mod_cast Finset.card_pos.2 ⟨1, Set.mem_toFinset.2 hA1⟩
    have hTbc : (Tb.card : ℝ) ≤ cover₀ := by exact_mod_cast hTb
    have h1 : (T.card : ℝ) * F.card ≤ K ^ (8 * q) * A.ncard := by
      rw [← hAcard, ← hPcard]
      calc (T.card : ℝ) * P.card ≤ (A.toFinset * P).card := by exact_mod_cast hTcard
        _ ≤ (A.toFinset ^ (8 * q + 1)).card := by exact_mod_cast Finset.card_le_card hAP
        _ ≤ _ := hpowc
    have h2 : c * η * A.ncard ≤ F.card * cover₀ := by
      have e1 : (SF.card : ℝ) ≤ F.card * Tb.card := by
        rwa [div_le_iff₀ hTbpos] at hfib
      calc c * η * A.ncard = c * (η * A.ncard) := by ring
        _ ≤ c * B.ncard := by gcongr
        _ ≤ S.ncard := hScard
        _ = SF.card := hSFcard.symm
        _ ≤ F.card * Tb.card := e1
        _ ≤ F.card * cover₀ := by gcongr
    apply Nat.le_floor
    rw [le_div_iff₀ (by positivity)]
    have hT0 : (0 : ℝ) ≤ T.card := by positivity
    have h3 : (T.card : ℝ) * (c * η) * A.ncard ≤ K ^ (8 * q) * cover₀ * A.ncard := by
      calc (T.card : ℝ) * (c * η) * A.ncard = T.card * (c * η * A.ncard) := by ring
        _ ≤ T.card * (F.card * cover₀) := by gcongr
        _ = (T.card * F.card) * cover₀ := by ring
        _ ≤ (K ^ (8 * q) * A.ncard) * cover₀ := by gcongr
        _ = K ^ (8 * q) * cover₀ * A.ncard := by ring
    exact le_of_mul_le_mul_right h3 hApos
  · rintro _ ⟨z, hz, rfl⟩
    rw [← lowerCentralSeries_map_of_surjective _ (Γ.subtype.subgroupMap_surjective LΓ)] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    have hφ : π.subgroupComap Lb y ∈ (⊤ : Subgroup Lb).lowerCentralSeries step :=
      lowerCentralSeries.map _ step ⟨y, hy, rfl⟩
    have hmem : π (y : Γ) ∈ (π '' SΓ) ^ radius₀ := hlcsb ⟨_, hφ, rfl⟩
    rw [← Set.image_pow] at hmem
    obtain ⟨s, hs, hsy⟩ := hmem
    have hsy' : s⁻¹ * (y : Γ) ∈ N := QuotientGroup.eq.1 hsy
    have hsG : ((s : Γ) : G) ∈ A ^ (4 * q * radius₀) := by
      have h1 : ((s : Γ) : G) ∈ (Γ.subtype '' SΓ) ^ radius₀ := by
        rw [← Set.image_pow]; exact ⟨s, hs, rfl⟩
      have h2 : Γ.subtype '' SΓ ⊆ S := by rintro _ ⟨x, hx, rfl⟩; exact hx
      rw [pow_mul]
      exact Set.pow_subset_pow_left (h2.trans hSA) h1
    have hhG : ((s⁻¹ * (y : Γ) : Γ) : G) ∈ A ^ q := hBA (hHB hsy')
    show (((y : Γ) : G)) ∈ A ^ (4 * q * radius₀ + q)
    have e : ((y : Γ) : G) = ((s : Γ) : G) * ((s⁻¹ * (y : Γ) : Γ) : G) := by simp
    rw [e, pow_add]
    exact Set.mul_mem_mul hsG hhG

end Lovasz
