module
public import RequestProject.BGTFlexibleNilpotence
public import RequestProject.FinalGreenRuzsa

/-!
# The graph theorems from flexible regularization

`FlexibleRegularization` is the finitary target of the NSS route: every finite `K`-approximate
group `A` contains flexible trapping data `(B, S)` (`BGT.HasFlexibleTrapping`) with all parameters
`κ, p, m, N, q, r` bounded by a constant `b = b(K)`, with `B ⊆ A^q` and `|A| ≤ r |B|`.  Unlike
`StrongRegularization` it does not prescribe the trapping times `1000` and `⌈10⁶K³⌉`.

* `finiteBGTCore_of_flexibleRegularization`: `FlexibleRegularization → FiniteBGTCore`, using the
  flexible finitary nilpotence theorem `BGT.finite_nilpotent_mod_zeroEsc_flex` and the
  unconditional `nilpotentFiniteCore`;
* `cayley_long_path_of_flexibleRegularization`, `vt_long_path_of_flexibleRegularization`: the
  long-path theorems assuming only `FlexibleRegularization`.

The statements here take `FlexibleRegularization` as an explicit hypothesis; it is proved in
`FlexibleRegularizationProof.lean` (`Lovasz.flexibleRegularization`), where the unconditional
corollaries are also stated.

(This file is not a `module` because it imports non-module files.)
-/

@[expose] public section


open scoped Pointwise

namespace Lovasz

/-- **Flexible regularization** (the finitary target of the NSS route; proved in
`FlexibleRegularizationProof.lean`).  For
each `K ≥ 1` there is `b` such that every `K`-approximate subgroup `A` of a finite group has
flexible trapping data `(B, S)` with parameters `κ, p, m, N ≤ b`, together with `q, r ≤ b` such
that `B ⊆ A^q` and `|A| ≤ r |B|`. -/
def FlexibleRegularization : Prop :=
  ∀ K : ℝ, 1 ≤ K → ∃ b : ℕ,
    ∀ (G : Type) [Group G] [Finite G] (A : Set G), IsApproximateSubgroup K A →
      ∃ (B S : Set G) (κ p m N q r : ℕ), κ ≤ b ∧ p ≤ b ∧ m ≤ b ∧ N ≤ b ∧ q ≤ b ∧ r ≤ b ∧
        BGT.HasFlexibleTrapping κ p m N B S ∧ B ⊆ A ^ q ∧ (A.ncard : ℝ) ≤ r * B.ncard

/-- Monotonicity of the Breuillard–Green–Tao approximate-group predicate in its constant. -/
lemma IsBGTApproxGroup.mono_const {G : Type*} [Group G] {K K'' : ℝ} {S : Set G}
    (hS : IsBGTApproxGroup K S) (hK : K ≤ K'') : IsBGTApproxGroup K'' S := by
  obtain ⟨hf, h1, hinv, X, hXinv, hX3, hXK, hcov⟩ := hS
  exact ⟨hf, h1, hinv, X, hXinv, hX3, hXK.trans hK, hcov⟩

/-- Uniform finitary nilpotence data from flexible regularization: the constants are obtained by
taking a maximum/minimum over the finitely many parameter tuples bounded by `b`. -/
theorem uniform_nilpotent_data_of_flexibleRegularization (hR : FlexibleRegularization)
    (K : ℝ) (hK : 1 ≤ K) :
    ∃ (K' c : ℝ) (q : ℕ) (η : ℝ), 0 < c ∧ 0 < η ∧
      ∀ (G : Type) [Group G] [Finite G] (A : Set G), IsApproximateSubgroup K A →
        ∃ (B S : Set G) (H Γ : Subgroup G) (j : ℕ), IsBGTApproxGroup K' S ∧
          c * B.ncard ≤ S.ncard ∧ S ⊆ B ^ 4 ∧ S ⊆ Γ ∧ (H : Set G) ⊆ B ∧ H ≤ Γ ∧
          (H.subgroupOf Γ).Normal ∧ (⊤ : Subgroup Γ).lowerCentralSeries j ≤ H.subgroupOf Γ ∧
          B ⊆ A ^ q ∧ η * A.ncard ≤ B.ncard := by
  obtain ⟨b, hb⟩ := hR K hK
  choose Kf cf hcf hf using fun t : ℕ × ℕ × ℕ =>
    BGT.finite_nilpotent_mod_zeroEsc_flex.{0} t.1 t.2.1 t.2.2
  set T : Finset (ℕ × ℕ × ℕ) :=
    Finset.range (b + 1) ×ˢ Finset.range (b + 1) ×ˢ Finset.range (b + 1) with hT
  have hTne : T.Nonempty := ⟨(0, 0, 0), by simp [hT]⟩
  refine ⟨T.sup' hTne Kf, T.inf' hTne cf, b, 1 / (b + 1), ?_, by positivity, ?_⟩
  · rw [Finset.lt_inf'_iff]; exact fun t _ => hcf t
  intro G _ _ A hA
  obtain ⟨B, S, κ, p, m, N, q, r, hκb, hpb, hmb, -, hqb, hrb, htrap, hBA, hAB⟩ := hb G A hA
  have ht : (κ, p, m) ∈ T := by simp [hT]; omega
  obtain ⟨S', H, Γ, j, hSapp, hScard, hS4, hSΓ, -, hHB, hHΓ, hHn, hlcs⟩ :=
    hf (κ, p, m) N B S htrap
  refine ⟨B, S', H, Γ, j, hSapp.mono_const (Finset.le_sup' Kf ht), ?_, hS4, hSΓ, hHB, hHΓ,
    hHn, hlcs, hBA.trans (Set.pow_subset_pow_right hA.one_mem hqb), ?_⟩
  · calc T.inf' hTne cf * B.ncard ≤ cf (κ, p, m) * B.ncard := by
          gcongr; exact Finset.inf'_le cf ht
      _ ≤ S'.ncard := hScard
  · have hr : (r : ℝ) ≤ b + 1 := by
      have : (r : ℝ) ≤ b := by exact_mod_cast hrb
      linarith
    have : (A.ncard : ℝ) ≤ (b + 1) * B.ncard :=
      hAB.trans (mul_le_mul_of_nonneg_right hr (by positivity))
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    linarith

/-- **Reduction.**  Flexible regularization implies the reduced structure theorem
`FiniteBGTCore`, using the flexible finitary nilpotence theorem and the (proved)
step-independent structure theorem for finite nilpotent groups `nilpotentFiniteCore`. -/
theorem finiteBGTCore_of_flexibleRegularization (hR : FlexibleRegularization) :
    FiniteBGTCore := by
  intro K hK
  obtain ⟨K', c, q, η, hc, hη, hU⟩ := uniform_nilpotent_data_of_flexibleRegularization hR K hK
  obtain ⟨cover₀, step, radius₀, hNil⟩ := nilpotentFiniteCore (max K' 1) (le_max_right _ _)
  refine ⟨⌊K ^ (8 * q) * cover₀ / (c * η)⌋₊, step, 4 * q * radius₀ + q, ?_⟩
  intro G _ _ A hA
  classical
  haveI := Fintype.ofFinite G
  obtain ⟨B, S, H, Γ, j, hSapp, hScard, hSB, hSΓ, hHB, hHΓ, hHn, hlcs, hBA, hBcard⟩ := hU G A hA
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


/-- **Theorem 3.17** (Cayley case) assuming only flexible regularization. -/
theorem cayley_long_path_of_flexibleRegularization (hR : FlexibleRegularization) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (H : Type) [Group H] [Finite H] (S : Set H),
      (cay S).Connected → n₀ ≤ Nat.card H →
      ∃ l : List H, IsPathL (cay S) l ∧ (Nat.card H : ℝ) ^ (1 - ε) ≤ (l.length : ℝ) - 1 :=
  cayley_long_path_of_finiteCore (finiteBGTCore_of_flexibleRegularization hR)

/-- **Theorem A.1** (vertex-transitive case) assuming only flexible regularization. -/
theorem vt_long_path_of_flexibleRegularization (hR : FlexibleRegularization) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (X : SimpleGraph V),
      X.Connected → VertexTransitive X → n₀ ≤ Fintype.card V →
      ∃ l : List V, IsPathL X l ∧ (Fintype.card V : ℝ) ^ (1 - ε) ≤ (l.length : ℝ) - 1 :=
  vt_long_path_of_finiteCore (finiteBGTCore_of_flexibleRegularization hR) Tointon.greenRuzsaRank

end Lovasz
