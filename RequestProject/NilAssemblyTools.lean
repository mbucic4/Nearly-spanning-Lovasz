module
public import RequestProject.NilCentral
public import RequestProject.NilCommWidth
public import RequestProject.NilLayers

/-!
# Relative forms of the finite tools, for the downward induction

The downward induction (Tointon, Proposition 5.1) works inside a finite nilpotent group `Γ`
with a *filtration* `P : ℕ → Set Γ` modelling the sets `A^m ∩ C`.  This file proves the relative
(quotient-free) versions of central saturation and of the Green–Ruzsa rank step that it uses.
-/

@[expose] public section

open scoped Pointwise commutatorElement

namespace Tointon

variable {Γ : Type} [Group Γ]

/-- A filtration modelling `m ↦ A^m ∩ C` for a `κ`-approximate group `A`. -/
structure Filt (κ : ℕ) (P : ℕ → Set Γ) : Prop where
  one_mem : (1 : Γ) ∈ P 0
  mono : ∀ {m n : ℕ}, m ≤ n → P m ⊆ P n
  mul : ∀ m n, P m * P n ⊆ P (m + n)
  inv : ∀ m, (P m)⁻¹ = P m
  approx : ∀ (E : Subgroup Γ) (m : ℕ), 2 ≤ m →
    IsApproximateSubgroup (((κ ^ (2 * m - 1) : ℕ)) : ℝ) (P m ∩ E)

namespace Filt

variable {κ : ℕ} {P : ℕ → Set Γ} (hP : Filt κ P)
include hP

lemma one_mem' (m : ℕ) : (1 : Γ) ∈ P m := hP.mono (Nat.zero_le m) hP.one_mem

lemma mul_mem {m n : ℕ} {x y : Γ} (hx : x ∈ P m) (hy : y ∈ P n) : x * y ∈ P (m + n) :=
  hP.mul m n (Set.mul_mem_mul hx hy)

lemma inv_mem {m : ℕ} {x : Γ} (hx : x ∈ P m) : x⁻¹ ∈ P m := by
  rw [← hP.inv m]; simpa using hx

lemma pow_subset (m : ℕ) : ∀ f : ℕ, (P m) ^ f ⊆ P (m * f)
  | 0 => by simpa using hP.one_mem
  | f + 1 => by
    rw [pow_succ]
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    have := hP.mul_mem (pow_subset m f ha) hb
    rwa [show m * f + m = m * (f + 1) by ring] at this

lemma comm_mem {a b : ℕ} {x y : Γ} (hx : x ∈ P a) (hy : y ∈ P b) : ⁅x, y⁆ ∈ P (2 * a + 2 * b) := by
  rw [commutatorElement_def]
  have := hP.mul_mem (hP.mul_mem (hP.mul_mem hx hy) (hP.inv_mem hx)) (hP.inv_mem hy)
  rwa [show a + b + a + b = 2 * a + 2 * b by ring] at this

/-- Products in `P a * N` with `N` normal. -/
lemma mul_mem_mul_normal {N : Subgroup Γ} [hN : N.Normal] {a b : ℕ} {x y : Γ}
    (hx : x ∈ P a * (N : Set Γ)) (hy : y ∈ P b * (N : Set Γ)) : x * y ∈ P (a + b) * (N : Set Γ) := by
  obtain ⟨p, hp, n, hn, rfl⟩ := hx
  obtain ⟨q, hq, n', hn', rfl⟩ := hy
  refine ⟨p * q, hP.mul_mem hp hq, q⁻¹ * n * q * n', N.mul_mem ?_ hn', by group⟩
  simpa using hN.conj_mem n hn q⁻¹

lemma subset_mul_normal_mono {N : Subgroup Γ} {a b : ℕ} (hab : a ≤ b) :
    P a * (N : Set Γ) ⊆ P b * (N : Set Γ) :=
  Set.mul_subset_mul_right (hP.mono hab)

/-- A product of `ℓ` elements of `P c * N` lies in `P (ℓ c) * N`. -/
lemma list_prod_mem {N : Subgroup Γ} [N.Normal] {c : ℕ} :
    ∀ l : List Γ, (∀ x ∈ l, x ∈ P c * (N : Set Γ)) → l.prod ∈ P (l.length * c) * (N : Set Γ)
  | [], _ => ⟨1, by simpa using hP.one_mem, 1, N.one_mem, by simp⟩
  | x :: l, h => by
    rw [List.prod_cons, List.length_cons]
    have := hP.mul_mem_mul_normal (h x (by simp)) (list_prod_mem l fun y hy => h y (by simp [hy]))
    rwa [show c + l.length * c = (l.length + 1) * c by ring] at this

end Filt

lemma exists_eq_mk_of_image_pow {Q : Type*} [Group Q] (E : Subgroup Γ) (π : E →* Q)
    {S : Set Γ} {n : ℕ} {q : Q} (hq : q ∈ (π '' ((↑) ⁻¹' S : Set E)) ^ n) :
    ∃ s : E, s ∈ ((↑) ⁻¹' S : Set E) ^ n ∧ π s = q := by
  rw [← Set.image_pow] at hq
  exact hq

lemma coe_mem_pow_of_mem_pow (E : Subgroup Γ) {S : Set Γ} {n : ℕ} {s : E}
    (hs : s ∈ ((↑) ⁻¹' S : Set E) ^ n) : (s : Γ) ∈ S ^ n := by
  have h := Set.mem_image_of_mem E.subtype hs
  rw [Set.image_pow] at h
  exact Set.pow_subset_pow_left (Set.image_preimage_subset _ _) h

lemma map_subtype_commutator_top (E : Subgroup Γ) :
    Subgroup.map E.subtype ⁅(⊤ : Subgroup E), ⊤⁆ = ⁅E, E⁆ := by
  rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

/-- **Central saturation, relative form.**  Let `Dᵢ ≤ E` with `Dᵢ` normal, let `S ⊆ E` be an
`M`-approximate group, and suppose `E = S ⟨z⟩ Dᵢ` with `z ∈ E` central in `E` modulo `Dᵢ`.
Then `[E, E] ⊆ S^(8M⁸ + 4) Dᵢ`. -/
theorem saturation_rel [Finite Γ] [Group.IsNilpotent Γ] {E Di : Subgroup Γ} [hDi : Di.Normal]
    {S : Set Γ} (hSE : S ⊆ E) {M : ℕ} (hS : IsApproximateSubgroup (M : ℝ) S) {zz : Γ}
    (hzE : zz ∈ E) (hzc : ∀ e ∈ E, ⁅zz, e⁆ ∈ Di)
    (hcov : ∀ e ∈ E, ∃ s ∈ S, ∃ k : ℤ, ∃ d ∈ Di, e = s * zz ^ k * d) :
    ((⁅E, E⁆ : Subgroup Γ) : Set Γ) ⊆ S ^ (8 * M ^ 8 + 4) * (Di : Set Γ) := by
  classical
  set N := Di.subgroupOf E with hN
  set π := QuotientGroup.mk' N with hπ
  set S' : Set E := (↑) ⁻¹' S with hS'def
  have hS' : IsApproximateSubgroup (M : ℝ) S' := isApproximateSubgroup_preimage_subtype hS hSE
  have hA : IsApproximateSubgroup (M : ℝ) (π '' S') := hS'.image π
  have hzcent : π (⟨zz, hzE⟩ : E) ∈ Subgroup.center (E ⧸ N) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨e, rfl⟩ := QuotientGroup.mk'_surjective N g
    have h1 : π ⁅(⟨zz, hzE⟩ : E), e⁆ = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf]
      exact hzc e e.2
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have hcovQ : ∀ q : E ⧸ N, ∃ a ∈ π '' S', ∃ w ∈ Subgroup.center (E ⧸ N), q = a * w := by
    intro q
    obtain ⟨e, rfl⟩ := QuotientGroup.mk'_surjective N q
    obtain ⟨s, hs, k, d, hd, he⟩ := hcov e e.2
    have hdE : d ∈ E := by
      have : d = (s * zz ^ k)⁻¹ * e := by rw [he]; group
      rw [this]
      exact E.mul_mem (E.inv_mem (E.mul_mem (hSE hs) (E.zpow_mem hzE k))) e.2
    refine ⟨π (⟨s, hSE hs⟩ : E), ⟨⟨s, hSE hs⟩, hs, rfl⟩, π (⟨zz, hzE⟩ : E) ^ k,
      Subgroup.zpow_mem _ hzcent k, ?_⟩
    have hee : e = ⟨s, hSE hs⟩ * ⟨zz, hzE⟩ ^ k * ⟨d, hdE⟩ := by
      apply Subtype.ext; simp [he]
    have hd1 : π (⟨d, hdE⟩ : E) = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf]
      exact hd
    rw [hee, map_mul, map_mul, hd1, mul_one, map_zpow]
  have hsat := derived_subset_pow_of_mul_center_eq_univ hA hcovQ
  intro x hx
  rw [← map_subtype_commutator_top] at hx
  obtain ⟨x', hx', rfl⟩ := hx
  have hmapc : Subgroup.map π ⁅(⊤ : Subgroup E), ⊤⁆ = ⁅(⊤ : Subgroup (E ⧸ N)), ⊤⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective N)]
  have hx'' : π x' ∈ ⁅(⊤ : Subgroup (E ⧸ N)), ⊤⁆ := hmapc ▸ Subgroup.mem_map_of_mem π hx'
  obtain ⟨s', hs', he'⟩ := exists_eq_mk_of_image_pow E π (hsat hx'')
  refine ⟨s', coe_mem_pow_of_mem_pow E hs', ((s'⁻¹ * x' : E) : Γ), ?_, by simp⟩
  have : s'⁻¹ * x' ∈ N := by
    rw [← QuotientGroup.eq_one_iff (N := N)]
    change π (s'⁻¹ * x') = 1
    rw [map_mul, map_inv, he', inv_mul_cancel]
  exact this

/-- The Green–Ruzsa conclusion at a fixed approximation constant `M`, with rank `d` and
exponent `c`. -/
def GRAt (M : ℝ) (d c : ℕ) : Prop :=
  ∀ (Z : Type) [CommGroup Z] [Finite Z] (B : Set Z), IsApproximateSubgroup M B →
    ∃ (H : Subgroup Z) (X : Finset Z), (H : Set Z) ⊆ B ^ c ∧ (X : Set Z) ⊆ B ^ c ∧ X.card ≤ d ∧
      B ⊆ (H : Set Z) * (Subgroup.closure (X : Set Z) : Set Z)

/-- **The Green–Ruzsa step, relative form.**  Let `N ≤ E` with `N` normal and `E / N` abelian,
and let `S ⊆ E` be an `M`-approximate group generating `E` modulo `N`.  Then there are a subgroup
`N ≤ J ≤ E` with `J ⊆ S^c N` and a set `Y ⊆ S^c` of at most `d` elements with `E ≤ ⟨Y, J⟩`. -/
theorem gr_rel [Finite Γ] {E N : Subgroup Γ} [hN : N.Normal] (hNE : N ≤ E) (hEE : ⁅E, E⁆ ≤ N)
    {S : Set Γ} (hSE : S ⊆ E) {M : ℝ} (hS : IsApproximateSubgroup M S)
    (hgen : E ≤ Subgroup.closure S ⊔ N) {d c : ℕ} (hGRM : GRAt M d c) :
    ∃ J : Subgroup Γ, N ≤ J ∧ J ≤ E ∧ (J : Set Γ) ⊆ S ^ c * (N : Set Γ) ∧
      ∃ Y : Finset Γ, (Y : Set Γ) ⊆ S ^ c ∧ Y.card ≤ d ∧
        E ≤ Subgroup.closure ((Y : Set Γ) ∪ (J : Set Γ)) := by
  classical
  set N' := N.subgroupOf E with hN'
  set π := QuotientGroup.mk' N' with hπ
  set S' : Set E := (↑) ⁻¹' S with hS'def
  have hS' : IsApproximateSubgroup M S' := isApproximateSubgroup_preimage_subtype hS hSE
  have hT : IsApproximateSubgroup M (π '' S') := hS'.image π
  have hmemN' : ∀ x : E, x ∈ N' ↔ (x : Γ) ∈ N := fun x => Subgroup.mem_subgroupOf
  have hcomm : ∀ a b : E ⧸ N', a * b = b * a := by
    intro a b
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective N' a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective N' b
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      hmemN']
    have : (((a * b)⁻¹ * (b * a) : E) : Γ) = ⁅(b : Γ)⁻¹, (a : Γ)⁻¹⁆ := by
      simp only [commutatorElement_def]; push_cast; group
    rw [this]
    exact hEE (Subgroup.commutator_mem_commutator (E.inv_mem b.2) (E.inv_mem a.2))
  letI : CommGroup (E ⧸ N') := { (inferInstance : Group (E ⧸ N')) with mul_comm := hcomm }
  obtain ⟨J, Yb, hJ, hYb, hYcard, hTsub⟩ := hGRM (E ⧸ N') (π '' S') hT
  -- lifts of the generators
  have hlift : ∀ y ∈ Yb, ∃ s : E, s ∈ S' ^ c ∧ π s = y := fun y hy =>
    exists_eq_mk_of_image_pow E π (hYb hy)
  choose! lift hliftS hliftπ using hlift
  set J' : Subgroup Γ := (J.comap π).map E.subtype with hJ'
  set Y : Finset Γ := Yb.image fun y => ((lift y : E) : Γ) with hY
  have hker : ∀ x : E, (x : Γ) ∈ N → π x = 1 := fun x hx => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hmemN']; exact hx
  refine ⟨J', ?_, ?_, ?_, Y, ?_, ?_, ?_⟩
  · intro n hn
    refine ⟨⟨n, hNE hn⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, hker ⟨n, hNE hn⟩ hn]; exact J.one_mem
  · rintro _ ⟨x, -, rfl⟩; exact x.2
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨s, hs, hse⟩ := exists_eq_mk_of_image_pow E π (hJ hx)
    refine ⟨s, coe_mem_pow_of_mem_pow E hs, ((s⁻¹ * x : E) : Γ), ?_, by simp⟩
    rw [SetLike.mem_coe, ← hmemN', ← QuotientGroup.eq_one_iff (N := N')]
    change π (s⁻¹ * x) = 1
    rw [map_mul, map_inv, hse, inv_mul_cancel]
  · intro y hy
    simp only [hY, Finset.coe_image, Set.mem_image] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    exact coe_mem_pow_of_mem_pow E (hliftS y' hy')
  · exact Finset.card_image_le.trans hYcard
  · intro e he
    -- `π e` lies in the closure of the image of `S'`
    set L : Subgroup Γ := ((Subgroup.closure (π '' S')).comap π).map E.subtype with hL
    have hEL : E ≤ L := by
      refine hgen.trans (sup_le ?_ ?_)
      · rw [Subgroup.closure_le]
        intro s hs
        exact ⟨⟨s, hSE hs⟩, Subgroup.subset_closure ⟨⟨s, hSE hs⟩, hs, rfl⟩, rfl⟩
      · intro n hn
        refine ⟨⟨n, hNE hn⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_comap, hker ⟨n, hNE hn⟩ hn]; exact Subgroup.one_mem _
    obtain ⟨e', he', hee'⟩ := hEL he
    have he'' : e' = ⟨e, he⟩ := Subtype.ext hee'
    subst he''
    have hcl : Subgroup.closure (π '' S') ≤ J ⊔ Subgroup.closure (Yb : Set (E ⧸ N')) := by
      rw [Subgroup.closure_le]
      intro t ht
      obtain ⟨j, hj, w, hw, rfl⟩ := hTsub ht
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hj) (Subgroup.mem_sup_right hw)
    obtain ⟨j, hj, w, hw, hjw⟩ := Subgroup.mem_sup.1 (hcl he')
    -- lift `w`
    have hYcl : Subgroup.closure (Yb : Set (E ⧸ N')) ≤
        (Subgroup.closure (lift '' (Yb : Set (E ⧸ N')))).map π := by
      rw [Subgroup.closure_le]
      intro y hy
      exact ⟨lift y, Subgroup.subset_closure ⟨y, hy, rfl⟩, hliftπ y hy⟩
    obtain ⟨w', hw', rfl⟩ := hYcl hw
    have hmemJ : ((⟨e, he⟩ : E) * w'⁻¹ : E) ∈ J.comap π := by
      rw [Subgroup.mem_comap, map_mul, map_inv, ← hjw, mul_inv_cancel_right]; exact hj
    have hw'Y : (w' : Γ) ∈ Subgroup.closure (Y : Set Γ) := by
      have h1 : (w' : Γ) ∈ (Subgroup.closure (lift '' (Yb : Set (E ⧸ N')))).map E.subtype :=
        ⟨w', hw', rfl⟩
      rw [MonoidHom.map_closure] at h1
      have h2 : (E.subtype '' (lift '' (Yb : Set (E ⧸ N')))) = (Y : Set Γ) := by
        ext x; simp [hY]
      rwa [h2] at h1
    have : e = (((⟨e, he⟩ : E) * w'⁻¹ : E) : Γ) * (w' : Γ) := by simp
    rw [this]
    refine Subgroup.mul_mem _ ?_ ?_
    · exact Subgroup.subset_closure (Or.inr ⟨_, hmemJ, rfl⟩)
    · exact (Subgroup.closure_mono Set.subset_union_left) hw'Y

end Tointon
