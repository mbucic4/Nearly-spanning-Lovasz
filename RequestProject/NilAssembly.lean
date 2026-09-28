module
public import RequestProject.NilAssemblyTools

/-!
# The downward induction (Tointon, Proposition 5.1), inside the ambient group `C`

We work in a finite nilpotent group `Γ` (in the application, `Γ = C` from the layer
construction) with a filtration `P` modelling `m ↦ A^m ∩ C`, and layer data
`D₁ ≤ ⋯ ≤ D_{k+1} = Γ`, `zᵢ`.  Using the Green–Ruzsa rank theorem once per layer we build normal
subgroups `E_{k+1} = Γ ≥ E_k ≥ ⋯ ≥ E₁` with `[Γ, E_{i+1}] ≤ E_i` and `E_i ⊆ P(b) Dᵢ`, where the
exponents `b` follow an explicit recurrence depending only on `κ`.
-/

@[expose] public section

open scoped Pointwise commutatorElement

namespace Tointon

variable {Γ : Type} [Group Γ]

/-- Layer data inside `Γ`. -/
structure LayersIn (P : ℕ → Set Γ) (k : ℕ) (D : ℕ → Subgroup Γ) (z : ℕ → Γ) : Prop where
  hDtop : D (k + 1) = ⊤
  hD1 : (D 1 : Set Γ) ⊆ P 2
  hmono : ∀ i, 1 ≤ i → i ≤ k → D i ≤ D (i + 1)
  hDn : ∀ i, 1 ≤ i → i ≤ k + 1 → (D i).Normal
  hz6 : ∀ i, 1 ≤ i → i ≤ k → z i ∈ P 6
  hzD : ∀ i, 1 ≤ i → i ≤ k → z i ∈ D (i + 1)
  hcent : ∀ i, 1 ≤ i → i ≤ k → ∀ c, ⁅z i, c⁆ ∈ D i
  hstep : ∀ i, 1 ≤ i → i ≤ k → ∀ x ∈ D (i + 1), ∃ p ∈ P 2, ∃ n : ℤ, ∃ d ∈ D i, x = p * z i ^ n * d

/-- The exponent produced by one step of the downward induction. -/
def stepB (κ b r a c : ℕ) : ℕ :=
  max 6 (b + 2) * c + (max 6 (b + 2) * (8 * (κ ^ (2 * max 6 (b + 2) - 1)) ^ 8 + 4) +
    r * (2 * a + 2 * max 6 (b + 2)))

/-- **One step of the downward induction.** -/
theorem downward_step [Finite Γ] [Group.IsNilpotent Γ] {κ : ℕ} {P : ℕ → Set Γ} (hP : Filt κ P)
    {Di Di1 : Subgroup Γ} [hDi : Di.Normal] (hDD : Di ≤ Di1) {zz : Γ} (hz6 : zz ∈ P 6)
    (hzD : zz ∈ Di1) (hcent : ∀ c, ⁅zz, c⁆ ∈ Di)
    (hstep : ∀ x ∈ Di1, ∃ p ∈ P 2, ∃ n : ℤ, ∃ d ∈ Di, x = p * zz ^ n * d)
    {E : Subgroup Γ} [hE : E.Normal] (hDE : Di1 ≤ E) {b r a : ℕ}
    (hEb : (E : Set Γ) ⊆ P b * (Di1 : Set Γ))
    (F : Finset Γ) (hFr : F.card ≤ r) (hFa : (F : Set Γ) ⊆ P a)
    (hgen : Subgroup.closure ((F : Set Γ) ∪ E) = ⊤)
    {d c : ℕ} (hGRM : GRAt ((κ ^ (2 * max 6 (b + 2) - 1) : ℕ) : ℝ) d c) :
    ∃ E' : Subgroup Γ, E'.Normal ∧ Di ≤ E' ∧ ⁅(⊤ : Subgroup Γ), E⁆ ≤ E' ∧
      (E' : Set Γ) ⊆ P (stepB κ b r a c) * (Di : Set Γ) ∧
      ∃ F' : Finset Γ, F'.card ≤ r + d ∧ (F' : Set Γ) ⊆ P (max a (max 6 (b + 2) * c)) ∧
        Subgroup.closure ((F' : Set Γ) ∪ E') = ⊤ := by
  classical
  set m := max 6 (b + 2) with hm
  set M : ℕ := κ ^ (2 * m - 1) with hM
  set f := 8 * M ^ 8 + 4 with hf
  set S : Set Γ := P m ∩ (E : Set Γ) with hSdef
  have hS : IsApproximateSubgroup (M : ℝ) S := hP.approx E m (by omega)
  have hSE : S ⊆ E := Set.inter_subset_right
  have hzE : zz ∈ E := hDE hzD
  have hzS : zz ∈ S := ⟨hP.mono (by omega) hz6, hzE⟩
  have hDiE : Di ≤ E := hDD.trans hDE
  have hSpow : ∀ n, S ^ n ⊆ P (m * n) := fun n =>
    (Set.pow_subset_pow_left Set.inter_subset_left).trans (hP.pow_subset m n)
  -- 8.1: `E = S ⟨z⟩ Dᵢ`
  have hcov : ∀ e ∈ E, ∃ s ∈ S, ∃ n : ℤ, ∃ d ∈ Di, e = s * zz ^ n * d := by
    intro e he
    obtain ⟨p, hp, d1, hd1, rfl⟩ := hEb he
    obtain ⟨q, hq, n, d, hd, rfl⟩ := hstep d1 hd1
    have hpq : p * q ∈ E := by
      have e1 : p * q = p * (q * zz ^ n * d) * (zz ^ n * d)⁻¹ := by group
      rw [e1]
      exact E.mul_mem he (E.inv_mem (E.mul_mem (E.zpow_mem hzE n) (hDiE hd)))
    refine ⟨p * q, ⟨hP.mono (by omega) (hP.mul_mem hp hq), hpq⟩, n, d, hd, by group⟩
  -- 8.2: `[E, E] ⊆ P(m f) Dᵢ`
  have hsat := saturation_rel hSE hS hzE (fun e _ => hcent e) hcov
  have hEE : ((⁅E, E⁆ : Subgroup Γ) : Set Γ) ⊆ P (m * f) * (Di : Set Γ) :=
    hsat.trans (Set.mul_subset_mul_right (hSpow f))
  set Dp : Subgroup Γ := ⁅E, E⁆ ⊔ Di with hDp
  have hDpS : (Dp : Set Γ) ⊆ P (m * f) * (Di : Set Γ) := by
    intro x hx
    rw [hDp, Subgroup.mul_normal] at hx
    obtain ⟨y, hy, n, hn, rfl⟩ := hx
    have := hP.mul_mem_mul_normal (hEE hy) ⟨1, hP.one_mem, n, hn, one_mul n⟩
    simpa using this
  -- 8.3: commutators with `E`
  have hgenl : Subgroup.closure ({x | x ∈ F.toList} ∪ (E : Set Γ)) = ⊤ := by
    rw [← hgen]; congr 1; ext x; simp
  have hfac : ∀ x ∈ F, ∀ dd ∈ E, ⁅x, dd⁆ ∈ P (2 * a + 2 * m) * (Di : Set Γ) := by
    intro x hx dd hdd
    obtain ⟨s, hs, n, d0, hd0, rfl⟩ := hcov dd hdd
    refine ⟨⁅x, s⁆, hP.comm_mem (hFa hx) hs.1, ⁅x, s⁆⁻¹ * ⁅x, s * zz ^ n * d0⁆, ?_, by group⟩
    set π := QuotientGroup.mk' Di
    have hzc : ∀ g : Γ ⧸ Di, π zz * g = g * π zz := by
      intro g
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Di g
      have h1 : π ⁅zz, g⁆ = 1 := (QuotientGroup.eq_one_iff _).2 (hcent g)
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have hd01 : π d0 = 1 := (QuotientGroup.eq_one_iff _).2 hd0
    rw [SetLike.mem_coe, ← QuotientGroup.eq_one_iff (N := Di)]
    change π (⁅x, s⁆⁻¹ * ⁅x, s * zz ^ n * d0⁆) = 1
    rw [map_mul, map_inv, map_commutatorElement, map_commutatorElement, map_mul, map_mul, hd01,
      mul_one, map_zpow]
    have hzk : ∀ g : Γ ⧸ Di, π zz ^ n * g = g * π zz ^ n := fun g =>
      ((Commute.zpow_left (hzc g) n))
    rw [inv_mul_eq_one]
    simp only [commutatorElement_def]
    calc π x * π s * (π x)⁻¹ * (π s)⁻¹
        = π x * π s * ((π x)⁻¹ * π zz ^ n) * ((π zz ^ n)⁻¹ * (π s)⁻¹) := by group
      _ = π x * π s * (π zz ^ n * (π x)⁻¹) * ((π zz ^ n)⁻¹ * (π s)⁻¹) := by rw [hzk (π x)⁻¹]
      _ = _ := by group
  have hcomm : ∀ g ∈ ⁅(⊤ : Subgroup Γ), E⁆, ∃ y ∈ P (r * (2 * a + 2 * m)) * (Di : Set Γ),
      ∃ n ∈ Dp, g = y * n := by
    intro g hg
    obtain ⟨ds, hlen, hds, n, hn, rfl⟩ :=
      exists_commutator_product (N := Dp) hE le_sup_left F.toList hgenl g hg
    refine ⟨commProd F.toList ds, ?_, n, hn, rfl⟩
    have hmem : ∀ y ∈ List.zipWith (fun x d => ⁅x, d⁆) F.toList ds,
        y ∈ P (2 * a + 2 * m) * (Di : Set Γ) := by
      intro y hy
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hy
      rw [List.getElem_zipWith]
      exact hfac _ (Finset.mem_toList.1 (List.getElem_mem _)) _ (hds _ (List.getElem_mem _))
    have := hP.list_prod_mem _ hmem
    rw [List.length_zipWith, hlen, min_self, Finset.length_toList] at this
    exact hP.subset_mul_normal_mono (Nat.mul_le_mul_right _ hFr) this
  set u := m * f + r * (2 * a + 2 * m) with hu
  set Ddd : Subgroup Γ := ⁅(⊤ : Subgroup Γ), E⁆ ⊔ Dp with hDdd
  have hDddS : (Ddd : Set Γ) ⊆ P u * (Di : Set Γ) := by
    intro x hx
    rw [hDdd, Subgroup.mul_normal] at hx
    obtain ⟨g, hg, n, hn, rfl⟩ := hx
    obtain ⟨y, hy, n1, hn1, rfl⟩ := hcomm g hg
    have := hP.mul_mem_mul_normal hy (hDpS (Dp.mul_mem hn1 hn))
    show y * n1 * n ∈ _
    rw [mul_assoc]
    exact hP.subset_mul_normal_mono (by omega) this
  -- 8.4: the Green–Ruzsa step
  have hEE' : ⁅E, E⁆ ≤ Ddd := le_sup_left.trans le_sup_right
  have hEEle : ⁅E, E⁆ ≤ E := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact E.mul_mem (E.mul_mem (E.mul_mem hx hy) (E.inv_mem hx)) (E.inv_mem hy)
  have hDddE : Ddd ≤ E := sup_le (Subgroup.commutator_le_right _ _) (sup_le hEEle hDiE)
  have hDiDdd : Di ≤ Ddd := le_sup_right.trans le_sup_right
  have hgenS : E ≤ Subgroup.closure S ⊔ Ddd := by
    intro e he
    obtain ⟨s, hs, n, d0, hd0, rfl⟩ := hcov e he
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) (Subgroup.mem_sup_right (hDiDdd hd0))
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure hs)
    · exact Subgroup.mem_sup_left (Subgroup.zpow_mem _ (Subgroup.subset_closure hzS) n)
  obtain ⟨J, hNJ, hJE, hJS, Y, hYS, hYd, hEY⟩ := gr_rel hDddE hEE' hSE hS hgenS hGRM
  refine ⟨J, ?_, hDiDdd.trans hNJ, le_sup_left.trans hNJ, ?_, F ∪ Y, ?_, ?_, ?_⟩
  · constructor
    intro x hx g
    have e1 : g * x * g⁻¹ = ⁅g, x⁆ * x := by simp only [commutatorElement_def]; group
    rw [e1]
    exact J.mul_mem (hNJ (Subgroup.mem_sup_left
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (hJE hx)))) hx
  · intro x hx
    obtain ⟨s, hs, n, hn, rfl⟩ := hJS hx
    have := hP.mul_mem_mul_normal ⟨s, hSpow c hs, 1, Di.one_mem, mul_one s⟩ (hDddS hn)
    refine hP.subset_mul_normal_mono ?_ this
    simp only [stepB, ← hm, ← hM, ← hf, ← hu]
    omega
  · exact (Finset.card_union_le _ _).trans (Nat.add_le_add hFr hYd)
  · rw [Finset.coe_union]
    refine Set.union_subset (hFa.trans (hP.mono (le_max_left _ _))) ?_
    exact hYS.trans ((hSpow c).trans (hP.mono (le_max_right _ _)))
  · rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro x (hx | hx)
    · exact Subgroup.subset_closure (Or.inl (by rw [Finset.coe_union]; exact Or.inl hx))
    · refine (Subgroup.closure_mono ?_) (hEY hx)
      rw [Finset.coe_union]
      exact Set.union_subset_union_left _ Set.subset_union_right

/-- Rank and exponent functions chosen once and for all from `GreenRuzsaRank`; they depend only on
the approximation constant `M`. -/
noncomputable def grDC (hGR : GreenRuzsaRank) (M : ℕ) : ℕ × ℕ :=
  if h : (1 : ℝ) ≤ M then ((hGR M h).choose, (hGR M h).choose_spec.choose) else (0, 0)

lemma grAt_grDC (hGR : GreenRuzsaRank) {M : ℕ} (hM : 1 ≤ M) :
    GRAt (M : ℝ) (grDC hGR M).1 (grDC hGR M).2 := by
  have h : (1 : ℝ) ≤ M := by exact_mod_cast hM
  simp only [grDC, dif_pos h]
  exact (hGR M h).choose_spec.choose_spec

/-- The explicit schedule `(b_t, r_t, a_t)` of the downward induction; it depends only on `κ`
(and on the chosen Green–Ruzsa functions). -/
noncomputable def sched (hGR : GreenRuzsaRank) (κ : ℕ) : ℕ → ℕ × ℕ × ℕ
  | 0 => (0, 0, 0)
  | t + 1 =>
    ((stepB κ (sched hGR κ t).1 (sched hGR κ t).2.1 (sched hGR κ t).2.2
        (grDC hGR (κ ^ (2 * max 6 ((sched hGR κ t).1 + 2) - 1))).2),
      (sched hGR κ t).2.1 + (grDC hGR (κ ^ (2 * max 6 ((sched hGR κ t).1 + 2) - 1))).1,
      max (sched hGR κ t).2.2
        (max 6 ((sched hGR κ t).1 + 2) * (grDC hGR (κ ^ (2 * max 6 ((sched hGR κ t).1 + 2) - 1))).2))

/-- **The downward induction.** -/
theorem downward (hGR : GreenRuzsaRank) [Finite Γ] [Group.IsNilpotent Γ] {κ : ℕ} (hκ : 1 ≤ κ)
    {P : ℕ → Set Γ} (hP : Filt κ P) {k : ℕ} {D : ℕ → Subgroup Γ} {z : ℕ → Γ}
    (hL : LayersIn P k D z) :
    ∀ t, t ≤ k → ∃ E : Subgroup Γ, E.Normal ∧ D (k + 1 - t) ≤ E ∧
      (E : Set Γ) ⊆ P (sched hGR κ t).1 * (D (k + 1 - t) : Set Γ) ∧
      (⊤ : Subgroup Γ).lowerCentralSeries t ≤ E ∧
      ∃ F : Finset Γ, F.card ≤ (sched hGR κ t).2.1 ∧ (F : Set Γ) ⊆ P (sched hGR κ t).2.2 ∧
        Subgroup.closure ((F : Set Γ) ∪ E) = ⊤
  | 0, _ => by
    refine ⟨⊤, inferInstance, le_top, ?_, le_top, ∅, by simp [sched], by simp, by simp⟩
    intro x _
    refine ⟨1, hP.one_mem, x, ?_, one_mul x⟩
    simp [hL.hDtop]
  | t + 1, ht => by
    obtain ⟨E, hEn, hDE, hEb, hlcs, F, hFr, hFa, hgen⟩ := downward hGR hκ hP hL t (by omega)
    obtain ⟨i, hi⟩ : ∃ i, i = k - t := ⟨_, rfl⟩
    have hi1 : 1 ≤ i := by omega
    have hik : i ≤ k := by omega
    have e1 : k + 1 - t = i + 1 := by omega
    have e2 : k + 1 - (t + 1) = i := by omega
    rw [e1] at hDE hEb
    rw [e2]
    haveI := hL.hDn i hi1 (by omega)
    haveI := hEn
    obtain ⟨E', hE'n, hDE', hcomm, hE'b, F', hF'r, hF'a, hgen'⟩ :=
      downward_step hP (hL.hmono i hi1 hik) (hL.hz6 i hi1 hik) (hL.hzD i hi1 hik)
        (hL.hcent i hi1 hik) (hL.hstep i hi1 hik) hDE hEb F hFr hFa hgen
        (grAt_grDC hGR (Nat.one_le_pow _ _ hκ))
    refine ⟨E', hE'n, hDE', hE'b, ?_, F', hF'r, hF'a, hgen'⟩
    change ⁅(⊤ : Subgroup Γ).lowerCentralSeries t, ⊤⁆ ≤ E'
    refine le_trans ?_ hcomm
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mono le_rfl hlcs

/-- The end of the downward induction: `γ_k(Γ) ⊆ P(b_k + 2)`. -/
theorem lcs_subset_of_layers (hGR : GreenRuzsaRank) [Finite Γ] [Group.IsNilpotent Γ] {κ : ℕ}
    (hκ : 1 ≤ κ) {P : ℕ → Set Γ} (hP : Filt κ P) {k : ℕ} {D : ℕ → Subgroup Γ} {z : ℕ → Γ}
    (hL : LayersIn P k D z) :
    (((⊤ : Subgroup Γ).lowerCentralSeries k : Subgroup Γ) : Set Γ) ⊆ P ((sched hGR κ k).1 + 2) := by
  obtain ⟨E, -, -, hEb, hlcs, -⟩ := downward hGR hκ hP hL k le_rfl
  rw [show k + 1 - k = 1 by omega] at hEb
  intro x hx
  obtain ⟨p, hp, d, hd, rfl⟩ := hEb (hlcs hx)
  exact hP.mul_mem hp (hL.hD1 hd)

end Tointon
