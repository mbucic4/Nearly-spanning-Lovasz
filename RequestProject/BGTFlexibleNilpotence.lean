module
public import RequestProject.BGTFlexible
public import RequestProject.BGTFiniteNilpotence

/-!
# Flexible trapping: product and commutator estimates, and finitary nilpotence

For flexible trapping data `HasFlexibleTrapping κ p m N B S` (see `BGTFlexible.lean`):

* `Lovasz.BGT.escNorm_list_prod_le_flex`: `‖g₁ ⋯ gₙ‖ ≤ 4 p κ m (‖g₁‖ + ⋯ + ‖gₙ‖)`;
* `Lovasz.BGT.escNorm_commutator_le_flex`: `‖g⁻¹ h⁻¹ g h‖ ≤ Ccomm ‖g‖ ‖h‖` for `g, h ∈ B¹⁰`,
  with `Ccomm = 4 p² κ (4 p κ m)²`;
* `Lovasz.BGT.exists_lcs_le_zeroEsc_flex` and `Lovasz.BGT.finite_nilpotent_mod_zeroEsc_flex`:
  the finitary nilpotence theorem modulo the zero-escape subgroup, with constants depending only on
  `κ, p, m` (the nilpotency class may depend on the individual finite set `B`).
-/

@[expose] public section

open scoped Pointwise commutatorElement
open Finset Function

namespace Lovasz.BGT

variable {G : Type*} [Group G]

/-- The product constant `Cprod = 4 p κ m`. -/
def flexCprod (κ p m : ℕ) : ℝ := 4 * p * κ * m

/-- The commutator constant `Ccomm = 4 p² κ Cprod²`. -/
def flexCcomm (κ p m : ℕ) : ℝ := 4 * p ^ 2 * κ * flexCprod κ p m ^ 2

lemma one_le_flexCprod {κ p m : ℕ} (hκ : 2 ≤ κ) (hp : 1 ≤ p) (hm : 1 ≤ m) :
    1 ≤ flexCprod κ p m := by
  have hκ' : (2 : ℝ) ≤ κ := by exact_mod_cast hκ
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  unfold flexCprod
  have : (1 : ℝ) ≤ p * κ := by nlinarith
  have : (1 : ℝ) ≤ p * κ * m := by nlinarith
  nlinarith

lemma one_le_flexCcomm {κ p m : ℕ} (hκ : 2 ≤ κ) (hp : 1 ≤ p) (hm : 1 ≤ m) :
    1 ≤ flexCcomm κ p m := by
  have hκ' : (2 : ℝ) ≤ κ := by exact_mod_cast hκ
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hC := one_le_flexCprod hκ hp hm
  unfold flexCcomm
  have h1 : (1 : ℝ) ≤ p ^ 2 := one_le_pow₀ hp'
  have h2 : (1 : ℝ) ≤ flexCprod κ p m ^ 2 := one_le_pow₀ hC
  have : (1 : ℝ) ≤ p ^ 2 * κ := by nlinarith
  have : (1 : ℝ) ≤ p ^ 2 * κ * flexCprod κ p m ^ 2 := by nlinarith
  nlinarith

/-- **Theorem 8.1 (ii)** for flexible trapping data (product property of the escape norm):
`‖g₁ ⋯ gₙ‖ ≤ 4 p κ m (‖g₁‖ + ⋯ + ‖gₙ‖)`. -/
theorem escNorm_list_prod_le_flex {κ p m N : ℕ} {B S : Set G}
    (hB : HasFlexibleTrapping κ p m N B S) (l : List G) :
    escNorm B l.prod ≤ flexCprod κ p m * (l.map (escNorm B)).sum := by
  classical
  obtain ⟨hApp, hκ, hp, hm, hN, hSinv, hQN, htrap1, htrap2⟩ := hB
  obtain ⟨A', rfl⟩ := hApp.1.exists_finset_coe
  have hAA : (#(A' * A') : ℝ) ≤ κ * #A' := by
    have := card_pow_succ_le_of_approx hApp 1
    rwa [pow_one, one_add_one_eq_two, sq] at this
  obtain ⟨-, hA1, hAinv, -⟩ := hApp
  have hA1' : (1 : G) ∈ A' := hA1
  have hAinv' : A'⁻¹ = A' := by rw [← coe_inj, coe_inv]; exact hAinv
  have hnn : ∀ y ∈ l.map (escNorm (A' : Set G)), 0 ≤ y := by
    simp only [List.mem_map]; rintro _ ⟨a, -, rfl⟩; exact escNorm_nonneg hA1
  have hsum0 : 0 ≤ (l.map (escNorm (A' : Set G))).sum := List.sum_nonneg hnn
  have hK2 : (2 : ℝ) ≤ κ := by exact_mod_cast hκ
  have hN' : 3 * (p : ℝ) * κ ≤ N := by exact_mod_cast hN
  set C0 : ℝ := flexCprod κ p m with hC0def
  have hC0nn : 0 ≤ C0 := by rw [hC0def, flexCprod]; positivity
  have hcore : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → escNorm (A' : Set G) l.prod ≤
      C0 * ((l.map (escNorm (A' : Set G))).sum + ε * l.length) := by
    intro ε hε0 hε1
    have h1 := escNorm_le_wdist_core_flex hA1' hAinv' hK2 hAA hSinv hp hN' hm hQN htrap1 htrap2
      hε0 hε1 l.prod
    have hw0 : ∀ g, 0 ≤ escNorm (A' : Set G) g + ε := fun g => by
      linarith [escNorm_nonneg (g := g) hA1]
    have h2 := wdist_le_list hw0 l rfl
    have h3 : (l.map (fun g => escNorm (A' : Set G) g + ε)).sum =
        (l.map (escNorm (A' : Set G))).sum + ε * l.length := by
      simp [List.sum_map_add, mul_comm]
    rw [h3] at h2
    have e : (p : ℝ) * (4 * ((κ : ℝ) * m)) = C0 := by rw [hC0def, flexCprod]; ring
    rw [e] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hC0nn)
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set ε := min 1 (δ / (C0 * (l.length + 1) + 1)) with hε
  have hε0 : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεδ : ε * (C0 * (l.length + 1) + 1) ≤ δ := by
    have := min_le_right 1 (δ / (C0 * (l.length + 1) + 1))
    rw [← hε, le_div_iff₀ (by positivity)] at this
    exact this
  have := hcore ε hε0 hε1
  have hlen : C0 * (ε * l.length) ≤ δ := by
    have : C0 * (ε * l.length) ≤ ε * (C0 * (l.length + 1) + 1) := by
      nlinarith [hε0.le, hC0nn]
    linarith
  nlinarith

/-- **Theorem 8.1 (iii)** for flexible trapping data (commutator property of the escape norm):
for `g, h ∈ B¹⁰`, `‖g⁻¹ h⁻¹ g h‖ ≤ 4 p² κ (4 p κ m)² ‖g‖ ‖h‖`. -/
theorem escNorm_commutator_le_flex {κ p m N : ℕ} {B S : Set G}
    (hB : HasFlexibleTrapping κ p m N B S) {g h : G} (hg : g ∈ B ^ 10) (hh : h ∈ B ^ 10) :
    escNorm B (g⁻¹ * h⁻¹ * g * h) ≤ flexCcomm κ p m * escNorm B g * escNorm B h := by
  classical
  have hprod := escNorm_list_prod_le_flex hB
  obtain ⟨hApp, hκ, hp, hm, hN, hSinv, hQN, htrap1, htrap2⟩ := hB
  have hconj := fun {x y : G} (hy : y ∈ B ^ 49) =>
    escNorm_conj_le_flex (g := x) hApp.2.1 hApp.2.2.1 hp htrap1 hy
  obtain ⟨A', rfl⟩ := hApp.1.exists_finset_coe
  have hAA : (#(A' * A') : ℝ) ≤ κ * #A' := by
    have := card_pow_succ_le_of_approx hApp 1
    rwa [pow_one, one_add_one_eq_two, sq] at this
  obtain ⟨-, hA1, hAinv, -⟩ := hApp
  have hA1' : (1 : G) ∈ A' := hA1
  have hAinv' : A'⁻¹ = A' := by rw [← coe_inj, coe_inv]; exact hAinv
  have hAne : A'.Nonempty := ⟨1, hA1'⟩
  set C : ℝ := flexCprod κ p m with hC
  have hC1 : 1 ≤ C := one_le_flexCprod hκ hp hm
  have hC0 : 0 < C := by linarith
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  set w : G → ℝ := escNorm (A' : Set G) with hw
  have hw0 : ∀ u, 0 ≤ w u := fun u => escNorm_nonneg hA1
  have hwinv : ∀ u, w u⁻¹ = w u := fun u => escNorm_inv hAinv
  have hdlow : ∀ z, w z / C ≤ wdist w z := fun z => le_wdist fun l hl => by
    rw [div_le_iff₀ hC0, mul_comm]
    have := hprod l
    rw [hl] at this
    exact this
  have hD : 1 / C ≤ wD w A' := le_wD (by rw [div_le_one hC0]; exact hC1) fun z hz => by
    have := hdlow z
    rwa [show w z = 1 from escNorm_eq_one_of_notMem hA1 hz] at this
  have hD0 : 0 < wD w A' := lt_of_lt_of_le (by positivity) hD
  have hLip : ∀ u y, |dif u (phi w A' hAne) y| ≤ C * w u := by
    intro u y
    refine (abs_dif_phi_le hAne hw0 hwinv hD0 u y).trans ?_
    rw [div_le_iff₀ hD0]
    have h1 : 1 ≤ C * wD w A' := by rw [div_le_iff₀ hC0] at hD; linarith
    have h2 := wdist_le hw0 u
    have h3 := wdist_nonneg hw0 u
    nlinarith [hw0 u]
  have hconjL : ∀ v : G, ∀ y ∈ (A' : Set G) ^ 12, ∀ z,
      |dif (y⁻¹ * v * y) (phi w A' hAne) z| ≤ C * (p * w v) := by
    intro v y hy z
    refine (hLip _ z).trans ?_
    gcongr
    exact hconj (Set.pow_subset_pow_right hA1 (by norm_num) hy)
  set Φ := bigPhi A' hAne w with hΦ
  have hdd1 : ∀ x, |dif h (dif g Φ) x| ≤ 2 * κ * (C * w g) * (C * (p * w h)) :=
    fun x => abs_dif_dif_bigPhi_le hAne hw0 hD0 hA1' hAA hg (hLip g) (hconjL h) x
  have hdd2 : ∀ x, |dif g (dif h Φ) x| ≤ 2 * κ * (C * w h) * (C * (p * w g)) :=
    fun x => abs_dif_dif_bigPhi_le hAne hw0 hD0 hA1' hAA hh (hLip h) (hconjL g) x
  have hc : ∀ z, |dif (g⁻¹ * h⁻¹ * g * h) Φ z| ≤ 4 * p * κ * C ^ 2 * (w g * w h) := by
    intro z
    have e := dif_comm g h Φ (h * g * z)
    rw [show g⁻¹ * h⁻¹ * (h * g * z) = z by group] at e
    rw [← e]
    calc |dif g (dif h Φ) (h * g * z) - dif h (dif g Φ) (h * g * z)|
        ≤ |dif g (dif h Φ) (h * g * z)| + |dif h (dif g Φ) (h * g * z)| := abs_sub _ _
      _ ≤ 2 * κ * (C * w h) * (C * (p * w g)) + 2 * κ * (C * w g) * (C * (p * w h)) :=
          add_le_add (hdd2 _) (hdd1 _)
      _ = 4 * p * κ * C ^ 2 * (w g * w h) := by ring
  have hΦ1 : 1 ≤ Φ 1 := one_le_bigPhi hAne hw0 hD0 hAinv' hA1'
  have hΦpos : ∀ x, 0 < Φ x → x ∈ (A' : Set G) ^ 100 := fun x hx =>
    Set.pow_subset_pow_right hA1 (by norm_num) (bigPhi_pos_mem hAne hw0 hD0 hx)
  have hnn : 0 ≤ 4 * p * κ * C ^ 2 * (w g * w h) := by
    have := hw0 g; have := hw0 h; positivity
  have h1 := escNorm_le_of_abs_dif_le_flex hp hAinv htrap1 hΦ1 hΦpos hnn hc
  calc escNorm (A' : Set G) (g⁻¹ * h⁻¹ * g * h) ≤ p * (4 * p * κ * C ^ 2 * (w g * w h)) := h1
    _ = flexCcomm κ p m * w g * w h := by rw [flexCcomm, ← hC]; ring

/-- For flexible trapping data, the elements of escape norm zero form a subgroup `H ⊆ B`,
normalised by `B¹⁰`. -/
theorem exists_subgroup_escNorm_eq_zero_flex {κ p m N : ℕ} {B S : Set G}
    (hB : HasFlexibleTrapping κ p m N B S) :
    ∃ H : Subgroup G, (H : Set G) = {g | escNorm B g = 0} ∧ (H : Set G) ⊆ B ∧
      ∀ a ∈ B ^ 10, ∀ g ∈ H, a⁻¹ * g * a ∈ H := by
  have hB1 : (1 : G) ∈ B := hB.1.2.1
  have hBinv : B⁻¹ = B := hB.1.2.2.1
  let H : Subgroup G :=
    { carrier := {g | escNorm B g = 0}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        have := escNorm_list_prod_le_flex hB [a, b]
        simp only [List.prod_cons, List.prod_nil, mul_one, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, ha, hb, add_zero, mul_zero] at this
        exact le_antisymm this (escNorm_nonneg hB1)
      one_mem' := escNorm_one hB1
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [escNorm_inv hBinv, ha] }
  refine ⟨H, rfl, fun g hg => mem_of_escNorm_lt_one hB1 (by
    change escNorm B g = 0 at hg; rw [hg]; norm_num), fun a ha g hg => ?_⟩
  change escNorm B g = 0 at hg
  change escNorm B (a⁻¹ * g * a) = 0
  have := escNorm_conj_le_flex (g := g) hB1 hBinv hB.2.2.1 hB.2.2.2.2.2.2.2.1
    (Set.pow_subset_pow_right hB1 (by norm_num) ha)
  rw [hg, mul_zero] at this
  exact le_antisymm this (escNorm_nonneg hB1)

/-- **Finitary nilpotence modulo the zero-escape subgroup, flexible version.**  If
`0 ≤ δ < 1` and `Ccomm δ ≤ 1/2`, the subgroup `Γ` generated by the elements of escape norm at
most `δ` contains the zero-escape subgroup `H` as a normal subgroup, and `Γ/H` is nilpotent (of
some class `j` which may depend on `B`). -/
theorem exists_lcs_le_zeroEsc_flex {κ p m N : ℕ} {B S : Set G}
    (hB : HasFlexibleTrapping κ p m N B S) {δ : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ < 1) (hCδ : flexCcomm κ p m * δ ≤ 1 / 2) :
    ∃ (H : Subgroup G) (j : ℕ), (H : Set G) = {g | escNorm B g = 0} ∧ (H : Set G) ⊆ B ∧
      H ≤ Subgroup.closure {g | escNorm B g ≤ δ} ∧
      (H.subgroupOf (Subgroup.closure {g | escNorm B g ≤ δ})).Normal ∧
      (⊤ : Subgroup (Subgroup.closure {g | escNorm B g ≤ δ})).lowerCentralSeries j ≤
        H.subgroupOf (Subgroup.closure {g | escNorm B g ≤ δ}) := by
  have hB1 : (1 : G) ∈ B := hB.1.2.1
  have hBinv : B⁻¹ = B := hB.1.2.2.1
  have hBf : B.Finite := hB.1.1
  have hB10 : B ⊆ B ^ 10 := by
    simpa using Set.pow_subset_pow_right hB1 (show 1 ≤ 10 by norm_num)
  obtain ⟨H, hHset, hHB, hHconj⟩ := exists_subgroup_escNorm_eq_zero_flex hB
  set X : Set G := {g | escNorm B g ≤ δ} with hX
  set Γ := Subgroup.closure X
  have hmemH : ∀ g, g ∈ H ↔ escNorm B g = 0 := fun g => by
    rw [← SetLike.mem_coe, hHset]; rfl
  have hXB : ∀ g ∈ X, g ∈ B := fun g hg => mem_of_escNorm_lt_one hB1 (lt_of_le_of_lt hg hδ1)
  have hHΓ : H ≤ Γ := fun g hg => Subgroup.subset_closure (by
    show escNorm B g ≤ δ; rw [(hmemH g).1 hg]; exact hδ)
  have hnorm : Γ ≤ Subgroup.normalizer (H : Set _) := by
    rw [Subgroup.closure_le]
    intro g hg
    rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
    intro h
    have hgB := hXB g hg
    have hginv : g⁻¹ ∈ B := by rw [← hBinv]; simpa using hgB
    constructor
    · intro hh
      simpa using hHconj g⁻¹ (hB10 hginv) h hh
    · intro hh
      simpa [mul_assoc] using hHconj g (hB10 hgB) _ hh
  set C : ℝ := flexCcomm κ p m
  set T : Set Γ := {x : Γ | escNorm B x ≤ δ} with hT
  have hbound : ∀ k, ∀ y ∈ leftComm T k, escNorm B (y : G) ≤ δ * (1 / 2) ^ k := by
    intro k
    induction k with
    | zero =>
      intro y hy
      change escNorm B (y : G) ≤ δ at hy
      simpa using hy
    | succ k ih =>
      rintro _ ⟨x, hx, t, ht, rfl⟩
      have hxb := ih x hx
      have ht' : escNorm B (t : G) ≤ δ := ht
      have hpow : δ * (1 / 2 : ℝ) ^ k ≤ δ := by
        apply mul_le_of_le_one_right hδ; apply pow_le_one₀ <;> norm_num
      have hxB : (x : G)⁻¹ ∈ B ^ 10 := by
        apply hB10; rw [← hBinv]; simpa using hXB _ (hxb.trans hpow)
      have htB : (t : G)⁻¹ ∈ B ^ 10 := by
        apply hB10; rw [← hBinv]; simpa using hXB _ ht'
      have hc := escNorm_commutator_le_flex hB hxB htB
      simp only [inv_inv, escNorm_inv hBinv] at hc
      have e : ((⁅x, t⁆ : Γ) : G) = (x : G) * t * (x : G)⁻¹ * (t : G)⁻¹ := by
        simp [commutatorElement_def]
      rw [e]
      refine hc.trans ?_
      have hn1 := escNorm_nonneg (g := (x : G)) hB1
      have hn2 := escNorm_nonneg (g := (t : G)) hB1
      have hC0 : 0 ≤ C := le_trans zero_le_one (one_le_flexCcomm hB.2.1 hB.2.2.1 hB.2.2.2.1)
      calc C * escNorm B (x : G) * escNorm B (t : G) ≤ C * (δ * (1 / 2) ^ k) * δ := by
            gcongr
        _ = (C * δ) * (δ * (1 / 2) ^ k) := by ring
        _ ≤ (1 / 2) * (δ * (1 / 2) ^ k) := by
            apply mul_le_mul_of_nonneg_right hCδ; positivity
        _ = δ * (1 / 2) ^ (k + 1) := by ring
  obtain ⟨μ, hμ, hgap⟩ := exists_escNorm_gap hBf hB1
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (show 0 < μ / 2 by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  have hHn : (H.subgroupOf Γ).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHΓ).2 hnorm
  refine ⟨H, j, hHset, hHB, hHΓ, hHn, ?_⟩
  refine lcs_le_of_leftComm_subset T Subgroup.closure_closure_coe_preimage _ j ?_
  intro y hy
  have hyb := hbound j y hy
  have hsmall : escNorm B (y : G) < μ := by
    calc escNorm B (y : G) ≤ δ * (1 / 2) ^ j := hyb
      _ ≤ 1 * (1 / 2) ^ j := by gcongr
      _ < μ := by linarith
  have hyB : (y : G) ∈ B := mem_of_escNorm_lt_one hB1 (hyb.trans_lt (by
    calc δ * (1 / 2 : ℝ) ^ j ≤ δ :=
          mul_le_of_le_one_right hδ (pow_le_one₀ (by norm_num) (by norm_num))
      _ < 1 := hδ1))
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, hmemH]
  rcases hgap _ hyB with h | h
  · exact h
  · linarith

/-- A uniformly large approximate group of uniformly small escape norm, from the
Sanders–Croot–Sisask theorem and the first trapping condition with time `p`:
`‖s‖ ≤ p/(L+1)` for `s ∈ S`. -/
theorem exists_large_small_escNorm_flex (κ p : ℕ) (hκ : 1 ≤ κ) (L : ℕ) :
    ∃ K' c : ℝ, 0 < c ∧ ∀ {G : Type*} [Group G] (B : Set G), IsBGTApproxGroup (κ : ℝ) B →
      1 ≤ p → (∀ g : G, (∀ i : ℕ, 1 ≤ i → i ≤ p → g ^ i ∈ B ^ 100) → g ∈ B) →
      ∃ S : Set G, IsBGTApproxGroup K' S ∧ c * B.ncard ≤ S.ncard ∧ S ⊆ B ^ 4 ∧
        ∀ s ∈ S, escNorm B s ≤ p / (L + 1) := by
  obtain ⟨K', c, hc, hS⟩ := sanders_small_neighbourhoods (κ : ℝ) (by exact_mod_cast hκ) (L + 1)
  refine ⟨K', c, hc, fun {G} _ B hB hp htrap => ?_⟩
  obtain ⟨S, hSapp, hcard, hpow⟩ := hS B hB
  have hS1 : (1 : G) ∈ S := hSapp.2.1
  have hB1 : (1 : G) ∈ B := hB.2.1
  have hpowS : ∀ s ∈ S, ∀ i ≤ L + 1, s ^ i ∈ B ^ 4 := fun s hs i hi =>
    hpow (Set.pow_subset_pow_right hS1 hi (Set.pow_mem_pow hs))
  refine ⟨S, hSapp, hcard, fun s hs => by simpa using hpowS s hs 1 (by omega), fun s hs => ?_⟩
  have h4 : B ^ 4 ⊆ B ^ 100 := Set.pow_subset_pow_right hB1 (by norm_num)
  exact escNorm_le_of_trapping hp htrap (n := L) (fun i hi => h4 (hpowS s hs i (by omega)))

/-- **Finitary nilpotence for flexible trapping data.**  For all `κ, p, m` there are `K'` and
`c > 0` such that for every `N` and all flexible trapping data `(B, S)` with parameters
`κ, p, m, N`, there are a `K'`-approximate group `S' ⊆ B⁴` with `|S'| ≥ c |B|` and a subgroup
`Γ ⊇ S'` such that the zero-escape subgroup `H ⊆ B` is normal in `Γ` with `Γ/H` nilpotent.

The constants depend only on `κ, p, m`; the nilpotency class `j` may depend on `B`. -/
theorem finite_nilpotent_mod_zeroEsc_flex (κ p m : ℕ) :
    ∃ K' c : ℝ, 0 < c ∧ ∀ {G : Type*} [Group G] (N : ℕ) (B S : Set G),
      HasFlexibleTrapping κ p m N B S →
      ∃ (S' : Set G) (H Γ : Subgroup G) (j : ℕ), IsBGTApproxGroup K' S' ∧
        c * B.ncard ≤ S'.ncard ∧ S' ⊆ B ^ 4 ∧ S' ⊆ Γ ∧
        (H : Set G) = {g | escNorm B g = 0} ∧ (H : Set G) ⊆ B ∧ H ≤ Γ ∧
         (H.subgroupOf Γ).Normal ∧ (⊤ : Subgroup Γ).lowerCentralSeries j ≤
           H.subgroupOf Γ := by
  set C : ℝ := flexCcomm κ p m with hCdef
  set L : ℕ := ⌈2 * p * C⌉₊ + p with hL
  obtain ⟨K', c, hc, hS⟩ := exists_large_small_escNorm_flex (max κ 1) p (le_max_right _ _) L
  refine ⟨K', c, hc, fun {G} _ N B S hB => ?_⟩
  have hκ1 : (max κ 1 : ℕ) = κ := max_eq_left (by have := hB.2.1; omega)
  rw [hκ1] at hS
  obtain ⟨S', hSapp, hcard, hS4, hSsmall⟩ := hS B hB.1 hB.2.2.1 hB.2.2.2.2.2.2.2.1
  have hC1 : 1 ≤ C := one_le_flexCcomm hB.2.1 hB.2.2.1 hB.2.2.2.1
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hB.2.2.1
  have hLC : 2 * p * C + p ≤ (L : ℝ) := by
    rw [hL]; push_cast; linarith [Nat.le_ceil (2 * p * C)]
  have hLpos : (0 : ℝ) < L + 1 := by positivity
  have hδ1 : (p : ℝ) / (L + 1) < 1 := by
    rw [div_lt_one hLpos]
    have : 0 ≤ 2 * p * C := by positivity
    linarith
  have hCδ : C * (p / (L + 1)) ≤ 1 / 2 := by
    rw [mul_div_assoc', div_le_iff₀ hLpos]
    nlinarith
  obtain ⟨H, j, hHset, hHB, hHΓ, hHn, hlcs⟩ :=
    exists_lcs_le_zeroEsc_flex hB (δ := p / (L + 1)) (by positivity) hδ1 hCδ
  exact ⟨S', H, _, j, hSapp, hcard, hS4, fun s hs => Subgroup.subset_closure (hSsmall s hs),
    hHset, hHB, hHΓ, hHn, hlcs⟩

end Lovasz.BGT
