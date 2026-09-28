module
public import Mathlib
public import RequestProject.BGTSanders

/-!
# The normal Sanders tower

For a finite `K`-approximate group `A` (in the sense of Breuillard–Green–Tao) we construct
approximate groups `R j` with

* `R 0 ^ 4 ⊆ A ^ 4` (Sanders' small neighbourhoods theorem at exponent `4`);
* `x⁻¹ R (j+1)^12 x ⊆ R j ^ 4` for `x ∈ A⁴` (the small normal neighbourhoods theorem applied with
  `S = R j` and `m = 12`);
* `|R j| ≥ c_j |A|` with `c_j > 0` depending only on `K` and `j`.

Setting `B j = R j ^ 4` gives the exponent adapter of the note: `B (j+1)³ ⊆ B j`,
`a⁻¹ B (j+1) a ⊆ B j` for `a ∈ A`, and `B j ⊆ A⁴`.  Ruzsa covering then gives
`A^r ⊆ F · B j` with `F ⊆ A^r` and `|F| ≤ M r j`, where `M` depends only on `K`
(`finite_tower`).  All numerical bounds are chosen recursively before the sets.
-/

@[expose] public section

open scoped Pointwise

namespace Lovasz.Tower

open BGT

lemma isBGTApproxGroup_mono {G : Type*} [Group G] {K K' : ℝ} {S : Set G}
    (hS : IsBGTApproxGroup K S) (hK : K ≤ K') : IsBGTApproxGroup K' S := by
  obtain ⟨hf, h1, hinv, X, hXinv, hX3, hXK, hcov⟩ := hS
  exact ⟨hf, h1, hinv, X, hXinv, hX3, hXK.trans hK, hcov⟩

/-- The tower constants `(K_j, c_j)`, `c_j > 0`, chosen recursively from `K` alone. -/
noncomputable def consts (K : ℝ) (hK : 1 ≤ K) : ℕ → {p : ℝ × ℝ // 0 < p.2}
  | 0 =>
    ⟨((sanders_small_neighbourhoods.{0} K hK 4).choose,
      (sanders_small_neighbourhoods.{0} K hK 4).choose_spec.choose),
      (sanders_small_neighbourhoods.{0} K hK 4).choose_spec.choose_spec.1⟩
  | j + 1 =>
    ⟨((sanders_small_normal_neighbourhoods.{0} K (max (consts K hK j).1.1 1) (consts K hK j).1.2
        hK (le_max_right _ _) (consts K hK j).2 12).choose,
      (sanders_small_normal_neighbourhoods.{0} K (max (consts K hK j).1.1 1) (consts K hK j).1.2
        hK (le_max_right _ _) (consts K hK j).2 12).choose_spec.choose),
      (sanders_small_normal_neighbourhoods.{0} K (max (consts K hK j).1.1 1) (consts K hK j).1.2
        hK (le_max_right _ _) (consts K hK j).2 12).choose_spec.choose_spec.1⟩

variable {K : ℝ} (hK : 1 ≤ K)

lemma consts_zero_spec {G : Type} [Group G] (A : Set G) (hA : IsBGTApproxGroup K A) :
    ∃ S : Set G, IsBGTApproxGroup (consts K hK 0).1.1 S ∧
      (consts K hK 0).1.2 * A.ncard ≤ S.ncard ∧ S ^ 4 ⊆ A ^ 4 :=
  (sanders_small_neighbourhoods.{0} K hK 4).choose_spec.choose_spec.2 A hA

lemma consts_succ_spec (j : ℕ) {G : Type} [Group G] (A S : Set G) (hA : IsBGTApproxGroup K A)
    (hS : IsBGTApproxGroup (max (consts K hK j).1.1 1) S) (hSA : S ⊆ A ^ 4)
    (hSc : (consts K hK j).1.2 * A.ncard ≤ S.ncard) :
    ∃ T : Set G, IsBGTApproxGroup (consts K hK (j + 1)).1.1 T ∧
      (consts K hK (j + 1)).1.2 * A.ncard ≤ T.ncard ∧
      ∀ x ∈ A ^ 4, ∀ y ∈ T ^ 12, x⁻¹ * y * x ∈ S ^ 4 :=
  (sanders_small_normal_neighbourhoods.{0} K (max (consts K hK j).1.1 1) (consts K hK j).1.2
    hK (le_max_right _ _) (consts K hK j).2 12).choose_spec.choose_spec.2 A S hA hS hSA hSc

variable {G : Type} [Group G]

/-- The invariant carried along the recursion. -/
def TowerInv (A : Set G) (j : ℕ) (S : Set G) : Prop :=
  IsBGTApproxGroup (max (consts K hK j).1.1 1) S ∧ S ⊆ A ^ 4 ∧
    (consts K hK j).1.2 * A.ncard ≤ S.ncard ∧ S ^ 4 ⊆ A ^ 4

lemma subset_pow_of_one_mem {S : Set G} (h1 : (1 : G) ∈ S) {m : ℕ} (hm : 1 ≤ m) : S ⊆ S ^ m := by
  simpa using Set.pow_subset_pow_right h1 hm

/-- The approximate groups `R j` of the tower. -/
noncomputable def towerR (A : Set G) (hA : IsBGTApproxGroup K A) :
    (j : ℕ) → {S : Set G // TowerInv hK A j S}
  | 0 =>
    let h := consts_zero_spec hK A hA
    ⟨h.choose, isBGTApproxGroup_mono h.choose_spec.1 (le_max_left _ _),
      (subset_pow_of_one_mem h.choose_spec.1.2.1 (by norm_num : 1 ≤ 4)).trans h.choose_spec.2.2,
      h.choose_spec.2.1, h.choose_spec.2.2⟩
  | j + 1 =>
    let S := towerR A hA j
    let h := consts_succ_spec hK j A S.1 hA S.2.1 S.2.2.1 S.2.2.2.1
    have h12 : h.choose ^ 12 ⊆ S.1 ^ 4 := fun y hy => by
      simpa using h.choose_spec.2.2 1 (Set.one_mem_pow hA.2.1) y hy
    have h1 : (1 : G) ∈ h.choose := h.choose_spec.1.2.1
    ⟨h.choose, isBGTApproxGroup_mono h.choose_spec.1 (le_max_left _ _),
      ((subset_pow_of_one_mem h1 (by norm_num : 1 ≤ 12)).trans h12).trans S.2.2.2.2,
      h.choose_spec.2.1,
      ((Set.pow_subset_pow_right h1 (by norm_num : 4 ≤ 12)).trans h12).trans S.2.2.2.2⟩

lemma towerR_succ_conj (A : Set G) (hA : IsBGTApproxGroup K A) (j : ℕ) :
    ∀ x ∈ A ^ 4, ∀ y ∈ (towerR hK A hA (j + 1)).1 ^ 12, x⁻¹ * y * x ∈ (towerR hK A hA j).1 ^ 4 :=
  (consts_succ_spec hK j A (towerR hK A hA j).1 hA (towerR hK A hA j).2.1
    (towerR hK A hA j).2.2.1 (towerR hK A hA j).2.2.2.1).choose_spec.2.2

include hK in
/-- **The finite normal Sanders tower.**  There is a function `M` (depending only on `K`) such
that every finite `K`-approximate group `A` admits sets `B j` with `1 ∈ B j`, `B j` symmetric,
`B (j+1) * B (j+1) ⊆ B j`, `a⁻¹ B (j+1) a ⊆ B j` for `a ∈ A`, `B j ⊆ A⁴`, and for all `r, j` a
finite set `F ⊆ A^r` with `|F| ≤ M r j` and `A^r ⊆ F · B j`. -/
theorem finite_tower : ∃ M : ℕ → ℕ → ℕ, ∀ {G : Type} [Group G] [Finite G] (A : Set G),
    IsBGTApproxGroup K A → ∃ B : ℕ → Set G, (∀ j, (1 : G) ∈ B j) ∧ (∀ j, (B j)⁻¹ = B j) ∧
      (∀ j, B (j + 1) * B (j + 1) ⊆ B j) ∧ (∀ j, ∀ a ∈ A, ∀ b ∈ B (j + 1), a⁻¹ * b * a ∈ B j) ∧
      (∀ j, B j ⊆ A ^ 4) ∧
      ∀ r j, ∃ F : Finset G, (F : Set G) ⊆ A ^ r ∧ A ^ r ⊆ (F : Set G) * B j ∧ F.card ≤ M r j := by
  refine ⟨fun r j => ⌊K ^ (r + 3) / (consts K hK (j + 1)).1.2⌋₊, ?_⟩
  intro G _ _ A hA
  classical
  set R : ℕ → Set G := fun j => (towerR hK A hA j).1 with hRdef
  have hRinv : ∀ j, TowerInv hK A j (R j) := fun j => (towerR hK A hA j).2
  have hR1 : ∀ j, (1 : G) ∈ R j := fun j => (hRinv j).1.2.1
  have hRsym : ∀ j, (R j)⁻¹ = R j := fun j => (hRinv j).1.2.2.1
  have hR12 : ∀ j, R (j + 1) ^ 12 ⊆ R j ^ 4 := fun j y hy => by
    simpa using towerR_succ_conj hK A hA j 1 (Set.one_mem_pow hA.2.1) y hy
  have h4_12 : ∀ j, R (j + 1) ^ 4 ⊆ R (j + 1) ^ 12 := fun j =>
    Set.pow_subset_pow_right (hR1 _) (by norm_num)
  set B : ℕ → Set G := fun j => R j ^ 4 with hBdef
  have hBsucc : ∀ j, B (j + 1) * B (j + 1) ⊆ B j := by
    intro j
    have : B (j + 1) * B (j + 1) ⊆ R (j + 1) ^ 12 := by
      simp only [hBdef]
      rw [← pow_add]
      exact Set.pow_subset_pow_right (hR1 _) (by norm_num)
    exact this.trans (hR12 j)
  have hBA : ∀ j, B j ⊆ A ^ 4 := fun j => (hRinv j).2.2.2
  refine ⟨B, fun j => Set.one_mem_pow (hR1 j), fun j => by simp only [hBdef]; rw [← inv_pow, hRsym],
    hBsucc, ?_, hBA, ?_⟩
  · intro j a ha b hb
    have ha4 : a ∈ A ^ 4 := subset_pow_of_one_mem hA.2.1 (by norm_num) ha
    have := towerR_succ_conj hK A hA j a ha4 b (h4_12 j hb)
    simpa using this
  · intro r j
    haveI := Fintype.ofFinite G
    set Rf : Finset G := (R (j + 1)).toFinset with hRf
    set Af : Finset G := A.toFinset with hAf
    have hAfA : (Af : Set G) = A := Set.coe_toFinset A
    have hRfR : (Rf : Set G) = R (j + 1) := Set.coe_toFinset _
    have hRne : Rf.Nonempty := ⟨1, by simpa [hRf] using hR1 (j + 1)⟩
    set c := (consts K hK (j + 1)).1.2 with hc
    have hcpos : 0 < c := (consts K hK (j + 1)).2
    have hsize : c * Af.card ≤ Rf.card := by
      have := (hRinv (j + 1)).2.2.1
      rw [Set.ncard_eq_toFinset_card' A, Set.ncard_eq_toFinset_card' (R (j + 1))] at this
      exact this
    have hmul : Af ^ r * Rf ⊆ Af ^ (r + 4) := by
      rw [← Finset.coe_subset, Finset.coe_mul, Finset.coe_pow, Finset.coe_pow, hAfA, hRfR,
        pow_add]
      exact Set.mul_subset_mul_left ((subset_pow_of_one_mem (hR1 _) (by norm_num)).trans
        (hRinv (j + 1)).2.2.2)
    have hApow : ((Af ^ (r + 4)).card : ℝ) ≤ K ^ (r + 3) * Af.card := by
      have hA' : IsBGTApproxGroup K (Af : Set G) := by rw [hAfA]; exact hA
      simpa using card_pow_succ_le_of_approx hA' (r + 3)
    have hcard : ((Af ^ r * Rf).card : ℝ) ≤ K ^ (r + 3) / c * Rf.card := by
      calc ((Af ^ r * Rf).card : ℝ) ≤ (Af ^ (r + 4)).card := by
            exact_mod_cast Finset.card_le_card hmul
        _ ≤ K ^ (r + 3) * Af.card := hApow
        _ ≤ K ^ (r + 3) * (Rf.card / c) := by
            have : (Af.card : ℝ) ≤ Rf.card / c := by rw [le_div_iff₀ hcpos]; linarith
            exact mul_le_mul_of_nonneg_left this (by positivity)
        _ = K ^ (r + 3) / c * Rf.card := by ring
    obtain ⟨F, hFA, hFcard, hcov⟩ := Finset.ruzsa_covering_mul hRne hcard
    refine ⟨F, ?_, ?_, ?_⟩
    · have := Finset.coe_subset.2 hFA
      rwa [Finset.coe_pow, hAfA] at this
    · have hcov' := Finset.coe_subset.2 hcov
      rw [Finset.coe_mul, Finset.coe_div, Finset.coe_pow, hAfA, hRfR] at hcov'
      refine hcov'.trans (Set.mul_subset_mul_left ?_)
      have hdiv : R (j + 1) / R (j + 1) ⊆ B (j + 1) := by
        rw [div_eq_mul_inv, hRsym]
        simp only [hBdef]
        have : R (j + 1) * R (j + 1) = R (j + 1) ^ 2 := (pow_two _).symm
        rw [this]
        exact Set.pow_subset_pow_right (hR1 _) (by norm_num)
      exact hdiv.trans (by
        have := hBsucc j
        exact fun x hx => this (by simpa using Set.mul_mem_mul hx (Set.one_mem_pow (hR1 (j + 1)))))
    · exact Nat.le_floor hFcard

end Lovasz.Tower
