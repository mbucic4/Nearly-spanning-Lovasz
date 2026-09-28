module
public import Mathlib
public import RequestProject.UltraFiniteTransfer
public import RequestProject.BGTFlexible

/-!
# Transfer of bounded words and of flexible trapping data

Continuing `UltraFiniteTransfer.lean`:

* `IsInternal`: a set of the ultraproduct is internal; closure under the Boolean operations,
  products, inverses, fixed powers and translates;
* `internal_conjSet`: the conjugation set `conjSet S T = {t⁻¹ s t}` transfers **with the same
  conjugating variable on both sides** (it is not replaced by `T⁻¹ S T`);
* `internal_powTrap_subset_iff`: transfer of the power-trapping tests
  `(∀ 1 ≤ i ≤ p, gⁱ ∈ C) → g ∈ T`;
* `internal_subset_finite_subcover`: an internal set covered by countably many internal sets is
  covered by finitely many of them (a consequence of countable saturation);
* `hasFlexibleTrapping_transfer`: internal flexible trapping data give flexible trapping data
  in `U`-almost every finite coordinate, with the same numerical parameters.
-/

@[expose] public section

open Filter
open scoped Pointwise

namespace Lovasz.Ultra

variable {G : ℕ → Type*} [∀ n, Group (G n)] {U : Ultrafilter ℕ}

variable (U) in
/-- A set in the ultraproduct is internal if it is the internal interpretation of a family. -/
def IsInternal (D : Set (UProd (G := G) U)) : Prop := ∃ S : ∀ n, Set (G n), D = internal U S

lemma isInternal_internal (S : ∀ n, Set (G n)) : IsInternal U (internal U S) := ⟨S, rfl⟩

namespace IsInternal

lemma union {D E : Set (UProd (G := G) U)} (hD : IsInternal U D) (hE : IsInternal U E) :
    IsInternal U (D ∪ E) := by
  obtain ⟨S, rfl⟩ := hD; obtain ⟨T, rfl⟩ := hE
  exact ⟨_, (internal_union S T).symm⟩

lemma inter {D E : Set (UProd (G := G) U)} (hD : IsInternal U D) (hE : IsInternal U E) :
    IsInternal U (D ∩ E) := by
  obtain ⟨S, rfl⟩ := hD; obtain ⟨T, rfl⟩ := hE
  exact ⟨_, (internal_inter S T).symm⟩

lemma compl {D : Set (UProd (G := G) U)} (hD : IsInternal U D) : IsInternal U Dᶜ := by
  obtain ⟨S, rfl⟩ := hD
  exact ⟨_, (internal_compl S).symm⟩

lemma diff {D E : Set (UProd (G := G) U)} (hD : IsInternal U D) (hE : IsInternal U E) :
    IsInternal U (D \ E) := hD.inter hE.compl

lemma mul {D E : Set (UProd (G := G) U)} (hD : IsInternal U D) (hE : IsInternal U E) :
    IsInternal U (D * E) := by
  obtain ⟨S, rfl⟩ := hD; obtain ⟨T, rfl⟩ := hE
  exact ⟨_, (internal_mul S T).symm⟩

lemma inv {D : Set (UProd (G := G) U)} (hD : IsInternal U D) : IsInternal U D⁻¹ := by
  obtain ⟨S, rfl⟩ := hD
  exact ⟨_, (internal_inv S).symm⟩

lemma pow {D : Set (UProd (G := G) U)} (hD : IsInternal U D) (j : ℕ) :
    IsInternal U (D ^ j) := by
  obtain ⟨S, rfl⟩ := hD
  exact ⟨_, (internal_pow S j).symm⟩

lemma singleton (q : UProd (G := G) U) : IsInternal U {q} := by
  obtain ⟨t, rfl⟩ := mk_surjective q
  exact ⟨_, (internal_singleton t).symm⟩

lemma empty : IsInternal U (∅ : Set (UProd (G := G) U)) :=
  ⟨fun _ => ∅, by ext q; obtain ⟨x, rfl⟩ := mk_surjective q; simp [U.neBot.ne]⟩

lemma univ : IsInternal U (Set.univ : Set (UProd (G := G) U)) := ⟨_, internal_univ.symm⟩

lemma translate {D : Set (UProd (G := G) U)} (hD : IsInternal U D) (q : UProd (G := G) U) :
    IsInternal U ({q} * D) := (singleton q).mul hD

lemma biUnion {ι : Type*} (s : Finset ι) {D : ι → Set (UProd (G := G) U)}
    (hD : ∀ i ∈ s, IsInternal U (D i)) : IsInternal U (⋃ i ∈ s, D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using empty
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert]
    exact (hD a (Finset.mem_insert_self a s)).union
      (ih fun i hi => hD i (Finset.mem_insert_of_mem hi))

lemma biInter {ι : Type*} (s : Finset ι) {D : ι → Set (UProd (G := G) U)}
    (hD : ∀ i ∈ s, IsInternal U (D i)) : IsInternal U (⋂ i ∈ s, D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using univ
  | insert a s ha ih =>
    rw [Finset.set_biInter_insert]
    exact (hD a (Finset.mem_insert_self a s)).inter
      (ih fun i hi => hD i (Finset.mem_insert_of_mem hi))

end IsInternal

/-! ### Conjugation sets -/

/-- **Transfer of the conjugated-word condition.**  The conjugation set
`conjSet S T = {t⁻¹ s t : s ∈ S, t ∈ T}` of internal sets is the internal conjugation set; the same
conjugating element occurs on both sides. -/
lemma internal_conjSet (S T : ∀ n, Set (G n)) :
    internal U (fun n => BGT.conjSet (S n) (T n)) =
      BGT.conjSet (internal U S) (internal U T) := by
  ext q
  obtain ⟨x, rfl⟩ := mk_surjective q
  rw [mk_mem_internal_iff]
  constructor
  · intro h
    classical
    have hex : ∀ n, x n ∈ BGT.conjSet (S n) (T n) →
        ∃ s ∈ S n, ∃ t ∈ T n, x n = t⁻¹ * s * t := fun n hn => hn
    set s : ∀ n, G n := fun n =>
      if hn : x n ∈ BGT.conjSet (S n) (T n) then (hex n hn).choose else 1
    set t : ∀ n, G n := fun n =>
      if hn : x n ∈ BGT.conjSet (S n) (T n) then (hex n hn).choose_spec.2.choose else 1
    refine ⟨mk s, (mk_mem_internal_iff _ _).2 ?_, mk t, (mk_mem_internal_iff _ _).2 ?_, ?_⟩
    · exact h.mono fun n hn => by
        simp only [s, dif_pos hn]; exact (hex n hn).choose_spec.1
    · exact h.mono fun n hn => by
        simp only [t, dif_pos hn]; exact (hex n hn).choose_spec.2.choose_spec.1
    · rw [← mk_inv, ← mk_mul, ← mk_mul, mk_eq_mk_iff]
      exact h.mono fun n hn => by
        simp only [Pi.mul_apply, Pi.inv_apply, s, t, dif_pos hn]
        exact (hex n hn).choose_spec.2.choose_spec.2
  · rintro ⟨q₁, hq₁, q₂, hq₂, hq⟩
    obtain ⟨s, rfl⟩ := mk_surjective q₁
    obtain ⟨t, rfl⟩ := mk_surjective q₂
    rw [← mk_inv, ← mk_mul, ← mk_mul, mk_eq_mk_iff] at hq
    rw [mk_mem_internal_iff] at hq₁ hq₂
    exact ((hq₁.and hq₂).and hq).mono fun n hn => ⟨s n, hn.1.1, t n, hn.1.2, hn.2⟩

/-! ### Power-trapping tests -/

/-- The set of `g` with `gⁱ ∈ C` for `1 ≤ i ≤ p`. -/
def powTrapSet {H : Type*} [Group H] (p : ℕ) (C : Set H) : Set H :=
  {g | ∀ i : ℕ, 1 ≤ i → i ≤ p → g ^ i ∈ C}

lemma internal_powTrapSet (p : ℕ) (C : ∀ n, Set (G n)) :
    internal U (fun n => powTrapSet p (C n)) = powTrapSet p (internal U C) := by
  ext q
  obtain ⟨x, rfl⟩ := mk_surjective q
  rw [mk_mem_internal_iff]
  simp only [powTrapSet, Set.mem_setOf_eq, ← mk_pow, mk_mem_internal_iff]
  have e : (∀ᶠ n in U, ∀ i ∈ Finset.Icc 1 p, x n ^ i ∈ C n) ↔
      ∀ i ∈ Finset.Icc 1 p, ∀ᶠ n in U, x n ^ i ∈ C n := eventually_all_finset _
  simp only [Finset.mem_Icc, and_imp] at e
  exact e

/-- **Transfer of a power-trapping test** `(∀ 1 ≤ i ≤ p, gⁱ ∈ C) → g ∈ T`. -/
lemma internal_powTrap_iff (p : ℕ) (C T : ∀ n, Set (G n)) :
    (∀ g, (∀ i : ℕ, 1 ≤ i → i ≤ p → g ^ i ∈ internal U C) → g ∈ internal U T) ↔
      ∀ᶠ n in U, ∀ g : G n, (∀ i : ℕ, 1 ≤ i → i ≤ p → g ^ i ∈ C n) → g ∈ T n := by
  have := internal_subset_iff (U := U) (fun n => powTrapSet p (C n)) T
  rw [internal_powTrapSet] at this
  exact this

/-! ### Countable internal covers -/

/-- **Countable internal covers have finite subcovers.**  Along a nonprincipal ultrafilter, if an
internal set is contained in the union of countably many internal sets, it is contained in the
union of finitely many of them. -/
theorem internal_subset_finite_subcover (hU : (U : Filter ℕ) ≤ cofinite)
    {C : Set (UProd (G := G) U)} (hC : IsInternal U C) {D : ℕ → Set (UProd (G := G) U)}
    (hD : ∀ j, IsInternal U (D j)) (hcov : C ⊆ ⋃ j, D j) :
    ∃ J : ℕ, C ⊆ ⋃ j ∈ Finset.range J, D j := by
  by_contra hcon
  push_neg at hcon
  choose S hS using fun j => (hC.diff (hD j))
  have hfin : ∀ k : ℕ, ∃ q, ∀ j < k, q ∈ internal U (S j) := by
    intro k
    obtain ⟨q, hqC, hq⟩ := Set.not_subset.1 (hcon k)
    refine ⟨q, fun j hj => ?_⟩
    rw [← hS j]
    exact ⟨hqC, fun hqD => hq (Set.mem_biUnion (Finset.mem_range.2 hj) hqD)⟩
  obtain ⟨q, hq⟩ := internal_countable_fip_nonempty hU S hfin
  have hqC : q ∈ C := by have := hq 0; rw [← hS 0] at this; exact this.1
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hcov hqC)
  have := hq j
  rw [← hS j] at this
  exact this.2 hj

/-! ### Transfer of the flexible trapping data -/

/-- **Transfer of flexible trapping data.**  Suppose the internal sets `B* = internal U Bs` and
`S* = internal U Ss` satisfy, in the ultraproduct, all clauses of flexible trapping: `1 ∈ B*`,
`B*` and `S*` symmetric, `B*² ⊆ ⋃ᵢ tᵢ B*` for `k` elements `tᵢ ∈ B*³` with `2k ≤ κ`, the
conjugated-product condition `(conjSet S* (B*⁴))^N ⊆ B*`, and both power-trapping implications.
Then `HasFlexibleTrapping κ p m N (Bs n) (Ss n)` holds for `U`-almost every `n`. -/
theorem hasFlexibleTrapping_transfer [∀ n, Finite (G n)] (Bs Ss : ∀ n, Set (G n))
    {κ p m N k : ℕ} (t : Fin k → ∀ n, G n)
    (hκ : 2 ≤ κ) (hp : 1 ≤ p) (hm : 1 ≤ m) (hN : 3 * p * κ ≤ N) (hk : 2 * k ≤ κ)
    (h1 : (1 : UProd (G := G) U) ∈ internal U Bs) (hBinv : (internal U Bs)⁻¹ = internal U Bs)
    (ht : ∀ i, mk (t i) ∈ internal U Bs ^ 3)
    (hcov : internal U Bs * internal U Bs ⊆ ⋃ i, {mk (t i)} * internal U Bs)
    (hSinv : (internal U Ss)⁻¹ = internal U Ss)
    (hconj : BGT.conjSet (internal U Ss) (internal U Bs ^ 4) ^ N ⊆ internal U Bs)
    (htrap1 : ∀ g, (∀ i : ℕ, 1 ≤ i → i ≤ p → g ^ i ∈ internal U Bs ^ 100) → g ∈ internal U Bs)
    (htrap2 : ∀ g, (∀ i : ℕ, 1 ≤ i → i ≤ m → g ^ i ∈ internal U Bs) → g ∈ internal U Ss) :
    ∀ᶠ n in U, BGT.HasFlexibleTrapping κ p m N (Bs n) (Ss n) := by
  classical
  have e1 : ∀ᶠ n in U, (1 : G n) ∈ Bs n := by
    have := (mk_mem_internal_iff Bs 1).1 h1; exact this
  have e2 : ∀ᶠ n in U, (Bs n)⁻¹ = Bs n := by
    rw [← internal_inv, internal_eq_iff] at hBinv; exact hBinv
  have e3 : ∀ᶠ n in U, ∀ i, t i n ∈ Bs n ^ 3 := by
    refine eventually_all.2 fun i => ?_
    have := ht i
    rw [← internal_pow, mk_mem_internal_iff] at this
    exact this
  have e4 : ∀ᶠ n in U, Bs n * Bs n ⊆ ⋃ i, {t i n} * Bs n := by
    rw [← internal_mul] at hcov
    exact (internal_subset_translates_iff t _ Bs).1 hcov
  have e5 : ∀ᶠ n in U, (Ss n)⁻¹ = Ss n := by
    rw [← internal_inv, internal_eq_iff] at hSinv; exact hSinv
  have e6 : ∀ᶠ n in U, BGT.conjSet (Ss n) (Bs n ^ 4) ^ N ⊆ Bs n := by
    rw [← internal_pow Bs 4, ← internal_conjSet, ← internal_pow, internal_subset_iff] at hconj
    exact hconj
  have e7 : ∀ᶠ n in U, ∀ g : G n, (∀ i : ℕ, 1 ≤ i → i ≤ p → g ^ i ∈ Bs n ^ 100) → g ∈ Bs n := by
    rw [← internal_pow Bs 100] at htrap1
    exact (internal_powTrap_iff p _ Bs).1 htrap1
  have e8 : ∀ᶠ n in U, ∀ g : G n, (∀ i : ℕ, 1 ≤ i → i ≤ m → g ^ i ∈ Bs n) → g ∈ Ss n :=
    (internal_powTrap_iff m Bs Ss).1 htrap2
  filter_upwards [e1, e2, e3, e4, e5, e6, e7, e8] with n h1 h2 h3 h4 h5 h6 h7 h8
  refine ⟨?_, hκ, hp, hm, hN, h5, h6, h7, h8⟩
  -- the approximate-group clause, with `X = {tᵢ} ∪ {tᵢ⁻¹}`
  set X : Finset (G n) := Finset.univ.image (fun i => t i n) ∪
    Finset.univ.image (fun i => (t i n)⁻¹) with hX
  refine ⟨Set.toFinite _, h1, h2, X, ?_, ?_, ?_, ?_⟩
  · ext g
    simp only [hX, Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Set.mem_inv, Set.mem_union, Set.mem_range]
    constructor
    · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
      · right; exact ⟨i, by rw [hi, inv_inv]⟩
      · left; exact ⟨i, inv_injective hi⟩
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · right; exact ⟨i, rfl⟩
      · left; exact ⟨i, by rw [inv_inv]⟩
  · intro g hg
    simp only [hX, Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Set.mem_union, Set.mem_range] at hg
    rcases hg with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact h3 i
    · have : (Bs n ^ 3)⁻¹ = Bs n ^ 3 := by rw [← inv_pow, h2]
      rw [← this]; exact Set.inv_mem_inv.2 (h3 i)
  · have : (X.card : ℝ) ≤ 2 * k := by
      have hc : X.card ≤ k + k := by
        refine (Finset.card_union_le _ _).trans (add_le_add ?_ ?_) <;>
        exact Finset.card_image_le.trans (by simp)
      exact_mod_cast (show X.card ≤ 2 * k by omega)
    exact this.trans (by exact_mod_cast hk)
  · intro g hg
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (h4 hg)
    obtain ⟨_, rfl, b, hb, rfl⟩ := hi
    exact Set.mul_mem_mul (by simp [hX]) hb

end Lovasz.Ultra
