module
public import Mathlib

/-!
# Algebraic ultraproducts of groups and transfer of internal sets

Let `U` be an ultrafilter on `ℕ` and `G n` a sequence of groups.  The algebraic ultraproduct is the
quotient of the ordinary product group `∀ n, G n` by the normal subgroup `nullSubgroup U` of
sequences that are eventually `1` along `U`.  A family of sets `S n ⊆ G n` has the *internal
interpretation* `internal U S`: the class of `x` lies in it iff `x n ∈ S n` for `U`-almost all `n`.

This file proves, directly and without first-order syntax:

* `mk_eq_mk_iff`: equality in the ultraproduct is eventual coordinatewise equality;
* `mk_mem_internal_iff`: membership in an internal set is independent of representatives;
* transfer of nonemptiness, inclusion, products, inverses, fixed powers, complements, finite
  intersections and unions, singletons, translates, and preimages under coordinatewise maps
  (in particular under fixed powers `g ↦ g ^ i`);
* transfer of a fixed finite cover by translates, and the resulting cardinality bound in the
  finite coordinates (`eventually_ncard_le_of_subset_translates`);
* an example of transferring a trapping test (`power_trapping_test_transfer`);
* countable saturation for internal sets along a nonprincipal ultrafilter, proved by an explicit
  diagonal argument (`internal_countable_fip_nonempty`).
-/

@[expose] public section

open Filter
open scoped Pointwise

namespace Lovasz.Ultra

variable {G : ℕ → Type*} [∀ n, Group (G n)] (U : Ultrafilter ℕ)

/-- Sequences that are eventually `1` along `U`. -/
def nullSubgroup : Subgroup (∀ n, G n) where
  carrier := {x | ∀ᶠ n in U, x n = 1}
  one_mem' := Eventually.of_forall fun _ => rfl
  mul_mem' {a b} ha hb := (ha.and hb).mono fun n h => by simp [h.1, h.2]
  inv_mem' {a} ha := ha.mono fun n h => by simp [h]

instance nullSubgroup_normal : (nullSubgroup (G := G) U).Normal where
  conj_mem x hx g := hx.mono fun n h => by simp [h]

/-- The algebraic ultraproduct of the groups `G n` along `U`. -/
abbrev UProd := (∀ n, G n) ⧸ nullSubgroup (G := G) U

variable {U}

/-- The class of a sequence in the ultraproduct. -/
abbrev mk (x : ∀ n, G n) : UProd (G := G) U := QuotientGroup.mk x

lemma mk_eq_mk_iff (x y : ∀ n, G n) : mk (U := U) x = mk y ↔ ∀ᶠ n in U, x n = y n := by
  rw [QuotientGroup.eq]
  change (∀ᶠ n in U, (x⁻¹ * y) n = 1) ↔ _
  simp [inv_mul_eq_one]

lemma mk_surjective : Function.Surjective (mk (G := G) (U := U)) :=
  QuotientGroup.mk_surjective

@[simp] lemma mk_mul (x y : ∀ n, G n) : mk (U := U) (x * y) = mk x * mk y := rfl

@[simp] lemma mk_inv (x : ∀ n, G n) : mk (U := U) x⁻¹ = (mk x)⁻¹ := rfl

@[simp] lemma mk_one : mk (U := U) (1 : ∀ n, G n) = 1 := rfl

@[simp] lemma mk_pow (x : ∀ n, G n) (j : ℕ) : mk (U := U) (x ^ j) = mk x ^ j := rfl

variable (U)

/-- The internal set determined by the family `S n ⊆ G n`. -/
def internal (S : ∀ n, Set (G n)) : Set (UProd (G := G) U) :=
  {q | ∃ x : ∀ n, G n, mk x = q ∧ ∀ᶠ n in U, x n ∈ S n}

variable {U}

@[simp] lemma mk_mem_internal_iff (S : ∀ n, Set (G n)) (x : ∀ n, G n) :
    mk x ∈ internal U S ↔ ∀ᶠ n in U, x n ∈ S n := by
  constructor
  · rintro ⟨y, hy, hS⟩
    rw [mk_eq_mk_iff] at hy
    exact (hy.and hS).mono fun n h => h.1 ▸ h.2
  · exact fun h => ⟨x, rfl, h⟩

/-! ### First transfer lemmas -/

open Classical in
/-- A choice of an element of `S n` whenever it is nonempty, and `1` otherwise. -/
noncomputable def pick (S : ∀ n, Set (G n)) : ∀ n, G n :=
  fun n => if h : (S n).Nonempty then h.some else 1

lemma pick_mem {S : ∀ n, Set (G n)} {n : ℕ} (h : (S n).Nonempty) : pick S n ∈ S n := by
  simp [pick, h, h.some_mem]

lemma internal_nonempty_iff (S : ∀ n, Set (G n)) :
    (internal U S).Nonempty ↔ ∀ᶠ n in U, (S n).Nonempty := by
  constructor
  · rintro ⟨q, x, -, hx⟩
    exact hx.mono fun n h => ⟨x n, h⟩
  · intro h
    exact ⟨mk (pick S), (mk_mem_internal_iff _ _).2 (h.mono fun n hn => pick_mem hn)⟩

lemma internal_subset_iff (S T : ∀ n, Set (G n)) :
    internal U S ⊆ internal U T ↔ ∀ᶠ n in U, S n ⊆ T n := by
  constructor
  · intro h
    by_contra hne
    have hbad : ∀ᶠ n in U, (S n \ T n).Nonempty := by
      rw [← Ultrafilter.eventually_not] at hne
      exact hne.mono fun n hn => by
        rw [Set.not_subset] at hn
        obtain ⟨a, ha, hb⟩ := hn
        exact ⟨a, ha, hb⟩
    set x := pick (fun n => S n \ T n)
    have hx : ∀ᶠ n in U, x n ∈ S n \ T n := hbad.mono fun n hn => pick_mem hn
    have hxT := (mk_mem_internal_iff T x).1
      (h ((mk_mem_internal_iff S x).2 (hx.mono fun n hn => hn.1)))
    have := (hx.and hxT).exists
    obtain ⟨n, hn1, hn2⟩ := this
    exact hn1.2 hn2
  · intro h q hq
    obtain ⟨x, rfl, hx⟩ := hq
    exact (mk_mem_internal_iff _ _).2 ((h.and hx).mono fun n hn => hn.1 hn.2)

lemma internal_eq_iff (S T : ∀ n, Set (G n)) :
    internal U S = internal U T ↔ ∀ᶠ n in U, S n = T n := by
  rw [Set.Subset.antisymm_iff, internal_subset_iff, internal_subset_iff, ← eventually_and]
  exact eventually_congr (Eventually.of_forall fun n => Set.Subset.antisymm_iff.symm)

lemma internal_mul (S T : ∀ n, Set (G n)) :
    internal U (fun n => S n * T n) = internal U S * internal U T := by
  ext q
  obtain ⟨x, rfl⟩ := mk_surjective q
  rw [mk_mem_internal_iff]
  constructor
  · intro h
    classical
    set a : ∀ n, G n := fun n =>
      if hn : x n ∈ S n * T n then (Set.mem_mul.1 hn).choose else x n
    set b : ∀ n, G n := fun n =>
      if hn : x n ∈ S n * T n then (Set.mem_mul.1 hn).choose_spec.2.choose else 1
    have hab : a * b = x := by
      funext n
      simp only [Pi.mul_apply, a, b]
      split_ifs with hn
      · exact (Set.mem_mul.1 hn).choose_spec.2.choose_spec.2
      · simp
    refine ⟨mk a, (mk_mem_internal_iff _ _).2 ?_, mk b, (mk_mem_internal_iff _ _).2 ?_, ?_⟩
    · exact h.mono fun n hn => by
        simp only [a, dif_pos hn]
        exact (Set.mem_mul.1 hn).choose_spec.1
    · exact h.mono fun n hn => by
        simp only [b, dif_pos hn]
        exact (Set.mem_mul.1 hn).choose_spec.2.choose_spec.1
    · show mk a * mk b = mk x
      rw [← mk_mul, hab]
  · rintro ⟨q₁, hq₁, q₂, hq₂, hq⟩
    obtain ⟨a, rfl⟩ := mk_surjective q₁
    obtain ⟨b, rfl⟩ := mk_surjective q₂
    change mk a * mk b = mk x at hq
    rw [← mk_mul, mk_eq_mk_iff] at hq
    rw [mk_mem_internal_iff] at hq₁ hq₂
    exact ((hq₁.and hq₂).and hq).mono fun n hn => hn.2 ▸ Set.mul_mem_mul hn.1.1 hn.1.2

lemma internal_inv (S : ∀ n, Set (G n)) :
    internal U (fun n => (S n)⁻¹) = (internal U S)⁻¹ := by
  ext q
  obtain ⟨x, rfl⟩ := mk_surjective q
  rw [Set.mem_inv, ← mk_inv, mk_mem_internal_iff, mk_mem_internal_iff]
  rfl

lemma internal_one : internal U (fun n => (1 : Set (G n))) = 1 := by
  ext q
  obtain ⟨x, rfl⟩ := mk_surjective q
  rw [mk_mem_internal_iff, Set.mem_one, ← mk_one, mk_eq_mk_iff]
  rfl

/-- Fixed powers of internal sets are internal. -/
lemma internal_pow (S : ∀ n, Set (G n)) (j : ℕ) :
    internal U (fun n => S n ^ j) = internal U S ^ j := by
  induction j with
  | zero => simpa using internal_one
  | succ j ih =>
    simp only [pow_succ]
    rw [internal_mul, ih]

lemma internal_compl (S : ∀ n, Set (G n)) :
    internal U (fun n => (S n)ᶜ) = (internal U S)ᶜ := by
  ext q
  obtain ⟨x, rfl⟩ := mk_surjective q
  rw [Set.mem_compl_iff, mk_mem_internal_iff, mk_mem_internal_iff]
  exact Ultrafilter.eventually_not

lemma internal_univ : internal U (fun n => (Set.univ : Set (G n))) = Set.univ := by
  ext q
  obtain ⟨x, rfl⟩ := mk_surjective q
  simp

lemma internal_inter (S T : ∀ n, Set (G n)) :
    internal U (fun n => S n ∩ T n) = internal U S ∩ internal U T := by
  ext q
  obtain ⟨x, rfl⟩ := mk_surjective q
  simp only [Set.mem_inter_iff, mk_mem_internal_iff]
  exact eventually_and

lemma internal_union (S T : ∀ n, Set (G n)) :
    internal U (fun n => S n ∪ T n) = internal U S ∪ internal U T := by
  ext q
  obtain ⟨x, rfl⟩ := mk_surjective q
  simp only [Set.mem_union, mk_mem_internal_iff]
  exact Ultrafilter.eventually_or

lemma internal_biInter_finset {ι : Type*} (s : Finset ι) (S : ι → ∀ n, Set (G n)) :
    internal U (fun n => ⋂ i ∈ s, S i n) = ⋂ i ∈ s, internal U (S i) := by
  ext q
  obtain ⟨x, rfl⟩ := mk_surjective q
  simp only [Set.mem_iInter, mk_mem_internal_iff]
  exact eventually_all_finset s

lemma internal_biUnion_finset {ι : Type*} (s : Finset ι) (S : ι → ∀ n, Set (G n)) :
    internal U (fun n => ⋃ i ∈ s, S i n) = ⋃ i ∈ s, internal U (S i) := by
  rw [← compl_compl (internal U fun n => ⋃ i ∈ s, S i n), ← internal_compl]
  simp only [Set.compl_iUnion]
  rw [internal_biInter_finset]
  simp only [internal_compl, ← Set.compl_iUnion, compl_compl]

lemma internal_singleton (t : ∀ n, G n) :
    internal U (fun n => ({t n} : Set (G n))) = {mk t} := by
  ext q
  obtain ⟨x, rfl⟩ := mk_surjective q
  simp only [mk_mem_internal_iff, Set.mem_singleton_iff, mk_eq_mk_iff]

/-- Left translates of internal sets are internal. -/
lemma internal_translate (t : ∀ n, G n) (S : ∀ n, Set (G n)) :
    internal U (fun n => {t n} * S n) = {mk t} * internal U S := by
  rw [internal_mul, internal_singleton]

/-- Preimages of internal sets under coordinatewise maps are internal. -/
lemma preimage_internal (f : ∀ n, G n → G n) (F : UProd (G := G) U → UProd (G := G) U)
    (hF : ∀ x, F (mk x) = mk fun n => f n (x n)) (S : ∀ n, Set (G n)) :
    F ⁻¹' internal U S = internal U (fun n => f n ⁻¹' S n) := by
  ext q
  obtain ⟨x, rfl⟩ := mk_surjective q
  rw [Set.mem_preimage, hF, mk_mem_internal_iff, mk_mem_internal_iff]
  rfl

/-- Preimages of internal sets under a fixed power map are internal. -/
lemma preimage_pow_internal (i : ℕ) (S : ∀ n, Set (G n)) :
    (fun q : UProd (G := G) U => q ^ i) ⁻¹' internal U S =
      internal U (fun n => (fun g : G n => g ^ i) ⁻¹' S n) :=
  preimage_internal (fun _ g => g ^ i) _ (fun x => (mk_pow x i).symm) S

/-! ### Finite covers by translates -/

/-- A fixed finite cover by translates transfers in both directions. -/
lemma internal_subset_translates_iff {r : ℕ} (t : Fin r → ∀ n, G n) (A B : ∀ n, Set (G n)) :
    internal U A ⊆ ⋃ i, {mk (t i)} * internal U B ↔
      ∀ᶠ n in U, A n ⊆ ⋃ i, {t i n} * B n := by
  have h : internal U (fun n => ⋃ i, {t i n} * B n) = ⋃ i, {mk (t i)} * internal U B := by
    have := internal_biUnion_finset (U := U) Finset.univ (fun i n => {t i n} * B n)
    simp only [Finset.mem_univ, Set.iUnion_true] at this
    rw [this]
    simp only [internal_translate]
  rw [← h, internal_subset_iff]

/-- In a finite group, a set covered by `r` left translates of `B` has at most `r * |B|`
elements. -/
lemma ncard_le_of_subset_translates {K : Type*} [Group K] [Finite K] {r : ℕ} (t : Fin r → K)
    {A B : Set K} (h : A ⊆ ⋃ i, {t i} * B) : A.ncard ≤ r * B.ncard := by
  calc A.ncard ≤ (⋃ i, {t i} * B).ncard := Set.ncard_le_ncard h
    _ ≤ ∑ i, ({t i} * B).ncard := Set.ncard_iUnion_le_of_fintype _
    _ = ∑ _i : Fin r, B.ncard := by
        congr 1; ext i
        rw [Set.singleton_mul]
        exact Set.ncard_image_of_injective _ (mul_right_injective (t i))
    _ = r * B.ncard := by simp

/-- An internal cover by `r` translates gives, in `U`-almost every finite coordinate, the
cardinality bound `|A n| ≤ r |B n|`.  No cardinality is interpreted inside the ultraproduct. -/
lemma eventually_ncard_le_of_subset_translates [∀ n, Finite (G n)] {r : ℕ}
    (t : Fin r → ∀ n, G n) (A B : ∀ n, Set (G n))
    (h : internal U A ⊆ ⋃ i, {mk (t i)} * internal U B) :
    ∀ᶠ n in U, (A n).ncard ≤ r * (B n).ncard :=
  ((internal_subset_translates_iff t A B).1 h).mono fun n hn =>
    ncard_le_of_subset_translates (fun i => t i n) hn

/-- **Transfer of the power-trapping test.**  The internal inclusion
`⋂_{1 ≤ i ≤ p} {g : g^i ∈ B^k} ⊆ B` holds in the ultraproduct iff the corresponding inclusion
holds in `U`-almost every coordinate. -/
lemma power_trapping_test_transfer (p k : ℕ) (B : ∀ n, Set (G n)) :
    (⋂ i ∈ Finset.Icc 1 p, (fun q : UProd (G := G) U => q ^ i) ⁻¹' (internal U B ^ k)) ⊆
        internal U B ↔
      ∀ᶠ n in U, (⋂ i ∈ Finset.Icc 1 p, (fun g : G n => g ^ i) ⁻¹' (B n ^ k)) ⊆ B n := by
  have : (⋂ i ∈ Finset.Icc 1 p, (fun q : UProd (G := G) U => q ^ i) ⁻¹' (internal U B ^ k)) =
      internal U (fun n => ⋂ i ∈ Finset.Icc 1 p, (fun g : G n => g ^ i) ⁻¹' (B n ^ k)) := by
    rw [internal_biInter_finset]
    refine Set.iInter₂_congr fun i _ => ?_
    rw [← internal_pow, preimage_pow_internal]
  rw [this, internal_subset_iff]

/-! ### Countable saturation by an explicit diagonal argument -/

/-- **Countable saturation for internal sets.**  Let `U` be a nonprincipal ultrafilter on `ℕ`
and `S j` (`j : ℕ`) families of sets such that every finite intersection of the internal sets
`internal U (S j)` is nonempty.  Then the intersection of all of them is nonempty.

The proof is the diagonal argument: in coordinate `n` choose a point in `S 0 n ∩ ⋯ ∩ S (k-1) n`
for the largest `k ≤ n` for which this intersection is nonempty.  It never intersects countably
many `U`-large sets. -/
theorem internal_countable_fip_nonempty (hU : (U : Filter ℕ) ≤ cofinite)
    (S : ℕ → ∀ n, Set (G n)) (hfin : ∀ k : ℕ, ∃ q, ∀ j < k, q ∈ internal U (S j)) :
    ∃ q, ∀ j, q ∈ internal U (S j) := by
  classical
  -- `P n k`: the first `k` sets have a common point in coordinate `n`
  set P : ℕ → ℕ → Prop := fun n k => ∃ g : G n, ∀ j < k, g ∈ S j n with hP
  have hP0 : ∀ n, P n 0 := fun n => ⟨1, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  have hPev : ∀ k, ∀ᶠ n in U, P n k := by
    intro k
    obtain ⟨q, hq⟩ := hfin k
    obtain ⟨y, rfl⟩ := mk_surjective q
    have : ∀ᶠ n in U, ∀ j ∈ Finset.range k, y n ∈ S j n :=
      (eventually_all_finset _).2 fun j hj =>
        (mk_mem_internal_iff _ _).1 (hq j (Finset.mem_range.1 hj))
    exact this.mono fun n hn => ⟨y n, fun j hj => hn j (Finset.mem_range.2 hj)⟩
  set kk : ℕ → ℕ := fun n => Nat.findGreatest (P n) n with hkk
  have hkkP : ∀ n, P n (kk n) := fun n => Nat.findGreatest_spec (Nat.zero_le n) (hP0 n)
  choose x hx using hkkP
  refine ⟨mk x, fun j => (mk_mem_internal_iff _ _).2 ?_⟩
  have hge : ∀ᶠ n in U, j + 1 ≤ n :=
    hU (by rw [Nat.cofinite_eq_atTop]; exact eventually_ge_atTop (j + 1))
  exact ((hPev (j + 1)).and hge).mono fun n hn =>
    hx n j (lt_of_lt_of_le (Nat.lt_succ_self j) (Nat.le_findGreatest hn.2 hn.1))

end Lovasz.Ultra
