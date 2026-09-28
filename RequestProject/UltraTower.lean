module
public import Mathlib
public import RequestProject.SandersTower
public import RequestProject.UltraModel

/-!
# The internal Sanders tower

For a sequence of finite `K`-approximate groups `A n` (Breuillard–Green–Tao sense) and a
nonprincipal ultrafilter `U`, the internal interpretations of the finite Sanders towers
(`Tower.finite_tower`) form a `UltraModel.TowerData` whose `A*` is `internal U A`
(`exists_towerData`).  The uniform bound on the number of translates in the finite covers is what
lets a fixed tuple of translating elements be transferred.
-/

@[expose] public section

open Filter
open scoped Pointwise

namespace Lovasz.UltraModel

open Ultra

/-- A set covered by at most `M` translates `F · B` (with `F ⊆ C`, `1 ∈ C`) is covered by the
translates by an explicit `M`-tuple of elements of `C`. -/
lemma exists_tuple_of_finset_cover {H : Type*} [Group H] {F : Finset H} {M : ℕ}
    (hF : F.card ≤ M) {A B C : Set H} (hC1 : (1 : H) ∈ C) (hFC : (F : Set H) ⊆ C)
    (hcov : A ⊆ (F : Set H) * B) :
    (∀ i : Fin M, F.toList.getD i 1 ∈ C) ∧ A ⊆ ⋃ i : Fin M, {F.toList.getD i 1} * B := by
  refine ⟨fun i => ?_, fun a ha => ?_⟩
  · by_cases hi : (i : ℕ) < F.toList.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact hFC (Finset.mem_toList.1 (List.getElem_mem hi))
    · rw [List.getD_eq_default _ _ (not_lt.1 hi)]; exact hC1
  · obtain ⟨f, hf, b, hb, rfl⟩ := hcov ha
    obtain ⟨k, hk, hkf⟩ := List.mem_iff_getElem.1 (Finset.mem_toList.2 hf)
    have hkM : k < M := by rw [Finset.length_toList] at hk; omega
    refine Set.mem_iUnion.2 ⟨⟨k, hkM⟩, f, ?_, b, hb, rfl⟩
    simp only [Set.mem_singleton_iff]
    rw [List.getD_eq_getElem _ _ hk, hkf]

/-- **The internal Sanders tower.**  For finite `K`-approximate groups `A n`, `K ≥ 1`, and a
nonprincipal ultrafilter `U`, there is tower data on the ultraproduct with `A* = internal U A`. -/
theorem exists_towerData {K : ℝ} (hK : 1 ≤ K) (G : ℕ → Type) [∀ n, Group (G n)]
    [∀ n, Finite (G n)] (A : ∀ n, Set (G n)) (hA : ∀ n, IsBGTApproxGroup K (A n))
    {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite) :
    ∃ T : TowerData U G, T.A = internal U A := by
  classical
  obtain ⟨M, hM⟩ := Tower.finite_tower hK
  choose B hB1 hBinv hBmul hBconj hBA hcov using fun n => hM (A n) (hA n)
  refine ⟨{
    nonprincipal := hU
    A := internal U A
    B := fun j => internal U (fun n => B n j)
    A_int := isInternal_internal A
    B_int := fun j => isInternal_internal _
    one_mem_A := (mk_mem_internal_iff A 1).2 (Eventually.of_forall fun n => (hA n).2.1)
    inv_A := by
      rw [← internal_inv, internal_eq_iff]
      exact Eventually.of_forall fun n => (hA n).2.2.1
    one_mem_B := fun j => (mk_mem_internal_iff _ 1).2 (Eventually.of_forall fun n => hB1 n j)
    inv_B := fun j => by
      rw [← internal_inv, internal_eq_iff]
      exact Eventually.of_forall fun n => hBinv n j
    mul_B := fun j => by
      rw [← internal_mul, internal_subset_iff]
      exact Eventually.of_forall fun n => hBmul n j
    conj_B := fun j a ha b hb => by
      obtain ⟨x, rfl⟩ := mk_surjective a
      obtain ⟨y, rfl⟩ := mk_surjective b
      rw [mk_mem_internal_iff] at ha hb
      rw [← mk_inv, ← mk_mul, ← mk_mul, mk_mem_internal_iff]
      exact (ha.and hb).mono fun n hn => hBconj n j _ hn.1 _ hn.2
    B_sub := fun j => by
      rw [← internal_pow, internal_subset_iff]
      exact Eventually.of_forall fun n => hBA n j
    cover := fun r j => by
      choose F hFA hFcov hFcard using fun n => hcov n r j
      set t : Fin (M r j) → ∀ n, G n := fun i n => (F n).toList.getD i 1 with htdef
      have ht : ∀ n, (∀ i : Fin (M r j), t i n ∈ A n ^ r) ∧
          A n ^ r ⊆ ⋃ i : Fin (M r j), {t i n} * B n j := fun n =>
        exists_tuple_of_finset_cover (hFcard n) (Set.one_mem_pow (hA n).2.1) (hFA n) (hFcov n)
      have hcovU : internal U (fun n => A n ^ r) ⊆
          ⋃ i, {mk (t i)} * internal U (fun n => B n j) :=
        (internal_subset_translates_iff t _ _).2 (Eventually.of_forall fun n => (ht n).2)
      rw [internal_pow] at hcovU
      refine ⟨Finset.univ.image fun i => mk (t i), ?_, ?_⟩
      · intro q hq
        simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hq
        obtain ⟨i, rfl⟩ := hq
        rw [← internal_pow, mk_mem_internal_iff]
        exact Eventually.of_forall fun n => (ht n).1 i
      · refine hcovU.trans fun q hq => ?_
        obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hq
        obtain ⟨_, rfl, b, hb, rfl⟩ := hi
        exact Set.mul_mem_mul (by simp) hb }, rfl⟩

end Lovasz.UltraModel
