module
public import Mathlib

/-!
# Packing and compression of subgroup chains

* `Tointon.card_mul_card_le_of_separated`: if `U ⊆ A^m` and `u v⁻¹ ∉ A²` for distinct
  `u, v ∈ U`, then the right translates `A u` are disjoint, so `|U| |A| ≤ |A^(m+1)|`.
* `Tointon.card_le_pow_of_separated`: for a `K`-approximate group, such `U` has `|U| ≤ K^m`.
* `Tointon.subgroup_chain_subset_bounded_pow`: a chain of subgroups `H₀ ≤ ⋯ ≤ Hₙ` with
  `H_{i+1} ⊆ A^t H_i` satisfies `Hₙ ⊆ A^(2tJ+t) H₀`, where `J` bounds the size of separated
  subsets of `A^(2t)`; the exponent does not depend on `n`.
-/

@[expose] public section

open scoped Pointwise

namespace Tointon

variable {G : Type*} [Group G]

/-- A finset is `A`-separated if `u v⁻¹ ∉ A²` for distinct members `u, v`. -/
def Separated (A : Set G) (U : Finset G) : Prop :=
  ∀ u ∈ U, ∀ v ∈ U, u ≠ v → u * v⁻¹ ∉ A ^ 2

lemma inv_pow_eq_self {A : Set G} (hA : A⁻¹ = A) (n : ℕ) : (A ^ n)⁻¹ = A ^ n := by
  rw [← inv_pow, hA]

/-- **Packing.**  Right translates of `A` by an `A`-separated set are disjoint. -/
theorem card_mul_card_le_of_separated [DecidableEq G] {A U : Finset G}
    (hA : (A : Set G)⁻¹ = A) {m : ℕ} (hU : (U : Set G) ⊆ (A : Set G) ^ m)
    (hsep : Separated (A : Set G) U) : U.card * A.card ≤ (A ^ (m + 1)).card := by
  classical
  have hsub : U.biUnion (fun u => A * {u}) ⊆ A ^ (m + 1) := by
    intro x hx
    obtain ⟨u, hu, hx⟩ := Finset.mem_biUnion.1 hx
    obtain ⟨a, ha, y, hy, rfl⟩ := Finset.mem_mul.1 hx
    rw [Finset.mem_singleton] at hy
    subst hy
    rw [← Finset.mem_coe, Finset.coe_pow, pow_succ']
    exact Set.mul_mem_mul ha (hU hu)
  have hdisj : (U : Set G).PairwiseDisjoint (fun u => A * {u}) := by
    intro u hu v hv huv
    rw [Function.onFun, Finset.disjoint_left]
    intro x hxu hxv
    obtain ⟨a, ha, y, hy, hx1⟩ := Finset.mem_mul.1 hxu
    obtain ⟨b, hb, y', hy', hab⟩ := Finset.mem_mul.1 hxv
    rw [Finset.mem_singleton] at hy hy'
    rw [hy] at hx1
    rw [hy', ← hx1] at hab
    apply hsep u hu v hv huv
    have : u * v⁻¹ = a⁻¹ * b := by
      calc u * v⁻¹ = a⁻¹ * (a * u) * v⁻¹ := by group
        _ = a⁻¹ * (b * v) * v⁻¹ := by rw [hab]
        _ = a⁻¹ * b := by group
    rw [this, pow_two]
    refine Set.mul_mem_mul ?_ hb
    rw [← hA]; simpa using ha
  calc U.card * A.card = ∑ u ∈ U, (A * {u}).card := by
        simp [Finset.card_mul_singleton]
    _ = (U.biUnion (fun u => A * {u})).card := (Finset.card_biUnion hdisj).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- For a `K`-approximate group, an `A`-separated subset of `A^m` has at most `K^m` elements. -/
theorem card_le_pow_of_separated [DecidableEq G] {K : ℝ} {A U : Finset G}
    (hA : IsApproximateSubgroup K (A : Set G)) {m : ℕ} (hU : (U : Set G) ⊆ (A : Set G) ^ m)
    (hsep : Separated (A : Set G) U) : (U.card : ℝ) ≤ K ^ m := by
  have h1 := card_mul_card_le_of_separated hA.inv_eq_self hU hsep
  have h2 := hA.card_pow_le (n := m + 1)
  have hpos : (0 : ℝ) < A.card := by
    have : (1 : G) ∈ A := by exact_mod_cast hA.one_mem
    exact_mod_cast Finset.card_pos.2 ⟨1, this⟩
  simp only [add_tsub_cancel_right] at h2
  have : (U.card : ℝ) * A.card ≤ K ^ m * A.card := by
    calc (U.card : ℝ) * A.card = ((U.card * A.card : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (A ^ (m + 1)).card := by exact_mod_cast h1
      _ ≤ _ := h2
  exact le_of_mul_le_mul_right this hpos

section Chain

variable {A : Set G} (hA1 : (1 : G) ∈ A) (hAinv : A⁻¹ = A)
include hA1 hAinv

omit hA1 hAinv in
lemma subset_pow_mul_of_subset {X : Set G} {H H' : Subgroup G} {a b : ℕ}
    (hX : X ⊆ A ^ a * H') (hH : (H' : Set G) ⊆ A ^ b * H) : X ⊆ A ^ (a + b) * H := by
  intro x hx
  obtain ⟨p, hp, y, hy, rfl⟩ := hX hx
  obtain ⟨q, hq, h, hh, rfl⟩ := hH hy
  show p * (q * h) ∈ _
  rw [← mul_assoc, pow_add]
  exact Set.mul_mem_mul (Set.mul_mem_mul hp hq) hh

/-- **Compression of a subgroup chain.**  If `H₀ ≤ ⋯ ≤ Hₙ` and `H_{i+1} ⊆ A^t H_i` with `t ≥ 2`,
and every `A`-separated subset of `A^(2t)` has at most `J` elements, then
`Hₙ ⊆ A^(2tJ + t) H₀`. -/
theorem subgroup_chain_subset_bounded_pow {t J : ℕ} (ht : 2 ≤ t)
    (hJ : ∀ U : Finset G, (U : Set G) ⊆ A ^ (2 * t) → Separated A U → U.card ≤ J)
    (H : ℕ → Subgroup G) (n : ℕ) (hmono : ∀ i < n, H i ≤ H (i + 1))
    (hstep : ∀ i < n, (H (i + 1) : Set G) ⊆ A ^ t * H i) :
    (H n : Set G) ⊆ A ^ (2 * t * J + t) * H 0 := by
  classical
  have hmono' : ∀ i i', i ≤ i' → i' ≤ n → H i ≤ H i' := by
    intro i i' hii' hi'
    induction i', hii' using Nat.le_induction with
    | base => exact le_rfl
    | succ k hk ih => exact (ih (by omega)).trans (hmono k (by omega))
  have hpow2 : A ^ 2 ⊆ A ^ t := Set.pow_subset_pow_right hA1 ht
  have hself : ∀ (s : ℕ) (L : Subgroup G), (L : Set G) ⊆ A ^ s * L := fun s L x hx =>
    ⟨1, Set.one_mem_pow hA1, x, hx, one_mul x⟩
  -- one jump of the greedy procedure
  have jump : ∀ j, j ≤ n → (H n : Set G) ⊆ A ^ t * H j ∨
      ∃ j', j' ≤ n ∧ j ≤ j' ∧ (H j' : Set G) ⊆ A ^ (2 * t) * H j ∧
        ∃ u ∈ A ^ (2 * t), u ∈ H j' ∧ u ∉ A ^ t * H j := by
    intro j hj
    set P : ℕ → Prop := fun l => j ≤ l ∧ (H l : Set G) ⊆ A ^ t * H j with hP
    set l := Nat.findGreatest P n with hl
    have hPj : P j := ⟨le_rfl, hself t (H j)⟩
    have hPl : P l := Nat.findGreatest_spec hj hPj
    have hln : l ≤ n := Nat.findGreatest_le n
    rcases eq_or_lt_of_le hln with heq | hlt
    · left; rw [← heq]; exact hPl.2
    · right
      have hnot : ¬ P (l + 1) := Nat.findGreatest_is_greatest (Nat.lt_succ_self l) hlt
      have hjl : j ≤ l + 1 := by have := hPl.1; omega
      have hsub : (H (l + 1) : Set G) ⊆ A ^ (2 * t) * H j := by
        have := subset_pow_mul_of_subset (hstep l hlt) hPl.2
        rwa [← two_mul] at this
      refine ⟨l + 1, hlt, hjl, hsub, ?_⟩
      have : ¬ (H (l + 1) : Set G) ⊆ A ^ t * H j := fun h => hnot ⟨hjl, h⟩
      obtain ⟨v, hv, hvn⟩ := Set.not_subset.1 this
      obtain ⟨u, hu, h, hh, rfl⟩ := hsub hv
      have hhl : h ∈ H (l + 1) := hmono' j (l + 1) hjl hlt hh
      refine ⟨u, hu, ?_, ?_⟩
      · have : u = u * h * h⁻¹ := by group
        rw [this]; exact (H (l + 1)).mul_mem hv ((H (l + 1)).inv_mem hhl)
      · rintro ⟨p, hp, h', hh', rfl⟩
        exact hvn ⟨p, hp, h' * h, (H j).mul_mem hh' hh, by group⟩
  have key : ∀ c j, j ≤ n → ∀ U : Finset G, (U : Set G) ⊆ A ^ (2 * t) → Separated A U →
      (U : Set G) ⊆ H j → J ≤ U.card + c → (H n : Set G) ⊆ A ^ (2 * t * c + t) * H j := by
    have ext : ∀ j (U : Finset G), (U : Set G) ⊆ A ^ (2 * t) → Separated A U →
        (U : Set G) ⊆ H j → ∀ u ∈ A ^ (2 * t), u ∉ A ^ t * H j →
        (insert u U : Finset G).card = U.card + 1 ∧ ((insert u U : Finset G) : Set G) ⊆ A ^ (2 * t) ∧
          Separated A (insert u U) := by
      intro j U hU hsepU hUH u hu hun
      have hnotin : u ∉ U := fun h => hun (hself t (H j) (hUH h))
      have hfar : ∀ w ∈ U, u * w⁻¹ ∉ A ^ 2 := by
        intro w hw hmem
        apply hun
        exact ⟨u * w⁻¹, hpow2 hmem, w, hUH hw, by group⟩
      refine ⟨Finset.card_insert_of_notMem hnotin, ?_, ?_⟩
      · rw [Finset.coe_insert]; exact Set.insert_subset hu hU
      · intro x hx y hy hxy
        rcases Finset.mem_insert.1 hx with rfl | hx' <;>
          rcases Finset.mem_insert.1 hy with rfl | hy'
        · exact absurd rfl hxy
        · exact hfar y hy'
        · intro hmem
          apply hfar x hx'
          rw [← inv_pow_eq_self hAinv 2]
          simpa using hmem
        · exact hsepU x hx' y hy' hxy
    intro c
    induction c with
    | zero =>
      intro j hj U hU hsepU hUH hJU
      rcases jump j hj with h | ⟨j', hj'n, hjj', hsub, u, hu, huH, hun⟩
      · simpa using h
      · obtain ⟨hcard, hU', hsep'⟩ := ext j U hU hsepU hUH u hu hun
        have := hJ _ hU' hsep'
        omega
    | succ c ih =>
      intro j hj U hU hsepU hUH hJU
      rcases jump j hj with h | ⟨j', hj'n, hjj', hsub, u, hu, huH, hun⟩
      · refine h.trans (Set.mul_subset_mul_right (Set.pow_subset_pow_right hA1 (by omega)))
      · obtain ⟨hcard, hU', hsep'⟩ := ext j U hU hsepU hUH u hu hun
        have hUH' : ((insert u U : Finset G) : Set G) ⊆ H j' := by
          rw [Finset.coe_insert]
          exact Set.insert_subset huH (hUH.trans (hmono' j j' hjj' hj'n))
        have := ih j' hj'n _ hU' hsep' hUH' (by omega)
        have h2 := subset_pow_mul_of_subset this hsub
        have e : 2 * t * c + t + 2 * t = 2 * t * (c + 1) + t := by ring
        rwa [e] at h2
  have := key J 0 (Nat.zero_le n) ∅ (by simp) (by simp [Separated]) (by simp) (by simp)
  exact this

end Chain

/-- Natural-number form of `card_le_pow_of_separated` for a set in a finite group. -/
theorem card_le_natPow_of_separated [Finite G] {κ : ℕ} {A : Set G}
    (hA : IsApproximateSubgroup (κ : ℝ) A) {m : ℕ} {U : Finset G} (hU : (U : Set G) ⊆ A ^ m)
    (hsep : Separated A U) : U.card ≤ κ ^ m := by
  classical
  have hfin : A.Finite := Set.toFinite A
  have hA' : IsApproximateSubgroup (κ : ℝ) ((hfin.toFinset : Finset G) : Set G) := by
    rwa [Set.Finite.coe_toFinset]
  have h := card_le_pow_of_separated hA' (U := U) (m := m) (by rwa [Set.Finite.coe_toFinset])
    (by rwa [Set.Finite.coe_toFinset])
  exact_mod_cast h

/-- **Chain compression for an approximate group.**  If `A` is a `κ`-approximate subgroup of a
finite group, `H₀ ≤ ⋯ ≤ Hₙ` and `H_{i+1} ⊆ A^t H_i` with `t ≥ 2`, then
`Hₙ ⊆ A^(2tκ^(2t) + t) H₀`. -/
theorem subgroup_chain_subset_pow_of_approx [Finite G] {κ : ℕ} {A : Set G}
    (hA : IsApproximateSubgroup (κ : ℝ) A) {t : ℕ} (ht : 2 ≤ t)
    (H : ℕ → Subgroup G) (n : ℕ) (hmono : ∀ i < n, H i ≤ H (i + 1))
    (hstep : ∀ i < n, (H (i + 1) : Set G) ⊆ A ^ t * H i) :
    (H n : Set G) ⊆ A ^ (2 * t * κ ^ (2 * t) + t) * H 0 :=
  subgroup_chain_subset_bounded_pow hA.one_mem hA.inv_eq_self ht
    (fun _ hU hsep => card_le_natPow_of_separated hA hU hsep) H n hmono hstep

end Tointon
