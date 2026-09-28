module
public import RequestProject.NilChain

/-!
# Central saturation: approximate groups covering a nilpotent group modulo its centre

If `A` is a `κ`-approximate subgroup of a finite nilpotent group `G` with `G = A · Z(G)`, then
`[G, G] ⊆ A^(8κ^8 + 4)` (Tointon, *Approximate subgroups of residually nilpotent groups*,
Proposition 4.1).  The bound does not depend on the nilpotency class of `G`.

Instead of Hall's basic commutators we use a greedy chain of normal subgroups
`1 = N₀ ≤ N₁ ≤ ⋯ ≤ [G, G]`, each obtained from the previous one by adjoining a single commutator
that is central modulo it; each step costs a factor `A⁴`, and the chain-compression lemma
bounds the total.
-/

@[expose] public section

open scoped Pointwise
open scoped commutatorElement

namespace Tointon

variable {G : Type*} [Group G]

/-- If `G = A · Z(G)`, every commutator lies in `A⁴`. -/
lemma commutator_mem_pow_four {A : Set G} (hAinv : A⁻¹ = A)
    (hcov : ∀ g : G, ∃ a ∈ A, ∃ z ∈ Subgroup.center G, g = a * z) (x y : G) :
    ⁅x, y⁆ ∈ A ^ 4 := by
  obtain ⟨a, ha, z, hz, rfl⟩ := hcov x
  obtain ⟨b, hb, w, hw, rfl⟩ := hcov y
  have hz' := Subgroup.mem_center_iff.1 hz
  have hw' := Subgroup.mem_center_iff.1 hw
  have e : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
    simp only [commutatorElement_def]
    calc a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹
        = a * (z * b) * (w * z⁻¹) * a⁻¹ * w⁻¹ * b⁻¹ := by group
      _ = a * (b * z) * (z⁻¹ * w) * a⁻¹ * w⁻¹ * b⁻¹ := by
          rw [hz' b]
          have : w * z⁻¹ = z⁻¹ * w := (Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ hz) w)
          rw [this]
      _ = a * b * (w * a⁻¹) * w⁻¹ * b⁻¹ := by group
      _ = a * b * (a⁻¹ * w) * w⁻¹ * b⁻¹ := by
          have : w * a⁻¹ = a⁻¹ * w := (hw' a⁻¹).symm
          rw [this]
      _ = a * b * a⁻¹ * b⁻¹ := by group
  rw [e, commutatorElement_def]
  have hainv : a⁻¹ ∈ A := by rw [← hAinv]; simpa using ha
  have hbinv : b⁻¹ ∈ A := by rw [← hAinv]; simpa using hb
  have : (4 : ℕ) = 1 + 1 + 1 + 1 := rfl
  rw [this, pow_add, pow_add, pow_add, pow_one]
  exact Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul ha hb) hainv) hbinv

/-- In a nilpotent group, a proper normal subgroup `N` of `[G, G]` misses some commutator that
is central modulo `N`. -/
lemma exists_commutator_central_mod [Group.IsNilpotent G] {N : Subgroup G}
    (hN : ¬ ⁅(⊤ : Subgroup G), ⊤⁆ ≤ N) :
    ∃ p : G × G, ⁅p.1, p.2⁆ ∉ N ∧ ∀ g, ⁅⁅p.1, p.2⁆, g⁆ ∈ N := by
  classical
  obtain ⟨s, hs⟩ := nilpotent_iff_lowerCentralSeries.1 (inferInstance : Group.IsNilpotent G)
  have h1 : ¬ (⊤ : Subgroup G).lowerCentralSeries 1 ≤ N := by
    rwa [lowerCentralSeries_one, commutator_def]
  set P : ℕ → Prop := fun j => ¬ (⊤ : Subgroup G).lowerCentralSeries j ≤ N with hP
  have hs1 : 1 ≤ s := by
    by_contra h
    have : s = 0 := by omega
    subst this
    apply h1
    have : (⊤ : Subgroup G).lowerCentralSeries 1 ≤ (⊤ : Subgroup G).lowerCentralSeries 0 :=
      (⊤ : Subgroup G).lowerCentralSeries_antitone (by omega)
    rw [hs] at this
    exact this.trans bot_le
  obtain ⟨j, hj⟩ : ∃ j, j = Nat.findGreatest P s := ⟨_, rfl⟩
  have hPj : P j := hj ▸ Nat.findGreatest_spec hs1 h1
  have hjs : j < s := by
    rcases lt_or_eq_of_le (hj ▸ Nat.findGreatest_le (P := P) s) with h | h
    · exact h
    · exfalso; apply hPj; rw [h, hs]; exact bot_le
  have hnext : (⊤ : Subgroup G).lowerCentralSeries (j + 1) ≤ N := by
    by_contra h
    exact Nat.findGreatest_is_greatest (P := P) (n := s) (k := j + 1) (by omega) (by omega) h
  have hj0 : 1 ≤ j := hj ▸ Nat.le_findGreatest hs1 h1
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have : ¬ ∀ x ∈ (⊤ : Subgroup G).lowerCentralSeries j', ∀ y : G, ⁅x, y⁆ ∈ N := by
    intro hall
    apply hPj
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.commutator_le]
    intro p hp q _
    exact hall p hp q
  push_neg at this
  obtain ⟨x, hx, y, hxy⟩ := this
  refine ⟨(x, y), hxy, fun g => hnext ?_⟩
  have hc : ⁅x, y⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries (j' + 1) := by
    rw [Subgroup.lowerCentralSeries_succ]
    exact Subgroup.commutator_mem_commutator hx trivial
  rw [Subgroup.lowerCentralSeries_succ]
  exact Subgroup.commutator_mem_commutator hc trivial

section Step

variable {N : Subgroup G} [hN : N.Normal] {c : G} (hc : ∀ g, ⁅c, g⁆ ∈ N)
include hc

/-- Adjoining an element that is central modulo a normal subgroup gives a normal subgroup. -/
lemma normal_zpowers_sup : (Subgroup.zpowers c ⊔ N).Normal := by
  constructor
  intro x hx g
  have hmem : (x : G) ∈ ((Subgroup.zpowers c ⊔ N : Subgroup G) : Set G) := hx
  rw [Subgroup.mul_normal] at hmem
  obtain ⟨y, hy, n, hn, rfl⟩ := hmem
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have hgc : g * c * g⁻¹ = ⁅g, c⁆ * c := by simp only [commutatorElement_def]; group
  have hgc' : ⁅g, c⁆ ∈ N := by
    have : ⁅g, c⁆ = ⁅c, g⁆⁻¹ := by simp only [commutatorElement_def]; group
    rw [this]; exact N.inv_mem (hc g)
  have e : g * (c ^ k * n) * g⁻¹ = (g * c * g⁻¹) ^ k * (g * n * g⁻¹) := by
    rw [← MulAut.conj_apply, map_mul, map_zpow]; simp [MulAut.conj_apply]
  rw [e]
  refine Subgroup.mul_mem _ (Subgroup.zpow_mem _ ?_ k) (Subgroup.mem_sup_right (hN.conj_mem n hn g))
  rw [hgc]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hgc')
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers c))

/-- Modulo `N`, `⁅x, y^m⁆ = ⁅x, y⁆^m` when `⁅x, y⁆` is central modulo `N`. -/
lemma pow_eq_commutator_pow_mul {x y : G} (hxy : c = ⁅x, y⁆) (m : ℕ) :
    ∃ n ∈ N, c ^ m = ⁅x, y ^ m⁆ * n := by
  set π := QuotientGroup.mk' N
  have hcent : ∀ g : G ⧸ N, π c * g = g * π c := by
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N g
    have : π ⁅c, g⁆ = 1 := (QuotientGroup.eq_one_iff _).2 (hc g)
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  have key : ∀ m : ℕ, ⁅π x, π y ^ m⁆ = π c ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have e : ⁅π x, π y ^ (m + 1)⁆ = ⁅π x, π y ^ m⁆ * (π y ^ m * ⁅π x, π y⁆ * (π y ^ m)⁻¹) := by
        rw [pow_succ]; simp only [commutatorElement_def]; group
      rw [e, ih, ← map_commutatorElement, ← hxy, ← hcent (π y ^ m), mul_inv_cancel_right,
        pow_succ]
  refine ⟨⁅x, y ^ m⁆⁻¹ * c ^ m, ?_, by group⟩
  rw [← QuotientGroup.eq_one_iff (N := N)]
  change π (⁅x, y ^ m⁆⁻¹ * c ^ m) = 1
  rw [map_mul, map_inv, map_pow, map_commutatorElement, map_pow, key, inv_mul_cancel]

end Step

/-- **Central saturation** (Tointon, Proposition 4.1).  If `A` is a `κ`-approximate subgroup of a
finite nilpotent group `G` and `G = A · Z(G)`, then `[G, G] ⊆ A^(8κ^8 + 4)`. -/
theorem derived_subset_pow_of_mul_center_eq_univ [Finite G] [Group.IsNilpotent G] {κ : ℕ}
    {A : Set G} (hA : IsApproximateSubgroup (κ : ℝ) A)
    (hcov : ∀ g : G, ∃ a ∈ A, ∃ z ∈ Subgroup.center G, g = a * z) :
    ((⁅(⊤ : Subgroup G), ⊤⁆ : Subgroup G) : Set G) ⊆ A ^ (8 * κ ^ 8 + 4) := by
  classical
  set D : Subgroup G := ⁅(⊤ : Subgroup G), ⊤⁆ with hD
  -- the greedy step
  let Pc : Subgroup G → G × G → Prop := fun N p => ⁅p.1, p.2⁆ ∉ N ∧ ∀ g, ⁅⁅p.1, p.2⁆, g⁆ ∈ N
  let next : Subgroup G → Subgroup G := fun N =>
    if h : ∃ p, Pc N p then Subgroup.zpowers ⁅h.choose.1, h.choose.2⁆ ⊔ N else N
  let H : ℕ → Subgroup G := fun i => next^[i] ⊥
  have hHsucc : ∀ i, H (i + 1) = next (H i) := fun i => Function.iterate_succ_apply' _ _ _
  -- invariants
  have hinv : ∀ i, (H i).Normal ∧ H i ≤ D := by
    intro i
    induction i with
    | zero => exact ⟨by simp only [H, Function.iterate_zero, id]; infer_instance, bot_le⟩
    | succ i ih =>
      obtain ⟨hn, hle⟩ := ih
      rw [hHsucc]
      simp only [next]
      split_ifs with h
      · have hspec := h.choose_spec
        refine ⟨normal_zpowers_sup hspec.2, sup_le ?_ hle⟩
        rw [Subgroup.zpowers_le]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      · exact ⟨hn, hle⟩
  have hmono : ∀ i, H i ≤ H (i + 1) := by
    intro i
    rw [hHsucc]
    simp only [next]
    split_ifs
    · exact le_sup_right
    · exact le_rfl
  have hstep : ∀ i, (H (i + 1) : Set G) ⊆ A ^ 4 * H i := by
    intro i x hx
    haveI := (hinv i).1
    rw [hHsucc] at hx
    simp only [next] at hx
    split_ifs at hx with h
    · set p := h.choose with hp
      have hspec : Pc (H i) p := h.choose_spec
      have hmem : x ∈ ((Subgroup.zpowers ⁅p.1, p.2⁆ ⊔ H i : Subgroup G) : Set G) := hx
      rw [Subgroup.mul_normal] at hmem
      obtain ⟨y, hy, n, hn, rfl⟩ := hmem
      have hy' : y ∈ Subgroup.zpowers ⁅p.1, p.2⁆ := hy
      rw [← mem_powers_iff_mem_zpowers] at hy'
      obtain ⟨m, rfl⟩ := hy'
      obtain ⟨n', hn', he⟩ := pow_eq_commutator_pow_mul hspec.2 rfl m
      show ⁅p.1, p.2⁆ ^ m * n ∈ _
      rw [he, mul_assoc]
      exact Set.mul_mem_mul (commutator_mem_pow_four hA.inv_eq_self hcov _ _)
        ((H i).mul_mem hn' hn)
    · exact ⟨1, Set.one_mem_pow hA.one_mem, x, hx, one_mul x⟩
  -- the chain reaches `D`
  have hreach : H (Nat.card G) = D := by
    have hgrow : ∀ i, H i = D ∨ i < (H i : Set G).ncard := by
      intro i
      induction i with
      | zero =>
        right
        simp only [H, Function.iterate_zero, id, Subgroup.coe_bot, Set.ncard_singleton]
        omega
      | succ i ih =>
        have hstay : H i = D → H (i + 1) = D := by
          intro heq
          have hno : ¬ ∃ p, Pc (H i) p := by
            rintro ⟨p, hp1, -⟩
            apply hp1
            rw [heq]
            exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
          rw [hHsucc]
          simp only [next, dif_neg hno]
          exact heq
        rcases ih with heq | hlt
        · exact Or.inl (hstay heq)
        · by_cases hD' : H i = D
          · exact Or.inl (hstay hD')
          · right
            have hnle : ¬ D ≤ H i := fun h => hD' (le_antisymm (hinv i).2 h)
            obtain ⟨p, hp⟩ := exists_commutator_central_mod hnle
            have hex : ∃ p, Pc (H i) p := ⟨p, hp⟩
            have hlt' : (H i : Set G) ⊂ (H (i + 1) : Set G) := by
              refine Set.ssubset_iff_subset_ne.2 ⟨hmono i, ?_⟩
              intro heq
              rw [hHsucc] at heq
              simp only [next, dif_pos hex] at heq
              apply hex.choose_spec.1
              rw [← SetLike.mem_coe, heq]
              exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
            have := Set.ncard_lt_ncard hlt' (Set.toFinite _)
            omega
    rcases hgrow (Nat.card G) with h | h
    · exact h
    · exfalso
      have : (H (Nat.card G) : Set G).ncard ≤ Nat.card G := by
        rw [← Set.ncard_univ]; exact Set.ncard_le_ncard (Set.subset_univ _)
      omega
  have := subgroup_chain_subset_pow_of_approx hA (t := 4) (by norm_num) H (Nat.card G)
    (fun i _ => hmono i) (fun i _ => hstep i)
  rw [hreach] at this
  simp only [H, Function.iterate_zero, id, Subgroup.coe_bot, Set.mul_singleton, mul_one,
    Set.image_id'] at this
  convert this using 2

end Tointon
