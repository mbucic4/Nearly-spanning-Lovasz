module
public import RequestProject.Cayley
public import Mathlib.Combinatorics.Additive.ApproximateSubgroup

/-!
# Tessera–Tointon for Cayley graphs, from Breuillard–Green–Tao

For a finite Cayley graph the argument of Tessera–Tointon (proof of Corollary 2.4 via
Theorem 2.3 and Theorem 7.1) reduces to the following steps, all proved here:

* a pigeonhole over the scales `m₀ 3^j` (Lemma 8.1) gives a radius `m` with
  `|T^(3m)| ≤ K |T^m|` where `T = {1} ∪ S ∪ S⁻¹`;
* Ruzsa's argument (Proposition 6.1, discrete case) makes `T^(2m)` a `K³`-approximate group;
* the Breuillard–Green–Tao theorem (Theorem 6.4 of Tessera–Tointon) then gives normal subgroups
  `N ⊆ T^(8m)` and `G₁` of bounded index with `G₁/(G₁ ∩ N)` nilpotent of bounded class.

The only input not proved in the project is the Breuillard–Green–Tao theorem, stated below (for
finite groups only, and without the rank bound, which is all that is used) as
`BreuillardGreenTao`.
-/

@[expose] public section


open scoped Pointwise

namespace Lovasz

/-- **Breuillard–Green–Tao** (Corollary 11.2 and Remark 11.4 of *The structure of approximate
groups*; Theorem 6.4 of Tessera–Tointon), for finite groups, without the rank bound.
For every `K ≥ 1` there are `n₀, k, s` such that: if `A` is a symmetric generating set of a
finite group `G` containing `1`, `m ≥ n₀`, and `A^m` is a `K`-approximate group, then there are
normal subgroups `H ≤ G₁` of `G` with `H ⊆ A^(4m)`, `[G : G₁] ≤ k`, and `G₁/(G₁ ∩ H)` nilpotent of
class at most `s` (i.e. the `s`-th term of the lower central series of `G₁` lies in `H`). -/
def BreuillardGreenTao : Prop :=
  ∀ K : ℝ, 1 ≤ K → ∃ n₀ k s : ℕ, ∀ (G : Type) [Group G] [Finite G] (A : Set G) (m : ℕ),
    1 ∈ A → A⁻¹ = A → Subgroup.closure A = ⊤ → n₀ ≤ m →
    IsApproximateSubgroup K (A ^ m) →
    ∃ H G₁ : Subgroup G, H.Normal ∧ G₁.Normal ∧ H ≤ G₁ ∧ (H : Set G) ⊆ A ^ (4 * m) ∧
      G₁.index ≤ k ∧ ((⊤ : Subgroup G₁).lowerCentralSeries s).map G₁.subtype ≤ H

/-- Relaxed form of `BreuillardGreenTao` in which the containment `H ⊆ A^(4m)` is weakened to
`H ⊆ A^(radius·m)` for some `radius` depending only on `K`.  This is all that the graph argument
needs: only the final threshold `n₀(ε)` depends on `radius`. -/
def BGTBoundedPower : Prop :=
  ∀ K : ℝ, 1 ≤ K → ∃ n₀ k s radius : ℕ, ∀ (G : Type) [Group G] [Finite G] (A : Set G) (m : ℕ),
    1 ∈ A → A⁻¹ = A → Subgroup.closure A = ⊤ → n₀ ≤ m →
    IsApproximateSubgroup K (A ^ m) →
    ∃ H G₁ : Subgroup G, H.Normal ∧ G₁.Normal ∧ H ≤ G₁ ∧ (H : Set G) ⊆ A ^ (radius * m) ∧
      G₁.index ≤ k ∧ ((⊤ : Subgroup G₁).lowerCentralSeries s).map G₁.subtype ≤ H

/-- `BreuillardGreenTao` is the special case `radius = 4` of `BGTBoundedPower`. -/
theorem bgtBoundedPower_of_BGT (hB : BreuillardGreenTao) : BGTBoundedPower := by
  intro K hK
  obtain ⟨n₀, k, s, h⟩ := hB K hK
  exact ⟨n₀, k, s, 4, h⟩

/-- The lower central series commutes with surjective homomorphisms. -/
lemma lowerCentralSeries_map_of_surjective {G Q : Type*} [Group G] [Group Q] (f : G →* Q)
    (hf : Function.Surjective f) (n : ℕ) :
    ((⊤ : Subgroup G).lowerCentralSeries n).map f =
      (⊤ : Subgroup Q).lowerCentralSeries n := by
  rw [Subgroup.map_lowerCentralSeries, Subgroup.map_top_of_surjective f hf]

/-- Pigeonhole over scales (Lemma 8.1 of Tessera–Tointon): a sequence bounded by `n`, starting
at least `1`, cannot grow by a factor more than `K` at each of `J` steps if `n < K^J`. -/
lemma exists_small_step (f : ℕ → ℕ) (n J : ℕ) (K : ℝ) (hK : 1 ≤ K) (h0 : 1 ≤ f 0)
    (hn : ∀ j, f j ≤ n) (hJ : (n : ℝ) < K ^ J) : ∃ j < J, (f (j + 1) : ℝ) ≤ K * f j := by
  by_contra! hc
  have key : ∀ j ≤ J, K ^ j ≤ (f j : ℝ) := by
    intro j hj
    induction j with
    | zero => simpa using h0
    | succ d hd =>
      have := hc d (by omega)
      have h1 := hd (by omega)
      rw [pow_succ]
      nlinarith
  have := key J le_rfl
  have := hn J
  have : (f J : ℝ) ≤ n := by exact_mod_cast hn J
  linarith

variable {H : Type*} [Group H]

/-- A word in `{1} ∪ S ∪ S⁻¹` of length `r` moves a vertex of `cay S` by distance at most `r`. -/
lemma cay_dist_le_of_mem_pow [Finite H] (S : Set H) (h : (cay S).Connected) :
    ∀ (r : ℕ) (x g : H), g ∈ (insert 1 (S ∪ S⁻¹) : Set H) ^ r → (cay S).dist x (x * g) ≤ r := by
  intro r
  induction r with
  | zero =>
    intro x g hg
    simp only [pow_zero, Set.mem_one] at hg
    simp [hg]
  | succ r ih =>
    intro x g hg
    rw [pow_succ] at hg
    obtain ⟨a, ha, t, ht, rfl⟩ := Set.mem_mul.1 hg
    have h1 := ih x a ha
    have h2 : (cay S).dist (x * a) (x * a * t) ≤ 1 := by
      by_cases ht1 : t = 1
      · simp [ht1]
      · have hadj : (cay S).Adj (x * a) (x * a * t) := by
          rw [cay_adj]
          refine ⟨fun h => ht1 ?_, ?_⟩
          · simpa using h.symm
          · simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_inv] at ht
            rcases ht with h | h | h
            · exact absurd h ht1
            · left; simpa [mul_assoc] using h
            · right; simpa [mul_assoc] using h
        rw [SimpleGraph.dist_eq_one_iff_adj.2 hadj]
    calc (cay S).dist x (x * (a * t)) ≤ (cay S).dist x (x * a) + (cay S).dist (x * a) (x * a * t) :=
          by rw [← mul_assoc]; exact h.dist_triangle
      _ ≤ r + 1 := by omega

/-- The numerical bookkeeping: the radius `c m₀ 3^i` is at most `n^λ`. -/
lemma tt_numeric (lam : ℝ) (hlam : 0 < lam) (c p m₀ n i : ℕ) (hp : 2 / lam ≤ p) (hpos : 0 < p)
    (hi : (3 ^ p) ^ i ≤ n) (hn : (c * m₀ : ℝ) ^ (2 / lam) ≤ n) :
    (c * (m₀ * 3 ^ i : ℕ) : ℝ) ≤ (n : ℝ) ^ lam := by
  have hn1 : (1 : ℝ) ≤ n := by
    have : 1 ≤ (3 ^ p) ^ i := Nat.one_le_pow _ _ (by positivity)
    exact_mod_cast this.trans hi
  have hp' : (0 : ℝ) < p := by exact_mod_cast hpos
  have h3 : ((3 : ℝ) ^ i) ≤ (n : ℝ) ^ ((1 : ℝ) / p) := by
    have hx : ((3 : ℝ) ^ i) ^ p ≤ n := by
      rw [← pow_mul, mul_comm, pow_mul]; exact_mod_cast hi
    calc ((3 : ℝ) ^ i) = (((3 : ℝ) ^ i) ^ p) ^ ((1 : ℝ) / p) := by
          rw [one_div, Real.pow_rpow_inv_natCast (by positivity) hpos.ne']
      _ ≤ (n : ℝ) ^ ((1 : ℝ) / p) := Real.rpow_le_rpow (by positivity) hx (by positivity)
  have h4 : (n : ℝ) ^ ((1 : ℝ) / p) ≤ (n : ℝ) ^ (lam / 2) := by
    apply Real.rpow_le_rpow_of_exponent_le hn1
    rw [div_le_div_iff₀ hp' (by norm_num)]
    rw [div_le_iff₀ hlam] at hp
    linarith
  have h5 : (c * m₀ : ℝ) ≤ (n : ℝ) ^ (lam / 2) := by
    calc (c * m₀ : ℝ) = ((c * m₀ : ℝ) ^ (2 / lam)) ^ (lam / 2) := by
          rw [← Real.rpow_mul (by positivity)]
          field_simp
          simp
      _ ≤ (n : ℝ) ^ (lam / 2) := Real.rpow_le_rpow (by positivity) hn (by positivity)
  have h6 : (n : ℝ) ^ lam = (n : ℝ) ^ (lam / 2) * (n : ℝ) ^ (lam / 2) := by
    rw [← Real.rpow_add (by linarith)]; ring_nf
  push_cast
  rw [h6]
  have : (0 : ℝ) ≤ m₀ := by positivity
  calc (c : ℝ) * ((m₀ : ℝ) * 3 ^ i) = (c * m₀) * 3 ^ i := by ring
    _ ≤ (n : ℝ) ^ (lam / 2) * (n : ℝ) ^ (lam / 2) := by
      apply mul_le_mul h5 (h3.trans h4) (by positivity) (by positivity)

/-- **Theorem 3.16** (Tessera–Tointon, Cayley form), derived from the relaxed
Breuillard–Green–Tao statement `BGTBoundedPower` (arbitrary bounded radius). -/
theorem tesseraTointon_cayley_of_boundedPower (hB : BGTBoundedPower) :
    ∀ lam : ℝ, 0 < lam → lam < 1 → ∃ c k n₀ : ℕ, ∀ (H : Type) [Group H] [Finite H] (S : Set H),
      (cay S).Connected → n₀ ≤ Nat.card H →
      ∃ N : Subgroup H, ∃ _ : N.Normal,
        (∀ x y : H, (x : H ⧸ N) = y → ((cay S).dist x y : ℝ) ≤ (Nat.card H : ℝ) ^ lam) ∧
        ∃ K : Subgroup (H ⧸ N), K.Normal ∧
          (⊤ : Subgroup K).lowerCentralSeries c = ⊥ ∧ K.index ≤ k := by
  intro lam hlam _
  classical
  set p : ℕ := ⌈2 / lam⌉₊ with hpdef
  have hp : 2 / lam ≤ p := Nat.le_ceil _
  have hpos : 0 < p := by
    have : (0 : ℝ) < 2 / lam := by positivity
    exact_mod_cast this.trans_le hp
  set K : ℝ := (3 : ℝ) ^ p with hKdef
  have hK1 : 1 ≤ K := one_le_pow₀ (by norm_num)
  obtain ⟨n₀, k, s, r, hBGT⟩ := hB (K ^ 3) (one_le_pow₀ hK1)
  set m₀ := n₀ + 1 with hm₀def
  refine ⟨s, k, ⌈((2 * r : ℕ) * m₀ : ℝ) ^ (2 / lam)⌉₊, ?_⟩
  intro H _ _ S hconn hn
  haveI := Fintype.ofFinite H
  set n := Nat.card H with hndef
  set T : Finset H := (insert 1 (S ∪ S⁻¹) : Set H).toFinset with hTdef
  have hT : (T : Set H) = insert 1 (S ∪ S⁻¹) := by simp [T]
  have hT1 : (1 : H) ∈ T := by simp [T]
  have hTinv : T⁻¹ = T := by
    rw [← Finset.coe_inj, Finset.coe_inv, hT]
    ext x
    simp only [Set.mem_inv, Set.mem_insert_iff, Set.mem_union, inv_eq_one, inv_inv]
    constructor <;> rintro (h | h | h) <;> simp [h]
  have hb : 1 < 3 ^ p := Nat.one_lt_pow hpos.ne' (by norm_num)
  have hn1 : 1 ≤ n := Nat.card_pos
  obtain ⟨J, hJ1, hJ2⟩ : ∃ J, n + 1 ≤ (3 ^ p) ^ J ∧ (3 ^ p) ^ (J - 1) ≤ n := by
    refine ⟨Nat.clog (3 ^ p) (n + 1), Nat.le_pow_clog hb _, ?_⟩
    have := Nat.pow_pred_clog_lt_self hb (show 1 < n + 1 by omega)
    rw [Nat.pred_eq_sub_one] at this
    omega
  set f : ℕ → ℕ := fun j => (T ^ (m₀ * 3 ^ j)).card with hfdef
  have hf0 : 1 ≤ f 0 := Finset.card_pos.2 ⟨1, Finset.one_mem_pow hT1⟩
  have hfn : ∀ j, f j ≤ n := fun j => by
    rw [hndef, Nat.card_eq_fintype_card]; exact Finset.card_le_univ _
  have hKJ : (n : ℝ) < K ^ J := by
    have : ((n + 1 : ℕ) : ℝ) ≤ ((3 ^ p) ^ J : ℕ) := by exact_mod_cast hJ1
    push_cast at this
    rw [hKdef]; linarith
  obtain ⟨j, hj, hstep⟩ := exists_small_step f n J K hK1 hf0 hfn hKJ
  set m := m₀ * 3 ^ j with hmdef
  have hm1 : 1 ∈ T ^ m := Finset.one_mem_pow hT1
  have hminv : (T ^ m)⁻¹ = T ^ m := by rw [← inv_pow, hTinv]
  have htrip : (((T ^ m) ^ 3).card : ℝ) ≤ K * (T ^ m).card := by
    have e : (T ^ m) ^ 3 = T ^ (m₀ * 3 ^ (j + 1)) := by
      rw [← pow_mul, hmdef, pow_succ, mul_assoc]
    rw [e]; exact hstep
  have happ := IsApproximateSubgroup.of_small_tripling hm1 hminv htrip
  have happ' : IsApproximateSubgroup (K ^ 3) ((T : Set H) ^ (2 * m)) := by
    convert happ using 1
    rw [mul_comm, pow_mul]; norm_cast
  have hcl : Subgroup.closure (T : Set H) = ⊤ := by
    rw [eq_top_iff, ← cay_connected_iff.1 hconn]
    apply Subgroup.closure_mono
    rw [hT]; intro x hx; simp [hx]
  obtain ⟨N, G₁, hN, hG₁, -, hNsub, hidx, hlcs⟩ :=
    hBGT H (T : Set H) (2 * m) (by simpa using hT1) (by rw [← Finset.coe_inv, hTinv]) hcl
      (by have := Nat.one_le_pow j 3 (by norm_num); rw [hmdef, hm₀def]; nlinarith) happ'
  refine ⟨N, hN, ?_, G₁.map (QuotientGroup.mk' N), ?_, ?_, ?_⟩
  · intro x y hxy
    have hmem : x⁻¹ * y ∈ N := QuotientGroup.eq.1 hxy
    have hmem' := hNsub hmem
    rw [hT] at hmem'
    have hd := cay_dist_le_of_mem_pow S hconn _ x _ hmem'
    rw [mul_inv_cancel_left] at hd
    have hnum := tt_numeric lam hlam (2 * r) p m₀ n j hp hpos
      ((Nat.pow_le_pow_right (by omega) (by omega)).trans hJ2)
      ((Nat.le_ceil _).trans (by exact_mod_cast hn))
    calc ((cay S).dist x y : ℝ) ≤ ((r * (2 * m) : ℕ) : ℝ) := by exact_mod_cast hd
      _ = ((2 * r : ℕ) * (m₀ * 3 ^ j : ℕ) : ℝ) := by rw [hmdef]; push_cast; ring
      _ ≤ _ := hnum
  · exact Subgroup.Normal.map hG₁ _ (QuotientGroup.mk'_surjective N)
  · set φ := (QuotientGroup.mk' N).subgroupMap G₁
    rw [← lowerCentralSeries_map_of_surjective φ ((QuotientGroup.mk' N).subgroupMap_surjective G₁),
      Subgroup.map_eq_bot_iff]
    intro g hg
    have : (g : H) ∈ N := hlcs (Subgroup.mem_map_of_mem _ hg)
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    simpa [φ] using this
  · exact (Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite))
      (Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective N))).trans hidx

/-- **Theorem 3.16** (Tessera–Tointon, Cayley form), derived from the Breuillard–Green–Tao
theorem. -/
theorem tesseraTointon_cayley_of_BGT (hB : BreuillardGreenTao) :
    ∀ lam : ℝ, 0 < lam → lam < 1 → ∃ c k n₀ : ℕ, ∀ (H : Type) [Group H] [Finite H] (S : Set H),
      (cay S).Connected → n₀ ≤ Nat.card H →
      ∃ N : Subgroup H, ∃ _ : N.Normal,
        (∀ x y : H, (x : H ⧸ N) = y → ((cay S).dist x y : ℝ) ≤ (Nat.card H : ℝ) ^ lam) ∧
        ∃ K : Subgroup (H ⧸ N), K.Normal ∧
          (⊤ : Subgroup K).lowerCentralSeries c = ⊥ ∧ K.index ≤ k :=
  tesseraTointon_cayley_of_boundedPower (bgtBoundedPower_of_BGT hB)

end Lovasz
