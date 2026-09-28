module
public import RequestProject.VTMain
public import RequestProject.TTCayley
public import RequestProject.TTNormalClosure

/-!
# Lemma A.2 (semiregular structural quotient), from Breuillard–Green–Tao and Tointon

For a finite connected vertex-transitive graph `X` with automorphism group `G = Aut(X)` (a finite
group), the argument of Tessera–Tointon (Theorem 7.1, Theorem 2.3, Corollary 2.4) together with the
semiregularity observation of the paper's Lemma A.2 runs as follows, all proved here:

* `S = {g ∈ G : d(e, g e) ≤ 1}` is a symmetric generating set containing `1`, and
  `S^r ⊆ {g : d(e, g e) ≤ r}` (Lemmas 3.4 and 3.8);
* a pigeonhole over scales (Lemma 8.1) gives `m` with `|S^(3m)| ≤ K |S^m|`, using
  `|G| = |G_e| n` and `G_e ⊆ S`; Ruzsa's argument makes `S^(2m)` a `K³`-approximate group;
* Breuillard–Green–Tao gives `H₁ ≤ N₁` normal in `G` with `H₁ ⊆ S^(8m)`, `[G : N₁]` bounded and
  `N₁/H₁` nilpotent of bounded class;
* Proposition 6.5 (from Tointon's lemma) bounds the normal closure of `G_e ∩ N₁` modulo `H₁`;
* `N = H₁ (G_e ∩ N₁)^G` has orbits of diameter `O(m) ≤ n^λ`, and `M = N₁` acts semiregularly on
  the `N`-orbits.

For finite graphs, the locally compact group machinery of Tessera–Tointon (Carolino's theorem,
Haar measure, topology on `Aut(X)`) is not needed: `Aut(X)` is finite and discrete.
-/

@[expose] public section


open scoped Pointwise

namespace Lovasz

/-- Pigeonhole over scales, in the form used for vertex-transitive graphs: a sequence with
`a ≤ f 0` and `f j ≤ a n` cannot grow by a factor more than `K` at each of `J` steps if
`n < K^J`. -/
lemma exists_small_step' (f : ℕ → ℕ) (a n J : ℕ) (K : ℝ) (hK : 1 ≤ K) (ha : 0 < a)
    (h0 : a ≤ f 0) (hn : ∀ j, f j ≤ a * n) (hJ : (n : ℝ) < K ^ J) :
    ∃ j < J, (f (j + 1) : ℝ) ≤ K * f j := by
  by_contra! hc
  have key : ∀ j ≤ J, K ^ j * a ≤ (f j : ℝ) := by
    intro j hj
    induction j with
    | zero => simpa using h0
    | succ d hd =>
      have := hc d (by omega)
      have h1 := hd (by omega)
      rw [pow_succ]
      have : 0 ≤ K ^ d * a := by positivity
      nlinarith
  have h1 := key J le_rfl
  have h2 : (f J : ℝ) ≤ a * n := by exact_mod_cast hn J
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  nlinarith

section VT

variable {V : Type} {X : SimpleGraph V}

/-- Automorphisms do not increase distances. -/
lemma aut_dist_le (hX : X.Connected) (g : X ≃g X) (u v : V) :
    X.dist (g u) (g v) ≤ X.dist u v := by
  obtain ⟨p, hp⟩ := hX.exists_walk_length_eq_dist u v
  calc X.dist (g u) (g v) ≤ (p.map g.toHom).length := SimpleGraph.dist_le _
    _ = X.dist u v := by rw [SimpleGraph.Walk.length_map, hp]

/-- Automorphisms preserve distances. -/
lemma aut_dist (hX : X.Connected) (g : X ≃g X) (u v : V) : X.dist (g u) (g v) = X.dist u v := by
  apply le_antisymm (aut_dist_le hX g u v)
  have := aut_dist_le hX g⁻¹ (g u) (g v)
  simpa using this

/-- `S^r ⊆ {g : d(e, g e) ≤ r}` for `S = {g : d(e, g e) ≤ 1}` (one half of Lemma 3.4 of
Tessera–Tointon). -/
lemma dist_le_of_mem_pow (hX : X.Connected) (e : V) :
    ∀ (r : ℕ) (g : X ≃g X), g ∈ {g : X ≃g X | X.dist e (g e) ≤ 1} ^ r → X.dist e (g e) ≤ r := by
  intro r
  induction r with
  | zero =>
    intro g hg
    simp only [pow_zero, Set.mem_one] at hg
    simp [hg]
  | succ r ih =>
    intro g hg
    rw [pow_succ] at hg
    obtain ⟨a, ha, t, ht, rfl⟩ := hg
    have h1 := ih a ha
    have h2 : X.dist (a e) (a (t e)) ≤ 1 := by rw [aut_dist hX]; exact ht
    calc X.dist e ((a * t) e) ≤ X.dist e (a e) + X.dist (a e) (a (t e)) := by
          rw [RelIso.mul_apply]; exact hX.dist_triangle
      _ ≤ r + 1 := by omega

/-- A walk of length `ℓ` from `g e` to `h e` gives `g⁻¹ h ∈ S^(ℓ+1)` (the other half of
Lemma 3.4 of Tessera–Tointon). -/
lemma mem_pow_of_walk (hX : X.Connected) (hvt : VertexTransitive X) (e : V) {u v : V}
    (p : X.Walk u v) : ∀ g h : X ≃g X, g e = u → h e = v →
      g⁻¹ * h ∈ {g : X ≃g X | X.dist e (g e) ≤ 1} ^ (p.length + 1) := by
  induction p with
  | nil =>
    intro g h hg hh
    simp only [SimpleGraph.Walk.length_nil, zero_add, pow_one, Set.mem_setOf_eq,
      RelIso.mul_apply]
    rw [hh, ← hg]
    simp
  | @cons u w v hadj p' ih =>
    intro g h hg hh
    obtain ⟨f, hf⟩ := hvt e w
    have h1 : g⁻¹ * f ∈ {g : X ≃g X | X.dist e (g e) ≤ 1} := by
      show X.dist e ((g⁻¹ * f) e) ≤ 1
      rw [← aut_dist hX g]
      simp only [RelIso.mul_apply, RelIso.apply_inv_self]
      rw [hg, hf, SimpleGraph.dist_eq_one_iff_adj.2 hadj]
    have h2 := ih f h hf hh
    have e1 : g⁻¹ * h = (g⁻¹ * f) * (f⁻¹ * h) := by group
    rw [e1, SimpleGraph.Walk.length_cons, pow_succ' _ (p'.length + 1)]
    exact Set.mul_mem_mul h1 h2

end VT

/-- **Lemma A.2** (semiregular structural quotient) of the paper, derived from the relaxed
Breuillard–Green–Tao statement `BGTBoundedPower` (arbitrary bounded radius) and Tointon's lemma,
following Tessera–Tointon. -/
theorem tesseraTointonVT_of_boundedPower (hB : BGTBoundedPower) (hT : TointonNormalClosure) :
    TesseraTointonVT := by
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
  obtain ⟨D, hD⟩ := normalClosure_subset_pow hT (K ^ 3) s k (one_le_pow₀ hK1)
  set m₀ := n₀ + 1 with hm₀def
  set c : ℕ := 2 * D + 4 * r with hcdef
  refine ⟨k, ⌈(c * m₀ : ℝ) ^ (2 / lam)⌉₊, ?_⟩
  intro V _ X hX hvt hn
  set n := Fintype.card V with hndef
  haveI : Finite (X ≃g X) := finite_aut X
  haveI : Fintype (X ≃g X) := Fintype.ofFinite _
  obtain ⟨e⟩ := hX.nonempty
  set S : Set (X ≃g X) := {g | X.dist e (g e) ≤ 1} with hSdef
  have hS1 : (1 : X ≃g X) ∈ S := by simp [S]
  have hSinv : S⁻¹ = S := by
    ext g
    simp only [Set.mem_inv, S, Set.mem_setOf_eq]
    rw [← aut_dist hX g, SimpleGraph.dist_comm]
    simp
  have hScl : Subgroup.closure S = ⊤ := by
    have hsub : ∀ r : ℕ, S ^ r ⊆ Subgroup.closure S := by
      intro r
      induction r with
      | zero => simp [Set.subset_def]
      | succ r ih =>
        rw [pow_succ]
        rintro _ ⟨a, ha, b, hb, rfl⟩
        exact Subgroup.mul_mem _ (ih ha) (Subgroup.subset_closure hb)
    rw [eq_top_iff]
    intro g _
    obtain ⟨q⟩ := hX.preconnected e (g e)
    have := mem_pow_of_walk hX hvt e q 1 g (by simp) rfl
    simpa using hsub _ this
  set stab := MulAction.stabilizer (X ≃g X) e with hstabdef
  have hstabS : (stab : Set (X ≃g X)) ⊆ S := by
    intro g hg
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff] at hg
    show X.dist e (g e) ≤ 1
    have : g e = e := hg
    simp [this]
  have hcardG : Nat.card (X ≃g X) = Nat.card stab * n := by
    rw [← Subgroup.card_mul_index stab, MulAction.index_stabilizer]
    congr 1
    have horb : MulAction.orbit (X ≃g X) e = Set.univ := by
      ext v
      simp only [Set.mem_univ, iff_true]
      obtain ⟨g, hg⟩ := hvt e v
      exact ⟨g, hg⟩
    rw [horb, Set.ncard_univ, Nat.card_eq_fintype_card]
  set T : Finset (X ≃g X) := S.toFinset with hTdef
  have hT : (T : Set (X ≃g X)) = S := Set.coe_toFinset S
  have hT1 : (1 : X ≃g X) ∈ T := by simpa [T] using hS1
  have hTinv : T⁻¹ = T := by rw [← Finset.coe_inj, Finset.coe_inv, hT, hSinv]
  have hb : 1 < 3 ^ p := Nat.one_lt_pow hpos.ne' (by norm_num)
  have hn1 : 1 ≤ n := Fintype.card_pos_iff.2 ⟨e⟩
  obtain ⟨J, hJ1, hJ2⟩ : ∃ J, n + 1 ≤ (3 ^ p) ^ J ∧ (3 ^ p) ^ (J - 1) ≤ n := by
    refine ⟨Nat.clog (3 ^ p) (n + 1), Nat.le_pow_clog hb _, ?_⟩
    have := Nat.pow_pred_clog_lt_self hb (show 1 < n + 1 by omega)
    rw [Nat.pred_eq_sub_one] at this
    omega
  set f : ℕ → ℕ := fun j => (T ^ (m₀ * 3 ^ j)).card with hfdef
  have hstab_pos : 0 < Nat.card stab := Nat.card_pos
  have hf0 : Nat.card stab ≤ f 0 := by
    have hc : Nat.card stab = (stab : Set (X ≃g X)).toFinset.card := by
      rw [← Nat.card_eq_card_toFinset]; rfl
    rw [hc]
    apply Finset.card_le_card
    intro g hg
    rw [Set.mem_toFinset] at hg
    have hgS : g ∈ S := hstabS hg
    have : g ∈ (T : Set (X ≃g X)) ^ (m₀ * 3 ^ 0) := by
      apply Set.pow_subset_pow_right (by simpa using hT1) (show 1 ≤ m₀ * 3 ^ 0 by simp [m₀])
      rw [pow_one, hT]; exact hgS
    rw [← Finset.coe_pow] at this
    exact this
  have hfn : ∀ j, f j ≤ Nat.card stab * n := fun j => by
    rw [← hcardG, Nat.card_eq_fintype_card]; exact Finset.card_le_univ _
  have hKJ : (n : ℝ) < K ^ J := by
    have : ((n + 1 : ℕ) : ℝ) ≤ ((3 ^ p) ^ J : ℕ) := by exact_mod_cast hJ1
    push_cast at this
    rw [hKdef]; linarith
  obtain ⟨j, hj, hstep⟩ := exists_small_step' f (Nat.card stab) n J K hK1 hstab_pos hf0 hfn hKJ
  set m := m₀ * 3 ^ j with hmdef
  have hm1 : 1 ∈ T ^ m := Finset.one_mem_pow hT1
  have hminv : (T ^ m)⁻¹ = T ^ m := by rw [← inv_pow, hTinv]
  have htrip : (((T ^ m) ^ 3).card : ℝ) ≤ K * (T ^ m).card := by
    have e3 : (T ^ m) ^ 3 = T ^ (m₀ * 3 ^ (j + 1)) := by
      rw [← pow_mul, hmdef, pow_succ, mul_assoc]
    rw [e3]; exact hstep
  have happ := IsApproximateSubgroup.of_small_tripling hm1 hminv htrip
  have happ' : IsApproximateSubgroup (K ^ 3) (S ^ (2 * m)) := by
    rw [← hT]
    convert happ using 1
    rw [mul_comm, pow_mul]; norm_cast
  obtain ⟨H1, N1, hH1, hN1, hH1N1, hH1sub, hidx, hlcs⟩ :=
    hBGT (X ≃g X) S (2 * m) hS1 hSinv hScl
      (by have := Nat.one_le_pow j 3 (by norm_num); rw [hmdef, hm₀def]; nlinarith) happ'
  set π := QuotientGroup.mk' H1 with hπdef
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective H1
  set Ge : Subgroup (X ≃g X) := stab ⊓ N1 with hGedef
  have hS2m : S ⊆ S ^ (2 * m) := by
    have := Set.pow_subset_pow_right (s := S) hS1 (show 1 ≤ 2 * m by
      have := Nat.one_le_pow j 3 (by norm_num); rw [hmdef, hm₀def]; nlinarith)
    rwa [pow_one] at this
  have hNC := hD ((X ≃g X) ⧸ H1) (π '' (S ^ (2 * m))) (N1.map π) (Ge.map π) (happ'.image π)
    (by
      rw [← MonoidHom.map_closure, eq_top_iff, ← Subgroup.map_top_of_surjective π hsurj]
      apply Subgroup.map_mono
      rw [← hScl]
      exact Subgroup.closure_mono hS2m)
    (hN1.map _ hsurj)
    ((Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_map_dvd _ hsurj)).trans hidx)
    (by
      rw [← lowerCentralSeries_map_of_surjective (π.subgroupMap N1)
        (π.subgroupMap_surjective N1), Subgroup.map_eq_bot_iff]
      intro g hg
      have : (g : X ≃g X) ∈ H1 := hlcs (Subgroup.mem_map_of_mem _ hg)
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      simpa [π] using this)
    (by
      rintro _ ⟨g, hg, rfl⟩
      exact ⟨g, hS2m (hstabS hg.1), rfl⟩)
    (Subgroup.map_mono inf_le_right)
  set NC := Subgroup.normalClosure (Ge : Set (X ≃g X)) with hNCdef
  have hNCsub : (NC : Set (X ≃g X)) ⊆ S ^ (2 * m * D + r * (2 * m)) := by
    intro x hx
    have hx' : π x ∈ Subgroup.normalClosure (π '' (Ge : Set (X ≃g X))) := by
      rw [← Subgroup.map_normalClosure _ _ hsurj]; exact Subgroup.mem_map_of_mem π hx
    have h1 := hNC (by simpa [Subgroup.coe_map] using hx')
    rw [← Set.image_pow] at h1
    obtain ⟨y, hy, hyx⟩ := h1
    have hyx' : y⁻¹ * x ∈ H1 := QuotientGroup.eq.1 hyx
    rw [pow_add, pow_mul]
    exact ⟨y, hy, y⁻¹ * x, hH1sub hyx', by group⟩
  set N : Subgroup (X ≃g X) := H1 ⊔ NC with hNdef
  have hNsub : (N : Set (X ≃g X)) ⊆ S ^ (c * m) := by
    rw [hNdef, Subgroup.normal_mul]
    rintro _ ⟨a, ha, b, hb, rfl⟩
    have e1 : c * m = r * (2 * m) + (2 * m * D + r * (2 * m)) := by rw [hcdef]; ring
    rw [e1, pow_add]
    exact Set.mul_mem_mul (hH1sub ha) (hNCsub hb)
  have hNCnormal : NC.Normal := Subgroup.normalClosure_normal
  have hNnormal : N.Normal := Subgroup.sup_normal H1 NC
  have hNN1 : N ≤ N1 :=
    sup_le hH1N1 (Subgroup.normalClosure_le_normal (fun x hx => hx.2))
  refine ⟨N, hNnormal, ?_, N1, hN1, hidx, ?_⟩
  · rintro u v ⟨g, hg, rfl⟩
    obtain ⟨h, rfl⟩ := hvt e u
    have hconj : h⁻¹ * g * h ∈ N := by
      have := hNnormal.conj_mem g hg h⁻¹; simpa using this
    have hd := dist_le_of_mem_pow hX e _ _ (hNsub hconj)
    have e2 : X.dist (h e) (g (h e)) = X.dist e ((h⁻¹ * g * h) e) := by
      rw [← aut_dist hX h⁻¹]; simp
    rw [e2]
    have hnum := tt_numeric lam hlam c p m₀ n j hp hpos
      ((Nat.pow_le_pow_right (by omega) (by omega)).trans hJ2)
      ((Nat.le_ceil _).trans (by exact_mod_cast hn))
    calc (X.dist e ((h⁻¹ * g * h) e) : ℝ) ≤ ((c * m : ℕ) : ℝ) := by exact_mod_cast hd
      _ = (c * (m₀ * 3 ^ j : ℕ) : ℝ) := by rw [hmdef]; push_cast; ring
      _ ≤ _ := hnum
  · rintro a ha x ⟨g, hg, hax⟩ y
    refine ⟨a, ?_, rfl⟩
    obtain ⟨h, rfl⟩ := hvt e x
    have hmem : h⁻¹ * (g⁻¹ * a) * h ∈ Ge := by
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · rw [MulAction.mem_stabilizer_iff]
        show (h⁻¹ * (g⁻¹ * a) * h) e = e
        simp only [RelIso.mul_apply]
        rw [hax]; simp
      · have := hN1.conj_mem _ (N1.mul_mem (N1.inv_mem (hNN1 hg)) ha) h⁻¹
        simpa using this
    have hNC' : g⁻¹ * a ∈ NC := by
      have := hNCnormal.conj_mem _ (Subgroup.subset_normalClosure hmem) h
      simpa [mul_assoc] using this
    have e3 : a = g * (g⁻¹ * a) := by group
    rw [e3]
    exact N.mul_mem hg (Subgroup.mem_sup_right hNC')

/-- **Lemma A.2** (semiregular structural quotient) of the paper, derived from the
Breuillard–Green–Tao theorem and Tointon's lemma, following Tessera–Tointon. -/
theorem tesseraTointonVT_of_BGT (hB : BreuillardGreenTao) (hT : TointonNormalClosure) :
    TesseraTointonVT :=
  tesseraTointonVT_of_boundedPower (bgtBoundedPower_of_BGT hB) hT

end Lovasz
