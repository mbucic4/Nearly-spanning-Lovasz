module
public import RequestProject.VTCorridor
public import RequestProject.VTContract
public import RequestProject.Final

/-!
# Near-linear paths in vertex-transitive graphs (Theorem A.1)

The appendix of the paper extends the Cayley bound (Theorem 3.17) to all connected
vertex-transitive graphs.  The only additional result imported from the literature is
Lemma A.2, the semiregular structural quotient obtained from the construction behind
Corollary 2.4 of Tessera–Tointon; it is stated here as the hypothesis `TesseraTointonVT`
(specialised to the full automorphism group `G = Aut(X)`, which is all the proof uses).
-/

@[expose] public section


open Classical

namespace Lovasz

/-- A graph is vertex-transitive if its automorphism group acts transitively on vertices. -/
def VertexTransitive {V : Type*} (X : SimpleGraph V) : Prop := ∀ u v : V, ∃ φ : X ≃g X, φ u = v

/-- **Lemma A.2** (semiregular structural quotient), for `G = Aut(X)`.  For every
`0 < λ < 1` there are integers `k, n₀` such that for every connected vertex-transitive graph
`X` of order `n ≥ n₀` there is `N ◁ Aut(X)` such that
(i) any two vertices in the same `N`-orbit are at distance at most `n^λ` in `X`, and
(ii) there is `M ◁ Aut(X)` of index at most `k` whose image in the group induced on `X/N` is
semiregular: if `a ∈ M` fixes one `N`-orbit, then it fixes every `N`-orbit.
(The image of `M` is the normal semiregular subgroup `K` of bounded index in the paper's
formulation; conversely, the preimage of such a `K` is such an `M`.) -/
def TesseraTointonVT : Prop :=
  ∀ lam : ℝ, 0 < lam → lam < 1 → ∃ k n₀ : ℕ, ∀ (V : Type) [Fintype V] (X : SimpleGraph V),
    X.Connected → VertexTransitive X → n₀ ≤ Fintype.card V →
    ∃ N : Subgroup (X ≃g X), N.Normal ∧
      (∀ u v : V, (∃ g ∈ N, g u = v) → (X.dist u v : ℝ) ≤ (Fintype.card V : ℝ) ^ lam) ∧
      ∃ M : Subgroup (X ≃g X), M.Normal ∧ M.index ≤ k ∧
        ∀ a ∈ M, ∀ x : V, (∃ g ∈ N, a x = g x) → ∀ y : V, ∃ g ∈ N, a y = g y

section Aux

variable {V Γ : Type*} [Group Γ] [MulAction Γ V]

lemma card_eq_card_fib_mul [Fintype V] [Fintype Γ] (N : Subgroup Γ) [Fintype (Fib N V)] {m : ℕ}
    (hm : ∀ v : V, (orb N v).card = m) : Fintype.card V = Fintype.card (Fib N V) * m := by
  rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := fib N) (t := Finset.univ)
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))]
  rw [Finset.sum_congr rfl (g := fun _ => m), Finset.sum_const, smul_eq_mul, Finset.card_univ]
  intro q _
  obtain ⟨v, rfl⟩ := fib_surjective N q
  rw [← hm v]; congr 1; ext w; simp [mem_orb]

lemma quotGraph_reachable {X : SimpleGraph V} (N : Subgroup Γ) {u v : V} (h : X.Reachable u v) :
    (quotGraph X N).Reachable (fib N u) (fib N v) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => rfl
  | @tail b c _ hbc ih =>
    refine ih.trans ?_
    by_cases he : fib N b = fib N c
    · rw [he]
    · exact (quotGraph_adj_of_adj hbc he).reachable

lemma quotGraph_connected {X : SimpleGraph V} (N : Subgroup Γ) (h : X.Connected) :
    (quotGraph X N).Connected := by
  rw [SimpleGraph.connected_iff]
  refine ⟨fun p q => ?_, ?_⟩
  · obtain ⟨u, rfl⟩ := fib_surjective N p
    obtain ⟨v, rfl⟩ := fib_surjective N q
    exact quotGraph_reachable N (h.preconnected u v)
  · obtain ⟨v⟩ := h.nonempty
    exact ⟨fib N v⟩

end Aux

lemma finite_aut {V : Type*} [Finite V] (X : SimpleGraph V) : Finite (X ≃g X) :=
  Finite.of_injective (fun g : X ≃g X => g.toEquiv) RelIso.toEquiv_injective

lemma actsOn_aut {V : Type*} (X : SimpleGraph V) : ActsOn X (X ≃g X) :=
  fun g _ _ h => g.map_adj_iff.2 h

/-- **Theorem A.1.** For every `ε > 0` there is `n₀` such that every connected
vertex-transitive graph on `n ≥ n₀` vertices contains a path with at least `n^(1-ε)` edges
(in particular on at least `n^(1-ε)` vertices).  The hypotheses are Theorem 1.2, the Cayley
form of the Tessera–Tointon theorem (Theorem 3.16) and Lemma A.2. -/
theorem vt_long_path (h12 : CycleMatchingTheorem) (hTT : TesseraTointonCayley)
    (hTTvt : TesseraTointonVT) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (X : SimpleGraph V),
      X.Connected → VertexTransitive X → n₀ ≤ Fintype.card V →
      ∃ l : List V, IsPathL X l ∧ (Fintype.card V : ℝ) ^ (1 - ε) ≤ (l.length : ℝ) - 1 := by
  suffices key : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V]
      (X : SimpleGraph V), X.Connected → VertexTransitive X → n₀ ≤ Fintype.card V →
      ∃ l : List V, IsPathL X l ∧ (Fintype.card V : ℝ) ^ (1 - ε) ≤ (l.length : ℝ) - 1 by
    intro ε hε
    by_cases h1 : ε ≤ 1
    · exact key ε hε h1
    · obtain ⟨n₀, hn₀⟩ := key 1 one_pos le_rfl
      refine ⟨max n₀ 1, fun V _ X hX hvt hn => ?_⟩
      obtain ⟨l, hl, hlen⟩ := hn₀ V X hX hvt (le_of_max_le_left hn)
      refine ⟨l, hl, le_trans ?_ hlen⟩
      have : (1:ℝ) ≤ Fintype.card V := by exact_mod_cast (le_of_max_le_right hn)
      exact Real.rpow_le_rpow_of_exponent_le this (by linarith)
  intro ε hε hε1
  obtain ⟨cη, hcη, hlift⟩ := fibre_lifting_vt h12 (ε / 4) (by positivity) (by linarith)
  obtain ⟨k, n1, hTT'⟩ := hTTvt (ε / 16) (by positivity) (by linarith)
  obtain ⟨b, hb, hsemi⟩ := semiregular_path_bound (cayley_long_path h12 hTT) (ε / 4)
    (by positivity) (by linarith) (max k 1) (le_max_right _ _)
  obtain ⟨n2, hn2⟩ := eventually_bound (min b (cη * b)) (2 * 0 + 4) ε (by positivity) hε hε1
  refine ⟨max (max n1 n2) 2, fun V _ X hS hvt hn => ?_⟩
  obtain ⟨l, hl, hlen⟩ := exists_isPathL_length_eq_pathOrder X
  refine ⟨l, hl, ?_⟩
  rw [hlen]
  suffices hP : (Fintype.card V : ℝ) ^ (1 - ε) + 1 ≤ pathOrder X by linarith
  refine le_trans (hn2 _ (le_trans (le_max_right _ _) (le_of_max_le_left hn))) ?_
  have hn2' : 2 ≤ Fintype.card V := le_of_max_le_right hn
  have hnR : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn2'
  obtain ⟨N, hN, hdiam, M, hM, hMk, hMsemi⟩ :=
    hTT' V X hS hvt (le_trans (le_max_left _ _) (le_of_max_le_left hn))
  -- the transitive action of `Γ = Aut(X)`
  haveI := finite_aut X
  letI : Fintype (X ≃g X) := Fintype.ofFinite _
  have hX := actsOn_aut X
  have hT : TransOn (X ≃g X) V := hvt
  obtain ⟨x0⟩ : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  set m := (orb N x0).card with hmdef
  have hm : ∀ v : V, (orb N v).card = m := fun v => card_orb_eq N hT v x0
  letI : Fintype (Fib N V) := Fintype.ofFinite _
  set Y := quotGraph X N with hYdef
  have hnmq : Fintype.card V = Fintype.card (Fib N V) * m := card_eq_card_fib_mul N hm
  -- the semiregular group induced by `M` on `Y`
  let ρ := MulAction.toPermHom (X ≃g X) (Fib N V)
  let K : Subgroup (Equiv.Perm (Fib N V)) := M.map ρ
  have hKsmul : ∀ (g : K) (y : Fib N V), g • y = (g : Equiv.Perm (Fib N V)) y := fun _ _ => rfl
  have hYK : ActsOn Y K := by
    rintro ⟨g, hg⟩ p q hpq
    obtain ⟨a, -, rfl⟩ := Subgroup.mem_map.1 hg
    exact (hX.quot N) a p q hpq
  have hfree : FreeAct K (Fib N V) := by
    rintro ⟨g, hg⟩ y hy
    obtain ⟨a, haM, rfl⟩ := Subgroup.mem_map.1 hg
    obtain ⟨x, rfl⟩ := fib_surjective N y
    have hy' : fib N (a • x) = fib N x := hy
    obtain ⟨g0, hg0N, hg0⟩ := fib_eq_iff.1 hy'
    have hall := hMsemi a haM x ⟨g0, hg0N, hg0.symm⟩
    apply Subtype.ext
    ext z
    obtain ⟨w, rfl⟩ := fib_surjective N z
    obtain ⟨g1, hg1N, hg1⟩ := hall w
    show fib N (a • w) = fib N w
    exact fib_eq_iff.2 ⟨g1, hg1N, hg1.symm⟩
  letI : Fintype K := Fintype.ofFinite _
  haveI : Finite ((X ≃g X) ⧸ M) := inferInstance
  letI : Fintype ((X ≃g X) ⧸ M) := Fintype.ofFinite _
  set F : Finset (Fib N V) :=
    Finset.univ.image (fun c : (X ≃g X) ⧸ M => (Quotient.out c) • fib N x0) with hF
  have hFk : F.card ≤ max k 1 := by
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]
    exact hMk.trans (le_max_left _ _)
  have hFcov : ∀ y : Fib N V, ∃ f ∈ F, ∃ g : K, g • f = y := by
    intro y
    obtain ⟨v, rfl⟩ := fib_surjective N y
    obtain ⟨h, rfl⟩ := hT x0 v
    obtain ⟨h', hh'⟩ := QuotientGroup.mk_out_eq_mul M h
    set c := Quotient.out (h : (X ≃g X) ⧸ M) with hc
    have ha : c * (h' : X ≃g X)⁻¹ * c⁻¹ ∈ M := hM.conj_mem _ (M.inv_mem h'.2) c
    refine ⟨c • fib N x0, Finset.mem_image.2 ⟨(h : (X ≃g X) ⧸ M), Finset.mem_univ _, rfl⟩,
      ⟨ρ (c * (h' : X ≃g X)⁻¹ * c⁻¹), Subgroup.mem_map_of_mem ρ ha⟩, ?_⟩
    rw [hKsmul]
    show (c * (h' : X ≃g X)⁻¹ * c⁻¹) • c • fib N x0 = fib N (h • x0)
    rw [← mul_smul, inv_mul_cancel_right, ← smul_fib, hh']
    simp
  have hY := hsemi (Fib N V) K Y hYK hfree (quotGraph_connected N hS) F hFk hFcov
  have hm1 : 1 ≤ m := Finset.card_pos.2 ⟨x0, self_mem_orb N x0⟩
  haveI : Nonempty (Fib N V) := ⟨fib N x0⟩
  have hq1 : 1 ≤ Fintype.card (Fib N V) := Fintype.card_pos
  have hYX : (pathOrder Y : ℝ) ≤ pathOrder X := by exact_mod_cast pathOrder_quotGraph_le hX N hm
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · -- `N` has trivial orbits: `X` and `Y` have the same number of vertices
    have hm' : m = 1 := by omega
    rw [hm', mul_one] at hnmq
    rw [← hnmq] at hY
    have hY' : b * (Fintype.card V : ℝ) ^ (1 - ε / 4) / Real.log (2 * Fintype.card V) ^ (2 * 0)
        ≤ pathOrder Y := by simpa using hY
    exact le_trans (final_arith_one ε b _ _ _ 0 hε (by positivity) (min_le_left _ _) hnR hY') hYX
  · -- the fibres have ambient diameter at most `R = ⌊n^(ε/16)⌋`
    set R := ⌊(Fintype.card V : ℝ) ^ (ε / 16)⌋₊ with hRdef
    have hR1 : 1 ≤ R := by
      rw [hRdef, Nat.one_le_floor_iff]
      exact Real.one_le_rpow (by linarith) (by positivity)
    have hwalk : ∀ x y : V, fib N x = fib N y → WalkLe X Set.univ x y R := by
      intro x y hxy
      obtain ⟨p, hp⟩ := (hS.preconnected x y).exists_walk_length_eq_dist
      refine ⟨p.support, p.isChain_adj_support, ?_, ?_, fun _ _ => trivial, ?_⟩
      · cases p <;> simp
      · rw [List.getLast?_eq_some_getLast (by simp), SimpleGraph.Walk.getLast_support]
      · rw [SimpleGraph.Walk.length_support, hp]
        obtain ⟨g, hgN, hg⟩ := fib_eq_iff.1 hxy
        have := Nat.le_floor (hdiam y x ⟨g, hgN, hg⟩)
        rw [SimpleGraph.dist_comm] at this
        omega
    have hXl := hlift V (X ≃g X) X N m R hX hT hm hm2 hR1 hwalk
    have hRle : (R : ℝ) ≤ (Fintype.card V : ℝ) ^ (ε / 16) := Nat.floor_le (by positivity)
    have hY' : b * (Fintype.card (Fib N V) : ℝ) ^ (1 - ε / 4) /
        Real.log (2 * Fintype.card (Fib N V)) ^ (2 * 0) ≤ pathOrder Y := by simpa using hY
    refine le_trans ?_ (final_arith ε b cη (Fintype.card V) m (Fintype.card (Fib N V)) R _ _ 0
      hb hcη (by exact_mod_cast hnmq.trans (mul_comm _ _) |>.trans (mul_comm _ _))
      (by exact_mod_cast hm2) (by exact_mod_cast hq1)
      (by exact_mod_cast hR1) hRle hY' hXl)
    gcongr
    · exact pow_nonneg (Real.log_nonneg (by linarith)) _
    · exact min_le_right _ _

/-- **Theorem A.1**, with Theorem 1.2 proved: every connected vertex-transitive graph of order
`n ≥ n₀(ε)` contains a path with at least `n^(1-ε)` edges, assuming only the results quoted by
the paper (Lemma 2.3, Lemma 2.4, Theorem 3.16 and Lemma A.2). -/
theorem vt_long_path_of_cited (hD : ExpanderDecomposition) (hL : LinkingLemma 114)
    (hTT : TesseraTointonCayley) (hTTvt : TesseraTointonVT) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (X : SimpleGraph V),
      X.Connected → VertexTransitive X → n₀ ≤ Fintype.card V →
      ∃ l : List V, IsPathL X l ∧ (Fintype.card V : ℝ) ^ (1 - ε) ≤ (l.length : ℝ) - 1 :=
  vt_long_path (cycle_matching_theorem hD hL) hTT hTTvt

end Lovasz
