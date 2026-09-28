module
public import RequestProject.Expander

/-!
# Edge expanders (towards Lemma 2.3)

Basic edge counting inside a vertex set, the notion of a `λ`-expander (edge expansion,
Definition 3.1 of the cited work on sublinear expanders), the conversion of a nearly regular
`λ`-expander into a `(1/8, c, λd/4)`-expander (Lemma 3.3 there), and the extraction of a single
`λ`-expander of nearly the same average degree (Lemma 4.5 there).
-/

@[expose] public section


open scoped BigOperators
open Classical

namespace Lovasz

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

/-- The number of ordered edges from `A` to `B`. -/
def eCut (A B : Finset V) : ℕ := ((A ×ˢ B).filter (fun p => G.Adj p.1 p.2)).card

/-- The degree sum of the graph induced on `W` (twice its number of edges). -/
def dsum (W : Finset V) : ℕ := ∑ v ∈ W, degIn G W v

/-- The average degree of the graph induced on `W`. -/
def avgDeg (W : Finset V) : ℝ := (dsum G W : ℝ) / W.card

/-- `W` spans a `λ`-expander: every `X ⊆ W` with `|X| ≤ |W|/2` sends at least
`λ · d(W) · |X|` edges to `W \ X`. -/
def IsLamExp (W : Finset V) (lam : ℝ) : Prop :=
  ∀ X ⊆ W, 2 * X.card ≤ W.card → lam * avgDeg G W * X.card ≤ eCut G X (W \ X)

variable {G}

lemma eCut_eq_sum (A B : Finset V) : eCut G A B = ∑ a ∈ A, degIn G B a := by
  unfold eCut degIn
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.card_filter]

lemma eCut_comm (A B : Finset V) : eCut G A B = eCut G B A := by
  unfold eCut
  refine Finset.card_bij (fun p _ => p.swap) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2.symm⟩
  · intro p _ q _ h
    exact Prod.swap_injective h
  · intro q hq
    refine ⟨q.swap, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_product] at hq ⊢
    exact ⟨⟨hq.1.2, hq.1.1⟩, hq.2.symm⟩

lemma degIn_union {A B : Finset V} (h : Disjoint A B) (v : V) :
    degIn G (A ∪ B) v = degIn G A v + degIn G B v := by
  unfold degIn
  rw [Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter h)]

lemma degIn_mono {A B : Finset V} (h : A ⊆ B) (v : V) : degIn G A v ≤ degIn G B v :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

lemma degIn_lt_card {W : Finset V} {v : V} (hv : v ∈ W) : degIn G W v < W.card := by
  unfold degIn
  refine Finset.card_lt_card ⟨Finset.filter_subset _ _, fun h => ?_⟩
  exact G.loopless.irrefl v (Finset.mem_filter.1 (h hv)).2

lemma degIn_split {A W : Finset V} (h : A ⊆ W) (v : V) :
    degIn G W v = degIn G A v + degIn G (W \ A) v := by
  rw [← degIn_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset h]

/-- Splitting the degree sum along `A ⊆ W`. -/
lemma dsum_split {A W : Finset V} (h : A ⊆ W) :
    dsum G W = dsum G A + dsum G (W \ A) + 2 * eCut G A (W \ A) := by
  unfold dsum
  rw [← Finset.sum_sdiff h]
  have h1 : ∑ v ∈ A, degIn G W v = ∑ v ∈ A, degIn G A v + eCut G A (W \ A) := by
    rw [eCut_eq_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => degIn_split h v
  have h2 : ∑ v ∈ W \ A, degIn G W v = ∑ v ∈ W \ A, degIn G (W \ A) v + eCut G A (W \ A) := by
    rw [eCut_comm, eCut_eq_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => by rw [degIn_split h v, add_comm]
  rw [h1, h2]; ring

lemma dsum_mono {A W : Finset V} (h : A ⊆ W) : dsum G A ≤ dsum G W := by
  rw [dsum_split h]; omega

/-- The degree sums of disjoint parts of `T` add up to at most the degree sum of `T`. -/
lemma sum_dsum_le {T : Finset V} {𝒞 : Finset (Finset V)}
    (hdisj : (𝒞 : Set (Finset V)).PairwiseDisjoint id) (hsub : ∀ W ∈ 𝒞, W ⊆ T) :
    ∑ W ∈ 𝒞, dsum G W ≤ dsum G T := by
  unfold dsum
  calc ∑ W ∈ 𝒞, ∑ v ∈ W, degIn G W v ≤ ∑ W ∈ 𝒞, ∑ v ∈ W, degIn G T v :=
        Finset.sum_le_sum fun W hW => Finset.sum_le_sum fun v _ => degIn_mono (hsub W hW) v
    _ = ∑ v ∈ 𝒞.biUnion id, degIn G T v := (Finset.sum_biUnion hdisj).symm
    _ ≤ ∑ v ∈ T, degIn G T v := by
        refine Finset.sum_le_sum_of_subset ?_
        intro v hv
        obtain ⟨W, hW, hvW⟩ := Finset.mem_biUnion.1 hv
        exact hsub W hW hvW

lemma card_biUnion_eq {𝒞 : Finset (Finset V)}
    (hdisj : (𝒞 : Set (Finset V)).PairwiseDisjoint id) :
    (𝒞.biUnion id).card = ∑ W ∈ 𝒞, W.card :=
  Finset.card_biUnion hdisj

lemma avgDeg_nonneg (W : Finset V) : 0 ≤ avgDeg G W := by
  unfold avgDeg; positivity

lemma avgDeg_mul_card {W : Finset V} (hW : W.Nonempty) :
    avgDeg G W * W.card = dsum G W := by
  unfold avgDeg
  have : (W.card : ℝ) ≠ 0 := by exact_mod_cast hW.card_pos.ne'
  field_simp

lemma IsLamExp.mono {W : Finset V} {lam lam' : ℝ} (h : IsLamExp G W lam) (hl : lam' ≤ lam) :
    IsLamExp G W lam' := by
  intro X hX h2
  refine le_trans ?_ (h X hX h2)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hl (avgDeg_nonneg W))
    (Nat.cast_nonneg _)

/-! ### Lemma 3.3: from edge expansion to robust vertex expansion -/

/-- Ordered edges from `X` to `W \ X` not in `F` land in the external neighbourhood, and each
neighbour receives at most `d` of them. -/
lemma eCut_le_F_add {W X : Finset V} (hX : X ⊆ W) (F : Finset (Sym2 V)) {d : ℝ}
    (hdeg : ∀ v ∈ W, (degIn G W v : ℝ) ≤ d) :
    (eCut G X (W \ X) : ℝ) ≤ F.card + d * (extNb G W X F).card := by
  set P := (X ×ˢ (W \ X)).filter (fun p => G.Adj p.1 p.2)
  have hsplit : P.card = (P.filter (fun p => s(p.1, p.2) ∈ F)).card +
      (P.filter (fun p => s(p.1, p.2) ∉ F)).card :=
    (Finset.card_filter_add_card_filter_not _).symm
  have h1 : (P.filter (fun p => s(p.1, p.2) ∈ F)).card ≤ F.card := by
    refine Finset.card_le_card_of_injOn (fun p => s(p.1, p.2)) ?_ ?_
    · intro p hp
      exact (Finset.mem_filter.1 (Finset.mem_coe.1 hp)).2
    · intro p hp q hq hpq
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_product,
        P, Finset.mem_sdiff] at hp hq
      rcases Sym2.eq_iff.1 hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Prod.ext h1 h2
      · exact absurd (h1 ▸ hp.1.1.1) hq.1.1.2.2
  have h2 : ((P.filter (fun p => s(p.1, p.2) ∉ F)).card : ℝ) ≤ d * (extNb G W X F).card := by
    set Q := P.filter (fun p => s(p.1, p.2) ∉ F)
    have hmaps : ∀ p ∈ Q, p.2 ∈ extNb G W X F := by
      intro p hp
      simp only [Q, P, Finset.mem_filter, Finset.mem_product] at hp
      exact Finset.mem_filter.2 ⟨hp.1.1.2, p.1, hp.1.1.1, hp.1.2, hp.2⟩
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    push_cast
    calc ∑ v ∈ extNb G W X F, ((Q.filter (fun p => p.2 = v)).card : ℝ)
        ≤ ∑ v ∈ extNb G W X F, d := by
          refine Finset.sum_le_sum fun v hv => ?_
          have hvW : v ∈ W := (Finset.mem_sdiff.1 (Finset.mem_filter.1 hv).1).1
          refine le_trans ?_ (hdeg v hvW)
          exact_mod_cast Finset.card_le_card_of_injOn (fun p : V × V => p.1)
            (by
              intro p hp
              simp only [Finset.coe_filter, Set.mem_setOf_eq, Q, P, Finset.mem_filter,
                Finset.mem_product] at hp
              simp only [Finset.coe_filter, Set.mem_setOf_eq]
              refine ⟨hX hp.1.1.1.1, ?_⟩
              rw [← hp.2]; exact hp.1.1.2.symm)
            (by
              intro p hp q hq hpq
              simp only [Finset.coe_filter, Set.mem_setOf_eq, Q, P, Finset.mem_filter] at hp hq
              exact Prod.ext hpq (hp.2.trans hq.2.symm))
      _ = d * (extNb G W X F).card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  unfold eCut
  rw [hsplit]; push_cast
  have := (show ((P.filter (fun p => s(p.1, p.2) ∈ F)).card : ℝ) ≤ F.card by exact_mod_cast h1)
  linarith

/-- **Lemma 3.3** (of the cited work): a `λ`-expander with maximum degree at most `d` and
average degree at least `3d/4` is a robust vertex expander. -/
lemma lamExp_vertex_expansion {W : Finset V} {d lam : ℝ} (hd : 0 < d) (hlam : 0 ≤ lam)
    (hdeg : ∀ v ∈ W, (degIn G W v : ℝ) ≤ d) (havg : d * (3 / 4) ≤ avgDeg G W)
    (hexp : IsLamExp G W lam) (X : Finset V) (hX : X ⊆ W) (F : Finset (Sym2 V))
    (h3 : 3 * X.card ≤ 2 * W.card) (hF : (F.card : ℝ) ≤ lam * d / 4 * X.card) :
    lam / 8 * X.card ≤ (extNb G W X F).card := by
  have hcut := eCut_le_F_add hX F hdeg
  have hN0 : (0 : ℝ) ≤ (extNb G W X F).card := Nat.cast_nonneg _
  have hX0 : (0 : ℝ) ≤ X.card := Nat.cast_nonneg _
  by_cases hhalf : 2 * X.card ≤ W.card
  · have he := hexp X hX hhalf
    have : lam * (d * (3 / 4)) * X.card ≤ lam * avgDeg G W * X.card :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left havg hlam) hX0
    have key : lam * d / 2 * X.card ≤ d * (extNb G W X F).card := by nlinarith
    have : lam / 2 * X.card ≤ (extNb G W X F).card := by
      rw [← mul_le_mul_iff_of_pos_left hd]; nlinarith
    nlinarith
  · push_neg at hhalf
    set Y := W \ X
    have hYW : Y ⊆ W := Finset.sdiff_subset
    have hWY : W \ Y = X := Finset.sdiff_sdiff_eq_self hX
    have hcard : Y.card + X.card = W.card := Finset.card_sdiff_add_card_eq_card hX
    have hY2 : 2 * Y.card ≤ W.card := by omega
    have he := hexp Y hYW hY2
    rw [hWY, eCut_comm] at he
    have hYX : (X.card : ℝ) ≤ 2 * Y.card := by
      have : X.card ≤ 2 * Y.card := by omega
      exact_mod_cast this
    have hY0 : (0 : ℝ) ≤ Y.card := Nat.cast_nonneg _
    have : lam * (d * (3 / 4)) * Y.card ≤ lam * avgDeg G W * Y.card :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left havg hlam) hY0
    have hld : 0 ≤ lam * d := mul_nonneg hlam hd.le
    have key : lam * d / 8 * X.card ≤ d * (extNb G W X F).card := by nlinarith
    rw [← mul_le_mul_iff_of_pos_left hd]; nlinarith

end

end Lovasz
