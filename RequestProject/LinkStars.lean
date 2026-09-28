module
public import RequestProject.Expander

/-!
# Robust expansion: stars or a spread bipartite subgraph

Deterministic tools for Lemma 2.4 (Lemma 5.1 of the cited work on sublinear expanders):

* `expand_avoid`: expansion avoiding the edges to a prescribed set of vertices;
* `highNb_large`: Proposition 5.2 (a set either has a large neighbourhood, or many outside
  vertices have at least `d` neighbours in it);
* `star_or_spread`: a corrected form of Lemma 5.3: a set `B` either sends many disjoint
  stars of size `t` out of `B`, or there is a large set of outside vertices each joined to `r`
  vertices of `B`, with every vertex of `B` used at most `2t` times;
* `exists_coloring`: greedy colouring of a conflict relation of bounded degree.
-/

@[expose] public section


open scoped BigOperators
open Classical

namespace Lovasz

noncomputable section

variable {V : Type*} {G : SimpleGraph V}

/-- The number of neighbours of `v` in `X`. -/
def nbCnt (G : SimpleGraph V) (X : Finset V) (v : V) : ℕ := (X.filter (G.Adj v)).card

/-- `N_d(X)`: the vertices of `U` outside `X` with at least `d` neighbours in `X`. -/
def highNb (G : SimpleGraph V) (U X : Finset V) (d : ℝ) : Finset V :=
  (U \ X).filter (fun v => d ≤ nbCnt G X v)

lemma card_edges_le (X Bv : Finset V) :
    (((X ×ˢ Bv).filter (fun p => G.Adj p.1 p.2)).image (fun p => s(p.1, p.2))).card ≤
      ∑ v ∈ Bv, nbCnt G X v := by
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_filter, Finset.sum_product_right]
  refine Finset.sum_le_sum fun v _ => le_of_eq ?_
  rw [← Finset.card_filter]
  unfold nbCnt
  congr 1
  exact Finset.filter_congr fun x _ => ⟨fun h => h.symm, fun h => h.symm⟩

/-- Expansion avoiding all edges from `X` to a set `Bv` of few edges. -/
lemma expand_avoid {U X : Finset V} {β : ℝ} {c : ℕ} {s : ℝ} (hexp : IsExpander G U β c s)
    (hX : X ⊆ U) (h1 : 1 ≤ X.card) (h2 : 3 * X.card ≤ 2 * U.card) (Bv : Finset V)
    (hF : (∑ v ∈ Bv, nbCnt G X v : ℝ) ≤ s * X.card) :
    β / Real.log U.card ^ c * X.card ≤
      ((U \ X).filter (fun v => v ∉ Bv ∧ ∃ x ∈ X, G.Adj x v)).card := by
  set F := ((X ×ˢ Bv).filter (fun p => G.Adj p.1 p.2)).image (fun p => s(p.1, p.2))
  have hFc : (F.card : ℝ) ≤ s * X.card :=
    le_trans (by exact_mod_cast card_edges_le X Bv) hF
  refine (hexp X hX F h1 h2 hFc).trans ?_
  refine Nat.cast_le.2 (Finset.card_le_card fun v hv => ?_)
  obtain ⟨hvU, x, hx, hxv, hvF⟩ := Finset.mem_filter.1 hv
  refine Finset.mem_filter.2 ⟨hvU, fun hvB => hvF ?_, x, hx, hxv⟩
  exact Finset.mem_image.2 ⟨(x, v), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hx, hvB⟩, hxv⟩, rfl⟩

/-- **Proposition 5.2.** -/
lemma highNb_large {U X : Finset V} {β : ℝ} {c : ℕ} {s d : ℝ} (hexp : IsExpander G U β c s)
    (hX : X ⊆ U) (h1 : 1 ≤ X.card) (h2 : 3 * X.card ≤ 2 * U.card) (hd : 0 < d) (hs : 0 ≤ s) :
    s * X.card ≤ 2 * d * (extNb G U X ∅).card ∨
      β / Real.log U.card ^ c * X.card ≤ (highNb G U X d).card := by
  by_cases h : s * X.card ≤ 2 * d * (extNb G U X ∅).card
  · exact Or.inl h
  right
  push_neg at h
  set N := extNb G U X ∅
  set Bv := N.filter (fun v => (nbCnt G X v : ℝ) < d)
  have hF : (∑ v ∈ Bv, nbCnt G X v : ℝ) ≤ s * X.card := by
    have h3 : (∑ v ∈ Bv, nbCnt G X v : ℝ) ≤ ∑ v ∈ Bv, d :=
      Finset.sum_le_sum fun v hv => (Finset.mem_filter.1 hv).2.le
    have h4 : (Bv.card : ℝ) ≤ N.card := by exact_mod_cast Finset.card_filter_le _ _
    rw [Finset.sum_const, nsmul_eq_mul] at h3
    have : 0 ≤ s * X.card := by positivity
    nlinarith
  refine (expand_avoid hexp hX h1 h2 Bv hF).trans ?_
  refine Nat.cast_le.2 (Finset.card_le_card fun v hv => ?_)
  obtain ⟨hvU, hvB, x, hx, hxv⟩ := Finset.mem_filter.1 hv
  refine Finset.mem_filter.2 ⟨hvU, ?_⟩
  by_contra hlt
  push_neg at hlt
  exact hvB (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hvU, x, hx, hxv, by simp⟩, hlt⟩)

/-- Greedy colouring of a symmetric conflict relation of maximum degree less than `K`. -/
lemma exists_coloring {α : Type*} (K : ℕ) (hK : 0 < K) (adj : α → α → Prop)
    (hsymm : ∀ x y, adj x y → adj y x) :
    ∀ X : Finset α, (∀ x ∈ X, (X.filter (fun y => y ≠ x ∧ adj x y)).card < K) →
    ∃ col : α → Fin K, ∀ x ∈ X, ∀ y ∈ X, x ≠ y → adj x y → col x ≠ col y := by
  intro X
  induction X using Finset.induction_on with
  | empty => exact fun _ => ⟨fun _ => ⟨0, hK⟩, by simp⟩
  | insert a X ha ih =>
    intro hdeg
    obtain ⟨col, hcol⟩ := ih (fun x hx => lt_of_le_of_lt (Finset.card_le_card
      (Finset.filter_subset_filter _ (Finset.subset_insert _ _))) (hdeg x (Finset.mem_insert_of_mem hx)))
    set used := (X.filter (fun y => adj a y)).image col
    have hused : used.card < K := by
      refine lt_of_le_of_lt Finset.card_image_le (lt_of_le_of_lt (Finset.card_le_card ?_)
        (hdeg a (Finset.mem_insert_self _ _)))
      intro y hy
      obtain ⟨hyX, hay⟩ := Finset.mem_filter.1 hy
      exact Finset.mem_filter.2 ⟨Finset.mem_insert_of_mem hyX, fun h => ha (h ▸ hyX), hay⟩
    obtain ⟨k, hk⟩ : ∃ k : Fin K, k ∉ used := by
      by_contra hne
      push_neg at hne
      have : (Finset.univ : Finset (Fin K)) ⊆ used := fun k _ => hne k
      have := Finset.card_le_card this
      simp at this; omega
    refine ⟨Function.update col a k, fun x hx y hy hxy hadj => ?_⟩
    by_cases hxa : x = a
    · subst hxa
      have hyX : y ∈ X := (Finset.mem_insert.1 hy).resolve_left (Ne.symm hxy)
      rw [Function.update_self, Function.update_of_ne (Ne.symm hxy)]
      intro h
      apply hk
      rw [h]
      exact Finset.mem_image.2 ⟨y, Finset.mem_filter.2 ⟨hyX, hadj⟩, rfl⟩
    · have hxX : x ∈ X := (Finset.mem_insert.1 hx).resolve_left hxa
      by_cases hya : y = a
      · subst hya
        rw [Function.update_self, Function.update_of_ne hxy]
        intro h
        apply hk
        rw [← h]
        exact Finset.mem_image.2 ⟨x, Finset.mem_filter.2 ⟨hxX, hsymm _ _ hadj⟩, rfl⟩
      · have hyX : y ∈ X := (Finset.mem_insert.1 hy).resolve_left hya
        rw [Function.update_of_ne hxa, Function.update_of_ne hya]
        exact hcol x hxX y hyX hxy hadj

section stars

variable [Fintype V]

/-- Valid families of disjoint stars with centres in `B` and `t` leaves in `U \ B`. -/
def StarOK (G : SimpleGraph V) (U B : Finset V) (t : ℕ) (g : V → Finset V) : Prop :=
  (∀ b, g b ≠ ∅ → b ∈ B ∧ g b ⊆ U \ B ∧ (g b).card = t ∧ ∀ v ∈ g b, G.Adj b v) ∧
    (∀ a b, a ≠ b → Disjoint (g a) (g b))

/-- Valid spread structures: outside vertices `x` with `r` neighbours `h x` in `B`, every vertex
of `B` used at most `2t` times. -/
def SpreadOK (G : SimpleGraph V) (U B : Finset V) (r t : ℕ) (h : V → Finset V) : Prop :=
  (∀ x, h x ≠ ∅ → x ∈ U \ B ∧ h x ⊆ B ∧ (h x).card = r ∧ ∀ b ∈ h x, G.Adj x b) ∧
    (∀ b ∈ B, (Finset.univ.filter (fun x => b ∈ h x)).card ≤ 2 * t)

set_option maxHeartbeats 800000 in
/-- **Lemma 5.3** (corrected form). -/
theorem star_or_spread {U B : Finset V} {c : ℕ} {s : ℝ}
    (hexp : IsExpander G U (1 / 16) c s) (hB : B ⊆ U) (h1 : 1 ≤ B.card)
    (h2 : 3 * B.card ≤ 2 * U.card) {r t : ℕ} (hr : 1 ≤ r) (hrt : r ≤ t) (ht : 2 ≤ t)
    (hs : 4 * (r : ℝ) * t ≤ s) (hL : 1 ≤ Real.log U.card ^ c)
    (hrL : 13 * Real.log U.card ^ c ≤ r) :
    (∃ g : V → Finset V, StarOK G U B t g ∧
        (B.card : ℝ) ≤ 10 * r * (Finset.univ.filter (fun b => g b ≠ ∅)).card) ∨
    (∃ h : V → Finset V, SpreadOK G U B r t h ∧
        (B.card : ℝ) ≤ 64 * Real.log U.card ^ c * (Finset.univ.filter (fun x => h x ≠ ∅)).card) := by
  set K := Real.log U.card ^ c with hKdef
  have hK0 : 0 < K := by linarith
  -- a maximal family of stars
  obtain ⟨g, hg, hgmax⟩ := Finset.exists_max_image
    ((Finset.univ : Finset (V → Finset V)).filter (StarOK G U B t))
    (fun g => (Finset.univ.filter (fun b => g b ≠ ∅)).card)
    ⟨fun _ => ∅, Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp [StarOK]⟩⟩
  have hgOK : StarOK G U B t g := (Finset.mem_filter.1 hg).2
  set C := Finset.univ.filter (fun b => g b ≠ ∅) with hCdef
  set Lset := C.biUnion g with hLdef
  have hCB : C ⊆ B := fun b hb => (hgOK.1 b (Finset.mem_filter.1 hb).2).1
  have hLcard : Lset.card ≤ t * C.card := by
    refine Finset.card_biUnion_le.trans ?_
    rw [mul_comm]
    exact le_of_eq (by
      rw [Finset.sum_congr rfl (fun b hb => (hgOK.1 b (Finset.mem_filter.1 hb).2).2.2.1),
        Finset.sum_const, smul_eq_mul])
  have hmaxstar : ∀ b ∈ B, g b = ∅ → (((U \ B) \ Lset).filter (G.Adj b)).card < t := by
    intro b hbB hgb
    by_contra hge
    push_neg at hge
    obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hge
    have hTne : T ≠ ∅ := by
      intro h; rw [h] at hTcard; simp at hTcard; omega
    set g' := Function.update g b T
    have hg' : StarOK G U B t g' := by
      refine ⟨fun a ha => ?_, fun a a' haa' => ?_⟩
      · by_cases hab : a = b
        · subst hab
          simp only [g', Function.update_self] at ha ⊢
          refine ⟨hbB, fun v hv => ?_, hTcard, fun v hv => ?_⟩
          · exact Finset.sdiff_subset (Finset.mem_filter.1 (hTsub hv)).1
          · exact (Finset.mem_filter.1 (hTsub hv)).2
        · simp only [g', Function.update_of_ne hab] at ha ⊢
          exact hgOK.1 a ha
      · have hT : ∀ a, a ≠ b → Disjoint T (g a) := by
          intro a hab
          rw [Finset.disjoint_left]
          intro v hvT hva
          have hvL : v ∉ Lset := (Finset.mem_sdiff.1 (Finset.mem_filter.1 (hTsub hvT)).1).2
          apply hvL
          have : g a ≠ ∅ := Finset.nonempty_iff_ne_empty.1 ⟨v, hva⟩
          exact Finset.mem_biUnion.2 ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, this⟩, hva⟩
        by_cases h1' : a = b
        · subst h1'
          simp only [g', Function.update_self, Function.update_of_ne (Ne.symm haa')]
          exact hT a' (Ne.symm haa')
        · by_cases h2' : a' = b
          · subst h2'
            simp only [g', Function.update_self, Function.update_of_ne haa']
            exact (hT a h1').symm
          · simp only [g', Function.update_of_ne h1', Function.update_of_ne h2']
            exact hgOK.2 a a' haa'
    have hmem : g' ∈ (Finset.univ : Finset (V → Finset V)).filter (StarOK G U B t) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hg'⟩
    have hle := hgmax g' hmem
    have hsub : insert b C ⊆ Finset.univ.filter (fun a => g' a ≠ ∅) := by
      intro a ha
      rcases Finset.mem_insert.1 ha with rfl | ha
      · simp [g', hTne]
      · have hab : a ≠ b := fun h => (Finset.mem_filter.1 ha).2 (h ▸ hgb)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, g',
          Function.update_of_ne hab]
        exact (Finset.mem_filter.1 ha).2
    have hbC : b ∉ C := fun h => (Finset.mem_filter.1 h).2 hgb
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hbC] at this
    simp only [C] at this hle
    omega
  by_cases hcase : (B.card : ℝ) ≤ 10 * r * C.card
  · exact Or.inl ⟨g, hgOK, hcase⟩
  push_neg at hcase
  -- a maximal spread structure
  obtain ⟨h, hh, hhmax⟩ := Finset.exists_max_image
    ((Finset.univ : Finset (V → Finset V)).filter (SpreadOK G U B r t))
    (fun h => (Finset.univ.filter (fun x => h x ≠ ∅)).card)
    ⟨fun _ => ∅, Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp [SpreadOK]⟩⟩
  have hhOK : SpreadOK G U B r t h := (Finset.mem_filter.1 hh).2
  set X := Finset.univ.filter (fun x => h x ≠ ∅) with hXdef
  by_cases hcase2 : (B.card : ℝ) ≤ 64 * K * X.card
  · exact Or.inr ⟨h, hhOK, hcase2⟩
  push_neg at hcase2
  exfalso
  set load : V → ℕ := fun b => (Finset.univ.filter (fun x => b ∈ h x)).card
  set Sat := B.filter (fun b => 2 * t ≤ load b)
  -- double counting
  have hdc : ∑ b ∈ B, load b = r * X.card := by
    simp only [load, Finset.card_filter]
    rw [Finset.sum_comm]
    have : ∀ x, ∑ b ∈ B, (if b ∈ h x then 1 else 0) = if h x ≠ ∅ then r else 0 := by
      intro x
      rw [← Finset.card_filter]
      by_cases hx : h x = ∅
      · simp [hx]
      · rw [if_pos hx]
        have hsub := (hhOK.1 x hx).2.1
        rw [← (hhOK.1 x hx).2.2.1]
        congr 1
        ext b; simp only [Finset.mem_filter]
        exact ⟨fun h' => h'.2, fun h' => ⟨hsub h', h'⟩⟩
    simp only [this]
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
  have hSat : 2 * t * Sat.card ≤ r * X.card := by
    rw [← hdc]
    calc 2 * t * Sat.card = ∑ b ∈ Sat, 2 * t := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ b ∈ Sat, load b := Finset.sum_le_sum fun b hb => (Finset.mem_filter.1 hb).2
      _ ≤ ∑ b ∈ B, load b := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hSat2 : 2 * Sat.card ≤ X.card := by
    have : 2 * t * Sat.card ≤ t * X.card := hSat.trans (Nat.mul_le_mul_right _ hrt)
    have ht0 : 0 < t := by omega
    nlinarith
  set B'' := B \ (C ∪ Sat) with hB''def
  have hB''B : B'' ⊆ B := Finset.sdiff_subset
  have hB''card : (B.card : ℝ) - C.card - Sat.card ≤ B''.card := by
    have h1' : B.card ≤ B''.card + (C ∪ Sat).card := by
      have := Finset.card_sdiff_add_card_inter B (C ∪ Sat)
      rw [← hB''def] at this
      have := Finset.card_le_card (Finset.inter_subset_right (s₁ := B) (s₂ := C ∪ Sat))
      omega
    have h2' := Finset.card_union_le C Sat
    have : (B.card : ℝ) ≤ B''.card + C.card + Sat.card := by exact_mod_cast (by omega)
    linarith
  -- numerical facts
  have hC : 130 * K * C.card < B.card := by
    have : 130 * K * C.card ≤ 10 * r * C.card := by
      have : (0 : ℝ) ≤ C.card := Nat.cast_nonneg _
      nlinarith
    linarith
  have hX : 64 * K * X.card < B.card := hcase2
  have hS : 128 * K * Sat.card < B.card := by
    have : (2 * Sat.card : ℝ) ≤ X.card := by exact_mod_cast hSat2
    have : 64 * K * (2 * Sat.card) ≤ 64 * K * X.card :=
      mul_le_mul_of_nonneg_left this (by positivity)
    linarith
  have hCK : 130 * (C.card : ℝ) ≤ 130 * K * C.card := by
    have : (0 : ℝ) ≤ C.card := Nat.cast_nonneg _
    nlinarith
  have hSK : 128 * (Sat.card : ℝ) ≤ 128 * K * Sat.card := by
    have : (0 : ℝ) ≤ Sat.card := Nat.cast_nonneg _
    nlinarith
  have hBpos : (1 : ℝ) ≤ B.card := by exact_mod_cast h1
  have hB''half : (B.card : ℝ) / 2 ≤ B''.card := by linarith
  have hB''1 : 1 ≤ B''.card := by
    have : (0 : ℝ) < B''.card := by linarith
    exact_mod_cast this
  -- the neighbourhood of `B''`
  set N := extNb G U B'' ∅
  have hNsub : N ⊆ (C ∪ Sat) ∪ Lset ∪
      B''.biUnion (fun b => ((U \ B) \ Lset).filter (G.Adj b)) := by
    intro v hv
    obtain ⟨hvU, b, hb, hbv, -⟩ := Finset.mem_filter.1 hv
    have hvB'' := (Finset.mem_sdiff.1 hvU).2
    by_cases hvB : v ∈ B
    · refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
      by_contra hc
      exact hvB'' (Finset.mem_sdiff.2 ⟨hvB, hc⟩)
    · by_cases hvL : v ∈ Lset
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hvL)
      · refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨b, hb, ?_⟩)
        exact Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨Finset.mem_sdiff.2
          ⟨(Finset.mem_sdiff.1 hvU).1, hvB⟩, hvL⟩, hbv⟩
  have hNcard : (N.card : ℝ) ≤ 2 * t * B.card := by
    have hb1 : (B''.biUnion (fun b => ((U \ B) \ Lset).filter (G.Adj b))).card ≤ t * B''.card := by
      refine Finset.card_biUnion_le.trans ?_
      calc ∑ b ∈ B'', (((U \ B) \ Lset).filter (G.Adj b)).card ≤ ∑ b ∈ B'', t :=
            Finset.sum_le_sum fun b hb => by
              have hbB := hB''B hb
              have hbC : b ∉ C := fun h' => (Finset.mem_sdiff.1 hb).2 (Finset.mem_union_left _ h')
              have hgb : g b = ∅ := by
                by_contra h'; exact hbC (Finset.mem_filter.2 ⟨Finset.mem_univ _, h'⟩)
              exact (hmaxstar b hbB hgb).le
        _ = t * B''.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have hcs : (C ∪ Sat).card ≤ B.card :=
      Finset.card_le_card (Finset.union_subset hCB (Finset.filter_subset _ _))
    have hdisj : Disjoint C B'' := Finset.disjoint_left.2 fun b hbC hbB'' =>
      (Finset.mem_sdiff.1 hbB'').2 (Finset.mem_union_left _ hbC)
    have hCB'' : C.card + B''.card ≤ B.card := by
      rw [← Finset.card_union_of_disjoint hdisj]
      exact Finset.card_le_card (Finset.union_subset hCB hB''B)
    have hN1 := Finset.card_le_card hNsub
    have h3 := Finset.card_union_le ((C ∪ Sat) ∪ Lset)
      (B''.biUnion (fun b => ((U \ B) \ Lset).filter (G.Adj b)))
    have h4 := Finset.card_union_le (C ∪ Sat) Lset
    have h5 : t * C.card + t * B''.card ≤ t * B.card := by
      rw [← mul_add]; exact Nat.mul_le_mul_left _ hCB''
    have h6 : B.card ≤ t * B.card := Nat.le_mul_of_pos_left _ (by omega)
    have : N.card ≤ t * B.card + t * B.card := by omega
    have : (N.card : ℝ) ≤ t * B.card + t * B.card := by exact_mod_cast this
    linarith
  set Bv := N.filter (fun v => v ∉ B ∧ nbCnt G B'' v < r)
  have hF : (∑ v ∈ Bv, nbCnt G B'' v : ℝ) ≤ s * B''.card := by
    have h3 : (∑ v ∈ Bv, nbCnt G B'' v : ℝ) ≤ ∑ v ∈ Bv, (r : ℝ) :=
      Finset.sum_le_sum fun v hv => by exact_mod_cast (Finset.mem_filter.1 hv).2.2.le
    have h4 : (Bv.card : ℝ) ≤ N.card := by exact_mod_cast Finset.card_filter_le _ _
    rw [Finset.sum_const, nsmul_eq_mul] at h3
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
    have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
    calc (∑ v ∈ Bv, nbCnt G B'' v : ℝ) ≤ Bv.card * r := h3
      _ ≤ N.card * r := mul_le_mul_of_nonneg_right h4 hr0
      _ ≤ (2 * t * B.card) * r := mul_le_mul_of_nonneg_right hNcard hr0
      _ ≤ (2 * t * (2 * B''.card)) * r := by
        gcongr; linarith
      _ = (4 * r * t) * B''.card := by ring
      _ ≤ s * B''.card := mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg _)
  have hexpB := expand_avoid hexp (hB''B.trans hB) hB''1
    (le_trans (Nat.mul_le_mul_left 3 (Finset.card_le_card hB''B)) h2) Bv hF
  -- the expansion lands in `C ∪ Sat ∪ X`
  have hland : (U \ B'').filter (fun v => v ∉ Bv ∧ ∃ x ∈ B'', G.Adj x v) ⊆ (C ∪ Sat) ∪ X := by
    intro v hv
    obtain ⟨hvU, hvBv, b, hb, hbv⟩ := Finset.mem_filter.1 hv
    have hvB'' := (Finset.mem_sdiff.1 hvU).2
    by_cases hvB : v ∈ B
    · refine Finset.mem_union_left _ ?_
      by_contra hc
      exact hvB'' (Finset.mem_sdiff.2 ⟨hvB, hc⟩)
    refine Finset.mem_union_right _ ?_
    have hvN : v ∈ N := Finset.mem_filter.2 ⟨hvU, b, hb, hbv, by simp⟩
    have hcnt : r ≤ nbCnt G B'' v := by
      by_contra hlt
      push_neg at hlt
      exact hvBv (Finset.mem_filter.2 ⟨hvN, hvB, hlt⟩)
    by_contra hvX
    have hhv : h v = ∅ := by
      by_contra h'; exact hvX (Finset.mem_filter.2 ⟨Finset.mem_univ _, h'⟩)
    obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hcnt
    have hTne : T ≠ ∅ := by
      intro h'; rw [h'] at hTcard; simp at hTcard; omega
    set h' := Function.update h v T
    have hh' : SpreadOK G U B r t h' := by
      refine ⟨fun x hx => ?_, fun b' hb' => ?_⟩
      · by_cases hxv : x = v
        · subst hxv
          simp only [h', Function.update_self]
          refine ⟨Finset.mem_sdiff.2 ⟨(Finset.mem_sdiff.1 hvU).1, hvB⟩,
            fun w hw => hB''B (Finset.mem_filter.1 (hTsub hw)).1, hTcard,
            fun w hw => (Finset.mem_filter.1 (hTsub hw)).2⟩
        · simp only [h', Function.update_of_ne hxv] at hx ⊢
          exact hhOK.1 x hx
      · have hsplit : Finset.univ.filter (fun x => b' ∈ h' x) ⊆
            insert v (Finset.univ.filter (fun x => b' ∈ h x)) := by
          intro x hx
          by_cases hxv : x = v
          · exact hxv ▸ Finset.mem_insert_self _ _
          · refine Finset.mem_insert_of_mem ?_
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, h',
              Function.update_of_ne hxv] at hx ⊢
            exact hx
        by_cases hb'T : b' ∈ T
        · have hb'B'' := (Finset.mem_filter.1 (hTsub hb'T)).1
          have hnotsat : b' ∉ Sat := fun hs' =>
            (Finset.mem_sdiff.1 hb'B'').2 (Finset.mem_union_right _ hs')
          have hlt : load b' < 2 * t := by
            by_contra hge; push_neg at hge
            exact hnotsat (Finset.mem_filter.2 ⟨hb', hge⟩)
          have := Finset.card_le_card hsplit
          have := Finset.card_insert_le v (Finset.univ.filter (fun x => b' ∈ h x))
          simp only [load] at hlt
          omega
        · have heq : Finset.univ.filter (fun x => b' ∈ h' x) =
              Finset.univ.filter (fun x => b' ∈ h x) := by
            ext x
            by_cases hxv : x = v
            · subst hxv; simp [h', hb'T, hhv]
            · simp [h', Function.update_of_ne hxv]
          rw [heq]; exact hhOK.2 b' hb'
    have hmem : h' ∈ (Finset.univ : Finset (V → Finset V)).filter (SpreadOK G U B r t) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hh'⟩
    have hle := hhmax h' hmem
    have hsub : insert v X ⊆ Finset.univ.filter (fun x => h' x ≠ ∅) := by
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · simp [h', hTne]
      · have hxv : x ≠ v := fun h'' => hvX (h'' ▸ hx)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, h',
          Function.update_of_ne hxv]
        exact (Finset.mem_filter.1 hx).2
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hvX] at this
    simp only [X] at this hle
    omega
  have hfin := hexpB.trans (Nat.cast_le.2 (Finset.card_le_card hland))
  have hu1 := Finset.card_union_le (C ∪ Sat) X
  have hu2 := Finset.card_union_le C Sat
  have hu : (((C ∪ Sat) ∪ X).card : ℝ) ≤ C.card + Sat.card + X.card := by
    exact_mod_cast (by omega)
  have key : (B''.card : ℝ) ≤ 16 * K * (C.card + Sat.card + X.card) := by
    have := hfin.trans hu
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hK0] at this
    linarith
  nlinarith

end stars

end

end Lovasz
