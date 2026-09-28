module
public import RequestProject.Coupling
public import RequestProject.Asymp
public import RequestProject.Basic

/-!
# Sublinear expanders (Section 2.1)

A graph is given by a `SimpleGraph V` on an ambient finite type together with a vertex set
`U : Finset V`; only edges inside `U` are ever used.  This covers subgraphs and vertex
deletions (`G - X` is `(G, U \ X)`).
-/

@[expose] public section


open scoped BigOperators
open Classical Filter

namespace Lovasz

noncomputable section

variable {V : Type*}

/-- The external neighbourhood of `X` inside `U` in the graph `G - F`. -/
def extNb (G : SimpleGraph V) (U X : Finset V) (F : Finset (Sym2 V)) : Finset V :=
  (U \ X).filter (fun v => ∃ x ∈ X, G.Adj x v ∧ s(x, v) ∉ F)

/-- The degree of `v` inside `U`. -/
def degIn (G : SimpleGraph V) (U : Finset V) (v : V) : ℕ := (U.filter (G.Adj v)).card

/-- **Definition 2.1.** `(G, U)` is a `(β, c, s)`-expander: for every `X ⊆ U` with
`1 ≤ |X| ≤ 2|U|/3` and every edge set `F` with `|F| ≤ s|X|`,
`|N_{G-F}(X)| ≥ β / (log |U|)^c · |X|`. -/
def IsExpander (G : SimpleGraph V) (U : Finset V) (β : ℝ) (c : ℕ) (s : ℝ) : Prop :=
  ∀ X ⊆ U, ∀ F : Finset (Sym2 V), 1 ≤ X.card → 3 * X.card ≤ 2 * U.card →
    (F.card : ℝ) ≤ s * X.card → β / Real.log U.card ^ c * X.card ≤ (extNb G U X F).card

lemma IsExpander.mono_s {G : SimpleGraph V} {U : Finset V} {β : ℝ} {c : ℕ} {s s' : ℝ}
    (h : IsExpander G U β c s) (hs : s' ≤ s) : IsExpander G U β c s' := by
  intro X hX F h1 h2 h3
  refine h X hX F h1 h2 (h3.trans ?_)
  exact mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg _)

/-- A path from `a` to `b`, as a list of vertices. -/
def PathFrom (G : SimpleGraph V) (a b : V) (P : List V) : Prop :=
  P.head? = some a ∧ P.getLast? = some b ∧ IsPathL G P

/-- The linking property of Lemma 2.4 for the set `R`: any family of pairs of distinct vertices
of `U \ R` whose subsets `X` all satisfy `|N(X)| ≥ K |X|` can be joined by vertex-disjoint
paths with all internal vertices in `R`. -/
def LinkProp (G : SimpleGraph V) (U R : Finset V) (K : ℝ) : Prop :=
  ∀ pairs : List (V × V), (pairs.map Prod.fst ++ pairs.map Prod.snd).Nodup →
    (∀ p ∈ pairs, p.1 ∈ U \ R ∧ p.2 ∈ U \ R) →
    (∀ X ⊆ (pairs.map Prod.fst ++ pairs.map Prod.snd).toFinset,
      K * X.card ≤ (extNb G U X ∅).card) →
    ∃ paths : List (List V), paths.flatten.Nodup ∧
      List.Forall₂ (fun p P => PathFrom G p.1 p.2 P ∧ ∀ v ∈ P, v = p.1 ∨ v = p.2 ∨ v ∈ R)
        pairs paths

/-- **Lemma 2.3** of the paper (Lemma 4.1 of the cited work on sublinear expanders, applied with
`α = 1`), in the instance `C = 57`, `c = C(C-1)/(C-29) = 114` used in the proof of
Theorem 1.2.  It is proved in `RequestProject/DecompMain.lean` (`expander_decomposition`). -/
def ExpanderDecomposition : Prop :=
  ∃ N₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (U : Finset V) (d ε : ℝ),
    N₀ ≤ U.card → 2 * Real.log U.card ≤ d → 0 ≤ ε → ε ≤ Real.log U.card ^ (-(56 : ℝ)) →
    (∀ v ∈ U, (degIn G U v : ℝ) ≤ d) → d * (1 - ε) * U.card ≤ ∑ v ∈ U, (degIn G U v : ℝ) →
    ∃ (m : ℕ) (W : Fin m → Finset V) (H : Fin m → SimpleGraph V),
      (∀ i, W i ⊆ U) ∧ (∀ i j, i ≠ j → Disjoint (W i) (W j)) ∧ (∀ i, H i ≤ G) ∧
      (∀ i, IsExpander (H i) (W i) (1 / 8) 114 (d / (4 * Real.log (W i).card ^ 114))) ∧
      (∀ i, d * (1 - Real.log (W i).card ^ (-(28 : ℝ))) * (W i).card ≤
        ∑ v ∈ W i, (degIn (H i) (W i) v : ℝ)) ∧
      (∀ i, ∀ v ∈ W i, (∑ u ∈ W i, (degIn (H i) (W i) u : ℝ)) / (W i).card / 2 ≤
        degIn (H i) (W i) v) ∧
      (1 - Real.log (Real.log (Real.log U.card)) ^ 2 / Real.log (Real.log U.card)) * U.card ≤
        ∑ i, ((W i).card : ℝ)

/-- The body of Lemma 2.4 for the constant `c` and threshold `N₀`. -/
def LinkingBody (c N₀ : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (U : Finset V) (q s : ℝ),
    N₀ ≤ U.card → 0 < q → q < 1 → 2 * Real.log U.card ^ (9 * c + 21) / q ^ 10 ≤ s →
    IsExpander G U (1 / 16) c s →
    1 - 1 / (U.card : ℝ) ≤ ppr (fun _ : V => bern q) (fun y =>
      LinkProp G U (U.filter (fun v => y v = true)) (100 * Real.log U.card ^ (7 * c + 19) / q ^ 6))

/-- **Lemma 2.4** of the paper (Lemma 5.1 of the cited work on sublinear expanders, applied with
`ε = 1/16`), for the constant `c`: for `q`-random subsets `R` of the vertex set of a sufficiently
large `(1/16, c, s)`-expander on `U` with `s ≥ 2 (log |U|)^(9c+21) / q^10`, with probability at
least `1 - 1/|U|` every family of pairs of distinct vertices outside `R` whose subsets expand by a
factor `100 (log |U|)^(7c+19) / q^6` can be linked by vertex-disjoint paths through `R`.  It is
proved in `RequestProject/LinkLemma.lean` (`linking_lemma`). -/
def LinkingLemma (c : ℕ) : Prop := ∃ N₀ : ℕ, LinkingBody c N₀


section lemma22

variable {G : SimpleGraph V}

lemma sum_card_F_le (U Y : Finset V) (F : Finset (Sym2 V)) :
    ∑ y ∈ Y, (U.filter (fun v => G.Adj y v ∧ s(y, v) ∈ F)).card ≤ 2 * F.card := by
  set P := (Y ×ˢ U).filter (fun p => G.Adj p.1 p.2 ∧ s(p.1, p.2) ∈ F)
  have h1 : ∑ y ∈ Y, (U.filter (fun v => G.Adj y v ∧ s(y, v) ∈ F)).card = P.card := by
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.card_filter]
  have h2 : P.card ≤ 2 * (P.image (fun p => s(p.1, p.2))).card := by
    refine Finset.card_le_mul_card_image _ 2 fun e he => ?_
    obtain ⟨⟨a, b⟩, -, rfl⟩ := Finset.mem_image.1 he
    calc (P.filter (fun p => s(p.1, p.2) = s(a, b))).card ≤ ({(a, b), (b, a)} : Finset (V × V)).card := by
          refine Finset.card_le_card fun p hp => ?_
          obtain ⟨-, hp⟩ := Finset.mem_filter.1 hp
          rcases Sym2.eq_iff.1 hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · simp [Prod.ext_iff, h1, h2]
          · simp [Prod.ext_iff, h1, h2]
      _ ≤ 2 := Finset.card_le_two
  have h3 : P.image (fun p => s(p.1, p.2)) ⊆ F := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 he
    exact (Finset.mem_filter.1 hp).2.2
  rw [h1]
  exact h2.trans (Nat.mul_le_mul_left 2 (Finset.card_le_card h3))

/-- The small-set case of Lemma 2.2: `|N_{G-F}(Y)| ≥ 3D/8`. -/
lemma small_set_nbhd {U Y : Finset V} {F : Finset (Sym2 V)} {D : ℝ}
    (hY : Y.Nonempty) (hdeg : ∀ y ∈ Y, D ≤ degIn G U y) (hYD : (Y.card : ℝ) ≤ D / 2)
    (hF : (2 * F.card : ℝ) ≤ Y.card * D / 8) :
    3 * D / 8 ≤ (extNb G U Y F).card := by
  set N := extNb G U Y F
  have hsub : ∀ y ∈ Y, (U \ Y).filter (fun v => G.Adj y v ∧ s(y, v) ∉ F) ⊆ N := by
    intro y hy v hv
    obtain ⟨hvU, hadj, hvF⟩ := Finset.mem_filter.1 hv
    exact Finset.mem_filter.2 ⟨hvU, y, hy, hadj, hvF⟩
  have hdeg' : ∀ y ∈ Y, (degIn G U y : ℝ) ≤ N.card + Y.card +
      (U.filter (fun v => G.Adj y v ∧ s(y, v) ∈ F)).card := by
    intro y hy
    have : U.filter (G.Adj y) ⊆ ((U \ Y).filter (fun v => G.Adj y v ∧ s(y, v) ∉ F) ∪ Y) ∪
        U.filter (fun v => G.Adj y v ∧ s(y, v) ∈ F) := by
      intro v hv
      obtain ⟨hvU, hadj⟩ := Finset.mem_filter.1 hv
      by_cases hvY : v ∈ Y
      · simp [hvY]
      · by_cases hvF : s(y, v) ∈ F
        · simp [hvU, hadj, hvF]
        · simp [hvU, hadj, hvF, hvY]
    have h := (Finset.card_le_card this).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
    have h2 := Finset.card_le_card (hsub y hy)
    unfold degIn
    exact_mod_cast h.trans (by omega)
  have hsum := Finset.sum_le_sum hdeg'
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  have hF2 : (∑ y ∈ Y, ((U.filter (fun v => G.Adj y v ∧ s(y, v) ∈ F)).card : ℝ)) ≤ 2 * F.card := by
    exact_mod_cast sum_card_F_le U Y F
  have hD : (Y.card : ℝ) * D ≤ ∑ y ∈ Y, (degIn G U y : ℝ) := by
    have := Finset.sum_le_sum (fun y hy => hdeg y hy)
    simpa [Finset.sum_const, nsmul_eq_mul] using this
  have hYpos : (0 : ℝ) < Y.card := by exact_mod_cast hY.card_pos
  have key : Y.card * (3 * D / 8) ≤ Y.card * (N.card : ℝ) := by nlinarith
  exact le_of_mul_le_mul_left key hYpos

/-- Comparison of `(log m')^c` with `(log m)^c` when `m' ≥ m/2`. -/
lemma log_pow_compare {m m' : ℝ} (c : ℕ) (hm : 0 < m) (hm' : m / 2 ≤ m')
    (hlog : 4 * c * Real.log 2 ≤ Real.log m) (hl2 : Real.log 2 ≤ Real.log m) :
    3 / 4 * Real.log m ^ c ≤ Real.log m' ^ c := by
  have hm'0 : 0 < m' := by linarith
  have hL : Real.log m - Real.log 2 ≤ Real.log m' := by
    rw [← Real.log_div (by linarith) (by norm_num)]
    exact Real.log_le_log (by positivity) (by linarith)
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set L := Real.log m
  have hLpos : 0 < L := by linarith
  have h1 : (L - Real.log 2) ^ c ≤ Real.log m' ^ c :=
    pow_le_pow_left₀ (by linarith) hL c
  have hb := one_add_mul_le_pow (a := -(Real.log 2 / L)) (by
    have : Real.log 2 / L ≤ 1 := (div_le_one hLpos).2 hl2
    linarith) c
  have h2 : (L - Real.log 2) ^ c = L ^ c * (1 + -(Real.log 2 / L)) ^ c := by
    rw [← mul_pow]; congr 1; field_simp; ring
  have h3 : (3 : ℝ) / 4 ≤ 1 + c * -(Real.log 2 / L) := by
    have : c * (Real.log 2 / L) ≤ 1 / 4 := by
      rw [mul_div_assoc', div_le_iff₀ hLpos]; linarith
    linarith
  have hLc : 0 ≤ L ^ c := pow_nonneg hLpos.le c
  calc 3 / 4 * L ^ c ≤ L ^ c * (1 + c * -(Real.log 2 / L)) := by nlinarith
    _ ≤ L ^ c * (1 + -(Real.log 2 / L)) ^ c := mul_le_mul_of_nonneg_left hb hLc
    _ = (L - Real.log 2) ^ c := h2.symm
    _ ≤ _ := h1

end lemma22

lemma extNb_sdiff (U X Y : Finset V) (F : Finset (Sym2 V)) :
    extNb G (U \ X) Y F = extNb G U Y F \ X := by
  ext v; simp only [extNb, Finset.mem_filter, Finset.mem_sdiff]; tauto

lemma card_le_of_degIn {U : Finset V} {v : V} : degIn G U v ≤ U.card :=
  Finset.card_filter_le _ _

/-- **Lemma 2.2** (deterministic form): deleting a small set `X` from a `(1/8, c, s)`-expander
of minimum degree at least `D` leaves a `(1/16, c, s)`-expander. -/
lemma expander_delete {U X : Finset V} {c : ℕ} {D s N A : ℝ}
    (hexp : IsExpander G U (1 / 8) c s) (hdeg : ∀ v ∈ U, D ≤ degIn G U v) (hs : s ≤ D / 16)
    (hXU : X ⊆ U) (hX : (X.card : ℝ) ≤ A) (hA : A ≤ D / 8) (hD3 : 3 ≤ D - A)
    (hlogc : 4 * c * Real.log 2 ≤ Real.log D) (hl2 : Real.log 2 ≤ Real.log D)
    (hUN : (U.card : ℝ) ≤ N) (hkey : 48 * Real.log N ^ c * A ≤ D) :
    IsExpander G (U \ X) (1 / 16) c s := by
  intro Y hY F h1 h2 h3
  have hYne : Y.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨y0, hy0⟩ := hYne
  have hy0U : y0 ∈ U := (Finset.mem_sdiff.1 (hY hy0)).1
  have hUD : D ≤ U.card := (hdeg y0 hy0U).trans (by exact_mod_cast card_le_of_degIn)
  have hA0 : 0 ≤ A := le_trans (Nat.cast_nonneg _) hX
  have hD0 : 0 < D := by linarith
  have hUX : (U.card : ℝ) - A ≤ (U \ X).card := by
    rw [Finset.card_sdiff_of_subset hXU, Nat.cast_sub (Finset.card_le_card hXU)]; linarith
  have hlogUX : 1 ≤ Real.log (U \ X).card := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hlogUXc : 1 ≤ Real.log (U \ X).card ^ c := one_le_pow₀ hlogUX
  have hext : ((extNb G U Y F).card : ℝ) - A ≤ (extNb G (U \ X) Y F).card := by
    rw [extNb_sdiff]
    have := Finset.le_card_sdiff X (extNb G U Y F)
    have h' : ((extNb G U Y F).card : ℝ) - X.card ≤ ((extNb G U Y F \ X).card : ℝ) := by
      have : (extNb G U Y F).card ≤ (extNb G U Y F \ X).card + X.card := by omega
      have : ((extNb G U Y F).card : ℝ) ≤ (extNb G U Y F \ X).card + X.card := by exact_mod_cast this
      linarith
    linarith
  have hYpos : (0 : ℝ) < Y.card := by exact_mod_cast (show 0 < Y.card by omega)
  by_cases hsmall : (Y.card : ℝ) ≤ D / 2
  · have hF : (F.card : ℝ) ≤ D / 16 * Y.card := h3.trans (mul_le_mul_of_nonneg_right hs hYpos.le)
    have hss := small_set_nbhd (G := G) (U := U) (F := F) ⟨y0, hy0⟩
      (fun y hy => hdeg y (Finset.mem_sdiff.1 (hY hy)).1) hsmall (by linarith)
    have : 1 / 16 / Real.log (U \ X).card ^ c * Y.card ≤ Y.card / 16 := by
      rw [div_div, div_mul_eq_mul_div, one_mul]
      exact div_le_div_of_nonneg_left hYpos.le (by norm_num) (by nlinarith)
    linarith
  · push_neg at hsmall
    have hYU : Y ⊆ U := hY.trans Finset.sdiff_subset
    have hbig := hexp Y hYU F h1 (by
      have := Finset.card_le_card (Finset.sdiff_subset (s := U) (t := X)); omega) h3
    have hUpos : (0 : ℝ) < U.card := by linarith
    have hlogU1 : 1 ≤ Real.log U.card := by
      rw [Real.le_log_iff_exp_le hUpos]; have := Real.exp_one_lt_d9; linarith
    have hcmp := log_pow_compare c hUpos (m' := (U \ X).card) (by linarith)
      (hlogc.trans (Real.log_le_log hD0 hUD)) (hl2.trans (Real.log_le_log hD0 hUD))
    have hLc : 1 ≤ Real.log U.card ^ c := one_le_pow₀ hlogU1
    have hLN : Real.log U.card ^ c ≤ Real.log N ^ c :=
      pow_le_pow_left₀ (by linarith) (Real.log_le_log hUpos hUN) c
    set L := Real.log U.card ^ c
    set L' := Real.log (U \ X).card ^ c
    have hL0 : 0 < L := by linarith
    -- `A ≤ |Y| / (24 L)`
    have hAY : 24 * L * A ≤ Y.card := by nlinarith
    have e1 : 1 / 16 / L' * Y.card ≤ 1 / 12 / L * Y.card := by
      have : 1 / 16 / L' ≤ 1 / 16 / (3 / 4 * L) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hcmp
      have h2 : 1 / 16 / (3 / 4 * L) = 1 / 12 / L := by field_simp; ring
      rw [h2] at this
      exact mul_le_mul_of_nonneg_right this hYpos.le
    have e2 : 1 / 12 / L * Y.card ≤ 1 / 8 / L * Y.card - A := by
      have h2 : 1 / 8 / L * Y.card - 1 / 12 / L * Y.card = Y.card / (24 * L) := by
        field_simp; ring
      have h3 : A ≤ Y.card / (24 * L) := by rw [le_div_iff₀ (by positivity)]; linarith
      linarith
    linarith

end

end Lovasz
