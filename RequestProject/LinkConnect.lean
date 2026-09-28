module
public import RequestProject.LinkRounds
public import RequestProject.Haxell

/-!
# Connecting pairs through the random set (Lemma 5.7 and the end of the proof of Lemma 5.1)

This file is deterministic: we fix an outcome `y` of the random set `R = U.filter y` and assume
the conclusions of the probabilistic statements as hypotheses:

* (T1) every set `S ⊆ U` with `1 ≤ |S| ≤ 2|U|/3` and every forbidden set `Z` with
  `D |Z| ≤ |S|` reach at least `θ` allowed vertices within `ρ` steps through `R \ Z`;
* (T3) every expanding set `X` has a `q/2` fraction of its neighbourhood in `R`;
* `|R| < 2θ`, so that two balls of size at least `θ` inside `R` intersect.

From these we obtain (Lemma 5.7) that for any forbidden set `Z` which is not too large some
pair can be connected avoiding `Z`, and then, by Haxell's theorem, the linking property.
-/

@[expose] public section


open scoped BigOperators
open Classical

namespace Lovasz

noncomputable section

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

omit [Fintype V] in
lemma allowed_sub (U Z : Finset V) (y : V → Bool) : allowed U Z y ⊆ U := fun v hv => by
  simp only [allowed, Finset.mem_sdiff, Finset.mem_filter] at hv; exact hv.1.1

omit [Fintype V] in
lemma allowed_inter_U (U Z : Finset V) (y : V → Bool) : allowed U (Z ∩ U) y = allowed U Z y := by
  ext v
  simp only [allowed, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_inter]
  tauto

omit [Fintype V] in
lemma ballY_sub_allowed (U Z : Finset V) (y : V → Bool) (d : ℕ) (S : Finset V) :
    ballY G U Z y d S ⊆ allowed U Z y := Finset.inter_subset_right

omit [Fintype V] in
lemma ballY_mono_S {U Z : Finset V} {y : V → Bool} {d : ℕ} {S S' : Finset V} (h : S ⊆ S') :
    ballY G U Z y d S ⊆ ballY G U Z y d S' :=
  ballY_mono (fun _ h => h) h

omit [Fintype V] in
lemma ballY_mono_d {U Z : Finset V} {y : V → Bool} {d d' : ℕ} (h : d ≤ d') (S : Finset V) :
    ballY G U Z y d S ⊆ ballY G U Z y d' S :=
  Finset.inter_subset_inter (reach_mono_d _ _ h) (Finset.Subset.refl _)

omit [Fintype V] in
lemma ballY_union (U Z : Finset V) (y : V → Bool) (d : ℕ) (S S' : Finset V) :
    ballY G U Z y d (S ∪ S') = ballY G U Z y d S ∪ ballY G U Z y d S' := by
  simp only [ballY, reach_union, Finset.union_inter_distrib_right]

omit [Fintype V] in
lemma ballY_trans {U Z : Finset V} {y : V → Bool} {a b : ℕ} {S T : Finset V}
    (hT : T ⊆ ballY G U Z y a S) : ballY G U Z y b T ⊆ ballY G U Z y (a + b) S :=
  Finset.inter_subset_inter (reach_trans _ _ _ (hT.trans Finset.inter_subset_left) b)
    (Finset.Subset.refl _)

section det

variable {U : Finset V} {y : V → Bool} {θ D q Kx : ℝ} {ρ : ℕ}

/-- The hypothesis (T1): sets of moderate size reach `θ` allowed vertices. -/
def T1Prop (G : SimpleGraph V) (U : Finset V) (y : V → Bool) (θ D : ℝ) (ρ : ℕ) : Prop :=
  ∀ S ⊆ U, ∀ Z ⊆ U, 1 ≤ S.card → 3 * S.card ≤ 2 * U.card → D * Z.card ≤ S.card →
    θ ≤ (ballY G U Z y ρ S).card

omit [Fintype V] in
/-- (T1) for sets of arbitrary size, by passing to a subset. -/
lemma T1_big (hT1 : T1Prop G U y θ D ρ) {m : ℕ} (hm1 : 1 ≤ m) (hm2 : 3 * m ≤ 2 * U.card)
    {S Z : Finset V} (hS : S ⊆ U) (hZ : Z ⊆ U) (hS1 : 1 ≤ S.card) (hSZ : D * Z.card ≤ S.card)
    (hmZ : D * Z.card ≤ m) : θ ≤ (ballY G U Z y ρ S).card := by
  obtain ⟨S', hS'S, hS'c⟩ := Finset.exists_subset_card_eq (min_le_left S.card m)
  have h1 : 1 ≤ S'.card := by rw [hS'c]; exact le_min hS1 hm1
  have h2 : 3 * S'.card ≤ 2 * U.card := by rw [hS'c]; exact le_trans (by omega) hm2
  have h3 : D * Z.card ≤ S'.card := by
    rw [hS'c]
    rcases le_total S.card m with h | h
    · rw [min_eq_left h]; exact hSZ
    · rw [min_eq_right h]; exact hmZ
  exact (hT1 S' (hS'S.trans hS) Z hZ h1 h2 h3).trans
    (Nat.cast_le.2 (Finset.card_le_card (ballY_mono_S hS'S)))

omit [Fintype V] in
/-- The halving argument of Claim 5.7.1: if a set `X` of at most `2^j` vertices has a large
ball, then so does one of its vertices, at the cost of `j` extra applications of (T1). -/
lemma halving (hT1 : T1Prop G U y θ D ρ) {m : ℕ} (hm1 : 1 ≤ m) (hm2 : 3 * m ≤ 2 * U.card)
    {Z : Finset V} (hZ : Z ⊆ U) (hθ : 2 ≤ θ) (hDZ : D * Z.card ≤ θ / 2) (hmZ : D * Z.card ≤ m) :
    ∀ (j a : ℕ) (X : Finset V), X.Nonempty → X.card ≤ 2 ^ j →
      θ ≤ (ballY G U Z y a X).card → ∃ x ∈ X, θ ≤ (ballY G U Z y (a + j * ρ) {x}).card := by
  intro j
  induction j with
  | zero =>
    intro a X hX hXc hb
    obtain ⟨x, hx⟩ := hX
    have : X = {x} := by
      rw [pow_zero] at hXc
      exact Finset.eq_singleton_iff_unique_mem.2 ⟨hx, fun z hz =>
        Finset.card_le_one.1 hXc z hz x hx⟩
    subst this
    exact ⟨x, Finset.mem_singleton_self x, by simpa using hb⟩
  | succ j ih =>
    intro a X hX hXc hb
    by_cases h1 : X.card ≤ 1
    · obtain ⟨x, hx⟩ := hX
      have : X = {x} := Finset.eq_singleton_iff_unique_mem.2 ⟨hx, fun z hz =>
        Finset.card_le_one.1 h1 z hz x hx⟩
      subst this
      exact ⟨x, Finset.mem_singleton_self x, hb.trans
        (Nat.cast_le.2 (Finset.card_le_card (ballY_mono_d (by omega) _)))⟩
    push_neg at h1
    obtain ⟨X1, hX1X, hX1c⟩ := Finset.exists_subset_card_eq (Nat.div_le_self X.card 2)
    set X2 := X \ X1
    have hX2c : X2.card = X.card - X.card / 2 := by rw [Finset.card_sdiff_of_subset hX1X, hX1c]
    have hsplit : X = X1 ∪ X2 := (Finset.union_sdiff_of_subset hX1X).symm
    have hbu : (ballY G U Z y a X).card ≤ (ballY G U Z y a X1).card + (ballY G U Z y a X2).card := by
      rw [hsplit, ballY_union]; exact Finset.card_union_le _ _
    have hpow : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
    -- one of the halves has a ball of size at least `θ / 2`
    have key : ∀ X' ⊆ X, X'.Nonempty → X'.card ≤ 2 ^ j → θ / 2 ≤ (ballY G U Z y a X').card →
        ∃ x ∈ X, θ ≤ (ballY G U Z y (a + (j + 1) * ρ) {x}).card := by
      intro X' hX'X hX'n hX'c hX'b
      set S := ballY G U Z y a X'
      have hSU : S ⊆ U := (ballY_sub_allowed U Z y a X').trans (allowed_sub U Z y)
      have hS1 : (1 : ℝ) ≤ S.card := by linarith
      have hb' := T1_big hT1 hm1 hm2 hSU hZ (by exact_mod_cast hS1) (hDZ.trans hX'b) hmZ
      have hb'' : θ ≤ (ballY G U Z y (a + ρ) X').card :=
        hb'.trans (Nat.cast_le.2 (Finset.card_le_card (ballY_trans (Finset.Subset.refl _))))
      obtain ⟨x, hx, hxb⟩ := ih (a + ρ) X' hX'n hX'c hb''
      refine ⟨x, hX'X hx, hxb.trans_eq ?_⟩
      congr 3; ring
    have hc : θ / 2 ≤ (ballY G U Z y a X1).card ∨ θ / 2 ≤ (ballY G U Z y a X2).card := by
      by_contra hc
      push_neg at hc
      have : ((ballY G U Z y a X).card : ℝ) ≤ (ballY G U Z y a X1).card + (ballY G U Z y a X2).card :=
        by exact_mod_cast hbu
      linarith
    rcases hc with hc | hc
    · refine key X1 hX1X (Finset.card_pos.1 (by omega)) (by omega) hc
    · refine key X2 Finset.sdiff_subset (Finset.card_pos.1 (by omega)) (by omega) hc

/-- The hypothesis (T3): expanding sets have a `q/2` fraction of their neighbourhood in `R`. -/
def T3Prop (G : SimpleGraph V) (U : Finset V) (y : V → Bool) (q Kx : ℝ) : Prop :=
  ∀ X ⊆ U, X.Nonempty → Kx * X.card ≤ (extNb G U X ∅).card →
    q * (extNb G U X ∅).card / 2 ≤ ((extNb G U X ∅).filter (fun v => y v = true)).card

omit [Fintype V] in
/-- **Claim 5.7.1**: fewer than half of the start vertices have a small ball. -/
lemma few_bad {ι : Type*} (hT1 : T1Prop G U y θ D ρ) (hT3 : T3Prop G U y q Kx) {m k : ℕ}
    (hm1 : 1 ≤ m) (hm2 : 3 * m ≤ 2 * U.card) (hk : U.card < 2 ^ k) (hq : 0 ≤ q) (hD : 0 ≤ D)
    {Z : Finset V} (hZ : Z ⊆ U) (hθ : 2 ≤ θ) (hDZ : D * Z.card ≤ θ / 2) (hmZ : D * Z.card ≤ m)
    {I : Finset ι} (hI : I.Nonempty) {xs : ι → V} (hinj : Set.InjOn xs I) (hxU : ∀ i ∈ I, xs i ∈ U)
    (hexp : ∀ X ⊆ I.image xs, Kx * X.card ≤ (extNb G U X ∅).card)
    (hZI : (D + 1) * Z.card + 1 ≤ q * Kx * I.card / 4) :
    2 * (I.filter (fun i => ((ballY G U Z y (1 + ρ + k * ρ) {xs i}).card : ℝ) < θ)).card <
      I.card := by
  set Ib := I.filter (fun i => ((ballY G U Z y (1 + ρ + k * ρ) {xs i}).card : ℝ) < θ)
  by_contra hcon
  push_neg at hcon
  have hIb : Ib.Nonempty := Finset.card_pos.1 (by have := Finset.card_pos.2 hI; omega)
  set X1 := Ib.image xs
  have hX1c : X1.card = Ib.card :=
    Finset.card_image_of_injOn (hinj.mono (by intro i hi; exact (Finset.mem_filter.1 hi).1))
  have hX1U : X1 ⊆ U := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hv
    exact hxU i (Finset.mem_filter.1 hi).1
  have hX1n : X1.Nonempty := hIb.image xs
  set N := extNb G U X1 ∅
  have hN := hexp X1 (Finset.image_subset_image (Finset.filter_subset _ _))
  have hT := hT3 X1 hX1U hX1n hN
  set S := N.filter (fun v => y v = true) \ Z
  have hSc : ((N.filter (fun v => y v = true)).card : ℝ) - Z.card ≤ S.card := card_sdiff_ge _ _
  have hIX : (I.card : ℝ) ≤ 2 * X1.card := by rw [hX1c]; exact_mod_cast hcon
  have hS1 : D * Z.card + 1 ≤ (S.card : ℝ) := by
    have h1 : q * Kx * I.card ≤ q * Kx * (2 * X1.card) := by
      have : 0 ≤ q * Kx := by
        by_contra h; push_neg at h
        have : q * Kx * I.card ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h.le (by positivity)
        have : (0 : ℝ) ≤ Z.card := by positivity
        have : (0 : ℝ) ≤ (D + 1) * Z.card := by
          have : (0 : ℝ) ≤ D + 1 := by linarith
          positivity
        linarith
      exact mul_le_mul_of_nonneg_left hIX this
    have h2 : q * (Kx * X1.card) ≤ q * N.card := mul_le_mul_of_nonneg_left hN hq
    nlinarith
  have hSU : S ⊆ U := fun v hv => by
    simp only [S, N, extNb, Finset.mem_sdiff, Finset.mem_filter] at hv; exact hv.1.1.1.1
  have hSb : S ⊆ ballY G U Z y 1 X1 := by
    intro v hv
    have hva : v ∈ allowed U Z y := by
      simp only [S, N, extNb, allowed, Finset.mem_sdiff, Finset.mem_filter] at hv ⊢
      exact ⟨⟨hv.1.1.1.1, hv.1.2⟩, hv.2⟩
    refine Finset.mem_inter.2 ⟨nbr_subset_reach_one _ _ (Finset.mem_filter.2 ⟨hva, ?_⟩), hva⟩
    simp only [S, N, extNb, Finset.mem_sdiff, Finset.mem_filter] at hv
    obtain ⟨u, hu, hadj, -⟩ := hv.1.1.2
    exact ⟨u, hu, hadj⟩
  have hDZ0 := mul_nonneg hD (Nat.cast_nonneg (α := ℝ) Z.card)
  have hb := T1_big hT1 hm1 hm2 hSU hZ (by exact_mod_cast (by linarith : (1 : ℝ) ≤ S.card))
    (by linarith) hmZ
  have hb' : θ ≤ (ballY G U Z y (1 + ρ) X1).card :=
    hb.trans (Nat.cast_le.2 (Finset.card_le_card (ballY_trans hSb)))
  obtain ⟨x, hx, hxb⟩ := halving hT1 hm1 hm2 hZ hθ hDZ hmZ k (1 + ρ) X1 hX1n
    ((Finset.card_le_card hX1U).trans hk.le) hb'
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
  exact absurd hxb (not_le.2 (Finset.mem_filter.1 hi).2)

omit [Fintype V] in
/-- **Lemma 5.7** (deterministic form): some pair can be joined by a short path through the
allowed vertices. -/
lemma connect_one {ι : Type*} (hT1 : T1Prop G U y θ D ρ) (hT3 : T3Prop G U y q Kx) {m k : ℕ}
    (hm1 : 1 ≤ m) (hm2 : 3 * m ≤ 2 * U.card) (hk : U.card < 2 ^ k) (hq : 0 ≤ q) (hD : 0 ≤ D)
    (hR : ((U.filter (fun v => y v = true)).card : ℝ) < 2 * θ)
    {Z : Finset V} (hZ : Z ⊆ U) (hθ : 2 ≤ θ) (hDZ : D * Z.card ≤ θ / 2) (hmZ : D * Z.card ≤ m)
    {I : Finset ι} (hI : I.Nonempty) {xs ys : ι → V} (hinjx : Set.InjOn xs I)
    (hinjy : Set.InjOn ys I) (hxU : ∀ i ∈ I, xs i ∈ U) (hyU : ∀ i ∈ I, ys i ∈ U)
    (hexpx : ∀ X ⊆ I.image xs, Kx * X.card ≤ (extNb G U X ∅).card)
    (hexpy : ∀ X ⊆ I.image ys, Kx * X.card ≤ (extNb G U X ∅).card)
    (hZI : (D + 1) * Z.card + 1 ≤ q * Kx * I.card / 4) :
    ∃ i ∈ I, ∃ P : List V, IsPathL G P ∧ P.head? = some (xs i) ∧ P.getLast? = some (ys i) ∧
      (∀ w ∈ P, w = xs i ∨ w = ys i ∨ w ∈ allowed U Z y) ∧
      P.length ≤ 2 * (1 + ρ + k * ρ) + 1 := by
  set a := 1 + ρ + k * ρ
  have hx := few_bad hT1 hT3 hm1 hm2 hk hq hD hZ hθ hDZ hmZ hI hinjx hxU hexpx hZI
  have hy := few_bad hT1 hT3 hm1 hm2 hk hq hD hZ hθ hDZ hmZ hI hinjy hyU hexpy hZI
  have hx' : 2 * (I.filter (fun i => ((ballY G U Z y a {xs i}).card : ℝ) < θ)).card < I.card := hx
  have hy' : 2 * (I.filter (fun i => ((ballY G U Z y a {ys i}).card : ℝ) < θ)).card < I.card := hy
  obtain ⟨i, hi, hgx, hgy⟩ : ∃ i ∈ I, θ ≤ (ballY G U Z y a {xs i}).card ∧
      θ ≤ (ballY G U Z y a {ys i}).card := by
    by_contra hc
    push_neg at hc
    have : I ⊆ I.filter (fun i => ((ballY G U Z y a {xs i}).card : ℝ) < θ) ∪
        I.filter (fun i => ((ballY G U Z y a {ys i}).card : ℝ) < θ) := by
      intro i hi
      by_cases h : θ ≤ (ballY G U Z y a {xs i}).card
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hi, hc i hi h⟩)
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hi, not_le.1 h⟩)
    have := (Finset.card_le_card this).trans (Finset.card_union_le _ _)
    omega
  have hsubR : ∀ S, ballY G U Z y a S ⊆ U.filter (fun v => y v = true) := fun S v hv => by
    have := ballY_sub_allowed U Z y a S hv
    simp only [allowed, Finset.mem_sdiff] at this; exact this.1
  obtain ⟨v, hv1, hv2⟩ : ∃ v, v ∈ ballY G U Z y a {xs i} ∧ v ∈ ballY G U Z y a {ys i} := by
    by_contra hc
    push_neg at hc
    have hd : Disjoint (ballY G U Z y a {xs i}) (ballY G U Z y a {ys i}) :=
      Finset.disjoint_left.2 hc
    have h1 := Finset.card_le_card (Finset.union_subset (hsubR {xs i}) (hsubR {ys i}))
    rw [Finset.card_union_of_disjoint hd] at h1
    have h2 : ((ballY G U Z y a {xs i}).card : ℝ) + (ballY G U Z y a {ys i}).card ≤
        (U.filter (fun v => y v = true)).card := by exact_mod_cast h1
    linarith
  obtain ⟨P, hP, h1, h2, h3, h4⟩ :=
    exists_path_of_reach (Finset.mem_inter.1 hv1).1 (Finset.mem_inter.1 hv2).1
  exact ⟨i, hi, P, hP, h1, h2, h3, h4⟩

omit [Fintype V] in
/-- **Proof of Lemma 5.1 from (T1), (T3) and `|R| < 2θ`**, via Haxell's theorem. -/
theorem linkProp_of_T (hT1 : T1Prop G U y θ D ρ) (hT3 : T3Prop G U y q Kx) {m k : ℕ}
    (hm1 : 1 ≤ m) (hm2 : 3 * m ≤ 2 * U.card) (hk : U.card < 2 ^ k) (hq : 0 ≤ q) (hD : 0 ≤ D)
    (hR : ((U.filter (fun v => y v = true)).card : ℝ) < 2 * θ) (hθ : 2 ≤ θ) (hθm : θ / 2 ≤ m)
    (hKx : 0 < Kx) (hΛ1 : 8 * (D + 1) * (2 * (1 + ρ + k * ρ) + 1 : ℕ) + 4 ≤ q * Kx)
    (hΛ2 : 2 * D * (2 * (1 + ρ + k * ρ) + 1 : ℕ) * U.card ≤ θ * Kx) :
    LinkProp G U (U.filter (fun v => y v = true)) Kx := by
  set Λ := 2 * (1 + ρ + k * ρ) + 1 with hΛdef
  set R := U.filter (fun v => y v = true)
  intro pairs hnd hmem hexp
  set r := pairs.length
  let xs : Fin r → V := fun i => (pairs.get i).1
  let ys : Fin r → V := fun i => (pairs.get i).2
  obtain ⟨hndx, hndy, hxy⟩ := List.nodup_append.1 hnd
  have hxmem : ∀ i, xs i ∈ pairs.map Prod.fst := fun i =>
    List.mem_map.2 ⟨pairs.get i, List.get_mem _ _, rfl⟩
  have hymem : ∀ i, ys i ∈ pairs.map Prod.snd := fun i =>
    List.mem_map.2 ⟨pairs.get i, List.get_mem _ _, rfl⟩
  have hxinj : ∀ i j, xs i = xs j → i = j := by
    intro i j h
    have : (pairs.map Prod.fst)[i.val]'(by rw [List.length_map]; exact i.2) = (pairs.map Prod.fst)[j.val]'(by rw [List.length_map]; exact j.2) := by
      simp only [List.getElem_map]; exact h
    exact Fin.ext ((hndx.getElem_inj_iff).1 this)
  have hyinj : ∀ i j, ys i = ys j → i = j := by
    intro i j h
    have : (pairs.map Prod.snd)[i.val]'(by rw [List.length_map]; exact i.2) = (pairs.map Prod.snd)[j.val]'(by rw [List.length_map]; exact j.2) := by
      simp only [List.getElem_map]; exact h
    exact Fin.ext ((hndy.getElem_inj_iff).1 this)
  have hxy' : ∀ i j, xs i ≠ ys j := fun i j => hxy _ (hxmem i) _ (hymem j)
  have hxR : ∀ i, xs i ∈ U ∧ xs i ∉ R := fun i => by
    have := (hmem _ (List.get_mem pairs i)).1; exact Finset.mem_sdiff.1 this
  have hyR : ∀ i, ys i ∈ U ∧ ys i ∉ R := fun i => by
    have := (hmem _ (List.get_mem pairs i)).2; exact Finset.mem_sdiff.1 this
  have hsubE : ∀ I : Finset (Fin r), I.image xs ∪ I.image ys ⊆
      (pairs.map Prod.fst ++ pairs.map Prod.snd).toFinset := by
    intro I v hv
    rw [List.mem_toFinset, List.mem_append]
    rcases Finset.mem_union.1 hv with hv | hv
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv; exact Or.inl (hxmem i)
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv; exact Or.inr (hymem i)
  -- the size of an index set is controlled by expansion
  have hIn : ∀ I : Finset (Fin r), 2 * Kx * I.card ≤ U.card := by
    intro I
    have hd : Disjoint (I.image xs) (I.image ys) := by
      refine Finset.disjoint_left.2 fun v hv hv' => ?_
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
      obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hv'
      exact hxy' i j hj.symm
    have hc : (I.image xs ∪ I.image ys).card = 2 * I.card := by
      rw [Finset.card_union_of_disjoint hd,
        Finset.card_image_of_injective _ (fun i j h => hxinj i j h),
        Finset.card_image_of_injective _ (fun i j h => hyinj i j h)]
      ring
    have h1 := hexp _ (hsubE I)
    have h2 : (extNb G U (I.image xs ∪ I.image ys) ∅).card ≤ U.card :=
      Finset.card_le_card (fun v hv => (Finset.mem_sdiff.1 (Finset.mem_filter.1 hv).1).1)
    rw [hc] at h1
    push_cast at h1
    have : ((extNb G U (I.image xs ∪ I.image ys) ∅).card : ℝ) ≤ U.card := by exact_mod_cast h2
    linarith
  -- the hypergraphs
  let H : Fin r → Finset V → Prop := fun i e => ∃ P : List V, PathFrom G (xs i) (ys i) P ∧
    (∀ w ∈ P, w = xs i ∨ w = ys i ∨ w ∈ R) ∧ e = P.toFinset \ {xs i, ys i} ∧ P.length ≤ Λ
  have hsz : ∀ i e, H i e → e.card ≤ Λ := by
    rintro i e ⟨P, -, -, rfl, hl⟩
    exact (Finset.card_le_card Finset.sdiff_subset).trans ((List.toFinset_card_le P).trans hl)
  have hcond : ∀ I : Finset (Fin r), I.Nonempty → ∀ Z : Finset V, Z.card ≤ 2 * Λ * (I.card - 1) →
      ∃ i ∈ I, ∃ e, H i e ∧ Disjoint e Z := by
    intro I hI Z hZc
    set Z' := Z ∩ U
    have hZ'U : Z' ⊆ U := Finset.inter_subset_right
    have hZ'c : (Z'.card : ℝ) ≤ 2 * Λ * I.card := by
      have h1 : Z'.card ≤ 2 * Λ * I.card :=
        (Finset.card_le_card Finset.inter_subset_left).trans (hZc.trans
          (Nat.mul_le_mul_left _ (Nat.sub_le _ _)))
      exact_mod_cast h1
    have hI1 : (1 : ℝ) ≤ I.card := by exact_mod_cast Finset.card_pos.2 hI
    have hInI := hIn I
    have hΛ0 : (0 : ℝ) ≤ Λ := Nat.cast_nonneg _
    have hDZ : D * Z'.card ≤ θ / 2 := by
      have h1 : D * Z'.card ≤ D * (2 * Λ * I.card) := mul_le_mul_of_nonneg_left hZ'c hD
      have h2 : D * (2 * Λ * I.card) * Kx ≤ θ / 2 * Kx := by
        have : D * (2 * Λ * I.card) * Kx = D * Λ * (2 * Kx * I.card) := by ring
        rw [this]
        have : D * Λ * (2 * Kx * I.card) ≤ D * Λ * U.card :=
          mul_le_mul_of_nonneg_left hInI (by positivity)
        linarith
      have := le_of_mul_le_mul_right h2 hKx
      linarith
    have hZI : (D + 1) * Z'.card + 1 ≤ q * Kx * I.card / 4 := by
      have h1 : (D + 1) * Z'.card ≤ (D + 1) * (2 * Λ * I.card) :=
        mul_le_mul_of_nonneg_left hZ'c (by linarith)
      have h2 : (8 * (D + 1) * Λ + 4) * I.card ≤ q * Kx * I.card :=
        mul_le_mul_of_nonneg_right hΛ1 (by positivity)
      nlinarith
    obtain ⟨i, hi, P, hP, h1, h2, h3, h4⟩ := connect_one hT1 hT3 hm1 hm2 hk hq hD hR hZ'U hθ hDZ
      (hDZ.trans hθm) hI (fun i _ j _ h => hxinj i j h) (fun i _ j _ h => hyinj i j h)
      (fun i _ => (hxR i).1) (fun i _ => (hyR i).1)
      (fun X hX => hexp X (hX.trans (Finset.subset_union_left.trans (hsubE I))))
      (fun X hX => hexp X (hX.trans (Finset.subset_union_right.trans (hsubE I)))) hZI
    refine ⟨i, hi, P.toFinset \ {xs i, ys i}, ⟨P, ⟨h1, h2, hP⟩, fun w hw => ?_, rfl, h4⟩, ?_⟩
    · rcases h3 w hw with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · refine Or.inr (Or.inr ?_)
        simp only [allowed, Finset.mem_sdiff] at h; exact h.1
    · refine Finset.disjoint_left.2 fun w hw hwZ => ?_
      simp only [Finset.mem_sdiff, List.mem_toFinset, Finset.mem_insert,
        Finset.mem_singleton, not_or] at hw
      rcases h3 w hw.1 with h | h | h
      · exact hw.2.1 h
      · exact hw.2.2 h
      · simp only [allowed, Finset.mem_sdiff, Finset.mem_filter] at h
        exact h.2 (Finset.mem_inter.2 ⟨hwZ, h.1.1⟩)
  obtain ⟨f, hf, hdisj⟩ := Haxell.haxell hsz hcond
  choose P hPpath hPin hPe hPl using hf
  refine ⟨List.ofFn P, ?_, ?_⟩
  · refine List.nodup_flatten.2 ⟨fun l hl => ?_, List.pairwise_ofFn.2 fun i j hij => ?_⟩
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hl
      exact (hPpath i).2.2.2
    · have hne : i ≠ j := ne_of_lt hij
      intro w hwi hwj
      have hmemf : ∀ l, w ∈ P l → w ∈ R → w ∈ f l := fun l hw hwR => by
        rw [hPe l]
        simp only [Finset.mem_sdiff, List.mem_toFinset, Finset.mem_insert,
          Finset.mem_singleton, not_or]
        exact ⟨hw, fun h => (hxR l).2 (h ▸ hwR), fun h => (hyR l).2 (h ▸ hwR)⟩
      rcases hPin i w hwi with h | h | h
      · rcases hPin j w hwj with h' | h' | h'
        · exact hne (hxinj i j (h.symm.trans h'))
        · exact hxy' i j (h.symm.trans h')
        · exact (hxR i).2 (h ▸ h')
      · rcases hPin j w hwj with h' | h' | h'
        · exact hxy' j i (h'.symm.trans h)
        · exact hne (hyinj i j (h.symm.trans h'))
        · exact (hyR i).2 (h ▸ h')
      · exact Finset.disjoint_left.1 (hdisj i j hne) (hmemf i hwi h) (hmemf j hwj h)
  · refine List.forall₂_iff_get.2 ⟨by simp [r], fun i h1 h2 => ?_⟩
    simp only [List.get_eq_getElem, List.getElem_ofFn]
    exact ⟨hPpath ⟨i, h1⟩, hPin ⟨i, h1⟩⟩

end det

end

end Lovasz
