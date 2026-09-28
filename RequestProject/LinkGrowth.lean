module
public import RequestProject.LinkStars
public import RequestProject.ProbExtra

/-!
# One round of growth into a fresh random set (Claim 5.5.1)

For a fixed set `B` in a `(1/16, c, s)`-expander and a fresh random set `S` (each vertex
independently with probability `p`), with high probability many vertices outside `B ∪ Z` have
a neighbour in `B ∩ S`.  The two cases come from `star_or_spread`: in the star case we count
sampled centres with the Chernoff bound, in the spread case we colour the outside vertices so
that each colour class consists of independent events, and apply the Chernoff bound to every
large colour class.
-/

@[expose] public section


open scoped BigOperators
open Classical

namespace Lovasz

noncomputable section

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- The vertices of `U` outside `B ∪ Z` with a neighbour in `B` that is sampled in `y`. -/
def newSet (G : SimpleGraph V) (U B Z : Finset V) (y : V → Bool) : Finset V :=
  (U \ (B ∪ Z)).filter (fun v => ∃ b ∈ B, y b = true ∧ G.Adj b v)

lemma exp_neg_one_bounds : 0.3678 < Real.exp (-1) ∧ Real.exp (-1) < 0.3679 := by
  constructor
  · have := Real.exp_neg_one_gt_d9; norm_num at this ⊢; linarith
  · have := Real.exp_neg_one_lt_d9; norm_num at this ⊢; linarith

omit [Fintype V] in
lemma card_sdiff_ge (A Z : Finset V) : (A.card : ℝ) - Z.card ≤ (A \ Z).card := by
  have h := Finset.card_sdiff_add_card_inter A Z
  have h2 := Finset.card_le_card (Finset.inter_subset_right (s₁ := A) (s₂ := Z))
  have : A.card ≤ (A \ Z).card + Z.card := by omega
  have : (A.card : ℝ) ≤ (A \ Z).card + Z.card := by exact_mod_cast this
  linarith

/-- The star case. -/
lemma growth_of_stars {U B Z : Finset V} {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) {r t : ℕ}
    (hr : 1 ≤ r) (htp : (r : ℝ) ≤ t * p) {K : ℝ} (hK : 1 ≤ K) {g : V → Finset V}
    (hg : StarOK G U B t g)
    (hC : (B.card : ℝ) ≤ 10 * r * (Finset.univ.filter (fun b => g b ≠ ∅)).card)
    (hZ : 2000 * K * Z.card ≤ B.card) :
    ppr (fun _ : V => bern p) (fun y => ((newSet G U B Z y).card : ℝ) < B.card / (1000 * K)) ≤
      Real.exp (-(p * B.card / (100 * r))) := by
  set C := Finset.univ.filter (fun b => g b ≠ ∅) with hCdef
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hK0 : 0 < K := by linarith
  have hdet : ∀ y : V → Bool, p * C.card / 2 < cntT C y →
      (B.card : ℝ) / (1000 * K) ≤ (newSet G U B Z y).card := by
    intro y hy
    set Cy := C.filter (fun b => y b = true)
    have hsub : Cy.biUnion g \ Z ⊆ newSet G U B Z y := by
      intro v hv
      obtain ⟨hv1, hvZ⟩ := Finset.mem_sdiff.1 hv
      obtain ⟨b, hb, hvb⟩ := Finset.mem_biUnion.1 hv1
      obtain ⟨hbC, hyb⟩ := Finset.mem_filter.1 hb
      have hgb := (Finset.mem_filter.1 hbC).2
      obtain ⟨hbB, hgsub, -, hadj⟩ := hg.1 b hgb
      have hvUB := hgsub hvb
      refine Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨(Finset.mem_sdiff.1 hvUB).1, ?_⟩,
        b, hbB, hyb, hadj v hvb⟩
      rw [Finset.mem_union, not_or]
      exact ⟨(Finset.mem_sdiff.1 hvUB).2, hvZ⟩
    have hcard : (Cy.biUnion g).card = t * Cy.card := by
      rw [Finset.card_biUnion (fun a _ b _ hab => hg.2 a b hab), mul_comm]
      rw [Finset.sum_congr rfl (fun b hb => (hg.1 b (Finset.mem_filter.1
        (Finset.mem_filter.1 hb).1).2).2.2.1), Finset.sum_const, smul_eq_mul]
    have h1 := card_sdiff_ge (Cy.biUnion g) Z
    have h2 := Finset.card_le_card hsub
    have hcnt : (cntT C y : ℝ) = Cy.card := rfl
    have h3 : ((Cy.biUnion g).card : ℝ) = t * Cy.card := by exact_mod_cast hcard
    have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
    have h4 : (t : ℝ) * (p * C.card / 2) ≤ t * Cy.card :=
      mul_le_mul_of_nonneg_left (by rw [← hcnt]; exact hy.le) ht0
    have h5 : (r : ℝ) * C.card ≤ t * p * C.card :=
      mul_le_mul_of_nonneg_right htp (Nat.cast_nonneg _)
    have h6 : (B.card : ℝ) / (1000 * K) ≤ B.card / 1000 :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num) (by nlinarith)
    have h7 : (Z.card : ℝ) ≤ B.card / 2000 := by
      have : (Z.card : ℝ) ≤ K * Z.card := le_mul_of_one_le_left (Nat.cast_nonneg _) hK
      linarith
    have h8 : ((newSet G U B Z y).card : ℝ) ≥ (Cy.biUnion g \ Z).card := by exact_mod_cast h2
    nlinarith
  calc ppr (fun _ : V => bern p) (fun y => ((newSet G U B Z y).card : ℝ) < B.card / (1000 * K))
      ≤ ppr (fun _ : V => bern p) (fun y => (cntT C y : ℝ) ≤ p * C.card / 2) := by
        refine ppr_mono (isPD_bern hp0.le hp1) fun y hy => ?_
        by_contra hc
        push_neg at hc
        exact absurd (hdet y hc) (not_le.2 hy)
    _ ≤ Real.exp (p * C.card / 2 - (1 - Real.exp (-1)) * p * C.card) :=
        chernoff_lower hp0.le hp1 C _
    _ ≤ Real.exp (-(p * B.card / (100 * r))) := by
        refine Real.exp_le_exp.2 ?_
        have he := exp_neg_one_bounds
        have hpc : p * B.card ≤ 10 * r * (p * C.card) := by nlinarith
        have hpc0 : 0 ≤ p * C.card := mul_nonneg hp0.le (Nat.cast_nonneg _)
        have hB' : p * B.card / (100 * r) ≤ p * C.card / 10 := by
          rw [div_le_iff₀ (by positivity)]; nlinarith
        have h1 : 0.632 * (p * C.card) ≤ (1 - Real.exp (-1)) * (p * C.card) :=
          mul_le_mul_of_nonneg_right (by linarith [he.2]) hpc0
        have h2 : (1 - Real.exp (-1)) * p * C.card = (1 - Real.exp (-1)) * (p * C.card) := by ring
        linarith

/-- The spread case. -/
lemma growth_of_spread {U B Z : Finset V} {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) {r t : ℕ}
    (hr : 1 ≤ r) (ht : 1 ≤ t) (hrp : 1 ≤ r * p) {K : ℝ} (hK : 1 ≤ K) {h : V → Finset V}
    (hh : SpreadOK G U B r t h)
    (hX : (B.card : ℝ) ≤ 64 * K * (Finset.univ.filter (fun x => h x ≠ ∅)).card)
    (hZ : 2000 * K * Z.card ≤ B.card) :
    ppr (fun _ : V => bern p) (fun y => ((newSet G U B Z y).card : ℝ) < B.card / (1000 * K)) ≤
      (2 * r * t) * Real.exp (-(B.card / (2000 * (2 * r * t) * K))) := by
  set X := Finset.univ.filter (fun x => h x ≠ ∅) with hXdef
  set Kc := 2 * r * t with hKcdef
  have hKc : 0 < Kc := by positivity
  have hK0 : 0 < K := by linarith
  have hμ : IsPD (fun _ : V => bern p) := isPD_bern hp0.le hp1
  set load : V → ℕ := fun b => (Finset.univ.filter (fun x => b ∈ h x)).card
  -- colouring
  have hdeg : ∀ x ∈ X, (X.filter (fun y => y ≠ x ∧ ¬ Disjoint (h x) (h y))).card < Kc := by
    intro x hx
    have hxne := (Finset.mem_filter.1 hx).2
    obtain ⟨-, hxB, hxr, -⟩ := hh.1 x hxne
    have hsub : X.filter (fun y => y ≠ x ∧ ¬ Disjoint (h x) (h y)) ⊆
        (h x).biUnion (fun b => (Finset.univ.filter (fun y => b ∈ h y)).erase x) := by
      intro y hy
      obtain ⟨-, hyx, hd⟩ := Finset.mem_filter.1 hy
      obtain ⟨b, hbx, hby⟩ := Finset.not_disjoint_iff.1 hd
      exact Finset.mem_biUnion.2 ⟨b, hbx, Finset.mem_erase.2 ⟨hyx, by simpa using hby⟩⟩
    refine lt_of_le_of_lt (Finset.card_le_card hsub) (lt_of_le_of_lt Finset.card_biUnion_le ?_)
    calc ∑ b ∈ h x, ((Finset.univ.filter (fun y => b ∈ h y)).erase x).card
        ≤ ∑ b ∈ h x, (2 * t - 1) := Finset.sum_le_sum fun b hb => by
          rw [Finset.card_erase_of_mem (by simpa using hb)]
          have := hh.2 b (hxB hb)
          omega
      _ = r * (2 * t - 1) := by rw [Finset.sum_const, smul_eq_mul, hxr]
      _ < Kc := by
          simp only [Kc]
          have : r * (2 * t - 1) + r = 2 * r * t := by
            have : 2 * t - 1 + 1 = 2 * t := by omega
            calc r * (2 * t - 1) + r = r * (2 * t - 1 + 1) := by ring
              _ = 2 * r * t := by rw [this]; ring
          omega
  obtain ⟨col, hcol⟩ := exists_coloring Kc hKc (fun x y => ¬ Disjoint (h x) (h y))
    (fun x y hxy => fun hd => hxy hd.symm) X (by intro x hx; convert hdeg x hx)
  set Q : Fin Kc → Finset V := fun k => X.filter (fun x => col x = k)
  set E : V → (V → Bool) → Prop := fun x y => ∃ b ∈ h x, y b = true
  set big := Finset.univ.filter (fun k : Fin Kc => (X.card : ℝ) / (2 * Kc) ≤ (Q k).card)
  have hsumQ : ∑ k, (Q k).card = X.card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := col) (t := Finset.univ) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))]
  have hsumQE : ∀ y, ∑ k, ((Q k).filter (fun x => E x y)).card = (X.filter (fun x => E x y)).card := by
    intro y
    rw [Finset.card_eq_sum_card_fiberwise (f := col) (t := Finset.univ) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    ext x; simp only [Q, Finset.mem_filter]; tauto
  have hbig : (X.card : ℝ) / 2 ≤ ∑ k ∈ big, ((Q k).card : ℝ) := by
    have h1 : ∑ k ∈ Finset.univ.filter (fun k : Fin Kc => ¬ (X.card : ℝ) / (2 * Kc) ≤ (Q k).card),
        ((Q k).card : ℝ) ≤ X.card / 2 := by
      calc _ ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin Kc => ¬ (X.card : ℝ) / (2 * Kc) ≤ (Q k).card),
            (X.card : ℝ) / (2 * Kc) := Finset.sum_le_sum fun k hk =>
              (not_le.1 (Finset.mem_filter.1 hk).2).le
        _ ≤ ∑ k : Fin Kc, (X.card : ℝ) / (2 * Kc) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun _ _ _ => by positivity)
        _ = X.card / 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            field_simp
    have h2 := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun k : Fin Kc => (X.card : ℝ) / (2 * Kc) ≤ (Q k).card) (fun k => ((Q k).card : ℝ))
    have h3 : ∑ k, ((Q k).card : ℝ) = X.card := by exact_mod_cast hsumQ
    linarith
  -- deterministic part
  have hdet : ∀ y : V → Bool, (∀ k ∈ big, 0.3 * ((Q k).card : ℝ) <
      ((Q k).filter (fun x => E x y)).card) →
      (B.card : ℝ) / (1000 * K) ≤ (newSet G U B Z y).card := by
    intro y hy
    have hsub : X.filter (fun x => E x y) \ Z ⊆ newSet G U B Z y := by
      intro v hv
      obtain ⟨hv1, hvZ⟩ := Finset.mem_sdiff.1 hv
      obtain ⟨hvX, b, hb, hyb⟩ := Finset.mem_filter.1 hv1
      obtain ⟨hvUB, hsubB, -, hadj⟩ := hh.1 v (Finset.mem_filter.1 hvX).2
      refine Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨(Finset.mem_sdiff.1 hvUB).1, ?_⟩,
        b, hsubB hb, hyb, (hadj b hb).symm⟩
      rw [Finset.mem_union, not_or]
      exact ⟨(Finset.mem_sdiff.1 hvUB).2, hvZ⟩
    have h1 : (0.15 : ℝ) * X.card ≤ (X.filter (fun x => E x y)).card := by
      have := hsumQE y
      have h2 : ∑ k ∈ big, (((Q k).filter (fun x => E x y)).card : ℝ) ≤
          ∑ k, (((Q k).filter (fun x => E x y)).card : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => by positivity)
      have h3 : ∑ k ∈ big, 0.3 * ((Q k).card : ℝ) ≤
          ∑ k ∈ big, (((Q k).filter (fun x => E x y)).card : ℝ) :=
        Finset.sum_le_sum fun k hk => (hy k hk).le
      rw [← Finset.mul_sum] at h3
      have h4 : (∑ k, (((Q k).filter (fun x => E x y)).card : ℝ)) =
          (X.filter (fun x => E x y)).card := by exact_mod_cast this
      linarith
    have h2 := card_sdiff_ge (X.filter (fun x => E x y)) Z
    have h3 := Finset.card_le_card hsub
    have h4 : ((newSet G U B Z y).card : ℝ) ≥ (X.filter (fun x => E x y) \ Z).card := by
      exact_mod_cast h3
    have h5 : (B.card : ℝ) / (1000 * K) * (1000 * K) = B.card := by field_simp
    have h6 : (Z.card : ℝ) * (2000 * K) ≤ B.card := by linarith
    have h7 : (X.card : ℝ) * (64 * K) ≥ B.card := by linarith
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  -- probability of the event in one colour class
  have hEprob : ∀ x ∈ X, 1 - Real.exp (-1) ≤ ppr (fun _ : V => bern p) (E x) := by
    intro x hx
    obtain ⟨-, -, hxr, -⟩ := hh.1 x (Finset.mem_filter.1 hx).2
    have e1 : ppr (fun _ : V => bern p) (E x) =
        1 - ppr (fun _ : V => bern p) (fun y => ∀ b ∈ h x, y b = false) := by
      rw [← ppr_not hμ]
      congr 1; funext y
      simp only [E]
      apply propext
      constructor
      · rintro ⟨b, hb, hyb⟩ hall; rw [hall b hb] at hyb; exact Bool.false_ne_true hyb
      · intro hn; push_neg at hn; obtain ⟨b, hb, hyb⟩ := hn
        exact ⟨b, hb, by simpa using hyb⟩
    rw [e1, ppr_none_true, hxr]
    have h1 : (1 - p) ^ r ≤ Real.exp (-p) ^ r :=
      pow_le_pow_left₀ (by linarith) (by have := Real.add_one_le_exp (-p); linarith) r
    have h2 : Real.exp (-p) ^ r = Real.exp (-(r * p)) := by
      rw [← Real.exp_nat_mul]; ring_nf
    have h3 : Real.exp (-(r * p)) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
    linarith
  have hclass : ∀ k ∈ big, ppr (fun _ : V => bern p)
      (fun y => (((Q k).filter (fun x => E x y)).card : ℝ) ≤ 0.3 * (Q k).card) ≤
      Real.exp (-(0.099 * (X.card / (2 * Kc)))) := by
    intro k hk
    have hQk := (Finset.mem_filter.1 hk).2
    have hdep : ∀ c ∈ Q k, ∀ x y : V → Bool, (∀ i ∈ h c, x i = y i) → (E c x ↔ E c y) := by
      intro c _ x y hxy
      simp only [E]
      exact ⟨fun ⟨b, hb, hyb⟩ => ⟨b, hb, (hxy b hb) ▸ hyb⟩,
        fun ⟨b, hb, hyb⟩ => ⟨b, hb, (hxy b hb).symm ▸ hyb⟩⟩
    have hdisj : ∀ c ∈ Q k, ∀ d ∈ Q k, c ≠ d → Disjoint (h c) (h d) := by
      intro c hc d hd hcd
      obtain ⟨hcX, hck⟩ := Finset.mem_filter.1 hc
      obtain ⟨hdX, hdk⟩ := Finset.mem_filter.1 hd
      by_contra hnd
      exact hcol c hcX d hdX hcd hnd (hck.trans hdk.symm)
    have hπ : ∀ c ∈ Q k, 1 - Real.exp (-1) ≤ ppr (fun _ : V => bern p) (E c) :=
      fun c hc => hEprob c (Finset.mem_filter.1 hc).1
    have hc := chernoff_indep hμ (Q k) E h hdep hdisj hπ (0.3 * ((Q k).card : ℝ))
    refine le_trans (le_of_eq (by congr!)) (hc.trans ?_)
    refine Real.exp_le_exp.2 ?_
    have he := exp_neg_one_bounds
    have hq : (0 : ℝ) ≤ (Q k).card := Nat.cast_nonneg _
    have h3 : (1 - Real.exp (-1)) * (1 - Real.exp (-1)) ≥ 0.3995 := by nlinarith
    have h4 : (1 - Real.exp (-1)) * (1 - Real.exp (-1)) * (Q k).card ≥ 0.3995 * (Q k).card :=
      mul_le_mul_of_nonneg_right h3 hq
    linarith
  calc ppr (fun _ : V => bern p) (fun y => ((newSet G U B Z y).card : ℝ) < B.card / (1000 * K))
      ≤ ppr (fun _ : V => bern p) (fun y => ∃ k ∈ big,
          (((Q k).filter (fun x => E x y)).card : ℝ) ≤ 0.3 * (Q k).card) := by
        refine ppr_mono hμ fun y hy => ?_
        by_contra hc
        push_neg at hc
        exact absurd (hdet y hc) (not_le.2 hy)
    _ ≤ ∑ k ∈ big, ppr (fun _ : V => bern p)
          (fun y => (((Q k).filter (fun x => E x y)).card : ℝ) ≤ 0.3 * (Q k).card) :=
        ppr_exists_le hμ _ _
    _ ≤ ∑ k ∈ big, Real.exp (-(0.099 * (X.card / (2 * Kc)))) := Finset.sum_le_sum hclass
    _ ≤ ∑ k : Fin Kc, Real.exp (-(0.099 * (X.card / (2 * Kc)))) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => by positivity)
    _ = Kc * Real.exp (-(0.099 * (X.card / (2 * Kc)))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ (2 * r * t) * Real.exp (-(B.card / (2000 * (2 * r * t) * K))) := by
        have hKcR : ((Kc : ℕ) : ℝ) = 2 * r * t := by simp [Kc]
        rw [hKcR]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
        rw [neg_le_neg_iff, ← hKcR]
        have hKcpos : (0 : ℝ) < Kc := by exact_mod_cast hKc
        rw [div_le_iff₀ (by positivity)]
        have : 0.099 * (X.card / (2 * (Kc : ℝ))) * (2000 * Kc * K) = 99 * X.card * K := by
          field_simp; ring
        rw [this]
        nlinarith

/-- **Claim 5.5.1** (one round of growth), with `r = ⌈1/p⌉` and `t = r²`. -/
theorem growth_step {U B Z : Finset V} {c : ℕ} {s p : ℝ} (hexp : IsExpander G U (1 / 16) c s)
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hL : 1 ≤ Real.log U.card ^ c)
    (hrL : 13 * Real.log U.card ^ c ≤ (⌈1 / p⌉₊ : ℝ)) (hs : 4 * (⌈1 / p⌉₊ : ℝ) ^ 3 ≤ s)
    (hB : B ⊆ U) (h1 : 1 ≤ B.card) (h2 : 3 * B.card ≤ 2 * U.card)
    (hZ : 2000 * Real.log U.card ^ c * Z.card ≤ B.card) :
    ppr (fun _ : V => bern p) (fun y => ((newSet G U B Z y).card : ℝ) <
        B.card / (1000 * Real.log U.card ^ c)) ≤
      Real.exp (-(p * B.card / (100 * ⌈1 / p⌉₊))) +
        2 * (⌈1 / p⌉₊ : ℝ) ^ 3 * Real.exp (-(B.card / (4000 * (⌈1 / p⌉₊ : ℝ) ^ 3 *
          Real.log U.card ^ c))) := by
  set r := ⌈1 / p⌉₊ with hrdef
  have hr13 : (13 : ℝ) ≤ r := by linarith
  have hr1 : 1 ≤ r := by exact_mod_cast (show (1 : ℝ) ≤ r by linarith)
  have hrp : 1 ≤ (r : ℝ) * p := by
    have := Nat.le_ceil (1 / p)
    rw [← hrdef] at this
    have h := mul_le_mul_of_nonneg_right this hp0.le
    rwa [one_div, inv_mul_cancel₀ hp0.ne'] at h
  have hμ : IsPD (fun _ : V => bern p) := isPD_bern hp0.le hp1
  have hE1 : 0 ≤ Real.exp (-(p * B.card / (100 * r))) := (Real.exp_pos _).le
  have hE2 : 0 ≤ 2 * (r : ℝ) ^ 3 * Real.exp (-(B.card / (4000 * (r : ℝ) ^ 3 *
      Real.log U.card ^ c))) := by positivity
  have hrt : r ≤ r * r := Nat.le_mul_of_pos_left _ (by omega)
  have hr2 : 2 ≤ r := by exact_mod_cast (show (2 : ℝ) ≤ r by linarith)
  have ht2 : 2 ≤ r * r := le_trans hr2 hrt
  have hs' : 4 * (r : ℝ) * ((r * r : ℕ) : ℝ) ≤ s := by push_cast; nlinarith
  rcases star_or_spread hexp hB h1 h2 hr1 hrt ht2 hs' hL hrL with ⟨g, hg, hC⟩ | ⟨h, hh, hX⟩
  · have htp : (r : ℝ) ≤ ((r * r : ℕ) : ℝ) * p := by
      push_cast; nlinarith
    have := growth_of_stars hp0 hp1 hr1 htp hL hg hC hZ
    linarith
  · have := growth_of_spread hp0 hp1 hr1 (le_trans (by norm_num) ht2) hrp hL hh hX hZ
    have e : ((2 * r * (r * r) : ℕ) : ℝ) = 2 * (r : ℝ) ^ 3 := by push_cast; ring
    have e2 : (2 * (r : ℝ) * ((r * r : ℕ) : ℝ)) = 2 * (r : ℝ) ^ 3 := by push_cast; ring
    rw [e2] at this
    have e3 : (2000 * (2 * (r : ℝ) ^ 3) * Real.log U.card ^ c) =
        4000 * (r : ℝ) ^ 3 * Real.log U.card ^ c := by ring
    rw [e3] at this
    linarith

end

end Lovasz
