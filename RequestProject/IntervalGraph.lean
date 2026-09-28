module
public import RequestProject.Detour

/-!
# The interval graph `G'_M` (Claim 2.12)

`mult I J` is the number of edges of `M` between the intervals `I` and `J`.  The simple graph
`IG` joins two intervals if exactly one edge of `M` runs between them; it has maximum degree at
most `t`.  Either many ordered pairs of first-half/second-half intervals are joined by at least two
edges of `M` (and then a detour path uses many edges of `M`), or the degree sum of `IG` is almost
`t` times the number of intervals.
-/

@[expose] public section


open Classical

namespace Lovasz

namespace Conc

variable {n t : ℕ}

lemma card_filter_fin_range (m a b : ℕ) (h : b ≤ m) :
    (Finset.univ.filter (fun u : Fin m => a ≤ u.val ∧ u.val < b)).card = b - a := by
  have : (Finset.univ.filter (fun u : Fin m => a ≤ u.val ∧ u.val < b)).map Fin.valEmbedding =
      Finset.Ico a b := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact hu
    · intro hx; exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [← Finset.card_map, this, Nat.card_Ico]

/-- Every vertex has a partner in `M`. -/
lemma exists_Mrel {f : Fin n → Fin n} (hf : Function.Bijective f) (u : Fin (2 * n)) :
    ∃ v, Mrel n f u v := by
  by_cases hu : u.val < n
  · exact ⟨⟨n + (f ⟨u.val, hu⟩).val, by omega⟩, Or.inl ⟨hu, rfl⟩⟩
  · obtain ⟨i, hi⟩ := hf.2 ⟨u.val - n, by omega⟩
    refine ⟨⟨i.val, by omega⟩, Or.inr ⟨i.2, ?_⟩⟩
    simp only [hi]; omega

/-- `M` joins the two halves. -/
lemma Mrel_half {f : Fin n → Fin n} {u v : Fin (2 * n)} (h : Mrel n f u v) :
    (u.val < n ↔ ¬ v.val < n) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-- An interval lies in the first half iff its index is `< Q`. -/
lemma iv_half {u : Fin (2 * n)} {k : Fin (2 * nQ n t)} (h : ivOf t n u = some k) :
    (u.val < n ↔ k.val < nQ n t) := by
  rw [ivOf_eq_some] at h
  constructor
  · intro hu
    by_contra hk
    have := st_ge_half (n := n) (t := t) (not_lt.1 hk); omega
  · intro hk
    have := st_lt_half (n := n) (t := t) hk; omega

lemma card_iv (k : Fin (2 * nQ n t)) :
    (Finset.univ.filter (fun u : Fin (2 * n) => ivOf t n u = some k)).card = t := by
  have e : (Finset.univ.filter (fun u : Fin (2 * n) => ivOf t n u = some k)) =
      Finset.univ.filter (fun u : Fin (2 * n) => st n t k ≤ u.val ∧ u.val < st n t k + t) := by
    ext u; simp [ivOf_eq_some]
  rw [e, card_filter_fin_range _ _ _ (by have := st_lt_top (n := n) (t := t) k.2; omega)]
  omega

variable (t) (f : Fin n → Fin n)

/-- The edges of `M` between the intervals `I` and `J`, as ordered pairs. -/
noncomputable def mpairs (I J : Fin (2 * nQ n t)) : Finset (Fin (2 * n) × Fin (2 * n)) :=
  Finset.univ.filter (fun p => ivOf t n p.1 = some I ∧ ivOf t n p.2 = some J ∧ Mrel n f p.1 p.2)

/-- The number of edges of `M` between two intervals. -/
noncomputable def mult (I J : Fin (2 * nQ n t)) : ℕ := (mpairs t f I J).card

variable {t f}

lemma mem_mpairs {I J : Fin (2 * nQ n t)} {p : Fin (2 * n) × Fin (2 * n)} :
    p ∈ mpairs t f I J ↔ ivOf t n p.1 = some I ∧ ivOf t n p.2 = some J ∧ Mrel n f p.1 p.2 := by
  simp [mpairs]

lemma mult_symm (I J : Fin (2 * nQ n t)) : mult t f I J = mult t f J I := by
  unfold mult
  refine Finset.card_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_coe, mem_mpairs] at hp ⊢
    exact ⟨hp.2.1, hp.1, Mrel_symm hp.2.2⟩
  · intro p hp
    rw [Finset.mem_coe, mem_mpairs] at hp ⊢
    exact ⟨hp.2.1, hp.1, Mrel_symm hp.2.2⟩
  · intro p _; rfl
  · intro p _; rfl

/-- Pairs with positive multiplicity lie in different halves. -/
lemma half_of_mult_pos {I J : Fin (2 * nQ n t)} (h : 0 < mult t f I J) :
    (I.val < nQ n t ↔ ¬ J.val < nQ n t) := by
  obtain ⟨p, hp⟩ := Finset.card_pos.1 h
  rw [mem_mpairs] at hp
  rw [← iv_half hp.1, ← iv_half hp.2.1]
  exact Mrel_half hp.2.2

lemma mult_self (I : Fin (2 * nQ n t)) : mult t f I I = 0 := by
  by_contra h
  have := half_of_mult_pos (Nat.pos_of_ne_zero h)
  tauto

/-- The multiplicities out of an interval sum to at most `t`. -/
lemma sum_mult_le (hf : Function.Injective f) (I : Fin (2 * nQ n t)) :
    ∑ J, mult t f I J ≤ t := by
  unfold mult
  rw [← Finset.card_biUnion]
  · refine le_trans ?_ (card_iv (n := n) I).le
    refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
    · intro p hp
      rw [Finset.mem_coe, Finset.mem_biUnion] at hp
      obtain ⟨J, -, hJ⟩ := hp
      rw [mem_mpairs] at hJ
      simpa using hJ.1
    · intro p hp q hq e
      rw [Finset.mem_coe, Finset.mem_biUnion] at hp hq
      obtain ⟨J, -, hJ⟩ := hp
      obtain ⟨J', -, hJ'⟩ := hq
      rw [mem_mpairs] at hJ hJ'
      have h3 := hJ.2.2
      rw [e] at h3
      exact Prod.ext e (Mrel_uniq hf h3 hJ'.2.2)
  · intro J _ J' _ hJJ
    refine Finset.disjoint_left.2 fun p hp hq => hJJ ?_
    rw [mem_mpairs] at hp hq
    exact Option.some.inj (hp.2.1.symm.trans hq.2.1)

lemma mult_le (hf : Function.Injective f) (I J : Fin (2 * nQ n t)) : mult t f I J ≤ t :=
  le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ J))
    (sum_mult_le hf I)

variable (t f)

/-- **The interval graph `G'_M`**: two intervals are adjacent if exactly one edge of `M` runs
between them. -/
noncomputable def IG : SimpleGraph (Fin (2 * nQ n t)) where
  Adj I J := I ≠ J ∧ mult t f I J = 1
  symm := ⟨fun I J h => ⟨h.1.symm, by rw [mult_symm]; exact h.2⟩⟩
  loopless := ⟨fun I h => h.1 rfl⟩

variable {t f}

lemma degIn_IG_le (hf : Function.Injective f) (I : Fin (2 * nQ n t)) :
    degIn (IG t f) Finset.univ I ≤ t := by
  unfold degIn
  refine le_trans ?_ (sum_mult_le hf I)
  rw [Finset.card_eq_sum_ones]
  refine le_trans (Finset.sum_le_sum (fun J hJ => ?_)) (Finset.sum_le_sum_of_subset
    (Finset.filter_subset (fun J => (IG t f).Adj I J) Finset.univ))
  simp only [Finset.mem_filter] at hJ
  exact le_of_eq hJ.2.2.symm

/-- Pointwise: the multiplicities out of `I` are at most the degree plus the heavy part. -/
lemma sum_mult_le_deg (I : Fin (2 * nQ n t)) :
    ∑ J, mult t f I J ≤ degIn (IG t f) Finset.univ I +
      ∑ J, (if 2 ≤ mult t f I J then mult t f I J else 0) := by
  unfold degIn
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun J _ => ?_
  by_cases h1 : mult t f I J = 1
  · have hIJ : I ≠ J := by rintro rfl; rw [mult_self] at h1; omega
    have : (IG t f).Adj I J := ⟨hIJ, h1⟩
    rw [if_pos this, h1]; simp
  · have : ¬ (IG t f).Adj I J := fun h => h1 h.2
    rw [if_neg this]
    split_ifs with h2
    · omega
    · omega

/-- The covered vertices number `2Qt`. -/
lemma card_covered :
    (Finset.univ.filter (fun u : Fin (2 * n) => (ivOf t n u).isSome)).card = 2 * nQ n t * t := by
  have e : Finset.univ.filter (fun u : Fin (2 * n) => (ivOf t n u).isSome) =
      Finset.univ.biUnion (fun k : Fin (2 * nQ n t) =>
        Finset.univ.filter (fun u : Fin (2 * n) => ivOf t n u = some k)) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · intro h; exact ⟨(ivOf t n u).get h, by simp⟩
    · rintro ⟨k, hk⟩; rw [hk]; rfl
  rw [e, Finset.card_biUnion]
  · simp [card_iv]
  · intro k _ k' _ hkk
    refine Finset.disjoint_left.2 fun u hu hu' => hkk ?_
    simp only [Finset.mem_filter] at hu hu'
    exact Option.some.inj (hu.2.symm.trans hu'.2)

/-- The total multiplicity: `4Qt ≤ Σ_{I,J} mult I J + 2n`. -/
lemma total_mult_ge (hf : Function.Bijective f) :
    2 * (2 * nQ n t * t) ≤ (∑ I, ∑ J, mult t f I J) + 2 * n := by
  set C := Finset.univ.filter (fun u : Fin (2 * n) => (ivOf t n u).isSome) with hC
  set Pc := Finset.univ.filter (fun p : Fin (2 * n) × Fin (2 * n) =>
    (ivOf t n p.1).isSome ∧ (ivOf t n p.2).isSome ∧ Mrel n f p.1 p.2) with hPc
  set P1 := Finset.univ.filter (fun p : Fin (2 * n) × Fin (2 * n) =>
    (ivOf t n p.1).isSome ∧ Mrel n f p.1 p.2) with hP1
  set P2 := Finset.univ.filter (fun p : Fin (2 * n) × Fin (2 * n) =>
    (ivOf t n p.1).isSome ∧ ¬ (ivOf t n p.2).isSome ∧ Mrel n f p.1 p.2) with hP2
  have hsum : ∑ I, ∑ J, mult t f I J = Pc.card := by
    unfold mult
    rw [← Finset.sum_product', ← Finset.card_biUnion]
    · congr 1
      ext p
      simp only [Finset.mem_biUnion, Finset.mem_product, Finset.mem_univ, true_and, mem_mpairs,
        hPc, Finset.mem_filter]
      constructor
      · rintro ⟨IJ, h1, h2, h3⟩; exact ⟨by rw [h1]; rfl, by rw [h2]; rfl, h3⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨((ivOf t n p.1).get h1, (ivOf t n p.2).get h2), by simp, by simp, h3⟩
    · intro IJ _ IJ' _ hne
      refine Finset.disjoint_left.2 fun p hp hp' => hne ?_
      rw [mem_mpairs] at hp hp'
      exact Prod.ext (Option.some.inj (hp.1.symm.trans hp'.1))
        (Option.some.inj (hp.2.1.symm.trans hp'.2.1))
  have h1 : P1.card = C.card := by
    refine Finset.card_nbij' Prod.fst (fun u => (u, (exists_Mrel hf u).choose)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [hP1, hC, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hp ⊢
      exact hp.1
    · intro u hu
      simp only [hP1, hC, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hu ⊢
      exact ⟨hu, (exists_Mrel hf u).choose_spec⟩
    · intro p hp
      simp only [hP1, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hp
      exact Prod.ext rfl (Mrel_uniq hf.1 (exists_Mrel hf p.1).choose_spec hp.2)
    · intro u _; rfl
  have h2 : P1.card ≤ Pc.card + P2.card := by
    refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
    intro p hp
    simp only [hP1, hPc, hP2, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union] at hp ⊢
    by_cases h : (ivOf t n p.2).isSome
    · exact Or.inl ⟨hp.1, h, hp.2⟩
    · exact Or.inr ⟨hp.1, h, hp.2⟩
  have h3 : P2.card + C.card ≤ 2 * n := by
    have hCc : (Finset.univ.filter (fun u : Fin (2 * n) => ¬ (ivOf t n u).isSome)).card +
        C.card = 2 * n := by
      rw [hC, add_comm, Finset.card_filter_add_card_filter_not]; simp
    have : P2.card ≤ (Finset.univ.filter (fun u : Fin (2 * n) => ¬ (ivOf t n u).isSome)).card := by
      refine Finset.card_le_card_of_injOn Prod.snd ?_ ?_
      · intro p hp
        simp only [hP2, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hp ⊢
        exact hp.2.1
      · intro p hp q hq e
        simp only [hP2, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hp hq
        have a := Mrel_symm hp.2.2
        have b := Mrel_symm hq.2.2
        rw [e] at a
        exact Prod.ext (Mrel_uniq hf.1 a b) e
    omega
  have hCcard : C.card = 2 * nQ n t * t := card_covered
  omega

/-- Ordered pairs of intervals, the first in the first half, joined by at least two edges
of `M`. -/
noncomputable def heavy (t : ℕ) (f : Fin n → Fin n) : Finset (Fin (2 * nQ n t) × Fin (2 * nQ n t)) :=
  Finset.univ.filter (fun p => p.1.val < nQ n t ∧ 2 ≤ mult t f p.1 p.2)

/-- The heavy part of the multiplicities is at most `2 t |heavy|`. -/
lemma heavy_sum_le (hf : Function.Injective f) :
    (∑ I, ∑ J, (if 2 ≤ mult t f I J then mult t f I J else 0)) ≤ 2 * t * (heavy t f).card := by
  set H := Finset.univ.filter (fun p : Fin (2 * nQ n t) × Fin (2 * nQ n t) => 2 ≤ mult t f p.1 p.2)
  have e1 : (∑ I, ∑ J, (if 2 ≤ mult t f I J then mult t f I J else 0)) =
      ∑ p ∈ H, mult t f p.1 p.2 := by
    rw [Finset.sum_filter, ← Finset.sum_product']; rfl
  have e2 : ∑ p ∈ H, mult t f p.1 p.2 ≤ ∑ p ∈ H, t :=
    Finset.sum_le_sum fun p _ => mult_le hf _ _
  have e3 : H.card ≤ 2 * (heavy t f).card := by
    rw [← Finset.card_filter_add_card_filter_not (fun p => p.1.val < nQ n t)]
    have ha : H.filter (fun p => p.1.val < nQ n t) = heavy t f := by
      ext p; simp [H, heavy, and_comm]
    have hb : (H.filter (fun p => ¬ p.1.val < nQ n t)).card ≤ (heavy t f).card := by
      refine Finset.card_le_card_of_injOn Prod.swap ?_ ?_
      · intro p hp
        simp only [H, heavy, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
          Set.mem_setOf_eq, Prod.fst_swap, Prod.snd_swap] at hp ⊢
        have hm : 0 < mult t f p.1 p.2 := by omega
        refine ⟨?_, by rw [mult_symm]; exact hp.1⟩
        have := half_of_mult_pos hm
        tauto
      · intro p _ q _ e
        exact Prod.swap_injective e
    rw [ha]; omega
  rw [Finset.sum_const, smul_eq_mul] at e2
  calc _ = ∑ p ∈ H, mult t f p.1 p.2 := e1
    _ ≤ H.card * t := e2
    _ ≤ 2 * (heavy t f).card * t := Nat.mul_le_mul_right _ e3
    _ = 2 * t * (heavy t f).card := by ring

/-- **The sparse case of Claim 2.12**: the degree sum of `IG` is at least
`4Qt - 2n - 2t |heavy|`. -/
theorem degree_sum_IG (hf : Function.Bijective f) :
    2 * (2 * nQ n t * t) ≤ (∑ I, degIn (IG t f) Finset.univ I) + 2 * t * (heavy t f).card +
      2 * n := by
  have h1 := total_mult_ge (t := t) hf
  have h2 : ∑ I, ∑ J, mult t f I J ≤ (∑ I, degIn (IG t f) Finset.univ I) +
      ∑ I, ∑ J, (if 2 ≤ mult t f I J then mult t f I J else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun I _ => sum_mult_le_deg I
  have h3 := heavy_sum_le (t := t) hf.1
  omega

end Conc

end Lovasz
