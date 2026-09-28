module
public import RequestProject.IntervalGraph

/-!
# The dense case of Claim 2.12

A maximal matching `P` in the set `heavy` of pairs of intervals joined by at least two edges of
`M` has at least `|heavy| / t` edges (every interval lies in at most `t / 2` heavy pairs), and
every pair of `P` yields a detour using two edges of `M`.
-/

@[expose] public section


open Classical

namespace Lovasz

namespace Conc

variable {n t : ℕ} {f : Fin n → Fin n}

/-- A set of pairs of intervals is a matching. -/
def IsMatch (P : Finset (Fin (2 * nQ n t) × Fin (2 * nQ n t))) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, p ≠ q → p.1 ≠ q.1 ∧ p.2 ≠ q.2

lemma exists_max_match (H : Finset (Fin (2 * nQ n t) × Fin (2 * nQ n t))) :
    ∃ P ⊆ H, IsMatch P ∧ ∀ e ∈ H, (∃ p ∈ P, p.1 = e.1) ∨ (∃ p ∈ P, p.2 = e.2) := by
  obtain ⟨P, hP, hmax⟩ := Finset.exists_max_image (H.powerset.filter IsMatch) Finset.card
    ⟨∅, by simp [IsMatch]⟩
  rw [Finset.mem_filter, Finset.mem_powerset] at hP
  refine ⟨P, hP.1, hP.2, fun e he => ?_⟩
  by_contra hne
  push_neg at hne
  have heP : e ∉ P := fun h => hne.1 e h rfl
  have hm : IsMatch (insert e P) := by
    intro p hp q hq hpq
    rw [Finset.mem_insert] at hp hq
    rcases hp with rfl | hp <;> rcases hq with rfl | hq
    · exact absurd rfl hpq
    · exact ⟨fun h => hne.1 q hq h.symm, fun h => hne.2 q hq h.symm⟩
    · exact ⟨hne.1 p hp, hne.2 p hp⟩
    · exact hP.2 p hp q hq hpq
  have := hmax (insert e P) (Finset.mem_filter.2 ⟨Finset.mem_powerset.2
    (Finset.insert_subset he hP.1), hm⟩)
  rw [Finset.card_insert_of_notMem heP] at this
  omega

lemma two_mul_card_heavy_fst (hf : Function.Injective f) (I : Fin (2 * nQ n t)) :
    2 * ((heavy t f).filter (fun p => p.1 = I)).card ≤ t := by
  refine le_trans ?_ (sum_mult_le hf I)
  have h1 : 2 * ((heavy t f).filter (fun p => p.1 = I)).card ≤
      ∑ p ∈ (heavy t f).filter (fun p => p.1 = I), mult t f I p.2 := by
    rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun p hp => ?_
    simp only [heavy, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rw [← hp.2]; exact hp.1.2
  refine h1.trans ?_
  rw [← Finset.sum_image (g := Prod.snd) (f := fun J => mult t f I J)]
  · exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  · intro p hp q hq e
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp hq
    exact Prod.ext (hp.2.trans hq.2.symm) e

lemma two_mul_card_heavy_snd (hf : Function.Injective f) (J : Fin (2 * nQ n t)) :
    2 * ((heavy t f).filter (fun p => p.2 = J)).card ≤ t := by
  refine le_trans ?_ (sum_mult_le hf J)
  have h1 : 2 * ((heavy t f).filter (fun p => p.2 = J)).card ≤
      ∑ p ∈ (heavy t f).filter (fun p => p.2 = J), mult t f J p.1 := by
    rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun p hp => ?_
    simp only [heavy, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rw [← hp.2, mult_symm]; exact hp.1.2
  refine h1.trans ?_
  rw [← Finset.sum_image (g := Prod.fst) (f := fun I => mult t f J I)]
  · exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  · intro p hp q hq e
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp hq
    exact Prod.ext e (hp.2.trans hq.2.symm)

/-- A maximal matching of `heavy` has at least `|heavy| / t` pairs. -/
lemma card_heavy_le (hf : Function.Injective f) {P : Finset (Fin (2 * nQ n t) × Fin (2 * nQ n t))}
    (hmax : ∀ e ∈ heavy t f, (∃ p ∈ P, p.1 = e.1) ∨ (∃ p ∈ P, p.2 = e.2)) :
    (heavy t f).card ≤ t * P.card := by
  have hsub : heavy t f ⊆ P.biUnion (fun p => (heavy t f).filter (fun e => e.1 = p.1) ∪
      (heavy t f).filter (fun e => e.2 = p.2)) := by
    intro e he
    rw [Finset.mem_biUnion]
    rcases hmax e he with ⟨p, hp, h⟩ | ⟨p, hp, h⟩
    · exact ⟨p, hp, Finset.mem_union_left _ (Finset.mem_filter.2 ⟨he, h.symm⟩)⟩
    · exact ⟨p, hp, Finset.mem_union_right _ (Finset.mem_filter.2 ⟨he, h.symm⟩)⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  have e : t * P.card = ∑ _p ∈ P, t := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  rw [e]
  refine Finset.sum_le_sum fun p _ => (Finset.card_union_le _ _).trans ?_
  have := two_mul_card_heavy_fst hf p.1
  have := two_mul_card_heavy_snd hf p.2
  omega

/-- Two distinct edges of `M` between heavy intervals, ordered along the first interval. -/
lemma exists_two_pairs (hf : Function.Injective f) {I J : Fin (2 * nQ n t)}
    (h : 2 ≤ mult t f I J) :
    ∃ a ∈ mpairs t f I J, ∃ b ∈ mpairs t f I J, a.1.val < b.1.val := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (show 1 < (mpairs t f I J).card from h)
  have h1 : a.1 ≠ b.1 := by
    intro e
    rw [mem_mpairs] at ha hb
    have h3 := ha.2.2
    rw [e] at h3
    exact hab (Prod.ext e (Mrel_uniq hf h3 hb.2.2))
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne h1) with h2 | h2
  · exact ⟨a, ha, b, hb, h2⟩
  · exact ⟨b, hb, a, ha, h2⟩

variable (t f)

/-- The data describing the detour at the `k`-th interval. -/
def DData (P : Finset (Fin (2 * nQ n t) × Fin (2 * nQ n t))) (k : ℕ)
    (x : (Fin (2 * nQ n t) × Fin (2 * nQ n t)) × (Fin (2 * n) × Fin (2 * n)) ×
      (Fin (2 * n) × Fin (2 * n))) : Prop :=
  x.1 ∈ P ∧ x.1.1.val = k ∧ x.2.1 ∈ mpairs t f x.1.1 x.1.2 ∧ x.2.2 ∈ mpairs t f x.1.1 x.1.2 ∧
    x.2.1.1.val < x.2.2.1.val

/-- The detour data built from a matching. -/
noncomputable def dtOf (P : Finset (Fin (2 * nQ n t) × Fin (2 * nQ n t))) : DT n := fun k =>
  if h : ∃ x, DData t f P k x then
    some (h.choose.2.1.1, h.choose.2.1.2, h.choose.2.2.1, h.choose.2.2.2) else none

/-- The second intervals of the detours. -/
noncomputable def JOf (P : Finset (Fin (2 * nQ n t) × Fin (2 * nQ n t))) (k : ℕ) : ℕ :=
  if h : ∃ x, DData t f P k x then h.choose.1.2.val else 0

variable {t f}

lemma dtOf_isSome {P : Finset (Fin (2 * nQ n t) × Fin (2 * nQ n t))} {k : ℕ} :
    (dtOf t f P k).isSome ↔ ∃ x, DData t f P k x := by
  unfold dtOf
  split_ifs with h <;> simp [h]

/-- **The dense case of Claim 2.12**: there is a path using at least `2 |heavy| / t` edges of `M`. -/
theorem dense_path (hn : 0 < n) (ht : 2 ≤ t) (hQ : 0 < nQ n t) (hf : Function.Injective f) :
    ∃ l, IsPathL (cycleMatchGraph n f) l ∧ 2 * (heavy t f).card ≤ t * countPairs (Mrel n f) l := by
  obtain ⟨P, hPH, hPm, hmax⟩ := exists_max_match (heavy t f)
  have hPH' : ∀ p ∈ P, p.1.val < nQ n t ∧ 2 ≤ mult t f p.1 p.2 := by
    intro p hp
    have := hPH hp
    simp only [heavy, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this
  -- the detour exists exactly at the first intervals of `P`
  have hiff : ∀ k, (∃ x, DData t f P k x) ↔ ∃ p ∈ P, p.1.val = k := by
    intro k
    constructor
    · rintro ⟨x, h1, h2, -⟩; exact ⟨x.1, h1, h2⟩
    · rintro ⟨p, hp, hpk⟩
      obtain ⟨a, ha, b, hb, hab⟩ := exists_two_pairs hf (hPH' p hp).2
      exact ⟨(p, a, b), hp, hpk, ha, hb, hab⟩
  have hOK : DetourOK t f (dtOf t f P) (JOf t f P) := by
    intro k hk u₁ w₁ u₂ w₂ e
    unfold dtOf at e
    split_ifs at e with h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h.choose_spec
    have e' := Option.some.inj e
    simp only [Prod.mk.injEq] at e'
    obtain ⟨rfl, rfl, rfl, rfl⟩ := e'
    have hJ : JOf t f P k = h.choose.1.2.val := by unfold JOf; rw [dif_pos h]
    rw [hJ]
    rw [mem_mpairs, ivOf_eq_some, ivOf_eq_some] at h3 h4
    rw [h2] at h3 h4
    have hm := (hPH' _ h1).2
    have hhalf := half_of_mult_pos (show 0 < mult t f h.choose.1.1 h.choose.1.2 by omega)
    have h1' := (hPH' _ h1).1
    refine ⟨h3.1.1, h5, h4.1.2, h3.2.2, h4.2.2, ?_, h.choose.1.2.2, h3.2.1.1, h3.2.1.2,
      h4.2.1.1, h4.2.1.2⟩
    have := hhalf.1 h1'
    omega
  have hJinj : ∀ k k', k < nQ n t → k' < nQ n t → k ≠ k' → (dtOf t f P k).isSome →
      (dtOf t f P k').isSome → JOf t f P k ≠ JOf t f P k' := by
    intro k k' _ _ hkk hs hs' e
    rw [dtOf_isSome] at hs hs'
    unfold JOf at e
    rw [dif_pos hs, dif_pos hs'] at e
    obtain ⟨a1, a2, -⟩ := hs.choose_spec
    obtain ⟨b1, b2, -⟩ := hs'.choose_spec
    have e2 : hs.choose.1.2 = hs'.choose.1.2 := Fin.ext e
    by_cases hpq : hs.choose.1 = hs'.choose.1
    · apply hkk; rw [← a2, ← b2, hpq]
    · exact (hPm _ a1 _ b1 hpq).2 e2
  obtain ⟨l, hl, hcount⟩ := detour_path hn ht hQ f hf (dtOf t f P) (JOf t f P) hOK hJinj
  refine ⟨l, hl, ?_⟩
  have hcard : ((Finset.range (nQ n t)).filter (fun k => (dtOf t f P k).isSome)).card = P.card := by
    have e : (Finset.range (nQ n t)).filter (fun k => (dtOf t f P k).isSome) =
        P.image (fun p => p.1.val) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, dtOf_isSome, hiff, Finset.mem_image]
      constructor
      · rintro ⟨-, h⟩; exact h
      · rintro ⟨p, hp, rfl⟩; exact ⟨(hPH' p hp).1, p, hp, rfl⟩
    rw [e, Finset.card_image_of_injOn]
    intro p hp q hq e
    by_contra hpq
    exact (hPm p hp q hq hpq).1 (Fin.ext e)
  rw [hcard] at hcount
  have := card_heavy_le hf hmax
  nlinarith

end Conc

end Lovasz
