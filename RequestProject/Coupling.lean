module
public import RequestProject.Prob

/-!
# Marginals and the coupling lemma (Lemma 2.7)
-/

@[expose] public section


open scoped BigOperators
open Classical

namespace Lovasz

noncomputable section

variable {κ : Type*} [Fintype κ]

/-- Marginalisation: an i.i.d. family indexed by `ι₂`, read along an injection `ι₁ → ι₂`,
is an i.i.d. family indexed by `ι₁`. -/
lemma pex_comp_injective {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] {ν : κ → ℝ}
    (hν : ∑ k, ν k = 1) (ψ : ι₁ → ι₂) (hψ : Function.Injective ψ) (F : (ι₁ → κ) → ℝ) :
    pex (fun _ : ι₂ => ν) (fun w => F (fun i => w (ψ i))) = pex (fun _ : ι₁ => ν) F := by
  set R := {j : ι₂ // j ∉ Set.range ψ}
  have hbij : Function.Bijective (Sum.elim ψ (fun r : R => r.1)) := by
    constructor
    · rintro (a | a) (b | b) h
      · simp only [Sum.elim_inl] at h; rw [hψ h]
      · simp only [Sum.elim_inl, Sum.elim_inr] at h; exact absurd ⟨a, h⟩ b.2
      · simp only [Sum.elim_inl, Sum.elim_inr] at h; exact absurd ⟨b, h.symm⟩ a.2
      · simp only [Sum.elim_inr] at h; rw [Subtype.ext h]
    · intro j
      by_cases hj : j ∈ Set.range ψ
      · obtain ⟨i, rfl⟩ := hj; exact ⟨Sum.inl i, rfl⟩
      · exact ⟨Sum.inr ⟨j, hj⟩, rfl⟩
  set e : ι₁ ⊕ R ≃ ι₂ := Equiv.ofBijective _ hbij
  rw [pex_reindex e]
  have he : ∀ i, e.symm (ψ i) = Sum.inl i := fun i => by
    rw [Equiv.symm_apply_eq]; rfl
  simp only [he]
  have key : ∑ x : ι₁ ⊕ R → κ, (∏ i, ν (x i)) * F (fun i => x (Sum.inl i)) =
      ∑ a : ι₁ → κ, (∏ i, ν (a i)) * F a := by
    rw [Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow ι₁ R κ) _
      (fun p => (∏ i, ν (p.1 i)) * (∏ r, ν (p.2 r)) * F p.1)
      (fun x => by simp [Fintype.prod_sum_type, Equiv.sumArrowEquivProdArrow]; left; rfl),
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show (∑ b : R → κ, (∏ i, ν (a i)) * (∏ r, ν (b r)) * F a) =
        (∏ i, ν (a i)) * F a * ∑ b : R → κ, ∏ r, ν (b r) by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b _ => by ring]
    rw [← Fintype.prod_sum (fun _ k => ν k)]
    simp [hν]
  unfold pex pwt
  convert key using 1
  · exact Finset.sum_congr (by congr; exact Subsingleton.elim _ _) fun x _ => rfl


lemma sum_boolArrow (f : (Bool → Bool) → ℝ) :
    ∑ z, f z = ∑ a : Bool, ∑ b : Bool, f (fun t => if t then b else a) := by
  rw [Fintype.sum_equiv (Equiv.boolArrowEquivProd Bool) f
    (fun p => f (fun t => if t then p.2 else p.1)) (fun z => by
      congr 1; funext t; cases t <;> simp), Fintype.sum_prod_type]

lemma pushD_and {ι : Type*} (s : ℝ) :
    pushD (fun (_ : ι) (z : Bool → Bool) => ∏ b, bern s (z b)) (fun z => z false && z true) =
      fun _ => bern (s * s) := by
  funext i c
  unfold pushD
  rw [Finset.sum_filter, sum_boolArrow]
  cases c
  · simp [bern]; ring
  · simp [bern]

lemma pushD_or {ι : Type*} (s : ℝ) :
    pushD (fun (_ : ι) (z : Bool → Bool) => ∏ b, bern s (z b)) (fun z => z false || z true) =
      fun _ => bern (2 * s - s * s) := by
  funext i c
  unfold pushD
  rw [Finset.sum_filter, sum_boolArrow]
  cases c <;> simp [bern] <;> ring


lemma ppr_split_and {α : Type*} [Fintype α] (s : ℝ) (Q : (α → Bool) → Prop) :
    ppr (fun _ : α => bern (s * s)) Q =
      ppr (fun _ : α × Bool => bern s) (fun z => Q (fun c => z (c, false) && z (c, true))) := by
  rw [← pushD_and (ι := α) s, ← ppr_map]
  unfold ppr
  exact (pex_curry (fun (_ : α) (_ : Bool) => bern s) (fun z : α × Bool → Bool =>
      if Q (fun c => z (c, false) && z (c, true)) then (1 : ℝ) else 0)).symm

lemma ppr_merge_or {α : Type*} [Fintype α] (s : ℝ) (Q : (α → Bool) → Prop) :
    ppr (fun _ : α × Bool => bern s) (fun w => Q (fun v => w (v, false) || w (v, true))) =
      ppr (fun _ : α => bern (2 * s - s * s)) Q := by
  rw [← pushD_or (ι := α) s, ← ppr_map]
  unfold ppr
  exact pex_curry (fun (_ : α) (_ : Bool) => bern s) (fun w : α × Bool → Bool =>
      if Q (fun v => w (v, false) || w (v, true)) then (1 : ℝ) else 0)

/-- The set of endpoints of the selected edges. -/
def endsSet {ι β : Type*} (E : Finset ι) (e₁ e₂ : ι → β) (x : ι → Bool) : Finset β :=
  (E.filter (fun c => x c = true)).image e₁ ∪ (E.filter (fun c => x c = true)).image e₂

/-- Existence of a slot assignment injective on the fibres of `g` when fibres have size `≤ 2`. -/
lemma exists_slot {α β : Type*} [Fintype α] (g : α → β)
    (hg : ∀ v, (Finset.univ.filter (fun i => g i = v)).card ≤ 2) :
    ∃ slot : α → Bool, ∀ i j, g i = g j → slot i = slot j → i = j := by
  let r : α → ℕ := fun i => (Fintype.equivFin α i).1
  have hr : Function.Injective r := fun i j h => (Fintype.equivFin α).injective (Fin.ext h)
  let slot : α → Bool := fun i => decide (∃ j, g j = g i ∧ r j < r i)
  have aux : ∀ i j, g i = g j → r i < r j → slot i = slot j → False := by
    intro i j hij hlt hs
    have hj : slot j = true := decide_eq_true ⟨i, hij, hlt⟩
    rw [← hs] at hj
    obtain ⟨k, hk, hki⟩ := of_decide_eq_true hj
    have : 2 < (Finset.univ.filter (fun l => g l = g i)).card :=
      Finset.two_lt_card.2 ⟨k, by simp [hk], i, by simp, j, by simp [hij],
        fun h => by rw [h] at hki; omega, fun h => by rw [h] at hki; omega,
        fun h => by rw [h] at hlt; omega⟩
    have := hg (g i); omega
  refine ⟨slot, fun i j hij hs => ?_⟩
  by_contra hne
  rcases lt_or_gt_of_ne (hr.ne hne) with h | h
  · exact aux i j hij h hs
  · exact aux j i hij.symm h hs.symm


/-- **Lemma 2.7** (coupling).  Let `E` be the edge set of a multigraph with vertex set `β` and
maximum degree at most `2`, the edge `c` having ends `e₁ c, e₂ c`.  Select every edge with
probability `p ≤ 1/4`; then every up-closed property of the set of vertices incident with a
selected edge is at most as likely as for a `2√p`-random subset of `β`. -/
theorem coupling_domination {ι β : Type*} [Fintype ι] [Fintype β] (E : Finset ι)
    (e₁ e₂ : ι → β)
    (hdeg : ∀ v, (E.filter (fun c => e₁ c = v)).card + (E.filter (fun c => e₂ c = v)).card ≤ 2)
    {p : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1 / 4) (P : Finset β → Prop)
    (hP : ∀ A B, A ⊆ B → P A → P B) :
    ppr (fun _ : ι => bern p) (fun x => P (endsSet E e₁ e₂ x)) ≤
      ppr (fun _ : β => bern (2 * Real.sqrt p))
        (fun y => P (Finset.univ.filter (fun v => y v = true))) := by
  set s := Real.sqrt p with hs_def
  have hs0 : 0 ≤ s := Real.sqrt_nonneg p
  have hss : s * s = p := Real.mul_self_sqrt hp0
  have hs1 : 2 * s ≤ 1 := by nlinarith
  have hbs : ∑ k, bern s k = 1 := by simp [bern]
  let g : E × Bool → β := fun i => if i.2 then e₂ i.1 else e₁ i.1
  let F' : (E → Bool) → Prop := fun x' =>
    P ((Finset.univ.filter (fun c : E => x' c = true)).image (fun c => e₁ c.1) ∪
      (Finset.univ.filter (fun c : E => x' c = true)).image (fun c => e₂ c.1))
  -- (a) marginalise to the edges of `E`
  have ha : ppr (fun _ : ι => bern p) (fun x => P (endsSet E e₁ e₂ x)) =
      ppr (fun _ : E => bern p) F' := by
    unfold ppr
    rw [← pex_comp_injective (ν := bern p) (by simp [bern]) (fun c : E => c.1)
      Subtype.val_injective]
    congr 1; funext x
    have : endsSet E e₁ e₂ x =
        (Finset.univ.filter (fun c : E => x c.1 = true)).image (fun c => e₁ c.1) ∪
          (Finset.univ.filter (fun c : E => x c.1 = true)).image (fun c => e₂ c.1) := by
      ext v; simp only [endsSet, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
        Finset.mem_univ, true_and, Subtype.exists]; aesop
    simp only [F', this]
  -- (b) split every edge into two half-edges
  have hb : ppr (fun _ : E => bern p) F' =
      ppr (fun _ : E × Bool => bern s) (fun z => F' (fun c => z (c, false) && z (c, true))) := by
    rw [← hss]; exact ppr_split_and s F'
  -- (c) monotonicity
  let Pv : (E × Bool → Bool) → Prop := fun z =>
    P (Finset.univ.filter (fun v => ∃ i, g i = v ∧ z i = true))
  have hc : ppr (fun _ : E × Bool => bern s) (fun z => F' (fun c => z (c, false) && z (c, true)))
      ≤ ppr (fun _ : E × Bool => bern s) Pv := by
    refine ppr_mono (isPD_bern hs0 (by linarith)) fun z hz => hP _ _ ?_ hz
    intro v hv
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.and_eq_true] at hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hv with ⟨c, ⟨h1, _⟩, rfl⟩ | ⟨c, ⟨_, h2⟩, rfl⟩
    · exact ⟨(c, false), rfl, h1⟩
    · exact ⟨(c, true), rfl, h2⟩
  -- (d) slots
  have hfib : ∀ v, (Finset.univ.filter (fun i => g i = v)).card ≤ 2 := by
    intro v
    have h1 : (Finset.univ.filter (fun i => g i = v)).card =
        (Finset.univ.filter (fun c : E => e₁ c.1 = v)).card +
          (Finset.univ.filter (fun c : E => e₂ c.1 = v)).card := by
      simp only [Finset.card_filter]
      rw [Fintype.sum_prod_type, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Fintype.sum_bool]; simp [g, add_comm]
    have h2 : ∀ e : ι → β, (Finset.univ.filter (fun c : E => e c.1 = v)).card =
        (E.filter (fun c => e c = v)).card := by
      intro e
      rw [Finset.card_filter, Finset.card_filter]
      exact Finset.sum_coe_sort E (fun c => if e c = v then 1 else 0)
    rw [h1, h2, h2]; exact hdeg v
  obtain ⟨slot, hslot⟩ := exists_slot g hfib
  let ψ : E × Bool → β × Bool := fun i => (g i, slot i)
  have hψ : Function.Injective ψ := fun i j h =>
    hslot i j (congrArg Prod.fst h) (congrArg Prod.snd h)
  have hd : ppr (fun _ : E × Bool => bern s) Pv =
      ppr (fun _ : β × Bool => bern s) (fun w => Pv (fun i => w (ψ i))) := by
    unfold ppr
    exact (pex_comp_injective hbs ψ hψ _).symm
  let Po : (β × Bool → Bool) → Prop := fun w =>
    P (Finset.univ.filter (fun v => (w (v, false) || w (v, true)) = true))
  have hd' : ppr (fun _ : β × Bool => bern s) (fun w => Pv (fun i => w (ψ i))) ≤
      ppr (fun _ : β × Bool => bern s) Po := by
    refine ppr_mono (isPD_bern hs0 (by linarith)) fun w hw => hP _ _ ?_ hw
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    obtain ⟨i, rfl, hi⟩ := hv
    simp only [ψ] at hi
    cases h : slot i <;> rw [h] at hi <;> simp [hi]
  -- (e) merge the two slots
  have he : ppr (fun _ : β × Bool => bern s) Po =
      ppr (fun _ : β => bern (2 * s - s * s))
        (fun y => P (Finset.univ.filter (fun v => y v = true))) := by
    exact ppr_merge_or s (fun y => P (Finset.univ.filter (fun v => y v = true)))
  have hmono : ppr (fun _ : β => bern (2 * s - s * s))
      (fun y => P (Finset.univ.filter (fun v => y v = true))) ≤
      ppr (fun _ : β => bern (2 * s)) (fun y => P (Finset.univ.filter (fun v => y v = true))) := by
    refine ppr_bern_mono (q := fun _ => 2 * s - s * s) (q' := fun _ => 2 * s)
      (fun _ => by nlinarith) (fun _ => by nlinarith) (fun _ => hs1) ?_
    intro x y hxy hx
    refine hP _ _ (fun v hv => ?_) hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact hxy v hv
  rw [ha, hb]
  exact hc.trans (hd.le.trans (hd'.trans (he.le.trans hmono)))


lemma pushD_any {ι : Type*} (K : ℕ) (q : ℝ) :
    pushD (fun (_ : ι) (z : Fin K → Bool) => ∏ j, bern q (z j)) (fun z => decide (∃ j, z j = true)) =
      fun _ => bern (1 - (1 - q) ^ K) := by
  have htot : ∑ z : Fin K → Bool, ∏ j, bern q (z j) = 1 := by
    rw [← Fintype.prod_sum (fun _ b => bern q b)]; simp [bern]
  have hfalse : ∑ z : Fin K → Bool, (∏ j, bern q (z j)) * (if ∀ j, z j = false then (1 : ℝ) else 0) =
      (1 - q) ^ K := by
    have : ∀ z : Fin K → Bool, (∏ j, bern q (z j)) * (if ∀ j, z j = false then (1 : ℝ) else 0) =
        ∏ j, (bern q (z j) * if z j = false then (1 : ℝ) else 0) := by
      intro z
      rw [Finset.prod_mul_distrib]
      congr 1
      by_cases h : ∀ j, z j = false
      · simp [h]
      · push_neg at h
        obtain ⟨j, hj⟩ := h
        rw [if_neg (by push_neg; exact ⟨j, hj⟩)]
        exact (Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])).symm
    simp only [this]
    rw [← Fintype.prod_sum (fun _ b => bern q b * if b = false then 1 else 0)]
    simp [bern]
  funext i c
  unfold pushD
  rw [Finset.sum_filter]
  cases c
  · show _ = 1 - (1 - (1 - q) ^ K)
    rw [sub_sub_cancel, ← hfalse]
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases h : ∃ j, z j = true
    · have : ¬ ∀ j, z j = false := by
        obtain ⟨j, hj⟩ := h; intro h'; simp [h' j] at hj
      rw [if_neg (by simpa using h), if_neg this]; ring
    · have : ∀ j, z j = false := by push_neg at h; simpa using h
      rw [if_pos (by simpa using h), if_pos this]; ring
  · have hsplit : ∀ z : Fin K → Bool, ∏ j, bern q (z j) =
        (if decide (∃ j, z j = true) = true then ∏ j, bern q (z j) else 0) +
          (∏ j, bern q (z j)) * (if ∀ j, z j = false then (1 : ℝ) else 0) := by
      intro z
      by_cases h : ∃ j, z j = true
      · have : ¬ ∀ j, z j = false := by
          obtain ⟨j, hj⟩ := h; intro h'; simp [h' j] at hj
        rw [if_pos (decide_eq_true h), if_neg this]; ring
      · have : ∀ j, z j = false := by push_neg at h; simpa using h
        rw [if_neg (by simpa using h), if_pos this]; ring
    have := htot
    rw [Finset.sum_congr rfl (fun z _ => hsplit z)] at this
    rw [Finset.sum_add_distrib, hfalse] at this
    show _ = 1 - (1 - q) ^ K
    rw [← eq_sub_of_add_eq this]
    exact Finset.sum_congr (by congr) fun x _ => by dsimp only; congr

/-- Amplification (the probabilistic content of Corollary 2.5): if an up-closed property of a
`q`-random set fails with probability at most `η`, then for a `Kq`-random set it fails with
probability at most `η^K`. -/
lemma ppr_amplify {V : Type*} [Fintype V] (K : ℕ) {q η : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hKq : K * q ≤ 1) (Good : Finset V → Prop) (hG : ∀ A B, A ⊆ B → Good A → Good B)
    (h1 : 1 - η ≤ ppr (fun _ : V => bern q) (fun y => Good (Finset.univ.filter (fun v => y v = true)))) :
    1 - η ^ K ≤ ppr (fun _ : V => bern (K * q))
      (fun y => Good (Finset.univ.filter (fun v => y v = true))) := by
  have hμ : IsPD (fun _ : V => bern q) := isPD_bern hq0 hq1
  -- bad probability of one copy
  set b := ppr (fun _ : V => bern q) (fun y => ¬ Good (Finset.univ.filter (fun v => y v = true)))
  have hb : b ≤ η := by simp only [b]; rw [ppr_not hμ]; linarith
  have hb0 : 0 ≤ b := ppr_nonneg hμ _
  -- the union of `K` independent copies
  have hq' : 0 ≤ 1 - (1 - q) ^ K := by
    have : (1 - q) ^ K ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    linarith
  have hq'K : 1 - (1 - q) ^ K ≤ K * q := by
    have := one_add_mul_le_pow (a := -q) (by linarith) K
    rw [show (1 + -q) = 1 - q by ring] at this
    linarith
  have step1 : ppr (fun _ : V => bern (1 - (1 - q) ^ K))
      (fun y => Good (Finset.univ.filter (fun v => y v = true))) ≤
      ppr (fun _ : V => bern (K * q)) (fun y => Good (Finset.univ.filter (fun v => y v = true))) :=
    ppr_bern_mono (q := fun _ => 1 - (1 - q) ^ K) (q' := fun _ => K * q) (fun _ => hq')
      (fun _ => hq'K) (fun _ => hKq) (fun x y hxy hx => hG _ _ (fun v hv => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢; exact hxy v hv) hx)
  have step2 : ppr (fun _ : V => bern (1 - (1 - q) ^ K))
      (fun y => Good (Finset.univ.filter (fun v => y v = true))) =
      ppr (fun _ : V => fun z : Fin K → Bool => ∏ j, bern q (z j))
        (fun X => Good (Finset.univ.filter (fun v => ∃ j, X v j = true))) := by
    rw [← pushD_any (ι := V) K q, ← ppr_map]
    simp
  have step3 : ppr (fun _ : V => fun z : Fin K → Bool => ∏ j, bern q (z j))
        (fun X => Good (Finset.univ.filter (fun v => ∃ j, X v j = true))) =
      ppr (fun _ : Fin K => fun z : V → Bool => ∏ v, bern q (z v))
        (fun X => Good (Finset.univ.filter (fun v => ∃ j, X j v = true))) := by
    unfold ppr
    rw [← pex_curry (fun (_ : V) (_ : Fin K) => bern q)
      (fun w => if Good (Finset.univ.filter (fun v => ∃ j, w (v, j) = true)) then 1 else 0),
      ← pex_curry (fun (_ : Fin K) (_ : V) => bern q)
      (fun w => if Good (Finset.univ.filter (fun v => ∃ j, w (j, v) = true)) then 1 else 0),
      pex_reindex (Equiv.prodComm (Fin K) V)]
    rfl
  have step4 : 1 - b ^ K ≤ ppr (fun _ : Fin K => fun z : V → Bool => ∏ v, bern q (z v))
        (fun X => Good (Finset.univ.filter (fun v => ∃ j, X j v = true))) := by
    have hν : IsPD (fun _ : Fin K => fun z : V → Bool => ∏ v, bern q (z v)) :=
      isPD_prod (ν := fun _ _ => bern q) (fun _ => hμ)
    have hall : ppr (fun _ : Fin K => fun z : V → Bool => ∏ v, bern q (z v))
        (fun X => ∀ j, ¬ Good (Finset.univ.filter (fun v => X j v = true))) = b ^ K := by
      unfold ppr
      trans pex (fun _ : Fin K => fun z : V → Bool => ∏ v, bern q (z v))
        (fun X => ∏ j, (if ¬ Good (Finset.univ.filter (fun v => X j v = true)) then (1 : ℝ) else 0))
      · congr 1; funext X
        by_cases h : ∀ j, ¬ Good (Finset.univ.filter (fun v => X j v = true))
        · rw [if_pos h]; symm; exact Finset.prod_eq_one fun j _ => if_pos (h j)
        · rw [if_neg h]; push_neg at h; obtain ⟨j, hj⟩ := h
          exact (Finset.prod_eq_zero (Finset.mem_univ j) (by rw [if_neg (not_not.2 hj)])).symm
      rw [pex_prod (fun (_ : Fin K) (z : V → Bool) => if ¬ Good (Finset.univ.filter (fun v => z v = true)) then 1 else 0)]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, b, ppr, pex, pwt]
      congr 1
      exact Finset.sum_congr rfl fun x _ => by
        congr 1; split_ifs <;> rfl
    have := ppr_not hν (fun X => ∀ j, ¬ Good (Finset.univ.filter (fun v => X j v = true)))
    rw [hall] at this
    rw [← this]
    refine ppr_mono hν fun X hX => ?_
    push_neg at hX
    obtain ⟨j, hj⟩ := hX
    exact hG _ _ (fun v hv => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢; exact ⟨j, hv⟩) hj
  have hbK : b ^ K ≤ η ^ K := pow_le_pow_left₀ hb0 hb K
  rw [step2, step3] at step1
  linarith

end

end Lovasz
