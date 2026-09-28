module
public import RequestProject.Linking

/-!
# The linking lemma: probabilistic part (Lemma 2.6)
-/

@[expose] public section


open scoped BigOperators
open Classical Filter

namespace Lovasz

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- The colour distribution used in the proof of Lemma 2.6: colours `0, 4` with probability
`r`, colour `5` with probability `8r`, colours `1, 2, 3` with probability `q`, colour `6`
(uncoloured) otherwise. -/
def colD (r q : ℝ) (k : Fin 7) : ℝ :=
  if k = 0 then r else if k = 4 then r else if k = 5 then 8 * r else
    if k = 6 then 1 - 10 * r - 3 * q else q

lemma colD_sum (r q : ℝ) : ∑ k, colD r q k = 1 := by
  simp [colD, Fin.sum_univ_seven]; ring

omit [Fintype ι] in
lemma isPD_colD {r q : ℝ} (hr : 0 ≤ r) (hq : 0 ≤ q) (h : 10 * r + 3 * q ≤ 1) :
    IsPD (fun _ : ι => colD r q) := by
  refine ⟨fun _ k => ?_, fun _ => colD_sum r q⟩
  fin_cases k <;> simp [colD] <;> linarith

omit [Fintype ι] in
lemma pushD_decide {κ : Type*} [Fintype κ] [DecidableEq κ] (ν : κ → ℝ) (hν : ∑ k, ν k = 1) (A : Finset κ) :
    pushD (fun _ : ι => ν) (fun k => decide (k ∈ A)) = fun _ => bern (∑ k ∈ A, ν k) := by
  funext i b
  unfold pushD
  cases b
  · simp only [decide_eq_false_iff_not, bern, Bool.false_eq_true, if_false]
    rw [← hν, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k => k ∈ A)]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    ring
  · simp only [decide_eq_true_eq, bern, if_true]
    congr 1; ext k; simp

lemma ppr_colour {κ : Type*} [Fintype κ] [DecidableEq κ] (ν : κ → ℝ) (hν : ∑ k, ν k = 1) (A : Finset κ)
    (P : (ι → Bool) → Prop) :
    ppr (fun _ : ι => ν) (fun x => P (fun v => decide (x v ∈ A))) =
      ppr (fun _ : ι => bern (∑ k ∈ A, ν k)) P := by
  rw [← pushD_decide ν hν A]
  exact ppr_map (fun _ : ι => ν) (fun k => decide (k ∈ A)) P

omit [Fintype ι] in
lemma cntT_decide {κ : Type*} [DecidableEq κ] (S : Finset ι) (A : Finset κ) (x : ι → κ) :
    cntT S (fun v => decide (x v ∈ A)) = (S.filter (fun v => x v ∈ A)).card := by
  unfold cntT; congr 1

lemma colour_upper {κ : Type*} [Fintype κ] [DecidableEq κ] {ν : κ → ℝ} (hν0 : ∀ k, 0 ≤ ν k) (hν : ∑ k, ν k = 1)
    (A : Finset κ) (S : Finset ι) (a : ℝ) :
    ppr (fun _ : ι => ν) (fun x => a ≤ ((S.filter (fun v => x v ∈ A)).card : ℝ)) ≤
      Real.exp ((Real.exp 1 - 1) * (∑ k ∈ A, ν k) * S.card - a) := by
  have h0 : 0 ≤ ∑ k ∈ A, ν k := Finset.sum_nonneg fun k _ => hν0 k
  have h1 : ∑ k ∈ A, ν k ≤ 1 := hν ▸ Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun k _ _ => hν0 k)
  have := ppr_colour (ι := ι) ν hν A (fun y => a ≤ (cntT S y : ℝ))
  simp only [cntT_decide] at this
  rw [this]
  exact chernoff_upper h0 h1 S a

lemma colour_lower {κ : Type*} [Fintype κ] [DecidableEq κ] {ν : κ → ℝ} (hν0 : ∀ k, 0 ≤ ν k) (hν : ∑ k, ν k = 1)
    (A : Finset κ) (S : Finset ι) (a : ℝ) :
    ppr (fun _ : ι => ν) (fun x => ((S.filter (fun v => x v ∈ A)).card : ℝ) ≤ a) ≤
      Real.exp (a - (1 - Real.exp (-1)) * (∑ k ∈ A, ν k) * S.card) := by
  have h0 : 0 ≤ ∑ k ∈ A, ν k := Finset.sum_nonneg fun k _ => hν0 k
  have h1 : ∑ k ∈ A, ν k ≤ 1 := hν ▸ Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun k _ _ => hν0 k)
  have := ppr_colour (ι := ι) ν hν A (fun y => (cntT S y : ℝ) ≤ a)
  simp only [cntT_decide] at this
  rw [this]
  exact chernoff_lower h0 h1 S a

omit [Fintype ι] in
lemma degIn_sdiff_le {V : Type*} (G : SimpleGraph V) (U X : Finset V) (v : V) :
    degIn G U v ≤ degIn G (U \ X) v + X.card := by
  unfold degIn
  have : U.filter (G.Adj v) ⊆ (U \ X).filter (G.Adj v) ∪ X := by
    intro w hw
    obtain ⟨hwU, hvw⟩ := Finset.mem_filter.1 hw
    by_cases hwX : w ∈ X
    · exact Finset.mem_union_right _ hwX
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨hwU, hwX⟩, hvw⟩)
  exact (Finset.card_le_card this).trans (Finset.card_union_le _ _)

omit [Fintype ι] in
lemma LinkProp.mono_R {V : Type*} {G : SimpleGraph V} {U R R' : Finset V} {K : ℝ}
    (h : LinkProp G U R K) (hR : R ⊆ R') :
    LinkProp G U R' K := by
  intro pairs hnd hends hexp
  obtain ⟨paths, hp, hF⟩ := h pairs hnd (fun p hp => by
    obtain ⟨h1, h2⟩ := hends p hp
    exact ⟨Finset.mem_sdiff.2 ⟨(Finset.mem_sdiff.1 h1).1, fun h => (Finset.mem_sdiff.1 h1).2 (hR h)⟩,
      Finset.mem_sdiff.2 ⟨(Finset.mem_sdiff.1 h2).1, fun h => (Finset.mem_sdiff.1 h2).2 (hR h)⟩⟩)
    hexp
  exact ⟨paths, hp, hF.imp fun p P h => ⟨h.1, fun v hv => by
    rcases h.2 v hv with h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (hR h'))⟩⟩

/-- The deterministic conclusion of the colouring argument in the proof of Lemma 2.6. -/
lemma colour_good {ι : Type*} [Fintype ι] (H : SimpleGraph ι) (U Vs : Finset ι) (x : ι → Fin 7)
    {KL t D' r : ℝ}
    (hlink : ∀ k ∈ ({1, 2, 3} : Finset (Fin 7)), LinkProp H (U \ Vs) ((U \ Vs).filter (fun v => x v = k)) KL)
    (hdeg : ∀ v ∈ U \ Vs, ((((U \ Vs).filter (H.Adj v)).filter
      (fun w => x w ∈ ({0, 4, 5} : Finset (Fin 7)))).card : ℝ) ≤ t)
    (hpriv : ∀ v ∈ Vs, (2 * Vs.card : ℝ) ≤
      (((U \ Vs).filter (H.Adj v)).filter (fun w => x w ∈ ({4} : Finset (Fin 7)))).card)
    (h5 : r * U.card + 1 < (((U \ Vs).filter (fun w => x w ∈ ({5} : Finset (Fin 7)))).card : ℝ))
    (hr1 : 1 ≤ r * U.card)
    (hmindeg : ∀ v ∈ U \ Vs, D' ≤ degIn H (U \ Vs) v) (ht : 0 < t) (hKL : KL ≤ (D' - t) / t) :
    LinkEvent H U Vs (Finset.univ.filter (fun v => decide (x v ∈ ({0} : Finset (Fin 7))) = true))
      (r * U.card) := by
  set U' := U \ Vs
  let f : Fin 3 → Fin 7 := fun c => ⟨c.val + 1, by omega⟩
  have hf : ∀ c, f c ∈ ({1, 2, 3} : Finset (Fin 7)) := by
    intro c; fin_cases c <;> simp [f]
  have hf0 : ∀ c, f c ≠ 0 ∧ f c ≠ 4 ∧ f c ≠ 5 := by
    intro c; fin_cases c <;> simp [f]
  have hfinj : ∀ c c', f c = f c' → c = c' := by
    intro c c' h; ext; have := congrArg Fin.val h; simp [f] at this; omega
  set C4 := U'.filter (fun v => x v = 4)
  set C5 := U'.filter (fun v => x v = 5)
  set Y := Finset.univ.filter (fun v => decide (x v ∈ ({0} : Finset (Fin 7))) = true)
  have hY : ∀ v, v ∈ Y ↔ x v = 0 := by intro v; simp [Y]
  have hC5eq : ((U \ Vs).filter (fun w => x w ∈ ({5} : Finset (Fin 7)))) = C5 := by
    ext v; simp [C5, U']
  -- private neighbours
  obtain ⟨a, b, hab1, hainj, hbinj, hab⟩ := private_nbrs Vs (fun v => C4.filter (H.Adj v)) (by
    intro v hv
    have := hpriv v hv
    have e : (((U \ Vs).filter (H.Adj v)).filter (fun w => x w ∈ ({4} : Finset (Fin 7)))) =
        C4.filter (H.Adj v) := by ext w; simp [C4, U']; tauto
    rw [e] at this; exact_mod_cast this)
  have d1 : Disjoint C5 Y := Finset.disjoint_left.2 fun v h1 h2 => by
    rw [hY] at h2; rw [(Finset.mem_filter.1 h1).2] at h2; exact absurd h2 (by decide)
  have d2 : Disjoint C4 Y := Finset.disjoint_left.2 fun v h1 h2 => by
    rw [hY] at h2; rw [(Finset.mem_filter.1 h1).2] at h2; exact absurd h2 (by decide)
  have d3 : ∀ c, Disjoint (U'.filter (fun v => x v = f c)) Y := fun c =>
    Finset.disjoint_left.2 fun v h1 h2 => by
      rw [hY] at h2; rw [(Finset.mem_filter.1 h1).2] at h2; exact (hf0 c).1 h2
  have d4 : Disjoint C5 C4 := Finset.disjoint_left.2 fun v h1 h2 => by
    have e1 := (Finset.mem_filter.1 h1).2; have e2 := (Finset.mem_filter.1 h2).2
    rw [e1] at e2; exact absurd e2 (by decide)
  have d5 : ∀ c, Disjoint C5 (U'.filter (fun v => x v = f c)) := fun c =>
    Finset.disjoint_left.2 fun v h1 h2 => by
      have e1 := (Finset.mem_filter.1 h1).2; have e2 := (Finset.mem_filter.1 h2).2
      rw [e1] at e2; exact (hf0 c).2.2 e2.symm
  have d6 : ∀ c, Disjoint C4 (U'.filter (fun v => x v = f c)) := fun c =>
    Finset.disjoint_left.2 fun v h1 h2 => by
      have e1 := (Finset.mem_filter.1 h1).2; have e2 := (Finset.mem_filter.1 h2).2
      rw [e1] at e2; exact (hf0 c).2.1 e2.symm
  have d7 : ∀ c c', c ≠ c' → Disjoint (U'.filter (fun v => x v = f c))
      (U'.filter (fun v => x v = f c')) := fun c c' hcc' =>
    Finset.disjoint_left.2 fun v h1 h2 =>
      hcc' (hfinj _ _ ((Finset.mem_filter.1 h1).2.symm.trans (Finset.mem_filter.1 h2).2))
  have ha : ∀ v ∈ Vs, a v ∈ C4 ∧ H.Adj v (a v) := fun v hv =>
    ⟨(Finset.mem_filter.1 (hab1 v hv).1).1, (Finset.mem_filter.1 (hab1 v hv).1).2⟩
  have hb : ∀ v ∈ Vs, b v ∈ C4 ∧ H.Adj v (b v) := fun v hv =>
    ⟨(Finset.mem_filter.1 (hab1 v hv).2).1, (Finset.mem_filter.1 (hab1 v hv).2).2⟩
  have hl : ∀ c, LinkProp H U' (U'.filter (fun v => x v = f c)) KL := fun c => hlink (f c) (hf c)
  refine linkEvent_of (H := H) (U := U) (K := KL) (C4 := C4) (C5 := C5)
    (fun c => U'.filter (fun v => x v = f c)) (a := a) (b := b)
    (Finset.filter_subset _ _) (Finset.filter_subset _ _) (fun c => Finset.filter_subset _ _)
    d1 d2 d3 d4 d5 d6 d7 ha hb hainj hbinj hab hl ?_ ?_ ?_
  · intro X hX
    set T := U'.filter (fun w => x w ∈ ({0, 4, 5} : Finset (Fin 7)))
    have hXT : X ⊆ T := by
      intro v hv
      have := hX hv
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter, hY, C4, C5,
        Finset.mem_filter, U'] at this
      simp only [T, U', Finset.mem_filter, Finset.mem_sdiff, Finset.mem_insert,
        Finset.mem_singleton]
      tauto
    have hXU : X ⊆ U' := hXT.trans (Finset.filter_subset _ _)
    have := expansion_of_degrees (H := H) hXT hXU hmindeg (fun v hv => by
      have e : (U' ∩ T).filter (H.Adj v) =
          ((U'.filter (H.Adj v)).filter (fun w => x w ∈ ({0, 4, 5} : Finset (Fin 7)))) := by
        ext w; simp [T]; tauto
      rw [e]; exact hdeg v hv) ht
    exact le_trans (mul_le_mul_of_nonneg_right hKL (Nat.cast_nonneg _)) this
  · rw [hC5eq] at h5
    have : (2 : ℝ) < C5.card := by linarith
    exact_mod_cast this.le
  · rw [hC5eq] at h5; linarith

end

end Lovasz
