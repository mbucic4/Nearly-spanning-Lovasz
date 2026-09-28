module
public import RequestProject.Concrete

/-!
# The initial circuit (Claim 2.13)

In the concrete geometry, the cycle `L` cut at every interval belonging to a block yields a
circuit: its strands are the stretches of `L` between consecutive block intervals (the last one
is split at the edge `2n-1 — 0`), and consecutive strands are joined by jumps inside a block
interval.  Every block containing an interval has a jump in this circuit.
-/

@[expose] public section


open Classical

namespace Lovasz

namespace Conc

variable {n t : ℕ} {hn : 0 < n}

lemma st_le_st {k k' : ℕ} (hkk : k ≤ k') (hk' : k' < 2 * nQ n t) : st n t k ≤ st n t k' := by
  rcases eq_or_lt_of_le hkk with rfl | h
  · exact le_rfl
  · have := st_mono (n := n) (t := t) h hk'; omega

lemma rng_eq_cons_append {a b : ℕ} (hab : a < b) :
    rng n hn a b = fv n hn a :: (rng n hn (a + 1) (b - 1) ++ [fv n hn b]) := by
  unfold rng
  have e : List.range' a (b + 1 - a) = a :: (List.range' (a + 1) (b - 1 + 1 - (a + 1)) ++ [b]) := by
    rw [show b + 1 - a = (b - 1 + 1 - (a + 1)) + 1 + 1 by omega, List.range'_succ,
      List.range'_concat]
    congr 3
    omega
  rw [e]
  simp

lemma mem_sInner_rng {a b : ℕ} (hab : a < b) (hb : b < 2 * n) {x : Fin (2 * n)}
    (hx : x ∈ sInner (rng n hn a b)) : a < x.val ∧ x.val < b := by
  rw [rng_eq_cons_append hab, sInner, List.tail_cons, List.dropLast_concat] at hx
  rw [mem_rng (by omega)] at hx
  omega

lemma rng_ne_nil {a b : ℕ} (hab : a ≤ b) : rng n hn a b ≠ [] := by
  intro h
  have := rng_head (n := n) (hn := hn) hab
  rw [h] at this; simp at this

lemma length_rng (a b : ℕ) : (rng n hn a b).length = b + 1 - a := by simp [rng]

section circuit

variable (t) (hQ : 0 < nQ n t)
  {β : Type*} (blk : Fin (2 * nQ n t) → Option β)

/-- The sorted list of intervals lying in some block. -/
noncomputable def actList : List (Fin (2 * nQ n t)) :=
  (Finset.univ.filter (fun J => ∃ G, blk J = some G)).sort (· ≤ ·)

/-- The (natural number) index of the `i`-th block interval. -/
noncomputable def aI (i : ℕ) : ℕ := ((actList t blk).getD i ⟨0, by omega⟩).val

/-- Start of the `i`-th strand. -/
noncomputable def sA (i : ℕ) : ℕ := if i = 0 then 0 else st n t (aI t hQ blk (i - 1)) + t - 1

/-- End of the `i`-th strand. -/
noncomputable def eA (i : ℕ) : ℕ :=
  if i < (actList t blk).length then st n t (aI t hQ blk i) else 2 * n - 1

/-- The initial circuit. -/
noncomputable def initCirc (hn' : 0 < n) : List (List (Fin (2 * n))) :=
  (List.range ((actList t blk).length + 1)).map
    (fun i => rng n hn' (sA t hQ blk i) (eA t hQ blk i))

variable {t}

lemma actList_sorted : (actList t blk).SortedLT := by
  unfold actList
  exact Finset.sortedLT_sort _

lemma mem_actList {J : Fin (2 * nQ n t)} : J ∈ actList t blk ↔ ∃ G, blk J = some G := by
  simp [actList]

lemma aI_lt (i : ℕ) : aI t hQ blk i < 2 * nQ n t := Fin.isLt _

lemma aI_eq {i : ℕ} (hi : i < (actList t blk).length) :
    aI t hQ blk i = ((actList t blk)[i]).val := by
  simp [aI, List.getElem?_eq_getElem hi]

lemma aI_strictMono {i j : ℕ} (hij : i < j) (hj : j < (actList t blk).length) :
    aI t hQ blk i < aI t hQ blk j := by
  rw [aI_eq hQ blk (by omega), aI_eq hQ blk hj]
  have := (actList_sorted blk).pairwise
  exact List.pairwise_iff_getElem.1 this i j (by omega) hj hij

lemma aI_mono {i j : ℕ} (hij : i ≤ j) (hj : j < (actList t blk).length) :
    aI t hQ blk i ≤ aI t hQ blk j := by
  rcases eq_or_lt_of_le hij with rfl | h
  · exact le_rfl
  · exact (aI_strictMono hQ blk h hj).le

/-- Every block interval occurs in the list. -/
lemma exists_aI {J : Fin (2 * nQ n t)} (hJ : ∃ G, blk J = some G) :
    ∃ i < (actList t blk).length, aI t hQ blk i = J.val := by
  obtain ⟨i, hi, e⟩ := List.getElem_of_mem ((mem_actList blk).2 hJ)
  exact ⟨i, hi, by rw [aI_eq hQ blk hi, e]⟩

lemma blk_aI {i : ℕ} (hi : i < (actList t blk).length) :
    ∃ G, blk ⟨aI t hQ blk i, aI_lt hQ blk i⟩ = some G := by
  have h := (mem_actList blk).1 (List.getElem_mem hi)
  have e : (⟨aI t hQ blk i, aI_lt hQ blk i⟩ : Fin (2 * nQ n t)) = (actList t blk)[i] :=
    Fin.ext (aI_eq hQ blk hi)
  rw [e]; exact h

lemma sA_lt_eA (ht : 2 ≤ t) {i : ℕ} (hi : i ≤ (actList t blk).length) (hm : 0 < (actList t blk).length) :
    sA t hQ blk i < eA t hQ blk i := by
  unfold sA eA
  have h1 := one_le_st (n := n) (t := t) (aI t hQ blk i)
  split_ifs with h0 h2 h2
  · exact h1
  · omega
  · have := st_mono (n := n) (t := t) (aI_strictMono hQ blk (show i - 1 < i by omega) h2)
      (aI_lt hQ blk i)
    omega
  · have := st_lt_top (n := n) (t := t) (aI_lt hQ blk (i - 1))
    omega

lemma eA_lt_sA_succ (ht : 2 ≤ t) {i : ℕ} (hi : i < (actList t blk).length) :
    eA t hQ blk i < sA t hQ blk (i + 1) := by
  unfold sA eA
  rw [if_pos hi, if_neg (by omega), Nat.add_sub_cancel]
  omega

lemma eA_lt (i : ℕ) : eA t hQ blk i < 2 * n := by
  have h0 := st_lt_top (n := n) (t := t) (k := 0) (by omega)
  have h1 := one_le_st (n := n) (t := t) 0
  unfold eA
  split_ifs
  · have := st_lt_top (n := n) (t := t) (aI_lt hQ blk i); omega
  · omega

lemma eA_lt_sA (ht : 2 ≤ t) {i j : ℕ} (hij : i < j) (hj : j ≤ (actList t blk).length)
    (hm : 0 < (actList t blk).length) : eA t hQ blk i < sA t hQ blk j := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | rfl
    · have := ih h (by omega)
      have := sA_lt_eA hQ blk ht (i := j) (by omega) hm
      have := eA_lt_sA_succ hQ blk ht (i := j) (by omega)
      omega
    · exact eA_lt_sA_succ hQ blk ht (by omega)

lemma mem_initCirc {σ : List (Fin (2 * n))} :
    σ ∈ initCirc t hQ blk hn ↔
      ∃ i ≤ (actList t blk).length, σ = rng n hn (sA t hQ blk i) (eA t hQ blk i) := by
  unfold initCirc
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, by omega, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, by omega, rfl⟩

lemma length_initCirc : (initCirc t hQ blk hn).length = (actList t blk).length + 1 := by
  simp [initCirc]

lemma getD_initCirc {i : ℕ} (hi : i ≤ (actList t blk).length) :
    (initCirc t hQ blk hn).getD i [] = rng n hn (sA t hQ blk i) (eA t hQ blk i) := by
  unfold initCirc
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp

/-- A vertex in an interval `k` lies strictly after `0` and strictly before `2n - 1`. -/
lemma iv_bounds {v : Fin (2 * n)} {k : Fin (2 * nQ n t)} (h : ivOf t n v = some k) :
    0 < v.val ∧ v.val < 2 * n - 1 := by
  rw [ivOf_eq_some] at h
  have := one_le_st (n := n) (t := t) k
  have := st_lt_top (n := n) (t := t) k.2
  omega

end circuit

section geo

variable (f : Fin n → Fin n) (hf : Function.Injective f) (ht : 2 ≤ t) (hQ : 0 < nQ n t)
  {β : Type*} (blk : Fin (2 * nQ n t) → Option β)

lemma cgeo_act_iff {v : Fin (2 * n)} :
    (cgeo n t hn ht hQ f hf blk).actI {J | ∃ G, (cgeo n t hn ht hQ f hf blk).blk J = some G ∧ True} v
      ↔ ∃ J, ivOf t n v = some J ∧ ∃ G, blk J = some G := by
  simp [Geo.actI, cgeo]

lemma cgeo_hd {a b : ℕ} (hab : a ≤ b) :
    (cgeo n t hn ht hQ f hf blk).hd (rng n hn a b) = fv n hn a := by
  unfold Geo.hd
  rw [List.headD_eq_head?_getD, rng_head hab]; rfl

lemma cgeo_lt {a b : ℕ} (hab : a ≤ b) :
    (cgeo n t hn ht hQ f hf blk).lt (rng n hn a b) = fv n hn b := by
  unfold Geo.lt
  rw [List.getLastD_eq_getLast?, rng_getLast hab]; rfl

/-- **Claim 2.13.**  The initial circuit is a circuit, and every block containing an interval
has a jump in it. -/
theorem initCirc_circ (hne : ∃ J G, blk J = some G) :
    (cgeo n t hn ht hQ f hf blk).Circ
      ((cgeo n t hn ht hQ f hf blk).actI
        {J | ∃ G, (cgeo n t hn ht hQ f hf blk).blk J = some G ∧ True})
      (initCirc t hQ blk hn) ∧
    ∀ J G, blk J = some G → (cgeo n t hn ht hQ f hf blk).JumpAt
      ((cgeo n t hn ht hQ f hf blk).actI
        {J | ∃ G, (cgeo n t hn ht hQ f hf blk).blk J = some G ∧ True})
      (initCirc t hQ blk hn) G := by
  set g := cgeo n t hn ht hQ f hf blk with hg
  set m := (actList t blk).length with hm_def
  have hm : 0 < m := by
    obtain ⟨J, G, hJ⟩ := hne
    obtain ⟨i, hi, -⟩ := exists_aI hQ blk ⟨G, hJ⟩
    omega
  have hact := fun v => cgeo_act_iff (hn := hn) f hf ht hQ blk (v := v)
  -- the block interval with index `aI i`
  set K : ℕ → Fin (2 * nQ n t) := fun i => ⟨aI t hQ blk i, aI_lt hQ blk i⟩ with hK
  have hlo : ∀ i, i < m → fv n hn (eA t hQ blk i) = g.lo (K i) := by
    intro i hi; simp [g, cgeo, eA, ← hm_def, if_pos hi, K]
  have hhi : ∀ i, 1 ≤ i → fv n hn (sA t hQ blk i) = g.hi (K (i - 1)) := by
    intro i hi; simp [g, cgeo, sA, if_neg (show i ≠ 0 by omega), K]
  have hivK_lo : ∀ i, g.ivOf (g.lo (K i)) = some (K i) := fun i => g.iv_lo _
  have hivK_hi : ∀ i, g.ivOf (g.hi (K i)) = some (K i) := fun i => g.iv_hi _
  have hivg : ∀ v, g.ivOf v = ivOf t n v := fun v => rfl
  -- a vertex with value `0` or `2n-1` is inactive
  have hina : ∀ v : Fin (2 * n), (v.val = 0 ∨ v.val = 2 * n - 1) → ¬ g.actI
      {J | ∃ G, g.blk J = some G ∧ True} v := by
    intro v hv hva
    obtain ⟨J, hJ, -⟩ := (hact _).1 hva
    have := iv_bounds hJ
    omega
  have hmem := fun σ => mem_initCirc (hn := hn) hQ blk (σ := σ)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro h; have := length_initCirc (hn := hn) hQ blk; rw [h] at this; simp at this
  · intro σ hσ
    obtain ⟨i, hi, rfl⟩ := (hmem σ).1 hσ
    have hlt := sA_lt_eA hQ blk ht hi hm
    have heb := eA_lt hQ blk i
    refine ⟨?_, rng_chain f heb, ?_, ?_, ?_⟩
    · rw [length_rng]; omega
    · intro v hv hva
      have hb := mem_sInner_rng hlt heb hv
      obtain ⟨J, hJ, G, hG⟩ := (hact _).1 hva
      obtain ⟨j, hj, hjJ⟩ := exists_aI hQ blk ⟨G, hG⟩
      rw [ivOf_eq_some] at hJ
      rw [← hjJ] at hJ
      by_cases hji : j < i
      · have h1 := st_le_st (n := n) (t := t) (aI_mono hQ blk (show j ≤ i - 1 by omega)
          (by omega)) (aI_lt hQ blk (i - 1))
        have : sA t hQ blk i = st n t (aI t hQ blk (i - 1)) + t - 1 := by
          simp [sA, show i ≠ 0 by omega]
        omega
      · have hi' : i < m := by omega
        have h1 := st_le_st (n := n) (t := t) (aI_mono hQ blk (show i ≤ j by omega) hj)
          (aI_lt hQ blk j)
        have : eA t hQ blk i = st n t (aI t hQ blk i) := by simp [eA, ← hm_def, hi']
        omega
    · intro hva
      rw [cgeo_hd f hf ht hQ blk hlt.le] at hva ⊢
      by_cases h0 : i = 0
      · exact absurd hva (hina _ (Or.inl (by rw [fv_val (by omega)]; simp [sA, h0])))
      · rw [hhi i (by omega)]
        exact ⟨_, hivK_hi _, Or.inr rfl⟩
    · intro hva
      rw [cgeo_lt f hf ht hQ blk hlt.le] at hva ⊢
      by_cases h0 : i < m
      · rw [hlo i h0]
        exact ⟨_, hivK_lo _, Or.inl rfl⟩
      · exact absurd hva (hina _ (Or.inr (by rw [fv_val (by omega)]; simp [eA, ← hm_def, h0])))
  · rw [List.nodup_flatten]
    refine ⟨fun σ hσ => ?_, ?_⟩
    · obtain ⟨i, hi, rfl⟩ := (hmem σ).1 hσ
      exact rng_nodup (eA_lt hQ blk i)
    · unfold initCirc
      rw [List.pairwise_map]
      refine List.pairwise_iff_getElem.2 fun i j hi hj hij => ?_
      simp only [List.getElem_range]
      simp only [List.length_range] at hi hj
      intro x hx1 hx2
      rw [mem_rng (eA_lt hQ blk _)] at hx1 hx2
      have := eA_lt_sA hQ blk ht hij (by omega) hm
      omega
  · intro p hp
    rw [cpairs_eq_range _ []] at hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hp
    rw [List.mem_range, length_initCirc] at hi
    rw [length_initCirc]
    simp only
    rw [getD_initCirc hQ blk (by omega)]
    have hlt := sA_lt_eA hQ blk ht (i := i) (by omega) hm
    rw [cgeo_lt f hf ht hQ blk hlt.le]
    by_cases him : i < m
    · rw [Nat.mod_eq_of_lt (by omega), getD_initCirc hQ blk (by omega)]
      have hlt' := sA_lt_eA hQ blk ht (i := i + 1) (by omega) hm
      rw [cgeo_hd f hf ht hQ blk hlt'.le, hlo i him, hhi (i + 1) (by omega),
        Nat.add_sub_cancel]
      obtain ⟨G, hG⟩ := blk_aI hQ blk him
      have hvb : ∀ v, g.ivOf v = some (K i) → g.vb v = some G := by
        intro v hv; unfold Geo.vb; rw [hv]; exact hG
      left
      refine ⟨(hact _).2 ⟨K i, hivK_lo i, G, hG⟩, (hact _).2 ⟨K i, hivK_hi i, G, hG⟩, G,
        hvb _ (hivK_lo i), hvb _ (hivK_hi i)⟩
    · have him' : i = m := by omega
      rw [him', show (m + 1) % (m + 1) = 0 from Nat.mod_self _,
        getD_initCirc hQ blk (Nat.zero_le _)]
      have hlt0 := sA_lt_eA hQ blk ht (i := 0) (Nat.zero_le _) hm
      rw [cgeo_hd f hf ht hQ blk hlt0.le]
      have e1 : eA t hQ blk m = 2 * n - 1 := by simp [eA, ← hm_def]
      have e0 : sA t hQ blk 0 = 0 := by simp [sA]
      rw [e1, e0]
      right
      refine ⟨hina _ (Or.inr (fv_val (by omega))), hina _ (Or.inl (fv_val (by omega))), ?_⟩
      exact adj_wrap f
  · intro J G hJ
    rw [Geo.jumpAt_iff]
    obtain ⟨i, hi, hiJ⟩ := exists_aI hQ blk ⟨G, hJ⟩
    have hlt := sA_lt_eA hQ blk ht (i := i) hi.le hm
    refine ⟨_, (hmem _).2 ⟨i, hi.le, rfl⟩, ?_⟩
    rw [cgeo_lt f hf ht hQ blk hlt.le, hlo i hi]
    have hKJ : K i = J := Fin.ext hiJ
    rw [hKJ]
    refine ⟨(hact _).2 ⟨J, by rw [← hivg, ← hKJ]; exact hivK_lo i, G, hJ⟩, ?_⟩
    have := hivK_lo i
    rw [hKJ] at this
    unfold Geo.vb; rw [this]; exact hJ

end geo

end Conc

end Lovasz
