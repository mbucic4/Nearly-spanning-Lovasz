module
public import RequestProject.Prob

/-!
# The loaded induction (Lemmas 2.8, 2.9 and Fact 2.11)

Cycles are abstracted to an index type `ι` together with their vertex sets `Vs : ι → Finset V`.
A random subcollection `Cp` of a collection `C` is encoded by an outcome `x : ι → Bool` of the
product Bernoulli space: `Cp = C.filter (x · = true)`.
-/

@[expose] public section


open scoped BigOperators
open Classical

namespace Lovasz

noncomputable section

/-! ### Numerical facts -/

lemma rpow_one_sub_add_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {a : ℝ} (ha : 0 ≤ a) (b : ℕ) :
    (a + b) ^ (1 - δ) ≤ a ^ (1 - δ) + b := by
  refine (Real.rpow_add_le_add_rpow ha (Nat.cast_nonneg b) (by linarith) (by linarith)).trans ?_
  gcongr
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb; simp [Real.zero_rpow (by linarith : (1 - δ) ≠ 0)]
  · exact Real.rpow_le_self_of_one_le (by exact_mod_cast hb) (by linarith)

/-- **Fact 2.11.** -/
lemma fact_2_11 {α : Type*} (s : Finset α) {k : ℕ} (hk : 1 ≤ k) {δ p x : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (hp : (k : ℝ) ^ (-δ) ≤ p) (hx : 0 ≤ x) (y : α → ℝ) (hy0 : ∀ a ∈ s, 0 ≤ y a)
    (hyx : ∀ a ∈ s, y a ≤ x / k) :
    (x + ∑ a ∈ s, y a) ^ (1 - δ) ≤ x ^ (1 - δ) + p * ∑ a ∈ s, y a ^ (1 - δ) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  rcases hx.lt_or_eq with hx | hx
  · -- `x > 0`
    have hS : 0 ≤ ∑ a ∈ s, y a := Finset.sum_nonneg hy0
    have key : ∀ a ∈ s, y a * x ^ (-δ) ≤ p * y a ^ (1 - δ) := by
      intro a ha
      rcases (hy0 a ha).lt_or_eq with hya | hya
      · have h1 : y a ^ (1 - δ) = y a * y a ^ (-δ) := by
          rw [sub_eq_add_neg, Real.rpow_add hya, Real.rpow_one]
        have h2 : (x / k) ^ (-δ) ≤ y a ^ (-δ) :=
          Real.rpow_le_rpow_of_nonpos hya (hyx a ha) (by linarith)
        have h3 : (x / k) ^ (-δ) = x ^ (-δ) / (k : ℝ) ^ (-δ) := Real.div_rpow hx.le hk0.le _
        have h4 : 0 < (k : ℝ) ^ (-δ) := Real.rpow_pos_of_pos hk0 _
        have h5 : x ^ (-δ) ≤ (k : ℝ) ^ (-δ) * y a ^ (-δ) := by
          rw [h3, div_le_iff₀ h4] at h2; linarith
        rw [h1]
        have h6 : 0 ≤ y a ^ (-δ) := (Real.rpow_pos_of_pos hya _).le
        calc y a * x ^ (-δ) ≤ y a * ((k : ℝ) ^ (-δ) * y a ^ (-δ)) :=
              mul_le_mul_of_nonneg_left h5 hya.le
          _ ≤ y a * (p * y a ^ (-δ)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp h6) hya.le
          _ = p * (y a * y a ^ (-δ)) := by ring
      · rw [← hya]; simp [Real.zero_rpow (by linarith : (1 - δ) ≠ 0)]
    have hsum : (∑ a ∈ s, y a) * x ^ (-δ) ≤ p * ∑ a ∈ s, y a ^ (1 - δ) := by
      rw [Finset.sum_mul, Finset.mul_sum]; exact Finset.sum_le_sum key
    have hxs : x ^ (1 - δ) = x * x ^ (-δ) := by
      rw [sub_eq_add_neg, Real.rpow_add hx, Real.rpow_one]
    have hT : (x + ∑ a ∈ s, y a) ^ (1 - δ) =
        (x + ∑ a ∈ s, y a) * (x + ∑ a ∈ s, y a) ^ (-δ) := by
      rw [sub_eq_add_neg, Real.rpow_add (by linarith), Real.rpow_one]
    have hmono : (x + ∑ a ∈ s, y a) ^ (-δ) ≤ x ^ (-δ) :=
      Real.rpow_le_rpow_of_nonpos hx (by linarith) (by linarith)
    rw [hT, hxs]
    calc (x + ∑ a ∈ s, y a) * (x + ∑ a ∈ s, y a) ^ (-δ)
        ≤ (x + ∑ a ∈ s, y a) * x ^ (-δ) := mul_le_mul_of_nonneg_left hmono (by linarith)
      _ = x * x ^ (-δ) + (∑ a ∈ s, y a) * x ^ (-δ) := by ring
      _ ≤ _ := by linarith
  · -- `x = 0`
    subst hx
    have : ∀ a ∈ s, y a = 0 := fun a ha => le_antisymm (by simpa using hyx a ha) (hy0 a ha)
    rw [Finset.sum_congr rfl this]
    have hp0 : 0 ≤ p := le_trans (Real.rpow_pos_of_pos hk0 _).le hp
    simp only [Finset.sum_const_zero, add_zero, Real.zero_rpow (by linarith : (1 - δ) ≠ 0),
      zero_add]
    exact mul_nonneg hp0 (Finset.sum_nonneg fun a ha => Real.rpow_nonneg (hy0 a ha) _)

/-! ### Collections of cycles -/

variable {ι V : Type*}
variable (Vs : ι → Finset V)

/-- Two cycles meet if they share a vertex. -/
def Meets (c c' : ι) : Prop := (Vs c ∩ Vs c').Nonempty

/-- Reachability in the intersection graph of the cycles of `B`. -/
def ReachC (B : Finset ι) (a b : ι) : Prop :=
  Relation.ReflTransGen (fun c c' => c ∈ B ∧ c' ∈ B ∧ Meets Vs c c') a b

/-- The vertex set covered by a collection of cycles. -/
def cov (B : Finset ι) : Finset V := B.biUnion Vs

/-- The set of vertices lying in components of `B` containing a cycle of `R`. -/
def compV (B R : Finset ι) : Finset V :=
  B.biUnion (fun c => if ∃ r ∈ R, r ∈ B ∧ ReachC Vs B r c then Vs c else ∅)

/-- The total weight of a set of vertices. -/
def wsum (w : V → ℕ) (X : Finset V) : ℝ := ∑ v ∈ X, (w v : ℝ)

/-- The number of cycles of `H` meeting `c`. -/
def meetCount (H : Finset ι) (c : ι) : ℕ := (H.filter (Meets Vs c)).card

variable {Vs}

lemma meets_comm {c c' : ι} : Meets Vs c c' ↔ Meets Vs c' c := by
  unfold Meets; rw [Finset.inter_comm]

lemma mem_cov {B : Finset ι} {v : V} : v ∈ cov Vs B ↔ ∃ c ∈ B, v ∈ Vs c := by
  simp [cov]

lemma mem_compV {B R : Finset ι} {v : V} :
    v ∈ compV Vs B R ↔ ∃ c ∈ B, (∃ r ∈ R, r ∈ B ∧ ReachC Vs B r c) ∧ v ∈ Vs c := by
  simp only [compV, Finset.mem_biUnion]
  constructor
  · rintro ⟨c, hc, hv⟩
    split_ifs at hv with h
    · exact ⟨c, hc, h, hv⟩
    · simp at hv
  · rintro ⟨c, hc, h, hv⟩
    exact ⟨c, hc, by rw [if_pos h]; exact hv⟩

lemma compV_subset_cov (B R : Finset ι) : compV Vs B R ⊆ cov Vs B := by
  intro v hv
  obtain ⟨c, hc, -, hv⟩ := mem_compV.1 hv
  exact mem_cov.2 ⟨c, hc, hv⟩

lemma cov_mono {B B' : Finset ι} (h : B ⊆ B') : cov Vs B ⊆ cov Vs B' :=
  Finset.biUnion_subset_biUnion_of_subset_left _ h

lemma ReachC.mono {B B' : Finset ι} (h : B ⊆ B') {a b : ι} (hab : ReachC Vs B a b) :
    ReachC Vs B' a b := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail ⟨h hbc.1, h hbc.2.1, hbc.2.2⟩

lemma ReachC.mem {B : Finset ι} {a b : ι} (hab : ReachC Vs B a b) (ha : a ∈ B) : b ∈ B := by
  induction hab with
  | refl => exact ha
  | tail _ h _ => exact h.2.1

lemma ReachC.symm {B : Finset ι} {a b : ι} (hab : ReachC Vs B a b) : ReachC Vs B b a := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h ih =>
    exact Relation.ReflTransGen.head ⟨h.2.1, h.1, meets_comm.1 h.2.2⟩ ih

lemma ReachC.trans {B : Finset ι} {a b c : ι} (hab : ReachC Vs B a b) (hbc : ReachC Vs B b c) :
    ReachC Vs B a c := Relation.ReflTransGen.trans hab hbc

lemma ReachC.single {B : Finset ι} {a b : ι} (ha : a ∈ B) (hb : b ∈ B) (h : Meets Vs a b) :
    ReachC Vs B a b := Relation.ReflTransGen.single ⟨ha, hb, h⟩

lemma compV_mono {B B' R R' : Finset ι} (hB : B ⊆ B') (hR : R ⊆ R') :
    compV Vs B R ⊆ compV Vs B' R' := by
  intro v hv
  obtain ⟨c, hc, ⟨r, hr, hrB, hrc⟩, hv⟩ := mem_compV.1 hv
  exact mem_compV.2 ⟨c, hB hc, ⟨r, hR hr, hB hrB, hrc.mono hB⟩, hv⟩

/-- Leaving a set along a chain. -/
lemma ReachC.exists_boundary {B S : Finset ι} {a b : ι} (hab : ReachC Vs B a b) (ha : a ∈ S)
    (hb : b ∉ S) : ∃ c ∈ S, c ∈ B ∧ ∃ c' ∈ B, c' ∉ S ∧ Meets Vs c c' := by
  induction hab with
  | refl => exact absurd ha hb
  | @tail b' c _ h ih =>
    by_cases hb' : b' ∈ S
    · exact ⟨b', hb', h.1, c, h.2.1, hb, h.2.2⟩
    · exact ih hb'

/-- A chain from `r` to `c ≠ r` enters `B \ {r}` at a cycle meeting `r`. -/
lemma ReachC.exists_first {B : Finset ι} {r c : ι} (h : ReachC Vs B r c) (hc : c ≠ r) :
    ∃ c' ∈ B, c' ≠ r ∧ Meets Vs r c' ∧ ReachC Vs (B.erase r) c' c := by
  induction h with
  | refl => exact absurd rfl hc
  | @tail b c' hrb hbc ih =>
    by_cases hb : b = r
    · subst hb
      exact ⟨c', hbc.2.1, hc, hbc.2.2, Relation.ReflTransGen.refl⟩
    · obtain ⟨c'', hc'', hne, hm, hreach⟩ := ih hb
      exact ⟨c'', hc'', hne, hm, Relation.ReflTransGen.tail hreach
        ⟨Finset.mem_erase.2 ⟨hb, hbc.1⟩, Finset.mem_erase.2 ⟨hc, hbc.2.1⟩, hbc.2.2⟩⟩

lemma wsum_nonneg (w : V → ℕ) (X : Finset V) : 0 ≤ wsum w X :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

lemma wsum_mono (w : V → ℕ) {X Y : Finset V} (h : X ⊆ Y) : wsum w X ≤ wsum w Y :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun _ _ _ => Nat.cast_nonneg _

lemma wsum_union (w : V → ℕ) {X Y : Finset V} (h : Disjoint X Y) :
    wsum w (X ∪ Y) = wsum w X + wsum w Y := Finset.sum_union h

lemma wsum_eq_nat (w : V → ℕ) (X : Finset V) : wsum w X = ((∑ v ∈ X, w v : ℕ) : ℝ) := by
  simp [wsum]

lemma wsum_sdiff (w : V → ℕ) {X Y : Finset V} (h : X ⊆ Y) :
    wsum w (Y \ X) = wsum w Y - wsum w X := by
  have := wsum_union w (Finset.disjoint_sdiff : Disjoint X (Y \ X))
  rw [Finset.union_sdiff_of_subset h] at this; linarith

/-! ### The greedy partition -/

section greedy

variable (Vs)

/-- A connected collection of cycles. -/
def Conn (K : Finset ι) : Prop := ∀ a ∈ K, ∀ b ∈ K, ReachC Vs K a b

/-- Natural-number valued weight. -/
def wsumN (w : V → ℕ) (X : Finset V) : ℕ := ∑ v ∈ X, w v

variable (w : V → ℕ) (C R : Finset ι)

/-- Candidates for the next part of the greedy partition. -/
def cand (U : Finset ι) : Finset (Finset ι) :=
  (C \ U).powerset.filter (fun K => Conn Vs K ∧ (K ∩ R).card = 1)

/-- Lexicographic score `(w(V(K) \ V(U)), |K|)` encoded as a natural number. -/
def score (U K : Finset ι) : ℕ := wsumN w (cov Vs K \ cov Vs U) * (C.card + 1) + K.card

/-- One greedy step. -/
def gstep (U : Finset ι) : Finset ι :=
  if h : (cand Vs C R U).Nonempty then
    Classical.choose (Finset.exists_max_image _ (score Vs w C U) h)
  else ∅

/-- The cycles used by the first `i` parts. -/
def used : ℕ → Finset ι
  | 0 => ∅
  | i + 1 => used i ∪ gstep Vs w C R (used i)

/-- The `i`-th part of the greedy partition. -/
def Kseq (i : ℕ) : Finset ι := gstep Vs w C R (used Vs w C R i)

variable {Vs w C R}

lemma gstep_spec {U : Finset ι} (h : (cand Vs C R U).Nonempty) :
    gstep Vs w C R U ∈ cand Vs C R U ∧
      ∀ K ∈ cand Vs C R U, score Vs w C U K ≤ score Vs w C U (gstep Vs w C R U) := by
  unfold gstep
  rw [dif_pos h]
  exact Classical.choose_spec (Finset.exists_max_image _ (score Vs w C U) h)

lemma mem_cand {U K : Finset ι} :
    K ∈ cand Vs C R U ↔ K ⊆ C \ U ∧ Conn Vs K ∧ (K ∩ R).card = 1 := by
  simp [cand]

lemma used_succ (i : ℕ) : used Vs w C R (i + 1) = used Vs w C R i ∪ Kseq Vs w C R i := rfl

lemma used_mono {i j : ℕ} (h : i ≤ j) : used Vs w C R i ⊆ used Vs w C R j := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step _ ih => exact ih.trans Finset.subset_union_left

lemma conn_singleton (c : ι) : Conn Vs {c} := by
  intro a ha b hb
  simp only [Finset.mem_singleton] at ha hb
  subst ha hb; exact Relation.ReflTransGen.refl

lemma conn_insert {K : Finset ι} (hK : Conn Vs K) {c b : ι} (hb : b ∈ K) (hcb : Meets Vs c b) :
    Conn Vs (insert c K) := by
  have hsub : K ⊆ insert c K := Finset.subset_insert _ _
  have hc : ∀ a ∈ K, ReachC Vs (insert c K) c a := fun a ha =>
    (ReachC.single (Finset.mem_insert_self _ _) (hsub hb) hcb).trans ((hK b hb a ha).mono hsub)
  intro a ha a' ha'
  rcases Finset.mem_insert.1 ha with h1 | ha <;> rcases Finset.mem_insert.1 ha' with h2 | ha'
  · rw [h1, h2]; exact Relation.ReflTransGen.refl
  · rw [h1]; exact hc a' ha'
  · rw [h2]; exact (hc a ha).symm
  · exact (hK a ha a' ha').mono hsub

variable (Vs w C R) in
/-- Invariants of the greedy construction. -/
lemma used_invariant (i : ℕ) (hi : i ≤ R.card) (hR : R ⊆ C) :
    used Vs w C R i ⊆ C ∧ (used Vs w C R i ∩ R).card = i := by
  induction i with
  | zero => simp [used]
  | succ i ih =>
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hne : (cand Vs C R (used Vs w C R i)).Nonempty := by
      have : (R \ used Vs w C R i).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h
        have : R ⊆ used Vs w C R i := Finset.sdiff_eq_empty_iff_subset.1 h
        have : (used Vs w C R i ∩ R).card = R.card := by
          rw [Finset.inter_eq_right.2 this]
        omega
      obtain ⟨r, hr⟩ := this
      rw [Finset.mem_sdiff] at hr
      refine ⟨{r}, mem_cand.2 ⟨?_, conn_singleton r, ?_⟩⟩
      · intro x hx; rw [Finset.mem_singleton] at hx; subst hx
        exact Finset.mem_sdiff.2 ⟨hR hr.1, hr.2⟩
      · rw [Finset.singleton_inter_of_mem hr.1]; rfl
    obtain ⟨hK, -⟩ := gstep_spec (Vs := Vs) (w := w) hne
    obtain ⟨hKsub, -, hKR⟩ := mem_cand.1 hK
    refine ⟨Finset.union_subset h1 (hKsub.trans Finset.sdiff_subset), ?_⟩
    rw [used_succ, Finset.union_inter_distrib_right, Finset.card_union_of_disjoint]
    · unfold Kseq; rw [h2, hKR]
    · refine Finset.disjoint_left.2 fun x hx hx' => ?_
      have := hKsub (Finset.mem_of_mem_inter_left hx')
      exact (Finset.mem_sdiff.1 this).2 (Finset.mem_of_mem_inter_left hx)

variable (Vs w C R) in
lemma cand_nonempty (i : ℕ) (hi : i < R.card) (hR : R ⊆ C) :
    (cand Vs C R (used Vs w C R i)).Nonempty := by
  obtain ⟨h1, h2⟩ := used_invariant Vs w C R i hi.le hR
  have : (R \ used Vs w C R i).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    have : R ⊆ used Vs w C R i := Finset.sdiff_eq_empty_iff_subset.1 h
    have : (used Vs w C R i ∩ R).card = R.card := by
      rw [Finset.inter_eq_right.2 this]
    omega
  obtain ⟨r, hr⟩ := this
  rw [Finset.mem_sdiff] at hr
  refine ⟨{r}, mem_cand.2 ⟨?_, conn_singleton r, ?_⟩⟩
  · intro x hx; rw [Finset.mem_singleton] at hx; subst hx
    exact Finset.mem_sdiff.2 ⟨hR hr.1, hr.2⟩
  · rw [Finset.singleton_inter_of_mem hr.1]; rfl

lemma Kseq_mem_cand {i : ℕ} (hi : i < R.card) (hR : R ⊆ C) :
    Kseq Vs w C R i ∈ cand Vs C R (used Vs w C R i) :=
  (gstep_spec (cand_nonempty Vs w C R i hi hR)).1

lemma Kseq_max {i : ℕ} (hi : i < R.card) (hR : R ⊆ C) {K : Finset ι}
    (hK : K ∈ cand Vs C R (used Vs w C R i)) :
    score Vs w C (used Vs w C R i) K ≤ score Vs w C (used Vs w C R i) (Kseq Vs w C R i) :=
  (gstep_spec (cand_nonempty Vs w C R i hi hR)).2 K hK

lemma Kseq_subset {i : ℕ} (hi : i < R.card) (hR : R ⊆ C) :
    Kseq Vs w C R i ⊆ C \ used Vs w C R i :=
  (mem_cand.1 (Kseq_mem_cand hi hR)).1

lemma Kseq_conn {i : ℕ} (hi : i < R.card) (hR : R ⊆ C) : Conn Vs (Kseq Vs w C R i) :=
  (mem_cand.1 (Kseq_mem_cand hi hR)).2.1

lemma Kseq_inter_R {i : ℕ} (hi : i < R.card) (hR : R ⊆ C) :
    (Kseq Vs w C R i ∩ R).card = 1 :=
  (mem_cand.1 (Kseq_mem_cand hi hR)).2.2

lemma Kseq_subset_used {i j : ℕ} (hij : i < j) : Kseq Vs w C R i ⊆ used Vs w C R j :=
  (Finset.subset_union_right : Kseq Vs w C R i ⊆ used Vs w C R (i + 1)).trans (used_mono hij)

lemma Kseq_disjoint {i j : ℕ} (hij : i < j) (hj : j < R.card) (hR : R ⊆ C) :
    Disjoint (Kseq Vs w C R i) (Kseq Vs w C R j) := by
  refine Finset.disjoint_left.2 fun x hx hx' => ?_
  exact (Finset.mem_sdiff.1 (Kseq_subset hj hR hx')).2 (Kseq_subset_used hij hx)

/-- The cycle of `R` in the `i`-th part. -/
def Rr [Nonempty ι] (Vs : ι → Finset V) (w : V → ℕ) (C R : Finset ι) (i : ℕ) : ι :=
  if h : (Kseq Vs w C R i ∩ R).card = 1 then
    Classical.choose (Finset.card_eq_one.1 h)
  else Classical.arbitrary ι

lemma Kseq_inter_R_eq [Nonempty ι] {i : ℕ} (hi : i < R.card) (hR : R ⊆ C) :
    Kseq Vs w C R i ∩ R = {Rr Vs w C R i} := by
  have h := Kseq_inter_R (Vs := Vs) (w := w) hi hR
  unfold Rr; rw [dif_pos h]
  exact Classical.choose_spec (Finset.card_eq_one.1 h)

lemma Rr_mem_Kseq [Nonempty ι] {i : ℕ} (hi : i < R.card) (hR : R ⊆ C) :
    Rr Vs w C R i ∈ Kseq Vs w C R i := by
  have := Kseq_inter_R_eq (Vs := Vs) (w := w) hi hR
  have h2 : Rr Vs w C R i ∈ Kseq Vs w C R i ∩ R := by rw [this]; simp
  exact Finset.mem_of_mem_inter_left h2

lemma Rr_mem_R [Nonempty ι] {i : ℕ} (hi : i < R.card) (hR : R ⊆ C) :
    Rr Vs w C R i ∈ R := by
  have := Kseq_inter_R_eq (Vs := Vs) (w := w) hi hR
  have h2 : Rr Vs w C R i ∈ Kseq Vs w C R i ∩ R := by rw [this]; simp
  exact Finset.mem_of_mem_inter_right h2

lemma mem_R_of_mem_Kseq [Nonempty ι] {i : ℕ} (hi : i < R.card) (hR : R ⊆ C) {c : ι}
    (hc : c ∈ Kseq Vs w C R i) (hcR : c ∈ R) : c = Rr Vs w C R i := by
  have := Kseq_inter_R_eq (Vs := Vs) (w := w) hi hR
  have h2 : c ∈ Kseq Vs w C R i ∩ R := Finset.mem_inter.2 ⟨hc, hcR⟩
  rw [this] at h2; simpa using h2

/-- The greedy parts cannot be extended. -/
lemma no_extend {i : ℕ} (hi : i < R.card) (hR : R ⊆ C) {c b : ι} (hcC : c ∈ C)
    (hcU : c ∉ used Vs w C R i) (hcK : c ∉ Kseq Vs w C R i) (hcR : c ∉ R)
    (hb : b ∈ Kseq Vs w C R i) (hcb : Meets Vs c b) : False := by
  set K := Kseq Vs w C R i
  have hK := Kseq_mem_cand (Vs := Vs) (w := w) hi hR
  obtain ⟨hKsub, hKconn, hKR⟩ := mem_cand.1 hK
  have hK' : insert c K ∈ cand Vs C R (used Vs w C R i) := by
    refine mem_cand.2 ⟨?_, conn_insert hKconn hb hcb, ?_⟩
    · exact Finset.insert_subset (Finset.mem_sdiff.2 ⟨hcC, hcU⟩) hKsub
    · rw [Finset.insert_inter_of_notMem hcR]; exact hKR
  have hmax := Kseq_max (Vs := Vs) (w := w) hi hR hK'
  unfold score at hmax
  have h1 : wsumN w (cov Vs K \ cov Vs (used Vs w C R i)) ≤
      wsumN w (cov Vs (insert c K) \ cov Vs (used Vs w C R i)) :=
    Finset.sum_le_sum_of_subset
      (Finset.sdiff_subset_sdiff (cov_mono (Finset.subset_insert _ _)) (Finset.Subset.refl _))
  have h2 : (insert c K).card = K.card + 1 := Finset.card_insert_of_notMem hcK
  have h3 : K.card ≤ C.card := Finset.card_le_card (hKsub.trans Finset.sdiff_subset)
  have : wsumN w (cov Vs (insert c K) \ cov Vs (used Vs w C R i)) * (C.card + 1) + K.card + 1 ≤
      wsumN w (cov Vs K \ cov Vs (used Vs w C R i)) * (C.card + 1) + K.card := by
    rw [h2] at hmax; linarith
  nlinarith

/-- Claim 2.10, first part. -/
lemma C_subset_used (hR : R ⊆ C) (hconn : ∀ c ∈ C, ∃ r ∈ R, ReachC Vs C r c) :
    C ⊆ used Vs w C R R.card := by
  by_contra hne
  rw [Finset.not_subset] at hne
  obtain ⟨c, hcC, hcU⟩ := hne
  obtain ⟨r, hrR, hrc⟩ := hconn c hcC
  have hRU : R ⊆ used Vs w C R R.card := by
    have h := (used_invariant Vs w C R R.card le_rfl hR).2
    have : used Vs w C R R.card ∩ R = R :=
      Finset.eq_of_subset_of_card_le (Finset.inter_subset_right :
        used Vs w C R R.card ∩ R ⊆ R) (by rw [h])
    intro r hr
    have hr' : r ∈ used Vs w C R R.card ∩ R := by rw [this]; exact hr
    exact (Finset.mem_inter.1 hr').1
  obtain ⟨b, hbU, hbC, c', hc'C, hc'U, hbc'⟩ := hrc.exists_boundary (hRU hrR) hcU
  -- `b` lies in some part `Kseq i`
  have : ∀ j, ∀ x ∈ used Vs w C R j, ∃ i < j, x ∈ Kseq Vs w C R i := by
    intro j
    induction j with
    | zero => simp [used]
    | succ j ih =>
      intro x hx
      rw [used_succ, Finset.mem_union] at hx
      rcases hx with hx | hx
      · obtain ⟨i, hi, hx⟩ := ih x hx; exact ⟨i, by omega, hx⟩
      · exact ⟨j, by omega, hx⟩
  obtain ⟨i, hi, hbi⟩ := this _ b hbU
  refine no_extend (Vs := Vs) (w := w) hi hR hc'C (fun h => hc'U (used_mono hi.le h))
    (fun h => hc'U (Kseq_subset_used hi h)) (fun h => hc'U (hRU h)) hbi (meets_comm.1 hbc')

/-- Claim 2.10, second part. -/
lemma Kseq_cov_disjoint [Nonempty ι] {i j : ℕ} (hij : i < j) (hj : j < R.card) (hR : R ⊆ C)
    {c : ι} (hc : c ∈ Kseq Vs w C R j) (hcr : c ≠ Rr Vs w C R j) :
    Disjoint (cov Vs (Kseq Vs w C R i)) (Vs c) := by
  rw [Finset.disjoint_left]
  intro v hv hvc
  obtain ⟨b, hb, hvb⟩ := mem_cov.1 hv
  have hcC : c ∈ C := (Finset.mem_sdiff.1 (Kseq_subset hj hR hc)).1
  have hcUj := (Finset.mem_sdiff.1 (Kseq_subset hj hR hc)).2
  refine no_extend (Vs := Vs) (w := w) (hij.trans hj) hR hcC (fun h => hcUj (used_mono hij.le h))
    (fun h => hcUj (Kseq_subset_used hij h)) (fun h => hcr (mem_R_of_mem_Kseq hj hR hc h)) hb
    ⟨v, Finset.mem_inter.2 ⟨hvc, hvb⟩⟩

/-- The new vertices of the `i`-th part. -/
def Yset (Vs : ι → Finset V) (w : V → ℕ) (C R : Finset ι) (i : ℕ) : Finset V :=
  cov Vs (Kseq Vs w C R i) \ cov Vs (used Vs w C R i)

lemma Yset_antitone {i : ℕ} (hi : i + 1 < R.card) (hR : R ⊆ C) :
    wsumN w (Yset Vs w C R (i + 1)) ≤ wsumN w (Yset Vs w C R i) := by
  have hK1 := Kseq_mem_cand (Vs := Vs) (w := w) hi hR
  obtain ⟨hsub, hconn, hRc⟩ := mem_cand.1 hK1
  have hcand : Kseq Vs w C R (i + 1) ∈ cand Vs C R (used Vs w C R i) :=
    mem_cand.2 ⟨hsub.trans (Finset.sdiff_subset_sdiff (Finset.Subset.refl _) (used_mono (by omega))), hconn, hRc⟩
  have hmax := Kseq_max (Vs := Vs) (w := w) (by omega : i < R.card) hR hcand
  unfold score at hmax
  have hcard : (Kseq Vs w C R (i + 1)).card ≤ C.card :=
    Finset.card_le_card (hsub.trans Finset.sdiff_subset)
  have h1 : wsumN w (cov Vs (Kseq Vs w C R (i + 1)) \ cov Vs (used Vs w C R i)) ≤
      wsumN w (Yset Vs w C R i) := by
    unfold Yset
    by_contra hlt
    push_neg at hlt
    have hcard2 : (Kseq Vs w C R i).card ≤ C.card :=
      Finset.card_le_card ((Kseq_subset (Vs := Vs) (w := w) (by omega) hR).trans
        Finset.sdiff_subset)
    have := Nat.mul_le_mul_right (C.card + 1) (Nat.succ_le_of_lt hlt)
    rw [Nat.succ_mul] at this
    omega
  refine le_trans ?_ h1
  unfold Yset
  exact Finset.sum_le_sum_of_subset
    (Finset.sdiff_subset_sdiff (Finset.Subset.refl _) (cov_mono (used_mono (by omega))))

end greedy

end

end Lovasz
