module
public import RequestProject.LinkGrowth
public import RequestProject.LinkReach

/-!
# Expansion into a random set (Lemma 5.5)

The random set is exposed in `ℓ + 2` independent rounds: round `0` (probability `q/20`) gives
the starting set `W ∩ S₀ \ Z`, rounds `1, …, ℓ` (probability `p` each) are used to grow the
explored set `Bᵢ` by a factor `1 + 1/(1000 (log n)^c)` each (Claim 5.5.1, `growth_step`), and
the last round (probability `0.88 q`) samples a large part of the explored set.  The union of
the rounds is a random set of density at most `q`, and the resulting event is up-closed.
-/

@[expose] public section


open scoped BigOperators
open Classical

namespace Lovasz

noncomputable section

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- The allowed vertices: those of `U` in the random set `y`, except the forbidden ones. -/
def allowed (U Z : Finset V) (y : V → Bool) : Finset V := (U.filter (fun v => y v = true)) \ Z

/-- The vertices of the random set reachable from `S` in at most `d` steps through it. -/
def ballY (G : SimpleGraph V) (U Z : Finset V) (y : V → Bool) (d : ℕ) (S : Finset V) :
    Finset V :=
  reach G (allowed U Z y) d S ∩ allowed U Z y

omit [Fintype V] in
lemma allowed_mono {U Z : Finset V} {y y' : V → Bool} (h : BLe y y') :
    allowed U Z y ⊆ allowed U Z y' := by
  intro v hv
  simp only [allowed, Finset.mem_sdiff, Finset.mem_filter] at hv ⊢
  exact ⟨⟨hv.1.1, h v hv.1.2⟩, hv.2⟩

omit [Fintype V] in
lemma ballY_mono {U Z : Finset V} {y y' : V → Bool} (h : BLe y y') {d : ℕ} {S S' : Finset V}
    (hS : S ⊆ S') : ballY G U Z y d S ⊆ ballY G U Z y' d S' :=
  Finset.inter_subset_inter (reach_mono (allowed_mono h) hS d) (allowed_mono h)

/-- The random set of round `k`. -/
def rnd {m : ℕ} (Y : Fin m → V → Bool) (k : ℕ) : V → Bool :=
  fun v => if h : k < m then Y ⟨k, h⟩ v else false

/-- The union of the rounds. -/
def unionY {m : ℕ} (Y : Fin m → V → Bool) : V → Bool := fun v => decide (∃ j, Y j v = true)

/-- The explored sets. -/
def Bseq (G : SimpleGraph V) (U W Z : Finset V) {m : ℕ} (Y : Fin m → V → Bool) : ℕ → Finset V
  | 0 => (W.filter (fun v => rnd Y 0 v = true)) \ Z
  | i + 1 => Bseq G U W Z Y i ∪ newSet G U (Bseq G U W Z Y i) Z (rnd Y (i + 1))

section det

variable {U W Z : Finset V} {m : ℕ}

omit [Fintype V] in
lemma rnd_update_ne (Y : Fin m → V → Bool) (j : Fin m) (z : V → Bool) {k : ℕ}
    (hk : k ≠ j.val) : rnd (Function.update Y j z) k = rnd Y k := by
  funext v
  simp only [rnd]
  split_ifs with h
  · rw [Function.update_of_ne]; intro h'; apply hk; rw [← h']
  · rfl

omit [Fintype V] in
lemma rnd_update_self (Y : Fin m → V → Bool) (j : Fin m) (z : V → Bool) :
    rnd (Function.update Y j z) j.val = z := by
  funext v
  simp [rnd, j.2]

omit [Fintype V] in
lemma rnd_update_eq (Y : Fin m → V → Bool) (j : Fin m) (z : V → Bool) {k : ℕ} (hk : k = j.val) :
    rnd (Function.update Y j z) k = z := by
  subst hk; exact rnd_update_self Y j z

omit [Fintype V] in
lemma Bseq_congr : ∀ (i : ℕ) (Y Y' : Fin m → V → Bool), (∀ k ≤ i, rnd Y k = rnd Y' k) →
    Bseq G U W Z Y i = Bseq G U W Z Y' i
  | 0, Y, Y', h => by simp only [Bseq, h 0 le_rfl]
  | i + 1, Y, Y', h => by
    simp only [Bseq]
    rw [Bseq_congr i Y Y' (fun k hk => h k (Nat.le_succ_of_le hk)), h (i + 1) le_rfl]

omit [Fintype V] in
lemma Bseq_update (Y : Fin m → V → Bool) (j : Fin m) (z : V → Bool) {i : ℕ} (hi : i < j.val) :
    Bseq G U W Z (Function.update Y j z) i = Bseq G U W Z Y i :=
  Bseq_congr i _ _ fun k hk => rnd_update_ne Y j z (by omega)

omit [Fintype V] in
lemma Bseq_sub (hW : W ⊆ U) (Y : Fin m → V → Bool) : ∀ i, Bseq G U W Z Y i ⊆ U \ Z
  | 0 => by
    intro v hv
    simp only [Bseq, Finset.mem_sdiff, Finset.mem_filter] at hv
    exact Finset.mem_sdiff.2 ⟨hW hv.1.1, hv.2⟩
  | i + 1 => by
    simp only [Bseq]
    refine Finset.union_subset (Bseq_sub hW Y i) fun v hv => ?_
    obtain ⟨hv1, -⟩ := Finset.mem_filter.1 hv
    obtain ⟨hvU, hvBZ⟩ := Finset.mem_sdiff.1 hv1
    exact Finset.mem_sdiff.2 ⟨hvU, fun hvZ => hvBZ (Finset.mem_union_right _ hvZ)⟩

omit [Fintype V] in
lemma Bseq_mono (Y : Fin m → V → Bool) (i : ℕ) : Bseq G U W Z Y i ⊆ Bseq G U W Z Y (i + 1) :=
  Finset.subset_union_left

omit [Fintype V] in
lemma Bseq_card_succ (Y : Fin m → V → Bool) (i : ℕ) :
    (Bseq G U W Z Y (i + 1)).card =
      (Bseq G U W Z Y i).card + (newSet G U (Bseq G U W Z Y i) Z (rnd Y (i + 1))).card := by
  simp only [Bseq]
  refine Finset.card_union_of_disjoint (Finset.disjoint_left.2 fun v hv hv' => ?_)
  obtain ⟨hv1, -⟩ := Finset.mem_filter.1 hv'
  exact (Finset.mem_sdiff.1 hv1).2 (Finset.mem_union_left _ hv)

omit [Fintype V] in
lemma unionY_of_rnd {Y : Fin m → V → Bool} {k : ℕ} {v : V} (h : rnd Y k v = true) :
    unionY Y v = true := by
  simp only [rnd] at h
  split_ifs at h with hk
  · simp only [unionY, decide_eq_true_eq]; exact ⟨_, h⟩

omit [Fintype V] in
lemma Bseq_reach (hW : W ⊆ U) (Y : Fin m → V → Bool) : ∀ i, ∀ v ∈ Bseq G U W Z Y i,
    unionY Y v = true → v ∈ reach G (allowed U Z (unionY Y)) i (W ∩ allowed U Z (unionY Y))
  | 0, v, hv, hvY => by
    simp only [Bseq, Finset.mem_sdiff, Finset.mem_filter] at hv
    show v ∈ W ∩ allowed U Z (unionY Y)
    simp only [allowed, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_filter]
    exact ⟨hv.1.1, ⟨hW hv.1.1, hvY⟩, hv.2⟩
  | i + 1, v, hv, hvY => by
    simp only [Bseq, Finset.mem_union] at hv
    simp only [reach, Finset.mem_union]
    rcases hv with hv | hv
    · exact Or.inl (Bseq_reach hW Y i v hv hvY)
    · right
      obtain ⟨hv1, b, hb, hyb, hbv⟩ := Finset.mem_filter.1 hv
      obtain ⟨hvU, hvBZ⟩ := Finset.mem_sdiff.1 hv1
      refine Finset.mem_filter.2 ⟨?_, b, Bseq_reach hW Y i b hb (unionY_of_rnd hyb), hbv⟩
      simp only [allowed, Finset.mem_sdiff, Finset.mem_filter]
      exact ⟨⟨hvU, hvY⟩, fun hvZ => hvBZ (Finset.mem_union_right _ hvZ)⟩

end det

omit [Fintype V] in
lemma slice_ppr_eq {m : ℕ} (pr : Fin m → ℝ) (j : Fin m) (Y : Fin m → V → Bool)
    (P : (Fin m → V → Bool) → Prop) (Q : (V → Bool) → Prop)
    (h : ∀ k, P (Function.update Y j k) ↔ Q k) [Fintype V] :
    ∑ k, roundD pr j k * (if P (Function.update Y j k) then (1 : ℝ) else 0) =
      ppr (fun _ : V => bern (pr j)) Q := by
  unfold ppr pex pwt roundD
  refine Finset.sum_congr rfl fun k _ => ?_
  dsimp only
  by_cases hq : Q k
  · rw [if_pos ((h k).2 hq), if_pos hq]
  · rw [if_neg (fun hp => hq ((h k).1 hp)), if_neg hq]

/-- The round probabilities. -/
def prR (q p : ℝ) (ℓ : ℕ) (j : Fin (ℓ + 2)) : ℝ :=
  if j.val = 0 then q / 20 else if j.val = ℓ + 1 then 0.88 * q else p

lemma prod_one_sub_ge {α : Type*} (s : Finset α) (a : α → ℝ) (h0 : ∀ j ∈ s, 0 ≤ a j)
    (h1 : ∀ j ∈ s, a j ≤ 1) : 1 - ∑ j ∈ s, a j ≤ ∏ j ∈ s, (1 - a j) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have ih' := ih (fun j hj => h0 j (Finset.mem_insert_of_mem hj))
      (fun j hj => h1 j (Finset.mem_insert_of_mem hj))
    have hai := h0 i (Finset.mem_insert_self _ _)
    have hai1 := h1 i (Finset.mem_insert_self _ _)
    have hp : 0 ≤ ∏ j ∈ s, (1 - a j) :=
      Finset.prod_nonneg fun j hj => by linarith [h1 j (Finset.mem_insert_of_mem hj)]
    have hs : 0 ≤ ∑ j ∈ s, a j := Finset.sum_nonneg fun j hj => h0 j (Finset.mem_insert_of_mem hj)
    nlinarith

lemma sum_ite_val_le {ℓ : ℕ} (k : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    ∑ j : Fin (ℓ + 2), (if j.val = k then a else 0) ≤ a := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have : (Finset.univ.filter (fun j : Fin (ℓ + 2) => j.val = k)).card ≤ 1 := by
    refine Finset.card_le_one.2 fun a ha b hb => ?_
    exact Fin.ext ((Finset.mem_filter.1 ha).2.trans (Finset.mem_filter.1 hb).2.symm)
  have : ((Finset.univ.filter (fun j : Fin (ℓ + 2) => j.val = k)).card : ℝ) ≤ 1 := by
    exact_mod_cast this
  nlinarith

lemma union_density_le {q p : ℝ} {ℓ : ℕ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hℓp : (ℓ + 2) * p ≤ q / 20) :
    1 - ∏ j, (1 - prR q p ℓ j) ≤ q := by
  have h0 : ∀ j, 0 ≤ prR q p ℓ j := fun j => by
    simp only [prR]; split_ifs <;> positivity
  have h1 : ∀ j, prR q p ℓ j ≤ 1 := fun j => by
    simp only [prR]; split_ifs <;> linarith
  have h2 := prod_one_sub_ge Finset.univ (prR q p ℓ) (fun j _ => h0 j) (fun j _ => h1 j)
  have h3 : ∀ j : Fin (ℓ + 2), prR q p ℓ j ≤ (if j.val = 0 then q / 20 else 0) +
      (if j.val = ℓ + 1 then 0.88 * q else 0) + p := by
    intro j
    simp only [prR]
    split_ifs <;> linarith
  have h4 : ∑ j, prR q p ℓ j ≤ q / 20 + 0.88 * q + (ℓ + 2) * p := by
    refine (Finset.sum_le_sum fun j _ => h3 j).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have := sum_ite_val_le (ℓ := ℓ) 0 (a := q / 20) (by positivity)
    have := sum_ite_val_le (ℓ := ℓ) (ℓ + 1) (a := 0.88 * q) (by positivity)
    push_cast
    linarith
  linarith

lemma exp_neg_small_bound : Real.exp (-0.05) ≤ 0.9525 := by
  have := Real.abs_exp_sub_one_sub_id_le (x := -0.05) (by norm_num [abs_of_neg])
  have := (abs_le.1 this).2
  norm_num at this ⊢
  linarith

set_option maxHeartbeats 1000000 in
/-- **Lemma 5.5** (expansion of a fixed set into a random set, avoiding `Z`). -/
theorem explore {U W Z : Finset V} {c : ℕ} {s q p : ℝ} (hexp : IsExpander G U (1 / 16) c s)
    (hW : W ⊆ U) (hq0 : 0 < q) (hq1 : q ≤ 1) (hp0 : 0 < p) (hp1 : p ≤ 1) {ℓ : ℕ}
    (hℓp : (ℓ + 2) * p ≤ q / 20) (hL : 1 ≤ Real.log U.card ^ c)
    (hrL : 13 * Real.log U.card ^ c ≤ (⌈1 / p⌉₊ : ℝ)) (hs : 4 * (⌈1 / p⌉₊ : ℝ) ^ 3 ≤ s)
    (hWq : 50 ≤ q * W.card) (hZ : 100000 * Real.log U.card ^ c * Z.card ≤ q * W.card)
    (hgrow : 2 * (U.card : ℝ) / 3 <
      (1 + 1 / (1000 * Real.log U.card ^ c)) ^ ℓ * (q * W.card / 50)) :
    1 - (Real.exp (-(q * W.card / 160)) +
      ℓ * (Real.exp (-(p * (q * W.card / 50) / (100 * ⌈1 / p⌉₊))) +
        2 * (⌈1 / p⌉₊ : ℝ) ^ 3 * Real.exp (-((q * W.card / 50) / (4000 * (⌈1 / p⌉₊ : ℝ) ^ 3 *
          Real.log U.card ^ c)))) +
      Real.exp (-(0.00036 * q * U.card))) ≤
    ppr (fun _ : V => bern q) (fun y => 0.55 * q * U.card ≤ (ballY G U Z y ℓ (W ∩ allowed U Z y)).card) := by
  set K := Real.log U.card ^ c with hKdef
  set r := ⌈1 / p⌉₊ with hrdef
  set w := q * W.card / 50 with hwdef
  set θ := 0.55 * q * U.card with hθdef
  set pr := prR q p ℓ
  have hK0 : 0 < K := by linarith
  have hpr0 : ∀ j, 0 ≤ pr j := fun j => by simp only [pr, prR]; split_ifs <;> positivity
  have hpr1 : ∀ j, pr j ≤ 1 := fun j => by simp only [pr, prR]; split_ifs <;> linarith
  have hμ : IsPD (roundD (V := V) pr) := isPD_roundD hpr0 hpr1
  have hw1 : 1 ≤ w := by simp only [w]; linarith
  have hZw : 2000 * K * Z.card ≤ w := by simp only [w]; linarith
  -- the failure events
  set F0 : (Fin (ℓ + 2) → V → Bool) → Prop :=
    fun Y => (cntT W (rnd Y 0) : ℝ) ≤ q * W.card / 40
  set Fg : ℕ → (Fin (ℓ + 2) → V → Bool) → Prop := fun i Y =>
    w ≤ (Bseq G U W Z Y i).card ∧ 3 * (Bseq G U W Z Y i).card ≤ 2 * U.card ∧
      2000 * K * Z.card ≤ (Bseq G U W Z Y i).card ∧
      ((newSet G U (Bseq G U W Z Y i) Z (rnd Y (i + 1))).card : ℝ) <
        (Bseq G U W Z Y i).card / (1000 * K)
  set Ff : (Fin (ℓ + 2) → V → Bool) → Prop := fun Y =>
    2 * U.card < 3 * (Bseq G U W Z Y ℓ).card ∧ (cntT (Bseq G U W Z Y ℓ) (rnd Y (ℓ + 1)) : ℝ) ≤ θ
  -- probability bounds
  have hP0 : ppr (roundD pr) F0 ≤ Real.exp (-(q * W.card / 160)) := by
    refine ppr_le_of_slice_dec hμ ⟨0, by omega⟩ fun Y => ?_
    have e : ∀ k, F0 (Function.update Y ⟨0, by omega⟩ k) ↔ (cntT W k : ℝ) ≤ q * W.card / 40 := by
      intro k; simp only [F0]
      rw [rnd_update_eq Y ⟨0, by omega⟩ k rfl]
    refine le_trans (le_of_eq (slice_ppr_eq pr _ Y F0 _ e)) ?_
    have hpr : pr ⟨0, by omega⟩ = q / 20 := by simp [pr, prR]
    rw [hpr]
    refine (chernoff_lower (by positivity) (by linarith) W _).trans (Real.exp_le_exp.2 ?_)
    have he := exp_neg_one_bounds
    have hWc : (0 : ℝ) ≤ q * W.card := by positivity
    nlinarith
  have hPg : ∀ i < ℓ, ppr (roundD pr) (Fg i) ≤
      Real.exp (-(p * w / (100 * r))) + 2 * (r : ℝ) ^ 3 * Real.exp (-(w / (4000 * (r : ℝ) ^ 3 * K))) := by
    intro i hi
    have hE : 0 ≤ Real.exp (-(p * w / (100 * r))) +
        2 * (r : ℝ) ^ 3 * Real.exp (-(w / (4000 * (r : ℝ) ^ 3 * K))) := by positivity
    refine ppr_le_of_slice_dec hμ ⟨i + 1, by omega⟩ fun Y => ?_
    set B := Bseq G U W Z Y i
    have e : ∀ k, Fg i (Function.update Y ⟨i + 1, by omega⟩ k) ↔
        (w ≤ B.card ∧ 3 * B.card ≤ 2 * U.card ∧ 2000 * K * Z.card ≤ B.card ∧
          ((newSet G U B Z k).card : ℝ) < B.card / (1000 * K)) := by
      intro k
      simp only [Fg]
      rw [Bseq_update Y ⟨i + 1, by omega⟩ k (by simp), rnd_update_eq Y ⟨i + 1, by omega⟩ k rfl]
    refine le_trans (le_of_eq (slice_ppr_eq pr _ Y (Fg i) _ e)) ?_
    have hpr : pr ⟨i + 1, by omega⟩ = p := by
      simp only [pr, prR]; rw [if_neg (by simp), if_neg (by simp; omega)]
    rw [hpr]
    by_cases hc : w ≤ B.card ∧ 3 * B.card ≤ 2 * U.card ∧ 2000 * K * Z.card ≤ B.card
    · obtain ⟨hc1, hc2, hc3⟩ := hc
      have hB1 : 1 ≤ B.card := by exact_mod_cast hw1.trans hc1
      have hgs := growth_step hexp hp0 hp1 hL hrL hs ((Bseq_sub hW Y i).trans Finset.sdiff_subset)
        hB1 hc2 hc3
      refine (ppr_mono (isPD_bern hp0.le hp1) fun k hk => hk.2.2.2).trans (hgs.trans ?_)
      have hr0 : (0 : ℝ) < r := by linarith
      gcongr
    · have : ppr (fun _ : V => bern p) (fun k => w ≤ B.card ∧ 3 * B.card ≤ 2 * U.card ∧
          2000 * K * Z.card ≤ B.card ∧ ((newSet G U B Z k).card : ℝ) < B.card / (1000 * K)) = 0 := by
        unfold ppr pex
        refine Finset.sum_eq_zero fun k _ => ?_
        dsimp only
        rw [if_neg (fun h => hc ⟨h.1, h.2.1, h.2.2.1⟩), mul_zero]
      rw [this]; exact hE
  have hPf : ppr (roundD pr) Ff ≤ Real.exp (-(0.00036 * q * U.card)) := by
    refine ppr_le_of_slice_dec hμ ⟨ℓ + 1, by omega⟩ fun Y => ?_
    set B := Bseq G U W Z Y ℓ
    have e : ∀ k, Ff (Function.update Y ⟨ℓ + 1, by omega⟩ k) ↔
        (2 * U.card < 3 * B.card ∧ (cntT B k : ℝ) ≤ θ) := by
      intro k
      simp only [Ff]
      rw [Bseq_update Y ⟨ℓ + 1, by omega⟩ k (by simp), rnd_update_eq Y ⟨ℓ + 1, by omega⟩ k rfl]
    refine le_trans (le_of_eq (slice_ppr_eq pr _ Y Ff _ e)) ?_
    have hpr : pr ⟨ℓ + 1, by omega⟩ = 0.88 * q := by
      simp only [pr, prR]; rw [if_neg (by simp)]; simp
    rw [hpr]
    have hμf : IsPD (fun _ : V => bern (0.88 * q)) := isPD_bern (by positivity) (by linarith)
    by_cases hc : 2 * U.card < 3 * B.card
    · refine (ppr_mono hμf fun k hk => hk.2).trans ?_
      refine (chernoff_lower_lam (by positivity) (by linarith) B θ (l := 0.05) (by norm_num)).trans
        (Real.exp_le_exp.2 ?_)
      have he := exp_neg_small_bound
      have hBc : (2 * U.card : ℝ) < 3 * B.card := by exact_mod_cast hc
      have hqB : 0.88 * q * (2 * U.card) ≤ 0.88 * q * (3 * B.card) :=
        mul_le_mul_of_nonneg_left hBc.le (by positivity)
      have h1 : 0.0475 * (0.88 * q * B.card) ≤ (1 - Real.exp (-0.05)) * (0.88 * q * B.card) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have h2 : (1 - Real.exp (-0.05)) * (0.88 * q) * B.card =
          (1 - Real.exp (-0.05)) * (0.88 * q * B.card) := by ring
      simp only [θ]
      nlinarith
    · have : ppr (fun _ : V => bern (0.88 * q))
          (fun k => 2 * U.card < 3 * B.card ∧ (cntT B k : ℝ) ≤ θ) = 0 := by
        unfold ppr pex
        refine Finset.sum_eq_zero fun k _ => ?_
        dsimp only
        rw [if_neg (fun h => hc h.1), mul_zero]
      rw [this]; exact (Real.exp_pos _).le
  -- the deterministic part
  have hdet : ∀ Y : Fin (ℓ + 2) → V → Bool, ¬ F0 Y → (∀ i < ℓ, ¬ Fg i Y) → ¬ Ff Y →
      θ ≤ (ballY G U Z (unionY Y) ℓ (W ∩ allowed U Z (unionY Y))).card := by
    intro Y h0 hg hf
    have hchain : ∀ i ≤ ℓ, 2 * U.card < 3 * (Bseq G U W Z Y i).card ∨
        (1 + 1 / (1000 * K)) ^ i * w ≤ (Bseq G U W Z Y i).card := by
      intro i
      induction i with
      | zero =>
        intro _
        right
        simp only [pow_zero, one_mul]
        have h1 := card_sdiff_ge (W.filter (fun v => rnd Y 0 v = true)) Z
        simp only [F0, not_le] at h0
        have : (cntT W (rnd Y 0) : ℝ) = (W.filter (fun v => rnd Y 0 v = true)).card := rfl
        have hZ' : (Z.card : ℝ) ≤ q * W.card / 200 := by
          have : (Z.card : ℝ) ≤ 500 * K * Z.card := by
            have := Nat.cast_nonneg (α := ℝ) Z.card; nlinarith
          linarith
        show w ≤ ((W.filter (fun v => rnd Y 0 v = true)) \ Z).card
        simp only [w]
        linarith
      | succ i ih =>
        intro hi
        rcases ih (by omega) with h | h
        · left
          have := Finset.card_le_card (Bseq_mono (G := G) (U := U) (W := W) (Z := Z) Y i)
          omega
        · by_cases h3 : 2 * U.card < 3 * (Bseq G U W Z Y i).card
          · left
            have := Finset.card_le_card (Bseq_mono (G := G) (U := U) (W := W) (Z := Z) Y i)
            omega
          right
          push_neg at h3
          have hpow : 1 ≤ (1 + 1 / (1000 * K)) ^ i := one_le_pow₀ (by
            have : 0 ≤ 1 / (1000 * K) := by positivity
            linarith)
          have hwB : w ≤ (Bseq G U W Z Y i).card := by nlinarith
          have hnot := hg i (by omega)
          simp only [Fg, not_and, not_lt] at hnot
          have hnew := hnot hwB h3 (hZw.trans hwB)
          rw [Bseq_card_succ]
          push_cast
          rw [pow_succ]
          have ha : 0 ≤ 1 / (1000 * K) := by positivity
          have : (Bseq G U W Z Y i).card / (1000 * K) = (Bseq G U W Z Y i).card * (1 / (1000 * K)) := by
            ring
          rw [this] at hnew
          nlinarith
    have hℓ : 2 * U.card < 3 * (Bseq G U W Z Y ℓ).card := by
      rcases hchain ℓ le_rfl with h | h
      · exact h
      · have : (2 * U.card : ℝ) < 3 * (Bseq G U W Z Y ℓ).card := by linarith
        exact_mod_cast this
    simp only [Ff, not_and, not_le] at hf
    have hcnt := hf hℓ
    refine le_trans hcnt.le (Nat.cast_le.2 (Finset.card_le_card fun v hv => ?_))
    obtain ⟨hvB, hvr⟩ := Finset.mem_filter.1 hv
    have hvY := unionY_of_rnd hvr
    have hvUZ := Bseq_sub hW Y ℓ hvB
    refine Finset.mem_inter.2 ⟨Bseq_reach hW Y ℓ v hvB hvY, ?_⟩
    simp only [allowed, Finset.mem_sdiff, Finset.mem_filter]
    exact ⟨⟨(Finset.mem_sdiff.1 hvUZ).1, hvY⟩, (Finset.mem_sdiff.1 hvUZ).2⟩
  -- combining
  have hbad : ppr (roundD pr) (fun Y => ¬ θ ≤ (ballY G U Z (unionY Y) ℓ (W ∩ allowed U Z (unionY Y))).card) ≤
      Real.exp (-(q * W.card / 160)) +
        ℓ * (Real.exp (-(p * w / (100 * r))) +
          2 * (r : ℝ) ^ 3 * Real.exp (-(w / (4000 * (r : ℝ) ^ 3 * K)))) +
        Real.exp (-(0.00036 * q * U.card)) := by
    calc ppr (roundD pr) (fun Y => ¬ θ ≤ (ballY G U Z (unionY Y) ℓ (W ∩ allowed U Z (unionY Y))).card)
        ≤ ppr (roundD pr) (fun Y => F0 Y ∨ (∃ i ∈ Finset.range ℓ, Fg i Y) ∨ Ff Y) := by
          refine ppr_mono hμ fun Y hY => ?_
          by_contra hc
          push_neg at hc
          exact hY (hdet Y hc.1 (fun i hi => hc.2.1 i (Finset.mem_range.2 hi)) hc.2.2)
      _ ≤ ppr (roundD pr) F0 + (ppr (roundD pr) (fun Y => ∃ i ∈ Finset.range ℓ, Fg i Y) +
            ppr (roundD pr) Ff) := by
          refine (ppr_or_le hμ _ _).trans ?_
          gcongr
          exact ppr_or_le hμ _ _
      _ ≤ Real.exp (-(q * W.card / 160)) + (∑ i ∈ Finset.range ℓ, ppr (roundD pr) (Fg i) +
            Real.exp (-(0.00036 * q * U.card))) := by
          gcongr
          exact ppr_exists_le hμ _ _
      _ ≤ Real.exp (-(q * W.card / 160)) + (∑ i ∈ Finset.range ℓ,
            (Real.exp (-(p * w / (100 * r))) +
              2 * (r : ℝ) ^ 3 * Real.exp (-(w / (4000 * (r : ℝ) ^ 3 * K)))) +
            Real.exp (-(0.00036 * q * U.card))) := by
          gcongr with i hi
          exact hPg i (Finset.mem_range.1 hi)
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have hgood : 1 - (Real.exp (-(q * W.card / 160)) +
        ℓ * (Real.exp (-(p * w / (100 * r))) +
          2 * (r : ℝ) ^ 3 * Real.exp (-(w / (4000 * (r : ℝ) ^ 3 * K)))) +
        Real.exp (-(0.00036 * q * U.card))) ≤
      ppr (roundD pr) (fun Y => θ ≤ (ballY G U Z (unionY Y) ℓ (W ∩ allowed U Z (unionY Y))).card) := by
    have := ppr_not hμ (fun Y => θ ≤ (ballY G U Z (unionY Y) ℓ (W ∩ allowed U Z (unionY Y))).card)
    linarith
  -- transfer to a `q`-random set
  have hrounds := ppr_rounds (V := V) pr (fun y => θ ≤ (ballY G U Z y ℓ (W ∩ allowed U Z y)).card)
  have hq' : 1 - ∏ j, (1 - pr j) ≤ q := union_density_le hq0.le hq1 hp0.le hp1 hℓp
  have hq'0 : 0 ≤ 1 - ∏ j, (1 - pr j) := by
    have : ∏ j, (1 - pr j) ≤ 1 :=
      Finset.prod_le_one₀ (fun j _ => by linarith [hpr1 j]) (fun j _ => by linarith [hpr0 j])
    linarith
  have hmono := ppr_bern_mono (ι := V) (q := fun _ => 1 - ∏ j, (1 - pr j)) (q' := fun _ => q)
    (fun _ => hq'0) (fun _ => hq') (fun _ => hq1)
    (P := fun y => θ ≤ (ballY G U Z y ℓ (W ∩ allowed U Z y)).card)
    (fun y y' hyy' hy => le_trans hy (Nat.cast_le.2 (Finset.card_le_card
      (ballY_mono hyy' (Finset.inter_subset_inter (Finset.Subset.refl _) (allowed_mono hyy'))))))
  have : ppr (roundD pr) (fun Y => θ ≤ (ballY G U Z (unionY Y) ℓ (W ∩ allowed U Z (unionY Y))).card) =
      ppr (fun _ : V => bern (1 - ∏ j, (1 - pr j))) (fun y => θ ≤ (ballY G U Z y ℓ (W ∩ allowed U Z y)).card) :=
    hrounds.symm
  linarith

end

end Lovasz
