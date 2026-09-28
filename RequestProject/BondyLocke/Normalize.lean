module
public import RequestProject.BondyLocke.Greedy

/-!
# Bondy–Locke: totally disjoint vines

Among all pairs of disjoint vines from a chord system, take one with the fewest chords and,
among those, with the largest sum of squared lengths of double zones.  Then neither
configuration (4) nor configuration (5) of Bondy–Locke occurs: operation (i) of the paper would
produce a pair with fewer chords, and operation (ii) (applied to a leftmost crossing) a pair with
the same number of chords and a larger sum of squares.
-/

@[expose] public section

namespace BondyLocke

open Vine

/-- The first `s` chords of `A` followed by the chords of `B` from index `t` on. -/
def splice (A : Vine) (s : ℕ) (B : Vine) (t : ℕ) : Vine :=
  ⟨s + (B.m - t), fun k => if k < s then A.u k else B.u (k - s + t),
    fun k => if k < s then A.v k else B.v (k - s + t)⟩

section splice
variable {A B : Vine} {s t k : ℕ}

lemma splice_m : (splice A s B t).m = s + (B.m - t) := rfl
lemma splice_u_lt (h : k < s) : (splice A s B t).u k = A.u k := by simp [splice, h]
lemma splice_v_lt (h : k < s) : (splice A s B t).v k = A.v k := by simp [splice, h]
lemma splice_u_ge (h : s ≤ k) : (splice A s B t).u k = B.u (k - s + t) := by
  simp [splice, Nat.not_lt.2 h]
lemma splice_v_ge (h : s ≤ k) : (splice A s B t).v k = B.v (k - s + t) := by
  simp [splice, Nat.not_lt.2 h]

end splice

lemma splice_isVine {ℓ : ℕ} {C : Set (ℕ × ℕ)} {A B : Vine} {s t : ℕ}
    (hA : A.Partial C) (hB : B.IsVine ℓ C) (hs1 : 1 ≤ s) (hsA : s ≤ A.m) (htB : t < B.m)
    (j1a : A.u (s - 1) < B.u t) (j1b : B.u t < A.v (s - 1)) (j1c : A.v (s - 1) < B.v t)
    (j2 : 2 ≤ s → A.v (s - 2) ≤ B.u t) (j3 : t + 1 < B.m → A.v (s - 1) ≤ B.u (t + 1)) :
    (splice A s B t).IsVine ℓ C := by
  have hBp := hB.1
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [splice_m]; omega
  · rw [splice_u_lt (by omega)]; exact hA.u0
  · intro k hk
    rw [splice_m] at hk
    by_cases h1 : k + 1 < s
    · rw [splice_u_lt (by omega), splice_u_lt h1, splice_v_lt (by omega), splice_v_lt h1]
      exact hA.step k (by omega)
    · by_cases h2 : k + 1 = s
      · rw [splice_u_lt (by omega), splice_u_ge (by omega), splice_v_lt (by omega),
          splice_v_ge (by omega), show k + 1 - s + t = t by omega, show k = s - 1 by omega]
        exact ⟨j1a, j1b, j1c⟩
      · rw [splice_u_ge (by omega), splice_u_ge (by omega), splice_v_ge (by omega),
          splice_v_ge (by omega), show k + 1 - s + t = (k - s + t) + 1 by omega]
        exact hBp.step _ (by omega)
  · intro k hk
    rw [splice_m] at hk
    by_cases h1 : k + 2 < s
    · rw [splice_v_lt (by omega), splice_u_lt h1]
      exact hA.gap k (by omega)
    · by_cases h2 : k + 2 = s
      · rw [splice_v_lt (by omega), splice_u_ge (by omega), show k + 2 - s + t = t by omega,
          show k = s - 2 by omega]
        exact j2 (by omega)
      · by_cases h3 : k + 1 = s
        · rw [splice_v_lt (by omega), splice_u_ge (by omega),
            show k + 2 - s + t = t + 1 by omega, show k = s - 1 by omega]
          exact j3 (by omega)
        · rw [splice_v_ge (by omega), splice_u_ge (by omega),
            show k + 2 - s + t = (k - s + t) + 2 by omega]
          exact hBp.gap _ (by omega)
  · rw [splice_m, splice_u_ge (by omega), splice_v_ge (by omega),
      show s + (B.m - t) - 1 - s + t = B.m - 1 by omega]
    exact hBp.lastlt
  · intro k hk
    rw [splice_m] at hk
    by_cases h1 : k < s
    · rw [splice_u_lt h1, splice_v_lt h1]; exact hA.mem k (by omega)
    · rw [splice_u_ge (by omega), splice_v_ge (by omega)]; exact hBp.mem _ (by omega)
  · unfold last
    rw [splice_m, splice_v_ge (by omega), show s + (B.m - t) - 1 - s + t = B.m - 1 by omega]
    exact hB.2

lemma Vine.Partial.chord_inj {C : Set (ℕ × ℕ)} {P : Vine} (hP : P.Partial C) {k k' : ℕ}
    (hk : k < P.m) (hk' : k' < P.m) (h : (P.u k, P.v k) = (P.u k', P.v k')) : k = k' := by
  by_contra hne
  simp only [Prod.mk.injEq] at h
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := hP.u_strict hlt hk'; omega
  · have := hP.u_strict hlt hk; omega

lemma disj_splice {C : Set (ℕ × ℕ)} {P Q : Vine} (hP : P.Partial C) (hQ : Q.Partial C)
    (hPQ : Disj P Q) {a b c d : ℕ} (had : a ≤ d) (hcb : c ≤ b) (haP : a ≤ P.m) (hcQ : c ≤ Q.m) :
    Disj (splice P a Q b) (splice Q c P d) := by
  intro k hk k' hk' he
  rw [splice_m] at hk hk'
  by_cases h1 : k < a
  · rw [splice_u_lt h1, splice_v_lt h1] at he
    by_cases h2 : k' < c
    · rw [splice_u_lt h2, splice_v_lt h2] at he
      exact hPQ k (by omega) k' (by omega) he
    · rw [splice_u_ge (by omega), splice_v_ge (by omega)] at he
      have := hP.chord_inj (by omega) (by omega) he
      omega
  · rw [splice_u_ge (by omega), splice_v_ge (by omega)] at he
    by_cases h2 : k' < c
    · rw [splice_u_lt h2, splice_v_lt h2] at he
      have := hQ.chord_inj (by omega) (by omega) he
      omega
    · rw [splice_u_ge (by omega), splice_v_ge (by omega)] at he
      exact hPQ _ (by omega) _ (by omega) he.symm

/-- The sum of the squared lengths of the double zones of a vine. -/
def sq (P : Vine) : ℕ := ∑ k ∈ Finset.range (P.m - 1), (P.v k - P.u (k + 1)) ^ 2

lemma sum_range_split (f : ℕ → ℕ) {a n : ℕ} (h : a < n) :
    ∑ k ∈ Finset.range n, f k =
      ∑ k ∈ Finset.range a, f k + f a + ∑ k ∈ Finset.range (n - 1 - a), f (a + 1 + k) := by
  conv_lhs => rw [show n = (a + 1) + (n - 1 - a) by omega]
  rw [Finset.sum_range_add, Finset.sum_range_succ]

lemma sq_split {P : Vine} {i : ℕ} (hi : i + 1 < P.m) :
    sq P = ∑ k ∈ Finset.range i, (P.v k - P.u (k + 1)) ^ 2 + (P.v i - P.u (i + 1)) ^ 2 +
      ∑ k ∈ Finset.range (P.m - 2 - i), (P.v (i + 1 + k) - P.u (i + 1 + k + 1)) ^ 2 := by
  unfold sq
  rw [sum_range_split _ (show i < P.m - 1 by omega), show P.m - 1 - 1 - i = P.m - 2 - i by omega]

lemma sq_splice {A B : Vine} {s t : ℕ} (hs : 1 ≤ s) (ht : t < B.m) :
    sq (splice A s B t) = ∑ k ∈ Finset.range (s - 1), (A.v k - A.u (k + 1)) ^ 2 +
      (A.v (s - 1) - B.u t) ^ 2 +
      ∑ k ∈ Finset.range (B.m - 1 - t), (B.v (t + k) - B.u (t + k + 1)) ^ 2 := by
  unfold sq
  rw [splice_m, sum_range_split _ (show s - 1 < s + (B.m - t) - 1 by omega)]
  congr 1
  · congr 1
    · apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      rw [splice_v_lt (by omega), splice_u_lt (by omega)]
    · rw [splice_v_lt (by omega), splice_u_ge (by omega), show s - 1 + 1 - s + t = t by omega]
  · rw [show s + (B.m - t) - 1 - 1 - (s - 1) = B.m - 1 - t by omega]
    apply Finset.sum_congr rfl
    intro k _
    rw [splice_v_ge (by omega), splice_u_ge (by omega),
      show s - 1 + 1 + k - s + t = t + k by omega, show s - 1 + 1 + k + 1 - s + t = t + k + 1 by omega]

section good
variable {ℓ : ℕ} {C : Set (ℕ × ℕ)}

/-- A pair of disjoint vines. -/
def Good (ℓ : ℕ) (C : Set (ℕ × ℕ)) (P Q : Vine) : Prop :=
  P.IsVine ℓ C ∧ Q.IsVine ℓ C ∧ Disj P Q

lemma Good.symm {P Q : Vine} (h : Good ℓ C P Q) : Good ℓ C Q P := ⟨h.2.1, h.1, h.2.2.symm⟩

lemma Good.u_ne {P Q : Vine} (hC : ChordSys ℓ C) (h : Good ℓ C P Q) {k k' : ℕ} (hk : k < P.m)
    (hk' : k' < Q.m) (he : P.u k = Q.u k') : P.u k = 0 :=
  hC.origin _ (h.1.1.mem k hk) _ (h.2.1.1.mem k' hk') he (h.2.2 k hk k' hk')

lemma Good.v_ne {P Q : Vine} (hC : ChordSys ℓ C) (h : Good ℓ C P Q) {k k' : ℕ} (hk : k < P.m)
    (hk' : k' < Q.m) (he : P.v k = Q.v k') : P.v k = ℓ :=
  hC.term _ (h.1.1.mem k hk) _ (h.2.1.1.mem k' hk') he (h.2.2 k hk k' hk')

lemma Vine.IsVine.v_lt_ell {P : Vine} (hP : P.IsVine ℓ C) {k : ℕ} (hk : k + 1 < P.m) : P.v k < ℓ := by
  have := hP.1.v_strict (show k < P.m - 1 by omega) (by omega)
  have h2 := hP.2
  unfold last at h2
  omega

lemma Vine.IsVine.u_pos {P : Vine} (hP : P.IsVine ℓ C) {k : ℕ} (hk : 0 < k) (hk' : k < P.m) :
    0 < P.u k := by
  have := hP.1.u_strict hk hk'
  rw [hP.1.u0] at this; exact this

/-- Operation (i) of Bondy–Locke: configuration (4) allows fewer chords. -/
lemma op_i {P Q : Vine} (h : Good ℓ C P Q) {i j : ℕ} (hi : i + 1 < P.m)
    (hj : j + 2 < Q.m) (h1 : P.u (i + 1) < Q.v j) (h2 : Q.u (j + 2) < P.v i) :
    ∃ P' Q', Good ℓ C P' Q' ∧ P'.m + Q'.m < P.m + Q.m := by
  obtain ⟨hP, hQ, hPQ⟩ := h
  have hPp := hP.1
  have hQp := hQ.1
  -- `r`: the first chord of `Q` ending after `P.u (i+1)`
  have hexr : ∃ r, r < Q.m ∧ P.u (i + 1) < Q.v r := ⟨j, by omega, h1⟩
  obtain ⟨r, hrQ, hr1, hrmin⟩ : ∃ r, r < Q.m ∧ P.u (i + 1) < Q.v r ∧
      ∀ r' < r, Q.v r' ≤ P.u (i + 1) := by
    refine ⟨Nat.find hexr, (Nat.find_spec hexr).1, (Nat.find_spec hexr).2, fun r' hr' => ?_⟩
    have := Nat.find_min hexr hr'
    push_neg at this
    exact this (by have := (Nat.find_spec hexr).1; omega)
  have hrj : r ≤ j := by
    by_contra hc
    have := hrmin j (by omega); omega
  -- `s`: the last chord of `Q` starting before `P.v i`
  set s := Nat.findGreatest (fun s => Q.u s < P.v i) (Q.m - 1) with hs
  have hjs : j + 2 ≤ s := Nat.le_findGreatest (by omega) h2
  have hsQ : s ≤ Q.m - 1 := Nat.findGreatest_le _
  have hs1 : Q.u s < P.v i := Nat.findGreatest_spec (P := fun s => Q.u s < P.v i) (show j + 2 ≤ Q.m - 1 by omega) h2
  have hs2 : s + 1 < Q.m → P.v i ≤ Q.u (s + 1) := by
    intro hlt
    have := Nat.findGreatest_is_greatest (P := fun s => Q.u s < P.v i) (n := Q.m - 1)
      (k := s + 1) (by omega) (by omega)
    simpa using this
  -- basic inequalities
  have hvj : Q.v j ≤ Q.u (j + 2) := hQp.gap j hj
  have hvrj : Q.v r ≤ Q.v j := hQp.v_mono hrj (by omega)
  have husj : Q.u (j + 2) ≤ Q.u s := by
    rcases Nat.eq_or_lt_of_le hjs with he | he
    · rw [he]
    · exact (hQp.u_strict he (by omega)).le
  have hPi := hPp.step i hi
  have hPvi1 : P.v (i + 1) ≤ ℓ := by
    have := hPp.v_le_last hi; rw [hP.2] at this; exact this
  refine ⟨splice P (i + 1) Q s, splice Q (r + 1) P (i + 1), ⟨?_, ?_, ?_⟩, ?_⟩
  · apply splice_isVine hPp hQ (by omega) (by omega) (by omega)
    · simp only [Nat.add_sub_cancel]; omega
    · simp only [Nat.add_sub_cancel]; exact hs1
    · simp only [Nat.add_sub_cancel]
      by_cases hsl : s + 1 < Q.m
      · have := hs2 hsl
        have := (hQp.step s hsl).2.1
        omega
      · have : s = Q.m - 1 := by omega
        have hl := hQ.2
        unfold last at hl
        rw [this, hl]; omega
    · intro hi2
      have := hPp.gap (i - 1) (by omega)
      rw [show i + 1 - 2 = i - 1 by omega]
      rw [show i - 1 + 2 = i + 1 by omega] at this
      omega
    · intro hs'
      simp only [Nat.add_sub_cancel]; exact hs2 hs'
  · apply splice_isVine hQp hP (by omega) (by omega) hi
    · simp only [Nat.add_sub_cancel]
      rcases Nat.eq_zero_or_pos r with hr0 | hr0
      · rw [hr0, hQp.u0]; exact Vine.IsVine.u_pos hP (by omega) hi
      · have := (hQp.step (r - 1) (by omega)).2.1
        have := hrmin (r - 1) (by omega)
        rw [show r - 1 + 1 = r by omega] at *
        omega
    · simp only [Nat.add_sub_cancel]; exact hr1
    · simp only [Nat.add_sub_cancel]; omega
    · intro hr2
      rw [show r + 1 - 2 = r - 1 by omega]
      exact hrmin _ (by omega)
    · intro hi2
      simp only [Nat.add_sub_cancel]
      have := hPp.gap i (by omega)
      rw [show i + 1 + 1 = i + 2 from rfl]
      omega
  · exact disj_splice hPp hQp hPQ le_rfl (by omega) (by omega) (by omega)
  · rw [splice_m, splice_m]; omega

/-- Operation (ii) of Bondy–Locke applied to a leftmost crossing: the same number of chords
and a larger sum of squares. -/
lemma op_ii (hC : ChordSys ℓ C) {P Q : Vine} (h : Good ℓ C P Q) (hnc1 : NoContain P Q)
    (hnc2 : NoContain Q P) {i j : ℕ} (hi : i + 1 < P.m) (hj : j + 1 < Q.m)
    (h1 : Q.u (j + 1) < P.u (i + 1)) (h2 : P.u (i + 1) < Q.v j) (h3 : Q.v j < P.v i)
    (hmin : ∀ i', i' + 1 < P.m → i' < i →
      ¬ (P.u (i' + 1) < Q.u (j + 1) ∧ Q.u (j + 1) < P.v i' ∧ P.v i' < Q.v j)) :
    ∃ P' Q', Good ℓ C P' Q' ∧ P'.m + Q'.m = P.m + Q.m ∧ sq P + sq Q < sq P' + sq Q' := by
  have hg := h
  obtain ⟨hP, hQ, hPQ⟩ := h
  have hPp := hP.1
  have hQp := hQ.1
  have hPi := hPp.step i hi
  have hQj := hQp.step j hj
  have hQu : 0 < Q.u (j + 1) := Vine.IsVine.u_pos hQ (by omega) hj
  -- `P.u i < Q.u (j+1)`
  have hA : P.u i < Q.u (j + 1) := by
    rcases Nat.lt_trichotomy (P.u i) (Q.u (j + 1)) with hlt | heq | hgt
    · exact hlt
    · have := hg.u_ne hC (by omega) hj heq; omega
    · exfalso
      rcases Nat.eq_zero_or_pos i with hi0 | hi0
      · subst hi0; rw [hPp.u0] at hgt; omega
      · have hs := hPp.step (i - 1) (by omega)
        have hg2 := hPp.gap (i - 1) (by omega)
        rw [show i - 1 + 1 = i by omega] at hs
        rw [show i - 1 + 2 = i + 1 by omega] at hg2
        exact hnc2 j (i - 1) hj (by omega) ⟨by omega, by rw [show i - 1 + 2 = i + 1 by omega]; omega⟩
  -- `P.v i < Q.v (j+1)` and `P.v i ≤ Q.u (j+2)`
  have hB : j + 2 < Q.m → P.v i ≤ Q.u (j + 2) := by
    intro hj2
    by_contra hc
    exact hnc1 i j hi hj2 ⟨h2, by omega⟩
  have hC' : P.v i < Q.v (j + 1) := by
    by_cases hj2 : j + 2 < Q.m
    · have := hB hj2
      have := (hQp.step (j + 1) hj2).2.1
      rw [show j + 1 + 1 = j + 2 from rfl] at this
      omega
    · have hl := hQ.2
      unfold last at hl
      rw [show j + 1 = Q.m - 1 by omega, hl]
      exact Vine.IsVine.v_lt_ell hP hi
  have hD : 1 ≤ i → P.v (i - 1) ≤ Q.u (j + 1) := by
    intro hi1
    by_contra hc
    have hg2 := hPp.gap (i - 1) (by omega)
    rw [show i - 1 + 2 = i + 1 by omega] at hg2
    exact hmin (i - 1) (by omega) (by omega)
      ⟨by rw [show i - 1 + 1 = i by omega]; exact hA, by omega, by omega⟩
  refine ⟨splice P (i + 1) Q (j + 1), splice Q (j + 1) P (i + 1), ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · apply splice_isVine hPp hQ (by omega) (by omega) hj
    · simp only [Nat.add_sub_cancel]; exact hA
    · simp only [Nat.add_sub_cancel]; omega
    · simp only [Nat.add_sub_cancel]; exact hC'
    · intro hi2; rw [show i + 1 - 2 = i - 1 by omega]; exact hD (by omega)
    · intro hj2; simp only [Nat.add_sub_cancel]; exact hB hj2
  · apply splice_isVine hQp hP (by omega) (by omega) hi
    · simp only [Nat.add_sub_cancel]; omega
    · simp only [Nat.add_sub_cancel]; exact h2
    · simp only [Nat.add_sub_cancel]; omega
    · intro hj2
      rw [show j + 1 - 2 = j - 1 by omega]
      have := hQp.gap (j - 1) (by omega)
      rw [show j - 1 + 2 = j + 1 by omega] at this
      omega
    · intro hi2
      simp only [Nat.add_sub_cancel]
      have := hPp.gap i (by omega)
      rw [show i + 1 + 1 = i + 2 from rfl]
      omega
  · exact disj_splice hPp hQp hPQ le_rfl le_rfl (by omega) (by omega)
  · rw [splice_m, splice_m]; omega
  · rw [sq_splice (by omega) hj, sq_splice (by omega) hi, sq_split hi, sq_split hj]
    simp only [Nat.add_sub_cancel]
    rw [show Q.m - 1 - (j + 1) = Q.m - 2 - j by omega, show P.m - 1 - (i + 1) = P.m - 2 - i by omega]
    have e1 : ∀ k, j + 1 + k + 1 = j + 1 + k + 1 := fun _ => rfl
    have key : (P.v i - P.u (i + 1)) ^ 2 + (Q.v j - Q.u (j + 1)) ^ 2 <
        (P.v i - Q.u (j + 1)) ^ 2 + (Q.v j - P.u (i + 1)) ^ 2 := by
      zify [h1.le, h2.le, h3.le, (h1.trans h2).le, (h2.trans h3).le, (h1.trans (h2.trans h3)).le]
      have a1 : (0 : ℤ) < (P.v i : ℤ) - Q.v j := by omega
      have a2 : (0 : ℤ) < (P.u (i + 1) : ℤ) - Q.u (j + 1) := by omega
      nlinarith [mul_pos a1 a2]
    omega

/-- Among pairs of disjoint vines, a pair with the fewest chords and then the largest sum of
squares of double zones is totally disjoint. -/
theorem exists_td_vines (hC : ChordSys ℓ C) (hℓ : 2 ≤ ℓ) :
    ∃ P Q, Good ℓ C P Q ∧ TD P Q := by
  classical
  have hex : ∃ N, ∃ P Q, Good ℓ C P Q ∧ P.m + Q.m = N := by
    obtain ⟨P, Q, h⟩ := exists_disj_vines hC hℓ
    exact ⟨_, P, Q, h, rfl⟩
  set N := Nat.find hex with hN
  have hNmin : ∀ P Q, Good ℓ C P Q → N ≤ P.m + Q.m := fun P Q h =>
    Nat.find_min' hex ⟨P, Q, h, rfl⟩
  -- bound on the sum of squares
  have hbound : ∀ P : Vine, P.IsVine ℓ C → sq P ≤ P.m * ℓ ^ 2 := by
    intro P hP
    unfold sq
    calc ∑ k ∈ Finset.range (P.m - 1), (P.v k - P.u (k + 1)) ^ 2
        ≤ ∑ _k ∈ Finset.range (P.m - 1), ℓ ^ 2 := by
          apply Finset.sum_le_sum
          intro k hk
          rw [Finset.mem_range] at hk
          have := hP.1.v_le_last (k := k) (by omega)
          rw [hP.2] at this
          exact Nat.pow_le_pow_left (by omega) 2
      _ ≤ P.m * ℓ ^ 2 := by simp; exact Nat.mul_le_mul_right _ (by omega)
  have hb2 : ∀ P Q, Good ℓ C P Q → sq P + sq Q ≤ (P.m + Q.m) * ℓ ^ 2 := by
    intro P Q h
    have := hbound P h.1; have := hbound Q h.2.1
    rw [add_mul]; omega
  have hex2 : ∃ D, ∃ P Q, Good ℓ C P Q ∧ P.m + Q.m = N ∧ N * ℓ ^ 2 - (sq P + sq Q) = D := by
    obtain ⟨P, Q, h, hm⟩ := Nat.find_spec hex
    exact ⟨_, P, Q, h, hm, rfl⟩
  obtain ⟨P, Q, hPQ, hm, hD⟩ := Nat.find_spec hex2
  have hDmin : ∀ P' Q', Good ℓ C P' Q' → P'.m + Q'.m = N →
      N * ℓ ^ 2 - (sq P + sq Q) ≤ N * ℓ ^ 2 - (sq P' + sq Q') := by
    intro P' Q' h' hm'
    rw [hD]
    exact Nat.find_min' hex2 ⟨P', Q', h', hm', rfl⟩
  have hsqP : sq P + sq Q ≤ N * ℓ ^ 2 := by
    have := hbound P hPQ.1; have := hbound Q hPQ.2.1
    rw [← hm, add_mul]; omega
  -- no configuration (4)
  have hnc1 : NoContain P Q := by
    intro i j hi hj ⟨h1, h2⟩
    obtain ⟨P', Q', h', hlt⟩ := op_i hPQ hi hj h1 h2
    have := hNmin P' Q' h'; omega
  have hnc2 : NoContain Q P := by
    intro i j hi hj ⟨h1, h2⟩
    obtain ⟨P', Q', h', hlt⟩ := op_i hPQ.symm hi hj h1 h2
    have := hNmin Q' P' h'.symm; omega
  -- no configuration (5): take a crossing with smallest index sum
  have hcross : ∀ n, ∀ i j, i + j = n → ¬ ((i + 1 < P.m ∧ j + 1 < Q.m ∧
      Q.u (j + 1) < P.u (i + 1) ∧ P.u (i + 1) < Q.v j ∧ Q.v j < P.v i) ∨
      (i + 1 < P.m ∧ j + 1 < Q.m ∧
      P.u (i + 1) < Q.u (j + 1) ∧ Q.u (j + 1) < P.v i ∧ P.v i < Q.v j)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro i j hij hc
    rcases hc with ⟨hi, hj, h1, h2, h3⟩ | ⟨hi, hj, h1, h2, h3⟩
    · obtain ⟨P', Q', h', hm', hsq⟩ := op_ii hC hPQ hnc1 hnc2 hi hj h1 h2 h3
        (fun i' hi' hlt hc => ih (i' + j) (by omega) i' j rfl (Or.inr ⟨hi', hj, hc⟩))
      have := hDmin P' Q' h' (by omega)
      have hb := hb2 P' Q' h'
      rw [show P'.m + Q'.m = N by omega] at hb
      omega
    · obtain ⟨Q', P', h', hm', hsq⟩ := op_ii hC hPQ.symm hnc2 hnc1 hj hi h1 h2 h3
        (fun j' hj' hlt hc => ih (i + j') (by omega) i j' rfl (Or.inl ⟨hi, hj', hc⟩))
      have := hDmin P' Q' h'.symm (by omega)
      have hb := hb2 P' Q' h'.symm
      rw [show P'.m + Q'.m = N by omega] at hb
      omega
  refine ⟨P, Q, hPQ, ?_, ?_, hnc1, hnc2⟩
  · intro i j hi hj hc
    exact hcross _ i j rfl (Or.inl ⟨hi, hj, hc⟩)
  · intro j i hj hi hc
    exact hcross _ i j rfl (Or.inr ⟨hi, hj, hc⟩)

end good

end BondyLocke
