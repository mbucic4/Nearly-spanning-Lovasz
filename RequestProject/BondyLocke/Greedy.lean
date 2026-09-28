module
public import RequestProject.BondyLocke.Defs

/-!
# Bondy–Locke, Lemma 1 (case `k = 3`): two disjoint vines

Every chord system on `0, …, ℓ` (with `ℓ ≥ 2`) contains two disjoint vines.  The proof is the
greedy procedure of Bondy–Locke: two partial vines are extended alternately, always extending
the one that reaches less far, by a chord jumping over its current end which the other partial
vine does not use.
-/

@[expose] public section

namespace BondyLocke

namespace Vine

variable {C : Set (ℕ × ℕ)} {P : Vine}

lemma Partial.u_lt_v (hP : P.Partial C) {k : ℕ} (hk : k < P.m) : P.u k < P.v k := by
  by_cases h : k + 1 < P.m
  · have := hP.step k h; omega
  · have : k = P.m - 1 := by omega
    subst this; exact hP.lastlt

lemma Partial.v_mono (hP : P.Partial C) {k k' : ℕ} (hkk : k ≤ k') (hk' : k' < P.m) :
    P.v k ≤ P.v k' := by
  induction k' with
  | zero =>
    have : k = 0 := by omega
    subst this; exact le_rfl
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hkk with h | h
    · rw [h]
    · have h1 := ih (by omega) (by omega)
      have h2 := (hP.step n hk').2.2
      omega

lemma Partial.u_strict (hP : P.Partial C) {k k' : ℕ} (hkk : k < k') (hk' : k' < P.m) :
    P.u k < P.u k' := by
  induction k' with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hkk) with h | h
    · subst h; exact (hP.step k hk').1
    · have h1 := ih h (by omega)
      have h2 := (hP.step n hk').1
      omega

lemma Partial.v_strict (hP : P.Partial C) {k k' : ℕ} (hkk : k < k') (hk' : k' < P.m) :
    P.v k < P.v k' := by
  induction k' with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hkk) with h | h
    · subst h; exact (hP.step k hk').2.2
    · have h1 := ih h (by omega)
      have h2 := (hP.step n hk').2.2
      omega

lemma Partial.v_le_last (hP : P.Partial C) {k : ℕ} (hk : k < P.m) : P.v k ≤ P.last :=
  hP.v_mono (by omega) (by have := hP.pos; omega)

lemma Partial.last_pos (hP : P.Partial C) : 0 < P.last := by
  have := hP.lastlt; unfold last; omega

lemma Partial.last_le (hP : P.Partial C) {ℓ : ℕ} (hC : ChordSys ℓ C) : P.last ≤ ℓ :=
  hC.le _ (hP.mem _ (by have := hP.pos; omega))

/-- The vine with a single chord `(a, b)`. -/
def single (a b : ℕ) : Vine := ⟨1, fun _ => a, fun _ => b⟩

/-- Keep the chords `0, …, k0` of `P` and append the chord `(a, b)`. -/
def ext (P : Vine) (k0 a b : ℕ) : Vine :=
  ⟨k0 + 2, fun k => if k ≤ k0 then P.u k else a, fun k => if k ≤ k0 then P.v k else b⟩

lemma single_partial {b : ℕ} (hb : 0 < b) (hC : (0, b) ∈ C) : (single 0 b).Partial C where
  pos := by simp [single]
  u0 := rfl
  step := by intro k hk; simp [single] at hk
  gap := by intro k hk; simp [single] at hk
  lastlt := hb
  mem := by intro k _; exact hC

lemma ext_partial (hP : P.Partial C) {k0 a b : ℕ} (hk0 : k0 < P.m) (ha : a < P.v k0)
    (hmin : ∀ k < k0, P.v k ≤ a) (ha0 : 0 < a) (hb : P.v k0 < b) (hab : (a, b) ∈ C) :
    (P.ext k0 a b).Partial C where
  pos := by simp [ext]
  u0 := by simp [ext, hP.u0]
  step := by
    intro k hk
    simp only [ext] at hk ⊢
    by_cases h : k + 1 ≤ k0
    · rw [if_pos (by omega), if_pos h, if_pos (by omega), if_pos h]
      exact hP.step k (by omega)
    · have hk' : k = k0 := by omega
      subst hk'
      rw [if_pos le_rfl, if_neg (by omega), if_pos le_rfl, if_neg (by omega)]
      refine ⟨?_, ha, hb⟩
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · subst h0; rw [hP.u0]; exact ha0
      · have h1 := (hP.step (k - 1) (by omega)).2.1
        have h2 := hmin (k - 1) (by omega)
        rw [show k - 1 + 1 = k by omega] at h1
        omega
  gap := by
    intro k hk
    simp only [ext] at hk ⊢
    by_cases h : k + 2 ≤ k0
    · rw [if_pos (by omega), if_pos h]
      exact hP.gap k (by omega)
    · rw [if_pos (by omega), if_neg h]
      exact hmin k (by omega)
  lastlt := by
    simp only [ext, show k0 + 2 - 1 = k0 + 1 by omega, if_neg (show ¬ k0 + 1 ≤ k0 by omega)]
    omega
  mem := by
    intro k hk
    simp only [ext] at hk ⊢
    by_cases h : k ≤ k0
    · rw [if_pos h, if_pos h]; exact hP.mem k (by omega)
    · rw [if_neg h, if_neg h]; exact hab

end Vine

open Vine

lemma Disj.symm {P Q : Vine} (h : Disj P Q) : Disj Q P := by
  intro k hk k' hk' he
  exact h k' hk' k hk he.symm

/-- The invariant of the greedy procedure. -/
structure GInv (C : Set (ℕ × ℕ)) (P₁ P₂ : Vine) : Prop where
  p1 : P₁.Partial C
  p2 : P₂.Partial C
  disj : Disj P₁ P₂
  le12 : P₁.last ≤ P₂.last → ∀ k, k + 1 < P₂.m → P₂.v k ≤ P₁.last
  le21 : P₂.last ≤ P₁.last → ∀ k, k + 1 < P₁.m → P₁.v k ≤ P₂.last

lemma GInv.symm {C : Set (ℕ × ℕ)} {P₁ P₂ : Vine} (h : GInv C P₁ P₂) : GInv C P₂ P₁ :=
  ⟨h.p2, h.p1, h.disj.symm, h.le21, h.le12⟩

/-- One step of the greedy procedure: the partial vine reaching less far can be extended. -/
lemma greedy_step {ℓ : ℕ} {C : Set (ℕ × ℕ)} (hC : ChordSys ℓ C) {P₁ P₂ : Vine}
    (h : GInv C P₁ P₂) (hle : P₁.last ≤ P₂.last) (hlt : P₁.last < ℓ) :
    ∃ P₁', GInv C P₁' P₂ ∧ P₁.last < P₁'.last := by
  set j := P₁.last with hj
  have hj0 : 0 < j := h.p1.last_pos
  obtain ⟨c, hc, c', hc', hne, hc1, hc2, hc1', hc2'⟩ := hC.cover j hj0 hlt
  -- a chord of `P₂` jumping over `j` is its last chord
  have hlast : ∀ d : ℕ × ℕ, d.1 < j → j < d.2 → ∀ k < P₂.m, (P₂.u k, P₂.v k) = d →
      k = P₂.m - 1 := by
    intro d _ hd2 k hk hkd
    by_contra hne'
    have := h.le12 hle k (by omega)
    rw [← hkd] at hd2
    simp at hd2
    omega
  obtain ⟨d, hd, hd1, hd2, hdP₂⟩ : ∃ d ∈ C, d.1 < j ∧ j < d.2 ∧
      ∀ k < P₂.m, (P₂.u k, P₂.v k) ≠ d := by
    by_cases hcase : ∀ k < P₂.m, (P₂.u k, P₂.v k) ≠ c
    · exact ⟨c, hc, hc1, hc2, hcase⟩
    · push_neg at hcase
      obtain ⟨k, hk, hkc⟩ := hcase
      refine ⟨c', hc', hc1', hc2', fun k' hk' hk'c => ?_⟩
      have e1 := hlast c hc1 hc2 k hk hkc
      have e2 := hlast c' hc1' hc2' k' hk' hk'c
      apply hne
      rw [← hkc, ← hk'c, e1, e2]
  obtain ⟨a, b⟩ := d
  simp only at hd1 hd2
  have hP₁ := h.p1
  -- chords of `P₁` end at or before `j`, so they differ from `(a, b)`
  have hP₁ne : ∀ k < P₁.m, (P₁.u k, P₁.v k) ≠ (a, b) := by
    intro k hk he
    have := hP₁.v_le_last hk
    simp only [Prod.mk.injEq] at he
    omega
  have hbl : b ≤ ℓ := hC.le _ hd
  rcases Nat.eq_zero_or_pos a with ha0 | ha0
  · -- the new chord starts at `0`: restart `P₁` with this chord alone
    subst ha0
    refine ⟨single 0 b, ⟨single_partial (by omega) hd, h.p2, ?_, ?_, ?_⟩, ?_⟩
    · intro k hk k' hk' he
      simp [single] at hk; subst hk
      exact hdP₂ k' hk' (by simpa [single] using he.symm)
    · intro _ k hk
      have := h.le12 hle k hk
      simp only [last, single]; omega
    · intro _ k hk; simp [single] at hk
    · simp only [last, single]; omega
  · -- keep the chords of `P₁` up to the first one ending after `a`
    have hex : ∃ k, k < P₁.m ∧ a < P₁.v k := ⟨P₁.m - 1, by have := hP₁.pos; omega, hd1⟩
    obtain ⟨k0, hk0lt, hk0a, hk0min⟩ : ∃ k0, k0 < P₁.m ∧ a < P₁.v k0 ∧ ∀ k < k0, P₁.v k ≤ a := by
      refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, fun k hk => ?_⟩
      have := Nat.find_min hex hk
      push_neg at this
      exact this (by have := (Nat.find_spec hex).1; omega)
    have hk0spec : k0 < P₁.m ∧ a < P₁.v k0 := ⟨hk0lt, hk0a⟩
    have hvk0 : P₁.v k0 ≤ j := hP₁.v_le_last hk0spec.1
    have hext := ext_partial hP₁ hk0spec.1 hk0spec.2 hk0min ha0 (by omega) hd
    have hlastext : (P₁.ext k0 a b).last = b := by
      simp [last, ext]
    refine ⟨P₁.ext k0 a b, ⟨hext, h.p2, ?_, ?_, ?_⟩, ?_⟩
    · intro k hk k' hk' he
      simp only [ext] at hk he
      by_cases hkk : k ≤ k0
      · rw [if_pos hkk, if_pos hkk] at he
        exact h.disj k (by omega) k' hk' he
      · rw [if_neg hkk, if_neg hkk] at he
        exact hdP₂ k' hk' he.symm
    · intro _ k hk
      have := h.le12 hle k hk
      rw [hlastext]; omega
    · intro _ k hk
      simp only [ext] at hk ⊢
      rw [if_pos (by omega)]
      have := hP₁.v_le_last (k := k) (by omega)
      omega
    · rw [hlastext]; omega

/-- From a greedy invariant, two complete disjoint vines. -/
lemma greedy_main {ℓ : ℕ} {C : Set (ℕ × ℕ)} (hC : ChordSys ℓ C) :
    ∀ n, ∀ P₁ P₂ : Vine, 2 * ℓ - (P₁.last + P₂.last) = n → GInv C P₁ P₂ →
      ∃ P Q, P.IsVine ℓ C ∧ Q.IsVine ℓ C ∧ Disj P Q := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P₁ P₂ hn h
  have h1 := h.p1.last_le hC
  have h2 := h.p2.last_le hC
  by_cases hdone : P₁.last = ℓ ∧ P₂.last = ℓ
  · exact ⟨P₁, P₂, ⟨h.p1, hdone.1⟩, ⟨h.p2, hdone.2⟩, h.disj⟩
  rcases le_total P₁.last P₂.last with hle | hle
  · obtain ⟨P₁', h', hlt⟩ := greedy_step hC h hle (by omega)
    have := h'.p1.last_le hC
    exact ih _ (by omega) P₁' P₂ rfl h'
  · obtain ⟨P₂', h', hlt⟩ := greedy_step hC h.symm hle (by omega)
    have := h'.p1.last_le hC
    exact ih _ (by omega) P₁ P₂' rfl h'.symm

/-- **Bondy–Locke, Lemma 1 (`k = 3`).**  A chord system on `0, …, ℓ` with `ℓ ≥ 2` contains two
disjoint vines. -/
theorem exists_disj_vines {ℓ : ℕ} {C : Set (ℕ × ℕ)} (hC : ChordSys ℓ C) (hℓ : 2 ≤ ℓ) :
    ∃ P Q, P.IsVine ℓ C ∧ Q.IsVine ℓ C ∧ Disj P Q := by
  obtain ⟨c, hc, c', hc', hne, hc1, hc2, hc1', hc2'⟩ := hC.cover 1 one_pos (by omega)
  obtain ⟨a, b⟩ := c
  obtain ⟨a', b'⟩ := c'
  simp only at hc1 hc2 hc1' hc2'
  have ha : a = 0 := by omega
  have ha' : a' = 0 := by omega
  subst ha ha'
  have h : GInv C (single 0 b) (single 0 b') := by
    refine ⟨single_partial (by omega) hc, single_partial (by omega) hc', ?_, ?_, ?_⟩
    · intro k hk k' hk' he
      simp [single] at he
      exact hne (by rw [he])
    · intro _ k hk; simp [single] at hk
    · intro _ k hk; simp [single] at hk
  exact greedy_main hC _ _ _ rfl h

end BondyLocke
