module
public import RequestProject.BondyLocke.Routing
public import RequestProject.BondyLocke.Lift

/-!
# Bondy–Locke: from three internally disjoint paths to a long cycle

Let `L = w₀ ⋯ w_ℓ` be a path of a graph `G` (`ℓ ≥ 2`), and let `Q 0, Q 1, Q 2` be three
`w₀ – w_ℓ` paths of `G` which are pairwise internally disjoint.  Every stretch of a `Q q` between
two consecutive visits to `L` (in `Q q`-order) going from `w_a` to `w_b` with `a < b` is a
*chord* `(a, b)`.  These chords form a chord system on `0, …, ℓ` (unless some `Q q` meets `L`
only in its ends), and the edges of the skeleton are realised by internally disjoint paths of
`G`.  Combining the routing theorem with the lifting lemma gives a cycle of `G` with at least
`(2ℓ + 8) / 7` edges (`cycle_of_three_paths`).
-/

@[expose] public section

namespace BondyLocke

open Classical

variable {V : Type*}

/-- Three `w₀ – w_ℓ` paths, pairwise internally disjoint, next to a path `L = w₀ ⋯ w_ℓ` with
`ℓ ≥ 2`. -/
structure ThreePaths (G : SimpleGraph V) (L : List V) (Q : Fin 3 → List V) : Prop where
  pathL : IsPathN G L
  len : 3 ≤ L.length
  path : ∀ q, IsPathN G (Q q)
  head : ∀ q, (Q q).head? = L.head?
  last : ∀ q, (Q q).getLast? = L.getLast?
  disj : ∀ q q', q ≠ q' → ∀ z ∈ Q q, z ∈ Q q' → z ∈ L.head? ∨ z ∈ L.getLast?

/-- `w = (q, i, j)` witnesses the chord `(a, b)`: positions `i < j` of `Q q` carry `w_a` and
`w_b`, and `Q q` avoids `L` strictly between them. -/
def Wit (L : List V) (Q : Fin 3 → List V) (a b : ℕ) (w : Fin 3 × ℕ × ℕ) : Prop :=
  b < L.length ∧ a < b ∧ w.2.1 < w.2.2 ∧ w.2.2 < (Q w.1).length ∧ (Q w.1)[w.2.1]? = L[a]? ∧
    (Q w.1)[w.2.2]? = L[b]? ∧ ∀ k x, w.2.1 < k → k < w.2.2 → (Q w.1)[k]? = some x → x ∉ L

/-- The chords of the three paths. -/
def chordSet (L : List V) (Q : Fin 3 → List V) : Set (ℕ × ℕ) := {c | ∃ w, Wit L Q c.1 c.2 w}

/-- The interior of the stretch of `Q w.1` between positions `w.2.1` and `w.2.2`. -/
def seg (Q : Fin 3 → List V) (w : Fin 3 × ℕ × ℕ) : List V :=
  ((Q w.1).drop (w.2.1 + 1)).take (w.2.2 - w.2.1 - 1)

/-- The interior path realising the skeleton edge `{s, t}`. -/
noncomputable def realise (L : List V) (Q : Fin 3 → List V) (s t : ℕ) : List V :=
  if h : ∃ w, Wit L Q s t w then seg Q h.choose
  else if h' : ∃ w, Wit L Q t s w then (seg Q h'.choose).reverse else []

section

variable {G : SimpleGraph V} {L : List V} {Q : Fin 3 → List V}

lemma mem_seg {w : Fin 3 × ℕ × ℕ} {z : V} :
    z ∈ seg Q w ↔ ∃ k, w.2.1 < k ∧ k < w.2.2 ∧ (Q w.1)[k]? = some z := by
  unfold seg
  rw [List.mem_iff_getElem?]
  constructor
  · rintro ⟨n, hn⟩
    rw [List.getElem?_take, List.getElem?_drop] at hn
    by_cases h : n < w.2.2 - w.2.1 - 1
    · rw [if_pos h] at hn
      exact ⟨w.2.1 + 1 + n, by omega, by omega, hn⟩
    · rw [if_neg h] at hn; simp at hn
  · rintro ⟨k, h1, h2, h3⟩
    refine ⟨k - w.2.1 - 1, ?_⟩
    rw [List.getElem?_take, List.getElem?_drop, if_pos (by omega),
      show w.2.1 + 1 + (k - w.2.1 - 1) = k by omega]
    exact h3

lemma Wit.not_mem_L {a b : ℕ} {w : Fin 3 × ℕ × ℕ} (hw : Wit L Q a b w) {z : V}
    (hz : z ∈ seg Q w) : z ∉ L := by
  obtain ⟨k, h1, h2, h3⟩ := mem_seg.1 hz
  exact hw.2.2.2.2.2.2 k z h1 h2 h3

lemma seg_nodup (hT : ThreePaths G L Q) (w : Fin 3 × ℕ × ℕ) : (seg Q w).Nodup :=
  (hT.path w.1).2.sublist ((List.take_sublist _ _).trans (List.drop_sublist _ _))

/-- The end vertices of a chord stretch. -/
lemma Wit.ends {a b : ℕ} {w : Fin 3 × ℕ × ℕ} (hw : Wit L Q a b w) :
    ∃ x y, L[a]? = some x ∧ L[b]? = some y ∧ (Q w.1)[w.2.1]? = some x ∧
      (Q w.1)[w.2.2]? = some y ∧ x ∈ L ∧ y ∈ L := by
  obtain ⟨hbL, hab, -, -, hi, hj, -⟩ := hw
  refine ⟨L[a]'(by omega), L[b], List.getElem?_eq_getElem _, List.getElem?_eq_getElem _,
    hi.trans (List.getElem?_eq_getElem _), hj.trans (List.getElem?_eq_getElem _),
    List.getElem_mem _, List.getElem_mem _⟩

lemma Wit.chain (hT : ThreePaths G L Q) {a b : ℕ} {w : Fin 3 × ℕ × ℕ} (hw : Wit L Q a b w)
    {x y : V} (hx : L[a]? = some x) (hy : L[b]? = some y) :
    (x :: (seg Q w ++ [y])).IsChain G.Adj := by
  obtain ⟨hbL, hab, hij, hjl, hi, hj, -⟩ := hw
  have hQi : (Q w.1)[w.2.1]? = some x := hi.trans hx
  have hQj : (Q w.1)[w.2.2]? = some y := hj.trans hy
  have hlt : w.2.1 < (Q w.1).length := by omega
  have heq : x :: (seg Q w ++ [y]) = ((Q w.1).drop w.2.1).take (w.2.2 - w.2.1 + 1) := by
    rw [List.drop_eq_getElem_cons hlt, List.take_succ_cons]
    have : (Q w.1)[w.2.1] = x := by
      rw [List.getElem?_eq_getElem hlt] at hQi; exact Option.some.inj hQi
    rw [this, show w.2.2 - w.2.1 = (w.2.2 - w.2.1 - 1) + 1 by omega, List.take_add_one,
      List.getElem?_drop, show w.2.1 + 1 + (w.2.2 - w.2.1 - 1) = w.2.2 by omega, hQj]
    rfl
  rw [heq]
  exact ((hT.path w.1).1.drop _).take _

/-- An index of `L` carrying an end vertex of `L` is `0` or `ℓ`. -/
lemma idx_of_ends (hT : ThreePaths G L Q) {a : ℕ} {x : V} (hx : L[a]? = some x)
    (he : x ∈ L.head? ∨ x ∈ L.getLast?) : a = 0 ∨ a = L.length - 1 := by
  have ha : a < L.length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hx; simp at hx
  rcases he with he | he
  · rw [List.head?_eq_getElem?] at he
    exact Or.inl ((List.Nodup.getElem?_inj ha hT.pathL.2).mp (hx.trans he.symm))
  · rw [List.getLast?_eq_getElem?] at he
    exact Or.inr ((List.Nodup.getElem?_inj ha hT.pathL.2).mp (hx.trans he.symm))

/-- Two chord stretches in the same path sharing one end position coincide. -/
lemma Wit.eq_of_same (hT : ThreePaths G L Q) {a b a' b' : ℕ} {w w' : Fin 3 × ℕ × ℕ}
    (hw : Wit L Q a b w) (hw' : Wit L Q a' b' w') (hq : w.1 = w'.1)
    (hij : w.2.1 = w'.2.1 ∨ w.2.2 = w'.2.2) : a = a' ∧ b = b' := by
  obtain ⟨x, y, hx, hy, hQx, hQy, hxL, hyL⟩ := hw.ends
  obtain ⟨x', y', hx', hy', hQx', hQy', hxL', hyL'⟩ := hw'.ends
  obtain ⟨hbL, hab, hij1, hjl, -, -, hno⟩ := hw
  obtain ⟨hbL', hab', hij1', hjl', -, -, hno'⟩ := hw'
  obtain ⟨q, i, j⟩ := w
  obtain ⟨q', i', j'⟩ := w'
  simp only at *
  subst hq
  have hij' : i = i' ∧ j = j' := by
    rcases hij with rfl | rfl
    · refine ⟨rfl, ?_⟩
      rcases lt_trichotomy j j' with h | h | h
      · exact absurd hyL (hno' j y (by omega) h hQy)
      · exact h
      · exact absurd hyL' (hno j' y' (by omega) h hQy')
    · refine ⟨?_, rfl⟩
      rcases lt_trichotomy i i' with h | h | h
      · exact absurd hxL' (hno i' x' h (by omega) hQx')
      · exact h
      · exact absurd hxL (hno' i x h (by omega) hQx)
  obtain ⟨rfl, rfl⟩ := hij'
  rw [hQx] at hQx'; rw [hQy] at hQy'
  cases hQx'; cases hQy'
  exact ⟨(List.Nodup.getElem?_inj (by omega) hT.pathL.2).mp (hx.trans hx'.symm),
    (List.Nodup.getElem?_inj hbL hT.pathL.2).mp (hy.trans hy'.symm)⟩

/-- Chord stretches in different paths share ends only at `0` or `ℓ`. -/
lemma Wit.ends_of_ne (hT : ThreePaths G L Q) {a b a' b' : ℕ} {w w' : Fin 3 × ℕ × ℕ}
    (hw : Wit L Q a b w) (hw' : Wit L Q a' b' w') (hq : w.1 ≠ w'.1) :
    (a = a' → a = 0 ∨ a = L.length - 1) ∧ (b = b' → b = 0 ∨ b = L.length - 1) := by
  obtain ⟨x, y, hx, hy, hQx, hQy, hxL, hyL⟩ := hw.ends
  obtain ⟨x', y', hx', hy', hQx', hQy', hxL', hyL'⟩ := hw'.ends
  constructor
  · rintro rfl
    rw [hx] at hx'; cases hx'
    exact idx_of_ends hT hx (hT.disj _ _ hq x (List.mem_of_getElem? hQx)
      (List.mem_of_getElem? hQx'))
  · rintro rfl
    rw [hy] at hy'; cases hy'
    exact idx_of_ends hT hy (hT.disj _ _ hq y (List.mem_of_getElem? hQy)
      (List.mem_of_getElem? hQy'))

lemma Wit.disj (hT : ThreePaths G L Q) {a b a' b' : ℕ} {w w' : Fin 3 × ℕ × ℕ}
    (hw : Wit L Q a b w) (hw' : Wit L Q a' b' w') {z : V} (hz : z ∈ seg Q w)
    (hz' : z ∈ seg Q w') : a = a' ∧ b = b' := by
  have hzL := hw.not_mem_L hz
  obtain ⟨k, hk1, hk2, hk⟩ := mem_seg.1 hz
  obtain ⟨k', hk1', hk2', hk'⟩ := mem_seg.1 hz'
  by_cases hq : w.1 = w'.1
  · obtain ⟨x, y, hx, hy, hQx, hQy, hxL, hyL⟩ := hw.ends
    obtain ⟨x', y', hx', hy', hQx', hQy', hxL', hyL'⟩ := hw'.ends
    have hno := hw.2.2.2.2.2.2
    have hno' := hw'.2.2.2.2.2.2
    have hjl := hw.2.2.2.1
    obtain ⟨q, i, j⟩ := w
    obtain ⟨q', i', j'⟩ := w'
    simp only at *
    subst hq
    have hkk : k = k' :=
      (List.Nodup.getElem?_inj (by omega) (hT.path q).2).mp (hk.trans hk'.symm)
    subst hkk
    refine hw.eq_of_same hT hw' rfl (Or.inl ?_)
    rcases lt_trichotomy i i' with h | h | h
    · exact absurd hxL' (hno i' x' h (by omega) hQx')
    · exact h
    · exact absurd hxL (hno' i x h (by omega) hQx)
  · exfalso
    rcases hT.disj _ _ hq z (List.mem_of_getElem? hk) (List.mem_of_getElem? hk') with h | h
    · exact hzL (List.mem_of_mem_head? h)
    · exact hzL (List.mem_of_mem_getLast? h)

lemma Wit.origin (hT : ThreePaths G L Q) {a b a' b' : ℕ} {w w' : Fin 3 × ℕ × ℕ}
    (hw : Wit L Q a b w) (hw' : Wit L Q a' b' w') (ha : a = a') (hne : (a, b) ≠ (a', b')) :
    a = 0 := by
  by_cases hq : w.1 = w'.1
  · exfalso
    obtain ⟨x, y, hx, hy, hQx, hQy, hxL, hyL⟩ := hw.ends
    obtain ⟨x', y', hx', hy', hQx', hQy', hxL', hyL'⟩ := hw'.ends
    subst ha
    rw [hx] at hx'; cases hx'
    have hi : w.2.1 = w'.2.1 :=
      (List.Nodup.getElem?_inj (by have := hw.2.2.2.1; have := hw.2.2.1; omega)
        (hT.path w.1).2).mp (hQx.trans (hq ▸ hQx').symm)
    exact hne (by rw [(hw.eq_of_same hT hw' hq (Or.inl hi)).2])
  · have hbL := hw.1; have hab := hw.2.1
    rcases (hw.ends_of_ne hT hw' hq).1 ha with h | h
    · exact h
    · omega

lemma Wit.term (hT : ThreePaths G L Q) {a b a' b' : ℕ} {w w' : Fin 3 × ℕ × ℕ}
    (hw : Wit L Q a b w) (hw' : Wit L Q a' b' w') (hb : b = b') (hne : (a, b) ≠ (a', b')) :
    b = L.length - 1 := by
  by_cases hq : w.1 = w'.1
  · exfalso
    obtain ⟨x, y, hx, hy, hQx, hQy, hxL, hyL⟩ := hw.ends
    obtain ⟨x', y', hx', hy', hQx', hQy', hxL', hyL'⟩ := hw'.ends
    subst hb
    rw [hy] at hy'; cases hy'
    have hj : w.2.2 = w'.2.2 :=
      (List.Nodup.getElem?_inj hw.2.2.2.1 (hT.path w.1).2).mp
        (hQy.trans (hq ▸ hQy').symm)
    exact hne (by rw [(hw.eq_of_same hT hw' hq (Or.inr hj)).1])
  · have hbL := hw.1; have hab := hw.2.1
    rcases (hw.ends_of_ne hT hw' hq).2 hb with h | h
    · omega
    · exact h

/-- A path `Q q` avoiding `w_j` jumps over `j`. -/
lemma exists_wit_jump (hT : ThreePaths G L Q) (q : Fin 3) {j : ℕ} (hj0 : 0 < j)
    (hjl : j < L.length - 1) (hjq : ∀ x, L[j]? = some x → x ∉ Q q) :
    ∃ a b w, w.1 = q ∧ Wit L Q a b w ∧ a < j ∧ j < b := by
  have h3 := hT.len
  have hLnd := hT.pathL.2
  obtain ⟨w₀, hw₀⟩ : ∃ w₀, L[0]? = some w₀ := ⟨L[0], List.getElem?_eq_getElem _⟩
  obtain ⟨wₗ, hwₗ⟩ : ∃ wₗ, L[L.length - 1]? = some wₗ :=
    ⟨L[L.length - 1], List.getElem?_eq_getElem _⟩
  have hQ0 : (Q q)[0]? = some w₀ := by
    rw [← List.head?_eq_getElem?, hT.head, List.head?_eq_getElem?, hw₀]
  have hQl : (Q q)[(Q q).length - 1]? = some wₗ := by
    rw [← List.getLast?_eq_getElem?, hT.last, List.getLast?_eq_getElem?, hwₗ]
  have hQlen : 0 < (Q q).length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hQ0; simp at hQ0
  have hi0 : L.idxOf w₀ = 0 := by
    have := List.getElem?_idxOf (List.mem_of_getElem? hw₀)
    exact (List.Nodup.getElem?_inj (List.idxOf_lt_length_of_mem (List.mem_of_getElem? hw₀))
      hLnd).mp (this.trans hw₀.symm)
  have hil : L.idxOf wₗ = L.length - 1 := by
    have := List.getElem?_idxOf (List.mem_of_getElem? hwₗ)
    exact (List.Nodup.getElem?_inj (List.idxOf_lt_length_of_mem (List.mem_of_getElem? hwₗ))
      hLnd).mp (this.trans hwₗ.symm)
  have hex : ∃ k, ∃ x, (Q q)[k]? = some x ∧ x ∈ L ∧ j < L.idxOf x :=
    ⟨_, wₗ, hQl, List.mem_of_getElem? hwₗ, by omega⟩
  obtain ⟨y, hy, hyL, hjy⟩ := Nat.find_spec hex
  set m := Nat.find hex with hm
  have hm0 : 0 < m := by
    by_contra h0
    have : m = 0 := by omega
    rw [this, hQ0] at hy; cases hy; omega
  have hmlen : m < (Q q).length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hy; simp at hy
  set i := Nat.findGreatest (fun k => ∃ x, (Q q)[k]? = some x ∧ x ∈ L) (m - 1) with hi
  obtain ⟨x, hx, hxL⟩ : ∃ x, (Q q)[i]? = some x ∧ x ∈ L :=
    Nat.findGreatest_spec (P := fun k => ∃ x, (Q q)[k]? = some x ∧ x ∈ L) (Nat.zero_le _)
      ⟨w₀, hQ0, List.mem_of_getElem? hw₀⟩
  have hi_le : i ≤ m - 1 := Nat.findGreatest_le _
  have hidx_ne : L.idxOf x ≠ j := by
    intro h
    exact hjq x (by rw [← h]; exact List.getElem?_idxOf hxL) (List.mem_of_getElem? hx)
  have hidx_lt : L.idxOf x < j := by
    by_contra hcon
    exact Nat.find_min hex (show i < m by omega) ⟨x, hx, hxL, by omega⟩
  refine ⟨L.idxOf x, L.idxOf y, (q, i, m), rfl,
    ⟨List.idxOf_lt_length_of_mem hyL, by omega, by simp only; omega, hmlen, ?_, ?_, ?_⟩,
    hidx_lt, hjy⟩
  · simp only; rw [hx, List.getElem?_idxOf hxL]
  · simp only; rw [hy, List.getElem?_idxOf hyL]
  · intro k z hk1 hk2 hkz hzL
    exact Nat.findGreatest_is_greatest (show i < k by simpa using hk1)
      (show k ≤ m - 1 by simp only at hk2; omega) ⟨z, hkz, hzL⟩

lemma chordSys_of_threePaths (hT : ThreePaths G L Q)
    (h0 : (0, L.length - 1) ∉ chordSet L Q) : ChordSys (L.length - 1) (chordSet L Q) := by
  refine ⟨fun c ⟨w, hw⟩ => hw.2.1, fun c ⟨w, hw⟩ => by have := hw.1; omega, ?_, ?_, ?_⟩
  · rintro c ⟨w, hw⟩ c' ⟨w', hw'⟩ h hne
    exact hw.origin hT hw' h (by simpa using hne)
  · rintro c ⟨w, hw⟩ c' ⟨w', hw'⟩ h hne
    exact hw.term hT hw' h (by simpa using hne)
  · intro j hj0 hjl
    obtain ⟨x, hx⟩ : ∃ x, L[j]? = some x := ⟨L[j], List.getElem?_eq_getElem _⟩
    have hone : ∀ q q', q ≠ q' → x ∈ Q q → x ∉ Q q' := by
      intro q q' hq h1 h2
      rcases idx_of_ends hT hx (hT.disj q q' hq x h1 h2) with h | h <;> omega
    obtain ⟨q₁, q₂, hq, h₁, h₂⟩ : ∃ q₁ q₂ : Fin 3, q₁ ≠ q₂ ∧ x ∉ Q q₁ ∧ x ∉ Q q₂ := by
      by_cases hx0 : x ∈ Q 0
      · exact ⟨1, 2, by decide, hone 0 1 (by decide) hx0, hone 0 2 (by decide) hx0⟩
      · by_cases hx1 : x ∈ Q 1
        · exact ⟨0, 2, by decide, hx0, hone 1 2 (by decide) hx1⟩
        · exact ⟨0, 1, by decide, hx0, hx1⟩
    have hx' : ∀ q, x ∉ Q q → ∀ y, L[j]? = some y → y ∉ Q q := by
      intro q h y hy; rw [hx] at hy; cases hy; exact h
    obtain ⟨a₁, b₁, w₁, hq₁, hw₁, ha₁, hb₁⟩ := exists_wit_jump hT q₁ hj0 hjl (hx' _ h₁)
    obtain ⟨a₂, b₂, w₂, hq₂, hw₂, ha₂, hb₂⟩ := exists_wit_jump hT q₂ hj0 hjl (hx' _ h₂)
    refine ⟨(a₁, b₁), ⟨w₁, hw₁⟩, (a₂, b₂), ⟨w₂, hw₂⟩, ?_, ha₁, hb₁, ha₂, hb₂⟩
    intro heq
    simp only [Prod.mk.injEq] at heq
    have hne : w₁.1 ≠ w₂.1 := by rw [hq₁, hq₂]; exact hq
    have e := hw₁.ends_of_ne hT hw₂ hne
    have hbL := hw₁.1
    have ha0 : a₁ = 0 := by rcases e.1 heq.1 with h | h <;> omega
    have hbl : b₁ = L.length - 1 := by rcases e.2 heq.2 with h | h <;> omega
    apply h0
    subst ha0
    refine ⟨w₁, ?_⟩
    show Wit L Q 0 (L.length - 1) w₁
    rw [← hbl]; exact hw₁

lemma mem_realise {s t : ℕ} {z : V} (hz : z ∈ realise L Q s t) :
    (∃ w, Wit L Q s t w ∧ z ∈ seg Q w) ∨ (∃ w, Wit L Q t s w ∧ z ∈ seg Q w) := by
  unfold realise at hz
  split_ifs at hz with h h'
  · exact Or.inl ⟨_, h.choose_spec, hz⟩
  · exact Or.inr ⟨_, h'.choose_spec, List.mem_reverse.1 hz⟩
  · simp at hz

lemma liftData_of_threePaths (hT : ThreePaths G L Q) (w₀ : V) :
    LiftData G (skel (chordSet L Q)) (L.length - 1) (fun z => L.getD z w₀) (realise L Q) := by
  have h3 := hT.len
  have hφ : ∀ z, z ≤ L.length - 1 → L[z]? = some (L.getD z w₀) := by
    intro z hz
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl
  have hφL : ∀ z, z ≤ L.length - 1 → L.getD z w₀ ∈ L := fun z hz =>
    List.mem_of_getElem? (hφ z hz)
  have hoff : ∀ s t, ∀ z ∈ realise L Q s t, z ∉ L := by
    intro s t z hz
    rcases mem_realise hz with ⟨w, hw, hzw⟩ | ⟨w, hw, hzw⟩
    · exact hw.not_mem_L hzw
    · exact hw.not_mem_L hzw
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s t hs ht he
    exact (List.Nodup.getElem?_inj (by omega) hT.pathL.2).mp
      ((hφ s hs).trans (he ▸ (hφ t ht).symm))
  · intro s t hs ht hadj
    unfold realise
    split_ifs with h h'
    · exact h.choose_spec.chain hT (hφ s hs) (hφ t ht)
    · have := h'.choose_spec.chain hT (hφ t ht) (hφ s hs)
      have hrev : L.getD s w₀ :: ((seg Q h'.choose).reverse ++ [L.getD t w₀]) =
          (L.getD t w₀ :: (seg Q h'.choose ++ [L.getD s w₀])).reverse := by simp
      rw [hrev, List.isChain_reverse]
      exact this.imp (fun a b hab => hab.symm)
    · obtain ⟨-, hst | hts | hst | hts⟩ := hadj
      · subst hst
        have := hT.pathL.1.getElem s (by omega)
        simp only [List.nil_append]
        rw [List.isChain_pair]
        simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show s < L.length by omega),
          List.getElem?_eq_getElem (show s + 1 < L.length by omega)] using this
      · subst hts
        have := hT.pathL.1.getElem t (by omega)
        simp only [List.nil_append]
        rw [List.isChain_pair]
        simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show t < L.length by omega),
          List.getElem?_eq_getElem (show t + 1 < L.length by omega)] using this.symm
      · exact absurd hst h
      · exact absurd hts h'
  · intro s t _ _ _
    unfold realise
    split_ifs
    · exact seg_nodup hT _
    · exact List.nodup_reverse.2 (seg_nodup hT _)
    · exact List.nodup_nil
  · intro s t _ _ _ z hz u hu he
    exact hoff s t z hz (he ▸ hφL u hu)
  · intro s t s' t' _ _ _ _ _ _ z hz hz'
    rcases mem_realise hz with ⟨w, hw, hzw⟩ | ⟨w, hw, hzw⟩ <;>
      rcases mem_realise hz' with ⟨w', hw', hzw'⟩ | ⟨w', hw', hzw'⟩
    · exact Or.inl (hw.disj hT hw' hzw hzw')
    · have := hw.disj hT hw' hzw hzw'; exact Or.inr ⟨this.1, this.2⟩
    · have := hw.disj hT hw' hzw hzw'; exact Or.inr ⟨this.2, this.1⟩
    · have := hw.disj hT hw' hzw hzw'; exact Or.inl ⟨this.2, this.1⟩

/-- **Three internally disjoint paths give a long cycle.** -/
theorem cycle_of_three_paths (hT : ThreePaths G L Q) :
    ∃ c, IsCycleN G c ∧ 2 * (L.length - 1) + 8 ≤ 7 * c.length := by
  have h3 := hT.len
  obtain ⟨w₀, -⟩ : ∃ w₀, L.head? = some w₀ := by
    cases L with
    | nil => simp at h3
    | cons a t => exact ⟨a, rfl⟩
  have hD := liftData_of_threePaths hT w₀
  by_cases h0 : (0, L.length - 1) ∈ chordSet L Q
  · -- the cycle `0, 1, …, ℓ` of the skeleton
    have hcyc : IsCycleN (skel (chordSet L Q)) (List.range' 0 (L.length - 1 + 1)) := by
      refine ⟨⟨chain_range' _ _ _, List.nodup_range'⟩, by simp; omega, ?_⟩
      intro a ha b hb
      simp [List.head?_range', List.getLast?_range'] at ha hb
      subst ha; subst hb
      exact ⟨by omega, Or.inr (Or.inr (Or.inr h0))⟩
    obtain ⟨c, hc, hlen⟩ := lift_cycle hD hcyc
      (fun z hz => by rw [List.mem_range'_1] at hz; omega)
    exact ⟨c, hc, by simp at hlen; omega⟩
  · have hC := chordSys_of_threePaths hT h0
    obtain ⟨P, P', hg, htd⟩ := exists_td_vines hC (by omega)
    obtain ⟨c, hc, hcl, hlen⟩ := long_cycle_of_td hC hg htd
    obtain ⟨c', hc', hlen'⟩ := lift_cycle hD hc hcl
    exact ⟨c', hc', by omega⟩

end

end BondyLocke
