module
public import RequestProject.CycleMain

/-!
# An unconditional square-root path-to-cycle bound

In a `2`-connected finite graph, a path with `N` vertices yields a cycle of length at least
about `√N`.  The argument: split the path into three thirds `X`, middle, `Y`.  Either every
`X`–`Y` path is long, and then two disjoint `X`–`Y` paths (Menger) close up through `X` and `Y`
into a long cycle; or some `X`–`Y` path `S` is short, and then one of the pieces of `S` between
consecutive visits to the path jumps over a long stretch of the path, giving a long cycle.
-/

@[expose] public section


open Classical

namespace Lovasz

variable {V : Type*} {G : SimpleGraph V}

/-- Gluing two chains along a shared vertex. -/
lemma chain_glue {A B : List V} {b : V} (hA : A.IsChain G.Adj) (hAb : A.getLast? = some b)
    (hB : (b :: B).IsChain G.Adj) : (A ++ B).IsChain G.Adj := by
  obtain ⟨A', rfl⟩ : ∃ A', A = A' ++ [b] := by
    rw [List.getLast?_eq_some_iff] at hAb
    exact hAb
  rw [List.append_assoc, List.singleton_append]
  rw [List.isChain_append] at hA ⊢
  exact ⟨hA.1, hB, fun x hx y hy => by
    simp at hy; subst hy; exact hA.2.2 x hx b (by simp)⟩

/-- A closed chain on distinct vertices is a cycle. -/
lemma isCycleL_of_chain {x : V} {W : List V} (hnd : (x :: W).Nodup)
    (hc : (x :: W ++ [x]).IsChain G.Adj) (h2 : 2 ≤ W.length) : IsCycleL G (x :: W) := by
  rw [List.isChain_append] at hc
  refine ⟨⟨hc.1, hnd⟩, by simp; omega, fun a ha b hb => ?_⟩
  simp at ha; rw [← ha]
  exact hc.2.2 b hb x (by simp)

/-- A segment of a path between two positions. -/
lemma exists_segment {l : List V} (hl : IsPathL G l) {i j : ℕ} (hij : i < j)
    (hj : j < l.length) :
    ∃ m : List V, (l[i] :: m ++ [l[j]]).IsChain G.Adj ∧ m.Nodup ∧ m.length + 1 = j - i ∧
      ∀ x ∈ m, ∃ k, i < k ∧ k < j ∧ ∃ hk : k < l.length, l[k] = x := by
  set m := (l.drop (i + 1)).take (j - i - 1) with hm
  have hdec : l.drop i = l[i] :: (m ++ l[j] :: l.drop (j + 1)) := by
    rw [List.drop_eq_getElem_cons (by omega)]
    congr 1
    conv_lhs => rw [← List.take_append_drop (j - i - 1) (l.drop (i + 1))]
    congr 1
    rw [List.drop_drop, List.drop_eq_getElem_cons (by omega)]
    congr 2 <;> omega
  have hinf : (l[i] :: m ++ [l[j]]) <:+: l := by
    refine List.IsInfix.trans ?_ (List.drop_suffix i l).isInfix
    rw [hdec]
    exact (List.prefix_append (l[i] :: m ++ [l[j]]) (l.drop (j + 1))).isInfix.trans
      (by simp)
  refine ⟨m, (hl.infix hinf).1, ?_, ?_, ?_⟩
  · have := (hl.infix hinf).2
    simp only [List.cons_append, List.nodup_cons, List.nodup_append] at this
    exact this.2.1
  · simp [hm]; omega
  · intro x hx
    rw [hm] at hx
    obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hx
    simp only [List.length_take, List.length_drop] at hn
    refine ⟨i + 1 + n, by omega, by omega, by omega, ?_⟩
    simp [List.getElem_take, List.getElem_drop]

/-- A segment of a path between two distinct positions, in either direction. -/
lemma exists_segment' {l : List V} (hl : IsPathL G l) {i j : ℕ} (hij : i ≠ j)
    (hi : i < l.length) (hj : j < l.length) :
    ∃ m : List V, (l[i] :: m ++ [l[j]]).IsChain G.Adj ∧ m.Nodup ∧
      m.length + 1 = max i j - min i j ∧
      ∀ x ∈ m, ∃ k, min i j < k ∧ k < max i j ∧ ∃ hk : k < l.length, l[k] = x := by
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · obtain ⟨m, h1, h2, h3, h4⟩ := exists_segment hl h hj
    refine ⟨m, h1, h2, by omega, fun x hx => ?_⟩
    obtain ⟨k, hk1, hk2, hk, rfl⟩ := h4 x hx
    exact ⟨k, by omega, by omega, hk, rfl⟩
  · obtain ⟨m, h1, h2, h3, h4⟩ := exists_segment hl h hi
    refine ⟨m.reverse, ?_, List.nodup_reverse.2 h2, by simp; omega, fun x hx => ?_⟩
    · have := List.isChain_reverse.2 (h1.imp fun _ _ hab => hab.symm)
      simpa using this
    · obtain ⟨k, hk1, hk2, hk, rfl⟩ := h4 x (List.mem_reverse.1 hx)
      exact ⟨k, by omega, by omega, hk, rfl⟩

/-- Distance between two positions. -/
def posDist (i j : ℕ) : ℕ := max i j - min i j

/-- **Pigeonhole along a path.**  A path `S` from position `i₀` to position `j₀` of `l`
contains a piece `A` running between two positions `i ≠ j` of `l`, whose interior avoids `l`,
and which jumps at least `1/(|S| - 1)` of the total displacement. -/
lemma exists_arc {l : List V} (hl : l.Nodup) :
    ∀ (n : ℕ) (S : List V), S.length = n → IsPathL G S → ∀ (i₀ j₀ : ℕ)
      (hi₀ : i₀ < l.length) (hj₀ : j₀ < l.length), i₀ ≠ j₀ →
      S.head? = some l[i₀] → S.getLast? = some l[j₀] →
      ∃ (A : List V) (i j : ℕ) (hi : i < l.length) (hj : j < l.length), IsPathL G A ∧
        A.head? = some l[i] ∧ A.getLast? = some l[j] ∧ i ≠ j ∧
        (∀ x ∈ A, x ∈ l → x = l[i] ∨ x = l[j]) ∧
        posDist i₀ j₀ ≤ (S.length - 1) * posDist i j := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S hSn hS i₀ j₀ hi₀ hj₀ hij hhead hlast
  obtain ⟨rest, rfl⟩ : ∃ rest, S = l[i₀] :: rest := by
    cases S with
    | nil => simp at hhead
    | cons a t => simp at hhead; exact ⟨t, by rw [hhead]⟩
  have hrest_ne : rest ≠ [] := by
    rintro rfl; simp at hlast
    exact hij ((List.Nodup.getElem_inj_iff hl).1 hlast)
  have hlast' : rest.getLast? = some l[j₀] := by
    cases hz : rest.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.1 hz) hrest_ne
    | some z => simp [List.getLast?_cons, hz] at hlast; simp [hlast]
  obtain ⟨r1, r2, q, hq, hdec, hr1⟩ := exists_prefix_first_mem {x | x ∈ l}
    ⟨l[j₀], List.mem_of_getLast? hlast', List.getElem_mem _⟩
  subst hdec
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (show q ∈ l from hq)
  have hnd := hS.2
  have hki : k ≠ i₀ := by
    intro h; subst h
    simp at hnd
  -- the first piece
  have hA0 : IsPathL G (l[i₀] :: r1 ++ [l[k]]) :=
    hS.prefix ⟨r2, by simp⟩
  have hA0mem : ∀ x ∈ l[i₀] :: r1 ++ [l[k]], x ∈ l → x = l[i₀] ∨ x = l[k] := by
    intro x hx hxl
    simp only [List.cons_append, List.mem_cons, List.mem_append] at hx
    rcases hx with h | h | h
    · exact Or.inl h
    · exact absurd hxl (hr1 x h)
    · exact Or.inr (by simpa using h)
  by_cases hr2 : r2 = []
  · subst hr2
    have hkj : l[k] = l[j₀] := by simpa using hlast'
    have hkj' : k = j₀ := (List.Nodup.getElem_inj_iff hl).1 hkj
    subst hkj'
    refine ⟨_, i₀, k, hi₀, hk, hA0, by simp, by rw [List.getLast?_append]; simp, hij, hA0mem, ?_⟩
    simp
    nlinarith [Nat.zero_le (posDist i₀ k)]
  · have hS' : IsPathL G (l[k] :: r2) := hS.suffix ⟨l[i₀] :: r1, by simp⟩
    have hlast2 : (l[k] :: r2).getLast? = some l[j₀] := by
      rw [← hlast', List.getLast?_append, List.getLast?_cons]; simp
    have hkj : k ≠ j₀ := by
      intro h; subst h
      have hmem : l[k] ∈ r2 := by
        have := List.mem_of_getLast? hlast2
        rcases List.mem_cons.1 this with h | h
        · -- `r2` nonempty with last element equal to its predecessor
          obtain ⟨z, hz⟩ : ∃ z, r2.getLast? = some z := by
            cases h' : r2.getLast? with
            | none => exact absurd (List.getLast?_eq_none_iff.1 h') hr2
            | some z => exact ⟨z, rfl⟩
          have : (l[k] :: r2).getLast? = some z := by simp [List.getLast?_cons, hz]
          rw [this] at hlast2
          cases hlast2
          exact List.mem_of_getLast? hz
        · exact h
      have := hS'.2
      simp at this
      exact this.1 hmem
    obtain ⟨A, i, j, hi, hj, hA, hAh, hAl, hij', hAmem, hbound⟩ :=
      ih (l[k] :: r2).length (by rw [← hSn]; simp) _ rfl hS' k j₀ hk hj₀ hkj rfl hlast2
    have htri : posDist i₀ j₀ ≤ posDist i₀ k + posDist k j₀ := by
      unfold posDist; omega
    have hlen : (l[i₀] :: (r1 ++ l[k] :: r2)).length - 1 =
        ((l[k] :: r2).length - 1) + (r1.length + 1) := by simp; omega
    rcases le_total (posDist i₀ k) (posDist i j) with h | h
    · refine ⟨A, i, j, hi, hj, hA, hAh, hAl, hij', hAmem, ?_⟩
      rw [hlen]; nlinarith
    · refine ⟨_, i₀, k, hi₀, hk, hA0, by simp, by rw [List.getLast?_append]; simp, hki.symm, hA0mem, ?_⟩
      rw [hlen]
      have : posDist k j₀ ≤ ((l[k] :: r2).length - 1) * posDist i₀ k :=
        hbound.trans (Nat.mul_le_mul_left _ h)
      nlinarith

lemma getElem_ne_of_ne {l : List V} (hl : l.Nodup) {i j : ℕ} (hi : i < l.length)
    (hj : j < l.length) (h : i ≠ j) : l[i] ≠ l[j] :=
  fun h' => h ((List.Nodup.getElem_inj_iff hl).1 h')

/-- A piece `A` joining two positions `i, j` of the path `l` whose interior avoids `l` closes up
with the segment of `l` between them into a cycle. -/
lemma cycle_of_arc {l : List V} (hl : IsPathL G l) {A : List V} (hA : IsPathL G A) {i j : ℕ}
    (hi : i < l.length) (hj : j < l.length) (hAh : A.head? = some l[i])
    (hAl : A.getLast? = some l[j]) (hmem : ∀ x ∈ A, x ∈ l → x = l[i] ∨ x = l[j])
    (hd : 2 ≤ posDist i j) : ∃ c, IsCycleL G c ∧ posDist i j + 1 ≤ c.length := by
  have hij : i ≠ j := by rintro rfl; simp [posDist] at hd
  obtain ⟨m, hmc, hmnd, hmlen, hmk⟩ := exists_segment' hl hij.symm hj hi
  obtain ⟨At, rfl⟩ : ∃ At, A = l[i] :: At := by
    cases A with
    | nil => simp at hAh
    | cons a t => simp at hAh; exact ⟨t, by rw [hAh]⟩
  have hAt : At ≠ [] := by
    rintro rfl; simp at hAl; exact getElem_ne_of_ne hl.2 hi hj hij hAl
  have hAtlen : 1 ≤ At.length := List.length_pos_of_ne_nil hAt
  have hmi : ∀ x ∈ m, x ≠ l[i] ∧ x ≠ l[j] ∧ x ∈ l := by
    intro x hx
    obtain ⟨k, hk1, hk2, hk, rfl⟩ := hmk x hx
    exact ⟨getElem_ne_of_ne hl.2 hk hi (by omega), getElem_ne_of_ne hl.2 hk hj (by omega),
      List.getElem_mem _⟩
  refine ⟨l[i] :: (At ++ m), isCycleL_of_chain ?_ ?_ ?_, ?_⟩
  · rw [← List.cons_append, List.nodup_append]
    refine ⟨hA.2, hmnd, fun x hx y hy hxy => ?_⟩
    subst hxy
    obtain ⟨h1, h2, h3⟩ := hmi x hy
    rcases hmem x hx h3 with h | h
    · exact h1 h
    · exact h2 h
  · have h1 : l[i] :: (At ++ m) ++ [l[i]] = (l[i] :: At) ++ (m ++ [l[i]]) := by simp
    rw [h1]
    exact chain_glue hA.1 hAl (by simpa using hmc)
  · simp; unfold posDist at hd; omega
  · simp; unfold posDist at hd ⊢; omega

/-- The first `a` vertices of the path `l`. -/
def headSet (l : List V) (a : ℕ) : Set V := {v | ∃ k, ∃ hk : k < l.length, k < a ∧ l[k] = v}

/-- The last `a` vertices of the path `l`. -/
def tailSet (l : List V) (a : ℕ) : Set V :=
  {v | ∃ k, ∃ hk : k < l.length, l.length - a ≤ k ∧ l[k] = v}

lemma headSet_tailSet_disjoint {l : List V} (hl : l.Nodup) {a : ℕ} (h2a : 2 * a ≤ l.length)
    {v : V} (hX : v ∈ headSet l a) (hY : v ∈ tailSet l a) : False := by
  obtain ⟨k1, hk1, hk1a, rfl⟩ := hX
  obtain ⟨k2, hk2, hk2a, h⟩ := hY
  exact getElem_ne_of_ne hl hk2 hk1 (by omega) h

/-- **Closing two rails.**  Two disjoint paths from the first `a` vertices of `l` to the last
`a` vertices (meeting these sets only at their ends) close up, through segments of `l`, into a
cycle at least as long as the two rails together. -/
lemma cycle_of_rails {l : List V} (hl : IsPathL G l) {a : ℕ} (h2a : 2 * a ≤ l.length)
    {R1 R2 : List V} (hR1 : IsPathL G R1) (hR2 : IsPathL G R2)
    (h1h : ∃ x ∈ headSet l a, R1.head? = some x) (h2h : ∃ x ∈ headSet l a, R2.head? = some x)
    (h1l : ∃ y ∈ tailSet l a, R1.getLast? = some y)
    (h2l : ∃ y ∈ tailSet l a, R2.getLast? = some y)
    (h1X : ∀ z ∈ R1, z ∈ headSet l a → R1.head? = some z)
    (h2X : ∀ z ∈ R2, z ∈ headSet l a → R2.head? = some z)
    (h1Y : ∀ z ∈ R1, z ∈ tailSet l a → R1.getLast? = some z)
    (h2Y : ∀ z ∈ R2, z ∈ tailSet l a → R2.getLast? = some z)
    (hdisj : R1.Disjoint R2) :
    ∃ c, IsCycleL G c ∧ R1.length + R2.length ≤ c.length := by
  have hnd := hl.2
  have hXY := fun {v} => @headSet_tailSet_disjoint V l hnd a h2a v
  obtain ⟨_, ⟨i1, hi1, hi1a, rfl⟩, h1h⟩ := h1h
  obtain ⟨_, ⟨i2, hi2, hi2a, rfl⟩, h2h⟩ := h2h
  obtain ⟨_, ⟨j1, hj1, hj1a, rfl⟩, h1l⟩ := h1l
  obtain ⟨_, ⟨j2, hj2, hj2a, rfl⟩, h2l⟩ := h2l
  have hmemX : ∀ k (hk : k < l.length), k < a → l[k] ∈ headSet l a :=
    fun k hk hka => ⟨k, hk, hka, rfl⟩
  have hmemY : ∀ k (hk : k < l.length), l.length - a ≤ k → l[k] ∈ tailSet l a :=
    fun k hk hka => ⟨k, hk, hka, rfl⟩
  have hi12 : i1 ≠ i2 := by
    rintro rfl
    exact hdisj (List.mem_of_head? h1h) (List.mem_of_head? h2h)
  have hj12 : j1 ≠ j2 := by
    rintro rfl
    exact hdisj (List.mem_of_getLast? h1l) (List.mem_of_getLast? h2l)
  obtain ⟨mY, hmYc, hmYnd, -, hmYk⟩ := exists_segment' hl hj12 hj1 hj2
  obtain ⟨mX, hmXc, hmXnd, -, hmXk⟩ := exists_segment' hl hi12.symm hi2 hi1
  have hmY : ∀ x ∈ mY, x ∈ tailSet l a ∧ x ≠ l[j1] ∧ x ≠ l[j2] := by
    intro x hx
    obtain ⟨k, hk1, hk2, hk, rfl⟩ := hmYk x hx
    exact ⟨hmemY k hk (by omega), getElem_ne_of_ne hnd hk hj1 (by omega),
      getElem_ne_of_ne hnd hk hj2 (by omega)⟩
  have hmX : ∀ x ∈ mX, x ∈ headSet l a ∧ x ≠ l[i1] ∧ x ≠ l[i2] := by
    intro x hx
    obtain ⟨k, hk1, hk2, hk, rfl⟩ := hmXk x hx
    exact ⟨hmemX k hk (by omega), getElem_ne_of_ne hnd hk hi1 (by omega),
      getElem_ne_of_ne hnd hk hi2 (by omega)⟩
  obtain ⟨R1t, rfl⟩ : ∃ t, R1 = l[i1] :: t := by
    cases R1 with
    | nil => simp at h1h
    | cons x t => simp at h1h; exact ⟨t, by rw [h1h]⟩
  -- the reversed second rail
  have hR2r : IsPathL G R2.reverse := hR2.reverse
  obtain ⟨R2t, hR2t⟩ : ∃ t, R2.reverse = l[j2] :: t := by
    cases h : R2.reverse with
    | nil => simp at h; subst h; simp at h2h
    | cons x t =>
      have : R2.reverse.head? = some l[j2] := by rw [List.head?_reverse, h2l]
      rw [h] at this; simp at this; exact ⟨t, by rw [this]⟩
  have hR2tl : R2t.getLast? = some l[i2] := by
    have : R2.reverse.getLast? = some l[i2] := by rw [List.getLast?_reverse, h2h]
    rw [hR2t, List.getLast?_cons] at this
    cases h : R2t.getLast? with
    | none =>
      rw [h] at this; simp at this
      exact absurd this (getElem_ne_of_ne hnd hj2 hi2 (by omega))
    | some z => rw [h] at this; simpa using this
  have hR2mem : ∀ z, z ∈ R2 ↔ z ∈ l[j2] :: R2t := by
    intro z; rw [← hR2t, List.mem_reverse]
  -- membership constraints
  have hR1X : ∀ z ∈ l[i1] :: R1t, z ∈ headSet l a → z = l[i1] := by
    intro z hz hzX; have := h1X z hz hzX; simp at this; exact this.symm
  have hR1Y : ∀ z ∈ l[i1] :: R1t, z ∈ tailSet l a → z = l[j1] := by
    intro z hz hzY; have := h1Y z hz hzY; rw [h1l] at this; exact (Option.some.inj this).symm
  have hR2X : ∀ z ∈ R2, z ∈ headSet l a → z = l[i2] := by
    intro z hz hzX; have := h2X z hz hzX; rw [h2h] at this; exact (Option.some.inj this).symm
  have hR2Y : ∀ z ∈ R2, z ∈ tailSet l a → z = l[j2] := by
    intro z hz hzY; have := h2Y z hz hzY; rw [h2l] at this; exact (Option.some.inj this).symm
  have hR1t : R1t ≠ [] := by
    rintro rfl
    simp at h1l
    exact getElem_ne_of_ne hnd hi1 hj1 (by omega) h1l
  have hR2tne : R2t ≠ [] := by rintro rfl; simp at hR2tl
  refine ⟨l[i1] :: (R1t ++ (mY ++ ((l[j2] :: R2t) ++ mX))), isCycleL_of_chain ?_ ?_ ?_, ?_⟩
  · rw [← List.cons_append, List.nodup_append, List.nodup_append, List.nodup_append]
    refine ⟨hR1.2, ⟨hmYnd, ⟨by rw [← hR2t]; exact hR2r.2, hmXnd, ?_⟩, ?_⟩, ?_⟩
    · intro x hx y hy hxy; subst hxy
      rw [← hR2mem] at hx
      exact (hmX x hy).2.2 (hR2X x hx (hmX x hy).1)
    · intro x hx y hy hxy; subst hxy
      rcases List.mem_append.1 hy with hy | hy
      · rw [← hR2mem] at hy
        exact (hmY x hx).2.2 (hR2Y x hy (hmY x hx).1)
      · exact hXY (hmX x hy).1 (hmY x hx).1
    · intro x hx y hy hxy; subst hxy
      rcases List.mem_append.1 hy with hy | hy
      · exact (hmY x hy).2.1 (hR1Y x hx (hmY x hy).1)
      rcases List.mem_append.1 hy with hy | hy
      · rw [← hR2mem] at hy
        exact hdisj hx hy
      · exact (hmX x hy).2.1 (hR1X x hx (hmX x hy).1)
  · have e : l[i1] :: (R1t ++ (mY ++ ((l[j2] :: R2t) ++ mX))) ++ [l[i1]] =
        (((l[i1] :: R1t) ++ (mY ++ [l[j2]])) ++ R2t) ++ (mX ++ [l[i1]]) := by simp
    rw [e]
    have s1 := chain_glue hR1.1 h1l (by simpa using hmYc)
    have s2 := chain_glue (b := l[j2]) s1 (by rw [List.getLast?_append]; simp)
      (by rw [← hR2t]; exact hR2r.1)
    exact chain_glue (b := l[i2]) s2 (by rw [List.getLast?_append, hR2tl]; simp) (by simpa using hmXc)
  · have := List.length_pos_of_ne_nil hR1t
    simp; omega
  · rw [← List.length_reverse (as := R2), hR2t]
    simp; omega

/-- One of two distinct vertices avoids a set with at most one element. -/
lemma exists_not_mem_of_card_lt_two {T : Finset V} (hT : T.card < 2) {x y : V} (hxy : x ≠ y) :
    x ∉ T ∨ y ∉ T := by
  by_contra h
  push_neg at h
  have : ({x, y} : Finset V) ⊆ T := by
    intro z hz; simp at hz; rcases hz with rfl | rfl
    · exact h.1
    · exact h.2
  have := Finset.card_le_card this
  rw [Finset.card_pair hxy] at this
  omega

/-- **The square-root dichotomy.**  Let `l` be a path in a `2`-connected finite graph, and let
`2 ≤ a` with `2a ≤ |l|` and `m ≤ |l| - 2a`.  Then there is a cycle which either has at least
`2(m+1)` vertices, or has at least `(|l| - 2a + 1)/(m - 1)` vertices. -/
theorem cycle_dichotomy [Fintype V] (hG : KConnected G 2) {l : List V} (hl : IsPathL G l)
    {a m : ℕ} (ha : 2 ≤ a) (h2a : 2 * a ≤ l.length) (hm : m ≤ l.length - 2 * a) :
    ∃ c, IsCycleL G c ∧ (2 * (m + 1) ≤ c.length ∨ l.length - 2 * a + 1 ≤ (m - 1) * c.length) := by
  have hnd := hl.2
  by_cases hshort : ∃ S, IsPathL G S ∧ (∃ x ∈ headSet l a, S.head? = some x) ∧
      (∃ y ∈ tailSet l a, S.getLast? = some y) ∧ S.length ≤ m
  · obtain ⟨S, hS, ⟨_, ⟨i₀, hi₀, hi₀a, rfl⟩, hSh⟩, ⟨_, ⟨j₀, hj₀, hj₀a, rfl⟩, hSl⟩, hSm⟩ :=
      hshort
    obtain ⟨A, i, j, hi, hj, hA, hAh, hAl, -, hAmem, hbound⟩ :=
      exists_arc hnd S.length S rfl hS i₀ j₀ hi₀ hj₀ (by omega) hSh hSl
    have hd0 : l.length - 2 * a + 1 ≤ posDist i₀ j₀ := by unfold posDist; omega
    have hSm' : S.length - 1 ≤ m - 1 := by omega
    by_cases hd : 2 ≤ posDist i j
    · obtain ⟨c, hc, hclen⟩ := cycle_of_arc hl hA hi hj hAh hAl hAmem hd
      refine ⟨c, hc, Or.inr ?_⟩
      calc l.length - 2 * a + 1 ≤ (S.length - 1) * posDist i j := hd0.trans hbound
        _ ≤ (m - 1) * c.length := Nat.mul_le_mul hSm' (by omega)
    · exfalso
      have : (S.length - 1) * posDist i j ≤ (m - 1) * 1 := Nat.mul_le_mul hSm' (by omega)
      omega
  · push_neg at hshort
    obtain ⟨p, hp⟩ := menger G (headSet l a) (tailSet l a) 2 (by
      intro T hT
      by_contra hlt
      push_neg at hlt
      have h01 : l[0]'(by omega) ≠ l[1]'(by omega) := getElem_ne_of_ne hnd _ _ (by omega)
      have h01' : l[l.length - 1]'(by omega) ≠ l[l.length - 2]'(by omega) :=
        getElem_ne_of_ne hnd _ _ (by omega)
      obtain ⟨x, hxX, hxT⟩ : ∃ x ∈ headSet l a, x ∉ T := by
        rcases exists_not_mem_of_card_lt_two hlt h01 with h | h
        · exact ⟨_, ⟨0, by omega, by omega, rfl⟩, h⟩
        · exact ⟨_, ⟨1, by omega, by omega, rfl⟩, h⟩
      obtain ⟨y, hyY, hyT⟩ : ∃ y ∈ tailSet l a, y ∉ T := by
        rcases exists_not_mem_of_card_lt_two hlt h01' with h | h
        · exact ⟨_, ⟨l.length - 1, by omega, by omega, rfl⟩, h⟩
        · exact ⟨_, ⟨l.length - 2, by omega, by omega, rfl⟩, h⟩
      exact hT x hxX y hyY (hG.2 T hlt x y hxT hyT))
    obtain ⟨hpP, hpA, hpB, hpA', hpB', hpD⟩ := hp
    have hlen : ∀ i, m + 1 ≤ (p i).length := fun i => hshort _ (hpP i) (hpA i) (hpB i)
    obtain ⟨c, hc, hclen⟩ := cycle_of_rails hl h2a (hpP 0) (hpP 1) (hpA 0) (hpA 1) (hpB 0)
      (hpB 1) (hpA' 0) (hpA' 1) (hpB' 0) (hpB' 1) (hpD 0 1 (by decide))
    exact ⟨c, hc, Or.inl (by have := hlen 0; have := hlen 1; omega)⟩

lemma KConnected.mono [Fintype V] {j k : ℕ} (h : KConnected G k) (hjk : j ≤ k) :
    KConnected G j :=
  ⟨lt_of_le_of_lt hjk h.1, fun T hT => h.2 T (lt_of_lt_of_le hT hjk)⟩

/-- **Square-root path-to-cycle bound.**  In a `2`-connected finite graph, a path with `N ≥ 9`
vertices yields a cycle with at least `√N / 3` vertices (equivalently, edges). -/
theorem cycle_sqrt_of_path [Fintype V] (hG : KConnected G 2) {l : List V} (hl : IsPathL G l)
    (h9 : 9 ≤ l.length) : ∃ c, IsCycleL G c ∧ Real.sqrt l.length / 3 ≤ c.length := by
  set N := l.length with hN
  set s := Nat.sqrt N with hs
  have hss : s * s ≤ N := Nat.sqrt_le N
  have hlt : N < (s + 1) * (s + 1) := Nat.lt_succ_sqrt N
  have hs3 : 3 ≤ s := Nat.le_sqrt.2 h9
  have hsN : s ≤ N - 2 * (N / 3) := by
    have : 3 * s ≤ N := le_trans (Nat.mul_le_mul_right s hs3) hss
    omega
  obtain ⟨c, hc, hcl⟩ := cycle_dichotomy hG hl (a := N / 3) (m := s) (by omega) (by omega) hsN
  refine ⟨c, hc, ?_⟩
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hsqrt_lt : Real.sqrt N < s + 1 := by
    rw [Real.sqrt_lt' (by positivity)]
    have : (N : ℝ) < ((s + 1) * (s + 1) : ℕ) := by exact_mod_cast hlt
    push_cast at this; nlinarith
  have hs_le : (s : ℝ) ≤ Real.sqrt N := by
    rw [Real.le_sqrt (by positivity) hN0]
    have : ((s * s : ℕ) : ℝ) ≤ N := by exact_mod_cast hss
    push_cast at this; nlinarith
  rcases hcl with h | h
  · have : ((2 * (s + 1) : ℕ) : ℝ) ≤ c.length := by exact_mod_cast h
    push_cast at this
    have := Real.sqrt_nonneg (N : ℝ)
    linarith
  · -- `N/3 ≤ (s-1) |c| ≤ √N |c|`
    have h1 : (N : ℝ) ≤ 3 * ((N - 2 * (N / 3) + 1 : ℕ) : ℝ) := by
      have : N ≤ 3 * (N - 2 * (N / 3) + 1) := by omega
      exact_mod_cast this
    have h2 : ((N - 2 * (N / 3) + 1 : ℕ) : ℝ) ≤ ((s - 1) * c.length : ℕ) := by exact_mod_cast h
    have h3 : ((s - 1 : ℕ) : ℝ) ≤ s := by exact_mod_cast Nat.sub_le s 1
    push_cast [Nat.cast_mul] at h1 h2
    have hc0 : (0 : ℝ) ≤ c.length := by positivity
    have h4 : (N : ℝ) ≤ 3 * (Real.sqrt N * c.length) := by
      have : ((s - 1 : ℕ) : ℝ) * c.length ≤ Real.sqrt N * c.length :=
        mul_le_mul_of_nonneg_right (h3.trans hs_le) hc0
      linarith
    have hpos : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < N))
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
    have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0
    nlinarith

/-- **Unconditional long cycles, square-root exponent.**  For every `ε > 0` there is `n₀` such
that every connected vertex-transitive graph of order `n ≥ n₀` contains a cycle of length at
least `n^(1/2 - ε)`.  (Obtained from the long-path theorem, Watkins' theorem and the square-root
path-to-cycle bound; no hypotheses.) -/
theorem vt_long_cycle_sqrt :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (X : SimpleGraph V),
      X.Connected → VertexTransitive X → n₀ ≤ Fintype.card V →
      ∃ (v : V) (c : X.Walk v v), c.IsCycle ∧
        (Fintype.card V : ℝ) ^ ((1 : ℝ) / 2 - ε) ≤ c.length := by
  intro ε hε
  set e := min ε (1 / 2) with he
  have he0 : 0 < e := lt_min hε (by norm_num)
  have he1 : e ≤ 1 / 2 := min_le_right _ _
  have heε : e ≤ ε := min_le_left _ _
  obtain ⟨n₁, hn₁⟩ := vt_long_path_unconditional e he0
  obtain ⟨n₂, hn₂⟩ := exists_nat_ge ((9 : ℝ) ^ (2 / e))
  refine ⟨max (max n₁ n₂) 1, fun V _ X hconn hvt hn => ?_⟩
  set n := Fintype.card V with hndef
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hn2 : (9 : ℝ) ^ (2 / e) ≤ n :=
    le_trans hn₂ (by exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn)
  -- `n^(e/2) ≥ 9`
  have h9 : (9 : ℝ) ≤ (n : ℝ) ^ (e / 2) := by
    have := Real.rpow_le_rpow (by positivity) hn2 (by positivity : (0 : ℝ) ≤ e / 2)
    rwa [← Real.rpow_mul (by norm_num), show 2 / e * (e / 2) = 1 by field_simp,
      Real.rpow_one] at this
  obtain ⟨l, hl, hllen⟩ := hn₁ V X hconn hvt (le_trans (le_trans (le_max_left _ _)
    (le_max_left _ _)) hn)
  have hN : (n : ℝ) ^ (1 - e) ≤ l.length := by linarith
  have hexp : (n : ℝ) ^ (e / 2) ≤ (n : ℝ) ^ (1 - e) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hlen9 : (9 : ℝ) ≤ l.length := by linarith
  have hl9 : 9 ≤ l.length := by exact_mod_cast hlen9
  have htarget : (n : ℝ) ^ ((1 : ℝ) / 2 - ε) ≤ (n : ℝ) ^ ((1 : ℝ) / 2 - e) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  rcases vt_cycle_of_path hconn hvt hl (by omega) with ⟨c, hc, hcl⟩ | hK
  · obtain ⟨v, w, hw, hwl⟩ := hc.exists_walk_isCycle
    refine ⟨v, w, hw, ?_⟩
    rw [hwl]
    have h1 : (n : ℝ) ^ ((1 : ℝ) / 2 - e) ≤ (n : ℝ) ^ (1 - e) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    have : (l.length : ℝ) ≤ c.length := by exact_mod_cast hcl
    linarith
  · obtain ⟨c, hc, hcl⟩ := cycle_sqrt_of_path (hK.mono (by norm_num)) hl hl9
    obtain ⟨v, w, hw, hwl⟩ := hc.exists_walk_isCycle
    refine ⟨v, w, hw, ?_⟩
    rw [hwl]
    -- `√|l| ≥ n^((1-e)/2) = n^(1/2 - e) · n^(e/2) ≥ 9 n^(1/2 - e)`
    have hsq : (n : ℝ) ^ ((1 - e) / 2) ≤ Real.sqrt l.length := by
      rw [Real.sqrt_eq_rpow, div_eq_mul_one_div (1 - e), Real.rpow_mul hn0.le]
      exact Real.rpow_le_rpow (by positivity) hN (by norm_num)
    have hsplit : (n : ℝ) ^ ((1 - e) / 2) = (n : ℝ) ^ ((1 : ℝ) / 2 - e) * (n : ℝ) ^ (e / 2) := by
      rw [← Real.rpow_add hn0]; ring_nf
    have hpos : 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 2 - e) := by positivity
    have : 9 * (n : ℝ) ^ ((1 : ℝ) / 2 - e) ≤ (n : ℝ) ^ ((1 - e) / 2) := by
      rw [hsplit]; nlinarith
    linarith

/-- **Unconditional long cycles in Cayley graphs, square-root exponent.** -/
theorem cayley_long_cycle_sqrt :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (H : Type) [Group H] [Finite H] (S : Set H),
      (cay S).Connected → n₀ ≤ Nat.card H →
      ∃ (v : H) (c : (cay S).Walk v v), c.IsCycle ∧
        (Nat.card H : ℝ) ^ ((1 : ℝ) / 2 - ε) ≤ c.length := by
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := vt_long_cycle_sqrt ε hε
  refine ⟨n₀, fun H _ _ S hconn hn => ?_⟩
  have := Fintype.ofFinite H
  rw [Nat.card_eq_fintype_card] at hn ⊢
  exact hn₀ H (cay S) hconn (vertexTransitive_cay S) hn

end Lovasz
