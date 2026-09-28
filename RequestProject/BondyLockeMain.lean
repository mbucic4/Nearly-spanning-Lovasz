module
public import RequestProject.CycleMain
public import RequestProject.BondyLocke.Chords

/-!
# The Bondy–Locke theorem and unconditional long cycles

J. A. Bondy and S. C. Locke (*Relative lengths of paths and cycles in 3-connected graphs*,
Discrete Math. 33 (1981) 111–122) proved that a `3`-connected graph containing a path with `ℓ`
edges contains a cycle with at least `2ℓ/5` edges.  We prove the weaker linear bound
`(2ℓ + 8)/7` (for `ℓ ≥ 2`), which is all that the long-cycle theorems need:

* `bondy_locke`: a finite `3`-connected graph with a path on `N ≥ 3` vertices has a cycle `c`
  with `2(N - 1) + 8 ≤ 7 |c|`.
* `pathToCycleLinear_two_sevenths`: `PathToCycleLinear (2/7)`.
* `vt_long_cycle` / `cayley_long_cycle`: the long-cycle theorems with exponent `1 - ε`, now
  without any hypothesis.

The combinatorial core (vines, their normalisation and the routing argument) is in
`RequestProject/BondyLocke/`; here we produce the three internally disjoint paths with Menger's
theorem.  (This file is not a `module`, because it imports the non-module files of the project.)
-/

@[expose] public section


open Classical

namespace Lovasz

variable {V : Type*}

/-- `G` with all edges at `u` and `v` removed. -/
def avoidTwo (G : SimpleGraph V) (u v : V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ≠ u ∧ x ≠ v ∧ y ≠ u ∧ y ≠ v
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2.2.1, h.2.2.2.2, h.2.1, h.2.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

lemma avoidTwo_le (G : SimpleGraph V) (u v : V) : avoidTwo G u v ≤ G := fun _ _ h => h.1

/-- The vertices of a chain in `avoidTwo G u v` starting away from `u, v` avoid `u, v`. -/
lemma avoidTwo_mem {G : SimpleGraph V} {u v : V} :
    ∀ (l : List V), l.IsChain (avoidTwo G u v).Adj → ∀ a, l.head? = some a → a ≠ u → a ≠ v →
      ∀ z ∈ l, z ≠ u ∧ z ≠ v
  | [], _, _, _, _, _, z, hz => by simp at hz
  | [x], _, a, ha, hau, hav, z, hz => by
      simp at ha hz; subst ha; subst hz; exact ⟨hau, hav⟩
  | x :: y :: t, hc, a, ha, hau, hav, z, hz => by
      simp at ha; subst ha
      rw [List.isChain_cons_cons] at hc
      rcases List.mem_cons.1 hz with rfl | hz
      · exact ⟨hau, hav⟩
      · exact avoidTwo_mem (y :: t) hc.2 y rfl hc.1.2.2.2.1 hc.1.2.2.2.2 z hz

/-- In a `3`-connected graph, the neighbourhoods of two non-adjacent vertices `u ≠ v` cannot be
separated by two vertices once `u` and `v` are deleted. -/
lemma three_le_sep [Fintype V] {G : SimpleGraph V} (hG : KConnected G 3) {u v : V} (huv : u ≠ v)
    (hadj : ¬ G.Adj u v) (T : Finset V)
    (hT : Separates (avoidTwo G u v) {x | G.Adj u x} {x | G.Adj v x} T) : 3 ≤ T.card := by
  by_contra hlt
  push_neg at hlt
  set T' := (T.erase u).erase v with hT'
  have hT'c : T'.card < 3 :=
    lt_of_le_of_lt ((Finset.card_erase_le).trans Finset.card_erase_le) hlt
  have hu' : u ∉ T' := by simp [hT', huv]
  have hv' : v ∉ T' := by simp [hT']
  obtain ⟨-, hr⟩ := hG.2 T' hT'c u v hu' hv'
  set H := avoidTwo G u v
  set s : Set V := {x | x ∉ T}
  -- invariant along the walk
  have key : ∀ x, Relation.ReflTransGen (fun a b => G.Adj a b ∧ b ∈ {w | w ∉ T'}) u x →
      x = u ∨ (x ≠ u ∧ x ≠ v ∧ ∃ a ∈ {x | G.Adj u x}, ReachIn H s a x) ∨
        (∃ a ∈ {x | G.Adj u x}, ∃ b ∈ {x | G.Adj v x}, ReachIn H s a b) := by
    intro x hx
    induction hx with
    | refl => exact Or.inl rfl
    | @tail y z _ hyz ih =>
      obtain ⟨hyz, hzT'⟩ := hyz
      have hzT : z ≠ u → z ≠ v → z ∉ T := by
        intro h1 h2 h3; exact hzT' (by simp [hT', h1, h2, h3])
      rcases ih with hyu0 | ⟨hyu, hyv, a, ha, hra⟩ | h
      · rw [hyu0] at hyz
        by_cases hzu : z = u
        · exact Or.inl hzu
        have hzv : z ≠ v := by rintro rfl; exact hadj hyz
        exact Or.inr (Or.inl ⟨hzu, hzv, z, hyz, hzT hzu hzv, Relation.ReflTransGen.refl⟩)
      · by_cases hzu : z = u
        · exact Or.inl hzu
        by_cases hzv : z = v
        · subst hzv
          exact Or.inr (Or.inr ⟨a, ha, y, hyz.symm, hra⟩)
        exact Or.inr (Or.inl ⟨hzu, hzv, a, ha, hra.1,
          hra.2.tail ⟨⟨hyz, hyu, hyv, hzu, hzv⟩, hzT hzu hzv⟩⟩)
      · exact Or.inr (Or.inr h)
  rcases key v hr with h | ⟨-, h, -⟩ | ⟨a, ha, b, hb, hab⟩
  · exact huv h.symm
  · exact h rfl
  · exact hT a ha b hb hab

/-- **Three internally disjoint paths.**  In a finite `3`-connected graph, the ends of a path `L`
with at least three vertices which are not adjacent are joined by three internally disjoint
paths. -/
theorem exists_threePaths [Fintype V] {G : SimpleGraph V} (hG : KConnected G 3) {L : List V}
    (hL : IsPathL G L) (h3 : 3 ≤ L.length) {u v : V} (hu : L.head? = some u)
    (hv : L.getLast? = some v) (hadj : ¬ G.Adj u v) :
    ∃ Q, BondyLocke.ThreePaths G L Q := by
  have huv : u ≠ v := by
    intro h
    subst h
    rw [List.head?_eq_getElem?] at hu
    rw [List.getLast?_eq_getElem?] at hv
    have := (List.Nodup.getElem?_inj (by omega) hL.2).mp (hu.trans hv.symm)
    omega
  obtain ⟨p, hpP, hpA, hpB, -, -, hpD⟩ :=
    menger (avoidTwo G u v) {x | G.Adj u x} {x | G.Adj v x} 3 (three_le_sep hG huv hadj)
  have hav : ∀ q, ∀ z ∈ p q, z ≠ u ∧ z ≠ v := by
    intro q
    obtain ⟨a, ha, hah⟩ := hpA q
    exact avoidTwo_mem (p q) (hpP q).1 a hah ha.ne' (fun h => hadj (h ▸ ha))
  refine ⟨fun q => u :: (p q ++ [v]), ⟨hL, h3, fun q => ⟨?_, ?_⟩, fun q => by simp [hu],
    fun q => by rw [hv, ← List.cons_append, List.getLast?_append]; simp, ?_⟩⟩
  · obtain ⟨a, ha, hah⟩ := hpA q
    obtain ⟨b, hb, hbl⟩ := hpB q
    obtain ⟨p', hp'⟩ : ∃ p', p q = a :: p' := by
      cases h : p q with
      | nil => rw [h] at hah; simp at hah
      | cons x t => rw [h] at hah; simp at hah; exact ⟨t, by rw [hah]⟩
    have hc : (p q ++ [v]).IsChain G.Adj := by
      rw [List.isChain_append]
      refine ⟨(hpP q).1.imp (fun _ _ h => h.1), List.isChain_singleton _, fun x hx y hy => ?_⟩
      rw [hbl] at hx; simp at hx hy; subst hx; subst hy; exact hb.symm
    rw [hp'] at hc ⊢
    exact List.IsChain.cons_cons ha hc
  · rw [List.nodup_cons, List.nodup_append]
    refine ⟨?_, (hpP q).2, List.nodup_singleton _, ?_⟩
    · simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨fun h => (hav q u h).1 rfl, huv⟩
    · intro x hx y hy hxy
      simp at hy; subst hy; subst hxy
      exact (hav q x hx).2 rfl
  · intro q q' hqq' z hz hz'
    simp only [List.mem_cons, List.mem_append, List.mem_nil_iff, or_false] at hz hz'
    rcases hz with rfl | hz | rfl
    · exact Or.inl (by simp [hu])
    · rcases hz' with rfl | hz' | rfl
      · exact Or.inl (by simp [hu])
      · exact absurd hz' (hpD q q' hqq' hz)
      · exact Or.inr (by simp [hv])
    · exact Or.inr (by simp [hv])

/-- **Bondy–Locke comparison** (with constant `2/7`).  A finite `3`-connected graph containing
a path on `N ≥ 3` vertices (`N - 1` edges) contains a cycle `c` with `2 (N - 1) + 8 ≤ 7 |c|`. -/
theorem bondy_locke [Fintype V] {G : SimpleGraph V} (hG : KConnected G 3) {L : List V}
    (hL : IsPathL G L) (h3 : 3 ≤ L.length) :
    ∃ c, IsCycleL G c ∧ 2 * (L.length - 1) + 8 ≤ 7 * c.length := by
  obtain ⟨u, hu⟩ : ∃ u, L.head? = some u := by
    cases L with
    | nil => simp at h3
    | cons a t => exact ⟨a, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, L.getLast? = some v := by
    cases h : L.getLast? with
    | none => simp at h; subst h; simp at h3
    | some v => exact ⟨v, rfl⟩
  by_cases hadj : G.Adj u v
  · refine ⟨L, ⟨hL, h3, fun a ha b hb => ?_⟩, by omega⟩
    rw [hu] at ha; rw [hv] at hb
    simp only [Option.mem_def, Option.some.injEq] at ha hb
    subst ha; subst hb
    exact hadj.symm
  · obtain ⟨Q, hQ⟩ := exists_threePaths hG hL h3 hu hv hadj
    obtain ⟨c, hc, hlen⟩ := BondyLocke.cycle_of_three_paths hQ
    exact ⟨c, hc, hlen⟩

/-- A finite `3`-connected graph contains a path on three vertices. -/
lemma exists_path_three [Fintype V] {G : SimpleGraph V} (hG : KConnected G 3) :
    ∃ L : List V, IsPathL G L ∧ L.length = 3 := by
  have hcard := hG.1
  have : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨u⟩ := this
  obtain ⟨w, hwu⟩ := Fintype.exists_ne_of_one_lt_card (by omega) u
  obtain ⟨-, hr⟩ := hG.2 ∅ (by simp) u w (by simp) (by simp)
  obtain ⟨x, hux⟩ : ∃ x, G.Adj u x := by
    rcases Relation.ReflTransGen.cases_head hr with h | ⟨x, hx, -⟩
    · exact absurd h hwu.symm
    · exact ⟨x, hx.1⟩
  obtain ⟨z, hz⟩ : ∃ z, z ∉ ({u, x} : Finset V) := by
    by_contra h
    push_neg at h
    have : (Finset.univ : Finset V) ⊆ {u, x} := fun z _ => h z
    have := Finset.card_le_card this
    rw [Finset.card_univ] at this
    have := Finset.card_le_two (a := u) (b := x)
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
  obtain ⟨-, hr'⟩ := hG.2 {u} (by simp) x z (by simpa using hux.ne') (by simpa using hz.1)
  obtain ⟨y, hxy, hyu⟩ : ∃ y, G.Adj x y ∧ y ≠ u := by
    rcases Relation.ReflTransGen.cases_head hr' with h | ⟨y, hy, -⟩
    · exact absurd h.symm hz.2
    · exact ⟨y, hy.1, by simpa using hy.2⟩
  refine ⟨[u, x, y], ⟨?_, ?_⟩, rfl⟩
  · exact List.IsChain.cons_cons hux (List.IsChain.cons_cons hxy (List.isChain_singleton _))
  · simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
      not_false_eq_true, List.nodup_nil, and_true]
    exact ⟨⟨hux.ne, hyu.symm⟩, hxy.ne⟩

/-- **Linear path-to-cycle bound** with `κ = 2/7`. -/
theorem pathToCycleLinear_two_sevenths : PathToCycleLinear (2 / 7) := by
  intro V _ G hG l hl
  by_cases h3 : 3 ≤ l.length
  · obtain ⟨c, hc, hlen⟩ := bondy_locke hG hl h3
    refine ⟨c, hc, ?_⟩
    have : ((2 * (l.length - 1) + 8 : ℕ) : ℝ) ≤ ((7 * c.length : ℕ) : ℝ) := by exact_mod_cast hlen
    push_cast [Nat.cast_sub (by omega : 1 ≤ l.length)] at this
    linarith
  · obtain ⟨L, hL, hL3⟩ := exists_path_three hG
    obtain ⟨c, hc, -⟩ := bondy_locke hG hL (by omega)
    refine ⟨c, hc, ?_⟩
    have h1 : (l.length : ℝ) ≤ 2 := by exact_mod_cast (by omega : l.length ≤ 2)
    have h2 : (3 : ℝ) ≤ c.length := by exact_mod_cast hc.2.1
    linarith

/-- The sub-polynomial path-to-cycle property holds. -/
theorem pathToCycleSubpoly_holds : PathToCycleSubpoly :=
  pathToCycleSubpoly_of_linear (by norm_num) pathToCycleLinear_two_sevenths

/-- **Long cycles in vertex-transitive graphs** (unconditional).  For every `ε > 0` there is
`n₀` such that every connected vertex-transitive graph of order `n ≥ n₀` contains a cycle of
length at least `n^(1-ε)`. -/
theorem vt_long_cycle :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (X : SimpleGraph V),
      X.Connected → VertexTransitive X → n₀ ≤ Fintype.card V →
      ∃ (v : V) (c : X.Walk v v), c.IsCycle ∧ (Fintype.card V : ℝ) ^ (1 - ε) ≤ c.length :=
  vt_long_cycle_of_pathToCycle pathToCycleSubpoly_holds

/-- **Long cycles in Cayley graphs** (unconditional).  For every `ε > 0` there is `n₀` such that
every connected Cayley graph of a finite group of order `n ≥ n₀` contains a cycle of length at
least `n^(1-ε)`. -/
theorem cayley_long_cycle :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (H : Type) [Group H] [Finite H] (S : Set H),
      (cay S).Connected → n₀ ≤ Nat.card H →
      ∃ (v : H) (c : (cay S).Walk v v), c.IsCycle ∧ (Nat.card H : ℝ) ^ (1 - ε) ≤ c.length :=
  cayley_long_cycle_of_pathToCycle pathToCycleSubpoly_holds

end Lovasz
