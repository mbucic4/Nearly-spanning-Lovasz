module
public import RequestProject.Menger

/-!
# Cycles and vertex connectivity

Basic definitions for the cycle versions of the long-path theorems.

* `IsCycleL G l`: the list `l` is the cyclic vertex sequence of a cycle of `G` (at least three
  distinct vertices, consecutive entries adjacent, last entry adjacent to the first).  Such a
  cycle has `l.length` edges.
* `KConnected G k`: `G` has more than `k` vertices and deleting fewer than `k` vertices leaves
  the remaining graph connected.

We also convert list cycles to Mathlib's `SimpleGraph.Walk.IsCycle`, and prove the classical
fact that an end vertex of a longest path has all its neighbours on the path.
-/

@[expose] public section


open Classical

namespace Lovasz

variable {V : Type*}

/-- `l` is the cyclic vertex sequence of a cycle of `G`: a path with at least three vertices
whose last vertex is adjacent to its first.  The cycle has `l.length` edges. -/
def IsCycleL (G : SimpleGraph V) (l : List V) : Prop :=
  IsPathL G l ∧ 3 ≤ l.length ∧ ∀ a ∈ l.head?, ∀ b ∈ l.getLast?, G.Adj b a

/-- `G` is `k`-connected: it has more than `k` vertices, and deleting any set of fewer than
`k` vertices leaves a connected graph. -/
def KConnected [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧
    ∀ T : Finset V, T.card < k → ∀ u v, u ∉ T → v ∉ T → ReachIn G {w | w ∉ T} u v

variable {G : SimpleGraph V}

/-- A list path is the support of a Mathlib walk between its end vertices. -/
lemma exists_walk_support_eq :
    ∀ (l : List V) (a b : V), l.IsChain G.Adj → l.head? = some a → l.getLast? = some b →
      ∃ p : G.Walk a b, p.support = l
  | [], _, _, _, h, _ => by simp at h
  | [x], a, b, _, ha, hb => by
      simp at ha hb; subst ha; subst hb; exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | x :: y :: t, a, b, hc, ha, hb => by
      simp at ha; subst ha
      rw [List.isChain_cons_cons] at hc
      obtain ⟨p, hp⟩ := exists_walk_support_eq (y :: t) y b hc.2 rfl (by simpa using hb)
      exact ⟨SimpleGraph.Walk.cons hc.1 p, by simp [hp]⟩

/-- A path of length at least two does not contain the edge joining its end vertices. -/
lemma not_mem_edges_ends {a b : V} {p : G.Walk a b} (hp : p.IsPath) (h2 : 2 ≤ p.length) :
    s(b, a) ∉ p.edges := by
  cases p with
  | nil => simp at h2
  | cons h' q =>
    rename_i y
    rw [SimpleGraph.Walk.cons_isPath_iff] at hp
    intro he
    rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
    rcases he with he | he
    · have hab : a ≠ b := by
        rintro rfl
        exact hp.2 (SimpleGraph.Walk.end_mem_support q)
      have hyb : y = b := by
        rw [Sym2.eq_iff] at he
        rcases he with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact absurd h1.symm hab
        · exact h1.symm
      subst hyb
      have : q.length = 0 := by
        have := hp.1
        cases q with
        | nil => rfl
        | cons hq r =>
          exfalso
          rw [SimpleGraph.Walk.cons_isPath_iff] at this
          exact this.2 (SimpleGraph.Walk.end_mem_support r)
      simp [this] at h2
    · exact hp.2 (q.snd_mem_support_of_mem_edges he)

/-- A list cycle gives a Mathlib cycle of the same length. -/
lemma IsCycleL.exists_walk_isCycle {l : List V} (h : IsCycleL G l) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = l.length := by
  obtain ⟨⟨hc, hnd⟩, h3, hadj⟩ := h
  obtain ⟨a, t, rfl⟩ : ∃ a t, l = a :: t := by
    cases l with
    | nil => simp at h3
    | cons a t => exact ⟨a, t, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, (a :: t).getLast? = some b :=
    ⟨(a :: t).getLast (by simp), List.getLast?_eq_some_getLast (by simp)⟩
  have hab := hadj a (by simp) b (by simp [hb])
  obtain ⟨p, hp⟩ := exists_walk_support_eq (a :: t) a b hc rfl hb
  have hpath : p.IsPath := by
    rw [SimpleGraph.Walk.isPath_def, hp]; exact hnd
  have hlen : p.length + 1 = (a :: t).length := by
    rw [← hp, SimpleGraph.Walk.length_support]
  refine ⟨b, SimpleGraph.Walk.cons hab p, ?_, by simp at hlen ⊢; omega⟩
  rw [SimpleGraph.Walk.cons_isCycle_iff]
  refine ⟨hpath, fun he => ?_⟩
  -- the edge `ba` would join the two ends of the path, forcing length one
  have hlen2 : 2 ≤ p.length := by simp at hlen h3 ⊢; omega
  exact not_mem_edges_ends hpath hlen2 he

end Lovasz

namespace Lovasz

variable {V : Type*} {G : SimpleGraph V}

/-- A neighbour of the first vertex of a path of maximum length lies on the path. -/
lemma mem_of_adj_head_of_longest {a : V} {t : List V} (hl : IsPathL G (a :: t))
    (hmax : ∀ l', IsPathL G l' → l'.length ≤ (a :: t).length) {w : V} (hw : G.Adj a w) :
    w ∈ a :: t := by
  by_contra hwl
  have hp : IsPathL G (w :: a :: t) :=
    ⟨List.IsChain.cons_cons hw.symm hl.1, List.nodup_cons.2 ⟨hwl, hl.2⟩⟩
  have := hmax _ hp
  simp at this

/-- In a graph all of whose vertices have degree two, a path of maximum length with at least
three vertices closes up into a cycle. -/
lemma isCycleL_of_longest_of_degree_two [Fintype V] (hreg : ∀ v, G.degree v = 2) {l : List V}
    (hl : IsPathL G l) (hmax : ∀ l', IsPathL G l' → l'.length ≤ l.length) (h3 : 3 ≤ l.length) :
    IsCycleL G l := by
  obtain ⟨a, b, t, rfl⟩ : ∃ a b t, l = a :: b :: t := by
    match l, h3 with
    | a :: b :: t, _ => exact ⟨a, b, t, rfl⟩
  have hab : G.Adj a b := (List.isChain_cons_cons.1 hl.1).1
  -- a second neighbour `w` of `a`
  obtain ⟨w, hw, hwb⟩ : ∃ w, G.Adj a w ∧ w ≠ b := by
    have hc : ((G.neighborFinset a).erase b).card = 1 := by
      rw [Finset.card_erase_of_mem (by simpa using hab), SimpleGraph.card_neighborFinset_eq_degree,
        hreg]
    obtain ⟨w, hw⟩ := Finset.card_pos.1 (by omega : 0 < ((G.neighborFinset a).erase b).card)
    rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hw
    exact ⟨w, hw.2, hw.1⟩
  have hwl := mem_of_adj_head_of_longest hl hmax hw
  have hwa : w ≠ a := fun h => G.loopless.irrefl a (h ▸ hw)
  have hwt : w ∈ t := by
    simp only [List.mem_cons] at hwl
    rcases hwl with h | h | h
    · exact absurd h hwa
    · exact absurd h hwb
    · exact h
  obtain ⟨t1, t2, rfl⟩ := List.mem_iff_append.1 hwt
  refine ⟨hl, h3, ?_⟩
  cases t2 with
  | nil =>
    intro a' ha' b' hb'
    have hlast : (b :: (t1 ++ [w])).getLast? = some w := by
      rw [← List.cons_append, List.getLast?_concat]
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq, List.getLast?_cons_cons] at ha' hb'
    rw [hlast, Option.some.injEq] at hb'
    subst ha'; subst hb'
    exact hw.symm
  | cons z t2 =>
    exfalso
    have hch := hl.1
    have hnd := hl.2
    rw [show a :: b :: (t1 ++ w :: z :: t2) = (a :: b :: t1) ++ w :: z :: t2 by simp] at hch hnd
    rw [List.isChain_append_cons_cons] at hch
    obtain ⟨h1, hwz, -⟩ := hch
    set y := (a :: b :: t1).getLast (by simp) with hy
    have hyw : G.Adj y w := by
      rw [List.isChain_append] at h1
      exact h1.2.2 y (by simp [hy, List.getLast?_eq_some_getLast]) w (by simp)
    have hymem : y ∈ b :: t1 := by
      rw [hy, List.getLast_cons (by simp)]; exact List.getLast_mem _
    rw [List.nodup_append] at hnd
    obtain ⟨hnd1, hnd2, hdisj⟩ := hnd
    have hya : y ≠ a := by
      intro h; rw [h] at hymem
      exact (List.nodup_cons.1 hnd1).1 hymem
    have hza : z ≠ a := fun h => hdisj a (by simp) z (by simp) h.symm
    have hyz : y ≠ z := fun h => hdisj y (by simp [hymem]) z (by simp) h
    have hsub : ({y, z, a} : Finset V) ⊆ G.neighborFinset w := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [SimpleGraph.mem_neighborFinset]
      rcases hx with rfl | rfl | rfl
      · exact hyw.symm
      · exact hwz
      · exact hw.symm
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simp [hyz, hya]),
      Finset.card_insert_of_notMem (by simp [hza]), Finset.card_singleton,
      SimpleGraph.card_neighborFinset_eq_degree, hreg] at hcard
    omega

end Lovasz
