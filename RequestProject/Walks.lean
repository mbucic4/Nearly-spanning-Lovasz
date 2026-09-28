module
public import RequestProject.Basic

/-!
# Walks, reachability inside sets, and list surgery
-/

@[expose] public section


open Classical

namespace Lovasz

variable {V : Type*} {G : SimpleGraph V} {s t : Set V} {u v w : V}

namespace ReachIn

lemma refl (hu : u ∈ s) : ReachIn G s u u := ⟨hu, Relation.ReflTransGen.refl⟩

lemma mem_left (h : ReachIn G s u v) : u ∈ s := h.1

lemma mem_right (h : ReachIn G s u v) : v ∈ s := by
  obtain ⟨hu, h⟩ := h
  induction h with
  | refl => exact hu
  | tail _ hbc _ => exact hbc.2

lemma tail (h : ReachIn G s u v) (hvw : G.Adj v w) (hw : w ∈ s) : ReachIn G s u w :=
  ⟨h.1, h.2.tail ⟨hvw, hw⟩⟩

lemma head (huv : G.Adj u v) (hu : u ∈ s) (h : ReachIn G s v w) : ReachIn G s u w :=
  ⟨hu, Relation.ReflTransGen.head ⟨huv, h.1⟩ h.2⟩

lemma trans (h₁ : ReachIn G s u v) (h₂ : ReachIn G s v w) : ReachIn G s u w :=
  ⟨h₁.1, h₁.2.trans h₂.2⟩

lemma symm (h : ReachIn G s u v) : ReachIn G s v u := by
  obtain ⟨hu, h⟩ := h
  induction h with
  | refl => exact refl hu
  | @tail b c hab hbc ih =>
    exact head hbc.1.symm hbc.2 ih

lemma mono {G' : SimpleGraph V} (hG : G ≤ G') (hst : s ⊆ t) (h : ReachIn G s u v) :
    ReachIn G' t u v := by
  obtain ⟨hu, h⟩ := h
  refine ⟨hst hu, ?_⟩
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail ⟨hG hbc.1, hst hbc.2⟩

/-- A set containing `u` and closed under steps inside `s` contains everything reachable. -/
lemma closed {Q : V → Prop} (hu : Q u)
    (hQ : ∀ a b, Q a → a ∈ s → b ∈ s → G.Adj a b → Q b) (h : ReachIn G s u v) : Q v := by
  obtain ⟨hus, h⟩ := h
  have key : Q v ∧ v ∈ s := by
    induction h with
    | refl => exact ⟨hu, hus⟩
    | tail _ hbc ih => exact ⟨hQ _ _ ih.1 ih.2 hbc.2 hbc.1, hbc.2⟩
  exact key.1

/-- Reachability can be restricted to the vertices reachable from the start. -/
lemma restrict (h : ReachIn G s u v) : ReachIn G (s ∩ {x | ReachIn G s u x}) u v := by
  have hu := h.1
  obtain ⟨_, h'⟩ := h
  refine ⟨⟨hu, refl hu⟩, ?_⟩
  induction h' with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hab hbc ih =>
    exact ih.tail ⟨hbc.1, hbc.2, ReachIn.tail (⟨hu, hab⟩ : ReachIn G s u b) hbc.1 hbc.2⟩

end ReachIn

lemma reachIn_univ_of_reachable (h : G.Reachable u v) : ReachIn G Set.univ u v := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  refine ⟨trivial, ?_⟩
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail ⟨hbc, trivial⟩

/-! ### Lists -/

lemma reachIn_of_chain {l : List V} (hl : l.IsChain G.Adj) (hs : ∀ x ∈ l, x ∈ s)
    (hu : l.head? = some u) (hv : l.getLast? = some v) : ReachIn G s u v := by
  induction l generalizing u with
  | nil => simp at hu
  | cons a l ih =>
    simp only [List.head?_cons, Option.some.injEq] at hu
    subst hu
    cases l with
    | nil =>
      simp at hv; subst hv; exact ReachIn.refl (hs _ (by simp))
    | cons b l =>
      rw [List.isChain_cons_cons] at hl
      have := ih hl.2 (fun x hx => hs x (List.mem_cons_of_mem _ hx)) rfl
        (by simpa [List.getLast?_cons_cons] using hv)
      exact ReachIn.head hl.1 (hs _ (by simp)) this

lemma WalkLe.reachIn {L : ℕ} (h : WalkLe G s u v L) : ReachIn G s u v := by
  obtain ⟨l, hl, hu, hv, hs, -⟩ := h
  exact reachIn_of_chain hl hs hu hv

/-- Every reachability inside `s` is witnessed by a path inside `s`. -/
lemma ReachIn.exists_path (h : ReachIn G s u v) :
    ∃ l : List V, IsPathL G l ∧ l.head? = some u ∧ l.getLast? = some v ∧ ∀ x ∈ l, x ∈ s := by
  obtain ⟨hu, h⟩ := h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[v], isPathL_singleton v, rfl, rfl, by simpa using hu⟩
  | @head a b hab _ ih =>
    obtain ⟨l, ⟨hc, hn⟩, hh, hl, hs⟩ := ih hab.2
    by_cases ha : a ∈ l
    · obtain ⟨l₁, l₂, rfl⟩ := List.mem_iff_append.1 ha
      refine ⟨a :: l₂, ⟨?_, ?_⟩, rfl, ?_, ?_⟩
      · exact (List.isChain_append.1 hc).2.1
      · exact (List.nodup_append.1 hn).2.1
      · simpa [List.getLast?_append] using hl
      · intro x hx; exact hs x (by simp at hx ⊢; tauto)
    · refine ⟨a :: l, ⟨?_, ?_⟩, rfl, ?_, ?_⟩
      · cases l with
        | nil => simp at hh
        | cons c l =>
          simp at hh; subst hh
          exact List.IsChain.cons_cons hab.1 hc
      · exact List.nodup_cons.2 ⟨ha, hn⟩
      · cases l with
        | nil => simp at hh
        | cons c l => simpa [List.getLast?_cons_cons] using hl
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hu
        · exact hs x hx

/-- Truncation of a list at the first vertex lying in a set `Q`. -/
lemma exists_prefix_first_mem {l : List V} (Q : Set V) (hl : ∃ x ∈ l, x ∈ Q) :
    ∃ l₁ l₂ : List V, ∃ q ∈ Q, l = l₁ ++ q :: l₂ ∧ ∀ x ∈ l₁, x ∉ Q := by
  induction l with
  | nil => simp at hl
  | cons a l ih =>
    by_cases ha : a ∈ Q
    · exact ⟨[], l, a, ha, rfl, by simp⟩
    · obtain ⟨x, hx, hxQ⟩ := hl
      have hx' : x ∈ l := by
        rcases List.mem_cons.1 hx with rfl | h
        · exact absurd hxQ ha
        · exact h
      obtain ⟨l₁, l₂, q, hq, rfl, h⟩ := ih ⟨x, hx', hxQ⟩
      refine ⟨a :: l₁, l₂, q, hq, rfl, ?_⟩
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact ha
      · exact h y hy

lemma IsPathL.prefix {l l' : List V} (h : IsPathL G l) (hp : l' <+: l) : IsPathL G l' :=
  ⟨h.1.prefix hp, h.2.sublist hp.sublist⟩

lemma IsPathL.suffix {l l' : List V} (h : IsPathL G l) (hp : l' <:+ l) : IsPathL G l' :=
  ⟨h.1.suffix hp, h.2.sublist hp.sublist⟩

lemma IsPathL.infix {l l' : List V} (h : IsPathL G l) (hp : l' <:+: l) : IsPathL G l' :=
  ⟨h.1.infix hp, h.2.sublist hp.sublist⟩

lemma IsPathL.reverse {l : List V} (h : IsPathL G l) : IsPathL G l.reverse :=
  ⟨List.isChain_reverse.2 (h.1.imp fun _ _ hab => hab.symm), List.nodup_reverse.2 h.2⟩

lemma IsPathL.mono {G' : SimpleGraph V} (hG : G ≤ G') {l : List V} (h : IsPathL G l) :
    IsPathL G' l :=
  ⟨h.1.imp fun _ _ hab => hG hab, h.2⟩

/-- A path which ends in `Q` can be truncated at its first vertex in `Q`. -/
lemma IsPathL.exists_trunc {l : List V} (h : IsPathL G l) {u : V} (hu : l.head? = some u)
    (Q : Set V) (hQ : ∃ x ∈ l, x ∈ Q) :
    ∃ l', IsPathL G l' ∧ l'.head? = some u ∧ (∃ q ∈ Q, l'.getLast? = some q) ∧
      (∀ x ∈ l', x ∈ l) ∧ (∀ x ∈ l', x ∈ Q → l'.getLast? = some x) := by
  obtain ⟨l₁, l₂, q, hq, rfl, hl₁⟩ := exists_prefix_first_mem Q hQ
  refine ⟨l₁ ++ [q], h.prefix ?_, ?_, ⟨q, hq, by simp⟩, ?_, ?_⟩
  · exact ⟨l₂, by simp⟩
  · cases l₁ with
    | nil => simpa using hu
    | cons a l₁ => simpa using hu
  · intro x hx; simp at hx ⊢; tauto
  · intro x hx hxQ
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact absurd hxQ (hl₁ x hx)
    · simp


/-! ### Walks of bounded length -/

namespace WalkLe

lemma refl (hu : u ∈ s) (L : ℕ) : WalkLe G s u u L :=
  ⟨[u], List.isChain_singleton u, rfl, rfl, by simpa using hu, by simp⟩

lemma mono_len {L L' : ℕ} (h : WalkLe G s u v L) (hL : L ≤ L') : WalkLe G s u v L' := by
  obtain ⟨l, h1, h2, h3, h4, h5⟩ := h
  exact ⟨l, h1, h2, h3, h4, by omega⟩

lemma mono_set (h : WalkLe G s u v L) (hst : s ⊆ t) : WalkLe G t u v L := by
  obtain ⟨l, h1, h2, h3, h4, h5⟩ := h
  exact ⟨l, h1, h2, h3, fun x hx => hst (h4 x hx), h5⟩

lemma mem_left {L : ℕ} (h : WalkLe G s u v L) : u ∈ s := by
  obtain ⟨l, h1, h2, h3, h4, h5⟩ := h
  exact h4 u (List.mem_of_head? h2)

lemma mem_right {L : ℕ} (h : WalkLe G s u v L) : v ∈ s := by
  obtain ⟨l, h1, h2, h3, h4, h5⟩ := h
  exact h4 v (List.mem_of_getLast? h3)

lemma trans {L₁ L₂ : ℕ} (h₁ : WalkLe G s u v L₁) (h₂ : WalkLe G s v w L₂) :
    WalkLe G s u w (L₁ + L₂) := by
  obtain ⟨l₁, a1, a2, a3, a4, a5⟩ := h₁
  obtain ⟨l₂, b1, b2, b3, b4, b5⟩ := h₂
  cases l₂ with
  | nil => simp at b2
  | cons x l₂ =>
    simp only [List.head?_cons, Option.some.injEq] at b2
    subst b2
    refine ⟨l₁ ++ l₂, ?_, ?_, ?_, ?_, ?_⟩
    · cases l₂ with
      | nil => simpa using a1
      | cons y l₂ =>
        rw [List.isChain_append]
        refine ⟨a1, (List.isChain_cons_cons.1 b1).2, ?_⟩
        intro a ha b hb
        rw [a3] at ha; simp at ha hb; subst ha; subst hb
        exact (List.isChain_cons_cons.1 b1).1
    · cases l₁ with
      | nil => simp at a2
      | cons y l₁ => simpa using a2
    · cases l₂ with
      | nil => simp at b3; simp [a3, b3]
      | cons y l₂ =>
        rw [List.getLast?_append]
        simp only [List.getLast?_cons_cons] at b3
        simp [b3]
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact a4 x hx
      · exact b4 x (List.mem_cons_of_mem _ hx)
    · simp at b5 ⊢; omega

lemma symm {L : ℕ} (h : WalkLe G s u v L) : WalkLe G s v u L := by
  obtain ⟨l, h1, h2, h3, h4, h5⟩ := h
  refine ⟨l.reverse, List.isChain_reverse.2 (h1.imp fun _ _ hab => hab.symm), ?_, ?_,
    fun x hx => h4 x (List.mem_reverse.1 hx), by simpa using h5⟩
  · simpa [List.head?_reverse] using h3
  · simpa [List.getLast?_reverse] using h2

lemma tail {L : ℕ} (h : WalkLe G s u v L) (hvw : G.Adj v w) (hw : w ∈ s) :
    WalkLe G s u w (L + 1) := by
  have : WalkLe G s v w 1 :=
    ⟨[v, w], List.IsChain.cons_cons hvw (List.isChain_singleton w), rfl, rfl,
      by simp [h.mem_right, hw], by simp⟩
  exact h.trans this

lemma of_eq_or_adj {L : ℕ} (h : WalkLe G s u v L) (hvw : v = w ∨ G.Adj v w) (hw : w ∈ s) :
    WalkLe G s u w (L + 1) := by
  rcases hvw with rfl | hvw
  · exact h.mono_len (Nat.le_succ L)
  · exact h.tail hvw hw

end WalkLe

end Lovasz
