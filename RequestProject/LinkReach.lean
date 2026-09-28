module
public import RequestProject.Expander
public import RequestProject.Walks

/-!
# Balls through a set of allowed vertices

`reach G A d S` is the set of vertices that can be reached from the seed set `S` by a walk of
length at most `d` all of whose vertices after the first lie in the set `A` of allowed vertices.
In the proof of Lemma 2.4, `A` is the random set `R` with a forbidden set `Z` removed.
-/

@[expose] public section


open scoped BigOperators
open Classical

namespace Lovasz

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

/-- Vertices reachable from `S` in at most `d` steps through the allowed set `A`. -/
def reach (A : Finset V) : ℕ → Finset V → Finset V
  | 0, S => S
  | d + 1, S => reach A d S ∪ A.filter (fun v => ∃ u ∈ reach A d S, G.Adj u v)

variable {G}

lemma subset_reach (A : Finset V) (S : Finset V) : ∀ d, S ⊆ reach G A d S
  | 0 => Finset.Subset.refl _
  | d + 1 => (subset_reach A S d).trans Finset.subset_union_left

lemma reach_mono_d (A S : Finset V) {d d' : ℕ} (h : d ≤ d') : reach G A d S ⊆ reach G A d' S := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step _ ih => exact ih.trans Finset.subset_union_left

lemma reach_mono {A A' S S' : Finset V} (hA : A ⊆ A') (hS : S ⊆ S') :
    ∀ d, reach G A d S ⊆ reach G A' d S'
  | 0 => hS
  | d + 1 => by
    simp only [reach]
    refine Finset.union_subset_union (reach_mono hA hS d) fun v hv => ?_
    obtain ⟨hvA, u, hu, huv⟩ := Finset.mem_filter.1 hv
    exact Finset.mem_filter.2 ⟨hA hvA, u, reach_mono hA hS d hu, huv⟩

lemma reach_union (A S S' : Finset V) : ∀ d, reach G A d (S ∪ S') = reach G A d S ∪ reach G A d S'
  | 0 => rfl
  | d + 1 => by
    simp only [reach, reach_union A S S' d]
    ext v
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ((h | h) | ⟨hA, u, hu | hu, huv⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl (Or.inr ⟨hA, u, hu, huv⟩)
      · exact Or.inr (Or.inr ⟨hA, u, hu, huv⟩)
    · rintro ((h | ⟨hA, u, hu, huv⟩) | (h | ⟨hA, u, hu, huv⟩))
      · exact Or.inl (Or.inl h)
      · exact Or.inr ⟨hA, u, Or.inl hu, huv⟩
      · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨hA, u, Or.inr hu, huv⟩

lemma reach_trans (A S T : Finset V) {a : ℕ} (hT : T ⊆ reach G A a S) :
    ∀ b, reach G A b T ⊆ reach G A (a + b) S
  | 0 => hT
  | b + 1 => by
    simp only [reach]
    refine Finset.union_subset_union (reach_trans A S T hT b) fun v hv => ?_
    obtain ⟨hvA, u, hu, huv⟩ := Finset.mem_filter.1 hv
    exact Finset.mem_filter.2 ⟨hvA, u, reach_trans A S T hT b hu, huv⟩

lemma nbr_subset_reach_one (A S : Finset V) :
    A.filter (fun v => ∃ u ∈ S, G.Adj u v) ⊆ reach G A 1 S :=
  Finset.subset_union_right

lemma reach_sub (A S : Finset V) : ∀ d, reach G A d S ⊆ S ∪ A
  | 0 => Finset.subset_union_left
  | d + 1 => by
    simp only [reach]
    exact Finset.union_subset (reach_sub A S d) (fun v hv =>
      Finset.mem_union_right _ (Finset.mem_filter.1 hv).1)

/-- Every vertex of `reach G A d S` is the end of a short walk from a seed through `A`. -/
lemma walkLe_of_mem_reach (A S : Finset V) : ∀ d, ∀ v ∈ reach G A d S,
    ∃ s ∈ S, WalkLe G (insert s (A : Set V)) s v d
  | 0, v, hv => ⟨v, hv, WalkLe.refl (Set.mem_insert _ _) 0⟩
  | d + 1, v, hv => by
    simp only [reach, Finset.mem_union, Finset.mem_filter] at hv
    rcases hv with hv | ⟨hvA, u, hu, huv⟩
    · obtain ⟨s, hs, hw⟩ := walkLe_of_mem_reach A S d v hv
      exact ⟨s, hs, hw.mono_len (Nat.le_succ d)⟩
    · obtain ⟨s, hs, hw⟩ := walkLe_of_mem_reach A S d u hu
      exact ⟨s, hs, hw.tail huv (Set.mem_insert_of_mem _ hvA)⟩

/-- Two balls through `A` that meet inside `A` yield a path whose internal vertices lie in `A`. -/
lemma exists_path_of_reach {A : Finset V} {x y v : V} {d : ℕ} (hx : v ∈ reach G A d {x})
    (hy : v ∈ reach G A d {y}) :
    ∃ P : List V, IsPathL G P ∧ P.head? = some x ∧ P.getLast? = some y ∧
      (∀ w ∈ P, w = x ∨ w = y ∨ w ∈ A) ∧ P.length ≤ 2 * d + 1 := by
  obtain ⟨s, hs, hws⟩ := walkLe_of_mem_reach A {x} d v hx
  obtain ⟨s', hs', hws'⟩ := walkLe_of_mem_reach A {y} d v hy
  rw [Finset.mem_singleton] at hs hs'
  subst hs hs'
  set T : Set V := insert s (insert s' (A : Set V))
  have h1 : WalkLe G T s v d := hws.mono_set (by
    intro w hw; rcases hw with rfl | hw
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hw))
  have h2 : WalkLe G T s' v d := hws'.mono_set (by
    intro w hw; rcases hw with rfl | hw
    · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hw))
  obtain ⟨l, hl1, hl2, hl3, hl4, hl5⟩ := h1.trans h2.symm
  have hr : ReachIn G {w | w ∈ l} s s' := reachIn_of_chain hl1 (fun w hw => hw) hl2 hl3
  obtain ⟨P, hP, hP1, hP2, hP3⟩ := hr.exists_path
  refine ⟨P, hP, hP1, hP2, fun w hw => ?_, ?_⟩
  · have := hl4 w (hP3 w hw)
    rcases this with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · have hsub : P.toFinset ⊆ l.toFinset := fun w hw => by
      simp only [List.mem_toFinset] at hw ⊢; exact hP3 w hw
    have := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hP.2] at this
    have := List.toFinset_card_le l
    omega

end

end Lovasz
