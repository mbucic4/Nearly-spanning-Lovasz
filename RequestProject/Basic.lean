module
public import Mathlib

/-!
# Basic path infrastructure

Paths are represented by their vertex lists: a list `l` is a path in `G` if consecutive
entries are adjacent and the entries are pairwise distinct.  `pathOrder G` is `p(G)`, the
maximum number of vertices of a path in `G`.
-/

@[expose] public section

open Classical

namespace Lovasz

variable {V : Type*}

/-- A path in `G`, given by its vertex list. -/
def IsPathL (G : SimpleGraph V) (l : List V) : Prop := l.IsChain G.Adj ∧ l.Nodup

/-- `p(G)`: the maximum number of vertices of a path in `G`. -/
noncomputable def pathOrder (G : SimpleGraph V) : ℕ :=
  sSup {n | ∃ l, IsPathL G l ∧ l.length = n}

/-- Reachability inside a vertex set `s`: there is a walk from `u` to `v` all of whose
vertices lie in `s`. -/
def ReachIn (G : SimpleGraph V) (s : Set V) (u v : V) : Prop :=
  u ∈ s ∧ Relation.ReflTransGen (fun a b => G.Adj a b ∧ b ∈ s) u v

/-- There is a walk from `u` to `v` inside `s` with at most `L` edges. -/
def WalkLe (G : SimpleGraph V) (s : Set V) (u v : V) (L : ℕ) : Prop :=
  ∃ l : List V, l.IsChain G.Adj ∧ l.head? = some u ∧ l.getLast? = some v ∧
    (∀ x ∈ l, x ∈ s) ∧ l.length ≤ L + 1

section pathOrder

variable {G : SimpleGraph V}

lemma pathOrder_set_bdd [Finite V] :
    BddAbove {n | ∃ l, IsPathL G l ∧ l.length = n} := by
  have := Fintype.ofFinite V
  refine ⟨Fintype.card V, ?_⟩
  rintro n ⟨l, hl, rfl⟩
  exact hl.2.length_le_card

lemma IsPathL.length_le_pathOrder [Finite V] {l : List V} (h : IsPathL G l) :
    l.length ≤ pathOrder G :=
  le_csSup pathOrder_set_bdd ⟨l, h, rfl⟩

lemma exists_isPathL_length_eq_pathOrder [Finite V] (G : SimpleGraph V) :
    ∃ l, IsPathL G l ∧ l.length = pathOrder G := by
  have hne : ({n | ∃ l, IsPathL G l ∧ l.length = n} : Set ℕ).Nonempty :=
    ⟨0, [], ⟨List.isChain_nil, List.nodup_nil⟩, rfl⟩
  exact Nat.sSup_mem hne pathOrder_set_bdd

lemma isPathL_singleton (v : V) : IsPathL G [v] := ⟨List.isChain_singleton v, List.nodup_singleton v⟩

lemma one_le_pathOrder [Finite V] [Nonempty V] (G : SimpleGraph V) : 1 ≤ pathOrder G :=
  (isPathL_singleton (G := G) (Classical.arbitrary V)).length_le_pathOrder

lemma pathOrder_le_card [Fintype V] (G : SimpleGraph V) : pathOrder G ≤ Fintype.card V := by
  obtain ⟨l, hl, h⟩ := exists_isPathL_length_eq_pathOrder G
  rw [← h]; exact hl.2.length_le_card

end pathOrder

end Lovasz
