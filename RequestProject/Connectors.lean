module
public import RequestProject.Rails

/-!
# Gluing paths, and connectors between two rails

`l₁ ++ l₂.tail` glues a list ending at `x` to a list starting at `x`.  Gluing the reversed
attachment at one rail, a connecting path, and the attachment at the other rail gives the
connectors used in Lemma 3.1.
-/

@[expose] public section


open Classical

namespace Lovasz

variable {V : Type*} {G : SimpleGraph V}

lemma eq_cons_of_head? {l : List V} {x : V} (h : l.head? = some x) : ∃ t, l = x :: t := by
  cases l with
  | nil => simp at h
  | cons a t => simp at h; exact ⟨t, by rw [h]⟩

lemma glue_chain {l1 l2 : List V} {x : V} (h1 : l1.IsChain G.Adj) (h2 : l2.IsChain G.Adj)
    (hl1 : l1.getLast? = some x) (hl2 : l2.head? = some x) :
    (l1 ++ l2.tail).IsChain G.Adj := by
  obtain ⟨t, rfl⟩ := eq_cons_of_head? hl2
  rw [List.isChain_append]
  refine ⟨h1, (List.isChain_cons.1 h2).2, ?_⟩
  intro a ha b hb
  rw [hl1, Option.mem_def, Option.some.injEq] at ha
  subst ha
  exact (List.isChain_cons.1 h2).1 b hb

lemma glue_nodup {l1 l2 : List V} {x : V} (h1 : l1.Nodup) (h2 : l2.Nodup)
    (hl2 : l2.head? = some x) (hcap : ∀ y ∈ l1, y ∈ l2 → y = x) :
    (l1 ++ l2.tail).Nodup := by
  obtain ⟨t, rfl⟩ := eq_cons_of_head? hl2
  rw [List.nodup_append]
  refine ⟨h1, (List.nodup_cons.1 h2).2, ?_⟩
  intro a ha b hb hab
  subst hab
  have := hcap a ha (List.mem_cons_of_mem _ hb)
  subst this
  exact (List.nodup_cons.1 h2).1 hb

lemma glue_mem {l1 l2 : List V} {y : V} (h : y ∈ l1 ++ l2.tail) : y ∈ l1 ∨ y ∈ l2 := by
  rcases List.mem_append.1 h with h | h
  · exact Or.inl h
  · exact Or.inr (List.mem_of_mem_tail h)

lemma glue_head {l1 l2 : List V} {x : V} (hl1 : l1.getLast? = some x) :
    (l1 ++ l2.tail).head? = l1.head? := by
  cases l1 with
  | nil => simp at hl1
  | cons a t => simp

lemma glue_getLast {l1 l2 : List V} {x : V} (hl1 : l1.getLast? = some x)
    (hl2 : l2.head? = some x) : (l1 ++ l2.tail).getLast? = l2.getLast? := by
  obtain ⟨t, rfl⟩ := eq_cons_of_head? hl2
  cases t with
  | nil => simpa using hl1
  | cons b t =>
    rw [List.tail_cons, List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _),
      List.getLast?_cons_cons]

lemma glue_length {l1 l2 : List V} {x : V} (hl1 : l1.getLast? = some x)
    (hl2 : l2.head? = some x) : l2.length ≤ (l1 ++ l2.tail).length := by
  obtain ⟨t, rfl⟩ := eq_cons_of_head? hl2
  cases l1 with
  | nil => simp at hl1
  | cons a t' => simp

/-- Connectors between two rails, obtained by gluing the (reversed) attachment at the first
rail, a connecting path, and the attachment at the second rail. -/
lemma connectors {ι : Type*} (Z0 Z1 : Set V) (hZ : Disjoint Z0 Z1) (P0 P1 : List V)
    (hP0 : ∀ x ∈ P0, x ∈ Z0) (hP1 : ∀ x ∈ P1, x ∈ Z1)
    (s e : ι → V) (a0 a1 lift : ι → List V)
    (ha0 : ∀ i, IsAttachment G Z0 P0 (s i) (a0 i)) (ha1 : ∀ i, IsAttachment G Z1 P1 (e i) (a1 i))
    (hlift : ∀ i, IsPathL G (lift i)) (hlh : ∀ i, (lift i).head? = some (s i))
    (hll : ∀ i, (lift i).getLast? = some (e i))
    (hl0 : ∀ i, ∀ y ∈ lift i, y ∈ Z0 → y = s i) (hl1 : ∀ i, ∀ y ∈ lift i, y ∈ Z1 → y = e i)
    (hd0 : ∀ i j, i ≠ j → (a0 i).Disjoint (a0 j)) (hd1 : ∀ i j, i ≠ j → (a1 i).Disjoint (a1 j))
    (hdl : ∀ i j, i ≠ j → (lift i).Disjoint (lift j)) :
    ∃ C : ι → List V, (∀ i, IsPathL G (C i)) ∧ (∀ i, ∃ x ∈ P0, (C i).head? = some x) ∧
      (∀ i, ∃ y ∈ P1, (C i).getLast? = some y) ∧ (∀ i j, i ≠ j → (C i).Disjoint (C j)) ∧
      (∀ i, ∀ x ∈ C i, x ∈ P0 → (C i).head? = some x) ∧
      (∀ i, ∀ x ∈ C i, x ∈ P1 → (C i).getLast? = some x) ∧
      (∀ i, (lift i).length ≤ (C i).length) := by
  have hZ' : ∀ y, y ∈ Z0 → y ∉ Z1 := fun y h0 h1 => Set.disjoint_left.1 hZ h0 h1
  -- basic facts on the pieces
  have hr_last : ∀ i, (a0 i).reverse.getLast? = some (s i) := by
    intro i; rw [List.getLast?_reverse]; exact (ha0 i).2.1
  have hs0 : ∀ i, s i ∈ a0 i := fun i => List.mem_of_head? (ha0 i).2.1
  have he1 : ∀ i, e i ∈ a1 i := fun i => List.mem_of_head? (ha1 i).2.1
  let D : ι → List V := fun i => (a0 i).reverse ++ (lift i).tail
  have hD_last : ∀ i, (D i).getLast? = some (e i) := by
    intro i; rw [glue_getLast (hr_last i) (hlh i)]; exact hll i
  have hD_mem : ∀ i y, y ∈ D i → y ∈ a0 i ∨ y ∈ lift i := by
    intro i y hy
    rcases glue_mem hy with h | h
    · exact Or.inl (List.mem_reverse.1 h)
    · exact Or.inr h
  let C : ι → List V := fun i => D i ++ (a1 i).tail
  have hC_mem : ∀ i y, y ∈ C i → y ∈ a0 i ∨ y ∈ lift i ∨ y ∈ a1 i := by
    intro i y hy
    rcases glue_mem hy with h | h
    · rcases hD_mem i y h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hC_head : ∀ i, (C i).head? = (a0 i).getLast? := by
    intro i
    rw [glue_head (hD_last i), glue_head (hr_last i), List.head?_reverse]
  have hC_last : ∀ i, (C i).getLast? = (a1 i).getLast? := fun i =>
    glue_getLast (hD_last i) (ha1 i).2.1
  -- in `Z0` only on the first attachment, in `Z1` only on the last
  have hC_Z0 : ∀ i y, y ∈ C i → y ∈ Z0 → y ∈ a0 i := by
    intro i y hy hy0
    rcases hC_mem i y hy with h | h | h
    · exact h
    · rw [hl0 i y h hy0]; exact hs0 i
    · exact absurd ((ha1 i).2.2.2.1 y h) (hZ' y hy0)
  have hC_Z1 : ∀ i y, y ∈ C i → y ∈ Z1 → y ∈ a1 i := by
    intro i y hy hy1
    rcases hC_mem i y hy with h | h | h
    · exact absurd hy1 (hZ' y ((ha0 i).2.2.2.1 y h))
    · rw [hl1 i y h hy1]; exact he1 i
    · exact h
  refine ⟨C, fun i => ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact glue_chain (glue_chain (List.isChain_reverse.2 ((ha0 i).1.1.imp fun _ _ h => h.symm))
      (hlift i).1 (hr_last i) (hlh i)) (ha1 i).1.1 (hD_last i) (ha1 i).2.1
  · refine glue_nodup (glue_nodup (List.nodup_reverse.2 (ha0 i).1.2) (hlift i).2 (hlh i) ?_)
      (ha1 i).1.2 (ha1 i).2.1 ?_
    · intro y hy hyl
      exact hl0 i y hyl ((ha0 i).2.2.2.1 y (List.mem_reverse.1 hy))
    · intro y hy hya
      rcases hD_mem i y hy with h | h
      · exact absurd ((ha1 i).2.2.2.1 y hya) (hZ' y ((ha0 i).2.2.2.1 y h))
      · exact hl1 i y h ((ha1 i).2.2.2.1 y hya)
  · intro i
    obtain ⟨x, hx, hxl⟩ := (ha0 i).2.2.1
    exact ⟨x, hx, by rw [hC_head, hxl]⟩
  · intro i
    obtain ⟨x, hx, hxl⟩ := (ha1 i).2.2.1
    exact ⟨x, hx, by rw [hC_last, hxl]⟩
  · intro i j hij y hyi hyj
    rcases hC_mem i y hyi with h | h | h
    · have hy0 := (ha0 i).2.2.2.1 y h
      exact hd0 i j hij h (hC_Z0 j y hyj hy0)
    · rcases hC_mem j y hyj with h' | h' | h'
      · have hy0 := (ha0 j).2.2.2.1 y h'
        exact hd0 i j hij (hC_Z0 i y hyi hy0) h'
      · exact hdl i j hij h h'
      · have hy1 := (ha1 j).2.2.2.1 y h'
        exact hd1 i j hij (hC_Z1 i y hyi hy1) h'
    · have hy1 := (ha1 i).2.2.2.1 y h
      exact hd1 i j hij h (hC_Z1 j y hyj hy1)
  · intro i x hx hxP
    rw [hC_head]
    exact (ha0 i).2.2.2.2 x (hC_Z0 i x hx (hP0 x hxP)) hxP
  · intro i x hx hxP
    rw [hC_last]
    exact (ha1 i).2.2.2.2 x (hC_Z1 i x hx (hP1 x hxP)) hxP
  · intro i
    refine (glue_length (hr_last i) (hlh i)).trans ?_
    show (D i).length ≤ (D i ++ (a1 i).tail).length
    exact (List.sublist_append_left _ _).length_le

end Lovasz
