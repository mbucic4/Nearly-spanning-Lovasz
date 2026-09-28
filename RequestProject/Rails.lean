module
public import RequestProject.Cayley

/-!
# Rails with attachments (Definition 3.4)

An attachment from `t` to the path `P` (inside the vertex set `Z`) is a path in `Z` from `t`
to a vertex of `P` which meets `P` only at its last vertex (the one-vertex path `[t]` if `t`
lies on `P`).  `HasRail G Z T` says that `Z` contains a path `P` together with pairwise
vertex-disjoint attachments from all vertices of `T` to `P`.
-/

@[expose] public section


open Classical

namespace Lovasz

variable {V : Type*}

/-- `a` is an attachment from `t` to the path `P` inside `Z`. -/
def IsAttachment (G : SimpleGraph V) (Z : Set V) (P : List V) (t : V) (a : List V) : Prop :=
  IsPathL G a ∧ a.head? = some t ∧ (∃ x ∈ P, a.getLast? = some x) ∧ (∀ x ∈ a, x ∈ Z) ∧
    (∀ x ∈ a, x ∈ P → a.getLast? = some x)

/-- `P` is a path inside `Z` with pairwise vertex-disjoint attachments from all of `T`. -/
def IsRail (G : SimpleGraph V) (Z : Set V) (T : Finset V) (P : List V) : Prop :=
  IsPathL G P ∧ (∀ x ∈ P, x ∈ Z) ∧ ∃ att : V → List V, (∀ t ∈ T, IsAttachment G Z P t (att t)) ∧
    ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → (att t).Disjoint (att t')

/-- `Z` contains a path with pairwise vertex-disjoint attachments from all vertices of `T`. -/
def HasRail (G : SimpleGraph V) (Z : Set V) (T : Finset V) : Prop := ∃ P, IsRail G Z T P

/-- A rail has at least as many vertices as it has attachments. -/
lemma IsRail.card_le_length {G : SimpleGraph V} {Z : Set V} {T : Finset V} {P : List V}
    (h : IsRail G Z T P) : T.card ≤ P.length := by
  obtain ⟨hP, -, att, hatt, hdisj⟩ := h
  choose! e he hee using fun t ht => (hatt t ht).2.2.1
  have hinj : Set.InjOn e T := by
    intro t ht t' ht' htt'
    by_contra hne
    have h1 : e t ∈ att t := List.mem_of_getLast? (hee t ht)
    have h2 : e t' ∈ att t' := List.mem_of_getLast? (hee t' ht')
    exact hdisj t ht t' ht' hne h1 (htt' ▸ h2)
  calc T.card = (T.image e).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ P.toFinset.card := Finset.card_le_card (by
        intro x hx
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hx
        exact List.mem_toFinset.2 (he t ht))
    _ ≤ P.length := List.toFinset_card_le P

lemma HasRail.card_le_pathOrder [Finite V] {G : SimpleGraph V} {Z : Set V} {T : Finset V}
    (h : HasRail G Z T) : T.card ≤ pathOrder G := by
  obtain ⟨P, hP⟩ := h
  exact hP.card_le_length.trans hP.1.length_le_pathOrder

section Cayley

variable {H : Type*} [Group H] {S : Set H}

/-- Left translates of rails are rails. -/
lemma HasRail.map_mul_left {Z : Set H} {T : Finset H} (h : HasRail (cay S) Z T) (g : H) :
    HasRail (cay S) ((g * ·) '' Z) (T.image (g * ·)) := by
  obtain ⟨P, hP, hPZ, att, hatt, hdisj⟩ := h
  refine ⟨P.map (g * ·), hP.map_mul_left g, ?_, fun x => (att (g⁻¹ * x)).map (g * ·), ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact ⟨y, hPZ y hy, rfl⟩
  · intro t ht
    obtain ⟨t, ht0, rfl⟩ := Finset.mem_image.1 ht
    simp only [inv_mul_cancel_left]
    obtain ⟨h1, h2, ⟨x, hx, h3⟩, h4, h5⟩ := hatt t ht0
    refine ⟨h1.map_mul_left g, by simp [h2], ⟨g * x, List.mem_map_of_mem hx, ?_⟩, ?_, ?_⟩
    · simp [List.getLast?_map, h3]
    · intro y hy
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
      exact ⟨z, h4 z hz, rfl⟩
    · intro y hy hyP
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
      obtain ⟨z', hz', hzz'⟩ := List.mem_map.1 hyP
      have : z' = z := mul_left_cancel hzz'
      subst this
      simp [List.getLast?_map, h5 z' hz hz']
  · intro t ht t' ht' hne
    obtain ⟨t, ht0, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨t', ht0', rfl⟩ := Finset.mem_image.1 ht'
    simp only [inv_mul_cancel_left]
    have hne' : t ≠ t' := fun h => hne (by rw [h])
    intro y hy hy'
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    obtain ⟨z', hz', hzz'⟩ := List.mem_map.1 hy'
    have : z' = z := mul_left_cancel hzz'
    subst this
    exact hdisj t ht0 t' ht0' hne' hz hz'

end Cayley

end Lovasz
