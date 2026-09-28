module
public import RequestProject.CycleBasic
public import RequestProject.VTMain

/-!
# Watkins' theorem (the part needed for cycles)

A finite connected vertex-transitive graph in which every vertex has degree at least `3` is
`3`-connected.  This is the consequence of Watkins' bound `κ ≥ 2(d+1)/3` used in the paper.

The proof is the classical atom argument.  For a vertex set `Y` let `bd Y` be its outer
boundary and `out Y` the vertices neither in `Y` nor in `bd Y`.  Let `κ` be the least size of a
boundary `bd Y` with `Y` and `out Y` nonempty; a *fragment* is such a `Y` with `|bd Y| = κ`, and
an *atom* is a fragment of least size.  Two atoms are equal or disjoint, and an atom meeting the
boundary of another atom lies inside that boundary.  By vertex-transitivity every vertex lies in
an atom, which forces `2|A| ≤ κ` for an atom `A`, and then `d ≤ |A| - 1 + κ` contradicts
`κ ≤ 2 < d`.
-/

@[expose] public section


open Classical

namespace Lovasz
namespace Watkins

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- The outer vertex boundary of `Y`. -/
noncomputable def bd (Y : Finset V) : Finset V :=
  Finset.univ.filter (fun w => w ∉ Y ∧ ∃ y ∈ Y, G.Adj y w)

/-- The vertices neither in `Y` nor on its boundary. -/
noncomputable def out (Y : Finset V) : Finset V :=
  Finset.univ.filter (fun w => w ∉ Y ∧ w ∉ bd G Y)

/-- `Y` and `out Y` are both nonempty, so `bd Y` separates. -/
def Sep (Y : Finset V) : Prop := Y.Nonempty ∧ (out G Y).Nonempty

variable {G}

lemma mem_bd {Y : Finset V} {w : V} : w ∈ bd G Y ↔ w ∉ Y ∧ ∃ y ∈ Y, G.Adj y w := by
  simp [bd]

lemma mem_out {Y : Finset V} {w : V} : w ∈ out G Y ↔ w ∉ Y ∧ w ∉ bd G Y := by
  simp [out]

lemma not_adj_out {Y : Finset V} {y z : V} (hy : y ∈ Y) (hz : z ∈ out G Y) : ¬ G.Adj y z :=
  fun h => (mem_out.1 hz).2 (mem_bd.2 ⟨(mem_out.1 hz).1, y, hy, h⟩)

lemma mem_or_mem_bd_of_adj {Y : Finset V} {y w : V} (hy : y ∈ Y) (h : G.Adj y w) :
    w ∈ Y ∨ w ∈ bd G Y := by
  by_cases hw : w ∈ Y
  · exact Or.inl hw
  · exact Or.inr (mem_bd.2 ⟨hw, y, hy, h⟩)

lemma not_mem_bd_of_mem {Y : Finset V} {w : V} (hw : w ∈ Y) : w ∉ bd G Y :=
  fun h => (mem_bd.1 h).1 hw

lemma mem_bd_of_not {Y : Finset V} {w : V} (h1 : w ∉ Y) (h2 : w ∉ out G Y) : w ∈ bd G Y := by
  by_contra h3; exact h2 (mem_out.2 ⟨h1, h3⟩)

lemma bd_out_subset (Y : Finset V) : bd G (out G Y) ⊆ bd G Y := by
  intro w hw
  obtain ⟨hw1, z, hz, hzw⟩ := mem_bd.1 hw
  have hwY : w ∉ Y := fun h => not_adj_out h hz hzw.symm
  exact mem_bd_of_not hwY hw1

lemma subset_out_out (Y : Finset V) : Y ⊆ out G (out G Y) := by
  intro y hy
  refine mem_out.2 ⟨fun h => (mem_out.1 h).1 hy, fun h => ?_⟩
  obtain ⟨-, z, hz, hzy⟩ := mem_bd.1 h
  exact not_adj_out hy hz hzy.symm

/-- Counting through indicator sums. -/
lemma card_add_card_le {A B C D : Finset V}
    (h : ∀ w, (if w ∈ A then 1 else 0) + (if w ∈ B then 1 else 0) ≤
      (if w ∈ C then 1 else 0) + (if w ∈ D then (1 : ℕ) else 0)) :
    A.card + B.card ≤ C.card + D.card := by
  have key : ∀ S : Finset V, S.card = ∑ w, if w ∈ S then 1 else 0 := by
    intro S; rw [Finset.sum_boole]; simp
  rw [key A, key B, key C, key D, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun w _ => h w)

lemma card_add_card_add_card_le {A B E C D : Finset V}
    (h : ∀ w, (if w ∈ A then 1 else 0) + (if w ∈ B then 1 else 0) + (if w ∈ E then 1 else 0) ≤
      (if w ∈ C then 1 else 0) + (if w ∈ D then (1 : ℕ) else 0)) :
    A.card + B.card + E.card ≤ C.card + D.card := by
  have key : ∀ S : Finset V, S.card = ∑ w, if w ∈ S then 1 else 0 := by
    intro S; rw [Finset.sum_boole]; simp
  rw [key A, key B, key E, key C, key D, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun w _ => h w)

section Atoms

variable (κ : ℕ)

/-- A fragment: a separating set whose boundary has the least possible size `κ`. -/
def Frag (Y : Finset V) : Prop := Sep G Y ∧ (bd G Y).card = κ

/-- An atom: a fragment of least cardinality. -/
def IsAtom (A : Finset V) : Prop := Frag (G := G) κ A ∧ ∀ F, Frag (G := G) κ F → A.card ≤ F.card

variable {κ} (hκ : ∀ Y : Finset V, Sep G Y → κ ≤ (bd G Y).card)
include hκ

lemma frag_out {Y : Finset V} (hY : Frag (G := G) κ Y) :
    Frag (G := G) κ (out G Y) ∧ bd G (out G Y) = bd G Y ∧ out G (out G Y) = Y := by
  obtain ⟨⟨hne, hout⟩, hcard⟩ := hY
  have hsep : Sep G (out G Y) := by
    obtain ⟨y, hy⟩ := hne
    exact ⟨hout, y, subset_out_out Y hy⟩
  have hbd : bd G (out G Y) = bd G Y := by
    apply Finset.eq_of_subset_of_card_le (bd_out_subset Y)
    rw [hcard]; exact hκ _ hsep
  refine ⟨⟨hsep, by rw [hbd, hcard]⟩, hbd, ?_⟩
  ext w
  constructor
  · intro hw
    obtain ⟨h1, h2⟩ := mem_out.1 hw
    rw [hbd] at h2
    by_contra hwY
    exact h1 (mem_out.2 ⟨hwY, h2⟩)
  · intro hw; exact subset_out_out Y hw

/-- Submodularity step: an atom meeting a fragment, whose outer parts also meet, lies in it. -/
lemma atom_subset_of_meet {X F : Finset V} (hX : IsAtom (G := G) κ X) (hF : Frag (G := G) κ F)
    (h1 : (X ∩ F).Nonempty) (h2 : (out G X ∩ out G F).Nonempty) : X ⊆ F := by
  set Y1 := X ∩ F
  set Y2 := out G X ∩ out G F
  have hsep1 : Sep G Y1 := by
    refine ⟨h1, ?_⟩
    obtain ⟨z, hz⟩ := h2
    rw [Finset.mem_inter] at hz
    refine ⟨z, mem_out.2 ⟨fun h => (mem_out.1 hz.1).1 (Finset.mem_inter.1 h).1, fun h => ?_⟩⟩
    obtain ⟨-, y, hy, hyz⟩ := mem_bd.1 h
    exact not_adj_out (Finset.mem_inter.1 hy).1 hz.1 hyz
  have hsep2 : Sep G Y2 := by
    refine ⟨h2, ?_⟩
    obtain ⟨z, hz⟩ := h1
    rw [Finset.mem_inter] at hz
    refine ⟨z, mem_out.2 ⟨fun h => (mem_out.1 (Finset.mem_inter.1 h).1).1 hz.1, fun h => ?_⟩⟩
    obtain ⟨-, y, hy, hyz⟩ := mem_bd.1 h
    exact not_adj_out hz.1 (Finset.mem_inter.1 hy).1 hyz.symm
  have hcount : (bd G Y1).card + (bd G Y2).card ≤ (bd G X).card + (bd G F).card := by
    apply card_add_card_le
    intro w
    have fa : w ∈ bd G Y1 → (w ∈ bd G X ∨ w ∈ bd G F) ∧ w ∉ out G X ∧ w ∉ out G F := by
      intro hw
      obtain ⟨hw1, y, hy, hyw⟩ := mem_bd.1 hw
      rw [Finset.mem_inter] at hy
      have o1 : w ∉ out G X := fun h => not_adj_out hy.1 h hyw
      have o2 : w ∉ out G F := fun h => not_adj_out hy.2 h hyw
      refine ⟨?_, o1, o2⟩
      by_contra hc
      push_neg at hc
      rcases mem_or_mem_bd_of_adj hy.1 hyw with hx | hx
      · rcases mem_or_mem_bd_of_adj hy.2 hyw with hf | hf
        · exact hw1 (Finset.mem_inter.2 ⟨hx, hf⟩)
        · exact hc.2 hf
      · exact hc.1 hx
    have fb : w ∈ bd G Y2 → (w ∈ bd G X ∨ w ∈ bd G F) ∧ w ∉ X ∧ w ∉ F := by
      intro hw
      obtain ⟨hw1, y, hy, hyw⟩ := mem_bd.1 hw
      rw [Finset.mem_inter] at hy
      have o1 : w ∉ X := fun h => not_adj_out h hy.1 hyw.symm
      have o2 : w ∉ F := fun h => not_adj_out h hy.2 hyw.symm
      refine ⟨?_, o1, o2⟩
      by_contra hc
      push_neg at hc
      have hx : w ∈ out G X := mem_out.2 ⟨o1, hc.1⟩
      have hf : w ∈ out G F := mem_out.2 ⟨o2, hc.2⟩
      exact hw1 (Finset.mem_inter.2 ⟨hx, hf⟩)
    by_cases ha : w ∈ bd G Y1 <;> by_cases hb : w ∈ bd G Y2
    · obtain ⟨-, a2, a3⟩ := fa ha
      obtain ⟨-, b2, b3⟩ := fb hb
      simp [ha, hb, mem_bd_of_not b2 a2, mem_bd_of_not b3 a3]
    · rcases (fa ha).1 with h | h <;> simp [ha, hb, h]
    · rcases (fb hb).1 with h | h <;> simp [ha, hb, h]
    · simp [ha, hb]
  have e1 := hκ _ hsep2
  have hXc := hX.1.2
  have hFc := hF.2
  have hle : (bd G Y1).card ≤ κ := by omega
  have hfrag : Frag (G := G) κ Y1 := ⟨hsep1, le_antisymm hle (hκ _ hsep1)⟩
  have hcardle := hX.2 _ hfrag
  have hsub : Y1 ⊆ X := Finset.inter_subset_left
  have heq : Y1 = X := Finset.eq_of_subset_of_card_le hsub hcardle
  intro x hx
  rw [← heq] at hx
  exact (Finset.mem_inter.1 hx).2

/-- An atom meeting a fragment `F` cannot have `out F` inside its boundary. -/
lemma atom_not_out_subset_bd {X F : Finset V} (hX : IsAtom (G := G) κ X)
    (hF : Frag (G := G) κ F) (h1 : (X ∩ F).Nonempty) (h2 : out G F ⊆ bd G X) : False := by
  set Y1 := X ∩ F
  obtain ⟨hfo, -, -⟩ := frag_out hκ hF
  have hXF := hX.2 _ hfo
  have hsep1 : Sep G Y1 := by
    refine ⟨h1, ?_⟩
    obtain ⟨z, hz⟩ := hF.1.2
    refine ⟨z, mem_out.2 ⟨fun h => (mem_out.1 hz).1 (Finset.mem_inter.1 h).2, fun h => ?_⟩⟩
    obtain ⟨-, y, hy, hyz⟩ := mem_bd.1 h
    exact not_adj_out (Finset.mem_inter.1 hy).2 hz hyz
  have hcount : (bd G Y1).card + (out G F).card + Y1.card ≤ (bd G X).card + X.card := by
    apply card_add_card_add_card_le
    intro w
    by_cases hw1 : w ∈ out G F
    · have a1 : w ∉ Y1 := fun h => (mem_out.1 hw1).1 (Finset.mem_inter.1 h).2
      have a2 : w ∉ bd G Y1 := by
        intro h
        obtain ⟨-, y, hy, hyw⟩ := mem_bd.1 h
        exact not_adj_out (Finset.mem_inter.1 hy).2 hw1 hyw
      have a3 : w ∈ bd G X := h2 hw1
      simp [hw1, a1, a2, a3]
    · by_cases hw2 : w ∈ Y1
      · have a2 : w ∉ bd G Y1 := not_mem_bd_of_mem hw2
        have a3 : w ∈ X := (Finset.mem_inter.1 hw2).1
        simp [hw1, hw2, a2, a3]
      · by_cases hw3 : w ∈ bd G Y1
        · obtain ⟨-, y, hy, hyw⟩ := mem_bd.1 hw3
          rcases mem_or_mem_bd_of_adj (Finset.mem_inter.1 hy).1 hyw with h | h <;>
            simp [hw1, hw2, hw3, h]
        · simp [hw1, hw2, hw3]
  have e1 := hκ _ hsep1
  have hXc := hX.1.2
  have hY1 : 1 ≤ Y1.card := Finset.card_pos.2 h1
  omega

omit hκ in
lemma atom_card_eq {A B : Finset V} (hA : IsAtom (G := G) κ A) (hB : IsAtom (G := G) κ B) :
    A.card = B.card :=
  le_antisymm (hA.2 _ hB.1) (hB.2 _ hA.1)

omit [Fintype V] hκ in
lemma inter_nonempty_comm {A B : Finset V} (h : (A ∩ B).Nonempty) : (B ∩ A).Nonempty := by
  rwa [Finset.inter_comm]

/-- Two atoms that meet are equal. -/
lemma atom_eq_of_meet {A B : Finset V} (hA : IsAtom (G := G) κ A) (hB : IsAtom (G := G) κ B)
    (h : (A ∩ B).Nonempty) : B = A := by
  have hsub : B ⊆ A := by
    by_cases c1 : (out G B ∩ out G A).Nonempty
    · exact atom_subset_of_meet hκ hB hA.1 (inter_nonempty_comm h) c1
    · by_cases c2 : (B ∩ out G A).Nonempty
      · by_cases c3 : (out G B ∩ A).Nonempty
        · obtain ⟨hfo, -, hoo⟩ := frag_out hκ hA.1
          have : B ⊆ out G A := atom_subset_of_meet hκ hB hfo c2 (by rwa [hoo])
          exfalso
          obtain ⟨x, hx⟩ := h
          rw [Finset.mem_inter] at hx
          exact (mem_out.1 (this hx.2)).1 hx.1
        · exfalso
          refine atom_not_out_subset_bd hκ hA hB.1 h ?_
          intro w hw
          refine mem_bd_of_not (fun hwA => c3 ⟨w, Finset.mem_inter.2 ⟨hw, hwA⟩⟩) ?_
          intro hwo
          exact c1 ⟨w, Finset.mem_inter.2 ⟨hw, hwo⟩⟩
      · exfalso
        refine atom_not_out_subset_bd hκ hB hA.1 (inter_nonempty_comm h) ?_
        intro w hw
        refine mem_bd_of_not (fun hwB => c2 ⟨w, Finset.mem_inter.2 ⟨hwB, hw⟩⟩) ?_
        intro hwo
        exact c1 ⟨w, Finset.mem_inter.2 ⟨hwo, hw⟩⟩
  exact Finset.eq_of_subset_of_card_le hsub (atom_card_eq hA hB).le

/-- An atom meeting the boundary of another atom lies inside that boundary. -/
lemma atom_subset_bd {A B : Finset V} (hA : IsAtom (G := G) κ A) (hB : IsAtom (G := G) κ B)
    (h : (B ∩ bd G A).Nonempty) : B ⊆ bd G A := by
  have nA : ¬ (B ∩ A).Nonempty := by
    intro hBA
    have := atom_eq_of_meet hκ hA hB (inter_nonempty_comm hBA)
    subst this
    obtain ⟨x, hx⟩ := h
    rw [Finset.mem_inter] at hx
    exact not_mem_bd_of_mem hx.1 hx.2
  have nO : ¬ (B ∩ out G A).Nonempty := by
    intro c2
    obtain ⟨hfo, -, hoo⟩ := frag_out hκ hA.1
    by_cases c3 : (out G B ∩ A).Nonempty
    · have : B ⊆ out G A := atom_subset_of_meet hκ hB hfo c2 (by rwa [hoo])
      obtain ⟨x, hx⟩ := h
      rw [Finset.mem_inter] at hx
      exact (mem_out.1 (this hx.1)).2 hx.2
    · refine atom_not_out_subset_bd hκ hB hfo c2 ?_
      rw [hoo]
      intro w hw
      refine mem_bd_of_not (fun hwB => nA ⟨w, Finset.mem_inter.2 ⟨hwB, hw⟩⟩) ?_
      intro hwo
      exact c3 ⟨w, Finset.mem_inter.2 ⟨hwo, hw⟩⟩
  intro b hb
  exact mem_bd_of_not (fun h' => nA ⟨b, Finset.mem_inter.2 ⟨hb, h'⟩⟩)
    (fun h' => nO ⟨b, Finset.mem_inter.2 ⟨hb, h'⟩⟩)

end Atoms

section Transport

variable (φ : G ≃g G)

lemma bd_image (Y : Finset V) : bd G (Y.image φ) = (bd G Y).image φ := by
  ext w
  obtain ⟨w', rfl⟩ := φ.surjective w
  simp only [mem_bd, Finset.mem_image, EmbeddingLike.apply_eq_iff_eq, exists_eq_right]
  constructor
  · rintro ⟨h1, _, ⟨y, hy, rfl⟩, h2⟩
    exact ⟨h1, y, hy, φ.map_adj_iff.1 h2⟩
  · rintro ⟨h1, y, hy, h2⟩
    exact ⟨h1, φ y, ⟨y, hy, rfl⟩, φ.map_adj_iff.2 h2⟩

lemma out_image (Y : Finset V) : out G (Y.image φ) = (out G Y).image φ := by
  ext w
  obtain ⟨w', rfl⟩ := φ.surjective w
  simp only [mem_out, bd_image, Finset.mem_image, EmbeddingLike.apply_eq_iff_eq,
    exists_eq_right]

omit [Fintype V] in
lemma card_image_iso (Y : Finset V) : (Y.image φ).card = Y.card :=
  Finset.card_image_of_injective _ φ.injective

lemma sep_image {Y : Finset V} (h : Sep G Y) : Sep G (Y.image φ) := by
  refine ⟨h.1.image _, ?_⟩
  rw [out_image]; exact h.2.image _

lemma frag_image {κ : ℕ} {Y : Finset V} (h : Frag (G := G) κ Y) : Frag (G := G) κ (Y.image φ) :=
  ⟨sep_image φ h.1, by rw [bd_image, card_image_iso, h.2]⟩

lemma atom_image {κ : ℕ} {A : Finset V} (h : IsAtom (G := G) κ A) :
    IsAtom (G := G) κ (A.image φ) := by
  refine ⟨frag_image φ h.1, fun F hF => ?_⟩
  have hF' := frag_image φ.symm hF
  have := h.2 _ hF'
  rw [card_image_iso] at this ⊢
  exact this

end Transport

/-- In a connected graph, a separating set has a nonempty boundary. -/
lemma bd_nonempty_of_sep (hconn : G.Connected) {Y : Finset V} (h : Sep G Y) :
    (bd G Y).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  obtain ⟨y, hy⟩ := h.1
  obtain ⟨z, hz⟩ := h.2
  have hr := reachIn_univ_of_reachable (hconn.preconnected y z)
  have : z ∈ Y := by
    refine ReachIn.closed (Q := (· ∈ Y)) hy (fun a b ha _ _ hab => ?_) hr
    rcases mem_or_mem_bd_of_adj ha hab with h' | h'
    · exact h'
    · rw [hne] at h'; simp at h'
  exact (mem_out.1 hz).1 this

end Watkins

open Watkins in
/-- **Watkins' theorem** (the case used for cycles).  A finite connected vertex-transitive
graph in which every vertex has degree at least `3` is `3`-connected. -/
theorem vt_kconnected_three {V : Type*} [Fintype V] {G : SimpleGraph V} (hconn : G.Connected)
    (hvt : VertexTransitive G) (hdeg : ∀ v, 3 ≤ G.degree v) : KConnected G 3 := by
  obtain ⟨v0⟩ := hconn.nonempty
  refine ⟨?_, ?_⟩
  · have h1 : v0 ∉ G.neighborFinset v0 := by simp
    have h2 := Finset.card_le_univ (insert v0 (G.neighborFinset v0))
    rw [Finset.card_insert_of_notMem h1, SimpleGraph.card_neighborFinset_eq_degree] at h2
    have := hdeg v0
    omega
  intro T hT u v hu hv
  by_contra hr
  -- the vertices reachable from `u` avoiding `T` form a separating set with boundary in `T`
  set Y0 : Finset V := Finset.univ.filter (fun w => ReachIn G {w | w ∉ T} u w)
  have hY0bd : bd G Y0 ⊆ T := by
    intro w hw
    obtain ⟨hw1, y, hy, hyw⟩ := mem_bd.1 hw
    by_contra hwT
    apply hw1
    simp only [Y0, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact hy.tail hyw hwT
  have hY0 : Sep G Y0 := by
    refine ⟨⟨u, by simp [Y0]; exact ReachIn.refl hu⟩, v, mem_out.2 ⟨?_, fun h => hv (hY0bd h)⟩⟩
    simp [Y0]; exact hr
  -- the connectivity `κ` and an atom
  have hP : ∃ k, ∃ Y, Sep G Y ∧ (bd G Y).card = k := ⟨_, Y0, hY0, rfl⟩
  set κ := Nat.find hP with hκdef
  have hκ : ∀ Y : Finset V, Sep G Y → κ ≤ (bd G Y).card :=
    fun Y hY => Nat.find_min' hP ⟨Y, hY, rfl⟩
  have hκ2 : κ ≤ 2 := by
    have := hκ _ hY0
    have := Finset.card_le_card hY0bd
    omega
  have hQ : ∃ m, ∃ A, Frag (G := G) κ A ∧ A.card = m := by
    obtain ⟨Y, hY, hYc⟩ := Nat.find_spec hP
    exact ⟨_, Y, ⟨hY, hYc⟩, rfl⟩
  obtain ⟨A, hAf, hAc⟩ := Nat.find_spec hQ
  have hA : IsAtom (G := G) κ A :=
    ⟨hAf, fun F hF => by rw [hAc]; exact Nat.find_min' hQ ⟨F, hF, rfl⟩⟩
  -- every vertex lies in an atom
  obtain ⟨a0, ha0⟩ := hAf.1.1
  have hcover : ∀ x, ∃ B, IsAtom (G := G) κ B ∧ x ∈ B := by
    intro x
    obtain ⟨φ, hφ⟩ := hvt a0 x
    exact ⟨A.image φ, atom_image φ hA, Finset.mem_image.2 ⟨a0, ha0, hφ⟩⟩
  obtain ⟨x, hx⟩ := bd_nonempty_of_sep hconn hAf.1
  obtain ⟨B, hB, hxB⟩ := hcover x
  have hBsub : B ⊆ bd G A := atom_subset_bd hκ hA hB ⟨x, Finset.mem_inter.2 ⟨hxB, hx⟩⟩
  have hABc := atom_card_eq hA hB
  -- the boundary of `A` contains two disjoint atoms
  have h2A : 2 * A.card ≤ κ := by
    by_contra hlt
    push_neg at hlt
    have hbdB : bd G A = B := by
      apply Finset.Subset.antisymm _ hBsub
      intro y hy
      obtain ⟨B', hB', hyB'⟩ := hcover y
      have hB'sub : B' ⊆ bd G A := atom_subset_bd hκ hA hB' ⟨y, Finset.mem_inter.2 ⟨hyB', hy⟩⟩
      by_cases hm : (B ∩ B').Nonempty
      · rw [← atom_eq_of_meet hκ hB hB' hm]; exact hyB'
      · exfalso
        rw [Finset.not_nonempty_iff_eq_empty, ← Finset.disjoint_iff_inter_eq_empty] at hm
        have := Finset.card_le_card (Finset.union_subset hBsub hB'sub)
        rw [Finset.card_union_of_disjoint hm, ← atom_card_eq hA hB,
          ← atom_card_eq hA hB', hAf.2] at this
        omega
    -- `bd B = A`
    obtain ⟨-, a1, ha1, ha1x⟩ := mem_bd.1 hx
    have ha1B : a1 ∈ bd G B := by
      refine mem_bd.2 ⟨fun h => ?_, x, hxB, ha1x.symm⟩
      rw [← hbdB] at h
      exact not_mem_bd_of_mem ha1 h
    have hAsub : A ⊆ bd G B := atom_subset_bd hκ hB hA ⟨a1, Finset.mem_inter.2 ⟨ha1, ha1B⟩⟩
    have hbdBA : bd G B = A := by
      symm
      apply Finset.eq_of_subset_of_card_le hAsub
      rw [hB.1.2, ← hAf.2, hbdB, hABc]
    -- then `A ∪ B` is closed under adjacency, contradicting `out A ≠ ∅`
    obtain ⟨z, hz⟩ := hAf.1.2
    have hr' := reachIn_univ_of_reachable (hconn.preconnected a0 z)
    have : z ∈ A ∨ z ∈ B := by
      refine ReachIn.closed (Q := fun w => w ∈ A ∨ w ∈ B) (Or.inl ha0) ?_ hr'
      intro p q hp _ _ hpq
      rcases hp with hp | hp
      · rcases mem_or_mem_bd_of_adj hp hpq with h' | h'
        · exact Or.inl h'
        · rw [hbdB] at h'; exact Or.inr h'
      · rcases mem_or_mem_bd_of_adj hp hpq with h' | h'
        · exact Or.inr h'
        · rw [hbdBA] at h'; exact Or.inl h'
    rcases this with h' | h'
    · exact (mem_out.1 hz).1 h'
    · exact (mem_out.1 hz).2 (hbdB ▸ h')
  -- so `A` is a single vertex, whose neighbours all lie in `bd A`
  have hA1 : A.card ≤ 1 := by omega
  have hsingle : A = {a0} := by
    apply Finset.eq_singleton_iff_unique_mem.2 ⟨ha0, fun y hy => ?_⟩
    exact Finset.card_le_one.1 hA1 y hy a0 ha0
  have hnb : G.neighborFinset a0 ⊆ bd G A := by
    intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    refine mem_bd.2 ⟨?_, a0, ha0, hw⟩
    rw [hsingle, Finset.mem_singleton]
    exact fun h => G.loopless.irrefl a0 (h ▸ hw)
  have := Finset.card_le_card hnb
  rw [SimpleGraph.card_neighborFinset_eq_degree, hAf.2] at this
  have := hdeg a0
  omega

end Lovasz
