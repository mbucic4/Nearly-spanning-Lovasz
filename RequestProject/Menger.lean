module
public import RequestProject.Connectors

/-!
# Menger's theorem (set-to-set, vertex version)

If every set of vertices separating `A` from `B` in a finite graph `G` has at least `k`
elements, then `G` contains `k` pairwise vertex-disjoint `A`–`B` paths.  Here an `A`–`B` path
starts in `A`, ends in `B` and meets `A` and `B` only in its first and last vertex
respectively; a common vertex of `A` and `B` gives a one-vertex path, and separators may meet
`A` and `B`.

The proof is by induction on the number of edges, following the classical edge-deletion
argument.
-/

@[expose] public section


open Classical

namespace Lovasz

variable {V : Type*}

/-- The finite set `T` separates `A` from `B` in `G`: no walk from `A` to `B` avoids `T`. -/
def Separates (G : SimpleGraph V) (A B : Set V) (T : Finset V) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, ¬ ReachIn G {v | v ∉ T} a b

/-- `p` is a family of `k` pairwise vertex-disjoint `A`–`B` paths in `G`. -/
def DisjPaths (G : SimpleGraph V) (A B : Set V) (k : ℕ) (p : Fin k → List V) : Prop :=
  (∀ i, IsPathL G (p i)) ∧ (∀ i, ∃ a ∈ A, (p i).head? = some a) ∧
    (∀ i, ∃ b ∈ B, (p i).getLast? = some b) ∧
    (∀ i, ∀ z ∈ p i, z ∈ A → (p i).head? = some z) ∧
    (∀ i, ∀ z ∈ p i, z ∈ B → (p i).getLast? = some z) ∧
    (∀ i j, i ≠ j → (p i).Disjoint (p j))

lemma Separates.symm {G : SimpleGraph V} {A B : Set V} {T : Finset V}
    (h : Separates G A B T) : Separates G B A T :=
  fun b hb a ha hr => h a ha b hb hr.symm

lemma reachIn_eq_of_no_edges {G : SimpleGraph V} (hG : ∀ u v, ¬ G.Adj u v) {s : Set V}
    {a b : V} (h : ReachIn G s a b) : a = b := by
  obtain ⟨-, h⟩ := h
  induction h with
  | refl => rfl
  | tail _ hbc _ => exact absurd hbc.1 (hG _ _)

/-- A path meeting `X` only in its last vertex reaches each of its other vertices from its
first vertex outside `X`. -/
lemma reachIn_of_mem_path {G : SimpleGraph V} {l : List V} (hl : IsPathL G l) {a : V}
    (ha : l.head? = some a) {X : Set V} (hX : ∀ z ∈ l, z ∈ X → l.getLast? = some z)
    {v : V} (hv : v ∈ l) (hvX : v ∉ X) : ReachIn G {w | w ∉ X} a v := by
  obtain ⟨l1, l2, rfl⟩ := List.mem_iff_append.1 hv
  have hpre : l1 ++ [v] <+: l1 ++ v :: l2 := ⟨l2, by simp⟩
  refine reachIn_of_chain (hl.1.prefix hpre) ?_ ?_ (by simp)
  · intro z hz hzX
    have hlast := hX z (hpre.subset hz) hzX
    have hnd := hl.2
    cases l2 with
    | nil =>
      simp at hlast
      exact hvX (hlast ▸ hzX)
    | cons c l2 =>
      have hmem : z ∈ c :: l2 := by
        have := List.mem_of_getLast? hlast
        simp only [List.mem_append, List.mem_cons] at this
        rw [List.getLast?_append_of_ne_nil _ (by simp)] at hlast
        exact List.mem_of_getLast? hlast
      rw [show l1 ++ v :: c :: l2 = (l1 ++ [v]) ++ (c :: l2) by simp] at hnd
      exact (List.nodup_append.1 hnd).2.2 z hz z hmem rfl
  · rw [← ha]
    cases l1 with
    | nil => simp
    | cons _ _ => simp

/-- The transfer step: if `S` separates `A` from `B` after deleting the edge `xy`, and `y`
cannot be reached from `A` avoiding `S`, then every set separating `A` from `S ∪ {x}` in the
smaller graph separates `A` from `B` in `G`. -/
lemma sep_transfer {G : SimpleGraph V} {x y : V} {A B : Set V} {S T : Finset V}
    (hS : Separates (G.deleteEdges {s(x, y)}) A B S)
    (hy : ∀ a ∈ A, ¬ ReachIn (G.deleteEdges {s(x, y)}) {v | v ∉ S} a y)
    (hT : Separates (G.deleteEdges {s(x, y)}) A (insert x S : Finset V) T) :
    Separates G A B T := by
  intro a ha b hb hr
  set G' := G.deleteEdges {s(x, y)} with hG'
  have hG'adj : ∀ u w, G.Adj u w → ¬ G'.Adj u w → s(u, w) = s(x, y) := by
    intro u w h h'
    rw [hG', SimpleGraph.deleteEdges_adj] at h'
    push_neg at h'
    simpa using h' h
  set X : Finset V := insert x S with hX
  have hsub : {w : V | w ∉ T ∧ w ∉ X} ⊆ {w | w ∉ S} := by
    intro w hw hwS; exact hw.2 (Finset.mem_insert_of_mem hwS)
  have hsub' : {w : V | w ∉ T ∧ w ∉ X} ⊆ {w | w ∉ T} := fun w hw => hw.1
  have key := ReachIn.closed
    (Q := fun v => (∃ z ∈ X, ReachIn G' {w | w ∉ T} a z) ∨
      ReachIn G' {w | w ∉ T ∧ w ∉ X} a v) (s := {w | w ∉ T}) ?_ ?_ hr
  · rcases key with ⟨z, hz, hrz⟩ | hrb
    · exact hT a ha z hz hrz
    · exact hS a ha b hb (hrb.mono le_rfl hsub)
  · by_cases haX : a ∈ X
    · exact Or.inl ⟨a, haX, ReachIn.refl hr.1⟩
    · exact Or.inr (ReachIn.refl ⟨hr.1, haX⟩)
  · intro u w hQu _ hw hadj
    rcases hQu with h | h
    · exact Or.inl h
    have huX : u ∉ X := h.mem_right.2
    by_cases hwX : w ∈ X
    · by_cases hG'uw : G'.Adj u w
      · exact Or.inl ⟨w, hwX, (h.mono le_rfl hsub').tail hG'uw hw⟩
      · have he := hG'adj u w hadj hG'uw
        rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact absurd (Finset.mem_insert_self _ _) huX
        · exact absurd (h.mono le_rfl hsub) (hy a ha)
    · by_cases hG'uw : G'.Adj u w
      · exact Or.inr (h.tail hG'uw ⟨hw, hwX⟩)
      · have he := hG'adj u w hadj hG'uw
        rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact absurd (Finset.mem_insert_self _ _) huX
        · exact absurd (Finset.mem_insert_self _ _) hwX

/-- Combining `A`–`(S ∪ {u})` paths with `(S ∪ {w})`–`B` paths across the edge `uw`. -/
lemma combine_paths {G G' : SimpleGraph V} (hGG : G' ≤ G) {u w : V} (huw : G.Adj u w)
    {A B : Set V} {S : Finset V} {k : ℕ} (hS : Separates G' A B S)
    (hu : ∃ a ∈ A, ReachIn G' {v | v ∉ S} a u) (hw : ∃ b ∈ B, ReachIn G' {v | v ∉ S} b w)
    (hYk : (insert w S).card ≤ k) (p q : Fin k → List V)
    (hp : DisjPaths G' A ((insert u S : Finset V) : Set V) k p)
    (hq : DisjPaths G' ((insert w S : Finset V) : Set V) B k q) :
    ∃ r, DisjPaths G A B k r := by
  let CA : V → Prop := fun v => ∃ a ∈ A, ReachIn G' {v | v ∉ S} a v
  let CB : V → Prop := fun v => ∃ b ∈ B, ReachIn G' {v | v ∉ S} b v
  have hCAB : ∀ v, CA v → CB v → False := by
    rintro v ⟨a, ha, hav⟩ ⟨b, hb, hbv⟩
    exact hS a ha b hb (hav.trans hbv.symm)
  have hCAS : ∀ v, CA v → v ∉ S := fun v ⟨_, _, h⟩ => h.mem_right
  have hCBS : ∀ v, CB v → v ∉ S := fun v ⟨_, _, h⟩ => h.mem_right
  have hCAB' : ∀ v, CA v → v ∈ B → False := fun v ⟨a, ha, h⟩ hv => hS a ha v hv h
  have hCBA : ∀ v, CB v → v ∈ A → False := fun v ⟨b, hb, h⟩ hv => hS v hv b hb h.symm
  have huS : u ∉ S := hCAS u hu
  have hwS : w ∉ S := hCBS w hw
  obtain ⟨hpP, hpA, hpB, hpA', hpB', hpD⟩ := hp
  obtain ⟨hqP, hqA, hqB, hqA', hqB', hqD⟩ := hq
  choose tl htlX htl using hpB
  choose hd hdY hhd using hqA
  have hF1 : ∀ i, ∀ v ∈ p i, CA v ∨ (v ∈ S ∧ v = tl i) := by
    intro i v hv
    by_cases hvX : v ∈ ((insert u S : Finset V) : Set V)
    · have h1 := hpB' i v hv hvX
      rw [htl i] at h1
      have hvt : v = tl i := (Option.some.inj h1).symm
      rcases Finset.mem_insert.1 hvX with rfl | hvS
      · exact Or.inl hu
      · exact Or.inr ⟨hvS, hvt⟩
    · obtain ⟨a, ha, hah⟩ := hpA i
      refine Or.inl ⟨a, ha, (reachIn_of_mem_path (hpP i) hah (hpB' i) hv hvX).mono le_rfl ?_⟩
      intro z hz hzS; exact hz (Finset.mem_insert_of_mem hzS)
  have hF2 : ∀ j, ∀ v ∈ q j, CB v ∨ (v ∈ S ∧ v = hd j) := by
    intro j v hv
    by_cases hvY : v ∈ ((insert w S : Finset V) : Set V)
    · have h1 := hqA' j v hv hvY
      rw [hhd j] at h1
      have hvt : v = hd j := (Option.some.inj h1).symm
      rcases Finset.mem_insert.1 hvY with rfl | hvS
      · exact Or.inl hw
      · exact Or.inr ⟨hvS, hvt⟩
    · obtain ⟨b, hb, hbl⟩ := hqB j
      have hrev : IsPathL G' (q j).reverse := (hqP j).reverse
      have hrevh : (q j).reverse.head? = some b := by rw [List.head?_reverse]; exact hbl
      have hrevX : ∀ z ∈ (q j).reverse, z ∈ ((insert w S : Finset V) : Set V) →
          (q j).reverse.getLast? = some z := by
        intro z hz hzY
        rw [List.getLast?_reverse]; exact hqA' j z (List.mem_reverse.1 hz) hzY
      refine Or.inl ⟨b, hb, (reachIn_of_mem_path hrev hrevh hrevX (List.mem_reverse.2 hv)
        hvY).mono le_rfl ?_⟩
      intro z hz hzS; exact hz (Finset.mem_insert_of_mem hzS)
  have hdinj : Function.Injective hd := by
    intro j j' h
    by_contra hjj
    exact hqD j j' hjj (List.mem_of_head? (hhd j)) (h ▸ List.mem_of_head? (hhd j'))
  have htlinj : Function.Injective tl := by
    intro i i' h
    by_contra hii
    exact hpD i i' hii (List.mem_of_getLast? (htl i)) (h ▸ List.mem_of_getLast? (htl i'))
  have hsurj : ∀ z ∈ insert w S, ∃ j, hd j = z := by
    intro z hz
    have hsub : Finset.univ.image hd ⊆ insert w S := by
      intro y hy
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
      exact hdY j
    have hcard : (insert w S).card ≤ (Finset.univ.image hd).card := by
      rw [Finset.card_image_of_injective _ hdinj, Finset.card_univ, Fintype.card_fin]
      exact hYk
    have heq := Finset.eq_of_subset_of_card_le hsub hcard
    rw [← heq] at hz
    obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hz
    exact ⟨j, hj⟩
  let t : Fin k → V := fun i => if tl i = u then w else tl i
  have htY : ∀ i, t i ∈ insert w S := by
    intro i
    by_cases h : tl i = u
    · simp only [t, if_pos h]; exact Finset.mem_insert_self _ _
    · simp only [t, if_neg h]
      rcases Finset.mem_insert.1 (htlX i) with h' | h'
      · exact absurd h' h
      · exact Finset.mem_insert_of_mem h'
  have htS : ∀ i, tl i ≠ u → tl i ∈ S := by
    intro i h
    rcases Finset.mem_insert.1 (htlX i) with h' | h'
    · exact absurd h' h
    · exact h'
  have htinj : ∀ i i', t i = t i' → i = i' := by
    intro i i' h
    apply htlinj
    by_cases h1 : tl i = u <;> by_cases h2 : tl i' = u <;> simp only [t, h1, h2, if_true,
      if_false] at h
    · rw [h1, h2]
    · exact absurd (h ▸ htS i' h2) hwS
    · exact absurd (h.symm ▸ htS i h1) hwS
    · exact h
  choose j hj using fun i => hsurj (t i) (htY i)
  have hjinj : ∀ i i', j i = j i' → i = i' := by
    intro i i' h
    apply htinj
    rw [← hj i, ← hj i', h]
  have hpne : ∀ i, p i ≠ [] := by
    intro i h; have := htl i; rw [h] at this; simp at this
  have hqne : ∀ j, q j ≠ [] := by
    intro j h; have := hhd j; rw [h] at this; simp at this
  let r : Fin k → List V := fun i => if tl i = u then p i ++ q (j i) else p i ++ (q (j i)).tail
  have hrmem : ∀ i v, v ∈ r i → v ∈ p i ∨ v ∈ q (j i) := by
    intro i v hv
    by_cases h : tl i = u
    · simp only [r, if_pos h] at hv; exact List.mem_append.1 hv
    · simp only [r, if_neg h] at hv; exact glue_mem hv
  have hqhead : ∀ i, tl i ≠ u → (q (j i)).head? = some (tl i) := by
    intro i h; rw [hhd, hj]; simp only [t, if_neg h]
  have hqheadu : ∀ i, tl i = u → (q (j i)).head? = some w := by
    intro i h; rw [hhd, hj]; simp only [t, if_pos h]
  refine ⟨r, fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_, ?_⟩
  · by_cases h : tl i = u
    · simp only [r, if_pos h]
      refine ⟨List.isChain_append.2 ⟨(hpP i).1.imp (fun _ _ h => hGG h),
        (hqP _).1.imp (fun _ _ h => hGG h), ?_⟩, List.nodup_append.2 ⟨(hpP i).2, (hqP _).2, ?_⟩⟩
      · intro a ha b hb
        rw [htl i, Option.mem_def, Option.some.injEq, h] at ha
        rw [hqheadu i h, Option.mem_def, Option.some.injEq] at hb
        subst ha hb; exact huw
      · intro a ha b hb hab
        subst hab
        rcases hF1 i a ha with h1 | ⟨h1, h1'⟩ <;> rcases hF2 _ a hb with h2 | ⟨h2, h2'⟩
        · exact hCAB a h1 h2
        · exact hCAS a h1 h2
        · exact hCBS a h2 h1
        · rw [h1', h] at h1; exact huS h1
    · simp only [r, if_neg h]
      refine ⟨glue_chain ((hpP i).1.imp (fun _ _ h => hGG h)) ((hqP _).1.imp
        (fun _ _ h => hGG h)) (htl i) (hqhead i h), glue_nodup (hpP i).2 (hqP _).2
        (hqhead i h) ?_⟩
      intro a ha hb
      rcases hF1 i a ha with h1 | ⟨h1, h1'⟩
      · rcases hF2 _ a hb with h2 | ⟨h2, h2'⟩
        · exact (hCAB a h1 h2).elim
        · exact (hCAS a h1 h2).elim
      · exact h1'
  · obtain ⟨a, ha, hah⟩ := hpA i
    refine ⟨a, ha, ?_⟩
    by_cases h : tl i = u
    · simp only [r, if_pos h]; rw [List.head?_append, hah]; rfl
    · simp only [r, if_neg h]; rw [glue_head (htl i), hah]
  · obtain ⟨b, hb, hbl⟩ := hqB (j i)
    refine ⟨b, hb, ?_⟩
    by_cases h : tl i = u
    · simp only [r, if_pos h]; rw [List.getLast?_append_of_ne_nil _ (hqne _), hbl]
    · simp only [r, if_neg h]; rw [glue_getLast (htl i) (hqhead i h), hbl]
  · intro v hv hvA
    have hhead : (r i).head? = (p i).head? := by
      by_cases h : tl i = u
      · simp only [r, if_pos h]; rw [List.head?_append]
        obtain ⟨a, -, hah⟩ := hpA i; rw [hah]; rfl
      · simp only [r, if_neg h]; rw [glue_head (htl i)]
    rw [hhead]
    rcases hrmem i v hv with h1 | h1
    · exact hpA' i v h1 hvA
    · rcases hF2 _ v h1 with h2 | ⟨h2, h2'⟩
      · exact (hCBA v h2 hvA).elim
      · rw [hj] at h2'
        by_cases h : tl i = u
        · simp only [t, if_pos h] at h2'; exact absurd (h2' ▸ h2) hwS
        · simp only [t, if_neg h] at h2'
          exact hpA' i v (h2' ▸ List.mem_of_getLast? (htl i)) hvA
  · intro v hv hvB
    have hlast : (r i).getLast? = (q (j i)).getLast? := by
      by_cases h : tl i = u
      · simp only [r, if_pos h]; rw [List.getLast?_append_of_ne_nil _ (hqne _)]
      · simp only [r, if_neg h]; rw [glue_getLast (htl i) (hqhead i h)]
    rw [hlast]
    rcases hrmem i v hv with h1 | h1
    · rcases hF1 i v h1 with h2 | ⟨h2, h2'⟩
      · exact (hCAB' v h2 hvB).elim
      · by_cases h : tl i = u
        · exact absurd (h ▸ h2' ▸ h2) huS
        · have := hqhead i h
          rw [← h2'] at this
          exact hqB' _ v (List.mem_of_head? this) hvB
    · exact hqB' _ v h1 hvB
  · intro i i' hii v hv hv'
    rcases hrmem i v hv with h1 | h1 <;> rcases hrmem i' v hv' with h2 | h2
    · exact hpD i i' hii h1 h2
    · rcases hF1 i v h1 with h3 | ⟨h3, h3'⟩ <;> rcases hF2 _ v h2 with h4 | ⟨h4, h4'⟩
      · exact hCAB v h3 h4
      · exact hCAS v h3 h4
      · exact hCBS v h4 h3
      · rw [hj] at h4'
        by_cases h : tl i' = u
        · simp only [t, if_pos h] at h4'; exact hwS (h4' ▸ h4)
        · simp only [t, if_neg h] at h4'
          exact hii (htlinj (h3'.symm.trans h4'))
    · rcases hF1 i' v h2 with h3 | ⟨h3, h3'⟩ <;> rcases hF2 _ v h1 with h4 | ⟨h4, h4'⟩
      · exact hCAB v h3 h4
      · exact hCAS v h3 h4
      · exact hCBS v h4 h3
      · rw [hj] at h4'
        by_cases h : tl i = u
        · simp only [t, if_pos h] at h4'; exact hwS (h4' ▸ h4)
        · simp only [t, if_neg h] at h4'
          exact hii (htlinj (h4'.symm.trans h3'))
    · have hjj : j i ≠ j i' := fun h => hii (hjinj i i' h)
      exact hqD _ _ hjj h1 h2

lemma DisjPaths.mono {G G' : SimpleGraph V} (hG : G' ≤ G) {A B : Set V} {k : ℕ}
    {p : Fin k → List V} (h : DisjPaths G' A B k p) : DisjPaths G A B k p :=
  ⟨fun i => (h.1 i).mono hG, h.2⟩

lemma menger_no_edges [Fintype V] {G : SimpleGraph V} (hG : ∀ u v, ¬ G.Adj u v)
    {A B : Set V} {k : ℕ} (h : ∀ T, Separates G A B T → k ≤ T.card) :
    ∃ p, DisjPaths G A B k p := by
  set T : Finset V := Finset.univ.filter (fun v => v ∈ A ∧ v ∈ B) with hT
  have hsep : Separates G A B T := by
    intro a ha b hb hr
    have hab := reachIn_eq_of_no_edges hG hr
    subst hab
    exact hr.mem_left (by simp [hT, ha, hb])
  have hk := h T hsep
  have hlen : k ≤ T.toList.length := by rw [Finset.length_toList]; exact hk
  have hmem : ∀ i : Fin k, T.toList[i.1]'(by omega) ∈ T := fun i =>
    Finset.mem_toList.1 (List.getElem_mem _)
  refine ⟨fun i => [T.toList[i.1]'(by omega)], fun i => isPathL_singleton _, fun i => ?_,
    fun i => ?_, fun i => ?_, fun i => ?_, fun i j hij => ?_⟩
  · exact ⟨_, (by simpa [hT] using hmem i : _ ∧ _).1, rfl⟩
  · exact ⟨_, (by simpa [hT] using hmem i : _ ∧ _).2, rfl⟩
  · intro z hz _; simp at hz; simp [hz]
  · intro z hz _; simp at hz; simp [hz]
  · intro z hz hz'
    simp only [List.mem_singleton] at hz hz'
    have := (List.Nodup.getElem_inj_iff (Finset.nodup_toList T)).1 (hz.symm.trans hz')
    exact hij (Fin.ext this)

/-- **Menger's theorem** (set version). -/
theorem menger [Fintype V] (G : SimpleGraph V) (A B : Set V) (k : ℕ)
    (h : ∀ T, Separates G A B T → k ≤ T.card) : ∃ p, DisjPaths G A B k p := by
  suffices key : ∀ n, ∀ (G : SimpleGraph V) (A B : Set V) (k : ℕ),
      (Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2)).card = n →
      (∀ T, Separates G A B T → k ≤ T.card) → ∃ p, DisjPaths G A B k p from
    key _ G A B k rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G A B k hn h
  by_cases hE : ∀ u v, ¬ G.Adj u v
  · exact menger_no_edges hE h
  push_neg at hE
  obtain ⟨x, y, hxy⟩ := hE
  set G' := G.deleteEdges {s(x, y)} with hG'
  have hle : G' ≤ G := SimpleGraph.deleteEdges_le _
  have hlt : (Finset.univ.filter (fun p : V × V => G'.Adj p.1 p.2)).card < n := by
    rw [← hn]
    refine Finset.card_lt_card ⟨fun p hp => ?_, fun hsub => ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢; exact hle hp
    · have := hsub (by simp [hxy] : (x, y) ∈ Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2))
      simp [hG'] at this
  have IH : ∀ (A B : Set V) (k : ℕ), (∀ T, Separates G' A B T → k ≤ T.card) →
      ∃ p, DisjPaths G' A B k p := fun A B k h => ih _ hlt G' A B k (by convert rfl) h
  by_cases hall : ∀ T, Separates G' A B T → k ≤ T.card
  · obtain ⟨p, hp⟩ := IH A B k hall
    exact ⟨p, hp.mono hle⟩
  push_neg at hall
  obtain ⟨S, hS, hSk⟩ := hall
  have hnsep : ¬ Separates G A B S := fun hs => absurd (h S hs) (not_le.2 hSk)
  simp only [Separates, not_forall, not_not] at hnsep
  obtain ⟨a, ha, b, hb, hab⟩ := hnsep
  let CA : V → Prop := fun v => ∃ a ∈ A, ReachIn G' {v | v ∉ S} a v
  let CB : V → Prop := fun v => ∃ b ∈ B, ReachIn G' {v | v ∉ S} b v
  have hCAB : ∀ v, CA v → CB v → False := by
    rintro v ⟨a, ha, hav⟩ ⟨b, hb, hbv⟩
    exact hS a ha b hb (hav.trans hbv.symm)
  have hG'adj : ∀ u w, G.Adj u w → ¬ G'.Adj u w → s(u, w) = s(x, y) := by
    intro u w h h'
    rw [hG', SimpleGraph.deleteEdges_adj] at h'
    push_neg at h'
    simpa using h' h
  -- a crossing edge from the `A` side
  have hstep : ∀ (C : V → Prop) (c d : V), C c → ¬ C d → ReachIn G {v | v ∉ S} c d →
      (∀ u w, C u → u ∉ S → w ∉ S → G'.Adj u w → C w) →
      ∃ u w, C u ∧ ¬ C w ∧ G.Adj u w ∧ s(u, w) = s(x, y) := by
    intro C c d hc hd hcd hC
    by_contra hno
    push_neg at hno
    refine hd (ReachIn.closed (Q := C) hc ?_ hcd)
    intro u w hu hus hws huw
    by_contra hw
    by_cases h' : G'.Adj u w
    · exact hw (hC u w hu hus hws h')
    · exact hno u w hu hw huw (hG'adj u w huw h')
  have hCAcl : ∀ u w, CA u → u ∉ S → w ∉ S → G'.Adj u w → CA w :=
    fun u w ⟨a, ha, hr⟩ _ hw huw => ⟨a, ha, hr.tail huw hw⟩
  have hCBcl : ∀ u w, CB u → u ∉ S → w ∉ S → G'.Adj u w → CB w :=
    fun u w ⟨a, ha, hr⟩ _ hw huw => ⟨a, ha, hr.tail huw hw⟩
  have haA : CA a := ⟨a, ha, ReachIn.refl hab.mem_left⟩
  have hbB : CB b := ⟨b, hb, ReachIn.refl hab.mem_right⟩
  obtain ⟨u, w, hu, hw, huw, he⟩ := hstep CA a b haA (fun h => hCAB b h hbB) hab hCAcl
  obtain ⟨u', w', hu', hw', huw', he'⟩ := hstep CB b a hbB (fun h => hCAB a haA h) hab.symm hCBcl
  have hwB : CB w := by
    rcases Sym2.eq_iff.1 (he.trans he'.symm) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (hCAB u hu hu').elim
    · exact hu'
  clear hstep hu' hw' huw' he' u' w'
  have hGe : G' = G.deleteEdges {s(u, w)} := by rw [he]
  have hGe' : G' = G.deleteEdges {s(w, u)} := by rw [Sym2.eq_swap, he]
  have hSw : ∀ a ∈ A, ¬ ReachIn G' {v | v ∉ S} a w := fun a ha hr => hCAB w ⟨a, ha, hr⟩ hwB
  have hSu : ∀ b ∈ B, ¬ ReachIn G' {v | v ∉ S} b u := fun b hb hr => hCAB u hu ⟨b, hb, hr⟩
  have h1 : ∀ T, Separates G' A (insert u S : Finset V) T → k ≤ T.card := by
    intro T hT
    rw [hGe] at hS hSw hT
    exact h T (sep_transfer hS hSw hT)
  have h2 : ∀ T, Separates G' (insert w S : Finset V) B T → k ≤ T.card := by
    intro T hT
    have hT' := hT.symm
    have hS' := hS.symm
    rw [hGe'] at hS' hSu hT'
    exact h T (sep_transfer hS' hSu hT').symm
  obtain ⟨p, hp⟩ := IH _ _ _ h1
  obtain ⟨q, hq⟩ := IH _ _ _ h2
  have hYk : (insert w S).card ≤ k := (Finset.card_insert_le _ _).trans hSk
  exact combine_paths hle huw hS hu hwB hYk p q hp hq

end Lovasz
