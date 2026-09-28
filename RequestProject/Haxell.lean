module
public import Mathlib

/-!
# Haxell's hypergraph Hall theorem

We prove a version of the hypergraph Hall theorem of Haxell (the combinatorial form of the
Aharoni–Haxell theorem used in Lemma 5.1 of the cited work on sublinear expanders): if
`H i` (`i ∈ ι`) are families of sets of size at most `Λ` such that for every nonempty set of
indices `I` and every set `Z` of at most `2Λ(|I|-1)` vertices some edge of some `H i`, `i ∈ I`,
avoids `Z`, then there is a system of pairwise disjoint representatives.

The proof is Haxell's alternating-tree argument, with termination by the lexicographic order
on the sequence of the numbers of blocking edges.
-/

@[expose] public section


open Classical

namespace Lovasz

namespace Haxell

variable {ι W : Type*} [DecidableEq W]

section tree

variable (S' : Finset ι) (F : ι → Finset W)

/-- The indices whose representative meets `a`. -/
noncomputable def blk (a : Finset W) : Finset ι := S'.filter (fun m => ¬ Disjoint (F m) a)

/-- The union of the blocking index sets of a tree (stored newest first). -/
noncomputable def bset : List (ι × Finset W) → Finset ι
  | [] => ∅
  | p :: T => blk S' F p.2 ∪ bset T

/-- The vertices covered by a tree: its edges and the blocking representatives. -/
noncomputable def verts : List (ι × Finset W) → Finset W
  | [] => ∅
  | p :: T => p.2 ∪ (blk S' F p.2).biUnion F ∪ verts T

/-- Legal alternating trees (stored newest first). -/
def Legal (H : ι → Finset W → Prop) (i0 : ι) : List (ι × Finset W) → Prop
  | [] => True
  | p :: T => Legal H i0 T ∧ (∀ q ∈ T.head?, (blk S' F q.2).Nonempty) ∧
      p.1 ∈ insert i0 (bset S' F T) ∧ H p.1 p.2 ∧ Disjoint p.2 (verts S' F T)

/-- The signature of a tree, oldest entry first. -/
noncomputable def sig : List (ι × Finset W) → List ℕ
  | [] => []
  | p :: T => sig T ++ [(blk S' F p.2).card]

end tree

section lemmas

variable {S' : Finset ι} {F : ι → Finset W} {H : ι → Finset W → Prop} {i0 : ι}

lemma blk_subset (a : Finset W) : blk S' F a ⊆ S' := Finset.filter_subset _ _

lemma bset_subset : ∀ T : List (ι × Finset W), bset S' F T ⊆ S'
  | [] => by simp [bset]
  | p :: T => by
    simp only [bset]
    exact Finset.union_subset (blk_subset _) (bset_subset T)

lemma mem_bset : ∀ {T : List (ι × Finset W)} {m : ι}, m ∈ bset S' F T →
    ∃ C p A, T = C ++ p :: A ∧ m ∈ blk S' F p.2
  | [], m, h => by simp [bset] at h
  | p :: T, m, h => by
    simp only [bset, Finset.mem_union] at h
    rcases h with h | h
    · exact ⟨[], p, T, rfl, h⟩
    · obtain ⟨C, q, A, rfl, hq⟩ := mem_bset h
      exact ⟨p :: C, q, A, rfl, hq⟩

lemma mem_bset_of {T : List (ι × Finset W)} {q : ι × Finset W} (hq : q ∈ T) {m : ι}
    (hm : m ∈ blk S' F q.2) : m ∈ bset S' F T := by
  induction T with
  | nil => simp at hq
  | cons p T ih =>
    simp only [bset, Finset.mem_union]
    rcases List.mem_cons.1 hq with rfl | hq
    · exact Or.inl hm
    · exact Or.inr (ih hq)

lemma edge_subset_verts {T : List (ι × Finset W)} {q : ι × Finset W} (hq : q ∈ T) :
    q.2 ⊆ verts S' F T := by
  induction T with
  | nil => simp at hq
  | cons p T ih =>
    simp only [verts]
    rcases List.mem_cons.1 hq with rfl | hq
    · exact fun x hx => Finset.mem_union_left _ (Finset.mem_union_left _ hx)
    · exact fun x hx => Finset.mem_union_right _ (ih hq hx)

lemma rep_subset_verts {T : List (ι × Finset W)} {m : ι} (hm : m ∈ bset S' F T) :
    F m ⊆ verts S' F T := by
  induction T with
  | nil => simp [bset] at hm
  | cons p T ih =>
    simp only [bset, Finset.mem_union] at hm
    simp only [verts]
    rcases hm with hm | hm
    · intro x hx
      exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨m, hm, hx⟩))
    · exact fun x hx => Finset.mem_union_right _ (ih hm hx)

lemma legal_suffix : ∀ (C : List (ι × Finset W)) {A : List (ι × Finset W)},
    Legal S' F H i0 (C ++ A) → Legal S' F H i0 A
  | [], _, h => h
  | _ :: C, _, h => legal_suffix C h.1

lemma legal_H : ∀ {T : List (ι × Finset W)}, Legal S' F H i0 T → ∀ q ∈ T, H q.1 q.2
  | [], _, q, hq => by simp at hq
  | p :: T, h, q, hq => by
    rcases List.mem_cons.1 hq with rfl | hq
    · exact h.2.2.2.1
    · exact legal_H h.1 q hq

lemma disjoint_blk_bset {p : ι × Finset W} {T : List (ι × Finset W)}
    (h : Disjoint p.2 (verts S' F T)) : Disjoint (blk S' F p.2) (bset S' F T) := by
  rw [Finset.disjoint_left]
  intro m hm1 hm2
  have h1 := (Finset.mem_filter.1 hm1).2
  exact h1 ((h.mono_right (rep_subset_verts hm2)).symm)

lemma card_bset : ∀ {T : List (ι × Finset W)}, Legal S' F H i0 T →
    (bset S' F T).card = (T.map (fun p => (blk S' F p.2).card)).sum
  | [], _ => by simp [bset]
  | p :: T, h => by
    simp only [bset, List.map_cons, List.sum_cons]
    rw [Finset.card_union_of_disjoint (disjoint_blk_bset h.2.2.2.2), card_bset h.1]

lemma card_verts {Λ : ℕ} (hF : ∀ m ∈ S', (F m).card ≤ Λ) :
    ∀ (T : List (ι × Finset W)), (∀ q ∈ T, q.2.card ≤ Λ) →
    (verts S' F T).card ≤ Λ * T.length + Λ * (T.map (fun p => (blk S' F p.2).card)).sum
  | [], _ => by simp [verts]
  | p :: T, hT => by
    simp only [verts, List.map_cons, List.sum_cons, List.length_cons]
    have h1 := card_verts hF T (fun q hq => hT q (List.mem_cons_of_mem _ hq))
    have h2 : ((blk S' F p.2).biUnion F).card ≤ Λ * (blk S' F p.2).card := by
      refine (Finset.card_biUnion_le).trans ?_
      calc ∑ m ∈ blk S' F p.2, (F m).card ≤ ∑ m ∈ blk S' F p.2, Λ :=
            Finset.sum_le_sum fun m hm => hF m (blk_subset _ hm)
        _ = Λ * (blk S' F p.2).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have h3 := hT p List.mem_cons_self
    calc (p.2 ∪ (blk S' F p.2).biUnion F ∪ verts S' F T).card
        ≤ (p.2 ∪ (blk S' F p.2).biUnion F).card + (verts S' F T).card := Finset.card_union_le _ _
      _ ≤ p.2.card + ((blk S' F p.2).biUnion F).card + (verts S' F T).card := by
        gcongr; exact Finset.card_union_le _ _
      _ ≤ _ := by nlinarith

lemma all_nonempty : ∀ {T : List (ι × Finset W)}, Legal S' F H i0 T →
    (∀ q ∈ T.head?, (blk S' F q.2).Nonempty) → ∀ q ∈ T, (blk S' F q.2).Nonempty
  | [], _, _, q, hq => by simp at hq
  | p :: T, h, hh, q, hq => by
    rcases List.mem_cons.1 hq with rfl | hq
    · exact hh _ rfl
    · exact all_nonempty h.1 h.2.1 q hq

lemma length_le_sum : ∀ (T : List (ι × Finset W)), (∀ q ∈ T, (blk S' F q.2).Nonempty) →
    T.length ≤ (T.map (fun p => (blk S' F p.2).card)).sum
  | [], _ => by simp
  | p :: T, h => by
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    have := length_le_sum T (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have h2 := (h p List.mem_cons_self).card_pos
    omega

lemma sig_length : ∀ T : List (ι × Finset W), (sig S' F T).length = T.length
  | [] => rfl
  | p :: T => by simp [sig, sig_length T]

lemma sig_le : ∀ (T : List (ι × Finset W)), ∀ x ∈ sig S' F T, x ≤ S'.card
  | [], x, hx => by simp [sig] at hx
  | p :: T, x, hx => by
    simp only [sig, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact sig_le T x hx
    · exact Finset.card_le_card (blk_subset _)

lemma sig_append : ∀ (C A : List (ι × Finset W)), sig S' F (C ++ A) = sig S' F A ++ sig S' F C
  | [], A => by simp [sig]
  | p :: C, A => by simp [sig, sig_append C A]

/-- Congruence: trees whose blocking data agree for two assignments. -/
lemma congr_of {F' : ι → Finset W} : ∀ (A : List (ι × Finset W)),
    (∀ q ∈ A, blk S' F' q.2 = blk S' F q.2 ∧ ∀ m ∈ blk S' F q.2, F' m = F m) →
    bset S' F' A = bset S' F A ∧ verts S' F' A = verts S' F A ∧
      (Legal S' F' H i0 A ↔ Legal S' F H i0 A) ∧ sig S' F' A = sig S' F A
  | [], _ => by simp [bset, verts, Legal, sig]
  | p :: A, h => by
    obtain ⟨h1, h2, h3, h4⟩ := congr_of A (fun q hq => h q (List.mem_cons_of_mem _ hq))
    obtain ⟨hp1, hp2⟩ := h p List.mem_cons_self
    have hb : (blk S' F' p.2).biUnion F' = (blk S' F p.2).biUnion F := by
      rw [hp1]; exact Finset.biUnion_congr rfl fun m hm => hp2 m hm
    have hhead : (∀ q ∈ A.head?, (blk S' F' q.2).Nonempty) ↔
        (∀ q ∈ A.head?, (blk S' F q.2).Nonempty) := by
      constructor
      · intro hh q hq
        have := hh q hq
        rwa [(h q (List.mem_cons_of_mem _ (List.mem_of_mem_head? hq))).1] at this
      · intro hh q hq
        rw [(h q (List.mem_cons_of_mem _ (List.mem_of_mem_head? hq))).1]
        exact hh q hq
    refine ⟨by simp [bset, hp1, h1], by simp [verts, hb, h2], ?_, by simp [sig, h4, hp1]⟩
    simp only [Legal, h3, hhead, h1, h2]

end lemmas

/-- The padded signature. -/
def pad (M P : ℕ) (l : List ℕ) : Fin M → ℕ := fun j => l.getD j P

lemma pad_lt {M P : ℕ} {l1 l2 : List ℕ} (i : Fin M) (h : ∀ j < i, pad M P l1 j = pad M P l2 j)
    (hi : pad M P l1 i < pad M P l2 i) : toLex (pad M P l1) < toLex (pad M P l2) :=
  ⟨i, fun j hj => h j hj, hi⟩

/-- The inductive step: a system of disjoint representatives for `S'` extends to `insert i0 S'`. -/
theorem extend_step {H : ι → Finset W → Prop} {Λ : ℕ} (hsz : ∀ i e, H i e → e.card ≤ Λ)
    (hcond : ∀ I : Finset ι, I.Nonempty → ∀ Z : Finset W, Z.card ≤ 2 * Λ * (I.card - 1) →
      ∃ i ∈ I, ∃ e, H i e ∧ Disjoint e Z)
    (S' : Finset ι) (i0 : ι) (hi0 : i0 ∉ S') (F0 : ι → Finset W)
    (hF0H : ∀ i ∈ S', H i (F0 i)) (hF0D : ∀ i ∈ S', ∀ j ∈ S', i ≠ j → Disjoint (F0 i) (F0 j)) :
    ∃ f : ι → Finset W, (∀ i ∈ insert i0 S', H i (f i)) ∧
      ∀ i ∈ insert i0 S', ∀ j ∈ insert i0 S', i ≠ j → Disjoint (f i) (f j) := by
  set M := S'.card + 2
  set P := S'.card + 1
  let μ : (ι → Finset W) → List (ι × Finset W) → Lex (Fin M → ℕ) :=
    fun F T => toLex (pad M P (sig S' F T))
  suffices key : ∀ m : Lex (Fin M → ℕ), ∀ (F : ι → Finset W) (T : List (ι × Finset W)),
      (∀ i ∈ S', H i (F i)) → (∀ i ∈ S', ∀ j ∈ S', i ≠ j → Disjoint (F i) (F j)) →
      Legal S' F H i0 T → μ F T = m →
      ∃ f : ι → Finset W, (∀ i ∈ insert i0 S', H i (f i)) ∧
        ∀ i ∈ insert i0 S', ∀ j ∈ insert i0 S', i ≠ j → Disjoint (f i) (f j) from
    key _ F0 [] hF0H hF0D trivial rfl
  intro m
  induction m using WellFoundedLT.induction with
  | _ m ih =>
  intro F T hFH hFD hT hm
  subst hm
  have hFsz : ∀ m ∈ S', (F m).card ≤ Λ := fun m hm => hsz _ _ (hFH m hm)
  -- the extension case
  have extend : (∀ q ∈ T.head?, (blk S' F q.2).Nonempty) → ∃ f : ι → Finset W,
      (∀ i ∈ insert i0 S', H i (f i)) ∧
        ∀ i ∈ insert i0 S', ∀ j ∈ insert i0 S', i ≠ j → Disjoint (f i) (f j) := by
    intro hhead
    have hall := all_nonempty hT hhead
    have hlen := length_le_sum T hall
    have hcb := card_bset hT
    have hi0b : i0 ∉ bset S' F T := fun h => hi0 (bset_subset T h)
    have hIcard : (insert i0 (bset S' F T)).card = (bset S' F T).card + 1 := Finset.card_insert_of_notMem hi0b
    have hZ : (verts S' F T).card ≤ 2 * Λ * ((insert i0 (bset S' F T)).card - 1) := by
      have := card_verts hFsz T (fun q hq => hsz _ _ (legal_H hT q hq))
      rw [hIcard, Nat.add_sub_cancel, hcb]
      nlinarith
    obtain ⟨i, hi, e, he, hdisj⟩ := hcond _ (Finset.insert_nonempty _ _) _ hZ
    have hT' : Legal S' F H i0 ((i, e) :: T) := ⟨hT, hhead, hi, he, hdisj⟩
    have hbS : (bset S' F T).card ≤ S'.card := Finset.card_le_card (bset_subset T)
    refine ih _ ?_ F ((i, e) :: T) hFH hFD hT' rfl
    -- the measure decreases
    have hsl := sig_length (S' := S') (F := F) T
    have hk : T.length < M := by rw [hcb] at hbS; omega
    refine pad_lt ⟨T.length, hk⟩ (fun j hj => ?_) ?_
    · simp only [pad, sig]
      have hj' : (j : ℕ) < (sig S' F T).length := by rw [hsl]; exact hj
      rw [List.getD_append _ _ _ _ hj']
    · simp only [pad, sig]
      rw [List.getD_append_right _ _ _ _ (by rw [hsl]), hsl, Nat.sub_self]
      simp only [List.getD_cons_zero]
      rw [List.getD_eq_default _ _ (by rw [hsl])]
      have := Finset.card_le_card (blk_subset (S' := S') (F := F) e)
      omega
  rcases T with _ | ⟨⟨ik, ak⟩, T0⟩
  · exact extend (by simp)
  by_cases hne : (blk S' F ak).Nonempty
  · exact extend (by simpa using hne)
  -- the swapping case
  have hempty : blk S' F ak = ∅ := Finset.not_nonempty_iff_eq_empty.1 hne
  obtain ⟨hT0, hhead0, hik, hHk, hdk⟩ := hT
  have hdisjF : ∀ m ∈ S', Disjoint (F m) ak := by
    intro m hm
    by_contra hc
    have : m ∈ blk S' F ak := Finset.mem_filter.2 ⟨hm, hc⟩
    rw [hempty] at this; simp at this
  rcases Finset.mem_insert.1 hik with hroot | hikb
  · -- the root gets a representative: done
    have hroot' : ik = i0 := hroot
    subst hroot'
    have hHk' : H ik ak := hHk
    refine ⟨Function.update F ik ak, fun i hi => ?_, fun i hi j hj hij => ?_⟩
    · by_cases h : i = ik
      · subst h; simpa using hHk'
      · have hi' : i ∈ S' := (Finset.mem_insert.1 hi).resolve_left h
        rw [Function.update_of_ne h]; exact hFH i hi'
    · by_cases h1 : i = ik
      · subst h1
        have hj' : j ∈ S' := (Finset.mem_insert.1 hj).resolve_left (Ne.symm hij)
        rw [Function.update_self, Function.update_of_ne (Ne.symm hij)]
        exact (hdisjF j hj').symm
      · have hi' : i ∈ S' := (Finset.mem_insert.1 hi).resolve_left h1
        by_cases h2 : j = ik
        · subst h2
          rw [Function.update_self, Function.update_of_ne hij]
          exact hdisjF i hi'
        · have hj' : j ∈ S' := (Finset.mem_insert.1 hj).resolve_left h2
          rw [Function.update_of_ne h1, Function.update_of_ne h2]
          exact hFD i hi' j hj' hij
  -- `ik` is blocking some entry `p` of the tree
  have hikS : ik ∈ S' := bset_subset T0 hikb
  obtain ⟨C, p, A, rfl, hikp⟩ := mem_bset hikb
  set F' := Function.update F ik ak
  have hpA : Legal S' F H i0 (p :: A) := legal_suffix C hT0
  obtain ⟨hA, hheadA, hp1, hpH, hpd⟩ := hpA
  have hak_edge : ∀ q ∈ C ++ p :: A, Disjoint ak q.2 := fun q hq =>
    hdk.mono_right (edge_subset_verts hq)
  have hblk' : ∀ q ∈ C ++ p :: A, blk S' F' q.2 = (blk S' F q.2).erase ik := by
    intro q hq
    ext m
    simp only [blk, Finset.mem_filter, Finset.mem_erase, F']
    by_cases hm : m = ik
    · subst hm; simp only [Function.update_self, ne_eq, not_true_eq_false, false_and,
        iff_false, not_and, not_not]
      exact fun _ => hak_edge q hq
    · rw [Function.update_of_ne hm]; tauto
  -- `ik` does not block the entries of `A`
  have hikA : ∀ q ∈ A, ik ∉ blk S' F q.2 := by
    intro q hq hm
    have h1 := rep_subset_verts (mem_bset_of hq hm)
    have h2 := (Finset.mem_filter.1 hikp).2
    exact h2 (hpd.mono_right h1).symm
  have hcongr := congr_of (S' := S') (F := F) (F' := F') (H := H) (i0 := i0) A (fun q hq => by
    refine ⟨by rw [hblk' q (List.mem_append_right _ (List.mem_cons_of_mem _ hq)),
      Finset.erase_eq_of_notMem (hikA q hq)], fun m hm => ?_⟩
    have : m ≠ ik := fun h => hikA q hq (h ▸ hm)
    simp [F', Function.update_of_ne this])
  obtain ⟨hc1, hc2, hc3, hc4⟩ := hcongr
  have hpblk : blk S' F' p.2 = (blk S' F p.2).erase ik :=
    hblk' p (List.mem_append_right _ List.mem_cons_self)
  have hleg' : Legal S' F' H i0 (p :: A) := by
    refine ⟨hc3.2 hA, fun q hq => ?_, by rw [hc1]; exact hp1, hpH, by rw [hc2]; exact hpd⟩
    rw [(show blk S' F' q.2 = blk S' F q.2 from by
      rw [hblk' q (List.mem_append_right _ (List.mem_cons_of_mem _
        (List.mem_of_mem_head? hq))), Finset.erase_eq_of_notMem
        (hikA q (List.mem_of_mem_head? hq))])]
    exact hheadA q hq
  have hF'H : ∀ i ∈ S', H i (F' i) := by
    intro i hi
    by_cases h : i = ik
    · subst h; simpa [F'] using hHk
    · simp only [F', Function.update_of_ne h]; exact hFH i hi
  have hF'D : ∀ i ∈ S', ∀ j ∈ S', i ≠ j → Disjoint (F' i) (F' j) := by
    intro i hi j hj hij
    by_cases h1 : i = ik
    · subst h1
      simp only [F', Function.update_self, Function.update_of_ne (Ne.symm hij)]
      exact (hdisjF j hj).symm
    · by_cases h2 : j = ik
      · subst h2
        simp only [F', Function.update_self, Function.update_of_ne hij]
        exact hdisjF i hi
      · simp only [F', Function.update_of_ne h1, Function.update_of_ne h2]
        exact hFD i hi j hj hij
  refine ih _ ?_ F' (p :: A) hF'H hF'D hleg' rfl
  -- the measure decreases
  have hallA := all_nonempty hT0 hhead0
  have hlenT0 := length_le_sum _ hallA
  have hcbT0 := card_bset hT0
  have hbS : (bset S' F (C ++ p :: A)).card ≤ S'.card := Finset.card_le_card (bset_subset _)
  have hlenA : A.length < M := by
    have : A.length < (C ++ p :: A).length := by simp; omega
    omega
  have hsA := sig_length (S' := S') (F := F) A
  have hcard_p : 1 ≤ (blk S' F p.2).card := Finset.card_pos.2 ⟨ik, hikp⟩
  have hsig_new : sig S' F' (p :: A) = sig S' F A ++ [(blk S' F p.2).card - 1] := by
    simp only [sig, hc4, hpblk, Finset.card_erase_of_mem hikp]
  have hsig_old : sig S' F ((ik, ak) :: (C ++ p :: A)) =
      (sig S' F A ++ [(blk S' F p.2).card]) ++ (sig S' F C ++ [(blk S' F ak).card]) := by
    simp only [sig, sig_append, List.append_assoc]
  refine pad_lt ⟨A.length, hlenA⟩ (fun j hj => ?_) ?_
  · simp only [pad]
    rw [hsig_new, hsig_old, List.append_assoc]
    have hj' : (j : ℕ) < (sig S' F A).length := by rw [hsA]; exact hj
    rw [List.getD_append _ _ _ _ hj', List.getD_append _ _ _ _ hj']
  · simp only [pad]
    rw [hsig_new, hsig_old, List.append_assoc]
    rw [List.getD_append_right _ _ _ _ (by rw [hsA]),
      List.getD_append_right _ _ _ _ (by rw [hsA]), hsA, Nat.sub_self]
    simp only [List.getD_cons_zero, List.singleton_append]
    omega

/-- **Haxell's theorem** (hypergraph Hall theorem, the form used in Lemma 5.1). -/
theorem haxell [Fintype ι] {H : ι → Finset W → Prop} {Λ : ℕ} (hsz : ∀ i e, H i e → e.card ≤ Λ)
    (hcond : ∀ I : Finset ι, I.Nonempty → ∀ Z : Finset W, Z.card ≤ 2 * Λ * (I.card - 1) →
      ∃ i ∈ I, ∃ e, H i e ∧ Disjoint e Z) :
    ∃ f : ι → Finset W, (∀ i, H i (f i)) ∧ ∀ i j, i ≠ j → Disjoint (f i) (f j) := by
  have key : ∀ S : Finset ι, ∃ f : ι → Finset W, (∀ i ∈ S, H i (f i)) ∧
      ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (f i) (f j) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨fun _ => ∅, by simp, by simp⟩
    | insert i0 S' hi0 ih =>
      obtain ⟨F0, h1, h2⟩ := ih
      exact extend_step hsz hcond S' i0 hi0 F0 h1 h2
  obtain ⟨f, h1, h2⟩ := key Finset.univ
  exact ⟨f, fun i => h1 i (Finset.mem_univ _), fun i j hij =>
    h2 i (Finset.mem_univ _) j (Finset.mem_univ _) hij⟩

end Haxell

end Lovasz
