module
public import RequestProject.Walks

/-!
# Balanced paths

In any finite vertex set `Z` there is a path `P ⊆ Z` such that every component of `Z ∖ P`
contains at most half of a given finite set `B` (the "zero time" of depth-first search in the
proof of Lemma 3.6).
-/

@[expose] public section

open Classical
namespace Lovasz
variable {V : Type*}

/-- Two vertices whose components (inside `s`) each contain more than half of `B` lie in the same
component. -/
lemma heavy_unique {G : SimpleGraph V} {s : Set V} {B : Finset V} {c c' : V}
    (hc : B.card < 2 * (B.filter (fun b => ReachIn G s c b)).card)
    (hc' : B.card < 2 * (B.filter (fun b => ReachIn G s c' b)).card) : ReachIn G s c c' := by
  by_contra hno
  have hdisj : Disjoint (B.filter (fun b => ReachIn G s c b)) (B.filter (fun b => ReachIn G s c' b)) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    exact hno ((Finset.mem_filter.1 hz).2.trans (Finset.mem_filter.1 hz').2.symm)
  have := Finset.card_union_of_disjoint hdisj
  have hsub : B.filter (fun b => ReachIn G s c b) ∪ B.filter (fun b => ReachIn G s c' b) ⊆ B :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have := Finset.card_le_card hsub
  omega

/-- A path `P` inside `Z` such that every component of `Z ∖ P` contains at most half of `B`. -/
theorem exists_balanced_path (G : SimpleGraph V) (Z B : Finset V) :
    ∃ P : List V, IsPathL G P ∧ (∀ v ∈ P, v ∈ Z) ∧
      ∀ c, 2 * (B.filter (fun b => ReachIn G {v | v ∈ Z ∧ v ∉ P} c b)).card ≤ B.card := by
  let R : List V → Set V := fun P => {v | v ∈ Z ∧ v ∉ P}
  let heavy : List V → V → Prop := fun P c =>
    B.card < 2 * (B.filter (fun b => ReachIn G (R P) c b)).card
  let comp : List V → V → Finset V := fun P c => Z.filter (fun z => ReachIn G (R P) c z)
  -- monotonicity of heavy components
  have hmono : ∀ P P' c c', (∀ v, v ∈ P → v ∈ P') → heavy P c → heavy P' c' →
      comp P' c' ⊆ comp P c := by
    intro P P' c c' hPP' hc hc' z hz
    have hRR : R P' ⊆ R P := fun v hv => ⟨hv.1, fun h => hv.2 (hPP' v h)⟩
    have hc'P : heavy P c' := by
      refine lt_of_lt_of_le hc' (Nat.mul_le_mul_left _ (Finset.card_le_card ?_))
      intro b hb
      simp only [Finset.mem_filter] at hb ⊢
      exact ⟨hb.1, hb.2.mono le_rfl hRR⟩
    have hcc' := heavy_unique hc hc'P
    simp only [comp, Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, hcc'.trans (hz.2.mono le_rfl hRR)⟩
  -- extending by a vertex of the heavy component shrinks it
  have hext : ∀ P c v, heavy P c → v ∈ comp P c → ∀ P', (∀ w, w ∈ P → w ∈ P') → v ∈ P' →
      ∀ c', heavy P' c' → (comp P' c').card < (comp P c).card := by
    intro P c v hc hv P' hPP' hvP' c' hc'
    refine Finset.card_lt_card ⟨hmono P P' c c' hPP' hc hc', fun h => ?_⟩
    have := (Finset.mem_filter.1 (h hv)).2.mem_right
    exact this.2 hvP'
  suffices key : ∀ n, ∀ P : List V, IsPathL G P → (∀ v ∈ P, v ∈ Z) →
      (∀ c, heavy P c → 2 * (comp P c).card + P.length ≤ n) →
      ∃ P : List V, IsPathL G P ∧ (∀ v ∈ P, v ∈ Z) ∧ ∀ c, ¬ heavy P c by
    obtain ⟨P, h1, h2, h3⟩ := key (2 * Z.card) [] ⟨List.isChain_nil, List.nodup_nil⟩ (by simp)
      (fun c _ => by simpa using Finset.card_le_card (Finset.filter_subset _ Z))
    exact ⟨P, h1, h2, fun c => not_lt.1 (h3 c)⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P hP hPZ hn
  by_cases hh : ∃ c, heavy P c
  swap
  · push_neg at hh; exact ⟨P, hP, hPZ, hh⟩
  obtain ⟨c, hc⟩ := hh
  have hcR : c ∈ R P := by
    by_contra hcR
    have : B.filter (fun b => ReachIn G (R P) c b) = ∅ :=
      Finset.filter_false_of_mem (fun b _ hb => hcR hb.mem_left)
    simp only [heavy, this] at hc; simp at hc
  have hcc : c ∈ comp P c := Finset.mem_filter.2 ⟨hcR.1, ReachIn.refl hcR⟩
  have hnc := hn c hc
  rcases List.eq_nil_or_concat P with rfl | ⟨P0, l, rfl⟩
  swap
  all_goals try simp only [List.concat_eq_append] at *
  swap
  · -- start the path at `c`
    have hpos := Finset.card_pos.2 ⟨c, hcc⟩
    refine ih (n - 1) (by simp at hnc; omega) [c] (isPathL_singleton c)
      (by simpa using hcR.1) (fun c' hc' => ?_)
    have := hext [] c c hc hcc [c] (by simp) (by simp) c' hc'
    simp at hnc ⊢; omega
  by_cases hadj : ∃ v ∈ comp (P0 ++ [l]) c, G.Adj l v
  · obtain ⟨v, hv, hlv⟩ := hadj
    have hvR : v ∈ R (P0 ++ [l]) := (Finset.mem_filter.1 hv).2.mem_right
    have hP' : IsPathL G (P0 ++ [l] ++ [v]) := by
      refine ⟨?_, ?_⟩
      · exact List.isChain_append.2 ⟨hP.1, List.isChain_singleton v, by
          intro a ha b hb; simp at ha hb; subst ha hb; exact hlv⟩
      · exact List.nodup_append.2 ⟨hP.2, List.nodup_singleton v, by
          intro a ha b hb hab; simp at hb; subst hb hab; exact hvR.2 ha⟩
    have hlen : (P0 ++ [l] ++ [v]).length = (P0 ++ [l]).length + 1 := by simp
    have hlen' : (P0 ++ [l]).length = P0.length + 1 := by simp
    refine ih (2 * (comp (P0 ++ [l]) c).card + (P0 ++ [l]).length - 1) (by omega) _ hP' ?_ ?_
    · intro w hw; simp only [List.mem_append, List.mem_singleton] at hw
      rcases hw with (hw | hw) | rfl
      · exact hPZ w (by simp [hw])
      · exact hPZ w (by simp [hw])
      · exact hvR.1
    · intro c' hc'
      have := hext _ c v hc hv (P0 ++ [l] ++ [v]) (by intro w hw; simp at hw ⊢; tauto)
        (by simp) c' hc'
      omega
  · push_neg at hadj
    -- drop the last vertex; the heavy component is unchanged
    have hcomp : comp P0 c = comp (P0 ++ [l]) c := by
      ext z
      simp only [comp, Finset.mem_filter]
      refine and_congr_right (fun _ => ⟨fun h => ?_, fun h => h.mono le_rfl ?_⟩)
      · refine ReachIn.closed (Q := fun z => ReachIn G (R (P0 ++ [l])) c z)
          (ReachIn.refl hcR) ?_ h
        intro a b ha _ hb hab
        have hbl : b ≠ l := by
          rintro rfl
          exact hadj a (Finset.mem_filter.2 ⟨ha.mem_right.1, ha⟩) hab.symm
        refine ha.tail hab ⟨hb.1, ?_⟩
        simp only [List.mem_append, List.mem_singleton, not_or]
        exact ⟨hb.2, hbl⟩
      · intro w hw; exact ⟨hw.1, fun h => hw.2 (by simp [h])⟩
    have hsame : (B.filter (fun b => ReachIn G (R P0) c b)) =
        B.filter (fun b => ReachIn G (R (P0 ++ [l])) c b) → heavy P0 c := by
      intro h; simp only [heavy, h]; exact hc
    have hcP0 : heavy P0 c := by
      apply hsame
      ext b
      simp only [Finset.mem_filter]
      refine and_congr_right (fun _ => ?_)
      constructor
      · intro h
        have hz : b ∈ comp P0 c := Finset.mem_filter.2 ⟨h.mem_right.1, h⟩
        rw [hcomp] at hz; exact (Finset.mem_filter.1 hz).2
      · intro h
        have hz : b ∈ comp (P0 ++ [l]) c := Finset.mem_filter.2 ⟨h.mem_right.1, h⟩
        rw [← hcomp] at hz; exact (Finset.mem_filter.1 hz).2
    refine ih (2 * (comp (P0 ++ [l]) c).card + P0.length) (by simp at hnc; omega) P0
      (hP.prefix ⟨[l], rfl⟩) (fun w hw => hPZ w (by simp [hw])) ?_
    intro c' hc'
    have hsub := hmono P0 P0 c c' (fun _ h => h) hcP0 hc'
    have := Finset.card_le_card hsub
    rw [hcomp] at this
    omega

end Lovasz
