module
public import RequestProject.Normalize

/-!
# Pieces: realising arcs of the interval graph

An arc `P = I₀ I₁ … I_m` of the interval graph is realised in `L ∪ M` by a path which, inside
each interval `I_k`, runs along a segment, and passes from `I_k` to `I_{k+1}` along a chosen
matching edge `me I_k I_{k+1}`.
-/

@[expose] public section


open Classical

namespace Lovasz

namespace Geo

variable {V ι β : Type*} (g : Geo V ι β)

/-- Extending a strand ending at `lt σ` by the inner vertices of a path `π` from `lt σ` to `p'`. -/
lemma StrandOK.extendPath {act act' : V → Prop} {σ π : List V} (h : g.StrandOK act σ)
    (hle : ∀ v, act' v → act v) (hπh : π.head? = some (g.lt σ)) {p' : V}
    (hπl : π.getLast? = some p') (hπ2 : 2 ≤ π.length) (hπc : π.IsChain g.Γ.Adj)
    (hna : ∀ v ∈ π.dropLast, ¬ act' v) :
    g.StrandOK act' (σ ++ sInner π) ∧ g.hd (σ ++ sInner π) = g.hd σ ∧
      ¬ act' (g.lt (σ ++ sInner π)) ∧ g.Γ.Adj (g.lt (σ ++ sInner π)) p' ∧
      countPairs g.Mp (σ ++ sInner π) + (if g.Mp (g.lt (σ ++ sInner π)) p' then 1 else 0) =
        countPairs g.Mp σ + countPairs g.Mp π := by
  set p := g.lt σ with hp
  set X := sInner π with hX
  have hne' := g.ne_nil_of_strand h
  have hπe : π = p :: (X ++ [p']) := eq_cons_sInner_append hπh hπl hπ2
  have hdl : π.dropLast = p :: X := by rw [hπe, ← List.cons_append, List.dropLast_concat]
  have hnaX : ∀ x ∈ X, ¬ act' x := fun x hx => hna x (by rw [hdl]; simp [hx])
  have hnap : ¬ act' p := hna p (by rw [hdl]; simp)
  have hσ := g.strand_tail_eq h
  rw [← hp] at hσ
  have hpX : ((p :: X) ++ [p']).IsChain g.Γ.Adj := by rw [List.cons_append, ← hπe]; exact hπc
  have hpXc := hpX
  rw [List.isChain_append] at hpX
  have hlast : (σ ++ X).getLast? = (p :: X).getLast? := by
    conv_lhs => rw [← List.dropLast_append_getLast hne']
    rw [List.append_assoc, List.singleton_append, List.getLast?_append_of_ne_nil _ (by simp)]
    rw [← g.lt_eq_getLast hne']
  have hlt : g.lt (σ ++ X) = (p :: X).getLast (by simp) := by
    unfold lt; rw [List.getLastD_eq_getLast?, hlast, List.getLast?_eq_some_getLast (by simp)]; rfl
  have hltna : ¬ act' (g.lt (σ ++ X)) := by
    rw [hlt]
    rcases List.mem_cons.1 (List.getLast_mem (l := p :: X) (by simp)) with h1 | h1
    · rw [h1]; exact hnap
    · exact hnaX _ h1
  have hhd : g.hd (σ ++ X) = g.hd σ := by
    obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hne'; rfl
  have hadj : g.Γ.Adj (g.lt (σ ++ X)) p' := by
    rw [hlt]; exact hpX.2.2 _ (List.getLast?_eq_some_getLast (by simp)) _ rfl
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hhd, hltna, hadj, ?_⟩
  · have := h.two_le; simp; omega
  · refine List.IsChain.append h.chain (List.IsChain.tail hpX.1) ?_
    intro x hx y hy
    rw [List.getLast?_eq_some_getLast hne', Option.mem_def, Option.some.injEq,
      ← g.lt_eq_getLast hne'] at hx
    subst hx
    obtain ⟨z, X', hz⟩ : ∃ z X', X = z :: X' := by
      cases hX' : X with
      | nil => rw [hX'] at hy; simp at hy
      | cons z X' => exact ⟨z, X', rfl⟩
    rw [hz] at hy hpX
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    subst hy
    exact (List.isChain_cons_cons.1 hpX.1).1
  · intro v hv hact
    have hv' : v ∈ sInner σ ++ [p] ++ X := by
      have : sInner (σ ++ X) ⊆ sInner σ ++ [p] ++ X := by
        unfold sInner
        conv_lhs => rw [hσ]
        simp only [List.cons_append, List.tail_cons]
        intro x hx
        have := List.dropLast_subset _ hx
        simpa [sInner, List.append_assoc] using this
      exact this hv
    simp only [List.mem_append, List.mem_singleton] at hv'
    rcases hv' with (h1 | rfl) | h1
    · exact h.inner_na v h1 (hle v hact)
    · exact hnap hact
    · exact hnaX v h1 hact
  · intro ha; rw [hhd] at ha ⊢; exact h.hd_bd (hle _ ha)
  · intro ha; exact absurd ha hltna
  · -- counting matching edges
    have hσX : σ ++ X ≠ [] := by simp [hne']
    have e1 : countPairs g.Mp ((σ ++ X) ++ [p']) = countPairs g.Mp (σ ++ X) +
        (if g.Mp (g.lt (σ ++ X)) p' then 1 else 0) := by
      rw [countPairs_append _ _ _ hσX (by simp), ← g.lt_eq_getLast hσX]
      simp [countPairs] <;> rfl
    have e2 : countPairs g.Mp (σ ++ (X ++ [p'])) = countPairs g.Mp σ +
        (if g.Mp p ((X ++ [p']).head (by simp)) then 1 else 0) + countPairs g.Mp (X ++ [p']) := by
      rw [countPairs_append _ _ _ hne' (by simp), ← g.lt_eq_getLast hne']
    have e3 : countPairs g.Mp π = (if g.Mp p ((X ++ [p']).head (by simp)) then 1 else 0) +
        countPairs g.Mp (X ++ [p']) := by
      rw [hπe]
      obtain ⟨z, t, hz⟩ := List.exists_cons_of_ne_nil (show X ++ [p'] ≠ [] by simp)
      simp only [hz, List.head_cons]
      rfl
    rw [← e1, List.append_assoc, e2, e3]
    ring

/-- The segments realising an interval path `P` from `u` to `w`, passing from each interval to
the next along the matching edge `me I I'`. -/
def realP (me : ι → ι → V × V) : V → List ι → V → List (List V)
  | u, I :: I' :: rest, w => g.seg u (me I I').1 :: realP me (me I I').2 (I' :: rest) w
  | u, _, w => [g.seg u w]

/-- The chosen matching edges along an interval path are matching edges between the right
intervals. -/
def MeOK (me : ι → ι → V × V) (P : List ι) : Prop :=
  ∀ q ∈ lpairs P, g.ivOf (me q.1 q.2).1 = some q.1 ∧ g.ivOf (me q.1 q.2).2 = some q.2 ∧
    g.Mp (me q.1 q.2).1 (me q.1 q.2).2

/-- The properties of a segment. -/
def SegOK (I : ι) (s : List V) : Prop :=
  (∀ v ∈ s, g.ivOf v = some I) ∧ s.Nodup ∧ s.IsChain g.Γ.Adj ∧ s ≠ []

lemma segOK_seg {I : ι} {u v : V} (hu : g.ivOf u = some I) (hv : g.ivOf v = some I) :
    g.SegOK I (g.seg u v) := by
  refine ⟨g.seg_iv hu hv, g.seg_nodup hu hv, g.seg_chain hu hv, fun h => ?_⟩
  have := g.seg_head hu hv; rw [h] at this; simp at this

lemma realP_spec (me : ι → ι → V × V) : ∀ (P : List ι) (u w : V) (I : ι), P.head? = some I →
    g.ivOf u = some I → (∀ J, P.getLast? = some J → g.ivOf w = some J) → g.MeOK me P →
    List.Forall₂ g.SegOK P (g.realP me u P w) ∧
    (g.realP me u P w).flatten.IsChain g.Γ.Adj ∧
    (g.realP me u P w).flatten.head? = some u ∧ (g.realP me u P w).flatten.getLast? = some w ∧
    P.length - 1 ≤ countPairs g.Mp (g.realP me u P w).flatten
  | [], _, _, _, h, _, _, _ => by simp at h
  | [I], u, w, I', h, hu, hw, _ => by
    simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    have hw' := hw I rfl
    have hs := g.segOK_seg hu hw'
    refine ⟨List.Forall₂.cons hs List.Forall₂.nil, ?_, ?_, ?_, by simp⟩
    · simpa [realP] using hs.2.2.1
    · simpa [realP] using g.seg_head hu hw'
    · simpa [realP] using g.seg_last hu hw'
  | I :: I' :: rest, u, w, I'', h, hu, hw, hme => by
    simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    have hq := hme (I, I') (by simp)
    obtain ⟨ha, hb, hab⟩ := hq
    set a := (me I I').1
    set b := (me I I').2
    have hme' : g.MeOK me (I' :: rest) := fun q hq => hme q (by simp [hq])
    have hw' : ∀ J, (I' :: rest).getLast? = some J → g.ivOf w = some J := fun J hJ =>
      hw J (by rw [List.getLast?_cons_cons]; exact hJ)
    obtain ⟨ih1, ih2, ih3, ih4, ih5⟩ := realP_spec me (I' :: rest) b w I' rfl hb hw' hme'
    have e : g.realP me u (I :: I' :: rest) w = g.seg u a :: g.realP me b (I' :: rest) w := rfl
    rw [e]
    have hs := g.segOK_seg hu ha
    set T := (g.realP me b (I' :: rest) w).flatten
    have hT : T ≠ [] := by intro h; rw [h] at ih3; simp at ih3
    refine ⟨List.Forall₂.cons hs ih1, ?_, ?_, ?_, ?_⟩
    · rw [List.flatten_cons]
      refine List.IsChain.append hs.2.2.1 ih2 ?_
      intro x hx y hy
      rw [g.seg_last hu ha, Option.mem_def, Option.some.injEq] at hx
      rw [ih3, Option.mem_def, Option.some.injEq] at hy
      subst hx hy
      exact g.Mp_adj hab
    · rw [List.flatten_cons, List.head?_append, g.seg_head hu ha]; rfl
    · rw [List.flatten_cons, List.getLast?_append_of_ne_nil _ hT, ih4]
    · rw [List.flatten_cons, countPairs_append _ _ _ hs.2.2.2 hT]
      have hl : (g.seg u a).getLast hs.2.2.2 = a := by
        have := g.seg_last hu ha
        rw [List.getLast?_eq_some_getLast hs.2.2.2, Option.some.injEq] at this; exact this
      have hh : T.head hT = b := by
        rw [List.head?_eq_some_head hT, Option.some.injEq] at ih3; exact ih3
      rw [hl, hh, if_pos hab]
      simp only [List.length_cons] at ih5 ⊢
      omega

lemma realP_head_seg (me : ι → ι → V × V) (u w : V) (I I' : ι) (rest : List ι) :
    (g.realP me u (I :: I' :: rest) w).head? = some (g.seg u (me I I').1) := rfl

lemma realP_last_seg (me : ι → ι → V × V) : ∀ (P : List ι) (u w : V) (J J' : ι),
    (lpairs P).getLast? = some (J, J') → (g.realP me u P w).getLast? = some (g.seg (me J J').2 w)
  | [], _, _, _, _, h => by simp at h
  | [_], _, _, _, _, h => by simp at h
  | [I, I'], u, w, J, J', h => by
    simp only [lpairs_cons_cons, lpairs_singleton, List.getLast?_singleton, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | I :: I' :: I'' :: rest, u, w, J, J', h => by
    have e : g.realP me u (I :: I' :: I'' :: rest) w =
        g.seg u (me I I').1 :: g.realP me (me I I').2 (I' :: I'' :: rest) w := rfl
    rw [e, List.getLast?_cons, realP_last_seg me (I' :: I'' :: rest) _ w J J' (by
      rw [lpairs_cons_cons, lpairs_cons_cons, List.getLast?_cons_cons] at h; rwa [lpairs_cons_cons])]
    rfl

end Geo

end Lovasz
