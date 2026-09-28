module
public import RequestProject.Assemble

/-!
# The linking step at a block

Given a normalised family of runs at the block `G` and arcs of the interval graph of `G`
joining the end of each run to the start of the next (as provided by Lemma 2.6), we realise
the arcs by pieces and splice them into the runs, obtaining a circuit in which `G` is no longer
active and which uses at least as many matching edges as the length of any of the arcs.
-/

@[expose] public section


open Classical

namespace Lovasz

section lists

variable {α γ : Type*}

lemma rel_of_mem_lpairs {r : α → α → Prop} : ∀ {l : List α}, l.IsChain r →
    ∀ q ∈ lpairs l, r q.1 q.2
  | [], _, q, hq => by simp at hq
  | [_], _, q, hq => by simp at hq
  | a :: b :: t, h, q, hq => by
    rw [lpairs_cons_cons, List.mem_cons] at hq
    rw [List.isChain_cons_cons] at h
    rcases hq with rfl | hq
    · exact h.1
    · exact rel_of_mem_lpairs h.2 q hq

lemma forall₂_getD {R : α → γ → Prop} {l₁ : List α} {l₂ : List γ} (h : List.Forall₂ R l₁ l₂)
    {i : ℕ} (hi : i < l₁.length) (d₁ : α) (d₂ : γ) : R (l₁.getD i d₁) (l₂.getD i d₂) := by
  have hl := h.length_eq
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (hl ▸ hi)]
  exact (List.forall₂_iff_get.1 h).2 i hi (hl ▸ hi)

/-- The keys of the segments of an arc: its intervals, the last one marked. -/
def arcKeys (d : α) (P : List α) : List (α × Bool) :=
  P.dropLast.map (fun I => (I, false)) ++ [(P.getLastD d, true)]

lemma length_arcKeys (d : α) {P : List α} (hP : P ≠ []) : (arcKeys d P).length = P.length := by
  have := List.length_pos_iff.2 hP
  simp [arcKeys]; omega

lemma mem_zip_arcKeys {d : α} {P : List α} {S : List γ} (hl : S.length = P.length)
    (h2 : 2 ≤ P.length) {x : (α × Bool) × γ} (hx : x ∈ (arcKeys d P).zip S) :
    ∃ m, ∃ hm : m < P.length, x.2 = S[m]'(hl ▸ hm) ∧ x.1.1 = P[m] ∧
      ((x.1.2 = false ∧ (m = 0 ∨ x.1.1 ∈ arcInner P)) ∨ (x.1.2 = true ∧ m = P.length - 1)) := by
  have hP : P ≠ [] := by rintro rfl; simp at h2
  obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.1 hx
  have hm' : m < P.length := by
    simp only [List.length_zip, length_arcKeys d hP, hl, min_self] at hm; exact hm
  refine ⟨m, hm', by simp, ?_⟩
  simp only [List.getElem_zip]
  by_cases hml : m < P.length - 1
  · have hk : m < (P.dropLast.map (fun I => (I, false))).length := by simp; omega
    have e : (arcKeys d P)[m]'(by rw [length_arcKeys d hP]; exact hm') = (P[m], false) := by
      unfold arcKeys
      rw [List.getElem_append_left hk]; simp [List.getElem_dropLast]
    rw [e]
    refine ⟨rfl, Or.inl ⟨rfl, ?_⟩⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · exact Or.inl rfl
    · right
      unfold arcInner
      have hlen : m - 1 < P.tail.dropLast.length := by simp; omega
      have : P.tail.dropLast[m - 1] = P[m] := by
        rw [List.getElem_dropLast, List.getElem_tail]; congr 1; omega
      rw [← this]; exact List.getElem_mem hlen
  · have hml' : m = P.length - 1 := by omega
    have hk : (P.dropLast.map (fun I => (I, false))).length ≤ m := by simp; omega
    have e : (arcKeys d P)[m]'(by rw [length_arcKeys d hP]; exact hm') = (P[m], true) := by
      unfold arcKeys
      rw [List.getElem_append_right hk]
      simp only [List.getElem_singleton, Prod.mk.injEq, and_true]
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?,
        List.getElem?_eq_getElem (show P.length - 1 < P.length by omega), Option.getD_some]
      subst hml'; rfl
    rw [e]
    exact ⟨rfl, Or.inr ⟨rfl, hml'⟩⟩

lemma dropLast_eq_cons_inner {P : List α} {y : α} (h : P.head? = some y) (h2 : 2 ≤ P.length) :
    P.dropLast = y :: arcInner P := by
  match P, h, h2 with
  | a :: b :: t, h, _ =>
    simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    simp [arcInner]

lemma mem_arcKeys_false {d : α} {P : List α} {I : α} (h : (I, false) ∈ arcKeys d P) :
    I ∈ P.dropLast := by
  unfold arcKeys at h
  simp only [List.mem_append, List.mem_map, List.mem_singleton, Prod.mk.injEq] at h
  rcases h with ⟨J, hJ, rfl, -⟩ | ⟨-, h⟩
  · exact hJ
  · exact absurd h (by decide)

lemma mem_arcKeys_true {d : α} {P : List α} {I : α} (h : (I, true) ∈ arcKeys d P) :
    I = P.getLastD d := by
  unfold arcKeys at h
  simp only [List.mem_append, List.mem_map, List.mem_singleton, Prod.mk.injEq] at h
  rcases h with ⟨J, -, -, h⟩ | ⟨h, -⟩
  · exact absurd h (by decide)
  · exact h

lemma arcKeys_nodup {d : α} {P : List α} (h : P.dropLast.Nodup) : (arcKeys d P).Nodup := by
  unfold arcKeys
  rw [List.nodup_append]
  refine ⟨h.map (fun a b hab => by simpa using hab), by simp, ?_⟩
  intro a ha b hb hab
  subst hab
  simp only [List.mem_map] at ha
  obtain ⟨J, -, rfl⟩ := ha
  simp at hb

end lists

namespace Geo

variable {V ι β : Type*} (g : Geo V ι β)

/-- The intervals of the block `G`. -/
def GI (G : β) : Set ι := {I | g.blk I = some G}

lemma actI_diff_GI (A : Set ι) (G : β) (v : V) :
    g.actI (A \ g.GI G) v ↔ g.actI A v ∧ g.vb v ≠ some G := by
  constructor
  · rintro ⟨J, h1, h2, h3⟩
    refine ⟨⟨J, h1, h2⟩, fun h => h3 ?_⟩
    unfold vb at h; rw [h1, Option.bind_some] at h; exact h
  · rintro ⟨⟨J, h1, h2⟩, h3⟩
    refine ⟨J, h1, h2, fun h => h3 ?_⟩
    unfold vb; rw [h1, Option.bind_some]; exact h

lemma not_actI_of_vb {A : Set ι} {G : β} {v : V} (h : g.vb v = some G) :
    ¬ g.actI (A \ g.GI G) v := fun h' => ((g.actI_diff_GI A G v).1 h').2 h

lemma JoinOK.deactG {A : Set ι} {G : β} {u v : V} (h : g.JoinOK (g.actI A) u v)
    (hn : ¬ (g.actI A u ∧ g.vb u = some G)) : g.JoinOK (g.actI (A \ g.GI G)) u v := by
  rcases h with ⟨h1, h2, G', h3, h4⟩ | ⟨h1, h2, h3⟩
  · have hG' : G' ≠ G := by rintro rfl; exact hn ⟨h1, h3⟩
    refine Or.inl ⟨(g.actI_diff_GI A G u).2 ⟨h1, by rw [h3]; simpa using hG'⟩,
      (g.actI_diff_GI A G v).2 ⟨h2, by rw [h4]; simpa using hG'⟩, G', h3, h4⟩
  · exact Or.inr ⟨fun h' => h1 ((g.actI_diff_GI A G u).1 h').1,
      fun h' => h2 ((g.actI_diff_GI A G v).1 h').1, h3⟩

/-- The data of an interval graph `H` on intervals `U` of the block `G`, whose edges are realised
by the matching edges `me I I'`. -/
structure BlockOK (G : β) (H : SimpleGraph ι) (U : Finset ι) (me : ι → ι → V × V) : Prop where
  blk_U : ∀ I ∈ U, g.blk I = some G
  me_iv1 : ∀ {I I'}, H.Adj I I' → g.ivOf (me I I').1 = some I
  me_iv2 : ∀ {I I'}, H.Adj I I' → g.ivOf (me I I').2 = some I'
  me_M : ∀ {I I'}, H.Adj I I' → g.Mp (me I I').1 (me I I').2
  me_swap : ∀ {I I'}, H.Adj I I' → me I' I = ((me I I').2, (me I I').1)

/-- The departure vertex of an arc. -/
def dep (me : ι → ι → V × V) (P : List ι) : V := (me (P.getD 0 g.dI) (P.getD 1 g.dI)).1

/-- The arrival vertex of an arc. -/
def arr (me : ι → ι → V × V) (P : List ι) : V :=
  (me ((lpairs P).getLastD (g.dI, g.dI)).1 ((lpairs P).getLastD (g.dI, g.dI)).2).2

/-- The segments realising the `i`-th arc, from the end of the `i`-th run to the start of the
next one. -/
def segsAt (me : ι → ι → V × V) (Rs : List (List (List V))) (As : List (List ι)) (i : ℕ) :
    List (List V) :=
  g.realP me (g.rlt (Rs.getD i [])) (As.getD i []) (g.rhd (Rs.getD ((i + 1) % Rs.length) []))

/-- The hypotheses of the linking step. -/
structure LinkPre (A : Set ι) (G : β) (H : SimpleGraph ι) (U B : Finset ι) (me : ι → ι → V × V)
    (Rs : List (List (List V))) (As : List (List ι)) : Prop where
  blk : g.BlockOK G H U me
  runs : g.RunsOK (g.actI A) G Rs
  disj : (Rs.map g.junc).Pairwise JDisj
  inB : ∀ R ∈ Rs, ∀ v ∈ R.flatten, g.vb v = some G → g.iv v ∈ B
  arcs : List.Forall₂ (ArcOK H U B) (demands (Rs.map g.junc)) As
  inner : (As.flatMap arcInner).Nodup
  edges : (As.flatMap arcEdges).Nodup

/-- The hypotheses of the linking step, including the orientation of runs whose two ends lie in
the same interval. -/
structure LinkHyp (A : Set ι) (G : β) (H : SimpleGraph ι) (U B : Finset ι) (me : ι → ι → V × V)
    (Rs : List (List (List V))) (As : List (List ι)) : Prop
    extends g.LinkPre A G H U B me Rs As where
  orient : ∀ i (hi : i < Rs.length), g.iv (g.rhd Rs[i]) = g.iv (g.rlt Rs[i]) →
    (g.seg (g.rlt Rs[i]) (g.dep me (As.getD i []))).Disjoint
      (g.seg (g.arr me (As.getD ((i + Rs.length - 1) % Rs.length) [])) (g.rhd Rs[i]))

variable {g}

section facts

variable {A : Set ι} {G : β} {H : SimpleGraph ι} {U B : Finset ι} {me : ι → ι → V × V}
  {Rs : List (List (List V))} {As : List (List ι)}

lemma LinkPre.len_pos (h : g.LinkPre A G H U B me Rs As) : 0 < Rs.length :=
  List.length_pos_iff.2 h.runs.ne

lemma LinkPre.len_arcs (h : g.LinkPre A G H U B me Rs As) : As.length = Rs.length := by
  rw [← h.arcs.length_eq, demands_length, List.length_map]

lemma LinkPre.run (h : g.LinkPre A G H U B me Rs As) {i : ℕ} (hi : i < Rs.length) :
    g.RunOK (g.actI A) G (Rs.getD i []) :=
  h.runs.run _ (by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi)

lemma LinkPre.arc (h : g.LinkPre A G H U B me Rs As) {i : ℕ} (hi : i < Rs.length) :
    ArcOK H U B (g.iv (g.rlt (Rs.getD i [])), g.iv (g.rhd (Rs.getD ((i + 1) % Rs.length) [])))
      (As.getD i []) := by
  have h1 := forall₂_getD h.arcs (i := i) (by rw [demands_length, List.length_map]; exact hi)
    (g.dI, g.dI) []
  have hk := h.len_pos
  have hi' : i < (demands (Rs.map g.junc)).length := by rw [demands_length, List.length_map]; exact hi
  rw [List.getD_eq_getElem _ _ hi', demands_getElem] at h1
  have hi2 : (i + 1) % Rs.length < Rs.length := Nat.mod_lt _ hk
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi2]
  simpa [junc] using h1

lemma blk_of_vb {v : V} {I : ι} {G : β} (hI : g.ivOf v = some I) (hG : g.vb v = some G) :
    g.blk I = some G := by
  unfold vb at hG; rwa [hI, Option.bind_some] at hG

lemma vb_of_blk {v : V} {I : ι} {G : β} (hI : g.ivOf v = some I) (hG : g.blk I = some G) :
    g.vb v = some G := by
  unfold vb; rwa [hI, Option.bind_some]

lemma LinkPre.seg_spec (h : g.LinkPre A G H U B me Rs As) {i : ℕ} (hi : i < Rs.length) :
    List.Forall₂ g.SegOK (As.getD i []) (g.segsAt me Rs As i) ∧
    (g.segsAt me Rs As i).flatten.IsChain g.Γ.Adj ∧
    (g.segsAt me Rs As i).flatten.head? = some (g.rlt (Rs.getD i [])) ∧
    (g.segsAt me Rs As i).flatten.getLast? = some (g.rhd (Rs.getD ((i + 1) % Rs.length) [])) ∧
    (As.getD i []).length - 1 ≤ countPairs g.Mp (g.segsAt me Rs As i).flatten := by
  have harc := h.arc hi
  have hi2 : (i + 1) % Rs.length < Rs.length := Nat.mod_lt _ h.len_pos
  refine g.realP_spec me _ _ _ _ harc.1 (g.iv_of_actI (h.run hi).lt_act) ?_ ?_
  · intro J hJ
    rw [harc.2.1, Option.some.injEq] at hJ
    rw [← hJ]; exact g.iv_of_actI (h.run hi2).hd_act
  · intro q hq
    have hadj := rel_of_mem_lpairs harc.2.2.1 q hq
    exact ⟨h.blk.me_iv1 hadj, h.blk.me_iv2 hadj, h.blk.me_M hadj⟩

lemma LinkPre.blk_arc (h : g.LinkPre A G H U B me Rs As) {i : ℕ} (hi : i < Rs.length) {I : ι}
    (hI : I ∈ As.getD i []) :
    g.blk I = some G ∧ (I ∈ B → I = g.iv (g.rlt (Rs.getD i [])) ∨
      I = g.iv (g.rhd (Rs.getD ((i + 1) % Rs.length) []))) := by
  have harc := h.arc hi
  have hi2 : (i + 1) % Rs.length < Rs.length := Nat.mod_lt _ h.len_pos
  rcases (mem_iff_inner harc.1 harc.2.1 harc.2.2.2.1).1 hI with rfl | hin | rfl
  · exact ⟨blk_of_vb (g.iv_of_actI (h.run hi).lt_act) (h.run hi).lt_G, fun _ => Or.inl rfl⟩
  · have := harc.2.2.2.2 I hin
    exact ⟨h.blk.blk_U I this.1, fun hB => absurd hB this.2⟩
  · exact ⟨blk_of_vb (g.iv_of_actI (h.run hi2).hd_act) (h.run hi2).hd_G, fun _ => Or.inr rfl⟩

lemma LinkPre.piece_vb (h : g.LinkPre A G H U B me Rs As) {i : ℕ} (hi : i < Rs.length) {v : V}
    (hv : v ∈ (g.segsAt me Rs As i).flatten) :
    ∃ I ∈ As.getD i [], g.ivOf v = some I ∧ g.vb v = some G := by
  obtain ⟨sg, hs, hvs⟩ := List.mem_flatten.1 hv
  obtain ⟨I, hI, hIs⟩ := forall₂_mem_right (h.seg_spec hi).1 hs
  have hvI := hIs.1 v hvs
  exact ⟨I, hI, hvI, vb_of_blk hvI (h.blk_arc hi hI).1⟩

lemma two_le_flatten {L : List (List V)} (hL : 2 ≤ L.length) (hne : ∀ s ∈ L, s ≠ []) :
    2 ≤ L.flatten.length := by
  obtain ⟨a, b, t, rfl⟩ : ∃ a b t, L = a :: b :: t := by
    match L, hL with
    | a :: b :: t, _ => exact ⟨a, b, t, rfl⟩
  have ha := List.length_pos_iff.2 (hne a (by simp))
  have hb := List.length_pos_iff.2 (hne b (by simp))
  simp only [List.flatten_cons, List.length_append]
  omega

lemma RunOK.flatten_eq {act : V → Prop} {R : List (List V)} (hR : g.RunOK act G R) :
    R.flatten = g.rhd R :: (sInner R.flatten ++ [g.rlt R]) := by
  obtain ⟨σ, t, rfl⟩ := List.exists_cons_of_ne_nil hR.ne
  have hσ := hR.strand σ (by simp)
  have hσne := g.ne_nil_of_strand hσ
  have hh : (σ :: t).flatten.head? = some (g.rhd (σ :: t)) := by
    rw [List.flatten_cons, List.head?_append, List.head?_eq_some_head hσne]
    change some (σ.head hσne) = some (g.hd σ)
    rw [g.hd_eq_head hσne]
  have hl : (σ :: t).flatten.getLast? = some (g.rlt (σ :: t)) := by
    have hL := List.getLast_mem hR.ne
    have hLne := g.ne_nil_of_strand (hR.strand _ hL)
    have e : (σ :: t).getLastD [] = (σ :: t).getLast hR.ne := by
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hR.ne]; rfl
    unfold rlt; rw [e, g.lt_eq_getLast hLne]
    conv_lhs => rw [← List.dropLast_append_getLast hR.ne]
    rw [List.flatten_append, List.flatten_singleton, List.getLast?_append_of_ne_nil _ hLne,
      List.getLast?_eq_some_getLast hLne]
  refine eq_cons_sInner_append hh hl ?_
  have := hσ.two_le
  simp only [List.flatten_cons, List.length_append]
  omega

omit g in
lemma flat_range (Rs : List (List (List V))) :
    (List.range Rs.length).map (fun i => (Rs.getD i []).flatten) = Rs.map List.flatten := by
  conv_rhs => rw [← range_map_getD Rs []]
  rw [List.map_map]; rfl

lemma LinkPre.run_nodup (h : g.LinkPre A G H U B me Rs As) :
    (∀ i < Rs.length, (Rs.getD i []).flatten.Nodup) ∧
      (List.range Rs.length).Pairwise (fun i j => (Rs.getD i []).flatten.Disjoint
        (Rs.getD j []).flatten) := by
  have hn := h.runs.nodup
  rw [List.flatten_flatten, ← flat_range, List.nodup_flatten, List.pairwise_map] at hn
  exact ⟨fun i hi => hn.1 _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩), hn.2⟩

end facts

omit g in
lemma realP_zero (g : Geo V ι β) (me : ι → ι → V × V) (u w : V) (P : List ι) (h2 : 2 ≤ P.length)
    (h0 : 0 < (g.realP me u P w).length) : (g.realP me u P w)[0] = g.seg u (g.dep me P) := by
  match P, h2 with
  | I :: I' :: rest, _ => rfl

lemma LinkPre.key_mem (h : g.LinkPre A G H U B me Rs As) {i : ℕ} (hi : i < Rs.length)
    {x : (ι × Bool) × List V} (hx : x ∈ (arcKeys g.dI (As.getD i [])).zip (g.segsAt me Rs As i)) :
    (∀ v ∈ x.2, g.ivOf v = some x.1.1) ∧ x.2.Nodup ∧
    ((x.1.2 = false ∧ ((x.1.1 = g.iv (g.rlt (Rs.getD i [])) ∧
        x.2 = g.seg (g.rlt (Rs.getD i [])) (g.dep me (As.getD i []))) ∨
        x.1.1 ∈ arcInner (As.getD i []))) ∨
     (x.1.2 = true ∧ x.1.1 = g.iv (g.rhd (Rs.getD ((i + 1) % Rs.length) [])) ∧
        x.2 = g.seg (g.arr me (As.getD i [])) (g.rhd (Rs.getD ((i + 1) % Rs.length) [])))) := by
  have hs := h.seg_spec hi
  have harc := h.arc hi
  have hl : (g.segsAt me Rs As i).length = (As.getD i []).length := hs.1.length_eq.symm
  obtain ⟨m, hm, hx2, hx1, hcase⟩ := mem_zip_arcKeys hl harc.2.2.2.1 hx
  have hseg := (List.forall₂_iff_get.1 hs.1).2 m hm (hl ▸ hm)
  simp only [List.get_eq_getElem] at hseg
  rw [hx2, hx1]
  refine ⟨hseg.1, hseg.2.1, ?_⟩
  rw [← hx1, ← hx2]
  rcases hcase with ⟨hb, hm0 | hin⟩ | ⟨hb, hml⟩
  · subst hm0
    left
    refine ⟨hb, Or.inl ⟨?_, ?_⟩⟩
    · rw [hx1]
      have := harc.1
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hm] at this
      exact Option.some.inj this
    · rw [hx2]
      exact g.realP_zero me _ _ _ harc.2.2.2.1 _
  · exact Or.inl ⟨hb, Or.inr hin⟩
  · right
    refine ⟨hb, ?_, ?_⟩
    · rw [hx1]
      have := harc.2.1
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem
        (by have := harc.2.2.2.1; omega)] at this
      simp only [hml]
      exact Option.some.inj this
    · rw [hx2]
      have hlp : lpairs (As.getD i []) ≠ [] := by
        intro h0; have h1 := congrArg List.length h0; rw [length_lpairs, List.length_nil] at h1
        have := harc.2.2.2.1; omega
      have hq := List.getLast?_eq_some_getLast hlp
      have hlast := g.realP_last_seg me (As.getD i []) (g.rlt (Rs.getD i []))
        (g.rhd (Rs.getD ((i + 1) % Rs.length) [])) _ _ hq
      have e1 : g.arr me (As.getD i []) = (me ((lpairs (As.getD i [])).getLast hlp).1
          ((lpairs (As.getD i [])).getLast hlp).2).2 := by
        unfold arr; rw [List.getLastD_eq_getLast?, hq]; rfl
      rw [e1]
      unfold segsAt at hl ⊢
      rw [List.getLast?_eq_getElem?] at hlast
      simp only [hml]
      rw [List.getElem?_eq_getElem (by omega)] at hlast
      have := Option.some.inj hlast
      convert this using 2
      omega

lemma LinkPre.jd (h : g.LinkPre A G H U B me Rs As) {i j : ℕ} (hi : i < Rs.length)
    (hj : j < Rs.length) (hij : i ≠ j) : JDisj (g.junc (Rs.getD i [])) (g.junc (Rs.getD j [])) := by
  have hp := List.pairwise_iff_getElem.1 h.disj
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · have := hp i j (by simpa using hi) (by simpa using hj) hlt
    simpa using this
  · have := hp j i (by simpa using hj) (by simpa using hi) hlt
    simp only [List.getElem_map] at this
    unfold JDisj at this ⊢
    exact ⟨fun e => this.1 e.symm, fun e => this.2.2.1 e.symm, fun e => this.2.1 e.symm,
      fun e => this.2.2.2 e.symm⟩

lemma LinkPre.inner_disj (h : g.LinkPre A G H U B me Rs As) {i j : ℕ} (hi : i < Rs.length)
    (hj : j < Rs.length) (hij : i ≠ j) :
    (arcInner (As.getD i [])).Disjoint (arcInner (As.getD j [])) := by
  have hn := h.inner
  rw [List.flatMap_def, List.nodup_flatten] at hn
  have hp := List.pairwise_iff_getElem.1 hn.2
  have hl := h.len_arcs
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · have := hp i j (by simp; omega) (by simp; omega) hlt
    rw [List.getElem_map, List.getElem_map] at this; exact this
  · have := hp j i (by simp; omega) (by simp; omega) hlt
    rw [List.getElem_map, List.getElem_map] at this; exact this.symm

lemma LinkPre.inner_nd (h : g.LinkPre A G H U B me Rs As) {i : ℕ} (hi : i < Rs.length) :
    (arcInner (As.getD i [])).Nodup := by
  have hn := h.inner
  rw [List.flatMap_def, List.nodup_flatten] at hn
  have hl := h.len_arcs
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact hn.1 _ (List.mem_map.2 ⟨_, List.getElem_mem (by omega), rfl⟩)

lemma LinkPre.yB (h : g.LinkPre A G H U B me Rs As) {i : ℕ} (hi : i < Rs.length) :
    g.iv (g.rlt (Rs.getD i [])) ∈ B :=
  h.inB _ (by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi) _
    (g.rlt_mem (h.run hi)) (h.run hi).lt_G

lemma LinkPre.xB (h : g.LinkPre A G H U B me Rs As) {i : ℕ} (hi : i < Rs.length) :
    g.iv (g.rhd (Rs.getD i [])) ∈ B :=
  h.inB _ (by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi) _
    (g.rhd_mem (h.run hi)) (h.run hi).hd_G

lemma LinkPre.inner_nB (h : g.LinkPre A G H U B me Rs As) {i : ℕ} (hi : i < Rs.length) {I : ι}
    (hI : I ∈ arcInner (As.getD i [])) : I ∉ B :=
  ((h.arc hi).2.2.2.2 I hI).2

lemma LinkPre.dropLast_nd (h : g.LinkPre A G H U B me Rs As) {i : ℕ} (hi : i < Rs.length) :
    (As.getD i []).dropLast.Nodup := by
  have harc := h.arc hi
  rw [dropLast_eq_cons_inner harc.1 harc.2.2.2.1, List.nodup_cons]
  exact ⟨fun hy => h.inner_nB hi hy (h.yB hi), h.inner_nd hi⟩

/-- The pieces are pairwise disjoint paths. -/
lemma LinkHyp.pieces_nodup (h : g.LinkHyp A G H U B me Rs As) :
    ((List.range Rs.length).map (fun i => (g.segsAt me Rs As i).flatten)).flatten.Nodup := by
  set k := Rs.length with hk
  have hk0 := h.len_pos
  have hnx : ∀ i, (i + 1) % k < k := fun i => Nat.mod_lt _ hk0
  set Z : ℕ → List ((ι × Bool) × List V) :=
    fun i => (arcKeys g.dI (As.getD i [])).zip (g.segsAt me Rs As i) with hZ
  set KL := ((List.range k).map Z).flatten with hKL
  have hlenK : ∀ i, i < k →
      (arcKeys g.dI (As.getD i [])).length = (g.segsAt me Rs As i).length := fun i hi => by
    have harc := h.arc hi
    rw [length_arcKeys _ (List.ne_nil_of_length_pos (by have := harc.2.2.2.1; omega)),
      (h.seg_spec hi).1.length_eq]
  have e : (KL.map Prod.snd).flatten =
      ((List.range k).map (fun i => (g.segsAt me Rs As i).flatten)).flatten := by
    rw [hKL, List.map_flatten, List.map_map]
    have : (List.range k).map (List.map Prod.snd ∘ Z) = (List.range k).map (g.segsAt me Rs As) :=
      List.map_congr_left fun i hi => List.map_snd_zip (le_of_eq (hlenK i (List.mem_range.1 hi)).symm)
    rw [this, List.flatten_flatten, List.map_map]; rfl
  have eK : KL.map Prod.fst = ((List.range k).map (fun i => arcKeys g.dI (As.getD i []))).flatten := by
    rw [hKL, List.map_flatten, List.map_map]
    congr 1
    exact List.map_congr_left fun i hi => List.map_fst_zip (le_of_eq (hlenK i (List.mem_range.1 hi)))
  have hmemKL : ∀ x ∈ KL, ∃ i, i < k ∧ x ∈ Z i := by
    intro x hx
    obtain ⟨_, hl, hxl⟩ := List.mem_flatten.1 hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hl
    exact ⟨i, List.mem_range.1 hi, hxl⟩
  have hgl : ∀ i, i < k → (As.getD i []).getLastD g.dI = g.iv (g.rhd (Rs.getD ((i + 1) % k) [])) :=
    fun i hi => by rw [List.getLastD_eq_getLast?, (h.arc hi).2.1]; rfl
  have hsucc : ∀ i j, i < k → j < k → (i + 1) % k = (j + 1) % k → i = j := by
    intro i j hi hj hij
    by_cases h1 : i + 1 < k <;> by_cases h2 : j + 1 < k
    · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hij; omega
    · rw [Nat.mod_eq_of_lt h1, show j + 1 = k by omega, Nat.mod_self] at hij; omega
    · rw [Nat.mod_eq_of_lt h2, show i + 1 = k by omega, Nat.mod_self] at hij; omega
    · omega
  have hpred : ∀ j, j < k → ((j + 1) % k + k - 1) % k = j := by
    intro j hj
    by_cases h1 : j + 1 < k
    · rw [Nat.mod_eq_of_lt h1, show j + 1 + k - 1 = j + k by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt hj]
    · rw [show j + 1 = k by omega, Nat.mod_self, zero_add, Nat.mod_eq_of_lt (by omega)]; omega
  rw [← e]
  refine g.nodup_of_keys KL (fun x hx => ?_) (fun x hx => ?_) ?_ ?_
  · obtain ⟨i, hi, hxi⟩ := hmemKL x hx
    exact (h.key_mem hi hxi).1
  · obtain ⟨i, hi, hxi⟩ := hmemKL x hx
    exact (h.key_mem hi hxi).2.1
  · rw [eK, List.nodup_flatten]
    refine ⟨fun l hl => ?_, ?_⟩
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hl
      exact arcKeys_nodup (h.dropLast_nd (List.mem_range.1 hi))
    · rw [List.pairwise_map]
      refine List.Pairwise.imp_of_mem ?_ List.nodup_range
      intro i j hi hj hij
      rw [List.mem_range] at hi hj
      rintro ⟨I, b⟩ h1 h2
      cases b
      · have h1' := mem_arcKeys_false h1
        have h2' := mem_arcKeys_false h2
        rw [dropLast_eq_cons_inner (h.arc hi).1 (h.arc hi).2.2.2.1, List.mem_cons] at h1'
        rw [dropLast_eq_cons_inner (h.arc hj).1 (h.arc hj).2.2.2.1, List.mem_cons] at h2'
        rcases h1' with rfl | h1' <;> rcases h2' with e2 | h2'
        · exact (h.jd hi hj hij).2.2.2 (by simp only [junc]; exact e2)
        · exact h.inner_nB hj h2' (h.yB hi)
        · rw [e2] at h1'; exact h.inner_nB hi h1' (h.yB hj)
        · exact h.inner_disj hi hj hij h1' h2'
      · have h1' := mem_arcKeys_true h1
        have h2' := mem_arcKeys_true h2
        rw [hgl i hi] at h1'
        rw [hgl j hj] at h2'
        have hne : (i + 1) % k ≠ (j + 1) % k := fun hh => hij (hsucc i j hi hj hh)
        exact (h.jd (hnx i) (hnx j) hne).1 (by simp only [junc]; rw [← h1', ← h2'])
  · have claim : ∀ x ∈ KL, ∀ y ∈ KL, x.1.1 = y.1.1 → x.1.2 = false → y.1.2 = true →
        x.2.Disjoint y.2 := by
      intro x hx y hy hxy hxb hyb
      obtain ⟨i, hi, hxi⟩ := hmemKL x hx
      obtain ⟨j, hj, hyj⟩ := hmemKL y hy
      obtain ⟨-, -, hxc⟩ := h.key_mem hi hxi
      obtain ⟨-, -, hyc⟩ := h.key_mem hj hyj
      rcases hyc with ⟨hb, -⟩ | ⟨-, hy1, hy2⟩
      · rw [hb] at hyb; exact absurd hyb (by decide)
      rcases hxc with ⟨-, ⟨hx1, hx2⟩ | hin⟩ | ⟨hb, -⟩
      · have hij : i = (j + 1) % k := by
          by_contra hne
          exact (h.jd hi (hnx j) hne).2.2.1 (by simp only [junc]; rw [← hx1, ← hy1, hxy])
        subst hij
        rw [List.getD_eq_getElem _ _ (hnx j)] at hx1 hx2 hy1 hy2
        have hxx : g.iv (g.rhd Rs[(j + 1) % k]) = g.iv (g.rlt Rs[(j + 1) % k]) := by
          rw [← hx1, ← hy1, hxy]
        have ho := h.orient _ (hnx j) hxx
        rw [hpred j hj] at ho
        rw [hx2, hy2]; exact ho
      · exact absurd (hxy ▸ hy1 ▸ h.xB (hnx j)) (h.inner_nB hi hin)
      · rw [hb] at hxb; exact absurd hxb (by decide)
    intro x hx y hy hxy hb
    cases hxb : x.1.2 <;> cases hyb : y.1.2
    · rw [hxb, hyb] at hb; exact absurd rfl hb
    · exact claim x hx y hy hxy hxb hyb
    · exact (claim y hy x hx hxy.symm hyb hxb).symm
    · rw [hxb, hyb] at hb; exact absurd rfl hb

/-- **The linking step**: splicing the pieces into the runs gives a circuit in which the block
`G` is no longer active, of size at least the total size of the runs plus the length of any arc. -/
theorem LinkHyp.assemble (h : g.LinkHyp A G H U B me Rs As) :
    ∃ cs, g.Circ (g.actI (A \ g.GI G)) cs ∧
      (∀ P ∈ As, (Rs.map (g.szR (g.actI A))).sum + (P.length - 1) ≤
        g.sz (g.actI (A \ g.GI G)) cs) ∧
      (∀ v ∈ cs.flatten, (∃ R ∈ Rs, v ∈ R.flatten) ∨ g.vb v = some G) ∧
      (∀ R ∈ Rs, ∀ v ∈ R.flatten, v ∈ cs.flatten) := by
  set k := Rs.length with hk
  have hk0 := h.len_pos
  set act' := g.actI (A \ g.GI G) with hact'
  have hle : ∀ v, act' v → g.actI A v := fun v hv => ((g.actI_diff_GI A G v).1 hv).1
  have hdeact : ∀ u v, g.JoinOK (g.actI A) u v → ¬ (g.actI A u ∧ g.vb u = some G) →
      g.JoinOK act' u v := fun u v h1 h2 => h1.deactG g h2
  set π : ℕ → List V := fun i => (g.segsAt me Rs As i).flatten with hπ
  set Rn : ℕ → List (List V) := fun i => Rs.getD i [] with hRn
  set R' : ℕ → List (List V) := fun i =>
    (Rn i).dropLast ++ [(Rn i).getLastD [] ++ sInner (π i)] with hR'
  have hnx : ∀ i, (i + 1) % k < k := fun i => Nat.mod_lt _ hk0
  have hπlen : ∀ i, i < k → 2 ≤ (π i).length := fun i hi => by
    have hs := h.seg_spec hi
    exact two_le_flatten
      (by rw [← hs.1.length_eq]; exact (h.arc hi).2.2.2.1) (fun sg hsg => by
        obtain ⟨I, -, hI⟩ := forall₂_mem_right hs.1 hsg; exact hI.2.2.2)
  have hπeq : ∀ i, i < k → π i = g.rlt (Rn i) :: (sInner (π i) ++ [g.rhd (Rn ((i + 1) % k))]) :=
    fun i hi => eq_cons_sInner_append (h.seg_spec hi).2.2.1 (h.seg_spec hi).2.2.2.1 (hπlen i hi)
  have hext : ∀ i, i < k → R' i ≠ [] ∧ (∀ σ ∈ R' i, g.StrandOK act' σ) ∧
      (∀ p ∈ lpairs (R' i), g.JoinOK act' (g.lt p.1) (g.hd p.2)) ∧
      g.rhd (R' i) = g.rhd (Rn i) ∧ ¬ act' (g.rlt (R' i)) ∧
      g.Γ.Adj (g.rlt (R' i)) (g.rhd (Rn ((i + 1) % k))) ∧
      g.szR (g.actI A) (Rn i) + countPairs g.Mp (π i) ≤
        g.szR act' (R' i) + (if g.Mp (g.rlt (R' i)) (g.rhd (Rn ((i + 1) % k))) then 1 else 0) ∧
      (R' i).flatten = (Rn i).flatten ++ sInner (π i) := by
    intro i hi
    have hs := h.seg_spec hi
    have h2 := hπlen i hi
    have hna : ∀ v ∈ (π i).dropLast, ¬ act' v := fun v hv => by
      obtain ⟨I, -, -, hvG⟩ := h.piece_vb hi (List.dropLast_subset _ hv)
      exact g.not_actI_of_vb hvG
    exact (h.run hi).extend g hle hdeact hs.2.2.1 hs.2.2.2.1 h2 hs.2.1 hna
  set Rs' := (List.range k).map R' with hRs'
  have hlen' : Rs'.length = k := by simp [Rs']
  have hget' : ∀ i, i < k → Rs'.getD i [] = R' i := fun i hi => by
    rw [List.getD_eq_getElem _ _ (by rw [hlen']; exact hi)]; simp [Rs']
  -- the vertices of the new runs
  have hflat : ∀ i, i < k → (R' i).flatten =
      [g.rhd (Rn i)] ++ sInner (Rn i).flatten ++ (π i).dropLast := by
    intro i hi
    rw [(hext i hi).2.2.2.2.2.2.2]
    have e1 := (h.run hi).flatten_eq
    have e2 : (π i).dropLast = g.rlt (Rn i) :: sInner (π i) := by
      conv_lhs => rw [hπeq i hi]
      rw [← List.cons_append, List.dropLast_concat]
    rw [e2]
    conv_lhs => rw [e1]
    simp only [List.cons_append, List.nil_append, List.append_assoc]; rfl
  have hmemR : ∀ i, i < k → Rn i ∈ Rs := fun i hi => by
    simp only [Rn]; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
  have hends : ∀ i, i < k → (Rn i).flatten.head? = some (g.rhd (Rn i)) ∧
      (Rn i).flatten.getLast? = some (g.rlt (Rn i)) := fun i hi => by
    rw [(h.run hi).flatten_eq]
    exact ⟨rfl, by rw [← List.cons_append, List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]; rfl⟩
  -- nodup of the new circuit
  have hnd : Rs'.flatten.flatten.Nodup := by
    rw [List.flatten_flatten, hRs', List.map_map]
    have e : (List.range k).map (List.flatten ∘ R') = (List.range k).map
        (fun i => [g.rhd (Rn i)] ++ sInner (Rn i).flatten ++ (π i).dropLast) :=
      List.map_congr_left (fun i hi => hflat i (List.mem_range.1 hi))
    rw [e]
    refine (perm_cyc k (fun i => g.rhd (Rn i)) (fun i => sInner (Rn i).flatten)
      (fun i => (π i).dropLast)).nodup_iff.2 ?_
    have e2 : (List.range k).map (fun i => (π i).dropLast ++ [g.rhd (Rn ((i + 1) % k))]) =
        (List.range k).map π := by
      refine List.map_congr_left (fun i hi => ?_)
      conv_rhs => rw [hπeq i (List.mem_range.1 hi)]
      conv_lhs => rw [hπeq i (List.mem_range.1 hi)]
      rw [← List.cons_append, List.dropLast_concat]
    rw [e2]
    obtain ⟨hn1, hn2⟩ := h.run_nodup
    refine List.nodup_append.2 ⟨?_, h.pieces_nodup, ?_⟩
    · rw [List.nodup_flatten, List.pairwise_map]
      refine ⟨fun l hl => ?_, hn2.imp fun hd => ?_⟩
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hl
        exact inner_nodup (hn1 i (List.mem_range.1 hi))
      · exact fun v hv1 hv2 => hd (inner_subset _ hv1) (inner_subset _ hv2)
    · intro v hv w hw hvw
      subst hvw
      obtain ⟨_, hl1, hv1⟩ := List.mem_flatten.1 hv
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hl1
      obtain ⟨_, hl2, hv2⟩ := List.mem_flatten.1 hw
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hl2
      rw [List.mem_range] at hi hj
      obtain ⟨I, hIj, hvI, hvG⟩ := h.piece_vb hj hv2
      have hvR : v ∈ (Rn i).flatten := inner_subset _ hv1
      have hB := h.inB _ (hmemR i hi) v hvR hvG
      have hivI : g.iv v = I := by simp [iv, hvI]
      rw [hivI] at hB
      have hact : g.actI A v := by
        rcases (h.blk_arc hj hIj).2 hB with e | e
        · have h1 := g.iv_of_actI (h.run hj).lt_act
          rw [← e] at h1
          exact g.actI_unif A h1 hvI (h.run hj).lt_act
        · have h1 := g.iv_of_actI (h.run (hnx j)).hd_act
          rw [← e] at h1
          exact g.actI_unif A h1 hvI (h.run (hnx j)).hd_act
      have hn := notMem_inner_of_nodup (hends i hi).1 (hends i hi).2 (hn1 i hi) hv1
      rcases (h.run hi).act_G_end g hvR hact hvG with e | e
      · exact hn.1 e
      · exact hn.2 e
  have hR'ok : ∀ R ∈ Rs', R ≠ [] ∧ (∀ σ ∈ R, g.StrandOK act' σ) ∧
      ∀ p ∈ lpairs R, g.JoinOK act' (g.lt p.1) (g.hd p.2) := by
    intro R hR
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hR
    have := hext i (List.mem_range.1 hi)
    exact ⟨this.1, this.2.1, this.2.2.1⟩
  have hne' : Rs' ≠ [] := by
    intro h'; have := congrArg List.length h'; rw [hlen'] at this; simp at this; omega
  have hj : ∀ q ∈ cpairs Rs', g.JoinOK act' (g.rlt q.1) (g.rhd q.2) := by
    intro q hq
    rw [cpairs_eq_range Rs' [], hlen'] at hq
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hq
    rw [List.mem_range] at hi
    simp only
    rw [hget' i hi, hget' _ (hnx i)]
    have e := hext i hi
    have e' := hext _ (hnx i)
    rw [e'.2.2.2.1]
    exact Or.inr ⟨e.2.2.2.2.1, g.not_actI_of_vb (h.run (hnx i)).hd_G, e.2.2.2.2.2.1⟩
  obtain ⟨hcirc, hsz⟩ := g.circ_of_runs hne' hR'ok hnd hj
  refine ⟨Rs'.flatten, hcirc, ?_, ?_, ?_⟩
  · intro P hP
    rw [hsz]
    have e1 : (Rs'.map (g.szR act')).sum = ((List.range k).map (fun i => g.szR act' (R' i))).sum := by
      rw [hRs', List.map_map]; rfl
    have e2 : ((cpairs Rs').map (fun q => g.joinVal act' (g.rlt q.1) (g.rhd q.2))).sum =
        ((List.range k).map (fun i => if g.Mp (g.rlt (R' i)) (g.rhd (Rn ((i + 1) % k)))
          then 1 else 0)).sum := by
      rw [cpairs_eq_range Rs' [], hlen', List.map_map]
      congr 1
      refine List.map_congr_left fun i hi => ?_
      rw [List.mem_range] at hi
      simp only [Function.comp_apply]
      rw [hget' i hi, hget' _ (hnx i), (hext _ (hnx i)).2.2.2.1]
      unfold joinVal
      simp [(hext i hi).2.2.2.2.1]
    have e3 : (Rs.map (g.szR (g.actI A))).sum =
        ((List.range k).map (fun i => g.szR (g.actI A) (Rn i))).sum := by
      conv_lhs => rw [← range_map_getD Rs []]
      rw [List.map_map]; rfl
    rw [e1, e2, e3]
    have hle1 := List.sum_le_sum (l := List.range k)
      (f := fun i => g.szR (g.actI A) (Rn i) + countPairs g.Mp (π i))
      (g := fun i => g.szR act' (R' i) + if g.Mp (g.rlt (R' i)) (g.rhd (Rn ((i + 1) % k)))
          then 1 else 0)
      fun i hi => (hext i (List.mem_range.1 hi)).2.2.2.2.2.2.1
    rw [List.sum_map_add, List.sum_map_add] at hle1
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hP
    have hjk : j < k := by have := h.len_arcs; omega
    have hc : As[j].length - 1 ≤ countPairs g.Mp (π j) := by
      have := (h.seg_spec hjk).2.2.2.2; rwa [List.getD_eq_getElem _ _ hj] at this
    have hc2 : countPairs g.Mp (π j) ≤ ((List.range k).map (fun i => countPairs g.Mp (π i))).sum :=
      List.le_sum_of_mem (List.mem_map.2 ⟨j, List.mem_range.2 hjk, rfl⟩)
    omega
  · intro v hv
    rw [List.flatten_flatten] at hv
    obtain ⟨_, hl, hvl⟩ := List.mem_flatten.1 hv
    obtain ⟨R, hR, rfl⟩ := List.mem_map.1 hl
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hR
    rw [List.mem_range] at hi
    rw [(hext i hi).2.2.2.2.2.2.2, List.mem_append] at hvl
    rcases hvl with hvl | hvl
    · exact Or.inl ⟨Rn i, hmemR i hi, hvl⟩
    · obtain ⟨I, -, -, hvG⟩ := h.piece_vb hi (inner_subset _ hvl)
      exact Or.inr hvG
  · intro R hR v hv
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hR
    rw [List.flatten_flatten]
    refine List.mem_flatten.2 ⟨(R' i).flatten, List.mem_map.2 ⟨R' i, List.mem_map.2
      ⟨i, List.mem_range.2 hi, rfl⟩, rfl⟩, ?_⟩
    rw [(hext i hi).2.2.2.2.2.2.2]
    refine List.mem_append_left _ ?_
    show v ∈ (Rs.getD i []).flatten
    rw [List.getD_eq_getElem _ _ hi]; exact hv


end Geo

end Lovasz
