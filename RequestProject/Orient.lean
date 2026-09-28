module
public import RequestProject.LinkStep

/-!
# Orienting runs whose two ends lie in the same interval

Before splicing in the pieces, each run whose two ends lie in the same interval is oriented so
that the segments of the two pieces meeting in that interval are disjoint.
-/

@[expose] public section


open Classical

namespace Lovasz

section lists

variable {α : Type*}

lemma getLastD_lpairs_cons3 (a b c : α) (t : List α) (d : α × α) :
    (lpairs (a :: b :: c :: t)).getLastD d = (lpairs (b :: c :: t)).getLastD d := by
  simp only [lpairs_cons_cons, List.getLastD_cons]

lemma headD_mem_lpairs {P : List α} (h2 : 2 ≤ P.length) (d : α × α) :
    (lpairs P).headD d ∈ lpairs P := by
  match P, h2 with
  | a :: b :: t, _ => simp [lpairs_cons_cons]

lemma getLastD_mem_lpairs {P : List α} (h2 : 2 ≤ P.length) (d : α × α) :
    (lpairs P).getLastD d ∈ lpairs P := by
  have hne : lpairs P ≠ [] := by
    intro h0; have := congrArg List.length h0; rw [length_lpairs, List.length_nil] at this; omega
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]
  exact List.getLast_mem hne

lemma getLastD_lpairs_snd : ∀ {P : List α}, 2 ≤ P.length → ∀ (d : α × α) (x : α),
    P.getLast? = some x → ((lpairs P).getLastD d).2 = x
  | [a, b], _, d, x, h => by simpa using h
  | a :: b :: c :: t, _, d, x, h => by
    rw [getLastD_lpairs_cons3]
    exact getLastD_lpairs_snd (P := b :: c :: t) (by simp) d x (by
      rw [List.getLast?_cons_cons] at h; exact h)

lemma headD_lpairs_fst {P : List α} (h2 : 2 ≤ P.length) (d : α × α) (y : α)
    (h : P.head? = some y) : ((lpairs P).headD d).1 = y := by
  match P, h2 with
  | a :: b :: t, _ => simpa [lpairs_cons_cons] using h

lemma arcEdges_eq_map (P : List α) : arcEdges P = (lpairs P).map (fun q => s(q.1, q.2)) := rfl

lemma flatten_map_perm {γ : Type*} (l : List γ) (f f' : γ → List α)
    (h : ∀ i ∈ l, (f i).Perm (f' i)) : (l.map f).flatten.Perm (l.map f').flatten := by
  induction l with
  | nil => simp
  | cons x t ih =>
    simp only [List.map_cons, List.flatten_cons]
    exact (h x (by simp)).append (ih fun i hi => h i (by simp [hi]))

end lists

namespace Geo

variable {V ι β : Type*} {g : Geo V ι β}

lemma dep_eq (me : ι → ι → V × V) {P : List ι} (h2 : 2 ≤ P.length) :
    g.dep me P = (me ((lpairs P).headD (g.dI, g.dI)).1 ((lpairs P).headD (g.dI, g.dI)).2).1 := by
  match P, h2 with
  | a :: b :: t, _ => rfl

lemma BlockOK.dep_iv {G : β} {H : SimpleGraph ι} {U : Finset ι} {me : ι → ι → V × V}
    (hb : g.BlockOK G H U me) {P : List ι} (hc : P.IsChain H.Adj) (h2 : 2 ≤ P.length) {y : ι}
    (hy : P.head? = some y) : g.ivOf (g.dep me P) = some y := by
  rw [dep_eq me h2, ← headD_lpairs_fst h2 (g.dI, g.dI) y hy]
  exact hb.me_iv1 (rel_of_mem_lpairs hc _ (headD_mem_lpairs h2 _))

lemma BlockOK.arr_iv {G : β} {H : SimpleGraph ι} {U : Finset ι} {me : ι → ι → V × V}
    (hb : g.BlockOK G H U me) {P : List ι} (hc : P.IsChain H.Adj) (h2 : 2 ≤ P.length) {x : ι}
    (hx : P.getLast? = some x) : g.ivOf (g.arr me P) = some x := by
  unfold arr
  rw [← getLastD_lpairs_snd h2 (g.dI, g.dI) x hx]
  exact hb.me_iv2 (rel_of_mem_lpairs hc _ (getLastD_mem_lpairs h2 _))

/-- If the departure vertex of `P` is the arrival vertex of `Q`, then the first edge of `P` is
the last edge of `Q`. -/
lemma BlockOK.dep_eq_arr {G : β} {H : SimpleGraph ι} {U : Finset ι} {me : ι → ι → V × V}
    (hb : g.BlockOK G H U me) {P Q : List ι} (hP : P.IsChain H.Adj) (hP2 : 2 ≤ P.length)
    (hQ : Q.IsChain H.Adj) (hQ2 : 2 ≤ Q.length) (he : g.dep me P = g.arr me Q) :
    s(((lpairs P).headD (g.dI, g.dI)).1, ((lpairs P).headD (g.dI, g.dI)).2) =
      s(((lpairs Q).getLastD (g.dI, g.dI)).1, ((lpairs Q).getLastD (g.dI, g.dI)).2) := by
  set a := ((lpairs P).headD (g.dI, g.dI)).1
  set b := ((lpairs P).headD (g.dI, g.dI)).2
  set c := ((lpairs Q).getLastD (g.dI, g.dI)).1
  set d := ((lpairs Q).getLastD (g.dI, g.dI)).2
  have hab : H.Adj a b := rel_of_mem_lpairs hP _ (headD_mem_lpairs hP2 _)
  have hcd : H.Adj c d := rel_of_mem_lpairs hQ _ (getLastD_mem_lpairs hQ2 _)
  rw [dep_eq me hP2] at he
  unfold arr at he
  have hsw := hb.me_swap hcd
  have h1 : (me d c).1 = (me a b).1 := by rw [hsw]; exact he.symm
  have hM1 := hb.me_M hab
  have hM2 := hb.me_M hcd.symm
  rw [h1] at hM2
  have h2 : (me a b).2 = (me d c).2 := g.Mp_uniq hM1 hM2
  have e1 := hb.me_iv2 hab
  rw [h2, hb.me_iv2 hcd.symm, Option.some.injEq] at e1
  have e2 := hb.me_iv1 hab
  rw [← h1, hb.me_iv1 hcd.symm, Option.some.injEq] at e2
  rw [e1, e2, Sym2.eq_swap]

lemma flip_good {J : ι} {p q w1 w2 : V} (hp : g.IsBd p) (hq : g.IsBd q)
    (hpJ : g.ivOf p = some J) (hqJ : g.ivOf q = some J) (hpq : p ≠ q)
    (h1 : g.ivOf w1 = some J) (h2 : g.ivOf w2 = some J) (hw : w1 ≠ w2)
    (hbad : ¬ (g.seg p w1).Disjoint (g.seg w2 q)) : (g.seg q w1).Disjoint (g.seg w2 p) := by
  obtain ⟨J1, hJ1, hp'⟩ := hp
  obtain ⟨J2, hJ2, hq'⟩ := hq
  rw [hpJ, Option.some.injEq] at hJ1
  rw [hqJ, Option.some.injEq] at hJ2
  subst hJ1 hJ2
  rcases g.seg_orient h1 h2 hw with ho | ho <;>
    rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl
  · exact absurd rfl hpq
  · exact absurd ho hbad
  · exact ho
  · exact absurd rfl hpq
  · exact absurd rfl hpq
  · exact ho
  · exact absurd ho hbad
  · exact absurd rfl hpq

section pre

variable {A : Set ι} {G : β} {H : SimpleGraph ι} {U B : Finset ι} {me : ι → ι → V × V}
  {Rs : List (List (List V))} {As : List (List ι)}

lemma LinkPre.edges_disj (h : g.LinkPre A G H U B me Rs As) {i j : ℕ} (hi : i < Rs.length)
    (hj : j < Rs.length) (hij : i ≠ j) :
    (arcEdges (As.getD i [])).Disjoint (arcEdges (As.getD j [])) := by
  have hn := h.edges
  rw [List.flatMap_def, List.nodup_flatten] at hn
  have hp := List.pairwise_iff_getElem.1 hn.2
  have hl := h.len_arcs
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · have := hp i j (by simp; omega) (by simp; omega) hlt
    rw [List.getElem_map, List.getElem_map] at this; exact this
  · have := hp j i (by simp; omega) (by simp; omega) hlt
    rw [List.getElem_map, List.getElem_map] at this; exact this.symm

lemma LinkPre.edges_nd (h : g.LinkPre A G H U B me Rs As) {i : ℕ} (hi : i < Rs.length) :
    (arcEdges (As.getD i [])).Nodup := by
  have hn := h.edges
  rw [List.flatMap_def, List.nodup_flatten] at hn
  have hl := h.len_arcs
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact hn.1 _ (List.mem_map.2 ⟨_, List.getElem_mem (by omega), rfl⟩)

lemma LinkPre.dep_ne_arr (h : g.LinkPre A G H U B me Rs As) {i : ℕ} (hi : i < Rs.length)
    (hxx : g.iv (g.rhd (Rs.getD i [])) = g.iv (g.rlt (Rs.getD i []))) :
    g.dep me (As.getD i []) ≠ g.arr me (As.getD ((i + Rs.length - 1) % Rs.length) []) := by
  intro he
  have hk0 := h.len_pos
  set k := Rs.length with hk
  set j := (i + k - 1) % k with hjdef
  have hj : j < k := Nat.mod_lt _ hk0
  have hai := h.arc hi
  have haj := h.arc hj
  have hse := h.blk.dep_eq_arr hai.2.2.1 hai.2.2.2.1 haj.2.2.1 haj.2.2.2.1 he
  have hm1 : s(((lpairs (As.getD i [])).headD (g.dI, g.dI)).1,
      ((lpairs (As.getD i [])).headD (g.dI, g.dI)).2) ∈ arcEdges (As.getD i []) := by
    rw [arcEdges_eq_map]
    exact List.mem_map_of_mem (f := fun q => s(q.1, q.2)) (headD_mem_lpairs hai.2.2.2.1 _)
  have hm2 : s(((lpairs (As.getD j [])).getLastD (g.dI, g.dI)).1,
      ((lpairs (As.getD j [])).getLastD (g.dI, g.dI)).2) ∈ arcEdges (As.getD j []) := by
    rw [arcEdges_eq_map]
    exact List.mem_map_of_mem (f := fun q => s(q.1, q.2)) (getLastD_mem_lpairs haj.2.2.2.1 _)
  by_cases hij : i = j
  · have hk1 : k = 1 ∧ i = 0 := by
      by_contra hne
      have hk2 : 2 ≤ k := by
        by_contra h1; have : k = 1 := by omega
        exact hne ⟨this, by omega⟩
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · rw [hjdef, h0, zero_add, Nat.mod_eq_of_lt (by omega)] at hij; omega
      · rw [hjdef, show i + k - 1 = (i - 1) + k by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)] at hij; omega
    obtain ⟨hk1, hi0⟩ := hk1
    rw [← hij] at hm2 hse
    have hnd := h.edges_nd hi
    have hlast := hai.2.1
    have hhead := hai.1
    have hnext : (i + 1) % k = i := by rw [hk1, hi0]
    rw [hnext, hxx] at hlast
    generalize As.getD i [] = P at hm1 hm2 hse hnd hlast hhead hai
    match P, hai.2.2.2.1 with
    | [a, b], _ =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at hlast
      have hadj := hai.2.2.1
      rw [List.isChain_cons_cons] at hadj
      rw [hhead, hlast] at hadj
      exact hadj.1.ne rfl
    | a :: b :: c :: t, _ =>
      rw [getLastD_lpairs_cons3] at hse
      have hmem : s(((lpairs (b :: c :: t)).getLastD (g.dI, g.dI)).1,
          ((lpairs (b :: c :: t)).getLastD (g.dI, g.dI)).2) ∈ arcEdges (b :: c :: t) := by
        rw [arcEdges_eq_map]
        exact List.mem_map_of_mem (f := fun q => s(q.1, q.2)) (getLastD_mem_lpairs (P := b :: c :: t)
          (Nat.le_add_left 2 t.length) _)
      rw [arcEdges_eq_map, lpairs_cons_cons, List.map_cons, List.nodup_cons] at hnd
      apply hnd.1
      rw [← arcEdges_eq_map]
      simp only [lpairs_cons_cons, List.headD_cons] at hse
      rw [hse]; exact hmem
  · exact h.edges_disj hi hj hij hm1 (hse ▸ hm2)

lemma RunOK.bd_ends {act : V → Prop} {R : List (List V)} (hR : g.RunOK act G R) :
    g.IsBd (g.rhd R) ∧ g.IsBd (g.rlt R) := by
  obtain ⟨σ, hσ, hvσ⟩ := List.mem_flatten.1 (g.rhd_mem hR)
  obtain ⟨τ, hτ, hvτ⟩ := List.mem_flatten.1 (g.rlt_mem hR)
  exact ⟨g.bd_of_act_mem (hR.strand σ hσ) hvσ hR.hd_act,
    g.bd_of_act_mem (hR.strand τ hτ) hvτ hR.lt_act⟩

/-- **Orientation of runs**: reversing suitable runs whose two ends lie in the same interval, we
obtain the orientation hypothesis of the linking step. -/
theorem LinkPre.orient_runs (h : g.LinkPre A G H U B me Rs As) :
    ∃ Ro, g.LinkHyp A G H U B me Ro As ∧
      (Ro.map (g.szR (g.actI A))).sum = (Rs.map (g.szR (g.actI A))).sum ∧
      (∀ R ∈ Ro, ∀ v ∈ R.flatten, ∃ R' ∈ Rs, v ∈ R'.flatten) ∧
      (∀ R' ∈ Rs, ∀ v ∈ R'.flatten, ∃ R ∈ Ro, v ∈ R.flatten) := by
  set k := Rs.length with hk
  have hk0 := h.len_pos
  set Rn : ℕ → List (List V) := fun i => Rs.getD i [] with hRn
  set bad : ℕ → Prop := fun i => g.iv (g.rhd (Rn i)) = g.iv (g.rlt (Rn i)) ∧
    ¬ (g.seg (g.rlt (Rn i)) (g.dep me (As.getD i []))).Disjoint
      (g.seg (g.arr me (As.getD ((i + k - 1) % k) [])) (g.rhd (Rn i))) with hbad
  set f : ℕ → List (List V) := fun i => if bad i then revRun (Rn i) else Rn i with hf
  set Ro := (List.range k).map f with hRo
  have hlen : Ro.length = k := by simp [Ro]
  have hfrun : ∀ i, i < k → g.RunOK (g.actI A) G (f i) ∧
      g.szR (g.actI A) (f i) = g.szR (g.actI A) (Rn i) ∧ (f i).flatten.Perm (Rn i).flatten ∧
      g.junc (f i) = g.junc (Rn i) := by
    intro i hi
    have hr := h.run hi
    by_cases hb : bad i
    · rw [show f i = revRun (Rn i) from if_pos hb]
      refine ⟨(hr.rev g).1, (hr.rev g).2, flatten_revRun_perm _, ?_⟩
      unfold junc; rw [g.rhd_revRun, g.rlt_revRun, hb.1]
    · rw [show f i = Rn i from if_neg hb]; exact ⟨hr, rfl, List.Perm.refl _, rfl⟩
  have hjunc : Ro.map g.junc = Rs.map g.junc := by
    rw [hRo, List.map_map]
    conv_rhs => rw [← range_map_getD Rs []]
    rw [List.map_map]
    exact List.map_congr_left fun i hi => (hfrun i (List.mem_range.1 hi)).2.2.2
  have hflat : Ro.flatten.flatten.Perm Rs.flatten.flatten := by
    rw [List.flatten_flatten, List.flatten_flatten, hRo, List.map_map]
    conv_rhs => rw [← range_map_getD Rs []]
    rw [List.map_map]
    exact flatten_map_perm _ _ _ fun i hi => (hfrun i (List.mem_range.1 hi)).2.2.1
  have hmemR : ∀ i, i < k → Rn i ∈ Rs := fun i hi => by
    simp only [Rn]; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
  have hvert1 : ∀ R ∈ Ro, ∀ v ∈ R.flatten, ∃ R' ∈ Rs, v ∈ R'.flatten := by
    intro R hR v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hR
    rw [List.mem_range] at hi
    exact ⟨Rn i, hmemR i hi, (hfrun i hi).2.2.1.mem_iff.1 hv⟩
  have hvert2 : ∀ R' ∈ Rs, ∀ v ∈ R'.flatten, ∃ R ∈ Ro, v ∈ R.flatten := by
    intro R' hR' v hv
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hR'
    refine ⟨f i, List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩, (hfrun i hi).2.2.1.mem_iff.2 ?_⟩
    show v ∈ (Rs.getD i []).flatten
    rw [List.getD_eq_getElem _ _ hi]; exact hv
  have hruns : g.RunsOK (g.actI A) G Ro := by
    refine ⟨fun h0 => by rw [h0] at hlen; simp at hlen; omega, fun R hR => ?_,
      hflat.nodup_iff.2 h.runs.nodup⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hR
    exact (hfrun i (List.mem_range.1 hi)).1
  have hsum : (Ro.map (g.szR (g.actI A))).sum = (Rs.map (g.szR (g.actI A))).sum := by
    rw [hRo, List.map_map]
    conv_rhs => rw [← range_map_getD Rs []]
    rw [List.map_map]
    congr 1
    exact List.map_congr_left fun i hi => (hfrun i (List.mem_range.1 hi)).2.1
  have hsucc : ∀ i, i < k → ((i + k - 1) % k + 1) % k = i := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | h0
    · rw [zero_add, Nat.mod_eq_of_lt (show k - 1 < k by omega), show k - 1 + 1 = k by omega,
        Nat.mod_self]
    · rw [show i + k - 1 = (i - 1) + k by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (show i - 1 < k by omega),
        show i - 1 + 1 = i by omega, Nat.mod_eq_of_lt hi]
  refine ⟨Ro, ⟨⟨h.blk, hruns, by rw [hjunc]; exact h.disj, ?_, by rw [hjunc]; exact h.arcs,
    h.inner, h.edges⟩, ?_⟩, hsum, hvert1, hvert2⟩
  · intro R hR v hv hvG
    obtain ⟨R', hR', hvR'⟩ := hvert1 R hR v hv
    exact h.inB R' hR' v hvR' hvG
  · intro i hi hxx
    have hi' : i < k := hlen ▸ hi
    have hRoi : Ro[i] = f i := by simp [Ro]
    simp only [hRoi, hlen] at hxx ⊢
    have hjf := (hfrun i hi').2.2.2
    have hxx' : g.iv (g.rhd (Rn i)) = g.iv (g.rlt (Rn i)) := by
      unfold junc at hjf
      rw [Prod.mk.injEq] at hjf
      rw [← hjf.1, ← hjf.2]; exact hxx
    by_cases hb : bad i
    · simp only [f, if_pos hb, g.rhd_revRun, g.rlt_revRun]
      have hr := h.run hi'
      set j := (i + k - 1) % k with hj
      have hjk : j < k := Nat.mod_lt _ hk0
      have hbd := hr.bd_ends
      have hpJ : g.ivOf (g.rlt (Rn i)) = some (g.iv (g.rlt (Rn i))) := g.iv_of_actI hr.lt_act
      have hqJ : g.ivOf (g.rhd (Rn i)) = some (g.iv (g.rlt (Rn i))) := by
        rw [← hxx']; exact g.iv_of_actI hr.hd_act
      have hpq : g.rlt (Rn i) ≠ g.rhd (Rn i) :=
        fun e => hr.hd_ne_lt g ((h.run_nodup).1 i hi') e.symm
      have hai := h.arc hi'
      have haj := h.arc hjk
      have h1 : g.ivOf (g.dep me (As.getD i [])) = some (g.iv (g.rlt (Rn i))) :=
        h.blk.dep_iv hai.2.2.1 hai.2.2.2.1 hai.1
      have h2 : g.ivOf (g.arr me (As.getD j [])) = some (g.iv (g.rlt (Rn i))) := by
        have := h.blk.arr_iv haj.2.2.1 haj.2.2.2.1 haj.2.1
        rw [hj, hsucc i hi'] at this
        rw [this, ← hxx']
      exact flip_good hbd.2 hbd.1 hpJ hqJ hpq h1 h2 (h.dep_ne_arr hi' hxx') hb.2
    · simp only [f, if_neg hb]
      by_contra hc
      exact hb ⟨hxx', hc⟩

end pre

end Geo

end Lovasz
