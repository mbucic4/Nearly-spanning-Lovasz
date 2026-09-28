module
public import RequestProject.Runs

/-!
# Merging two runs through an interval

If two different runs at a block `G` have ends `p`, `p'` in the same interval `J`, we may
join them through the interior of `J` (a subpath of `L`), after which `J` is no longer active.
-/

@[expose] public section


open Classical

namespace Lovasz

section lists

variable {α : Type*}

lemma eq_cons_sInner_append {l : List α} {a b : α} (ha : l.head? = some a)
    (hb : l.getLast? = some b) (hl : 2 ≤ l.length) : l = a :: sInner l ++ [b] := by
  obtain ⟨c, l', rfl⟩ : ∃ c l', l = c :: l' := by
    cases l with
    | nil => simp at hl
    | cons c l' => exact ⟨c, l', rfl⟩
  simp only [List.head?_cons, Option.some.injEq] at ha
  subst ha
  have hl' : l' ≠ [] := by rintro rfl; simp at hl
  have hb' : l'.getLast hl' = b := by
    rw [List.getLast?_cons, List.getLast?_eq_some_getLast hl'] at hb; simpa using hb
  unfold sInner
  simp only [List.tail_cons, List.cons_append, List.cons.injEq, true_and]
  rw [← hb']; exact (List.dropLast_append_getLast hl').symm

end lists

namespace Geo

variable {V ι β : Type*} (g : Geo V ι β)

lemma StrandOK.mono {act act' : V → Prop} {σ : List V} (h : g.StrandOK act σ)
    (hle : ∀ v, act' v → act v) : g.StrandOK act' σ :=
  ⟨h.two_le, h.chain, fun v hv ha => h.inner_na v hv (hle v ha),
    fun ha => h.hd_bd (hle _ ha), fun ha => h.lt_bd (hle _ ha)⟩

lemma joinVal_mono {act act' : V → Prop} (hle : ∀ v, act' v → act v) (u v : V) :
    g.joinVal act u v ≤ g.joinVal act' u v := by
  unfold joinVal
  split_ifs with h1 h2 h2 <;> simp_all

lemma szR_mono {act act' : V → Prop} (hle : ∀ v, act' v → act v) (R : List (List V)) :
    g.szR act R ≤ g.szR act' R := by
  unfold szR
  gcongr
  exact List.sum_le_sum fun p _ => g.joinVal_mono hle _ _

lemma szR_singleton (act : V → Prop) (σ : List V) : g.szR act [σ] = countPairs g.Mp σ := by
  simp [szR]

lemma szR_append (act : V → Prop) (A B : List (List V)) (hA : A ≠ []) (hB : B ≠ []) :
    g.szR act (A ++ B) = g.szR act A + g.szR act B +
      g.joinVal act (g.lt (A.getLastD [])) (g.hd (B.headD [])) := by
  unfold szR
  rw [lpairs_append A B hA hB]
  have e1 : A.getLast hA = A.getLastD [] := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hA]; rfl
  have e2 : B.head hB = B.headD [] := by
    obtain ⟨b, t, rfl⟩ := List.exists_cons_of_ne_nil hB; rfl
  simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons, e1, e2]
  ring

lemma rhd_append (A B : List (List V)) (hA : A ≠ []) : g.rhd (A ++ B) = g.rhd A := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hA; rfl

lemma rlt_append (A B : List (List V)) (hB : B ≠ []) : g.rlt (A ++ B) = g.rlt B := by
  unfold rlt
  rw [List.getLastD_eq_getLast?, List.getLastD_eq_getLast?, List.getLast?_append_of_ne_nil _ hB]

lemma mem_ends_of_act {act : V → Prop} {σ : List V} (h : g.StrandOK act σ) {v : V} (hv : v ∈ σ)
    (ha : act v) : v = g.hd σ ∨ v = g.lt σ := by
  have hne := g.ne_nil_of_strand h
  have hh : σ.head? = some (g.hd σ) := by rw [g.hd_eq_head hne]; exact List.head?_eq_some_head hne
  have hl : σ.getLast? = some (g.lt σ) := by
    rw [g.lt_eq_getLast hne]; exact List.getLast?_eq_some_getLast hne
  rw [eq_cons_sInner_append hh hl h.two_le] at hv
  simp only [List.cons_append, List.mem_cons, List.mem_append] at hv
  rcases hv with h1 | h1 | h1
  · exact Or.inl h1
  · exact absurd ha (h.inner_na v h1)
  · exact Or.inr (by simpa using h1)

lemma bd_of_act_mem {act : V → Prop} {σ : List V} (h : g.StrandOK act σ) {v : V} (hv : v ∈ σ)
    (ha : act v) : g.IsBd v := by
  rcases g.mem_ends_of_act h hv ha with rfl | rfl
  · exact h.hd_bd ha
  · exact h.lt_bd ha

lemma eq_of_bd {v p p' : V} {J : ι} (hv : g.IsBd v) (hp : g.IsBd p) (hp' : g.IsBd p')
    (hvJ : g.ivOf v = some J) (hpJ : g.ivOf p = some J) (hp'J : g.ivOf p' = some J)
    (hne : p ≠ p') : v = p ∨ v = p' := by
  obtain ⟨J1, h1, hv⟩ := hv
  obtain ⟨J2, h2, hp⟩ := hp
  obtain ⟨J3, h3, hp'⟩ := hp'
  rw [hvJ, Option.some.injEq] at h1
  rw [hpJ, Option.some.injEq] at h2
  rw [hp'J, Option.some.injEq] at h3
  subst h1 h2 h3
  rcases hv with rfl | rfl <;> rcases hp with rfl | rfl <;> rcases hp' with rfl | rfl <;> simp_all

lemma strand_tail_eq {act : V → Prop} {σ : List V} (h : g.StrandOK act σ) :
    σ = g.hd σ :: (sInner σ ++ [g.lt σ]) := by
  have hne := g.ne_nil_of_strand h
  have hh : σ.head? = some (g.hd σ) := by rw [g.hd_eq_head hne]; exact List.head?_eq_some_head hne
  have hl : σ.getLast? = some (g.lt σ) := by
    rw [g.lt_eq_getLast hne]; exact List.getLast?_eq_some_getLast hne
  exact eq_cons_sInner_append hh hl h.two_le

lemma seg_eq {J : ι} {u v : V} (hu : g.ivOf u = some J) (hv : g.ivOf v = some J) (hne : u ≠ v) :
    g.seg u v = u :: (sInner (g.seg u v) ++ [v]) := by
  have hn := g.seg_nodup hu hv
  have hh := g.seg_head hu hv
  have hl := g.seg_last hu hv
  refine eq_cons_sInner_append hh hl ?_
  obtain ⟨a, t, ht⟩ : ∃ a t, g.seg u v = a :: t := by
    cases h : g.seg u v with
    | nil => rw [h] at hh; simp at hh
    | cons a t => exact ⟨a, t, rfl⟩
  rw [ht] at hh hl ⊢
  simp only [List.head?_cons, Option.some.injEq] at hh
  subst hh
  cases t with
  | nil => simp at hl; exact absurd hl hne
  | cons b t => simp

/-- Extending a strand ending at `p` by the inner vertices of the segment from `p` to `p'`. -/
lemma StrandOK.extend {act : V → Prop} {σ : List V} (h : g.StrandOK act σ) {J : ι} {p' : V}
    (hpJ : g.ivOf (g.lt σ) = some J) (hp'J : g.ivOf p' = some J) (hne : g.lt σ ≠ p') :
    g.StrandOK (fun v => act v ∧ g.ivOf v ≠ some J) (σ ++ sInner (g.seg (g.lt σ) p')) ∧
      g.hd (σ ++ sInner (g.seg (g.lt σ) p')) = g.hd σ ∧
      g.ivOf (g.lt (σ ++ sInner (g.seg (g.lt σ) p'))) = some J ∧
      g.Γ.Adj (g.lt (σ ++ sInner (g.seg (g.lt σ) p'))) p' ∧
      countPairs g.Mp σ ≤ countPairs g.Mp (σ ++ sInner (g.seg (g.lt σ) p')) := by
  set p := g.lt σ with hp
  set X := sInner (g.seg p p') with hX
  have hne' := g.ne_nil_of_strand h
  have hseg := g.seg_eq hpJ hp'J hne
  have hsegc := g.seg_chain hpJ hp'J
  rw [← hX] at hseg
  have hXJ : ∀ x ∈ X, g.ivOf x = some J := fun x hx =>
    g.seg_iv hpJ hp'J x (List.tail_subset _ (List.dropLast_subset _ hx))
  have hσ := g.strand_tail_eq h
  rw [← hp] at hσ
  have hpX : ((p :: X) ++ [p']).IsChain g.Γ.Adj := by rw [List.cons_append, ← hseg]; exact hsegc
  rw [List.isChain_append] at hpX
  -- the last vertex
  have hlast : (σ ++ X).getLast? = (p :: X).getLast? := by
    conv_lhs => rw [← List.dropLast_append_getLast hne']
    rw [List.append_assoc, List.singleton_append, List.getLast?_append_of_ne_nil _ (by simp)]
    rw [← g.lt_eq_getLast hne']
  have hlt : g.lt (σ ++ X) = (p :: X).getLast (by simp) := by
    unfold lt; rw [List.getLastD_eq_getLast?, hlast, List.getLast?_eq_some_getLast (by simp)]; rfl
  have hltJ : g.ivOf (g.lt (σ ++ X)) = some J := by
    rw [hlt]
    rcases List.mem_cons.1 (List.getLast_mem (l := p :: X) (by simp)) with h1 | h1
    · rw [h1]; exact hpJ
    · exact hXJ _ h1
  have hhd : g.hd (σ ++ X) = g.hd σ := by
    obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hne'; rfl
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hhd, hltJ, ?_, countPairs_mono_append_left _ _ _⟩
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
    · exact h.inner_na v h1 hact.1
    · exact hact.2 hpJ
    · exact hact.2 (hXJ v h1)
  · intro ha; rw [hhd] at ha ⊢; exact h.hd_bd ha.1
  · intro ha; exact absurd hltJ ha.2
  · rw [hlt]
    exact hpX.2.2 _ (List.getLast?_eq_some_getLast (by simp)) _ rfl

lemma lpairs_snoc_map {D : List (List V)} {x y : List V} (hxy : g.hd x = g.hd y) :
    (lpairs (D ++ [x])).map (fun q => (g.lt q.1, g.hd q.2)) =
      (lpairs (D ++ [y])).map (fun q => (g.lt q.1, g.hd q.2)) := by
  rcases eq_or_ne D [] with rfl | hD
  · rfl
  rw [lpairs_append_singleton _ _ hD, lpairs_append_singleton _ _ hD]
  simp [hxy]

lemma szR_snoc_le (act : V → Prop) {D : List (List V)} {x y : List V} (hxy : g.hd x = g.hd y)
    (hc : countPairs g.Mp y ≤ countPairs g.Mp x) : g.szR act (D ++ [y]) ≤ g.szR act (D ++ [x]) := by
  unfold szR
  have e : ((lpairs (D ++ [x])).map (fun p => g.joinVal act (g.lt p.1) (g.hd p.2))).sum =
      ((lpairs (D ++ [y])).map (fun p => g.joinVal act (g.lt p.1) (g.hd p.2))).sum := by
    have := congrArg (fun l => (l.map (fun q : V × V => g.joinVal act q.1 q.2)).sum)
      (g.lpairs_snoc_map (D := D) hxy)
    simpa [List.map_map, Function.comp_def] using this
  rw [e]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  omega

lemma rhd_snoc {D : List (List V)} {x y : List V} (hxy : g.hd x = g.hd y) :
    g.rhd (D ++ [x]) = g.rhd (D ++ [y]) := by
  cases D with
  | nil => exact hxy
  | cons a t => rfl

lemma JoinOK.deact {act : V → Prop} {G : β} {J : ι} {u v : V} (h : g.JoinOK act u v)
    (hnG : ¬ (act u ∧ g.vb u = some G)) (hJG : g.blk J = some G) :
    g.JoinOK (fun w => act w ∧ g.ivOf w ≠ some J) u v := by
  rcases h with ⟨h1, h2, G', h3, h4⟩ | ⟨h1, h2, h3⟩
  · have hG' : G' ≠ G := by rintro rfl; exact hnG ⟨h1, h3⟩
    have key : ∀ w, g.vb w = some G' → g.ivOf w ≠ some J := by
      intro w hw hwJ
      unfold vb at hw; rw [hwJ, Option.bind_some, hJG, Option.some.injEq] at hw
      exact hG' hw.symm
    exact Or.inl ⟨⟨h1, key u h3⟩, ⟨h2, key v h4⟩, G', h3, h4⟩
  · exact Or.inr ⟨fun h' => h1 h'.1, fun h' => h2 h'.1, h3⟩

lemma rhd_mem {act : V → Prop} {G : β} {R : List (List V)} (h : g.RunOK act G R) :
    g.rhd R ∈ R.flatten := by
  obtain ⟨σ, t, rfl⟩ := List.exists_cons_of_ne_nil h.ne
  exact List.mem_flatten.2 ⟨σ, by simp, g.hd_mem (g.ne_nil_of_strand (h.strand σ (by simp)))⟩

lemma rlt_mem {act : V → Prop} {G : β} {R : List (List V)} (h : g.RunOK act G R) :
    g.rlt R ∈ R.flatten := by
  have hl := List.getLast_mem h.ne
  have e : R.getLastD [] = R.getLast h.ne := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast h.ne]; rfl
  refine List.mem_flatten.2 ⟨_, hl, ?_⟩
  unfold rlt; rw [e]
  exact g.lt_mem (g.ne_nil_of_strand (h.strand _ hl))

lemma RunOK.hd_ne_lt {act : V → Prop} {G : β} {R : List (List V)} (h : g.RunOK act G R)
    (hn : R.flatten.Nodup) : g.rhd R ≠ g.rlt R := by
  obtain ⟨σ, t, rfl⟩ := List.exists_cons_of_ne_nil h.ne
  have hσ := h.strand σ (by simp)
  rcases eq_or_ne t [] with rfl | ht
  · -- a single strand
    have e := g.strand_tail_eq hσ
    have hn' : σ.Nodup := by simpa using hn
    change g.hd σ ≠ g.lt σ
    intro heq
    rw [e, List.nodup_cons] at hn'
    exact hn'.1 (by rw [heq]; simp)
  · have e1 : g.rlt (σ :: t) = g.rlt t := g.rlt_append [σ] t ht
    rw [e1]
    have h2 : g.rlt t ∈ t.flatten := by
      have hl := List.getLast_mem ht
      have e : t.getLastD [] = t.getLast ht := by
        rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast ht]; rfl
      refine List.mem_flatten.2 ⟨_, hl, ?_⟩
      unfold rlt; rw [e]
      exact g.lt_mem (g.ne_nil_of_strand (h.strand _ (List.mem_cons_of_mem _ hl)))
    have h1 : g.rhd (σ :: t) ∈ σ := g.hd_mem (g.ne_nil_of_strand hσ)
    rw [List.flatten_cons, List.nodup_append] at hn
    exact hn.2.2 _ h1 _ h2

lemma rhd_eq_head {R : List (List V)} (hne : R ≠ []) : g.rhd R = g.hd (R.head hne) := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hne; rfl

lemma RunOK.deact {act : V → Prop} {G : β} {J : ι} {R : List (List V)} (h : g.RunOK act G R)
    (hJG : g.blk J = some G) (hhd : g.ivOf (g.rhd R) ≠ some J) (hlt : g.ivOf (g.rlt R) ≠ some J) :
    g.RunOK (fun v => act v ∧ g.ivOf v ≠ some J) G R :=
  ⟨h.ne, fun σ hσ => (h.strand σ hσ).mono g (fun _ hv => hv.1), fun q hq =>
    ⟨((h.join q hq).1).deact g (h.join q hq).2 hJG, fun hh => (h.join q hq).2 ⟨hh.1.1, hh.2⟩⟩,
    ⟨h.hd_act, hhd⟩, h.hd_G, ⟨h.lt_act, hlt⟩, h.lt_G⟩

/-- The run obtained by merging `R` and `R'` through the segment from `rlt R` to `rhd R'`. -/
def mergeR (R R' : List (List V)) : List (List V) :=
  R.dropLast ++ (R.getLastD [] ++ sInner (g.seg (g.rlt R) (g.rhd R'))) :: R'

/-- **Merging two runs** whose ends `rlt R`, `rhd R'` lie in the same interval `J`: the result is
again a family of runs (with `J` deactivated), of at least the same size. -/
lemma RunsOK.merge {act : V → Prop} {G : β} {R R' : List (List V)} {Rs : List (List (List V))}
    (h : g.RunsOK act G (R :: R' :: Rs)) {J : ι}
    (hJ : g.ivOf (g.rlt R) = some J) (hJ' : g.ivOf (g.rhd R') = some J)
    (hunif : ∀ v w, g.ivOf v = some J → g.ivOf w = some J → act v → act w) :
    g.RunsOK (fun v => act v ∧ g.ivOf v ≠ some J) G (g.mergeR R R' :: Rs) ∧
    g.szR act R + g.szR act R' ≤ g.szR (fun v => act v ∧ g.ivOf v ≠ some J) (g.mergeR R R') ∧
    g.rhd (g.mergeR R R') = g.rhd R ∧ g.rlt (g.mergeR R R') = g.rlt R' ∧
    (∀ v ∈ (g.mergeR R R').flatten, v ∈ R.flatten ∨ v ∈ R'.flatten ∨ g.ivOf v = some J) ∧
    (∀ v, v ∈ R.flatten ∨ v ∈ R'.flatten → v ∈ (g.mergeR R R').flatten) := by
  have h1 := h.run R (by simp)
  have h2 := h.run R' (by simp)
  have hN := h.nodup
  have eN : (R :: R' :: Rs).flatten.flatten = R.flatten ++ (R'.flatten ++ Rs.flatten.flatten) := by
    simp
  rw [eN] at hN
  have hRn : R.flatten.Nodup := (List.nodup_append.1 hN).1
  have hR'n : R'.flatten.Nodup := (List.nodup_append.1 (List.nodup_append.1 hN).2.1).1
  have hdis1 : ∀ a ∈ R.flatten, ∀ b ∈ R'.flatten ++ Rs.flatten.flatten, a ≠ b :=
    (List.nodup_append.1 hN).2.2
  have hdis2 : ∀ a ∈ R'.flatten, ∀ b ∈ Rs.flatten.flatten, a ≠ b :=
    (List.nodup_append.1 (List.nodup_append.1 hN).2.1).2.2
  have hstr : ∀ Q ∈ R :: R' :: Rs, ∀ τ ∈ Q, g.StrandOK act τ := fun Q hQ τ hτ =>
    (h.run Q hQ).strand τ hτ
  obtain ⟨D, σ, rfl⟩ := (List.eq_nil_or_concat' R).resolve_left h1.ne
  have hrlt : g.rlt (D ++ [σ]) = g.lt σ := by simp [rlt]
  rw [hrlt] at hJ
  set p := g.lt σ with hp
  set p' := g.rhd R' with hp'
  have hσ : g.StrandOK act σ := h1.strand σ (by simp)
  have hpR : p ∈ (D ++ [σ]).flatten := by rw [← hrlt]; exact g.rlt_mem h1
  have hp'R' : p' ∈ R'.flatten := g.rhd_mem h2
  have hpp' : p ≠ p' := hdis1 _ hpR _ (List.mem_append_left _ hp'R')
  have hactp : act p := by rw [← hrlt]; exact h1.lt_act
  have hbdp : g.IsBd p := g.bd_of_act_mem hσ (g.lt_mem (g.ne_nil_of_strand hσ)) hactp
  obtain ⟨τ0, t', hR'⟩ := List.exists_cons_of_ne_nil h2.ne
  have hbdp' : g.IsBd p' := by
    have hh : g.rhd R' = g.hd τ0 := by rw [hR']; rfl
    rw [hp', hh]; exact (h2.strand τ0 (by rw [hR']; simp)).hd_bd (hh ▸ h2.hd_act)
  have key : ∀ Q ∈ (D ++ [σ]) :: R' :: Rs, ∀ v ∈ Q.flatten, g.ivOf v = some J → v = p ∨ v = p' := by
    intro Q hQ v hv hvJ
    obtain ⟨τ, hτ, hvτ⟩ := List.mem_flatten.1 hv
    exact g.eq_of_bd (g.bd_of_act_mem (hstr Q hQ τ hτ) hvτ (hunif p v hJ hvJ hactp)) hbdp hbdp'
      hvJ hJ hJ' hpp'
  have hJG : g.blk J = some G := by
    have := h1.lt_G; rw [hrlt] at this; unfold vb at this; rwa [hJ, Option.bind_some] at this
  obtain ⟨hτ, hτhd, hτJ, hτadj, hτc⟩ := hσ.extend g hJ hJ' hpp'
  set X := sInner (g.seg p p') with hX
  set τ := σ ++ X with hτdef
  have hmerge : g.mergeR (D ++ [σ]) R' = (D ++ [τ]) ++ R' := by
    unfold mergeR; rw [hrlt, ← hp']; simp [τ, X]
  rw [hmerge]
  -- the ends of `R` and `R'` are not in `J`
  have hhdR : g.ivOf (g.rhd (D ++ [σ])) ≠ some J := by
    intro hh
    rcases key _ (by simp) _ (g.rhd_mem h1) hh with e | e
    · exact h1.hd_ne_lt g hRn (e.trans hrlt.symm)
    · exact hdis1 _ (g.rhd_mem h1) _ (List.mem_append_left _ hp'R') e
  have hltR' : g.ivOf (g.rlt R') ≠ some J := by
    intro hh
    rcases key R' (by simp) _ (g.rlt_mem h2) hh with e | e
    · exact hdis1 _ hpR _ (List.mem_append_left _ (g.rlt_mem h2)) e.symm
    · exact h2.hd_ne_lt g hR'n e.symm
  have hrhdM : g.rhd ((D ++ [τ]) ++ R') = g.rhd (D ++ [σ]) := by
    rw [g.rhd_append _ _ (by simp), g.rhd_snoc hτhd]
  have hrltM : g.rlt ((D ++ [τ]) ++ R') = g.rlt R' := g.rlt_append _ _ h2.ne
  have hlastτ : (D ++ [τ]).getLast (by simp) = τ := by simp
  have hheadR' : g.hd (R'.head h2.ne) = p' := by rw [hp', g.rhd_eq_head h2.ne]
  refine ⟨⟨by simp, ?_, ?_⟩, ?_, hrhdM, hrltM, ?_, ?_⟩
  · intro Q hQ
    rcases List.mem_cons.1 hQ with rfl | hQ
    · refine ⟨by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro ρ hρ
        simp only [List.append_assoc, List.singleton_append, List.mem_append, List.mem_cons] at hρ
        rcases hρ with hρ | rfl | hρ
        · exact (h1.strand ρ (by simp [hρ])).mono g (fun _ hv => hv.1)
        · exact hτ
        · exact (h2.strand ρ hρ).mono g (fun _ hv => hv.1)
      · intro q hq
        rw [lpairs_append _ _ (by simp) h2.ne, hlastτ, List.mem_append, List.mem_cons] at hq
        rcases hq with hq | rfl | hq
        · have hm : (g.lt q.1, g.hd q.2) ∈ (lpairs (D ++ [σ])).map (fun q => (g.lt q.1, g.hd q.2)) := by
            rw [← g.lpairs_snoc_map hτhd]; exact List.mem_map_of_mem hq
          obtain ⟨q', hq', e⟩ := List.mem_map.1 hm
          simp only [Prod.mk.injEq] at e
          rw [← e.1, ← e.2]
          obtain ⟨j1, j2⟩ := h1.join q' hq'
          exact ⟨j1.deact g j2 hJG, fun hh => j2 ⟨hh.1.1, hh.2⟩⟩
        · simp only
          rw [hheadR']
          exact ⟨Or.inr ⟨fun hh => hh.2 hτJ, fun hh => hh.2 hJ', hτadj⟩, fun hh => hh.1.2 hτJ⟩
        · obtain ⟨j1, j2⟩ := h2.join q hq
          exact ⟨j1.deact g j2 hJG, fun hh => j2 ⟨hh.1.1, hh.2⟩⟩
      · rw [hrhdM]; exact ⟨h1.hd_act, hhdR⟩
      · rw [hrhdM]; exact h1.hd_G
      · rw [hrltM]; exact ⟨h2.lt_act, hltR'⟩
      · rw [hrltM]; exact h2.lt_G
    · have hQ' := h.run Q (by simp [hQ])
      have hdisQ : ∀ v ∈ Q.flatten, v ≠ p ∧ v ≠ p' := by
        intro v hv
        have hvRs : v ∈ Rs.flatten.flatten :=
          List.mem_flatten.2 ⟨Q.flatten, List.mem_map.2 ⟨Q, hQ, rfl⟩, hv⟩ |> fun hh => by
            simpa [List.flatten_flatten] using hh
        exact ⟨fun e => hdis1 _ hpR _ (List.mem_append_right _ hvRs) e.symm,
          fun e => hdis2 _ hp'R' _ hvRs e.symm⟩
      refine hQ'.deact g hJG ?_ ?_
      · intro hh
        have := hdisQ _ (g.rhd_mem hQ')
        rcases key Q (by simp [hQ]) _ (g.rhd_mem hQ') hh with e | e
        · exact this.1 e
        · exact this.2 e
      · intro hh
        have := hdisQ _ (g.rlt_mem hQ')
        rcases key Q (by simp [hQ]) _ (g.rlt_mem hQ') hh with e | e
        · exact this.1 e
        · exact this.2 e
  · have e1 : (((D ++ [τ]) ++ R') :: Rs).flatten.flatten =
        (D.flatten ++ σ) ++ X ++ (R'.flatten ++ Rs.flatten.flatten) := by simp [τ]
    have e2 : (D ++ [σ]).flatten = D.flatten ++ σ := by simp
    rw [e1]
    have hperm : ((D.flatten ++ σ) ++ X ++ (R'.flatten ++ Rs.flatten.flatten)).Perm
        (X ++ ((D ++ [σ]).flatten ++ (R'.flatten ++ Rs.flatten.flatten))) := by
      rw [e2, ← List.append_assoc X]
      exact List.perm_append_comm.append_right _
    refine hperm.nodup_iff.2 (List.nodup_append.2 ⟨inner_nodup (g.seg_nodup hJ hJ'), hN, ?_⟩)
    intro a ha b hb hab
    subst hab
    have hn := notMem_inner_of_nodup (g.seg_head hJ hJ') (g.seg_last hJ hJ')
      (g.seg_nodup hJ hJ') ha
    have haJ : g.ivOf a = some J :=
      g.seg_iv hJ hJ' a (List.tail_subset _ (List.dropLast_subset _ ha))
    have hQ : ∃ Q ∈ (D ++ [σ]) :: R' :: Rs, a ∈ Q.flatten := by
      simp only [List.mem_append] at hb
      rcases hb with hb | hb | hb
      · exact ⟨_, by simp, hb⟩
      · exact ⟨R', by simp, hb⟩
      · obtain ⟨τ', hτ', haτ⟩ := List.mem_flatten.1 hb
        obtain ⟨Q, hQ, hτQ⟩ := List.mem_flatten.1 hτ'
        exact ⟨Q, by simp [hQ], List.mem_flatten.2 ⟨τ', hτQ, haτ⟩⟩
    obtain ⟨Q, hQ, haQ⟩ := hQ
    rcases key Q hQ a haQ haJ with e | e
    · exact hn.1 e
    · exact hn.2 e
  · rw [g.szR_append _ _ _ (by simp) h2.ne]
    have a1 := g.szR_snoc_le (fun v => act v ∧ g.ivOf v ≠ some J) (D := D) hτhd hτc
    have a2 := g.szR_mono (act := act) (act' := fun v => act v ∧ g.ivOf v ≠ some J)
      (fun v hv => hv.1) (D ++ [σ])
    have a3 := g.szR_mono (act := act) (act' := fun v => act v ∧ g.ivOf v ≠ some J)
      (fun v hv => hv.1) R'
    omega
  · intro v hv
    have : v ∈ D.flatten ∨ v ∈ σ ∨ v ∈ X ∨ v ∈ R'.flatten := by simpa [τ, or_assoc] using hv
    rcases this with hv | hv | hv | hv
    · exact Or.inl (by simp [hv])
    · exact Or.inl (by simp [hv])
    · exact Or.inr (Or.inr (g.seg_iv hJ hJ' v (List.tail_subset _ (List.dropLast_subset _ hv))))
    · exact Or.inr (Or.inl hv)
  · intro v hv
    rcases hv with hv | hv
    · have : v ∈ D.flatten ∨ v ∈ σ := by simpa using hv
      rcases this with h' | h' <;> simp [τ, h']
    · simp [hv]

end Geo

end Lovasz
