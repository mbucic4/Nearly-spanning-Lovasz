module
public import RequestProject.Merge

/-!
# Normalising a family of runs

Repeatedly merging runs whose ends share an interval, we reach a family of runs whose
junctions are pairwise disjoint (so that the linking lemma can be applied to them).
-/

@[expose] public section


open Classical

namespace Lovasz

/-- Two junctions are disjoint. -/
def JDisj {ι : Type*} (a b : ι × ι) : Prop := a.1 ≠ b.1 ∧ a.1 ≠ b.2 ∧ a.2 ≠ b.1 ∧ a.2 ≠ b.2

lemma jEntries_nodup_of_pairwise {ι : Type*} :
    ∀ {Jn : List (ι × ι)}, Jn.Pairwise JDisj → (jEntries Jn).Nodup
  | [], _ => by simp [jEntries]
  | p :: Jn, h => by
    rw [List.pairwise_cons] at h
    have ih := jEntries_nodup_of_pairwise h.2
    have e : jEntries (p :: Jn) = (if p.1 = p.2 then [p.1] else [p.1, p.2]) ++ jEntries Jn := by
      simp [jEntries]
    rw [e, List.nodup_append]
    refine ⟨by split_ifs with h' <;> simp [h'], ih, ?_⟩
    intro a ha b hb hab
    subst hab
    obtain ⟨q, hq, hbq⟩ := mem_jEntries.1 hb
    have hd := h.1 q hq
    have ha' : a = p.1 ∨ a = p.2 := by split_ifs at ha <;> simp at ha <;> tauto
    unfold JDisj at hd
    rcases ha' with rfl | rfl <;> rcases hbq with h1 | h1 <;> tauto

namespace Geo

variable {V ι β : Type*} (g : Geo V ι β)

/-- The activity predicate given by a set of active intervals. -/
def actI (A : Set ι) (v : V) : Prop := ∃ J, g.ivOf v = some J ∧ J ∈ A

lemma actI_diff (A : Set ι) (J : ι) :
    g.actI (A \ {J}) = fun v => g.actI A v ∧ g.ivOf v ≠ some J := by
  funext v
  apply propext
  constructor
  · rintro ⟨J', h1, h2, h3⟩
    exact ⟨⟨J', h1, h2⟩, fun h => h3 (by rw [h1, Option.some.injEq] at h; exact h)⟩
  · rintro ⟨⟨J', h1, h2⟩, h3⟩
    exact ⟨J', h1, h2, fun h => h3 (by rw [h1, Set.mem_singleton_iff.1 h])⟩

lemma actI_unif (A : Set ι) {J : ι} {v w : V} (hv : g.ivOf v = some J) (hw : g.ivOf w = some J)
    (ha : g.actI A v) : g.actI A w := by
  obtain ⟨J', h1, h2⟩ := ha
  rw [hv, Option.some.injEq] at h1
  subst h1
  exact ⟨J, hw, h2⟩

lemma iv_of_actI {A : Set ι} {v : V} (h : g.actI A v) : g.ivOf v = some (g.iv v) := by
  obtain ⟨J, h1, -⟩ := h
  simp [iv, h1]

/-- `e` is an end of one of the runs of `Rs`. -/
def IsEnd (Rs : List (List (List V))) (e : V) : Prop := ∃ R ∈ Rs, e = g.rhd R ∨ e = g.rlt R

lemma RunsOK.rev_head {act : V → Prop} {G : β} {R : List (List V)} {Rs : List (List (List V))}
    (h : g.RunsOK act G (R :: Rs)) : g.RunsOK act G (revRun R :: Rs) := by
  refine ⟨by simp, fun Q hQ => ?_, ?_⟩
  · rcases List.mem_cons.1 hQ with rfl | hQ
    · exact ((h.run R (by simp)).rev g).1
    · exact h.run Q (by simp [hQ])
  · have := h.nodup
    simp only [List.flatten_cons, List.flatten_append] at this ⊢
    exact (((flatten_revRun_perm R).append_right _)).nodup_iff.2 this

/-- Orienting two runs. -/
lemma RunsOK.orient {act : V → Prop} {G : β} {a b : List (List V)} {Rs : List (List (List V))}
    (h : g.RunsOK act G (a :: b :: Rs)) (ba bb : Bool) :
    g.RunsOK act G ((if ba then revRun a else a) :: (if bb then revRun b else b) :: Rs) := by
  have h1 : g.RunsOK act G ((if ba then revRun a else a) :: b :: Rs) := by
    cases ba
    · exact h
    · exact h.rev_head g
  have h2 : g.RunsOK act G (b :: (if ba then revRun a else a) :: Rs) :=
    h1.perm g (List.Perm.swap _ _ _)
  have h3 : g.RunsOK act G ((if bb then revRun b else b) :: (if ba then revRun a else a) :: Rs) := by
    cases bb
    · exact h2
    · exact h2.rev_head g
  exact h3.perm g (List.Perm.swap _ _ _)

lemma szR_ori (act : V → Prop) {G : β} {a : List (List V)} (h : g.RunOK act G a) (b : Bool) :
    g.szR act (if b then revRun a else a) = g.szR act a := by
  cases b
  · rfl
  · exact (h.rev g).2

lemma rhd_ori (a : List (List V)) (b : Bool) :
    g.rhd (if b then revRun a else a) = g.rhd a ∨ g.rhd (if b then revRun a else a) = g.rlt a := by
  cases b
  · exact Or.inl rfl
  · exact Or.inr (g.rhd_revRun a)

lemma rlt_ori (a : List (List V)) (b : Bool) :
    g.rlt (if b then revRun a else a) = g.rhd a ∨ g.rlt (if b then revRun a else a) = g.rlt a := by
  cases b
  · exact Or.inr rfl
  · exact Or.inl (g.rlt_revRun a)

lemma mem_flatten_ori {a : List (List V)} {b : Bool} {v : V}
    (hv : v ∈ (if b then revRun a else a).flatten) : v ∈ a.flatten := by
  cases b
  · exact hv
  · exact (flatten_revRun_perm a).mem_iff.1 hv

lemma mem_flatten_ori' {a : List (List V)} {b : Bool} {v : V}
    (hv : v ∈ a.flatten) : v ∈ (if b then revRun a else a).flatten := by
  cases b
  · exact hv
  · exact (flatten_revRun_perm a).mem_iff.2 hv

/-- **Normalisation** of a family of runs. -/
theorem normalize {G : β} : ∀ (n : ℕ) (A : Set ι) (Rs : List (List (List V))), Rs.length = n →
    g.RunsOK (g.actI A) G Rs →
    ∃ A' ⊆ A, ∃ Rs', g.RunsOK (g.actI A') G Rs' ∧
      (Rs.map (g.szR (g.actI A))).sum ≤ (Rs'.map (g.szR (g.actI A'))).sum ∧
      (Rs'.map g.junc).Pairwise JDisj ∧
      (∀ R' ∈ Rs', g.IsEnd Rs (g.rhd R') ∧ g.IsEnd Rs (g.rlt R')) ∧
      (∀ R' ∈ Rs', ∀ v ∈ R'.flatten, (∃ R ∈ Rs, v ∈ R.flatten) ∨
        ∃ J ∈ A, J ∉ A' ∧ g.ivOf v = some J) ∧
      (∀ J ∈ A, J ∉ A' → ∃ e, g.IsEnd Rs e ∧ g.ivOf e = some J) ∧
      (∀ R ∈ Rs, ∀ v ∈ R.flatten, ∃ R' ∈ Rs', v ∈ R'.flatten) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A Rs hn h
  by_cases hP : (Rs.map g.junc).Pairwise JDisj
  · refine ⟨A, le_rfl, Rs, h, le_rfl, hP, fun R' hR' => ⟨⟨R', hR', Or.inl rfl⟩, ⟨R', hR', Or.inr rfl⟩⟩,
      fun R' hR' v hv => Or.inl ⟨R', hR', hv⟩, fun J hJ hJ' => absurd hJ hJ',
      fun R hR v hv => ⟨R, hR, hv⟩⟩
  rw [List.pairwise_map, List.pairwise_iff_forall_sublist] at hP
  push_neg at hP
  obtain ⟨a, b, hsub, hab⟩ := hP
  obtain ⟨rest, hperm⟩ := hsub.exists_perm_append
  have h0 : g.RunsOK (g.actI A) G (a :: b :: rest) := h.perm g hperm
  have ha := h0.run a (by simp)
  have hb := h0.run b (by simp)
  obtain ⟨ba, bb, hJeq⟩ : ∃ ba bb : Bool, g.iv (g.rlt (if ba then revRun a else a)) =
      g.iv (g.rhd (if bb then revRun b else b)) := by
    unfold JDisj junc at hab
    simp only at hab
    by_cases h1 : g.iv (g.rhd a) = g.iv (g.rhd b)
    · exact ⟨true, false, by simpa [g.rlt_revRun] using h1⟩
    by_cases h2 : g.iv (g.rhd a) = g.iv (g.rlt b)
    · exact ⟨true, true, by simpa [g.rlt_revRun, g.rhd_revRun] using h2⟩
    by_cases h3 : g.iv (g.rlt a) = g.iv (g.rhd b)
    · exact ⟨false, false, by simpa using h3⟩
    have h4 : g.iv (g.rlt a) = g.iv (g.rlt b) := by tauto
    exact ⟨false, true, by simpa [g.rhd_revRun] using h4⟩
  have e2 := g.szR_ori (g.actI A) ha ba
  have e3 := g.szR_ori (g.actI A) hb bb
  have hra := g.rhd_ori a ba
  have hla := g.rlt_ori a ba
  have hlb := g.rlt_ori b bb
  set R1 := if ba then revRun a else a with hR1
  set R2 := if bb then revRun b else b with hR2
  have h1 : g.RunsOK (g.actI A) G (R1 :: R2 :: rest) := h0.orient g ba bb
  have hr1 := h1.run R1 (by simp)
  have hr2 := h1.run R2 (by simp)
  set J := g.iv (g.rlt R1) with hJdef
  have hJ1 : g.ivOf (g.rlt R1) = some J := g.iv_of_actI hr1.lt_act
  have hJ2 : g.ivOf (g.rhd R2) = some J := by rw [hJeq]; exact g.iv_of_actI hr2.hd_act
  have hJA : J ∈ A := by
    obtain ⟨J', h', hJ'⟩ := hr1.lt_act; rw [hJ1, Option.some.injEq] at h'; rwa [h']
  obtain ⟨hM, hsz, hrhd, hrlt, hmem, hmem2⟩ :=
    h1.merge g hJ1 hJ2 (fun v w hv hw hav => g.actI_unif A hv hw hav)
  rw [← g.actI_diff] at hM hsz
  obtain ⟨A', hA', Rs', hRs', hsz', hP', hends', hmem', hdeact', hold'⟩ :=
    ih (rest.length + 1) (by rw [← hn, hperm.length_eq]; simp) (A \ {J}) _ (by simp) hM
  have hainRs : a ∈ Rs := hperm.mem_iff.2 (by simp)
  have hbinRs : b ∈ Rs := hperm.mem_iff.2 (by simp)
  have hE : ∀ e, g.IsEnd (g.mergeR R1 R2 :: rest) e → g.IsEnd Rs e := by
    rintro e ⟨Q, hQ, hQe⟩
    rcases List.mem_cons.1 hQ with rfl | hQ
    · rw [hrhd, hrlt] at hQe
      rcases hQe with rfl | rfl
      · rcases hra with e' | e'
        · exact ⟨a, hainRs, Or.inl e'⟩
        · exact ⟨a, hainRs, Or.inr e'⟩
      · rcases hlb with e' | e'
        · exact ⟨b, hbinRs, Or.inl e'⟩
        · exact ⟨b, hbinRs, Or.inr e'⟩
    · exact ⟨Q, hperm.mem_iff.2 (by simp [hQ]), hQe⟩
  refine ⟨A', hA'.trans Set.diff_subset, Rs', hRs', ?_, hP', ?_, ?_, ?_, ?_⟩
  · have e1 : (Rs.map (g.szR (g.actI A))).sum = g.szR (g.actI A) a + g.szR (g.actI A) b +
        (rest.map (g.szR (g.actI A))).sum := by
      rw [(hperm.map _).sum_eq]; simp; ring
    have hmono : (rest.map (g.szR (g.actI A))).sum ≤
        (rest.map (g.szR (g.actI (A \ {J})))).sum :=
      List.sum_le_sum fun R _ => g.szR_mono (fun v hv => by rw [g.actI_diff] at hv; exact hv.1) R
    simp only [List.map_cons, List.sum_cons] at hsz'
    rw [e1]; omega
  · intro R' hR'
    exact ⟨hE _ (hends' R' hR').1, hE _ (hends' R' hR').2⟩
  · intro R' hR' v hv
    rcases hmem' R' hR' v hv with ⟨Q, hQ, hvQ⟩ | ⟨J', hJ'A, hJ'A', hvJ'⟩
    · rcases List.mem_cons.1 hQ with rfl | hQ
      · rcases hmem v hvQ with hv1 | hv2 | hv3
        · exact Or.inl ⟨a, hainRs, mem_flatten_ori hv1⟩
        · exact Or.inl ⟨b, hbinRs, mem_flatten_ori hv2⟩
        · exact Or.inr ⟨J, hJA, fun hh => (hA' hh).2 (Set.mem_singleton J), hv3⟩
      · exact Or.inl ⟨Q, hperm.mem_iff.2 (by simp [hQ]), hvQ⟩
    · exact Or.inr ⟨J', hJ'A.1, hJ'A', hvJ'⟩
  · intro J' hJ'A hJ'A'
    by_cases hJJ : J' = J
    · subst hJJ
      refine ⟨g.rlt R1, ?_, hJ1⟩
      rcases hla with e' | e'
      · exact ⟨a, hainRs, Or.inl e'⟩
      · exact ⟨a, hainRs, Or.inr e'⟩
    · obtain ⟨e, he, heJ⟩ := hdeact' J' ⟨hJ'A, hJJ⟩ hJ'A'
      exact ⟨e, hE e he, heJ⟩
  · intro R hR v hv
    have hR' := hperm.mem_iff.1 hR
    simp only [List.cons_append, List.nil_append, List.mem_cons] at hR'
    rcases hR' with rfl | rfl | hR'
    · exact hold' _ (by simp) v (hmem2 v (Or.inl (mem_flatten_ori' hv)))
    · exact hold' _ (by simp) v (hmem2 v (Or.inr (mem_flatten_ori' hv)))
    · exact hold' R (by simp [hR']) v hv

end Geo

end Lovasz
