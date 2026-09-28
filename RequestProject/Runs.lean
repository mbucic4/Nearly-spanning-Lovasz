module
public import RequestProject.Circuit

/-!
# Runs of a circuit at a block

Cutting a circuit at all jumps inside a block `G` produces *runs*: lists of strands whose inner
junctions are not jumps at `G`, and whose two ends are active vertices of `G`.  Since the
junctions between runs are jumps at `G`, runs may be permuted and reversed freely.
-/

@[expose] public section


open Classical

namespace Lovasz

section lists

variable {α : Type*}

lemma lpairs_flatten_perm (d : α) (Rs : List (List α)) (hne : ∀ R ∈ Rs, R ≠ []) :
    (lpairs Rs.flatten).Perm ((Rs.map lpairs).flatten ++
      (lpairs Rs).map (fun q => (q.1.getLastD d, q.2.headD d))) := by
  induction Rs with
  | nil => simp
  | cons R t ih =>
    have ih' := ih (fun R' h => hne R' (by simp [h]))
    have hR := hne R (by simp)
    cases t with
    | nil => simp
    | cons R' t =>
      have hR' := hne R' (by simp)
      have hft : (R' :: t).flatten ≠ [] := by simp [hR']
      have e1 : R.getLast hR = R.getLastD d := by
        rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hR]; rfl
      have e2 : (R' :: t).flatten.head hft = R'.headD d := by
        obtain ⟨a, u, rfl⟩ := List.exists_cons_of_ne_nil hR'; simp
      rw [List.flatten_cons, lpairs_append R _ hR hft, e1, e2]
      have eR : ((R :: R' :: t).map lpairs).flatten = lpairs R ++ ((R' :: t).map lpairs).flatten := by
        simp
      have eL : lpairs (R :: R' :: t) = (R, R') :: lpairs (R' :: t) := rfl
      rw [eR, eL, List.map_cons, List.append_assoc]
      refine List.Perm.append_left _ ?_
      exact (List.Perm.cons _ ih').trans List.perm_middle.symm

lemma cpairs_flatten_perm (d : α) (Rs : List (List α)) (hne : ∀ R ∈ Rs, R ≠ []) :
    (cpairs Rs.flatten).Perm ((Rs.map lpairs).flatten ++
      (cpairs Rs).map (fun q => (q.1.getLastD d, q.2.headD d))) := by
  rcases eq_or_ne Rs [] with rfl | hRs
  · simp
  obtain ⟨R, t, rfl⟩ := List.exists_cons_of_ne_nil hRs
  have hR := hne R (by simp)
  obtain ⟨a, u, rfl⟩ := List.exists_cons_of_ne_nil hR
  have hfl : (((a :: u) :: t).flatten) = a :: (u ++ t.flatten) := by simp
  rw [hfl, cpairs_cons, cpairs_cons, ← hfl]
  have hflne : ((a :: u) :: t).flatten ≠ [] := by simp
  rw [lpairs_append_singleton _ _ hflne, lpairs_append_singleton _ _ (by simp)]
  simp only [List.map_append, List.map_cons, List.map_nil]
  rw [← List.append_assoc]
  refine List.Perm.append_right _ (lpairs_flatten_perm d _ hne) |>.trans ?_
  simp only [List.append_assoc]
  refine List.Perm.append_left _ (List.Perm.append_left _ ?_)
  have hl : ((a :: u) :: t).getLast (by simp) ≠ [] := hne _ (List.getLast_mem _)
  have e1 : (((a :: u) :: t).flatten).getLast hflne =
      (((a :: u) :: t).getLast (by simp)).getLastD d := by
    have h1 : ((a :: u) :: t).flatten.getLast? = (((a :: u) :: t).getLast (by simp)).getLast? := by
      conv_lhs => rw [← List.dropLast_append_getLast (l := (a :: u) :: t) (by simp)]
      rw [List.flatten_append, List.flatten_singleton, List.getLast?_append_of_ne_nil _ hl]
    rw [List.getLast?_eq_some_getLast hflne, List.getLast?_eq_some_getLast hl] at h1
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hl]
    simpa using h1
  rw [e1]; rfl

end lists

/-- Reversal of a run. -/
def revRun {V : Type*} (R : List (List V)) : List (List V) := (R.map List.reverse).reverse

namespace Geo

variable {V ι β : Type*} (g : Geo V ι β)

/-- The interval of a vertex (with a default value). -/
def iv (v : V) : ι := (g.ivOf v).getD g.dI


/-- First vertex of a run. -/
def rhd (R : List (List V)) : V := g.hd (R.headD [])

/-- Last vertex of a run. -/
def rlt (R : List (List V)) : V := g.lt (R.getLastD [])

/-- A run at the block `G`. -/
structure RunOK (act : V → Prop) (G : β) (R : List (List V)) : Prop where
  ne : R ≠ []
  strand : ∀ σ ∈ R, g.StrandOK act σ
  join : ∀ p ∈ lpairs R, g.JoinOK act (g.lt p.1) (g.hd p.2) ∧
    ¬ (act (g.lt p.1) ∧ g.vb (g.lt p.1) = some G)
  hd_act : act (g.rhd R)
  hd_G : g.vb (g.rhd R) = some G
  lt_act : act (g.rlt R)
  lt_G : g.vb (g.rlt R) = some G

/-- A family of runs at `G` forming a circuit (in any order). -/
structure RunsOK (act : V → Prop) (G : β) (Rs : List (List (List V))) : Prop where
  ne : Rs ≠ []
  run : ∀ R ∈ Rs, g.RunOK act G R
  nodup : Rs.flatten.flatten.Nodup

/-- The size of a run. -/
noncomputable def szR (act : V → Prop) (R : List (List V)) : ℕ :=
  (R.map (countPairs g.Mp)).sum + ((lpairs R).map (fun p => g.joinVal act (g.lt p.1) (g.hd p.2))).sum

/-- The junction of a run: the intervals of its two ends. -/
def junc (R : List (List V)) : ι × ι := (g.iv (g.rhd R), g.iv (g.rlt R))

lemma lt_eq_getLastD (σ : List V) : g.lt σ = σ.getLastD g.dflt := rfl

lemma RunsOK.circ {act : V → Prop} {G : β} {Rs : List (List (List V))} (h : g.RunsOK act G Rs) :
    g.Circ act Rs.flatten ∧ g.sz act Rs.flatten = (Rs.map (g.szR act)).sum := by
  have hne : ∀ R ∈ Rs, R ≠ [] := fun R hR => (h.run R hR).ne
  have hperm := cpairs_flatten_perm [] Rs hne
  have hjG : ∀ q ∈ cpairs Rs, g.JoinOK act (g.lt (q.1.getLastD [])) (g.hd (q.2.headD [])) ∧
      g.joinVal act (g.lt (q.1.getLastD [])) (g.hd (q.2.headD [])) = 0 := by
    intro q hq
    have h1 := h.run _ (mem_of_mem_cpairs_fst hq)
    have h2 := h.run _ (mem_of_mem_cpairs_snd hq)
    refine ⟨Or.inl ⟨h1.lt_act, h2.hd_act, G, h1.lt_G, h2.hd_G⟩, ?_⟩
    unfold joinVal; rw [if_neg]; exact fun h' => h'.1 h1.lt_act
  refine ⟨⟨?_, ?_, h.nodup, ?_⟩, ?_⟩
  · intro h'
    obtain ⟨R, hR⟩ := List.exists_mem_of_ne_nil _ h.ne
    exact hne R hR (List.flatten_eq_nil_iff.1 h' R hR)
  · intro σ hσ
    obtain ⟨R, hR, hσR⟩ := List.mem_flatten.1 hσ
    exact (h.run R hR).strand σ hσR
  · intro p hp
    rcases List.mem_append.1 (hperm.mem_iff.1 hp) with hp | hp
    · obtain ⟨l, hl, hpl⟩ := List.mem_flatten.1 hp
      obtain ⟨R, hR, rfl⟩ := List.mem_map.1 hl
      exact ((h.run R hR).join p hpl).1
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact (hjG q hq).1
  · unfold sz
    rw [(hperm.map _).sum_eq, List.map_append, List.sum_append, List.map_map]
    have e2 : ((cpairs Rs).map ((fun p : List V × List V => g.joinVal act (g.lt p.1) (g.hd p.2)) ∘
        (fun q => (q.1.getLastD [], q.2.headD [])))).sum = 0 := by
      refine List.sum_eq_zero fun x hx => ?_
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
      exact (hjG q hq).2
    rw [e2, add_zero]
    clear hjG hperm e2 h hne
    induction Rs with
    | nil => rfl
    | cons R t ih =>
      simp only [List.flatten_cons, List.map_append, List.sum_append, List.map_cons,
        List.sum_cons, szR] at ih ⊢
      rw [← ih]; ring

end Geo

section lists2

variable {α : Type*}

lemma exists_split (P : α → Prop) (l : List α) (hl : l ≠ []) (hlast : P (l.getLast hl)) :
    ∃ Rs : List (List α), Rs.flatten = l ∧
      ∀ R ∈ Rs, ∃ h : R ≠ [], P (R.getLast h) ∧ ∀ x ∈ R.dropLast, ¬ P x := by
  induction l with
  | nil => exact absurd rfl hl
  | cons a t ih =>
    rcases eq_or_ne t [] with rfl | ht
    · refine ⟨[[a]], by simp, ?_⟩
      intro R hR
      simp only [List.mem_singleton] at hR; subst hR
      exact ⟨by simp, by simpa using hlast, by simp⟩
    have hlast' : P (t.getLast ht) := by rwa [List.getLast_cons ht] at hlast
    obtain ⟨Rs, hRs, hR⟩ := ih ht hlast'
    by_cases ha : P a
    · refine ⟨[a] :: Rs, by simp [hRs], ?_⟩
      intro R hR'
      rcases List.mem_cons.1 hR' with rfl | hR'
      · exact ⟨by simp, by simpa using ha, by simp⟩
      · exact hR R hR'
    · obtain ⟨R₁, rest, rfl⟩ : ∃ R₁ rest, Rs = R₁ :: rest := by
        cases Rs with
        | nil => exact absurd (by simpa using hRs.symm) ht
        | cons R₁ rest => exact ⟨R₁, rest, rfl⟩
      obtain ⟨hR₁, hP₁, hd₁⟩ := hR R₁ (by simp)
      refine ⟨(a :: R₁) :: rest, by simp [← hRs], ?_⟩
      intro R hR'
      rcases List.mem_cons.1 hR' with rfl | hR'
      · refine ⟨by simp, by rwa [List.getLast_cons hR₁], ?_⟩
        intro x hx
        rw [List.dropLast_cons_of_ne_nil hR₁, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ha
        · exact hd₁ x hx
      · exact hR R (List.mem_cons_of_mem _ hR')

lemma fst_mem_dropLast_of_mem_lpairs {l : List α} {p : α × α} (hp : p ∈ lpairs l) :
    p.1 ∈ l.dropLast := by
  induction l with
  | nil => simp at hp
  | cons a t ih =>
    cases t with
    | nil => simp at hp
    | cons b t =>
      rw [lpairs_cons_cons, List.mem_cons] at hp
      rw [List.dropLast_cons_of_ne_nil (by simp), List.mem_cons]
      rcases hp with rfl | hp
      · exact Or.inl rfl
      · exact Or.inr (ih hp)

lemma mem_lpairs_mem {l : List α} {p : α × α} (hp : p ∈ lpairs l) : p.1 ∈ l ∧ p.2 ∈ l :=
  ⟨(List.of_mem_zip hp).1, List.tail_subset _ (List.of_mem_zip hp).2⟩

lemma lpairs_sub_cpairs {l : List α} {p : α × α} (hp : p ∈ lpairs l) : p ∈ cpairs l := by
  cases l with
  | nil => simp at hp
  | cons a t =>
    rw [cpairs_cons, lpairs_append_singleton _ _ (by simp)]
    exact List.mem_append_left _ hp

lemma exists_cpairs_snd {l : List α} {x : α} (hx : x ∈ l) : ∃ q ∈ cpairs l, q.2 = x := by
  cases l with
  | nil => simp at hx
  | cons a t =>
    rw [cpairs_cons]
    rcases List.mem_cons.1 hx with rfl | hx
    · refine ⟨((x :: t).getLast (by simp), x), ?_, rfl⟩
      rw [lpairs_append_singleton _ _ (by simp)]; simp
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      refine ⟨((a :: t)[i]'(by simp; omega), t[i]), ?_, rfl⟩
      rw [lpairs_append_singleton _ _ (by simp)]
      refine List.mem_append_left _ ?_
      unfold lpairs
      rw [List.mem_iff_getElem]
      refine ⟨i, by simp; omega, ?_⟩
      simp

end lists2

namespace Geo

variable {V ι β : Type*} (g : Geo V ι β)

lemma exists_runs {act : V → Prop} {G : β} {cs : List (List V)} (h : g.Circ act cs)
    (hG : ∃ σ ∈ cs, act (g.lt σ) ∧ g.vb (g.lt σ) = some G) :
    ∃ Rs : List (List (List V)), ∃ k, g.RunsOK act G Rs ∧ Rs.flatten = cs.rotate k := by
  obtain ⟨σ, hσ, hσG⟩ := hG
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hσ
  set cs' := cs.rotate (i + 1) with hcs'
  have hc' := Circ.rotate g h (i + 1)
  have hne' : cs' ≠ [] := hc'.ne
  have hlast : cs'.getLast hne' = cs[i] := by
    rw [List.getLast_eq_getElem]
    simp only [cs', List.getElem_rotate, List.length_rotate]
    congr 1
    have : cs.length - 1 + (i + 1) = i + cs.length := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
  obtain ⟨Rs, hRs, hR⟩ := exists_split (fun τ => act (g.lt τ) ∧ g.vb (g.lt τ) = some G) cs'
    hne' (by rw [hlast]; exact hσG)
  have hRne : ∀ R ∈ Rs, R ≠ [] := fun R hR' => (hR R hR').1
  have hperm := cpairs_flatten_perm [] Rs hRne
  rw [hRs] at hperm
  refine ⟨Rs, i + 1, ⟨?_, ?_, ?_⟩, hRs⟩
  · rintro rfl; exact hne' (by simpa using hRs.symm)
  · intro R hR'
    obtain ⟨hRn, hPR, hdR⟩ := hR R hR'
    have hmem : ∀ τ ∈ R, τ ∈ cs' := fun τ hτ => by
      rw [← hRs]; exact List.mem_flatten.2 ⟨R, hR', hτ⟩
    -- the junction preceding `R`
    obtain ⟨q, hq, hq2⟩ := exists_cpairs_snd hR'
    have hjq := hc'.join _ (hperm.mem_iff.2 (List.mem_append_right _
      (List.mem_map.2 ⟨q, hq, rfl⟩)))
    have hq1 := (hR _ (mem_of_mem_cpairs_fst hq))
    have hPq : act (g.lt (q.1.getLastD [])) ∧ g.vb (g.lt (q.1.getLastD [])) = some G := by
      obtain ⟨hn, hp, -⟩ := hq1
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hn]; exact hp
    have hrhd : g.rhd R = g.hd (q.2.headD []) := by rw [hq2]; rfl
    have hrlt : g.rlt R = g.lt (R.getLast hRn) := by
      unfold rlt; rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hRn]; rfl
    refine ⟨hRn, fun τ hτ => hc'.strand τ (hmem τ hτ), fun p hp => ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · refine hc'.join p (hperm.mem_iff.2 (List.mem_append_left _ ?_))
      exact List.mem_flatten.2 ⟨lpairs R, List.mem_map.2 ⟨R, hR', rfl⟩, hp⟩
    · exact hdR p.1 (fst_mem_dropLast_of_mem_lpairs hp)
    · rw [hrhd]
      rcases hjq with ⟨-, h2, -⟩ | ⟨h1, -, -⟩
      · exact h2
      · exact absurd hPq.1 h1
    · rw [hrhd]
      rcases hjq with ⟨-, -, G', h3, h4⟩ | ⟨h1, -, -⟩
      · rw [h4, ← h3, hPq.2]
      · exact absurd hPq.1 h1
    · rw [hrlt]; exact hPR.1
    · rw [hrlt]; exact hPR.2
  · rw [hRs]; exact hc'.nodup

end Geo

section lists3

variable {α : Type*}

lemma getLastD_reverse' (l : List α) (d : α) : l.reverse.getLastD d = l.headD d := by
  cases l <;> simp [List.getLastD_eq_getLast?]

lemma headD_reverse' (l : List α) (d : α) : l.reverse.headD d = l.getLastD d := by
  rw [← getLastD_reverse', List.reverse_reverse]

lemma sInner_reverse (l : List α) : sInner l.reverse = (sInner l).reverse := by
  unfold sInner
  rw [List.tail_reverse, List.dropLast_reverse, List.tail_dropLast]

lemma lpairs_reverse (l : List α) : lpairs l.reverse = ((lpairs l).map Prod.swap).reverse := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases t with
    | nil => rfl
    | cons b t =>
      rw [List.reverse_cons, lpairs_append_singleton _ _ (by simp), ih]
      simp [lpairs_cons_cons]

lemma lpairs_map {γ : Type*} (f : α → γ) (l : List α) :
    lpairs (l.map f) = (lpairs l).map (Prod.map f f) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases t with
    | nil => rfl
    | cons b t => simp only [List.map_cons, lpairs_cons_cons] at ih ⊢; rw [ih]; rfl

end lists3

namespace Geo

variable {V ι β : Type*} (g : Geo V ι β)

lemma hd_reverse (σ : List V) : g.hd σ.reverse = g.lt σ := headD_reverse' σ g.dflt

lemma lt_reverse (σ : List V) : g.lt σ.reverse = g.hd σ := getLastD_reverse' σ g.dflt

lemma StrandOK.reverse {act : V → Prop} {σ : List V} (h : g.StrandOK act σ) :
    g.StrandOK act σ.reverse := by
  refine ⟨by simpa using h.two_le, ?_, fun v hv => ?_, fun ha => ?_, fun ha => ?_⟩
  · rw [List.isChain_reverse]
    exact h.chain.imp fun a b hab => hab.symm
  · rw [sInner_reverse, List.mem_reverse] at hv; exact h.inner_na v hv
  · rw [g.hd_reverse] at ha ⊢; exact h.lt_bd ha
  · rw [g.lt_reverse] at ha ⊢; exact h.hd_bd ha

lemma rhd_revRun (R : List (List V)) : g.rhd (revRun R) = g.rlt R := by
  unfold rhd rlt revRun
  rw [headD_reverse']
  cases R using List.reverseRecOn with
  | nil => rfl
  | append_singleton R σ _ => simp [hd_reverse]

lemma rlt_revRun (R : List (List V)) : g.rlt (revRun R) = g.rhd R := by
  unfold rhd rlt revRun
  rw [getLastD_reverse']
  cases R with
  | nil => rfl
  | cons σ R => simp [lt_reverse]

lemma lpairs_revRun (R : List (List V)) :
    lpairs (revRun R) = ((lpairs R).map (fun p => (p.2.reverse, p.1.reverse))).reverse := by
  unfold revRun
  rw [lpairs_reverse, lpairs_map, List.map_map]
  rfl

lemma flatten_revRun_perm (R : List (List V)) : (revRun R).flatten.Perm R.flatten := by
  unfold revRun
  refine (List.reverse_perm _).flatten.trans ?_
  induction R with
  | nil => simp
  | cons σ t ih =>
    simp only [List.map_cons, List.flatten_cons]
    exact (List.reverse_perm σ).append ih

lemma mem_revRun {R : List (List V)} {τ : List V} (h : τ ∈ revRun R) : τ.reverse ∈ R := by
  unfold revRun at h
  rw [List.mem_reverse, List.mem_map] at h
  obtain ⟨σ, hσ, rfl⟩ := h
  rwa [List.reverse_reverse]

lemma joinVal_symm {act : V → Prop} {u v : V} (h : g.JoinOK act u v) :
    g.joinVal act u v = g.joinVal act v u := by
  unfold joinVal
  rcases h with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
  · rw [if_neg (fun h' => h'.1 h1), if_neg (fun h' => h'.1 h2)]
  · have : g.Mp u v ↔ g.Mp v u := ⟨g.Mp_symm, g.Mp_symm⟩
    simp only [h1, h2, not_false_eq_true, true_and, this]

lemma RunOK.rev {act : V → Prop} {G : β} {R : List (List V)} (h : g.RunOK act G R) :
    g.RunOK act G (revRun R) ∧ g.szR act (revRun R) = g.szR act R := by
  have hmem : ∀ p ∈ lpairs (revRun R), ∃ q ∈ lpairs R, p = (q.2.reverse, q.1.reverse) := by
    intro p hp
    rw [lpairs_revRun, List.mem_reverse, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact ⟨q, hq, rfl⟩
  refine ⟨⟨?_, fun σ hσ => ?_, fun p hp => ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · unfold revRun; simpa using h.ne
  · have := (h.strand _ (mem_revRun hσ)).reverse
    rwa [List.reverse_reverse] at this
  · obtain ⟨q, hq, rfl⟩ := hmem p hp
    obtain ⟨hj, hnG⟩ := h.join q hq
    simp only [lt_reverse, hd_reverse]
    refine ⟨hj.symm, fun ⟨ha, hG⟩ => hnG ?_⟩
    rcases hj with ⟨h1, -, G', h3, h4⟩ | ⟨-, h2, -⟩
    · exact ⟨h1, by rw [h3, ← h4, hG]⟩
    · exact absurd ha h2
  · rw [rhd_revRun]; exact h.lt_act
  · rw [rhd_revRun]; exact h.lt_G
  · rw [rlt_revRun]; exact h.hd_act
  · rw [rlt_revRun]; exact h.hd_G
  · unfold szR
    congr 1
    · unfold revRun
      rw [List.map_reverse, List.sum_reverse, List.map_map]
      congr 1
      refine List.map_congr_left fun σ _ => ?_
      exact countPairs_reverse _ (fun a b hab => g.Mp_symm hab) σ
    · rw [lpairs_revRun, List.map_reverse, List.sum_reverse, List.map_map]
      congr 1
      refine List.map_congr_left fun q hq => ?_
      simp only [Function.comp_apply, lt_reverse, hd_reverse]
      exact (g.joinVal_symm (h.join q hq).1).symm

lemma RunsOK.perm {act : V → Prop} {G : β} {Rs Rs' : List (List (List V))}
    (h : g.RunsOK act G Rs) (hp : Rs.Perm Rs') : g.RunsOK act G Rs' := by
  refine ⟨fun h' => h.ne (by subst h'; exact List.perm_nil.1 hp), fun R hR =>
    h.run R (hp.mem_iff.2 hR), (hp.flatten.flatten).nodup_iff.1 h.nodup⟩

end Geo

end Lovasz
