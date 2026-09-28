module
public import RequestProject.Pieces

/-!
# Assembling circuits from runs and pieces
-/

@[expose] public section


open Classical

namespace Lovasz

section lists

variable {α : Type*}

lemma range_map_getD (l : List α) (d : α) :
    (List.range l.length).map (fun i => l.getD i d) = l := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp [List.getElem?_eq_getElem h2]

lemma cpairs_eq_range (l : List α) (d : α) :
    cpairs l = (List.range l.length).map (fun i => (l.getD i d, l.getD ((i + 1) % l.length) d)) := by
  rcases eq_or_ne l [] with rfl | hl
  · rfl
  have hlen : 0 < l.length := List.length_pos_iff.2 hl
  refine List.ext_getElem (by simp [length_cpairs]) fun i h1 h2 => ?_
  simp only [List.length_map, List.length_range] at h2
  simp only [cpairs, lpairs, List.getElem_zip, List.getElem_tail, List.getElem_map,
    List.getElem_range]
  rw [List.getElem_append_left h2, List.getD_eq_getElem _ _ h2]
  congr 1
  by_cases hi : i + 1 < l.length
  · rw [List.getElem_append_left hi, Nat.mod_eq_of_lt hi, List.getD_eq_getElem _ _ hi]
  · have hi' : i + 1 = l.length := by omega
    have : (i + 1) % l.length = 0 := by rw [hi', Nat.mod_self]
    rw [this, List.getD_eq_getElem _ _ hlen, List.getElem_append_right (by omega)]
    obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hl
    simp [hi']

lemma getElem_mem_lpairs (l : List α) (j : ℕ) (hj : j + 1 < l.length) :
    (l[j]'(by omega), l[j + 1]) ∈ lpairs l := by
  have hlen : j < (lpairs l).length := by rw [length_lpairs]; omega
  have : (lpairs l)[j] = (l[j]'(by omega), l[j + 1]) := by
    simp [lpairs, List.getElem_zip, List.getElem_tail]
  rw [← this]; exact List.getElem_mem hlen

lemma flatten_map_append_perm {γ : Type*} (l : List γ) (f h : γ → List α) :
    (l.map (fun i => f i ++ h i)).flatten.Perm ((l.map f).flatten ++ (l.map h).flatten) := by
  induction l with
  | nil => simp
  | cons x t ih =>
    simp only [List.map_cons, List.flatten_cons, List.append_assoc]
    refine List.Perm.append_left _ ?_
    refine (List.Perm.append_left _ ih).trans ?_
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.Perm.append_right _ List.perm_append_comm

lemma flatten_map_singleton' {γ : Type*} (l : List γ) (f : γ → α) :
    (l.map (fun i => [f i])).flatten = l.map f := by
  induction l with
  | nil => rfl
  | cons x t ih => simp [ih]

lemma range_succ_mod_perm (k : ℕ) : ((List.range k).map (fun i => (i + 1) % k)).Perm (List.range k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hinj : Set.InjOn (fun i => (i + 1) % k) {i | i < k} := by
    intro i hi j hj hij
    simp only [Set.mem_setOf_eq] at hi hj hij
    by_cases h1 : i + 1 < k <;> by_cases h2 : j + 1 < k
    · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hij; omega
    · rw [Nat.mod_eq_of_lt h1, show j + 1 = k by omega, Nat.mod_self] at hij; omega
    · rw [Nat.mod_eq_of_lt h2, show i + 1 = k by omega, Nat.mod_self] at hij; omega
    · omega
  refine (List.perm_ext_iff_of_nodup ?_ List.nodup_range).2 fun x => ?_
  · refine List.Nodup.map_on (fun i hi j hj hij => hinj (List.mem_range.1 hi) (List.mem_range.1 hj) hij)
      List.nodup_range
  · simp only [List.mem_map, List.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact Nat.mod_lt _ hk
    · intro hx
      rcases Nat.eq_zero_or_pos x with rfl | hx0
      · exact ⟨k - 1, by omega, by rw [show k - 1 + 1 = k by omega, Nat.mod_self]⟩
      · exact ⟨x - 1, by omega, by rw [show x - 1 + 1 = x by omega, Nat.mod_eq_of_lt hx]⟩

/-- Rotating the first elements of the blocks of a cyclic concatenation. -/
lemma perm_cyc (k : ℕ) (a : ℕ → α) (m d : ℕ → List α) :
    ((List.range k).map (fun i => [a i] ++ m i ++ d i)).flatten.Perm
      (((List.range k).map m).flatten ++
        ((List.range k).map (fun i => d i ++ [a ((i + 1) % k)])).flatten) := by
  have h1 := flatten_map_append_perm (List.range k) (fun i => [a i] ++ m i) d
  have h2 := flatten_map_append_perm (List.range k) (fun i => [a i]) m
  have h3 := flatten_map_append_perm (List.range k) d (fun i => [a ((i + 1) % k)])
  have h4 : ((List.range k).map (fun i => [a ((i + 1) % k)])).flatten.Perm
      ((List.range k).map (fun i => [a i])).flatten := by
    have e1 : ((List.range k).map (fun i => [a ((i + 1) % k)])).flatten =
        ((List.range k).map (fun i => (i + 1) % k)).map a := by
      rw [flatten_map_singleton', List.map_map]; rfl
    have e2 : ((List.range k).map (fun i => [a i])).flatten = (List.range k).map a :=
      flatten_map_singleton' _ _
    rw [e1, e2]
    exact (range_succ_mod_perm k).map a
  refine h1.trans ((h2.append_right _).trans ?_)
  refine List.Perm.trans ?_ (h3.append_left _).symm
  rw [List.append_assoc]
  refine List.perm_append_comm.trans ?_
  rw [List.append_assoc]
  exact (List.Perm.append_left _ (List.Perm.append_left _ h4)).symm

end lists

namespace Geo

variable {V ι β : Type*} (g : Geo V ι β)

/-- A list of runs whose junctions (inside runs and between consecutive runs) are admissible
forms a circuit. -/
lemma circ_of_runs {act : V → Prop} {Rs : List (List (List V))} (hne : Rs ≠ [])
    (hR : ∀ R ∈ Rs, R ≠ [] ∧ (∀ σ ∈ R, g.StrandOK act σ) ∧
      ∀ p ∈ lpairs R, g.JoinOK act (g.lt p.1) (g.hd p.2))
    (hnd : Rs.flatten.flatten.Nodup)
    (hj : ∀ q ∈ cpairs Rs, g.JoinOK act (g.rlt q.1) (g.rhd q.2)) :
    g.Circ act Rs.flatten ∧ g.sz act Rs.flatten = (Rs.map (g.szR act)).sum +
      ((cpairs Rs).map (fun q => g.joinVal act (g.rlt q.1) (g.rhd q.2))).sum := by
  have hne' : ∀ R ∈ Rs, R ≠ [] := fun R hR' => (hR R hR').1
  have hperm := cpairs_flatten_perm [] Rs hne'
  refine ⟨⟨?_, ?_, hnd, ?_⟩, ?_⟩
  · intro h'
    obtain ⟨R, hR'⟩ := List.exists_mem_of_ne_nil _ hne
    exact hne' R hR' (List.flatten_eq_nil_iff.1 h' R hR')
  · intro σ hσ
    obtain ⟨R, hR', hσR⟩ := List.mem_flatten.1 hσ
    exact (hR R hR').2.1 σ hσR
  · intro p hp
    rcases List.mem_append.1 (hperm.mem_iff.1 hp) with hp | hp
    · obtain ⟨l, hl, hpl⟩ := List.mem_flatten.1 hp
      obtain ⟨R, hR', rfl⟩ := List.mem_map.1 hl
      exact (hR R hR').2.2 p hpl
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact hj q hq
  · unfold sz
    rw [(hperm.map _).sum_eq, List.map_append, List.sum_append, List.map_map]
    have e2 : ((cpairs Rs).map ((fun p : List V × List V => g.joinVal act (g.lt p.1) (g.hd p.2)) ∘
        (fun q => (q.1.getLastD [], q.2.headD [])))) =
        (cpairs Rs).map (fun q => g.joinVal act (g.rlt q.1) (g.rhd q.2)) := rfl
    rw [e2]
    have key : (Rs.flatten.map (countPairs g.Mp)).sum +
        (((Rs.map lpairs).flatten).map (fun p => g.joinVal act (g.lt p.1) (g.hd p.2))).sum =
        (Rs.map (g.szR act)).sum := by
      clear hperm e2 hj hnd hR hne hne'
      induction Rs with
      | nil => rfl
      | cons R t ih =>
        simp only [List.flatten_cons, List.map_append, List.sum_append, List.map_cons,
          List.sum_cons, szR] at ih ⊢
        rw [← ih]; ring
    rw [← key]; ring

/-- An active vertex of the block `G` on a run is one of its two ends. -/
lemma RunOK.act_G_end {act : V → Prop} {G : β} {R : List (List V)} (h : g.RunOK act G R)
    {v : V} (hv : v ∈ R.flatten) (ha : act v) (hG : g.vb v = some G) :
    v = g.rhd R ∨ v = g.rlt R := by
  obtain ⟨σ, hσ, hvσ⟩ := List.mem_flatten.1 hv
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hσ
  have hs := h.strand _ hσ
  rcases g.mem_ends_of_act hs hvσ ha with rfl | rfl
  · -- `v` is the first vertex of `R[j]`
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · left
      obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil h.ne
      rfl
    · exfalso
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      obtain ⟨hjn, hnG⟩ := h.join _ (getElem_mem_lpairs R j' hj)
      rcases hjn with ⟨h1, -, G', h3, h4⟩ | ⟨-, h2, -⟩
      · exact hnG ⟨h1, by rw [h3, ← h4, hG]⟩
      · exact h2 ha
  · -- `v` is the last vertex of `R[j]`
    by_cases hjl : j + 1 < R.length
    · exfalso
      exact (h.join _ (getElem_mem_lpairs R j hjl)).2 ⟨ha, hG⟩
    · right
      have hjl' : j = R.length - 1 := by omega
      subst hjl'
      unfold rlt
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getElem?_eq_getElem hj]
      rfl

lemma nodup_of_keys (KL : List ((ι × Bool) × List V))
    (hin : ∀ x ∈ KL, ∀ v ∈ x.2, g.ivOf v = some x.1.1) (hnd : ∀ x ∈ KL, x.2.Nodup)
    (hk : (KL.map Prod.fst).Nodup)
    (hdis : ∀ x ∈ KL, ∀ y ∈ KL, x.1.1 = y.1.1 → x.1.2 ≠ y.1.2 → x.2.Disjoint y.2) :
    (KL.map Prod.snd).flatten.Nodup := by
  rw [List.nodup_flatten]
  refine ⟨fun l hl => ?_, ?_⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hl; exact hnd x hx
  · rw [List.pairwise_map]
    have hp : KL.Pairwise (fun x y => x.1 ≠ y.1) := List.pairwise_map.1 hk
    refine List.Pairwise.imp_of_mem ?_ hp
    intro x y hx hy hxy
    by_cases h1 : x.1.1 = y.1.1
    · exact hdis x hx y hy h1 (fun h2 => hxy (Prod.ext h1 h2))
    · intro v hvx hvy
      have e1 := hin x hx v hvx
      rw [hin y hy v hvy, Option.some.injEq] at e1
      exact h1 e1.symm

lemma szR_snoc_swap {act act' : V → Prop} (hle : ∀ v, act' v → act v) (D : List (List V))
    {x y : List V} (hxy : g.hd x = g.hd y) :
    g.szR act (D ++ [y]) + countPairs g.Mp x ≤ g.szR act' (D ++ [x]) + countPairs g.Mp y := by
  unfold szR
  have e : ((lpairs (D ++ [y])).map (fun p => g.joinVal act (g.lt p.1) (g.hd p.2))).sum =
      ((lpairs (D ++ [x])).map (fun p => g.joinVal act (g.lt p.1) (g.hd p.2))).sum := by
    have := congrArg (fun l => (l.map (fun q : V × V => g.joinVal act q.1 q.2)).sum)
      (g.lpairs_snoc_map (D := D) hxy)
    simpa [List.map_map, Function.comp_def] using this.symm
  have hm : ((lpairs (D ++ [x])).map (fun p => g.joinVal act (g.lt p.1) (g.hd p.2))).sum ≤
      ((lpairs (D ++ [x])).map (fun p => g.joinVal act' (g.lt p.1) (g.hd p.2))).sum :=
    List.sum_le_sum fun p _ => g.joinVal_mono hle _ _
  rw [e]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  omega

/-- Extending the last strand of a run by the inner vertices of a path `π` starting at the
end of the run. -/
lemma RunOK.extend {act act' : V → Prop} {G : β} {R : List (List V)} (h : g.RunOK act G R)
    (hle : ∀ v, act' v → act v)
    (hdeact : ∀ u v, g.JoinOK act u v → ¬ (act u ∧ g.vb u = some G) → g.JoinOK act' u v)
    {π : List V} (hπh : π.head? = some (g.rlt R)) {p' : V} (hπl : π.getLast? = some p')
    (hπ2 : 2 ≤ π.length) (hπc : π.IsChain g.Γ.Adj) (hna : ∀ v ∈ π.dropLast, ¬ act' v) :
    let R' := R.dropLast ++ [R.getLastD [] ++ sInner π]
    R' ≠ [] ∧ (∀ σ ∈ R', g.StrandOK act' σ) ∧
      (∀ p ∈ lpairs R', g.JoinOK act' (g.lt p.1) (g.hd p.2)) ∧
      g.rhd R' = g.rhd R ∧ ¬ act' (g.rlt R') ∧ g.Γ.Adj (g.rlt R') p' ∧
      g.szR act R + countPairs g.Mp π ≤
        g.szR act' R' + (if g.Mp (g.rlt R') p' then 1 else 0) ∧
      R'.flatten = R.flatten ++ sInner π := by
  intro R'
  obtain ⟨D, σ, rfl⟩ := (List.eq_nil_or_concat' R).resolve_left h.ne
  have hσ : g.StrandOK act σ := h.strand σ (by simp)
  have hrlt : g.rlt (D ++ [σ]) = g.lt σ := by simp [rlt]
  rw [hrlt] at hπh
  obtain ⟨hτ, hτhd, hτna, hτadj, hτc⟩ := hσ.extendPath g hle hπh hπl hπ2 hπc hna
  have hR' : R' = D ++ [σ ++ sInner π] := by simp [R']
  rw [hR']
  have hrlt' : g.rlt (D ++ [σ ++ sInner π]) = g.lt (σ ++ sInner π) := by simp [rlt]
  refine ⟨by simp, ?_, ?_, g.rhd_snoc hτhd, by rw [hrlt']; exact hτna,
    by rw [hrlt']; exact hτadj, ?_, by simp⟩
  · intro τ hτ'
    rcases List.mem_append.1 hτ' with hτ' | hτ'
    · exact (h.strand τ (by simp [hτ'])).mono g hle
    · rw [List.mem_singleton.1 hτ']; exact hτ
  · intro q hq
    have hm : (g.lt q.1, g.hd q.2) ∈ (lpairs (D ++ [σ])).map (fun q => (g.lt q.1, g.hd q.2)) := by
      rw [← g.lpairs_snoc_map hτhd]; exact List.mem_map_of_mem hq
    obtain ⟨q', hq', e⟩ := List.mem_map.1 hm
    simp only [Prod.mk.injEq] at e
    rw [← e.1, ← e.2]
    obtain ⟨j1, j2⟩ := h.join q' hq'
    exact hdeact _ _ j1 j2
  · have h1 := g.szR_snoc_swap hle D hτhd
    rw [hrlt']
    omega

end Geo

end Lovasz
