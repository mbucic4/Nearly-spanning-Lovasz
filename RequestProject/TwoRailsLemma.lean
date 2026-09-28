module
public import RequestProject.Realize

/-!
# Two rails (Lemma 3.1)
-/

@[expose] public section


open Classical

namespace Lovasz

/-- The case of many connectors: the connectors and rail segments realize every path of the
cycle-and-matching graph of Theorem 1.2 (after cutting it at the two artificial edges). -/
lemma two_rails_large {V : Type} (G : SimpleGraph V) (P₀ P₁ : List V) (k : ℕ)
    (Q : Fin k → List V) (D : ℕ) (hk : 1 ≤ k) (hP₀ : IsPathL G P₀) (hP₁ : IsPathL G P₁)
    (hdisj : P₀.Disjoint P₁) (hQ : ∀ i, IsPathL G (Q i))
    (hQ0 : ∀ i, ∃ x ∈ P₀, (Q i).head? = some x) (hQ1 : ∀ i, ∃ y ∈ P₁, (Q i).getLast? = some y)
    (hQd : ∀ i j, i ≠ j → (Q i).Disjoint (Q j))
    (hQP0 : ∀ i, ∀ x ∈ Q i, x ∈ P₀ → (Q i).head? = some x)
    (hQP1 : ∀ i, ∀ x ∈ Q i, x ∈ P₁ → (Q i).getLast? = some x)
    (hQlen : ∀ i, D + 1 ≤ (Q i).length) :
    ∃ f : Fin k → Fin k, Function.Bijective f ∧ ∀ l : List (Fin (2 * k)),
      IsPathL (cycleMatchGraph k f) l → ∃ l₂, IsPathL G l₂ ∧ l₂ ≠ [] ∧
        D * countPairs (fun i j => matchAdj k f i j ∨ matchAdj k f j i) l ≤
          4 * (l₂.length - 1) := by
  have hk0 : 0 < k := hk
  choose x hxP hxQ using hQ0
  choose y hyP hyQ using hQ1
  have hxm : ∀ i, x i ∈ Q i := fun i => List.mem_of_head? (hxQ i)
  have hym : ∀ i, y i ∈ Q i := fun i => List.mem_of_getLast? (hyQ i)
  have hxinj : Function.Injective x := fun i j h => by
    by_contra hij; exact hQd i j hij (hxm i) (h ▸ hxm j)
  have hyinj : Function.Injective y := fun i j h => by
    by_contra hij; exact hQd i j hij (hym i) (h ▸ hym j)
  have hPP : ∀ z, z ∈ P₀ → z ∈ P₁ → False := fun z h0 h1 => hdisj h0 h1
  -- positions of the attachment points along the rails
  let pos0 : Fin k → ℕ := fun i => P₀.idxOf (x i)
  let pos1 : Fin k → ℕ := fun i => P₁.idxOf (y i)
  have hpos0lt : ∀ i, pos0 i < P₀.length := fun i => List.idxOf_lt_length_of_mem (hxP i)
  have hpos1lt : ∀ i, pos1 i < P₁.length := fun i => List.idxOf_lt_length_of_mem (hyP i)
  have hpos0get : ∀ i, P₀[pos0 i]'(hpos0lt i) = x i := fun i => List.getElem_idxOf _
  have hpos1get : ∀ i, P₁[pos1 i]'(hpos1lt i) = y i := fun i => List.getElem_idxOf _
  have hpos0inj : Function.Injective pos0 := fun i j h =>
    hxinj ((List.idxOf_inj (hxP i)).1 h)
  have hpos1inj : Function.Injective pos1 := fun i j h =>
    hyinj ((List.idxOf_inj (hyP i)).1 h)
  let e0 := Tuple.sort pos0
  let e1 := Tuple.sort pos1
  have hsm0 : StrictMono (pos0 ∘ e0) :=
    (Tuple.monotone_sort pos0).strictMono_of_injective (hpos0inj.comp e0.injective)
  have hsm1 : StrictMono (pos1 ∘ e1) :=
    (Tuple.monotone_sort pos1).strictMono_of_injective (hpos1inj.comp e1.injective)
  let f : Fin k → Fin k := fun a => e1.symm (e0 a)
  refine ⟨f, (e0.trans e1.symm).bijective, ?_⟩
  intro l hl
  -- the model vertices
  let idx : ℕ → Fin k := fun a => ⟨a % k, Nat.mod_lt _ hk0⟩
  have hidx : ∀ a, a < k → (idx a).val = a := fun a ha => Nat.mod_eq_of_lt ha
  let L0 : ℕ → V := fun a => x (e0 (idx a))
  let L1 : ℕ → V := fun b => y (e1 (idx b))
  let q0 : ℕ → ℕ := fun a => pos0 (e0 (idx a))
  let q1 : ℕ → ℕ := fun b => pos1 (e1 (idx b))
  have hq0lt : ∀ a, q0 a < P₀.length := fun a => hpos0lt _
  have hq1lt : ∀ b, q1 b < P₁.length := fun b => hpos1lt _
  have hq0get : ∀ a, P₀[q0 a]'(hq0lt a) = L0 a := fun a => hpos0get _
  have hq1get : ∀ b, P₁[q1 b]'(hq1lt b) = L1 b := fun b => hpos1get _
  have hq0mono : ∀ a a', a < a' → a' < k → q0 a < q0 a' := by
    intro a a' h h'
    refine hsm0 (show idx a < idx a' from ?_)
    rw [Fin.lt_def, hidx a (by omega), hidx a' h']; exact h
  have hq1mono : ∀ b b', b < b' → b' < k → q1 b < q1 b' := by
    intro b b' h h'
    refine hsm1 (show idx b < idx b' from ?_)
    rw [Fin.lt_def, hidx b (by omega), hidx b' h']; exact h
  have hL0P : ∀ a, L0 a ∈ P₀ := fun a => hxP _
  have hL1P : ∀ b, L1 b ∈ P₁ := fun b => hyP _
  let ρ : Fin (2 * k) → V := fun u => if u.val < k then L0 u.val else L1 (u.val - k)
  have hρ0 : ∀ u : Fin (2 * k), u.val < k → ρ u = L0 u.val := fun u h => if_pos h
  have hρ1 : ∀ u : Fin (2 * k), ¬ u.val < k → ρ u = L1 (u.val - k) := fun u h => if_neg h
  have hL0inj : ∀ a a', a < k → a' < k → L0 a = L0 a' → a = a' := by
    intro a a' ha ha' h
    have := e0.injective (hxinj h)
    have := congrArg Fin.val this
    rwa [hidx a ha, hidx a' ha'] at this
  have hL1inj : ∀ b b', b < k → b' < k → L1 b = L1 b' → b = b' := by
    intro b b' hb hb' h
    have := e1.injective (hyinj h)
    have := congrArg Fin.val this
    rwa [hidx b hb, hidx b' hb'] at this
  have hρinj : Function.Injective ρ := by
    intro u v h
    apply Fin.ext
    by_cases hu : u.val < k <;> by_cases hv : v.val < k
    · rw [hρ0 u hu, hρ0 v hv] at h; exact hL0inj _ _ hu hv h
    · rw [hρ0 u hu, hρ1 v hv] at h; exact absurd (h ▸ hL0P _) (fun h' => hPP _ h' (hL1P _))
    · rw [hρ1 u hu, hρ0 v hv] at h; exact absurd (h ▸ hL1P _) (fun h' => hPP _ (hL0P _) h')
    · rw [hρ1 u hu, hρ1 v hv] at h
      have := hL1inj _ _ (by omega) (by omega) h
      omega
  -- the rail segments between consecutive attachment points
  let S0 : ℕ → List V := fun a => (P₀.drop (q0 a)).take (q0 (a + 1) - q0 a + 1)
  let S1 : ℕ → List V := fun b => (P₁.drop (q1 b)).take (q1 (b + 1) - q1 b + 1)
  have hS0 : ∀ a, a + 1 < k → IsPathL G (S0 a) ∧ (S0 a).head? = some (L0 a) ∧
      (S0 a).getLast? = some (L0 (a + 1)) ∧
      ∀ z ∈ S0 a, ∃ t, ∃ ht : t < P₀.length, q0 a ≤ t ∧ t ≤ q0 (a + 1) ∧ P₀[t] = z := by
    intro a ha
    have hlt := hq0mono a (a + 1) (by omega) ha
    obtain ⟨-, h2, h3, h4⟩ := subpath_facts P₀ (q0 a) (q0 (a + 1)) hlt.le (hq0lt _)
    refine ⟨hP₀.infix (slice_infix _ _ _), ?_, ?_, h4⟩
    · rw [h2, hq0get]
    · rw [h3, hq0get]
  have hS1 : ∀ b, b + 1 < k → IsPathL G (S1 b) ∧ (S1 b).head? = some (L1 b) ∧
      (S1 b).getLast? = some (L1 (b + 1)) ∧
      ∀ z ∈ S1 b, ∃ t, ∃ ht : t < P₁.length, q1 b ≤ t ∧ t ≤ q1 (b + 1) ∧ P₁[t] = z := by
    intro b hb
    have hlt := hq1mono b (b + 1) (by omega) hb
    obtain ⟨-, h2, h3, h4⟩ := subpath_facts P₁ (q1 b) (q1 (b + 1)) hlt.le (hq1lt _)
    refine ⟨hP₁.infix (slice_infix _ _ _), ?_, ?_, h4⟩
    · rw [h2, hq1get]
    · rw [h3, hq1get]
  have hS0P : ∀ a, ∀ z ∈ S0 a, z ∈ P₀ := fun a z hz => (slice_infix _ _ _).subset hz
  have hS1P : ∀ b, ∀ z ∈ S1 b, z ∈ P₁ := fun b z hz => (slice_infix _ _ _).subset hz
  have hS0rho : ∀ a, a + 1 < k → ∀ z ∈ S0 a, ∀ w : Fin (2 * k), z = ρ w →
      w.val = a ∨ w.val = a + 1 := by
    intro a ha z hz w hzw
    obtain ⟨t, ht, h1, h2, hzt⟩ := (hS0 a ha).2.2.2 z hz
    by_cases hw : w.val < k
    · rw [hρ0 w hw] at hzw
      have heq : P₀[t] = P₀[q0 w.val]'(hq0lt _) := by rw [hzt, hq0get, hzw]
      have htq := (List.Nodup.getElem_inj_iff hP₀.2).1 heq
      by_contra hcon
      rcases Nat.lt_or_gt_of_ne (show w.val ≠ a by omega) with hlt | hgt
      · have := hq0mono w.val a hlt (by omega); omega
      · have := hq0mono (a + 1) w.val (by omega) hw; omega
    · rw [hρ1 w hw] at hzw
      exact absurd (hzw ▸ hS0P a z hz) (fun h => hPP _ h (hL1P _))
  have hS1rho : ∀ b, b + 1 < k → ∀ z ∈ S1 b, ∀ w : Fin (2 * k), z = ρ w →
      w.val = k + b ∨ w.val = k + b + 1 := by
    intro b hb z hz w hzw
    obtain ⟨t, ht, h1, h2, hzt⟩ := (hS1 b hb).2.2.2 z hz
    by_cases hw : w.val < k
    · rw [hρ0 w hw] at hzw
      exact absurd (hzw ▸ hS1P b z hz) (fun h => hPP _ (hL0P _) h)
    · rw [hρ1 w hw] at hzw
      have heq : P₁[t] = P₁[q1 (w.val - k)]'(hq1lt _) := by rw [hzt, hq1get, hzw]
      have htq := (List.Nodup.getElem_inj_iff hP₁.2).1 heq
      have hwk : w.val - k < k := by omega
      by_contra hcon
      rcases Nat.lt_or_gt_of_ne (show w.val - k ≠ b by omega) with hlt | hgt
      · have := hq1mono (w.val - k) b hlt (by omega); omega
      · have := hq1mono (b + 1) (w.val - k) (by omega) hwk; omega
  have hS0S0 : ∀ a a', a + 1 < k → a' + 1 < k → a < a' → ∀ z ∈ S0 a, z ∈ S0 a' →
      ∃ w, z = ρ w := by
    intro a a' ha ha' haa z hz hz'
    obtain ⟨t, ht, h1, h2, hzt⟩ := (hS0 a ha).2.2.2 z hz
    obtain ⟨t', ht', h1', h2', hzt'⟩ := (hS0 a' ha').2.2.2 z hz'
    have htt : t = t' := (List.Nodup.getElem_inj_iff hP₀.2).1 (hzt.trans hzt'.symm)
    have hle : q0 (a + 1) ≤ q0 a' := by
      rcases Nat.lt_or_ge (a + 1) a' with h | h
      · exact (hq0mono _ _ h (by omega)).le
      · have : a + 1 = a' := by omega
        rw [this]
    have hta : t = q0 a' := by omega
    refine ⟨⟨a', by omega⟩, ?_⟩
    rw [hρ0 _ (show a' < k by omega), ← hzt]
    simp only [hta, hq0get]
  have hS1S1 : ∀ b b', b + 1 < k → b' + 1 < k → b < b' → ∀ z ∈ S1 b, z ∈ S1 b' →
      ∃ w, z = ρ w := by
    intro b b' hb hb' hbb z hz hz'
    obtain ⟨t, ht, h1, h2, hzt⟩ := (hS1 b hb).2.2.2 z hz
    obtain ⟨t', ht', h1', h2', hzt'⟩ := (hS1 b' hb').2.2.2 z hz'
    have htt : t = t' := (List.Nodup.getElem_inj_iff hP₁.2).1 (hzt.trans hzt'.symm)
    have hle : q1 (b + 1) ≤ q1 b' := by
      rcases Nat.lt_or_ge (b + 1) b' with h | h
      · exact (hq1mono _ _ h (by omega)).le
      · have : b + 1 = b' := by omega
        rw [this]
    have htb : t = q1 b' := by omega
    refine ⟨⟨k + b', by omega⟩, ?_⟩
    rw [hρ1 _ (show ¬ (k + b' < k) by omega), ← hzt]
    simp only [Nat.add_sub_cancel_left, htb, hq1get]
  -- the model edges and their realizations
  let Mt : Fin (2 * k) → Fin (2 * k) → Prop := fun i j => matchAdj k f i j ∨ matchAdj k f j i
  have hidxfin : ∀ j : Fin k, idx j.val = j := fun j => Fin.ext (hidx _ j.2)
  let lft : Fin k → Fin (2 * k) := fun i => ⟨(e0.symm i).val, by omega⟩
  let rgt : Fin k → Fin (2 * k) := fun i => ⟨k + (e1.symm i).val, by omega⟩
  have hlftρ : ∀ i, ρ (lft i) = x i := by
    intro i
    rw [hρ0 _ (e0.symm i).2]
    show x (e0 (idx (e0.symm i).val)) = x i
    rw [hidxfin, Equiv.apply_symm_apply]
  have hrgtρ : ∀ i, ρ (rgt i) = y i := by
    intro i
    rw [hρ1 _ (show ¬ (k + (e1.symm i).val < k) by omega)]
    show y (e1 (idx (k + (e1.symm i).val - k))) = y i
    rw [Nat.add_sub_cancel_left, hidxfin, Equiv.apply_symm_apply]
  have hmatch : ∀ u v : Fin (2 * k), matchAdj k f u v →
      u.val < k ∧ u = lft (e0 (idx u.val)) ∧ v = rgt (e0 (idx u.val)) := by
    rintro u v ⟨hu, hv⟩
    refine ⟨hu, Fin.ext ?_, Fin.ext ?_⟩
    · show u.val = (e0.symm (e0 (idx u.val))).val
      rw [Equiv.symm_apply_apply, hidx _ hu]
    · show v.val = k + (e1.symm (e0 (idx u.val))).val
      rw [hv]
      congr 3
      exact Fin.ext (hidx _ hu).symm
  let R : Fin (2 * k) → Fin (2 * k) → List V := fun u v =>
    if Mt u v then (if u.val < k then Q (e0 (idx u.val)) else (Q (e0 (idx v.val))).reverse)
    else if u.val + 1 = v.val then (if v.val < k then S0 u.val else S1 (u.val - k))
    else (if u.val < k then (S0 v.val).reverse else (S1 (v.val - k)).reverse)
  let Adm : Fin (2 * k) → Fin (2 * k) → Prop := fun u v =>
    Mt u v ∨ (u.val + 1 = v.val ∧ v.val ≠ k) ∨ (v.val + 1 = u.val ∧ u.val ≠ k)
  -- a matching edge is realized by its connector
  have hRmatch : ∀ u v, Mt u v → ∃ i, (R u v = Q i ∧ u = lft i ∧ v = rgt i) ∨
      (R u v = (Q i).reverse ∧ u = rgt i ∧ v = lft i) := by
    intro u v hM
    by_cases hu : u.val < k
    · have hm : matchAdj k f u v := by
        rcases hM with h | h
        · exact h
        · have := (hmatch v u h); have := congrArg Fin.val this.2.2
          simp only [rgt] at this; omega
      obtain ⟨-, h1, h2⟩ := hmatch u v hm
      refine ⟨e0 (idx u.val), Or.inl ⟨?_, h1, h2⟩⟩
      simp only [R, if_pos hM, if_pos hu]
    · have hm : matchAdj k f v u := by
        rcases hM with h | h
        · exact absurd (hmatch u v h).1 hu
        · exact h
      obtain ⟨-, h1, h2⟩ := hmatch v u hm
      refine ⟨e0 (idx v.val), Or.inr ⟨?_, h2, h1⟩⟩
      simp only [R, if_pos hM, if_neg hu]
  have hRseg : ∀ u v, Adm u v → ¬ Mt u v →
      (∃ a, a + 1 < k ∧ ((R u v = S0 a ∧ u.val = a ∧ v.val = a + 1) ∨
        (R u v = (S0 a).reverse ∧ u.val = a + 1 ∧ v.val = a))) ∨
      (∃ b, b + 1 < k ∧ ((R u v = S1 b ∧ u.val = k + b ∧ v.val = k + b + 1) ∨
        (R u v = (S1 b).reverse ∧ u.val = k + b + 1 ∧ v.val = k + b))) := by
    intro u v hA hM
    have hu2 := u.2
    have hv2 := v.2
    rcases hA with hA | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd hA hM
    · by_cases hv : v.val < k
      · refine Or.inl ⟨u.val, by omega, Or.inl ⟨?_, rfl, h1.symm⟩⟩
        simp only [R, if_neg hM, if_pos h1, if_pos hv]
      · refine Or.inr ⟨u.val - k, by omega, Or.inl ⟨?_, by omega, by omega⟩⟩
        simp only [R, if_neg hM, if_pos h1, if_neg hv]
    · have h1' : ¬ (u.val + 1 = v.val) := by omega
      by_cases hu : u.val < k
      · refine Or.inl ⟨v.val, by omega, Or.inr ⟨?_, h1.symm, rfl⟩⟩
        simp only [R, if_neg hM, if_neg h1', if_pos hu]
      · refine Or.inr ⟨v.val - k, by omega, Or.inr ⟨?_, by omega, by omega⟩⟩
        simp only [R, if_neg hM, if_neg h1', if_neg hu]
  have hρ0' : ∀ u : Fin (2 * k), ∀ a, u.val = a → a < k → ρ u = L0 a := by
    intro u a h ha; rw [hρ0 u (h ▸ ha), h]
  have hρ1' : ∀ u : Fin (2 * k), ∀ b, u.val = k + b → ρ u = L1 b := by
    intro u b h; rw [hρ1 u (by omega), h, Nat.add_sub_cancel_left]
  -- (a) realizations are paths between the right endpoints
  have hR : ∀ u v, Adm u v →
      IsPathL G (R u v) ∧ (R u v).head? = some (ρ u) ∧ (R u v).getLast? = some (ρ v) := by
    intro u v hA
    by_cases hM : Mt u v
    · obtain ⟨i, ⟨hRi, rfl, rfl⟩ | ⟨hRi, rfl, rfl⟩⟩ := hRmatch u v hM
      · rw [hRi, hlftρ, hrgtρ]; exact ⟨hQ i, hxQ i, hyQ i⟩
      · rw [hRi, hlftρ, hrgtρ, List.head?_reverse, List.getLast?_reverse]
        exact ⟨(hQ i).reverse, hyQ i, hxQ i⟩
    · rcases hRseg u v hA hM with ⟨a, ha, ⟨hRa, hu, hv⟩ | ⟨hRa, hu, hv⟩⟩ |
        ⟨b, hb, ⟨hRb, hu, hv⟩ | ⟨hRb, hu, hv⟩⟩
      · obtain ⟨h1, h2, h3, -⟩ := hS0 a ha
        rw [hRa, hρ0' u a hu (by omega), hρ0' v (a + 1) hv ha]; exact ⟨h1, h2, h3⟩
      · obtain ⟨h1, h2, h3, -⟩ := hS0 a ha
        rw [hRa, hρ0' u (a + 1) hu ha, hρ0' v a hv (by omega), List.head?_reverse,
          List.getLast?_reverse]
        exact ⟨h1.reverse, h3, h2⟩
      · obtain ⟨h1, h2, h3, -⟩ := hS1 b hb
        rw [hRb, hρ1' u b hu, hρ1' v (b + 1) (by omega)]; exact ⟨h1, h2, h3⟩
      · obtain ⟨h1, h2, h3, -⟩ := hS1 b hb
        rw [hRb, hρ1' u (b + 1) (by omega), hρ1' v b hv, List.head?_reverse,
          List.getLast?_reverse]
        exact ⟨h1.reverse, h3, h2⟩
  -- connectors meet the realization vertices only at their ends
  have hρP : ∀ w, ρ w ∈ P₀ ∨ ρ w ∈ P₁ := by
    intro w
    by_cases hw : w.val < k
    · rw [hρ0 w hw]; exact Or.inl (hL0P _)
    · rw [hρ1 w hw]; exact Or.inr (hL1P _)
  have hQρ : ∀ i, ∀ z ∈ Q i, ∀ w, z = ρ w → w = lft i ∨ w = rgt i := by
    intro i z hz w hzw
    rcases hρP w with h | h
    · rw [← hzw] at h
      have := hQP0 i z hz h
      rw [hxQ i] at this
      left; apply hρinj; rw [← hzw, hlftρ]; exact (Option.some.inj this).symm
    · rw [← hzw] at h
      have := hQP1 i z hz h
      rw [hyQ i] at this
      right; apply hρinj; rw [← hzw, hrgtρ]; exact (Option.some.inj this).symm
  -- membership classification
  have hclass : ∀ u v, Adm u v →
      (∃ i, (∀ z, z ∈ R u v ↔ z ∈ Q i) ∧ ((u = lft i ∧ v = rgt i) ∨ (u = rgt i ∧ v = lft i))) ∨
      (∃ a, a + 1 < k ∧ (∀ z, z ∈ R u v ↔ z ∈ S0 a) ∧
        ((u.val = a ∧ v.val = a + 1) ∨ (u.val = a + 1 ∧ v.val = a))) ∨
      (∃ b, b + 1 < k ∧ (∀ z, z ∈ R u v ↔ z ∈ S1 b) ∧
        ((u.val = k + b ∧ v.val = k + b + 1) ∨ (u.val = k + b + 1 ∧ v.val = k + b))) := by
    intro u v hA
    by_cases hM : Mt u v
    · obtain ⟨i, ⟨hRi, h1, h2⟩ | ⟨hRi, h1, h2⟩⟩ := hRmatch u v hM
      · exact Or.inl ⟨i, fun z => by rw [hRi], Or.inl ⟨h1, h2⟩⟩
      · exact Or.inl ⟨i, fun z => by rw [hRi, List.mem_reverse], Or.inr ⟨h1, h2⟩⟩
    · rcases hRseg u v hA hM with ⟨a, ha, ⟨hRa, hu, hv⟩ | ⟨hRa, hu, hv⟩⟩ |
        ⟨b, hb, ⟨hRb, hu, hv⟩ | ⟨hRb, hu, hv⟩⟩
      · exact Or.inr (Or.inl ⟨a, ha, fun z => by rw [hRa], Or.inl ⟨hu, hv⟩⟩)
      · exact Or.inr (Or.inl ⟨a, ha, fun z => by rw [hRa, List.mem_reverse], Or.inr ⟨hu, hv⟩⟩)
      · exact Or.inr (Or.inr ⟨b, hb, fun z => by rw [hRb], Or.inl ⟨hu, hv⟩⟩)
      · exact Or.inr (Or.inr ⟨b, hb, fun z => by rw [hRb, List.mem_reverse], Or.inr ⟨hu, hv⟩⟩)
  -- (b)
  have hb : ∀ u v, Adm u v → ∀ z ∈ R u v, ∀ w, z = ρ w → w = u ∨ w = v := by
    intro u v hA z hz w hzw
    rcases hclass u v hA with ⟨i, hmem, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ |
      ⟨a, ha, hmem, ⟨hu, hv⟩ | ⟨hu, hv⟩⟩ | ⟨b, hb', hmem, ⟨hu, hv⟩ | ⟨hu, hv⟩⟩
    · exact hQρ i z ((hmem z).1 hz) w hzw
    · exact (hQρ i z ((hmem z).1 hz) w hzw).symm
    · rcases hS0rho a ha z ((hmem z).1 hz) w hzw with h | h
      · exact Or.inl (Fin.ext (by omega))
      · exact Or.inr (Fin.ext (by omega))
    · rcases hS0rho a ha z ((hmem z).1 hz) w hzw with h | h
      · exact Or.inr (Fin.ext (by omega))
      · exact Or.inl (Fin.ext (by omega))
    · rcases hS1rho b hb' z ((hmem z).1 hz) w hzw with h | h
      · exact Or.inl (Fin.ext (by omega))
      · exact Or.inr (Fin.ext (by omega))
    · rcases hS1rho b hb' z ((hmem z).1 hz) w hzw with h | h
      · exact Or.inr (Fin.ext (by omega))
      · exact Or.inl (Fin.ext (by omega))
  -- (c)
  have hQS0 : ∀ i a, ∀ z ∈ Q i, z ∈ S0 a → ∃ w, z = ρ w := by
    intro i a z hz hz'
    have := hQP0 i z hz (hS0P a z hz')
    rw [hxQ i] at this
    exact ⟨lft i, by rw [hlftρ]; exact (Option.some.inj this).symm⟩
  have hQS1 : ∀ i b, ∀ z ∈ Q i, z ∈ S1 b → ∃ w, z = ρ w := by
    intro i b z hz hz'
    have := hQP1 i z hz (hS1P b z hz')
    rw [hyQ i] at this
    exact ⟨rgt i, by rw [hrgtρ]; exact (Option.some.inj this).symm⟩
  have hS01 : ∀ a b, ∀ z ∈ S0 a, z ∈ S1 b → False := fun a b z h0 h1 =>
    hPP z (hS0P a z h0) (hS1P b z h1)
  have hc : ∀ u v u' v', Adm u v → Adm u' v' → ¬ ((u = u' ∧ v = v') ∨ (u = v' ∧ v = u')) →
      ∀ z ∈ R u v, z ∈ R u' v' → ∃ w, z = ρ w := by
    intro u v u' v' hA hA' hne z hz hz'
    rcases hclass u v hA with ⟨i, hmem, ho⟩ | ⟨a, ha, hmem, ho⟩ | ⟨b, hb', hmem, ho⟩ <;>
      rcases hclass u' v' hA' with ⟨i', hmem', ho'⟩ | ⟨a', ha', hmem', ho'⟩ |
        ⟨b'', hb'', hmem', ho'⟩
    · by_cases hii : i = i'
      · subst hii
        exfalso; apply hne
        rcases ho with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases ho' with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · exact Or.inl ⟨h1.trans h3.symm, h2.trans h4.symm⟩
        · exact Or.inr ⟨h1.trans h4.symm, h2.trans h3.symm⟩
        · exact Or.inr ⟨h1.trans h4.symm, h2.trans h3.symm⟩
        · exact Or.inl ⟨h1.trans h3.symm, h2.trans h4.symm⟩
      · exact absurd ((hmem' z).1 hz') (fun h => hQd i i' hii ((hmem z).1 hz) h)
    · exact hQS0 i a' z ((hmem z).1 hz) ((hmem' z).1 hz')
    · exact hQS1 i b'' z ((hmem z).1 hz) ((hmem' z).1 hz')
    · exact hQS0 i' a z ((hmem' z).1 hz') ((hmem z).1 hz)
    · rcases lt_trichotomy a a' with h | rfl | h
      · exact hS0S0 a a' ha ha' h z ((hmem z).1 hz) ((hmem' z).1 hz')
      · exfalso; apply hne
        rcases ho with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases ho' with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · exact Or.inl ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
        · exact Or.inr ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
        · exact Or.inr ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
        · exact Or.inl ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
      · exact hS0S0 a' a ha' ha h z ((hmem' z).1 hz') ((hmem z).1 hz)
    · exact (hS01 a b'' z ((hmem z).1 hz) ((hmem' z).1 hz')).elim
    · exact hQS1 i' b z ((hmem' z).1 hz') ((hmem z).1 hz)
    · exact (hS01 a' b z ((hmem' z).1 hz') ((hmem z).1 hz)).elim
    · rcases lt_trichotomy b b'' with h | rfl | h
      · exact hS1S1 b b'' hb' hb'' h z ((hmem z).1 hz) ((hmem' z).1 hz')
      · exfalso; apply hne
        rcases ho with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases ho' with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · exact Or.inl ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
        · exact Or.inr ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
        · exact Or.inr ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
        · exact Or.inl ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
      · exact hS1S1 b'' b hb'' hb' h z ((hmem' z).1 hz') ((hmem z).1 hz)
  have hlen : ∀ u v, Adm u v → Mt u v → D + 1 ≤ (R u v).length := by
    intro u v _ hM
    obtain ⟨i, ⟨hRi, -, -⟩ | ⟨hRi, -, -⟩⟩ := hRmatch u v hM
    · rw [hRi]; exact hQlen i
    · rw [hRi, List.length_reverse]; exact hQlen i
  -- cutting the model path at the two artificial edges
  let Bad1 : Fin (2 * k) → Fin (2 * k) → Prop := fun u v =>
    ¬ Mt u v ∧ ((u.val + 1 = k ∧ v.val = k) ∨ (u.val = k ∧ v.val + 1 = k))
  let Bad2 : Fin (2 * k) → Fin (2 * k) → Prop := fun u v =>
    ¬ Mt u v ∧ ((u.val + 1 = 2 * k ∧ v.val = 0) ∨ (u.val = 0 ∧ v.val + 1 = 2 * k))
  obtain ⟨l', hinf', hno1, hcnt1⟩ := exists_good_piece Mt Bad1 (fun u v h => h.1)
    (by
      rintro u v u' v' ⟨-, h⟩ ⟨-, h'⟩
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases h' with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact Or.inl ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
      · exact Or.inr ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
      · exact Or.inr ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
      · exact Or.inl ⟨Fin.ext (by omega), Fin.ext (by omega)⟩) l hl.2
  obtain ⟨l'', hinf'', hno2, hcnt2⟩ := exists_good_piece Mt Bad2 (fun u v h => h.1)
    (by
      rintro u v u' v' ⟨-, h⟩ ⟨-, h'⟩
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases h' with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact Or.inl ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
      · exact Or.inr ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
      · exact Or.inr ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
      · exact Or.inl ⟨Fin.ext (by omega), Fin.ext (by omega)⟩) l'
      (hl.2.sublist hinf'.sublist)
  have hinf : l'' <:+: l := hinf''.trans hinf'
  have hcyc : ∀ u v : Fin (2 * k), cycAdj k u v → u.val + 1 = v.val ∨
      (u.val + 1 = 2 * k ∧ v.val = 0) := by
    intro u v h
    have hu := u.2
    unfold cycAdj at h
    rcases Nat.lt_or_ge (u.val + 1) (2 * k) with h' | h'
    · rw [Nat.mod_eq_of_lt h'] at h; exact Or.inl h.symm
    · have he : u.val + 1 = 2 * k := by omega
      rw [he, Nat.mod_self] at h; exact Or.inr ⟨he, h⟩
  have hchain : l''.IsChain Adm := by
    rw [List.isChain_iff_forall_rel_of_append_cons_cons]
    intro a b l1 l2 heq
    have hab : [a, b] <:+: l'' := ⟨l1, l2, by rw [heq]; simp⟩
    have hadj : (cycleMatchGraph k f).Adj a b :=
      (List.isChain_cons_cons.1 (hl.1.infix (hab.trans hinf))).1
    have n1 := hno1 a b (hab.trans hinf'')
    have n2 := hno2 a b hab
    by_cases hM : Mt a b
    · exact Or.inl hM
    right
    rw [cycleMatchGraph, SimpleGraph.fromRel_adj] at hadj
    obtain ⟨-, h | h⟩ := hadj
    · rcases h with h | h
      · rcases hcyc a b h with h' | ⟨h1, h2⟩
        · by_cases hbk : b.val = k
          · exact absurd ⟨hM, Or.inl ⟨by omega, hbk⟩⟩ n1
          · exact Or.inl ⟨h', hbk⟩
        · exact absurd ⟨hM, Or.inl ⟨h1, h2⟩⟩ n2
      · exact absurd (Or.inl h) hM
    · rcases h with h | h
      · rcases hcyc b a h with h' | ⟨h1, h2⟩
        · by_cases hak : a.val = k
          · exact absurd ⟨hM, Or.inr ⟨hak, by omega⟩⟩ n1
          · exact Or.inr ⟨h', hak⟩
        · exact absurd ⟨hM, Or.inr ⟨h2, h1⟩⟩ n2
      · exact absurd (Or.inr h) hM
  cases hl'' : l'' with
  | nil =>
    rw [hl''] at hcnt2
    refine ⟨Q ⟨0, hk0⟩, hQ _, ?_, ?_⟩
    · intro h; have := hQlen ⟨0, hk0⟩; rw [h] at this; simp at this
    · have : countPairs Mt ([] : List (Fin (2 * k))) = 0 := rfl
      have h0 : countPairs Mt l = 0 := by omega
      show D * countPairs Mt l ≤ _
      rw [h0]; simp
  | cons u rest =>
    rw [hl''] at hchain hcnt2 hinf
    obtain ⟨hP, -, hL, -⟩ := realize_spec G ρ R Adm Mt D hR hb hc hlen rest u
      (hl.2.sublist hinf.sublist) hchain
    refine ⟨realize ρ R (u :: rest), hP, ?_, ?_⟩
    · intro h; rw [h] at hL; simp at hL
    · show D * countPairs Mt l ≤ _
      calc D * countPairs Mt l ≤ D * (4 * countPairs Mt (u :: rest)) :=
            Nat.mul_le_mul_left _ (by omega)
        _ = 4 * (D * countPairs Mt (u :: rest)) := by ring
        _ ≤ 4 * ((realize ρ R (u :: rest)).length - 1) :=
            Nat.mul_le_mul_left _ (by omega)


/-- **Lemma 3.1** (two rails). Let `P₀, P₁` be disjoint paths and `Q₀, …, Q_{k-1}` pairwise
vertex-disjoint paths, each starting on `P₀` and ending on `P₁`, meeting `P₀ ∪ P₁` only in
their endpoints, and each having at least `D` edges.  Then the union contains a path with at
least `a D k^(1-η)` edges. -/
theorem two_rails (h12 : CycleMatchingTheorem) (η : ℝ) (hη0 : 0 < η) :
    ∃ a : ℝ, 0 < a ∧ ∀ {V : Type} (G : SimpleGraph V) (P₀ P₁ : List V) (k : ℕ)
      (Q : Fin k → List V) (D : ℕ), 1 ≤ k → IsPathL G P₀ → IsPathL G P₁ → P₀.Disjoint P₁ →
      (∀ i, IsPathL G (Q i)) → (∀ i, ∃ x ∈ P₀, (Q i).head? = some x) →
      (∀ i, ∃ y ∈ P₁, (Q i).getLast? = some y) → (∀ i j, i ≠ j → (Q i).Disjoint (Q j)) →
      (∀ i, ∀ x ∈ Q i, x ∈ P₀ → (Q i).head? = some x) →
      (∀ i, ∀ x ∈ Q i, x ∈ P₁ → (Q i).getLast? = some x) →
      (∀ i, D + 1 ≤ (Q i).length) →
      ∃ l, IsPathL G l ∧ a * D * (k : ℝ) ^ (1 - η) ≤ (l.length : ℝ) - 1 := by
  obtain ⟨n0, hn0⟩ := h12 η hη0
  set N0 := max n0 1 with hN0
  have hN01 : 1 ≤ N0 := le_max_right _ _
  have hN0pos : (0 : ℝ) < N0 := by exact_mod_cast hN01
  refine ⟨1 / (4 * N0), by positivity, ?_⟩
  intro V G P₀ P₁ k Q D hk hP₀ hP₁ hdisj hQ hQ0 hQ1 hQd hQP0 hQP1 hQlen
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpow : (k : ℝ) ^ (1 - η) ≤ k := by
    calc (k : ℝ) ^ (1 - η) ≤ (k : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)
      _ = k := Real.rpow_one _
  have hD0 : (0 : ℝ) ≤ D := by positivity
  by_cases hkN : k < N0
  · refine ⟨Q ⟨0, by omega⟩, hQ _, ?_⟩
    have hlen := hQlen ⟨0, by omega⟩
    have hlen' : (D : ℝ) ≤ ((Q ⟨0, by omega⟩).length : ℝ) - 1 := by
      have : ((D + 1 : ℕ) : ℝ) ≤ ((Q ⟨0, by omega⟩).length : ℝ) := by exact_mod_cast hlen
      push_cast at this; linarith
    have hkN' : (k : ℝ) ≤ N0 := by exact_mod_cast hkN.le
    calc 1 / (4 * (N0 : ℝ)) * D * (k : ℝ) ^ (1 - η) ≤ 1 / (4 * (N0 : ℝ)) * D * N0 := by
          gcongr; exact hkpow.trans hkN'
      _ = D / 4 := by field_simp
      _ ≤ D := by linarith
      _ ≤ _ := hlen'
  · push_neg at hkN
    obtain ⟨f, hf, hlift⟩ := two_rails_large G P₀ P₁ k Q D hk hP₀ hP₁ hdisj hQ hQ0 hQ1 hQd
      hQP0 hQP1 hQlen
    obtain ⟨l, hl, hcount⟩ := hn0 k (le_trans (le_max_left _ _) hkN) f hf
    obtain ⟨l2, hl2, hne, hD⟩ := hlift l hl
    refine ⟨l2, hl2, ?_⟩
    have hl2len : 1 ≤ l2.length := List.length_pos_of_ne_nil hne
    have hD' : (D : ℝ) * countPairs (fun i j => matchAdj k f i j ∨ matchAdj k f j i) l ≤
        4 * ((l2.length : ℝ) - 1) := by
      have := (Nat.cast_le (α := ℝ)).2 hD
      push_cast [Nat.cast_sub hl2len] at this
      exact this
    have hq : 1 / (4 * (N0 : ℝ)) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : (1 : ℝ) ≤ N0 := by exact_mod_cast hN01
      linarith
    calc 1 / (4 * (N0 : ℝ)) * D * (k : ℝ) ^ (1 - η)
        ≤ 1 / 4 * D * countPairs (fun i j => matchAdj k f i j ∨ matchAdj k f j i) l := by
          gcongr
      _ ≤ _ := by linarith

end Lovasz
