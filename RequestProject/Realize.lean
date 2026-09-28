module
public import RequestProject.TwoRails
public import RequestProject.Connectors

/-!
# Realizing paths of a model graph (machinery for Lemma 3.1)

A path in a "model" graph on `M` is realized in `G` by replacing every model vertex `w` by a
vertex `ρ w` and every model edge `(u, v)` by a path `R u v` from `ρ u` to `ρ v`.  If distinct
model edges are realized by paths meeting only in realization vertices, and each `R u v` meets
the realization vertices only at its ends, the realization of a model path is a path.

We also record the elementary facts about `countPairs` and about cutting a path at "bad"
edges which are needed to pass from Theorem 1.2 to Lemma 3.1.
-/

@[expose] public section


open Classical

namespace Lovasz

section countPairs

variable {α : Type*} (r : α → α → Prop)

lemma countPairs_cons (c : α) (l : List α) :
    countPairs r (c :: l) = (if ∃ d ∈ l.head?, r c d then 1 else 0) + countPairs r l := by
  cases l with
  | nil => simp [countPairs]
  | cons d l => simp [countPairs]

lemma countPairs_append_cons_cons (A : List α) (a b : α) (B : List α) :
    countPairs r (A ++ a :: b :: B) =
      countPairs r (A ++ [a]) + (if r a b then 1 else 0) + countPairs r (b :: B) := by
  induction A with
  | nil => simp [countPairs]
  | cons c A ih =>
    rw [List.cons_append, countPairs_cons, ih, List.cons_append, countPairs_cons r c (A ++ [a])]
    cases A with
    | nil => simp; ring
    | cons d A => simp; ring

end countPairs

section cut

variable {α : Type*}

/-- Cutting a duplicate-free list at the (unique) occurrence of a bad edge. -/
lemma exists_good_piece (Mt Bad : α → α → Prop) (hBM : ∀ u v, Bad u v → ¬ Mt u v)
    (hBad : ∀ u v u' v', Bad u v → Bad u' v' → (u = u' ∧ v = v') ∨ (u = v' ∧ v = u'))
    (l : List α) (hl : l.Nodup) :
    ∃ l', l' <:+: l ∧ (∀ u v, [u, v] <:+: l' → ¬ Bad u v) ∧
      countPairs Mt l ≤ 2 * countPairs Mt l' := by
  by_cases h : ∃ u v, [u, v] <:+: l ∧ Bad u v
  · obtain ⟨u, v, ⟨A, B, hAB⟩, huv⟩ := h
    have hl' : l = (A ++ [u]) ++ v :: B := by rw [← hAB]; simp
    rw [hl'] at hl
    have hdisj := (List.nodup_append.1 hl).2.2
    have hcount : countPairs Mt l = countPairs Mt (A ++ [u]) + countPairs Mt (v :: B) := by
      rw [hl', List.append_assoc, List.singleton_append, countPairs_append_cons_cons,
        if_neg (hBM u v huv), add_zero]
    have hinf1 : A ++ [u] <:+: l := by rw [hl']; exact (List.prefix_append _ _).isInfix
    have hinf2 : v :: B <:+: l := by rw [hl']; exact (List.suffix_append _ _).isInfix
    have hno1 : ∀ u' v', [u', v'] <:+: A ++ [u] → ¬ Bad u' v' := by
      intro u' v' hinf hbad
      have hsub := hinf.subset
      rcases hBad u v u' v' huv hbad with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact hdisj v (hsub (by simp)) v (by simp) rfl
      · exact hdisj v (hsub (by simp)) v (by simp) rfl
    have hno2 : ∀ u' v', [u', v'] <:+: v :: B → ¬ Bad u' v' := by
      intro u' v' hinf hbad
      have hsub := hinf.subset
      rcases hBad u v u' v' huv hbad with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact hdisj u (by simp) u (hsub (by simp)) rfl
      · exact hdisj u (by simp) u (hsub (by simp)) rfl
    rcases le_total (countPairs Mt (v :: B)) (countPairs Mt (A ++ [u])) with hle | hle
    · exact ⟨A ++ [u], hinf1, hno1, by omega⟩
    · exact ⟨v :: B, hinf2, hno2, by omega⟩
  · push_neg at h
    exact ⟨l, List.infix_refl l, fun u v huv => h u v huv, by omega⟩

end cut

section realize

variable {M V : Type*}

/-- The realization of a model path. -/
def realize (ρ : M → V) (R : M → M → List V) : List M → List V
  | [] => []
  | [u] => [ρ u]
  | u :: v :: rest => R u v ++ (realize ρ R (v :: rest)).tail

lemma realize_spec (G : SimpleGraph V) (ρ : M → V)
    (R : M → M → List V) (Adm Mt : M → M → Prop) (D : ℕ)
    (hR : ∀ u v, Adm u v →
      IsPathL G (R u v) ∧ (R u v).head? = some (ρ u) ∧ (R u v).getLast? = some (ρ v))
    (hb : ∀ u v, Adm u v → ∀ y ∈ R u v, ∀ w, y = ρ w → w = u ∨ w = v)
    (hc : ∀ u v u' v', Adm u v → Adm u' v' → ¬ ((u = u' ∧ v = v') ∨ (u = v' ∧ v = u')) →
      ∀ y ∈ R u v, y ∈ R u' v' → ∃ w, y = ρ w)
    (hlen : ∀ u v, Adm u v → Mt u v → D + 1 ≤ (R u v).length) :
    ∀ (l : List M) (u : M), (u :: l).Nodup → (u :: l).IsChain Adm →
      IsPathL G (realize ρ R (u :: l)) ∧ (realize ρ R (u :: l)).head? = some (ρ u) ∧
      D * countPairs Mt (u :: l) + 1 ≤ (realize ρ R (u :: l)).length ∧
      ∀ y ∈ realize ρ R (u :: l),
        (∃ w ∈ u :: l, y = ρ w) ∨ ∃ w w', [w, w'] <:+: u :: l ∧ Adm w w' ∧ y ∈ R w w' := by
  intro l
  induction l with
  | nil =>
    intro u _ _
    refine ⟨isPathL_singleton _, rfl, by simp [realize, countPairs], ?_⟩
    intro y hy
    simp only [realize, List.mem_singleton] at hy
    exact Or.inl ⟨u, by simp, hy⟩
  | cons v rest ih =>
    intro u hnd hch
    have hadj : Adm u v := (List.isChain_cons_cons.1 hch).1
    have hnd' : (v :: rest).Nodup := (List.nodup_cons.1 hnd).2
    have hunot : u ∉ v :: rest := (List.nodup_cons.1 hnd).1
    obtain ⟨hP, hH, hL, hM⟩ := ih v hnd' (List.isChain_cons_cons.1 hch).2
    obtain ⟨hRp, hRh, hRl⟩ := hR u v hadj
    have hreal : realize ρ R (u :: v :: rest) = R u v ++ (realize ρ R (v :: rest)).tail := rfl
    rw [hreal]
    -- common vertices of `R u v` and the rest
    have hcap : ∀ y ∈ R u v, y ∈ realize ρ R (v :: rest) → y = ρ v := by
      intro y hy hy'
      rcases hM y hy' with ⟨w, hw, rfl⟩ | ⟨w, w', hww', hadj', hyw⟩
      · rcases hb u v hadj _ hy w rfl with rfl | rfl
        · exact absurd hw hunot
        · rfl
      · have hsub := hww'.subset
        have hne : ¬ ((u = w ∧ v = w') ∨ (u = w' ∧ v = w)) := by
          rintro (⟨rfl, -⟩ | ⟨rfl, -⟩)
          · exact hunot (hsub (by simp))
          · exact hunot (hsub (by simp))
        obtain ⟨z, rfl⟩ := hc u v w w' hadj hadj' hne y hy hyw
        rcases hb u v hadj _ hy z rfl with rfl | rfl
        · rcases hb w w' hadj' _ hyw z rfl with rfl | rfl
          · exact absurd (hsub (by simp)) hunot
          · exact absurd (hsub (by simp)) hunot
        · rfl
    refine ⟨⟨glue_chain hRp.1 hP.1 hRl hH, glue_nodup hRp.2 hP.2 hH hcap⟩,
      by rw [glue_head hRl]; exact hRh, ?_, ?_⟩
    · have hl1 : 1 ≤ (realize ρ R (v :: rest)).length := by
        cases h : realize ρ R (v :: rest) with
        | nil => rw [h] at hH; simp at hH
        | cons _ _ => simp
      have hlen' : (R u v ++ (realize ρ R (v :: rest)).tail).length + 1 =
          (R u v).length + (realize ρ R (v :: rest)).length := by
        rw [List.length_append, List.length_tail]; omega
      have hR1 : 1 ≤ (R u v).length := by
        cases h : R u v with
        | nil => rw [h] at hRh; simp at hRh
        | cons _ _ => simp
      have hcnt : countPairs Mt (u :: v :: rest) =
          (if Mt u v then 1 else 0) + countPairs Mt (v :: rest) := rfl
      rw [hcnt]
      by_cases hmt : Mt u v
      · simp only [hmt, if_true]
        have := hlen u v hadj hmt
        rw [mul_add]; omega
      · simp only [hmt, if_false, zero_add]; omega
    · intro y hy
      rcases glue_mem hy with h | h
      · exact Or.inr ⟨u, v, ⟨[], rest, by simp⟩, hadj, h⟩
      · rcases hM y h with ⟨w, hw, rfl⟩ | ⟨w, w', hww', hadj', hyw⟩
        · exact Or.inl ⟨w, List.mem_cons_of_mem _ hw, rfl⟩
        · exact Or.inr ⟨w, w', hww'.trans (List.suffix_cons _ _).isInfix, hadj', hyw⟩

end realize

section slices

variable {α : Type*}

lemma subpath_facts (l : List α) (i j : ℕ) (hij : i ≤ j) (hj : j < l.length) :
    ((l.drop i).take (j - i + 1)).length = j - i + 1 ∧
    ((l.drop i).take (j - i + 1)).head? = some l[i] ∧
    ((l.drop i).take (j - i + 1)).getLast? = some l[j] ∧
    ∀ z ∈ (l.drop i).take (j - i + 1), ∃ k, ∃ hk : k < l.length, i ≤ k ∧ k ≤ j ∧ l[k] = z := by
  refine ⟨by simp; omega, by rw [List.head?_eq_getElem?]; simp, ?_, ?_⟩
  · rw [List.getLast?_eq_getElem?]; simp
    have : i + (min (j - i + 1) (l.length - i) - 1) = j := by omega
    rw [this]; simp
  · intro z hz
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hz
    simp at hk
    exact ⟨i + k, by omega, by omega, by omega, by simp⟩

lemma slice_infix (l : List α) (i n : ℕ) : (l.drop i).take n <:+: l :=
  (List.take_prefix _ _).isInfix.trans (List.drop_suffix _ _).isInfix

end slices

end Lovasz
