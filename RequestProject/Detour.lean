module
public import RequestProject.InitCircuit

/-!
# Paths with detours (the dense case of Claim 2.12)

Walking along the first half `1, 2, …, n-2` of the cycle interval by interval, and replacing,
inside some intervals `I`, the stretch between two vertices `u₁ < u₂` of `I` by a detour
`u₁ → w₁ ⇝ w₂ → u₂` through an interval `J` of the second half (where `u₁ w₁` and `u₂ w₂` are
edges of `M`), we obtain a path of `L ∪ M` using two edges of `M` per detour, provided distinct
detours use distinct intervals `J`.
-/

@[expose] public section


open Classical

namespace Lovasz

lemma exists_of_mem_lpairs {α : Type*} {l : List α} {p : α × α} (hp : p ∈ lpairs l) :
    ∃ j, ∃ h : j + 1 < l.length, p = (l[j]'(by omega), l[j + 1]) := by
  unfold lpairs at hp
  obtain ⟨j, hj, e⟩ := List.getElem_of_mem hp
  simp only [List.length_zip, List.length_tail] at hj
  refine ⟨j, by omega, ?_⟩
  rw [← e]
  simp [List.getElem_zip, List.getElem_tail]

namespace Conc

variable {n t : ℕ}

section detour

variable (hn : 0 < n) (t)

/-- Detour data: `dt k = some (u₁, w₁, u₂, w₂)`. -/
abbrev DT (n : ℕ) := ℕ → Option (Fin (2 * n) × Fin (2 * n) × Fin (2 * n) × Fin (2 * n))

/-- The piece of the path inside the `k`-th interval of the first half. -/
noncomputable def piece (dt : DT n) (k : ℕ) : List (Fin (2 * n)) :=
  match dt k with
  | some (u₁, w₁, u₂, w₂) =>
      rng n hn (st n t k) u₁.val ++ seg n hn w₁ w₂ ++ rng n hn u₂.val (st n t k + t - 1)
  | none => rng n hn (st n t k) (st n t k + t - 1)

variable {t}

/-- The conditions on the detour data. -/
def DetourOK (t : ℕ) (f : Fin n → Fin n) (dt : DT n) (J : ℕ → ℕ) : Prop :=
  ∀ k < nQ n t, ∀ u₁ w₁ u₂ w₂, dt k = some (u₁, w₁, u₂, w₂) →
    st n t k ≤ u₁.val ∧ u₁.val < u₂.val ∧ u₂.val < st n t k + t ∧
    Mrel n f u₁ w₁ ∧ Mrel n f u₂ w₂ ∧ nQ n t ≤ J k ∧ J k < 2 * nQ n t ∧
    st n t (J k) ≤ w₁.val ∧ w₁.val < st n t (J k) + t ∧
    st n t (J k) ≤ w₂.val ∧ w₂.val < st n t (J k) + t

variable {hn}

lemma mem_piece {f : Fin n → Fin n} {dt : DT n} {J : ℕ → ℕ} (hdt : DetourOK t f dt J)
    {k : ℕ} (hk : k < nQ n t) {x : Fin (2 * n)} (hx : x ∈ piece t hn dt k) :
    (st n t k ≤ x.val ∧ x.val < st n t k + t) ∨
      ((dt k).isSome ∧ st n t (J k) ≤ x.val ∧ x.val < st n t (J k) + t) := by
  have ht : 0 < t := t_pos_of hk
  have hb := st_lt_half (n := n) (t := t) hk
  unfold piece at hx
  split at hx
  · rename_i u₁ w₁ u₂ w₂ e
    obtain ⟨h1, h2, h3, -, -, h6, h7, h8, h9, h10, h11⟩ := hdt k hk u₁ w₁ u₂ w₂ e
    rw [List.mem_append, List.mem_append, mem_rng (by omega), mem_seg, mem_rng (by omega)] at hx
    rcases hx with (hx | hx) | hx
    · left; omega
    · right
      refine ⟨by rw [e]; rfl, ?_, ?_⟩
      · rcases le_total w₁.val w₂.val with h | h
        · rw [min_eq_left h] at hx; omega
        · rw [min_eq_right h] at hx; omega
      · rcases le_total w₁.val w₂.val with h | h
        · rw [max_eq_right h] at hx; omega
        · rw [max_eq_left h] at hx; omega
    · left; omega
  · rw [mem_rng (by omega)] at hx
    left; omega

lemma piece_ne_nil (dt : DT n) (k : ℕ) (hk : k < nQ n t) {f : Fin n → Fin n} {J : ℕ → ℕ}
    (hdt : DetourOK t f dt J) : piece t hn dt k ≠ [] := by
  have ht : 0 < t := t_pos_of hk
  unfold piece
  split
  · rename_i u₁ w₁ u₂ w₂ e
    obtain ⟨h1, -⟩ := hdt k hk u₁ w₁ u₂ w₂ e
    simp [rng_ne_nil h1]
  · exact rng_ne_nil (by omega)

lemma piece_hd (dt : DT n) (k : ℕ) (hk : k < nQ n t) {f : Fin n → Fin n} {J : ℕ → ℕ}
    (hdt : DetourOK t f dt J) : (piece t hn dt k).head? = some (fv n hn (st n t k)) := by
  have ht : 0 < t := t_pos_of hk
  unfold piece
  split
  · rename_i u₁ w₁ u₂ w₂ e
    obtain ⟨h1, -⟩ := hdt k hk u₁ w₁ u₂ w₂ e
    rw [List.append_assoc, List.head?_append, rng_head h1]; rfl
  · exact rng_head (by omega)

lemma piece_last (dt : DT n) (k : ℕ) (hk : k < nQ n t) {f : Fin n → Fin n} {J : ℕ → ℕ}
    (hdt : DetourOK t f dt J) :
    (piece t hn dt k).getLast? = some (fv n hn (st n t k + t - 1)) := by
  have ht : 0 < t := t_pos_of hk
  unfold piece
  split
  · rename_i u₁ w₁ u₂ w₂ e
    obtain ⟨-, h2, h3, -⟩ := hdt k hk u₁ w₁ u₂ w₂ e
    rw [List.getLast?_append, rng_getLast (by omega)]; rfl
  · exact rng_getLast (by omega)

lemma piece_nodup (dt : DT n) (k : ℕ) (hk : k < nQ n t) {f : Fin n → Fin n} {J : ℕ → ℕ}
    (hdt : DetourOK t f dt J) : (piece t hn dt k).Nodup := by
  have ht : 0 < t := t_pos_of hk
  have hb := st_lt_half (n := n) (t := t) hk
  unfold piece
  split
  · rename_i u₁ w₁ u₂ w₂ e
    obtain ⟨h1, h2, h3, -, -, h6, h7, h8, h9, h10, h11⟩ := hdt k hk u₁ w₁ u₂ w₂ e
    have hJ := st_ge_half (n := n) (t := t) h6
    rw [List.nodup_append, List.nodup_append]
    refine ⟨⟨rng_nodup (by omega), seg_nodup _ _, ?_⟩, rng_nodup (by omega), ?_⟩
    · intro x hx y hy e'
      subst e'
      rw [mem_rng (by omega)] at hx
      rw [mem_seg] at hy
      have := hy.1
      simp only [min_le_iff] at this
      omega
    · intro x hx y hy e'
      subst e'
      rw [mem_rng (by omega)] at hy
      rw [List.mem_append, mem_rng (by omega), mem_seg] at hx
      rcases hx with hx | hx
      · omega
      · have := hx.1
        simp only [min_le_iff] at this
        omega
  · exact rng_nodup (by omega)

lemma piece_chain (dt : DT n) (k : ℕ) (hk : k < nQ n t) {f : Fin n → Fin n} {J : ℕ → ℕ}
    (hdt : DetourOK t f dt J) : (piece t hn dt k).IsChain (cycleMatchGraph n f).Adj := by
  have ht : 0 < t := t_pos_of hk
  have hb := st_lt_half (n := n) (t := t) hk
  unfold piece
  split
  · rename_i u₁ w₁ u₂ w₂ e
    obtain ⟨h1, h2, h3, h4, h5, -⟩ := hdt k hk u₁ w₁ u₂ w₂ e
    refine List.IsChain.append (List.IsChain.append (rng_chain f (by omega)) (seg_chain f _ _) ?_)
      (rng_chain f (by omega)) ?_
    · intro x hx y hy
      rw [rng_getLast h1, Option.mem_def, Option.some.injEq, fv_eq] at hx
      rw [seg_head, Option.mem_def, Option.some.injEq] at hy
      subst hx hy
      exact Mrel_adj h4
    · intro x hx y hy
      rw [List.getLast?_append, seg_last] at hx
      rw [rng_head (by omega), Option.mem_def, Option.some.injEq, fv_eq] at hy
      simp only [Option.some_or, Option.mem_def, Option.some.injEq] at hx
      subst hx hy
      exact (cycleMatchGraph n f).adj_symm (Mrel_adj h5)
  · exact rng_chain f (by omega)

lemma piece_count (dt : DT n) (k : ℕ) (hk : k < nQ n t) {f : Fin n → Fin n} {J : ℕ → ℕ}
    (hdt : DetourOK t f dt J) :
    (if (dt k).isSome then 2 else 0) ≤ countPairs (Mrel n f) (piece t hn dt k) := by
  have ht : 0 < t := t_pos_of hk
  rcases e : dt k with _ | ⟨u₁, w₁, u₂, w₂⟩
  · simp
  · obtain ⟨h1, h2, h3, h4, h5, -⟩ := hdt k hk u₁ w₁ u₂ w₂ e
    simp only [piece, e, Option.isSome_some, if_true]
    have hA := rng_ne_nil (n := n) (hn := hn) h1
    have hB : seg n hn w₁ w₂ ≠ [] := by
      intro h; have := seg_head (n := n) (hn := hn) w₁ w₂; rw [h] at this; simp at this
    have hC := rng_ne_nil (n := n) (hn := hn) (show u₂.val ≤ st n t k + t - 1 by omega)
    have hAB : rng n hn (st n t k) u₁.val ++ seg n hn w₁ w₂ ≠ [] := by simp [hA]
    rw [countPairs_append _ _ _ hAB hC, countPairs_append _ _ _ hA hB]
    have e1 : (rng n hn (st n t k) u₁.val).getLast hA = u₁ := by
      have := rng_getLast (n := n) (hn := hn) h1
      rw [List.getLast?_eq_some_getLast hA, fv_eq] at this
      exact Option.some.inj this
    have e2 : (seg n hn w₁ w₂).head hB = w₁ := by
      have := seg_head (n := n) (hn := hn) w₁ w₂
      rw [List.head?_eq_some_head hB] at this
      exact Option.some.inj this
    have e3 : (rng n hn (st n t k) u₁.val ++ seg n hn w₁ w₂).getLast hAB = w₂ := by
      have h' : (rng n hn (st n t k) u₁.val ++ seg n hn w₁ w₂).getLast? = some w₂ := by
        rw [List.getLast?_append, seg_last]; rfl
      rw [List.getLast?_eq_some_getLast hAB] at h'
      exact Option.some.inj h'
    have e4 : (rng n hn u₂.val (st n t k + t - 1)).head hC = u₂ := by
      have := rng_head (n := n) (hn := hn) (show u₂.val ≤ st n t k + t - 1 by omega)
      rw [List.head?_eq_some_head hC, fv_eq] at this
      exact Option.some.inj this
    rw [e1, e2, e3, e4, if_pos h4, if_pos (Mrel_symm h5)]
    omega

/-- **Detour paths.** -/
theorem detour_path (hn : 0 < n) (ht : 2 ≤ t) (hQ : 0 < nQ n t) (f : Fin n → Fin n) (hf : Function.Injective f)
    (dt : DT n) (J : ℕ → ℕ) (hdt : DetourOK t f dt J)
    (hJ : ∀ k k', k < nQ n t → k' < nQ n t → k ≠ k' → (dt k).isSome → (dt k').isSome →
      J k ≠ J k') :
    ∃ l, IsPathL (cycleMatchGraph n f) l ∧
      2 * ((Finset.range (nQ n t)).filter (fun k => (dt k).isSome)).card ≤
        countPairs (Mrel n f) l := by
  set g := cgeo n t hn ht hQ f hf (β := Unit) (fun _ => none) with hg
  set cs := (List.range (nQ n t)).map (piece t hn dt) with hcs
  have hmem : ∀ σ ∈ cs, ∃ k < nQ n t, σ = piece t hn dt k := by
    intro σ hσ
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hσ
    exact ⟨k, List.mem_range.1 hk, rfl⟩
  have hne : ∀ σ ∈ cs, σ ≠ [] := by
    intro σ hσ
    obtain ⟨k, hk, rfl⟩ := hmem σ hσ
    exact piece_ne_nil dt k hk hdt
  have hlt : ∀ k < nQ n t, g.lt (piece t hn dt k) = fv n hn (st n t k + t - 1) := by
    intro k hk
    unfold Geo.lt
    rw [List.getLastD_eq_getLast?, piece_last dt k hk hdt]; rfl
  have hhd : ∀ k < nQ n t, g.hd (piece t hn dt k) = fv n hn (st n t k) := by
    intro k hk
    unfold Geo.hd
    rw [List.headD_eq_head?_getD, piece_hd dt k hk hdt]; rfl
  refine ⟨cs.flatten, ⟨?_, ?_⟩, ?_⟩
  · have hG : g.Γ = cycleMatchGraph n f := rfl
    rw [← hG]
    refine g.chain_flatten hne (fun σ hσ => ?_) (fun p hp => ?_)
    · rw [hG]
      obtain ⟨k, hk, rfl⟩ := hmem σ hσ
      exact piece_chain dt k hk hdt
    · obtain ⟨j, hj, rfl⟩ := exists_of_mem_lpairs hp
      simp only [hcs, List.length_map, List.length_range] at hj
      simp only [hcs, List.getElem_map, List.getElem_range]
      rw [hlt j (by omega), hhd (j + 1) hj]
      have e : st n t (j + 1) = st n t j + t - 1 + 1 := by
        have h1 : j + 1 < nQ n t := hj
        have ht0 : 0 < t := by omega
        unfold st; rw [if_pos h1, if_pos (by omega)]; rw [Nat.add_mul, one_mul]; omega
      rw [e, hG]
      exact adj_succ f (by have := st_lt_half (n := n) (t := t) (k := j + 1) hj; omega)
  · rw [List.nodup_flatten]
    refine ⟨fun σ hσ => ?_, ?_⟩
    · obtain ⟨k, hk, rfl⟩ := hmem σ hσ
      exact piece_nodup dt k hk hdt
    · rw [hcs, List.pairwise_map]
      refine List.pairwise_iff_getElem.2 fun i j hi hj hij => ?_
      simp only [List.length_range] at hi hj
      simp only [List.getElem_range]
      intro x hx1 hx2
      rcases mem_piece hdt hi hx1 with h1 | ⟨s1, h1⟩ <;>
        rcases mem_piece hdt hj hx2 with h2 | ⟨s2, h2⟩
      · have := st_inj (n := n) (t := t) (by omega) (by omega) h1.1 h1.2 h2.1 h2.2; omega
      · obtain ⟨-, -, -, -, -, h6, -⟩ := hdt j hj _ _ _ _ (Option.some_get s2).symm
        have := st_lt_half (n := n) (t := t) hi
        have := st_ge_half (n := n) (t := t) h6
        omega
      · obtain ⟨-, -, -, -, -, h6, -⟩ := hdt i hi _ _ _ _ (Option.some_get s1).symm
        have := st_lt_half (n := n) (t := t) hj
        have := st_ge_half (n := n) (t := t) h6
        omega
      · obtain ⟨-, -, -, -, -, -, h7, -⟩ := hdt i hi _ _ _ _ (Option.some_get s1).symm
        obtain ⟨-, -, -, -, -, -, h7', -⟩ := hdt j hj _ _ _ _ (Option.some_get s2).symm
        exact hJ i j hi hj (by omega) s1 s2
          (st_inj (n := n) (t := t) h7 h7' h1.1 h1.2 h2.1 h2.2)
  · rw [g.countPairs_flatten (Mrel n f) hne]
    have h1 : 2 * ((Finset.range (nQ n t)).filter (fun k => (dt k).isSome)).card ≤ (cs.map (countPairs (Mrel n f))).sum := by
      rw [Finset.card_filter, Finset.mul_sum]
      have : (cs.map (countPairs (Mrel n f))).sum = ∑ k ∈ Finset.range (nQ n t), countPairs (Mrel n f) (piece t hn dt k) := by
        rw [hcs, List.map_map]; rfl
      rw [this]
      refine Finset.sum_le_sum fun k hk => ?_
      have := piece_count (hn := hn) dt k (Finset.mem_range.1 hk) hdt
      split_ifs at this ⊢ <;> omega
    exact le_trans h1 (Nat.le_add_right _ _)

end detour

end Conc

end Lovasz
