module
public import RequestProject.VTBasic

/-!
# Disjoint lifts of quotient paths (Lemma A.8)

If every `N`-orbit has `m` elements, the edges of `X` between two adjacent orbits form a
biregular bipartite graph with both parts of size `m`, hence (Hall) contain a perfect matching.
Following these matchings along a path of `X/N` gives `m` pairwise vertex-disjoint lifts.
-/

@[expose] public section


open Classical

namespace Lovasz

variable {V Γ : Type*} [Group Γ] [MulAction Γ V] [Fintype Γ] {X : SimpleGraph V}

/-- The neighbours of `x` in a finset `B`. -/
noncomputable def nbrIn (X : SimpleGraph V) (B : Finset V) (x : V) : Finset V :=
  B.filter (X.Adj x)

lemma card_nbrIn_orb (hX : ActsOn X Γ) (N : Subgroup Γ) (b : V) {a x : V}
    (hx : fib N x = fib N a) : (nbrIn X (orb N b) x).card = (nbrIn X (orb N b) a).card := by
  obtain ⟨n, hn, rfl⟩ := fib_eq_iff.1 hx
  refine Finset.card_bij (fun y _ => n⁻¹ • y) ?_ ?_ ?_
  · intro y hy
    obtain ⟨hyb, hadj⟩ := Finset.mem_filter.1 hy
    refine Finset.mem_filter.2 ⟨mem_orb.2 ?_, ?_⟩
    · rw [fib_smul_of_mem (N.inv_mem hn)]; exact mem_orb.1 hyb
    · have := hX n⁻¹ _ _ hadj; simpa using this
  · intro y _ y' _ h; exact MulAction.injective n⁻¹ h
  · intro y hy
    obtain ⟨hyb, hadj⟩ := Finset.mem_filter.1 hy
    refine ⟨n • y, Finset.mem_filter.2 ⟨mem_orb.2 ?_, hX n _ _ hadj⟩, by simp⟩
    rw [fib_smul_of_mem hn]; exact mem_orb.1 hyb

/-- **Hall step of Lemma A.8.** Between two orbits joined by an edge there is a perfect
matching. -/
lemma exists_orbit_matching (hX : ActsOn X Γ) (N : Subgroup Γ) {m : ℕ}
    (hm : ∀ v : V, (orb N v).card = m) {a b : V} (hab : X.Adj a b) :
    ∃ σ : V → V, (∀ x ∈ orb N a, σ x ∈ orb N b ∧ X.Adj x (σ x)) ∧ Set.InjOn σ (orb N a) := by
  set A := orb N a
  set B := orb N b
  set d := (nbrIn X B a).card with hd
  set d' := (nbrIn X A b).card with hd'
  have hdA : ∀ x ∈ A, (nbrIn X B x).card = d := fun x hx => card_nbrIn_orb hX N b (mem_orb.1 hx)
  have hdB : ∀ y ∈ B, (nbrIn X A y).card = d' := fun y hy => card_nbrIn_orb hX N a (mem_orb.1 hy)
  have hdd : d = d' := by
    have h := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun x y => X.Adj x y)
      (s := A) (t := B)
    have e1 : ∀ x ∈ A, (Finset.bipartiteAbove (fun x y => X.Adj x y) B x).card = d :=
      fun x hx => hdA x hx
    have e2 : ∀ y ∈ B, (Finset.bipartiteBelow (fun x y => X.Adj x y) A y).card = d' := by
      intro y hy
      rw [← hdB y hy]
      unfold Finset.bipartiteBelow nbrIn
      congr 1; ext x; simp only [Finset.mem_filter]
      exact ⟨fun h => ⟨h.1, h.2.symm⟩, fun h => ⟨h.1, h.2.symm⟩⟩
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_const, Finset.sum_const,
      smul_eq_mul, smul_eq_mul, hm a, hm b] at h
    have hm0 : 0 < m := by rw [← hm a]; exact Finset.card_pos.2 ⟨a, self_mem_orb N a⟩
    exact Nat.eq_of_mul_eq_mul_left hm0 h
  have hd0 : 0 < d := Finset.card_pos.2 ⟨b, Finset.mem_filter.2 ⟨self_mem_orb N b, hab⟩⟩
  let t : {x // x ∈ A} → Finset V := fun x => nbrIn X B x
  have hhall : ∀ s : Finset {x // x ∈ A}, s.card ≤ (s.biUnion t).card := by
    intro s
    have h := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (fun (x : {x // x ∈ A}) y => X.Adj x y) (s := s) (t := s.biUnion t)
    have e1 : ∀ x ∈ s, (Finset.bipartiteAbove (fun (x : {x // x ∈ A}) y => X.Adj x y)
        (s.biUnion t) x).card = d := by
      intro x hx
      rw [← hdA x x.2]
      unfold Finset.bipartiteAbove nbrIn
      congr 1; ext y
      simp only [Finset.mem_filter, Finset.mem_biUnion]
      constructor
      · rintro ⟨⟨x', -, hy⟩, hadj⟩; exact ⟨(Finset.mem_filter.1 hy).1, hadj⟩
      · rintro ⟨hy, hadj⟩; exact ⟨⟨x, hx, Finset.mem_filter.2 ⟨hy, hadj⟩⟩, hadj⟩
    have e2 : ∀ y ∈ s.biUnion t, (Finset.bipartiteBelow (fun (x : {x // x ∈ A}) y => X.Adj x y)
        s y).card ≤ d := by
      intro y hy
      obtain ⟨x, -, hyx⟩ := Finset.mem_biUnion.1 hy
      have hyB : y ∈ B := (Finset.mem_filter.1 hyx).1
      rw [hdd, ← hdB y hyB]
      refine Finset.card_le_card_of_injOn (fun x => (x : V)) ?_ ?_
      · intro x hx
        have hx' := Finset.mem_filter.1 hx
        exact Finset.mem_filter.2 ⟨x.2, hx'.2.symm⟩
      · intro x _ x' _ h; exact Subtype.ext h
    rw [Finset.sum_congr rfl e1, Finset.sum_const, smul_eq_mul] at h
    have h2 := Finset.sum_le_sum e2
    rw [Finset.sum_const, smul_eq_mul] at h2
    have : s.card * d ≤ (s.biUnion t).card * d := h ▸ h2
    exact Nat.le_of_mul_le_mul_right this hd0
  obtain ⟨f, hfinj, hft⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hhall
  refine ⟨fun x => if h : x ∈ A then f ⟨x, h⟩ else x, ?_, ?_⟩
  · intro x hx
    simp only [dif_pos hx]
    exact Finset.mem_filter.1 (hft ⟨x, hx⟩)
  · intro x hx x' hx' h
    simp only [Finset.mem_coe] at hx hx'
    simp only [dif_pos hx, dif_pos hx'] at h
    exact congrArg Subtype.val (hfinj h)

/-- **Lemma A.8** (disjoint lifts of a quotient path). Every path `l` of `X/N` has a lift
starting at every vertex of its initial orbit; these lifts are paths of `X` projecting onto `l`,
and lifts with different starting vertices are vertex-disjoint. -/
theorem exists_disjoint_lifts (hX : ActsOn X Γ) (N : Subgroup Γ) {m : ℕ}
    (hm : ∀ v : V, (orb N v).card = m) :
    ∀ (l : List (Fib N V)) (hne : l ≠ []), IsPathL (quotGraph X N) l →
      ∃ Lf : V → List V, (∀ x, fib N x = l.head hne →
          IsPathL X (Lf x) ∧ (Lf x).map (fib N) = l ∧ (Lf x).head? = some x) ∧
        ∀ x x', fib N x = l.head hne → fib N x' = l.head hne → x ≠ x' → (Lf x).Disjoint (Lf x')
  | [], hne, _ => absurd rfl hne
  | [p], _, _ => by
    refine ⟨fun x => [x], fun x hx => ⟨isPathL_singleton x, by simpa using hx, rfl⟩, ?_⟩
    intro x x' _ _ hxx' y hy hy'
    simp only [List.mem_singleton] at hy hy'
    exact hxx' (hy.symm.trans hy')
  | p :: p' :: rest, _, hl => by
    have hl' : IsPathL (quotGraph X N) (p' :: rest) := hl.suffix (List.suffix_cons _ _)
    obtain ⟨Lf', hLf', hdisj'⟩ := exists_disjoint_lifts hX N hm (p' :: rest) (by simp) hl'
    have hadj := (List.isChain_cons_cons.1 hl.1).1
    obtain ⟨-, u, v, rfl, rfl, huv⟩ := quotGraph_adj.1 hadj
    obtain ⟨σ, hσ, hσinj⟩ := exists_orbit_matching hX N hm huv
    have hpnot : fib N u ∉ fib N v :: rest := (List.nodup_cons.1 hl.2).1
    have hnot : ∀ x, fib N x = fib N u → ∀ y, fib N y = fib N v → x ∉ Lf' y := by
      intro x hx y hy hmem
      apply hpnot
      rw [← hx, ← (hLf' y hy).2.1]
      exact List.mem_map_of_mem hmem
    have hσv : ∀ x, fib N x = fib N u → fib N (σ x) = fib N v :=
      fun x hx => mem_orb.1 (hσ x (mem_orb.2 hx)).1
    refine ⟨fun x => x :: Lf' (σ x), ?_, ?_⟩
    · intro x hx
      simp only [List.head_cons] at hx
      obtain ⟨hP, hmap, hhead⟩ := hLf' (σ x) (hσv x hx)
      refine ⟨⟨?_, List.nodup_cons.2 ⟨hnot x hx _ (hσv x hx), hP.2⟩⟩, ?_, rfl⟩
      · obtain ⟨t, ht⟩ : ∃ t, Lf' (σ x) = σ x :: t := by
          cases h : Lf' (σ x) with
          | nil => rw [h] at hhead; simp at hhead
          | cons a t => rw [h] at hhead; simp at hhead; exact ⟨t, by rw [hhead]⟩
        show List.IsChain X.Adj (x :: Lf' (σ x))
        rw [ht]
        refine List.IsChain.cons_cons (hσ x (mem_orb.2 hx)).2 ?_
        rw [← ht]; exact hP.1
      · simp only [List.map_cons, hx, hmap]
    · intro x x' hx hx' hxx'
      simp only [List.head_cons] at hx hx'
      have hσne : σ x ≠ σ x' := fun h => hxx' (hσinj (mem_orb.2 hx) (mem_orb.2 hx') h)
      intro y hy hy'
      simp only [List.mem_cons] at hy hy'
      rcases hy with rfl | hy <;> rcases hy' with h | hy'
      · exact hxx' h
      · exact hnot y hx _ (hσv x' hx') hy'
      · subst h; exact hnot y hx' _ (hσv x hx) hy
      · exact hdisj' _ _ (hσv x hx) (hσv x' hx') hσne hy hy'

/-- Paths of the quotient lift to paths of the same order: `p(X/N) ≤ p(X)`. -/
theorem pathOrder_quotGraph_le [Finite V] (hX : ActsOn X Γ) (N : Subgroup Γ) {m : ℕ}
    (hm : ∀ v : V, (orb N v).card = m) : pathOrder (quotGraph X N) ≤ pathOrder X := by
  obtain ⟨l, hl, hlen⟩ := exists_isPathL_length_eq_pathOrder (quotGraph X N)
  rw [← hlen]
  by_cases hne : l = []
  · simp [hne]
  obtain ⟨Lf, hLf, -⟩ := exists_disjoint_lifts hX N hm l hne hl
  obtain ⟨x, hx⟩ := fib_surjective N (l.head hne)
  obtain ⟨hP, hmap, -⟩ := hLf x hx
  calc l.length = (Lf x).length := by rw [← hmap, List.length_map]
    _ ≤ pathOrder X := hP.length_le_pathOrder

end Lovasz
