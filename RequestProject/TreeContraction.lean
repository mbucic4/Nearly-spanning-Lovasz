module
public import RequestProject.Rails

/-!
# Tree contraction (machinery for Lemma 3.11)

A subgroup `K` acts freely by left multiplication on a `K`-invariant connected vertex set `Z`
of `cay S`.  We choose a connected set `T0 ⊆ Z` meeting every `K`-orbit exactly once; its
translates `k T0` (the *cells*) partition `Z`, and contracting them gives the Cayley graph
`cay (contractGen S K T0)` of `K`.
-/

@[expose] public section


open Classical

namespace Lovasz

variable {H : Type*} [Group H]

/-- The cell `k T0`. -/
def cell (K : Subgroup H) (T0 : Set H) (k : K) : Set H := (fun x => (k : H) * x) '' T0

/-- The generating set of the contracted Cayley graph: `k` is a generator if some vertex of
`T0` is adjacent to some vertex of the cell `k T0`. -/
def contractGen (S : Set H) (K : Subgroup H) (T0 : Set H) : Set K :=
  {k | ∃ u ∈ T0, ∃ v ∈ T0, (cay S).Adj u ((k : H) * v)}

section

variable {S : Set H} {K : Subgroup H} {T0 : Set H}

lemma cell_unique (hdist : ∀ x ∈ T0, ∀ y ∈ T0, x * y⁻¹ ∈ K → x = y) {k k' : K} {x : H}
    (hk : x ∈ cell K T0 k) (hk' : x ∈ cell K T0 k') : k = k' := by
  obtain ⟨u, hu, rfl⟩ := hk
  obtain ⟨v, hv, hv'⟩ := hk'
  simp only at hv'
  have hvu : v = u := hdist v hv u hu (by
    have : v = (k' : H)⁻¹ * (k * u) := by rw [← hv']; group
    rw [this]; simpa [mul_assoc] using K.mul_mem (K.inv_mem k'.2) k.2)
  subst hvu
  exact Subtype.ext (mul_right_cancel hv'.symm)

lemma cell_orbit_unique (hdist : ∀ x ∈ T0, ∀ y ∈ T0, x * y⁻¹ ∈ K → x = y) {k : K} {t t' : H}
    (ht : t ∈ cell K T0 k) (ht' : t' ∈ cell K T0 k) (htt' : t * t'⁻¹ ∈ K) : t = t' := by
  obtain ⟨u, hu, rfl⟩ := ht
  obtain ⟨u', hu', rfl⟩ := ht'
  have : u * u'⁻¹ ∈ K := by
    have := K.mul_mem (K.mul_mem (K.inv_mem k.2) htt') k.2
    simpa [mul_assoc] using this
  simp [hdist u hu u' hu' this]

lemma cell_subset {Z : Set H} (hZ : ∀ k ∈ K, ∀ z ∈ Z, k * z ∈ Z) (hT0Z : T0 ⊆ Z) (k : K) :
    cell K T0 k ⊆ Z := by
  rintro _ ⟨u, hu, rfl⟩; exact hZ k k.2 u (hT0Z hu)

lemma cell_reach (hconn0 : ∀ u ∈ T0, ∀ v ∈ T0, ReachIn (cay S) T0 u v) {k : K} {x y : H}
    (hx : x ∈ cell K T0 k) (hy : y ∈ cell K T0 k) : ReachIn (cay S) (cell K T0 k) x y := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  exact (hconn0 u hu v hv).map_mul_left (k : H)

lemma cell_adj {k k' : K} {x y : H} (hx : x ∈ cell K T0 k) (hy : y ∈ cell K T0 k')
    (hxy : (cay S).Adj x y) (hkk' : k ≠ k') : (cay (contractGen S K T0)).Adj k k' := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  rw [cay_adj]
  refine ⟨hkk', Or.inl ⟨u, hu, v, hv, ?_⟩⟩
  have := (cay_adj_mul_left (S := S) ((k : H)⁻¹)).2 hxy
  simpa [mul_assoc] using this

lemma contract_adj_lift {k k' : K} (h : (cay (contractGen S K T0)).Adj k k') :
    ∃ x ∈ cell K T0 k, ∃ y ∈ cell K T0 k', (cay S).Adj x y := by
  rw [cay_adj] at h
  obtain ⟨-, h | h⟩ := h
  · obtain ⟨u, hu, v, hv, huv⟩ := h
    refine ⟨k * u, ⟨u, hu, rfl⟩, k' * v, ⟨v, hv, rfl⟩, ?_⟩
    have := (cay_adj_mul_left (S := S) (k : H)).2 huv
    simpa [mul_assoc] using this
  · obtain ⟨u, hu, v, hv, huv⟩ := h
    refine ⟨k * v, ⟨v, hv, rfl⟩, k' * u, ⟨u, hu, rfl⟩, ?_⟩
    have := (cay_adj_mul_left (S := S) (k' : H)).2 huv
    simpa [mul_assoc] using this.symm

/-- Lifting paths of the contracted graph: a path `k :: l` lifts to a path meeting exactly the
cells of `k :: l`, each at least once, and which starts with its whole visit to the cell `k`. -/
lemma lift_contract_path (hdist : ∀ x ∈ T0, ∀ y ∈ T0, x * y⁻¹ ∈ K → x = y)
    (hne0 : T0.Nonempty) (hconn0 : ∀ u ∈ T0, ∀ v ∈ T0, ReachIn (cay S) T0 u v) :
    ∀ (l : List K) (k : K), IsPathL (cay (contractGen S K T0)) (k :: l) →
      ∃ P : List H, IsPathL (cay S) P ∧ (∀ x ∈ P, ∃ k' ∈ k :: l, x ∈ cell K T0 k') ∧
        (∀ k' ∈ k :: l, ∃ x ∈ P, x ∈ cell K T0 k') ∧
        ∃ P1 P2 : List H, P = P1 ++ P2 ∧ P1 ≠ [] ∧ (∀ x ∈ P1, x ∈ cell K T0 k) ∧
          (∀ x ∈ P2, x ∉ cell K T0 k) := by
  intro l
  induction l with
  | nil =>
    intro k _
    obtain ⟨u0, hu0⟩ := hne0
    have hc : (k : H) * u0 ∈ cell K T0 k := ⟨u0, hu0, rfl⟩
    refine ⟨[(k : H) * u0], isPathL_singleton _, ?_, ?_, [(k : H) * u0], [], by simp, by simp,
      ?_, by simp⟩
    · intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact ⟨k, by simp, hc⟩
    · intro k' hk'; simp only [List.mem_singleton] at hk'; subst hk'; exact ⟨_, by simp, hc⟩
    · intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact hc
  | cons k' l ih =>
    intro k hl
    have hl' : IsPathL (cay (contractGen S K T0)) (k' :: l) := hl.suffix (List.suffix_cons _ _)
    have hadj : (cay (contractGen S K T0)).Adj k k' := (List.isChain_cons_cons.1 hl.1).1
    have hknot : k ∉ k' :: l := (List.nodup_cons.1 hl.2).1
    obtain ⟨P', hP', hPcell, hPcov, P1, P2, rfl, hP1ne, hP1, hP2⟩ := ih k' hl'
    obtain ⟨a, ha, b, hb, hab⟩ := contract_adj_lift hadj
    obtain ⟨h0, P1t, hP1eq⟩ := List.exists_cons_of_ne_nil hP1ne
    have hh0 : h0 ∈ P1 := by simp [hP1eq]
    obtain ⟨Q, hQ, hQh, hQl, hQs⟩ := (cell_reach hconn0 hb (hP1 h0 hh0)).exists_path
    obtain ⟨Qt, hQt, hQth, ⟨q, hqP, hQtl⟩, hQtsub, hQtonly⟩ :=
      hQ.exists_trunc hQh {x | x ∈ P1 ++ P2} ⟨h0, List.mem_of_getLast? hQl, by simp [hh0]⟩
    have hqcell : q ∈ cell K T0 k' := hQs q (hQtsub q (List.mem_of_getLast? hQtl))
    have hqP1 : q ∈ P1 := by
      rcases List.mem_append.1 hqP with h | h
      · exact h
      · exact absurd hqcell (hP2 q h)
    obtain ⟨A, B, hAB⟩ := List.mem_iff_append.1 hqP1
    have hsuf : IsPathL (cay S) (q :: (B ++ P2)) := hP'.suffix ⟨A, by rw [hAB]; simp⟩
    have hrestP : ∀ x ∈ B ++ P2, x ∈ P1 ++ P2 := by
      intro x hx; rw [hAB]; simp at hx ⊢; tauto
    have hcells : ∀ x ∈ Qt ++ (B ++ P2), ∃ k'' ∈ k' :: l, x ∈ cell K T0 k'' := by
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact ⟨k', by simp, hQs x (hQtsub x hx)⟩
      · exact hPcell x (hrestP x hx)
    have hnotk : ∀ x ∈ Qt ++ (B ++ P2), x ∉ cell K T0 k := by
      intro x hx hxk
      obtain ⟨k'', hk'', hx''⟩ := hcells x hx
      exact hknot (cell_unique hdist hxk hx'' ▸ hk'')
    have hQtne : Qt ≠ [] := by rintro rfl; simp at hQth
    refine ⟨a :: (Qt ++ (B ++ P2)), ⟨?_, ?_⟩, ?_, ?_, [a], Qt ++ (B ++ P2), rfl, by simp,
      by simpa using ha, hnotk⟩
    · rw [List.isChain_cons]
      refine ⟨?_, ?_⟩
      · intro y hy
        rw [List.head?_append_of_ne_nil _ hQtne, hQth] at hy
        simp only [Option.mem_def, Option.some.injEq] at hy
        subst hy; exact hab
      · rw [List.isChain_append]
        have := List.isChain_cons.1 hsuf.1
        refine ⟨hQt.1, this.2, ?_⟩
        intro x hx y hy
        rw [hQtl] at hx
        simp only [Option.mem_def, Option.some.injEq] at hx
        subst hx
        exact this.1 y hy
    · rw [List.nodup_cons, List.nodup_append]
      refine ⟨fun h => hnotk a h ha, hQt.2, (List.nodup_cons.1 hsuf.2).2, ?_⟩
      intro x hx y hy hxy
      subst hxy
      have := hQtonly x hx (hrestP x hy)
      rw [hQtl] at this
      simp only [Option.some.injEq] at this
      subst this
      exact (List.nodup_cons.1 hsuf.2).1 hy
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨k, by simp, ha⟩
      · obtain ⟨k'', hk'', hx''⟩ := hcells x hx
        exact ⟨k'', List.mem_cons_of_mem _ hk'', hx''⟩
    · intro k'' hk''
      rcases List.mem_cons.1 hk'' with rfl | hk''
      · exact ⟨a, by simp, ha⟩
      · by_cases hkk : k'' = k'
        · subst hkk
          exact ⟨q, by simp [List.mem_of_getLast? hQtl], hqcell⟩
        · obtain ⟨x, hx, hxc⟩ := hPcov k'' hk''
          refine ⟨x, ?_, hxc⟩
          have hxP2 : x ∈ P2 := by
            rcases List.mem_append.1 hx with h | h
            · exact absurd (cell_unique hdist hxc (hP1 x h)) hkk
            · exact h
          simp [hxP2]

/-- A path meeting all cells of a duplicate-free list of cells has at least as many
vertices. -/
lemma length_le_of_meets_cells (hdist : ∀ x ∈ T0, ∀ y ∈ T0, x * y⁻¹ ∈ K → x = y)
    {l : List K} (hl : l.Nodup) {P : List H} (hcov : ∀ k ∈ l, ∃ x ∈ P, x ∈ cell K T0 k) :
    l.length ≤ P.length := by
  choose! f hf hfc using hcov
  have hinj : Set.InjOn f {k | k ∈ l} := by
    intro k hk k' hk' h
    exact cell_unique hdist (hfc k hk) (h ▸ hfc k' hk')
  calc l.length = l.toFinset.card := (List.toFinset_card_of_nodup hl).symm
    _ = (l.toFinset.image f).card :=
        (Finset.card_image_of_injOn (fun k hk k' hk' h =>
          hinj (List.mem_toFinset.1 hk) (List.mem_toFinset.1 hk') h)).symm
    _ ≤ P.toFinset.card := Finset.card_le_card (by
        intro x hx
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
        exact List.mem_toFinset.2 (hf k (List.mem_toFinset.1 hk)))
    _ ≤ P.length := List.toFinset_card_le P

/-- The contracted graph is connected. -/
lemma contract_connected {Z : Set H} (hdist : ∀ x ∈ T0, ∀ y ∈ T0, x * y⁻¹ ∈ K → x = y)
    (hT0Z : T0 ⊆ Z) (hne0 : T0.Nonempty) (hcover : ∀ z ∈ Z, ∃ k : K, z ∈ cell K T0 k)
    (hconn : ∀ u ∈ Z, ∀ v ∈ Z, ReachIn (cay S) Z u v) (hZ : ∀ k ∈ K, ∀ z ∈ Z, k * z ∈ Z) :
    (cay (contractGen S K T0)).Connected := by
  obtain ⟨u0, hu0⟩ := hne0
  have key : ∀ k : K, (cay (contractGen S K T0)).Reachable 1 k := by
    intro k
    have hr := hconn u0 (hT0Z hu0) ((k : H) * u0) (hZ k k.2 u0 (hT0Z hu0))
    have := ReachIn.closed
      (Q := fun x => ∃ k' : K, x ∈ cell K T0 k' ∧ (cay (contractGen S K T0)).Reachable 1 k')
      ⟨1, ⟨u0, hu0, by simp⟩, SimpleGraph.Reachable.refl _⟩ ?_ hr
    · obtain ⟨k', hk', hr'⟩ := this
      rwa [cell_unique hdist hk' ⟨u0, hu0, rfl⟩] at hr'
    · rintro x y ⟨k', hk', hr'⟩ - hy hxy
      obtain ⟨k'', hk''⟩ := hcover y hy
      refine ⟨k'', hk'', ?_⟩
      by_cases hkk : k' = k''
      · exact hkk ▸ hr'
      · exact hr'.trans (cell_adj hk' hk'' hxy hkk).reachable
  rw [SimpleGraph.connected_iff]
  exact ⟨fun a b => (key a).symm.trans (key b), ⟨1⟩⟩

/-- A path meeting every cell is a rail with disjoint attachments from any `K`-orbit. -/
lemma rail_of_meets_all_cells {Z : Finset H} (hdist : ∀ x ∈ T0, ∀ y ∈ T0, x * y⁻¹ ∈ K → x = y)
    (hT0Z : T0 ⊆ Z) (hcover : ∀ z ∈ Z, ∃ k : K, z ∈ cell K T0 k)
    (hconn0 : ∀ u ∈ T0, ∀ v ∈ T0, ReachIn (cay S) T0 u v) (hZ : ∀ k ∈ K, ∀ z ∈ Z, k * z ∈ Z)
    {P : List H} (hP : IsPathL (cay S) P) (hPZ : ∀ x ∈ P, x ∈ Z)
    (hPcov : ∀ k : K, ∃ x ∈ P, x ∈ cell K T0 k) (y : H) :
    HasRail (cay S) Z (Z.filter (fun z => z * y⁻¹ ∈ K)) := by
  have hatt : ∀ t ∈ Z, ∃ a : List H, IsAttachment (cay S) Z P t a ∧
      ∃ k : K, t ∈ cell K T0 k ∧ ∀ x ∈ a, x ∈ cell K T0 k := by
    intro t ht
    obtain ⟨k, hk⟩ := hcover t ht
    obtain ⟨x, hxP, hxc⟩ := hPcov k
    obtain ⟨R, hR, hRh, hRl, hRs⟩ := (cell_reach hconn0 hk hxc).exists_path
    obtain ⟨a, ha, hah, hal, hasub, haonly⟩ :=
      hR.exists_trunc hRh {x | x ∈ P} ⟨x, List.mem_of_getLast? hRl, hxP⟩
    refine ⟨a, ⟨ha, hah, hal, fun z hz => cell_subset (Z := (Z : Set H)) hZ hT0Z k
      (hRs z (hasub z hz)), haonly⟩, k, hk, fun z hz => hRs z (hasub z hz)⟩
  choose! att hattA k hk hkc using hatt
  refine ⟨P, hP, hPZ, att, fun t ht => hattA t (Finset.mem_filter.1 ht).1, ?_⟩
  intro t ht t' ht' htt' x hx hx'
  have ht1 := Finset.mem_filter.1 ht
  have ht1' := Finset.mem_filter.1 ht'
  have hkk := cell_unique hdist (hkc t ht1.1 x hx) (hkc t' ht1'.1 x hx')
  apply htt'
  refine cell_orbit_unique hdist (hk t ht1.1) (hkk ▸ hk t' ht1'.1) ?_
  have := K.mul_mem ht1.2 (K.inv_mem ht1'.2)
  simpa [mul_assoc] using this

end

/-- Existence of a connected set `T0 ⊆ Z` meeting every `K`-orbit of `Z` exactly once. -/
lemma exists_orbit_transversal [Finite H] (S : Set H) (K : Subgroup H) (Z : Finset H)
    (hZ : ∀ k ∈ K, ∀ z ∈ Z, k * z ∈ Z) (hconn : ∀ u ∈ Z, ∀ v ∈ Z, ReachIn (cay S) Z u v)
    (hne : Z.Nonempty) :
    ∃ T0 : Finset H, T0.Nonempty ∧ (T0 : Set H) ⊆ Z ∧
      (∀ x ∈ T0, ∀ y ∈ T0, x * y⁻¹ ∈ K → x = y) ∧
      (∀ u ∈ T0, ∀ v ∈ T0, ReachIn (cay S) T0 u v) ∧
      (∀ z ∈ Z, ∃ k : K, z ∈ cell K (T0 : Set H) k) := by
  let good : Finset H → Prop := fun T0 => T0.Nonempty ∧
    (∀ x ∈ T0, ∀ y ∈ T0, x * y⁻¹ ∈ K → x = y) ∧ (∀ u ∈ T0, ∀ v ∈ T0, ReachIn (cay S) T0 u v)
  obtain ⟨z0, hz0⟩ := hne
  have hgood : (Z.powerset.filter good).Nonempty := by
    refine ⟨{z0}, Finset.mem_filter.2 ⟨by simpa using hz0, ⟨z0, by simp⟩, ?_, ?_⟩⟩
    · intro x hx y hy _; simp at hx hy; rw [hx, hy]
    · intro u hu v hv; simp at hu hv; subst hu hv; exact ReachIn.refl (by simp)
  obtain ⟨T0, hT0mem, hmax⟩ := Finset.exists_max_image _ Finset.card hgood
  have hT0mem' := Finset.mem_filter.1 hT0mem
  have hT0Z := Finset.mem_powerset.1 hT0mem'.1
  obtain ⟨hT0ne, hdist, hconn0⟩ := hT0mem'.2
  refine ⟨T0, hT0ne, fun x hx => hT0Z hx, hdist, hconn0, ?_⟩
  intro w hw
  by_contra hnot
  push_neg at hnot
  obtain ⟨u0, hu0⟩ := hT0ne
  have hQ : ∃ a b : H, a ∈ Z ∧ b ∈ Z ∧ (cay S).Adj a b ∧ (∃ k : K, a ∈ cell K T0 k) ∧
      ∀ k : K, b ∉ cell K T0 k := by
    by_contra hno
    push_neg at hno
    have := ReachIn.closed (Q := fun x => ∃ k : K, x ∈ cell K (T0 : Set H) k)
      ⟨1, u0, hu0, by simp⟩ (fun a b ha haZ hbZ hab => hno a b haZ hbZ hab ha)
      (hconn u0 (hT0Z hu0) w hw)
    obtain ⟨k, hk⟩ := this
    exact hnot k hk
  obtain ⟨a, b, -, hbZ, hab, ⟨k, u, hu, rfl⟩, hb⟩ := hQ
  set b' := (k : H)⁻¹ * b with hb'
  have hb'Z : b' ∈ Z := hZ _ (K.inv_mem k.2) b hbZ
  have hub' : (cay S).Adj u b' := by
    have := (cay_adj_mul_left (S := S) ((k : H)⁻¹)).2 hab
    simpa [hb'] using this
  have hb'orb : ∀ x ∈ T0, b' * x⁻¹ ∉ K := by
    intro x hx hK
    apply hb (k * ⟨b' * x⁻¹, hK⟩)
    refine ⟨x, hx, ?_⟩
    simp [hb', mul_assoc]
  have hb'T0 : b' ∉ T0 := fun h => hb'orb b' h (by simp [K.one_mem])
  have hT1 : insert b' T0 ∈ Z.powerset.filter good := by
    refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.insert_subset hb'Z hT0Z),
      ⟨b', by simp⟩, ?_, ?_⟩
    · intro x hx y hy hxy
      rw [Finset.mem_insert] at hx hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · rfl
      · exact absurd hxy (hb'orb y hy)
      · exact absurd (by simpa using K.inv_mem hxy) (hb'orb x hx)
      · exact hdist x hx y hy hxy
    · have hsub : (T0 : Set H) ⊆ (insert b' T0 : Finset H) := by
        intro x hx; simp [Finset.mem_coe.1 hx]
      have hto : ∀ v ∈ insert b' T0, ReachIn (cay S) (insert b' T0 : Finset H) u v := by
        intro v hv
        rcases Finset.mem_insert.1 hv with rfl | hv
        · exact (ReachIn.refl (by simp [hu])).tail hub' (by simp)
        · exact (hconn0 u hu v hv).mono le_rfl hsub
      intro x hx y hy
      exact (hto x hx).symm.trans (hto y hy)
  have := hmax _ hT1
  rw [Finset.card_insert_of_notMem hb'T0] at this
  omega

end Lovasz
