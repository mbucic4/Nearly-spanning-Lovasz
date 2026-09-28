module
public import RequestProject.VTBasic
public import RequestProject.Main

/-!
# Semiregular contraction (Lemma A.3 and Corollary A.4)

A finite group `K` acts semiregularly (freely) by automorphisms on a finite connected graph
`Y`.  We choose a connected set `T0` meeting every `K`-orbit exactly once; its translates
`k • T0` (the *cells*) partition the vertex set, and contracting them gives the Cayley graph
`cay (acontractGen Y T0)` of `K`.  Paths of the contracted graph lift to paths of `Y` of at least
the same order.
-/

@[expose] public section


open Classical

namespace Lovasz

variable {Q K : Type*} [Group K] [MulAction K Q]

/-- The cell `k • T0`. -/
def acell (T0 : Set Q) (k : K) : Set Q := (k • ·) '' T0

/-- The generating set of the contracted Cayley graph. -/
def acontractGen (Y : SimpleGraph Q) (T0 : Set Q) : Set K :=
  {k | ∃ u ∈ T0, ∃ v ∈ T0, Y.Adj u (k • v)}

/-- The action is free (semiregular). -/
def FreeAct (K Q : Type*) [Group K] [MulAction K Q] : Prop := ∀ (k : K) (y : Q), k • y = y → k = 1

section

variable {Y : SimpleGraph Q} {T0 : Set Q}

lemma acell_unique (hfree : FreeAct K Q)
    (hdist : ∀ x ∈ T0, ∀ y ∈ T0, ∀ k : K, k • y = x → x = y) {k k' : K} {x : Q}
    (hk : x ∈ acell T0 k) (hk' : x ∈ acell T0 k') : k = k' := by
  obtain ⟨u, hu, rfl⟩ := hk
  obtain ⟨v, hv, hv'⟩ := hk'
  simp only at hv'
  have hvu : v = u := hdist v hv u hu (k'⁻¹ * k) (by rw [mul_smul, ← hv', inv_smul_smul])
  subst hvu
  have := hfree (k'⁻¹ * k) v (by rw [mul_smul, ← hv', inv_smul_smul])
  rw [inv_mul_eq_one] at this
  exact this.symm

lemma acell_reach (hY : ActsOn Y K) (hconn0 : ∀ u ∈ T0, ∀ v ∈ T0, ReachIn Y T0 u v) {k : K}
    {x y : Q} (hx : x ∈ acell T0 k) (hy : y ∈ acell T0 k) : ReachIn Y (acell T0 k) x y := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  exact (hconn0 u hu v hv).map_smul hY k

lemma acell_adj (hY : ActsOn Y K) {k k' : K} {x y : Q} (hx : x ∈ acell T0 k)
    (hy : y ∈ acell T0 k') (hxy : Y.Adj x y) (hkk' : k ≠ k') :
    (cay (acontractGen Y T0)).Adj k k' := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  rw [cay_adj]
  refine ⟨hkk', Or.inl ⟨u, hu, v, hv, ?_⟩⟩
  have := hY k⁻¹ _ _ hxy
  simpa [mul_smul] using this

lemma acontract_adj_lift (hY : ActsOn Y K) {k k' : K} (h : (cay (acontractGen Y T0)).Adj k k') :
    ∃ x ∈ acell T0 k, ∃ y ∈ acell T0 k', Y.Adj x y := by
  rw [cay_adj] at h
  obtain ⟨-, h | h⟩ := h
  · obtain ⟨u, hu, v, hv, huv⟩ := h
    refine ⟨k • u, ⟨u, hu, rfl⟩, k' • v, ⟨v, hv, rfl⟩, ?_⟩
    have := hY k _ _ huv
    simpa [← mul_smul] using this
  · obtain ⟨u, hu, v, hv, huv⟩ := h
    refine ⟨k • v, ⟨v, hv, rfl⟩, k' • u, ⟨u, hu, rfl⟩, ?_⟩
    have := hY k' _ _ huv
    simpa [← mul_smul] using this.symm

/-- Lifting paths of the contracted graph (as in Lemma 3.11). -/
lemma lift_acontract_path (hY : ActsOn Y K) (hfree : FreeAct K Q)
    (hdist : ∀ x ∈ T0, ∀ y ∈ T0, ∀ k : K, k • y = x → x = y)
    (hne0 : T0.Nonempty) (hconn0 : ∀ u ∈ T0, ∀ v ∈ T0, ReachIn Y T0 u v) :
    ∀ (l : List K) (k : K), IsPathL (cay (acontractGen Y T0)) (k :: l) →
      ∃ P : List Q, IsPathL Y P ∧ (∀ x ∈ P, ∃ k' ∈ k :: l, x ∈ acell T0 k') ∧
        (∀ k' ∈ k :: l, ∃ x ∈ P, x ∈ acell T0 k') ∧
        ∃ P1 P2 : List Q, P = P1 ++ P2 ∧ P1 ≠ [] ∧ (∀ x ∈ P1, x ∈ acell T0 k) ∧
          (∀ x ∈ P2, x ∉ acell T0 k) := by
  intro l
  induction l with
  | nil =>
    intro k _
    obtain ⟨u0, hu0⟩ := hne0
    have hc : k • u0 ∈ acell T0 k := ⟨u0, hu0, rfl⟩
    refine ⟨[k • u0], isPathL_singleton _, ?_, ?_, [k • u0], [], by simp, by simp,
      ?_, by simp⟩
    · intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact ⟨k, by simp, hc⟩
    · intro k' hk'; simp only [List.mem_singleton] at hk'; subst hk'; exact ⟨_, by simp, hc⟩
    · intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact hc
  | cons k' l ih =>
    intro k hl
    have hl' : IsPathL (cay (acontractGen Y T0)) (k' :: l) := hl.suffix (List.suffix_cons _ _)
    have hadj : (cay (acontractGen Y T0)).Adj k k' := (List.isChain_cons_cons.1 hl.1).1
    have hknot : k ∉ k' :: l := (List.nodup_cons.1 hl.2).1
    obtain ⟨P', hP', hPcell, hPcov, P1, P2, rfl, hP1ne, hP1, hP2⟩ := ih k' hl'
    obtain ⟨a, ha, b, hb, hab⟩ := acontract_adj_lift hY hadj
    obtain ⟨h0, P1t, hP1eq⟩ := List.exists_cons_of_ne_nil hP1ne
    have hh0 : h0 ∈ P1 := by simp [hP1eq]
    obtain ⟨R, hR, hRh, hRl, hRs⟩ := (acell_reach hY hconn0 hb (hP1 h0 hh0)).exists_path
    obtain ⟨Qt, hQt, hQth, ⟨q, hqP, hQtl⟩, hQtsub, hQtonly⟩ :=
      hR.exists_trunc hRh {x | x ∈ P1 ++ P2} ⟨h0, List.mem_of_getLast? hRl, by simp [hh0]⟩
    have hqcell : q ∈ acell T0 k' := hRs q (hQtsub q (List.mem_of_getLast? hQtl))
    have hqP1 : q ∈ P1 := by
      rcases List.mem_append.1 hqP with h | h
      · exact h
      · exact absurd hqcell (hP2 q h)
    obtain ⟨A, B, hAB⟩ := List.mem_iff_append.1 hqP1
    have hsuf : IsPathL Y (q :: (B ++ P2)) := hP'.suffix ⟨A, by rw [hAB]; simp⟩
    have hrestP : ∀ x ∈ B ++ P2, x ∈ P1 ++ P2 := by
      intro x hx; rw [hAB]; simp at hx ⊢; tauto
    have hcells : ∀ x ∈ Qt ++ (B ++ P2), ∃ k'' ∈ k' :: l, x ∈ acell T0 k'' := by
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact ⟨k', by simp, hRs x (hQtsub x hx)⟩
      · exact hPcell x (hrestP x hx)
    have hnotk : ∀ x ∈ Qt ++ (B ++ P2), x ∉ acell T0 k := by
      intro x hx hxk
      obtain ⟨k'', hk'', hx''⟩ := hcells x hx
      exact hknot (acell_unique hfree hdist hxk hx'' ▸ hk'')
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
            · exact absurd (acell_unique hfree hdist hxc (hP1 x h)) hkk
            · exact h
          simp [hxP2]

/-- A path meeting all cells of a duplicate-free list of cells has at least as many
vertices. -/
lemma length_le_of_meets_acells (hfree : FreeAct K Q)
    (hdist : ∀ x ∈ T0, ∀ y ∈ T0, ∀ k : K, k • y = x → x = y)
    {l : List K} (hl : l.Nodup) {P : List Q} (hcov : ∀ k ∈ l, ∃ x ∈ P, x ∈ acell T0 k) :
    l.length ≤ P.length := by
  by_cases hl0 : l = []
  · simp [hl0]
  obtain ⟨k0, hk0⟩ := List.exists_mem_of_ne_nil l hl0
  haveI : Nonempty Q := ⟨(hcov k0 hk0).choose⟩
  choose! f hf hfc using hcov
  have hinj : Set.InjOn f {k | k ∈ l} := by
    intro k hk k' hk' h
    exact acell_unique hfree hdist (hfc k hk) (h ▸ hfc k' hk')
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
lemma acontract_connected (hY : ActsOn Y K) (hfree : FreeAct K Q)
    (hdist : ∀ x ∈ T0, ∀ y ∈ T0, ∀ k : K, k • y = x → x = y)
    (hne0 : T0.Nonempty) (hcover : ∀ z : Q, ∃ k : K, z ∈ acell T0 k) (hconn : Y.Connected) :
    (cay (acontractGen (K := K) Y T0)).Connected := by
  obtain ⟨u0, hu0⟩ := hne0
  have key : ∀ k : K, (cay (acontractGen Y T0)).Reachable 1 k := by
    intro k
    have hr := reachIn_univ_of_reachable (hconn.preconnected u0 (k • u0))
    have := ReachIn.closed
      (Q := fun x => ∃ k' : K, x ∈ acell T0 k' ∧ (cay (acontractGen Y T0)).Reachable 1 k')
      ⟨1, ⟨u0, hu0, by simp⟩, SimpleGraph.Reachable.refl _⟩ ?_ hr
    · obtain ⟨k', hk', hr'⟩ := this
      rwa [acell_unique hfree hdist hk' ⟨u0, hu0, rfl⟩] at hr'
    · rintro x y ⟨k', hk', hr'⟩ - - hxy
      obtain ⟨k'', hk''⟩ := hcover y
      refine ⟨k'', hk'', ?_⟩
      by_cases hkk : k' = k''
      · exact hkk ▸ hr'
      · exact hr'.trans (acell_adj hY hk' hk'' hxy hkk).reachable
  rw [SimpleGraph.connected_iff]
  exact ⟨fun a b => (key a).symm.trans (key b), ⟨1⟩⟩

end

/-- Existence of a connected set `T0` meeting every `K`-orbit exactly once. -/
lemma exists_aorbit_transversal [Fintype Q] (Y : SimpleGraph Q) (hY : ActsOn Y K)
    (hconn : Y.Connected) :
    ∃ T0 : Finset Q, T0.Nonempty ∧
      (∀ x ∈ T0, ∀ y ∈ T0, ∀ k : K, k • y = x → x = y) ∧
      (∀ u ∈ T0, ∀ v ∈ T0, ReachIn Y T0 u v) ∧
      (∀ z : Q, ∃ k : K, z ∈ acell (T0 : Set Q) k) := by
  let good : Finset Q → Prop := fun T0 => T0.Nonempty ∧
    (∀ x ∈ T0, ∀ y ∈ T0, ∀ k : K, k • y = x → x = y) ∧ (∀ u ∈ T0, ∀ v ∈ T0, ReachIn Y T0 u v)
  obtain ⟨z0⟩ := hconn.nonempty
  have hgood : (Finset.univ.powerset.filter good).Nonempty := by
    refine ⟨{z0}, Finset.mem_filter.2 ⟨by simp, ⟨z0, by simp⟩, ?_, ?_⟩⟩
    · intro x hx y hy _ _; simp at hx hy; rw [hx, hy]
    · intro u hu v hv; simp at hu hv; subst hu hv; exact ReachIn.refl (by simp)
  obtain ⟨T0, hT0mem, hmax⟩ := Finset.exists_max_image _ Finset.card hgood
  obtain ⟨hT0ne, hdist, hconn0⟩ := (Finset.mem_filter.1 hT0mem).2
  refine ⟨T0, hT0ne, hdist, hconn0, ?_⟩
  intro w
  by_contra hnot
  push_neg at hnot
  obtain ⟨u0, hu0⟩ := hT0ne
  have hQ : ∃ a b : Q, Y.Adj a b ∧ (∃ k : K, a ∈ acell (T0 : Set Q) k) ∧
      ∀ k : K, b ∉ acell (T0 : Set Q) k := by
    by_contra hno
    push_neg at hno
    have := ReachIn.closed (Q := fun x => ∃ k : K, x ∈ acell (T0 : Set Q) k)
      ⟨1, u0, hu0, by simp⟩ (fun a b ha _ _ hab => hno a b hab ha)
      (reachIn_univ_of_reachable (hconn.preconnected u0 w))
    obtain ⟨k, hk⟩ := this
    exact hnot k hk
  obtain ⟨a, b, hab, ⟨k, u, hu, rfl⟩, hb⟩ := hQ
  set b' := k⁻¹ • b with hb'
  have hub' : Y.Adj u b' := by
    have := hY k⁻¹ _ _ hab
    simpa [hb'] using this
  have hb'orb : ∀ x ∈ T0, ∀ g : K, g • x ≠ b' := by
    intro x hx g hg
    apply hb (k * g)
    exact ⟨x, hx, by simp only; rw [mul_smul, hg, hb', smul_inv_smul]⟩
  have hb'T0 : b' ∉ T0 := fun h => hb'orb b' h 1 (one_smul _ _)
  have hT1 : insert b' T0 ∈ Finset.univ.powerset.filter good := by
    refine Finset.mem_filter.2 ⟨by simp, ⟨b', by simp⟩, ?_, ?_⟩
    · intro x hx y hy g hxy
      rw [Finset.mem_insert] at hx hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · rfl
      · exact absurd hxy (hb'orb y hy g)
      · exact absurd (by rw [← hxy, inv_smul_smul]) (hb'orb x hx g⁻¹)
      · exact hdist x hx y hy g hxy
    · have hsub : (T0 : Set Q) ⊆ (insert b' T0 : Finset Q) := by
        intro x hx; simp [Finset.mem_coe.1 hx]
      have hto : ∀ v ∈ insert b' T0, ReachIn Y (insert b' T0 : Finset Q) u v := by
        intro v hv
        rcases Finset.mem_insert.1 hv with rfl | hv
        · exact (ReachIn.refl (by simp [hu])).tail hub' (by simp)
        · exact (hconn0 u hu v hv).mono le_rfl hsub
      intro x hx y hy
      exact (hto x hx).symm.trans (hto y hy)
  have := hmax _ hT1
  rw [Finset.card_insert_of_notMem hb'T0] at this
  omega

/-- **Lemma A.3** (semiregular contraction). If a finite group `K` acts semiregularly by
automorphisms on a finite connected graph `Y`, there is a connected Cayley graph `C` of `K`
with `p(C) ≤ p(Y)`; moreover `|V(Y)| = |K| · t`, where `t` is the size of a set meeting
every `K`-orbit exactly once. -/
theorem semiregular_contraction [Fintype Q] [Fintype K] (Y : SimpleGraph Q) (hY : ActsOn Y K)
    (hfree : FreeAct K Q) (hconn : Y.Connected) :
    ∃ S : Set K, (cay S).Connected ∧ pathOrder (cay S) ≤ pathOrder Y ∧
      ∃ T0 : Finset Q, Fintype.card Q = Fintype.card K * T0.card ∧
        ∀ x ∈ T0, ∀ y ∈ T0, ∀ k : K, k • y = x → x = y := by
  obtain ⟨T0, hne0, hdist, hconn0, hcover⟩ := exists_aorbit_transversal Y hY hconn
  refine ⟨acontractGen Y T0, acontract_connected hY hfree hdist hne0 hcover hconn, ?_,
    T0, ?_, hdist⟩
  · obtain ⟨l, hl, hlen⟩ := exists_isPathL_length_eq_pathOrder (cay (acontractGen (K := K) Y T0))
    rw [← hlen]
    cases l with
    | nil => exact Nat.zero_le _
    | cons k l =>
      obtain ⟨P, hP, -, hPcov, -⟩ := lift_acontract_path hY hfree hdist hne0 hconn0 l k hl
      exact (length_le_of_meets_acells hfree hdist hl.2 hPcov).trans hP.length_le_pathOrder
  · have hbij : Function.Bijective (fun p : K × {x // x ∈ T0} => p.1 • (p.2 : Q)) := by
      constructor
      · rintro ⟨k, t, ht⟩ ⟨k', t', ht'⟩ h
        simp only at h
        have htt : t' = t := hdist t' ht' t ht (k'⁻¹ * k) (by rw [mul_smul, h, inv_smul_smul])
        subst htt
        have := hfree (k'⁻¹ * k) t' (by rw [mul_smul, h, inv_smul_smul])
        rw [inv_mul_eq_one] at this
        subst this; rfl
      · intro z
        obtain ⟨k, t, ht, rfl⟩ := hcover z
        exact ⟨(k, ⟨t, ht⟩), rfl⟩
    rw [← Fintype.card_of_bijective hbij, Fintype.card_prod, Fintype.card_coe]

/-- **Corollary A.4.** Assume the Cayley bound (Theorem 3.17).  For `0 < η < 1` and `k ≥ 1`
there is `b > 0` such that every finite connected graph `Y` admitting a semiregular action by
automorphisms with at most `k` vertex-orbits (i.e. with a set of at most `k` vertices meeting
every orbit) satisfies `p(Y) ≥ b |V(Y)|^(1-η)`. -/
theorem semiregular_path_bound
    (hC : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (H : Type) [Group H] [Finite H] (S : Set H),
      (cay S).Connected → n₀ ≤ Nat.card H →
      ∃ l : List H, IsPathL (cay S) l ∧ (Nat.card H : ℝ) ^ (1 - ε) ≤ (l.length : ℝ) - 1)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (k : ℕ) (hk : 1 ≤ k) :
    ∃ b : ℝ, 0 < b ∧ ∀ (Q K : Type) [Fintype Q] [Group K] [Fintype K] [MulAction K Q]
      (Y : SimpleGraph Q), ActsOn Y K → FreeAct K Q → Y.Connected →
      ∀ F : Finset Q, F.card ≤ k → (∀ y : Q, ∃ f ∈ F, ∃ g : K, g • f = y) →
      b * (Fintype.card Q : ℝ) ^ (1 - η) ≤ pathOrder Y := by
  obtain ⟨n0, hn0⟩ := hC η hη0
  set n1 := max n0 1 with hn1
  have hn1pos : (0 : ℝ) < n1 := by exact_mod_cast (lt_of_lt_of_le one_pos (le_max_right n0 1))
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨1 / n1 / k, by positivity, ?_⟩
  intro Q K _ _ _ _ Y hY hfree hconn F hF hcov
  obtain ⟨S, hSconn, hSp, T0, hcard, hdist⟩ := semiregular_contraction Y hY hfree hconn
  -- `|T0| ≤ |F| ≤ k`
  have hT0 : T0.card ≤ k := by
    refine le_trans ?_ hF
    have hch : ∀ t ∈ T0, ∃ f ∈ F, ∃ g : K, g • f = t := fun t _ => hcov t
    choose! φ hφF g hg using hch
    refine Finset.card_le_card_of_injOn φ (fun t ht => hφF t ht) ?_
    intro t ht t' ht' h
    have e : t = (g t * (g t')⁻¹) • t' := by
      have h1 : (g t')⁻¹ • t' = φ t' := by rw [inv_smul_eq_iff]; exact (hg t' ht').symm
      rw [mul_smul, h1, ← h, hg t ht]
    exact hdist t ht t' ht' _ e.symm
  -- the Cayley bound for `K`
  have hK1 : (1 : ℝ) ≤ Fintype.card K := by exact_mod_cast Fintype.card_pos
  have hpC : (1 / n1 : ℝ) * (Fintype.card K : ℝ) ^ (1 - η) ≤ pathOrder (cay S) := by
    have hp1 : (1 : ℝ) ≤ pathOrder (cay S) := by exact_mod_cast one_le_pathOrder (cay S)
    by_cases hbig : n0 ≤ Fintype.card K
    · obtain ⟨l, hl, hlen⟩ := hn0 K S hSconn (by rwa [Nat.card_eq_fintype_card])
      rw [Nat.card_eq_fintype_card] at hlen
      have := hl.length_le_pathOrder
      have hl' : (l.length : ℝ) ≤ pathOrder (cay S) := by exact_mod_cast this
      have ha : (1 / n1 : ℝ) ≤ 1 := by
        rw [div_le_one hn1pos]; exact_mod_cast le_max_right n0 1
      have := Real.rpow_nonneg (by linarith : (0:ℝ) ≤ Fintype.card K) (1 - η)
      nlinarith
    · push_neg at hbig
      have h1 : (Fintype.card K : ℝ) ^ (1 - η) ≤ Fintype.card K := by
        calc (Fintype.card K : ℝ) ^ (1 - η) ≤ (Fintype.card K : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hK1 (by linarith)
          _ = _ := Real.rpow_one _
      have h2 : (Fintype.card K : ℝ) ≤ n1 := by
        have : Fintype.card K ≤ n1 := le_trans hbig.le (le_max_left _ _)
        exact_mod_cast this
      calc (1 / n1 : ℝ) * (Fintype.card K : ℝ) ^ (1 - η) ≤ (1 / n1) * n1 := by gcongr; linarith
        _ = 1 := by field_simp
        _ ≤ _ := hp1
  have hS' : (pathOrder (cay S) : ℝ) ≤ pathOrder Y := by exact_mod_cast hSp
  refine le_trans ?_ (hpC.trans hS')
  rw [hcard]
  push_cast
  have hT0r : (T0.card : ℝ) ≤ k := by exact_mod_cast hT0
  have hK0 : (0 : ℝ) ≤ Fintype.card K := by positivity
  have hQ : ((Fintype.card K : ℝ) * T0.card) ^ (1 - η) ≤ (Fintype.card K : ℝ) ^ (1 - η) * k := by
    rw [Real.mul_rpow hK0 (by positivity)]
    gcongr
    calc (T0.card : ℝ) ^ (1 - η) ≤ (k : ℝ) ^ (1 - η) :=
          Real.rpow_le_rpow (by positivity) hT0r (by linarith)
      _ ≤ (k : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hk) (by linarith)
      _ = k := Real.rpow_one _
  calc 1 / n1 / k * ((Fintype.card K : ℝ) * T0.card) ^ (1 - η)
      ≤ 1 / n1 / k * ((Fintype.card K : ℝ) ^ (1 - η) * k) := by gcongr
    _ = 1 / n1 * (Fintype.card K : ℝ) ^ (1 - η) := by field_simp

end Lovasz
