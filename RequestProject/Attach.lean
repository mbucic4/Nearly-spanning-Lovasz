module
public import RequestProject.Menger
public import RequestProject.Balanced

/-!
# A rail with many attachments (Lemmas 3.5 and 3.6)

Throughout, `N ≤ H` acts on `H` by left multiplication, `Z` is an `N`-invariant set of
vertices of `cay S`, and any two vertices of `Z` are joined by a walk inside `Z` with at most
`L` edges.  The `N`-orbit of `x` is `{y | y * x⁻¹ ∈ N}`.
-/

@[expose] public section


open Classical

namespace Lovasz

lemma greedy_subset {α : Type*} (g : Finset α → ℕ) (θ c : ℕ) (Y : Finset α) (h0 : g ∅ < θ)
    (hstep : ∀ b ∈ Y, ∀ X, g (insert b X) < g X + c) (hY : θ ≤ g Y) :
    ∃ X ⊆ Y, θ ≤ g X ∧ g X < θ + c := by
  induction Y using Finset.induction_on with
  | empty => exact absurd hY (not_le.2 h0)
  | insert b Y hb ih =>
    by_cases hθ : θ ≤ g Y
    · obtain ⟨X, hX, h1, h2⟩ := ih (fun b' hb' X => hstep b' (Finset.mem_insert_of_mem hb') X) hθ
      exact ⟨X, hX.trans (Finset.subset_insert _ _), h1, h2⟩
    · have := hstep b (Finset.mem_insert_self _ _) Y
      exact ⟨insert b Y, subset_rfl, hY, by omega⟩

lemma chain_mem_of_head {V : Type*} {G : SimpleGraph V} {Z : Set V}
    (hZ : ∀ u v, G.Adj u v → v ∈ Z) :
    ∀ (l : List V) (a : V), l.IsChain G.Adj → l.head? = some a → a ∈ Z → ∀ v ∈ l, v ∈ Z := by
  intro l
  induction l with
  | nil => intro a _ h; simp at h
  | cons b l ih =>
    intro a hch hh ha v hv
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    rcases List.mem_cons.1 hv with rfl | hv
    · exact ha
    · cases l with
      | nil => simp at hv
      | cons c l =>
        have h := List.isChain_cons_cons.1 hch
        exact ih c h.2 rfl (hZ _ _ h.1) v hv

/-- Disjoint paths from `A` to a path `P` give a rail. -/
lemma rail_of_disjPaths {V : Type*} {G G' : SimpleGraph V} (hG : G' ≤ G) {Z : Set V}
    (hZ : ∀ u v, G'.Adj u v → v ∈ Z) {A : Set V} (hA : A ⊆ Z) {P : List V} (hP : IsPathL G P)
    (hPZ : ∀ v ∈ P, v ∈ Z) {k : ℕ} {p : Fin k → List V}
    (h : DisjPaths G' A {v | v ∈ P} k p) :
    ∃ T : Finset V, (∀ t ∈ T, t ∈ A) ∧ T.card = k ∧ IsRail G Z T P := by
  obtain ⟨hpP, hpA, hpB, hpA', hpB', hpD⟩ := h
  choose hd hdA hhd using hpA
  have hdinj : Function.Injective hd := by
    intro i j hij
    by_contra hne
    exact hpD i j hne (List.mem_of_head? (hhd i)) (hij ▸ List.mem_of_head? (hhd j))
  refine ⟨Finset.univ.image hd, ?_, ?_, hP, hPZ, fun t => if h : ∃ i, hd i = t then
    p h.choose else [], ?_, ?_⟩
  · intro t ht
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ht
    exact hdA i
  · rw [Finset.card_image_of_injective _ hdinj, Finset.card_univ, Fintype.card_fin]
  · intro t ht
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ht
    have hex : ∃ j, hd j = hd i := ⟨i, rfl⟩
    have hj : hex.choose = i := hdinj hex.choose_spec
    simp only [dif_pos hex, hj]
    obtain ⟨b, hb, hbl⟩ := hpB i
    exact ⟨(hpP i).mono hG, hhd i, ⟨b, hb, hbl⟩,
      chain_mem_of_head hZ _ _ (hpP i).1 (hhd i) (hA (hdA i)), fun z hz hzP => hpB' i z hz hzP⟩
  · intro t ht t' ht' hne
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 ht'
    have hex : ∃ i', hd i' = hd i := ⟨i, rfl⟩
    have hex' : ∃ j', hd j' = hd j := ⟨j, rfl⟩
    simp only [dif_pos hex, dif_pos hex', hdinj hex.choose_spec, hdinj hex'.choose_spec]
    exact hpD i j (fun h => hne (by rw [h]))

variable {H : Type*} [Group H]

/-- A walk from `U` to `D` inside a separated set meets the separator. -/
lemma walk_meets_separator {S : Set H} {Z U S₀ D : Finset H}
    (hcover : ∀ z ∈ Z, z ∈ U ∨ z ∈ S₀ ∨ z ∈ D) (hUD : Disjoint U D)
    (hnoedge : ∀ u ∈ U, ∀ d ∈ D, ¬ (cay S).Adj u d) :
    ∀ (l : List H) (u : H), (u :: l).IsChain (cay S).Adj → (∀ z ∈ u :: l, z ∈ Z) → u ∈ U →
      (∃ d ∈ u :: l, d ∈ D) → ∃ s ∈ u :: l, s ∈ S₀ := by
  intro l
  induction l with
  | nil =>
    intro u _ _ hu ⟨d, hd, hdD⟩
    simp only [List.mem_singleton] at hd
    subst hd
    exact absurd hdD (Finset.disjoint_left.1 hUD hu)
  | cons b l ih =>
    intro u hch hZ hu ⟨d, hd, hdD⟩
    have hub := (List.isChain_cons_cons.1 hch).1
    rcases hcover b (hZ b (by simp)) with hb | hb | hb
    · have hd' : ∃ d ∈ b :: l, d ∈ D := by
        rcases List.mem_cons.1 hd with rfl | hd
        · exact absurd hdD (Finset.disjoint_left.1 hUD hu)
        · exact ⟨d, hd, hdD⟩
      obtain ⟨s, hs, hsS⟩ := ih b (List.isChain_cons_cons.1 hch).2
        (fun z hz => hZ z (List.mem_cons_of_mem _ hz)) hb hd'
      exact ⟨s, List.mem_cons_of_mem _ hs, hsS⟩
    · exact ⟨b, by simp, hb⟩
    · exact absurd hub (hnoedge u hu b hb)

/-- **Lemma 3.5** (routing inequality). If `(U, S₀, D)` is a separation of `Z` (the three
sets cover `Z`, `U` and `D` are disjoint and there is no edge between them) and `B` is the
`N`-orbit of `x ∈ Z`, then `|U ∩ B| |D ∩ B| ≤ m (L + 1) |S₀|`. -/
theorem separation_ineq [Finite H] (S : Set H) (N : Subgroup H) (Z : Finset H) (L : ℕ)
    (hL : ∀ u ∈ Z, ∀ v ∈ Z, WalkLe (cay S) Z u v L) (x : H) (hx : x ∈ Z)
    (hZ : ∀ n ∈ N, ∀ z ∈ Z, n * z ∈ Z)
    (U S₀ D : Finset H) (hcover : ∀ z ∈ Z, z ∈ U ∨ z ∈ S₀ ∨ z ∈ D) (hUD : Disjoint U D)
    (hnoedge : ∀ u ∈ U, ∀ d ∈ D, ¬ (cay S).Adj u d) :
    (U.filter (fun y => y * x⁻¹ ∈ N)).card * (D.filter (fun y => y * x⁻¹ ∈ N)).card ≤
      Nat.card N * (L + 1) * S₀.card := by
  have := Fintype.ofFinite N
  have hγ : ∀ t : N, ∃ γ : List H, γ.IsChain (cay S).Adj ∧ γ.head? = some x ∧
      γ.getLast? = some ((t : H) * x) ∧ (∀ z ∈ γ, z ∈ Z) ∧ γ.length ≤ L + 1 :=
    fun t => hL x hx _ (hZ t t.2 x hx)
  choose γ hγc hγh hγl hγZ hγlen using hγ
  set BU := U.filter (fun y => y * x⁻¹ ∈ N) with hBU
  set BD := D.filter (fun y => y * x⁻¹ ∈ N) with hBD
  let Bad : Finset (N × N) :=
    Finset.univ.filter (fun p => ∃ s ∈ S₀, s ∈ (γ p.2).map ((p.1 : H) * ·))
  let φ : H × H → N × N := fun p =>
    if h : p.1 * x⁻¹ ∈ N ∧ p.2 * x⁻¹ ∈ N then
      (⟨p.1 * x⁻¹, h.1⟩, ⟨(p.1 * x⁻¹)⁻¹ * (p.2 * x⁻¹), N.mul_mem (N.inv_mem h.1) h.2⟩)
    else (1, 1)
  have h1 : BU.card * BD.card ≤ Bad.card := by
    rw [← Finset.card_product]
    refine Finset.card_le_card_of_injOn φ ?_ ?_
    · intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.1 hp
      obtain ⟨hpU, hpN⟩ := Finset.mem_filter.1 hp1
      obtain ⟨hpD, hpN'⟩ := Finset.mem_filter.1 hp2
      have hφ : φ p = (⟨p.1 * x⁻¹, hpN⟩,
          ⟨(p.1 * x⁻¹)⁻¹ * (p.2 * x⁻¹), N.mul_mem (N.inv_mem hpN) hpN'⟩) :=
        dif_pos ⟨hpN, hpN'⟩
      rw [Finset.mem_coe, hφ]
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      set t : N := ⟨(p.1 * x⁻¹)⁻¹ * (p.2 * x⁻¹), N.mul_mem (N.inv_mem hpN) hpN'⟩
      have hroute := walk_meets_separator (S := S) hcover hUD hnoedge
      obtain ⟨g0, rest, hg⟩ : ∃ g0 rest, γ t = g0 :: rest := by
        cases h : γ t with
        | nil => have := hγh t; rw [h] at this; simp at this
        | cons g0 rest => exact ⟨g0, rest, rfl⟩
      have hg0 : g0 = x := by have := hγh t; rw [hg] at this; simpa using this
      have hlast : (p.1 * x⁻¹) * ((t : H) * x) = p.2 := by
        simp only [t]; group
      have hmapeq : (γ t).map ((p.1 * x⁻¹) * ·) = p.1 :: rest.map ((p.1 * x⁻¹) * ·) := by
        rw [hg, hg0]; simp
      obtain ⟨s, hs, hsS⟩ := hroute (rest.map ((p.1 * x⁻¹) * ·)) p.1
        (by
          rw [← hmapeq, List.isChain_map]
          exact (hγc t).imp fun a b hab => (cay_adj_mul_left _).2 hab)
        (by
          rw [← hmapeq]; intro z hz
          obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hz
          exact hZ _ hpN _ (hγZ t a ha))
        hpU
        ⟨p.2, by
          rw [← hmapeq, ← hlast]
          exact List.mem_map_of_mem (List.mem_of_getLast? (hγl t)), hpD⟩
      exact ⟨s, hsS, by rw [hmapeq]; exact hs⟩
    · intro p hp q hq hpq
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.1 hp
      obtain ⟨hq1, hq2⟩ := Finset.mem_product.1 hq
      have hpN := (Finset.mem_filter.1 hp1).2
      have hpN' := (Finset.mem_filter.1 hp2).2
      have hqN := (Finset.mem_filter.1 hq1).2
      have hqN' := (Finset.mem_filter.1 hq2).2
      simp only [φ, dif_pos (And.intro hpN hpN'), dif_pos (And.intro hqN hqN'),
        Prod.mk.injEq, Subtype.mk.injEq] at hpq
      obtain ⟨h1, h2⟩ := hpq
      have e1 : p.1 = q.1 := mul_right_cancel h1
      rw [h1] at h2
      have e2 : p.2 = q.2 := mul_right_cancel (mul_left_cancel h2)
      exact Prod.ext e1 e2
  have h2 : Bad.card ≤ S₀.card * (Nat.card N * (L + 1)) := by
    have hsub : Bad ⊆ S₀.biUnion (fun s => Finset.univ.filter
        (fun p : N × N => s ∈ (γ p.2).map ((p.1 : H) * ·))) := by
      intro p hp
      obtain ⟨-, s, hs, hsp⟩ := Finset.mem_filter.1 hp
      exact Finset.mem_biUnion.2 ⟨s, hs, Finset.mem_filter.2 ⟨Finset.mem_univ _, hsp⟩⟩
    refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
    rw [← smul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum (fun s _ => ?_)
    have hsub2 : Finset.univ.filter (fun p : N × N => s ∈ (γ p.2).map ((p.1 : H) * ·)) ⊆
        Finset.univ.biUnion (fun t : N =>
          (Finset.univ.filter (fun n : N => (n : H)⁻¹ * s ∈ γ t)).image (fun n => (n, t))) := by
      intro p hp
      obtain ⟨-, hsp⟩ := Finset.mem_filter.1 hp
      obtain ⟨a, ha, hsa⟩ := List.mem_map.1 hsp
      refine Finset.mem_biUnion.2 ⟨p.2, Finset.mem_univ _, Finset.mem_image.2
        ⟨p.1, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, rfl⟩⟩
      rw [← hsa]; simpa using ha
    refine (Finset.card_le_card hsub2).trans (Finset.card_biUnion_le.trans ?_)
    calc ∑ t : N, ((Finset.univ.filter (fun n : N => (n : H)⁻¹ * s ∈ γ t)).image
            (fun n => (n, t))).card
        ≤ ∑ _t : N, (L + 1) := by
          refine Finset.sum_le_sum (fun t _ => Finset.card_image_le.trans ?_)
          refine le_trans ?_ ((List.toFinset_card_le (γ t)).trans (hγlen t))
          refine Finset.card_le_card_of_injOn (fun n : N => (n : H)⁻¹ * s) ?_ ?_
          · intro n hn
            exact List.mem_toFinset.2 (Finset.mem_filter.1 hn).2
          · intro n _ n' _ h
            exact Subtype.ext (inv_injective (mul_right_cancel h))
      _ = Nat.card N * (L + 1) := by
          rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, smul_eq_mul]
  calc BU.card * BD.card ≤ S₀.card * (Nat.card N * (L + 1)) := h1.trans h2
    _ = Nat.card N * (L + 1) * S₀.card := by ring

/-- **Lemma 3.6** (a rail with many attachments). There is a path in `Z` with at least
`m / (16 (L + 1))` pairwise vertex-disjoint attachments from the `N`-orbit of `x`. -/
theorem exists_rail [Finite H] (S : Set H) (N : Subgroup H) (Z : Finset H) (L : ℕ)
    (hL : ∀ u ∈ Z, ∀ v ∈ Z, WalkLe (cay S) Z u v L) (hZ : ∀ n ∈ N, ∀ z ∈ Z, n * z ∈ Z)
    (x : H) (hx : x ∈ Z) :
    ∃ T : Finset H, (∀ t ∈ T, t * x⁻¹ ∈ N) ∧ (Nat.card N : ℝ) / (16 * (L + 1)) ≤ T.card ∧
      HasRail (cay S) Z T := by
  have := Fintype.ofFinite H
  set B : Finset H := Finset.univ.filter (fun y => y * x⁻¹ ∈ N) with hB
  have hBZ : ∀ b ∈ B, b ∈ Z := by
    intro b hb
    have := hZ _ (Finset.mem_filter.1 hb).2 x hx
    simpa using this
  have hBcard : B.card = Nat.card N := by
    have := Fintype.ofFinite N
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
    refine Finset.card_bij' (fun y hy => ⟨y * x⁻¹, (Finset.mem_filter.1 hy).2⟩)
      (fun n _ => (n : H) * x) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro n _; simp [hB]
    · intro y _; simp
    · intro n _; ext; simp
  set m := B.card with hm
  have hxB : x ∈ B := by simp [hB, N.one_mem]
  have hm0 : 0 < m := Finset.card_pos.2 ⟨x, hxB⟩
  obtain ⟨P, hP, hPZ, hbal⟩ := exists_balanced_path (cay S) Z B
  let GZ : SimpleGraph H :=
    { Adj := fun u v => (cay S).Adj u v ∧ u ∈ Z ∧ v ∈ Z
      symm := ⟨fun u v h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
      loopless := ⟨fun u h => h.1.ne rfl⟩ }
  have hGZ : GZ ≤ cay S := fun u v h => h.1
  have hex : ∃ n, ∃ T : Finset H, Separates GZ (B : Set H) {v | v ∈ P} T ∧ T.card = n :=
    ⟨_, Finset.univ, fun a _ _ _ hr => hr.mem_left (Finset.mem_univ a), rfl⟩
  set k := Nat.find hex with hk
  obtain ⟨T₀, hT₀, hT₀k⟩ := Nat.find_spec hex
  have hmin : ∀ T, Separates GZ (B : Set H) {v | v ∈ P} T → k ≤ T.card :=
    fun T hT => Nat.find_min' hex ⟨T, hT, rfl⟩
  obtain ⟨p, hp⟩ := menger GZ (B : Set H) {v | v ∈ P} k hmin
  obtain ⟨T, hTB, hTk, hrail⟩ := rail_of_disjPaths hGZ (Z := (Z : Set H))
    (fun u v h => h.2.2) (fun b hb => hBZ b hb) hP hPZ hp
  refine ⟨T, fun t ht => (Finset.mem_filter.1 (hTB t ht)).2, ?_, ⟨P, hrail⟩⟩
  suffices hkey : m ≤ 16 * (L + 1) * k by
    rw [← hBcard, hTk, div_le_iff₀ (by positivity)]
    have : ((m : ℕ) : ℝ) ≤ ((16 * (L + 1) * k : ℕ) : ℝ) := by exact_mod_cast hkey
    push_cast at this; linarith
  by_contra hlt
  push_neg at hlt
  have h4k : 4 * k ≤ m := by nlinarith
  set sT : Set H := {v | v ∈ Z ∧ v ∉ T₀} with hsT
  set R : Finset H := Z.filter (fun v => v ∉ T₀) with hR
  have hRZ : ∀ b z, ReachIn (cay S) sT b z → ReachIn GZ {v | v ∉ T₀} b z := by
    intro b z h
    refine ReachIn.closed (Q := fun z => ReachIn GZ {v | v ∉ T₀} b z)
      (ReachIn.refl h.mem_left.2) ?_ h
    intro a c ha has hcs hac
    exact ha.tail ⟨hac, has.1, hcs.1⟩ hcs.2
  have hsmall : ∀ b ∈ B, 2 * (B.filter (fun y => ReachIn (cay S) sT b y)).card ≤ m := by
    intro b hb
    refine le_trans (Nat.mul_le_mul_left _ (Finset.card_le_card ?_)) (hbal b)
    intro y hy
    simp only [Finset.mem_filter] at hy ⊢
    refine ⟨hy.1, hy.2.restrict.mono le_rfl ?_⟩
    rintro w ⟨hw, hbw⟩
    exact ⟨hw.1, fun hwP => hT₀ b hb w hwP (hRZ b w hbw)⟩
  let wt : Finset H → ℕ := fun F => (F.filter (fun y => y * x⁻¹ ∈ N)).card
  let U : Finset H → Finset H := fun X => R.filter (fun z => ∃ b ∈ X, ReachIn (cay S) sT b z)
  have hUR : ∀ X, U X ⊆ R := fun X => Finset.filter_subset _ _
  have hsplit : ∀ X, wt (U X) + wt (R \ U X) = wt R := by
    intro X
    have he : (R \ U X).filter (fun y => y * x⁻¹ ∈ N) =
        R.filter (fun y => y * x⁻¹ ∈ N) \ (U X).filter (fun y => y * x⁻¹ ∈ N) := by
      ext y; simp only [Finset.mem_filter, Finset.mem_sdiff]; tauto
    simp only [wt, he]
    rw [Finset.card_sdiff_of_subset (Finset.monotone_filter_left _ (hUR X))]
    have := Finset.card_le_card (Finset.monotone_filter_left (fun y => y * x⁻¹ ∈ N) (hUR X))
    omega
  have hsep : ∀ X, wt (U X) * wt (R \ U X) ≤ m * (L + 1) * k := by
    intro X
    refine le_of_le_of_eq (separation_ineq S N Z L hL x hx hZ (U X) T₀ (R \ U X) ?_ ?_ ?_)
      (by rw [← hBcard, hT₀k])
    · intro z hz
      by_cases hzT : z ∈ T₀
      · exact Or.inr (Or.inl hzT)
      · by_cases hzU : z ∈ U X
        · exact Or.inl hzU
        · exact Or.inr (Or.inr (Finset.mem_sdiff.2 ⟨Finset.mem_filter.2 ⟨hz, hzT⟩, hzU⟩))
    · exact Finset.disjoint_sdiff
    · intro u hu d hd hud
      obtain ⟨hdR, hdU⟩ := Finset.mem_sdiff.1 hd
      obtain ⟨-, b, hb, hbu⟩ := Finset.mem_filter.1 hu
      have hdR' := Finset.mem_filter.1 hdR
      exact hdU (Finset.mem_filter.2 ⟨hdR, b, hb, hbu.tail hud ⟨hdR'.1, hdR'.2⟩⟩)
  have hwtR : m ≤ wt R + k := by
    have hT₀k' : T₀.card = k := hT₀k
    rw [← hT₀k']
    have hsub : B ⊆ R.filter (fun y => y * x⁻¹ ∈ N) ∪ T₀ := by
      intro b hb
      by_cases hbT : b ∈ T₀
      · exact Finset.mem_union_right _ hbT
      · exact Finset.mem_union_left _ (Finset.mem_filter.2
          ⟨Finset.mem_filter.2 ⟨hBZ b hb, hbT⟩, (Finset.mem_filter.1 hb).2⟩)
    exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hsingle : ∀ b ∈ B, wt (U {b}) ≤ (B.filter (fun y => ReachIn (cay S) sT b y)).card := by
    intro b hb
    refine Finset.card_le_card ?_
    intro y hy
    simp only [U, Finset.mem_filter, Finset.mem_singleton, exists_eq_left] at hy
    simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hy.2, hy.1.2⟩
  have hins : ∀ b X, wt (U (insert b X)) ≤ wt (U X) + wt (U {b}) := by
    intro b X
    have hsub : U (insert b X) ⊆ U X ∪ U {b} := by
      intro z hz
      obtain ⟨hzR, c, hc, hcz⟩ := Finset.mem_filter.1 hz
      rcases Finset.mem_insert.1 hc with rfl | hc
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hzR, c, Finset.mem_singleton_self _, hcz⟩)
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hzR, c, hc, hcz⟩)
    refine (Finset.card_le_card (Finset.monotone_filter_left _ hsub)).trans ?_
    rw [Finset.filter_union]
    exact Finset.card_union_le _ _
  set Y : Finset H := B.filter (fun b => b ∉ T₀) with hY
  have hUY : wt (U Y) = wt R := by
    refine le_antisymm (Finset.card_le_card (Finset.monotone_filter_left _ (hUR Y))) ?_
    refine Finset.card_le_card ?_
    intro z hz
    obtain ⟨hzR, hzN⟩ := Finset.mem_filter.1 hz
    have hzR' := Finset.mem_filter.1 hzR
    refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hzR, z, ?_, ReachIn.refl hzR'⟩, hzN⟩
    simp [hY, hB, hzN, hzR'.2]
  obtain ⟨X, hX1, hX2⟩ : ∃ X, m ≤ 4 * wt (U X) ∧ m ≤ 4 * wt (R \ U X) := by
    by_cases hA : ∃ b ∈ Y, m ≤ 4 * wt (U {b})
    · obtain ⟨b, hbY, hb⟩ := hA
      have hbB := (Finset.mem_filter.1 hbY).1
      have h1 := (hsingle b hbB).trans' le_rfl
      have h2 := hsmall b hbB
      have h3 := hsplit {b}
      exact ⟨{b}, hb, by omega⟩
    · push_neg at hA
      obtain ⟨X, -, h1, h2⟩ := greedy_subset (fun X => 4 * wt (U X)) m m Y
        (by simp [U, wt]; omega)
        (fun b hb X => by have := hins b X; have := hA b hb; omega)
        (by omega)
      have h3 := hsplit X
      exact ⟨X, h1, by omega⟩
  have h5 := hsep X
  have h6 : m * m ≤ m * (16 * (L + 1) * k) := by
    calc m * m ≤ (4 * wt (U X)) * (4 * wt (R \ U X)) := Nat.mul_le_mul hX1 hX2
      _ = 16 * (wt (U X) * wt (R \ U X)) := by ring
      _ ≤ 16 * (m * (L + 1) * k) := Nat.mul_le_mul_left _ h5
      _ = m * (16 * (L + 1) * k) := by ring
  have := Nat.le_of_mul_le_mul_left h6 hm0
  omega

end Lovasz
