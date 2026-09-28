module
public import RequestProject.VTBasic
public import RequestProject.VTWindow
public import RequestProject.Attach

/-!
# A rail with many attachments for a transitive fibre (Lemmas A.6 and A.7)

A finite group `Γ` acts on the graph `G` by automorphisms, `N ≤ Γ`, all `N`-orbits have `m`
elements, `Z` is an `N`-invariant vertex set, and any two vertices of `Z` are joined by a walk
inside `Z` with at most `L` edges.
-/

@[expose] public section


open Classical

namespace Lovasz

variable {V Γ : Type*} [Group Γ] [MulAction Γ V] [Fintype Γ] {G : SimpleGraph V}

omit [Fintype Γ] in
/-- A walk from `U` to `D` inside a separated set meets the separator. -/
lemma walk_meets_separator_gen {Z U S₀ D : Finset V}
    (hcover : ∀ z ∈ Z, z ∈ U ∨ z ∈ S₀ ∨ z ∈ D) (hUD : Disjoint U D)
    (hnoedge : ∀ u ∈ U, ∀ d ∈ D, ¬ G.Adj u d) :
    ∀ (l : List V) (u : V), (u :: l).IsChain G.Adj → (∀ z ∈ u :: l, z ∈ Z) → u ∈ U →
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

/-- Counting group elements sending `a` into a finset: at most `s` per target point, where
`s = #{g ∈ N : g • x = x}`. -/
lemma card_filter_smul_mem_le (N : Subgroup Γ) {m : ℕ} (hm : ∀ v : V, (orb N v).card = m)
    (x a : V) (F : Finset V) :
    ((nset N).filter (fun g => g • a ∈ F)).card ≤
      F.card * ((nset N).filter (fun g : Γ => g • x = x)).card := by
  have hsub : (nset N).filter (fun g => g • a ∈ F) ⊆
      F.biUnion (fun z => (nset N).filter (fun g => g • a = z)) := by
    intro g hg
    obtain ⟨hgN, hgF⟩ := Finset.mem_filter.1 hg
    exact Finset.mem_biUnion.2 ⟨_, hgF, Finset.mem_filter.2 ⟨hgN, rfl⟩⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  rw [← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun z _ => ?_
  by_cases hz : fib N z = fib N a
  · exact (card_filter_smul_uniform N hm hz rfl).le
  · rw [Finset.card_eq_zero.2]
    · exact Nat.zero_le _
    · rw [Finset.filter_eq_empty_iff]
      intro g hg hgz
      exact hz (hgz ▸ fib_smul_of_mem (mem_nset.1 hg) a)

lemma card_filter_smul_mem_eq (N : Subgroup Γ) {m : ℕ} (hm : ∀ v : V, (orb N v).card = m)
    (x a : V) (ha : fib N a = fib N x) (F : Finset V) (hF : ∀ v ∈ F, fib N v = fib N x) :
    ((nset N).filter (fun g => g • a ∈ F)).card =
      F.card * ((nset N).filter (fun g : Γ => g • x = x)).card := by
  have := Finset.card_eq_sum_card_fiberwise (f := fun g => g • a)
    (s := (nset N).filter (fun g => g • a ∈ F)) (t := F)
    (fun g hg => Finset.mem_coe.2 (Finset.mem_filter.1 hg).2)
  rw [this, Finset.sum_congr rfl (g := fun _ => ((nset N).filter (fun g : Γ => g • x = x)).card),
    Finset.sum_const, smul_eq_mul]
  intro a' ha'
  rw [← card_filter_smul_uniform N hm ((hF a' ha').trans ha.symm) rfl, Finset.filter_filter]
  congr 1; ext g; simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hg, -, h⟩; exact ⟨hg, h⟩
  · rintro ⟨hg, h⟩; exact ⟨hg, by rw [h]; exact ha', h⟩

/-- **Lemma A.6** (transitive routing inequality). If `(U, S₀, D)` is a separation of `Z` and
`B` is the `N`-orbit of `x ∈ Z`, then `|U ∩ B| |D ∩ B| ≤ m (L + 1) |S₀|`. -/
theorem separation_ineq_vt (hX : ActsOn G Γ) (N : Subgroup Γ) {m : ℕ}
    (hm : ∀ v : V, (orb N v).card = m) (Z : Finset V) (L : ℕ)
    (hL : ∀ u ∈ Z, ∀ v ∈ Z, WalkLe G Z u v L) (x : V) (hx : x ∈ Z)
    (hZ : ∀ n ∈ N, ∀ z ∈ Z, n • z ∈ Z)
    (U S₀ D : Finset V) (hcover : ∀ z ∈ Z, z ∈ U ∨ z ∈ S₀ ∨ z ∈ D) (hUD : Disjoint U D)
    (hnoedge : ∀ u ∈ U, ∀ d ∈ D, ¬ G.Adj u d) :
    (U.filter (fun y => fib N y = fib N x)).card * (D.filter (fun y => fib N y = fib N x)).card ≤
      m * (L + 1) * S₀.card := by
  set S := nset N with hSdef
  set s := (S.filter (fun g : Γ => g • x = x)).card with hs
  have hsm : s * m = S.card := by rw [← hm x]; exact card_filter_smul_eq N rfl
  have hs0 : 0 < s :=
    Finset.card_pos.2 ⟨1, Finset.mem_filter.2 ⟨mem_nset.2 N.one_mem, one_smul _ _⟩⟩
  have hγ : ∀ t : Γ, ∃ γ : List V, t ∈ N → (γ.IsChain G.Adj ∧ γ.head? = some x ∧
      γ.getLast? = some (t • x) ∧ (∀ z ∈ γ, z ∈ Z) ∧ γ.length ≤ L + 1) := by
    intro t
    by_cases ht : t ∈ N
    · obtain ⟨γ, h⟩ := hL x hx _ (hZ t ht x hx); exact ⟨γ, fun _ => h⟩
    · exact ⟨[], fun h => absurd h ht⟩
  choose γ hγ using hγ
  set BU := U.filter (fun y => fib N y = fib N x) with hBU
  set BD := D.filter (fun y => fib N y = fib N x) with hBD
  let bad : Γ → Γ → Prop := fun g t => ∃ w ∈ γ t, g • w ∈ S₀
  have hup : ∑ g ∈ S, (S.filter (fun t => bad g t)).card ≤
      S.card * ((L + 1) * (S₀.card * s)) := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm, ← smul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun t ht => ?_
    rw [← Finset.card_filter]
    have hsub : S.filter (fun g => bad g t) ⊆
        (γ t).toFinset.biUnion (fun w => S.filter (fun g => g • w ∈ S₀)) := by
      intro g hg
      obtain ⟨hgS, w, hw, hwS⟩ := Finset.mem_filter.1 hg
      exact Finset.mem_biUnion.2 ⟨w, List.mem_toFinset.2 hw, Finset.mem_filter.2 ⟨hgS, hwS⟩⟩
    refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
    calc ∑ w ∈ (γ t).toFinset, (S.filter (fun g => g • w ∈ S₀)).card
        ≤ ∑ _w ∈ (γ t).toFinset, S₀.card * s :=
          Finset.sum_le_sum fun w _ => card_filter_smul_mem_le N hm x w S₀
      _ = (γ t).toFinset.card * (S₀.card * s) := by simp
      _ ≤ (L + 1) * (S₀.card * s) := by
          gcongr
          exact (List.toFinset_card_le _).trans (hγ t (mem_nset.1 ht)).2.2.2.2
  have hlow : BU.card * s * (BD.card * s) ≤ ∑ g ∈ S, (S.filter (fun t => bad g t)).card := by
    have h1 : (S.filter (fun g => g • x ∈ BU)).card = BU.card * s :=
      card_filter_smul_mem_eq N hm x x rfl BU (fun v hv => (Finset.mem_filter.1 hv).2)
    rw [← h1, ← smul_eq_mul, ← Finset.sum_const]
    refine le_trans ?_ (Finset.sum_le_sum_of_subset (Finset.filter_subset (fun g : Γ => g • x ∈ BU) S))
    refine Finset.sum_le_sum fun g hg => ?_
    obtain ⟨hgS, hgU⟩ := Finset.mem_filter.1 hg
    have hgN := mem_nset.1 hgS
    have h2 := card_filter_smul_mem_eq N hm x x rfl (BD.image (g⁻¹ • ·)) (by
      intro v hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hv
      rw [fib_smul_of_mem (N.inv_mem hgN)]; exact (Finset.mem_filter.1 hw).2)
    rw [Finset.card_image_of_injective _ (MulAction.injective _)] at h2
    rw [← h2]
    refine Finset.card_le_card fun t ht => ?_
    obtain ⟨htS, htD⟩ := Finset.mem_filter.1 ht
    obtain ⟨w, hw, hwe⟩ := Finset.mem_image.1 htD
    refine Finset.mem_filter.2 ⟨htS, ?_⟩
    have htN := mem_nset.1 htS
    obtain ⟨hc, hh, hl, hZ', -⟩ := hγ t htN
    obtain ⟨g0, rest, hg⟩ : ∃ g0 rest, γ t = g0 :: rest := by
      cases h : γ t with
      | nil => rw [h] at hh; simp at hh
      | cons g0 rest => exact ⟨g0, rest, rfl⟩
    have hg0 : g0 = x := by rw [hg] at hh; simpa using hh
    have hmapeq : (γ t).map (g • ·) = g • x :: rest.map (g • ·) := by rw [hg, hg0]; simp
    have hwmem : w ∈ (γ t).map (g • ·) := by
      have : w = g • (t • x) := by rw [← hwe]; simp
      rw [this]; exact List.mem_map_of_mem (List.mem_of_getLast? hl)
    obtain ⟨z, hz, hzS⟩ := walk_meets_separator_gen hcover hUD hnoedge (rest.map (g • ·)) (g • x)
      (by rw [← hmapeq, List.isChain_map]; exact hc.imp fun a b hab => hX g a b hab)
      (by
        rw [← hmapeq]; intro z hz
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hz
        exact hZ g hgN a (hZ' a ha))
      (Finset.mem_filter.1 hgU).1 ⟨w, by rw [← hmapeq]; exact hwmem, (Finset.mem_filter.1 hw).1⟩
    rw [← hmapeq] at hz
    obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hz
    exact ⟨w', hw', hzS⟩
  have key : BU.card * BD.card * (s * s) ≤ m * (L + 1) * S₀.card * (s * s) := by
    calc BU.card * BD.card * (s * s) = BU.card * s * (BD.card * s) := by ring
      _ ≤ S.card * ((L + 1) * (S₀.card * s)) := hlow.trans hup
      _ = m * (L + 1) * S₀.card * (s * s) := by rw [← hsm]; ring
  exact Nat.le_of_mul_le_mul_right key (Nat.mul_pos hs0 hs0)

theorem exists_rail_vt [Fintype V] (hX : ActsOn G Γ) (N : Subgroup Γ) {m : ℕ}
    (hm : ∀ v : V, (orb N v).card = m) (Z : Finset V) (L : ℕ)
    (hL : ∀ u ∈ Z, ∀ v ∈ Z, WalkLe G Z u v L) (hZ : ∀ n ∈ N, ∀ z ∈ Z, n • z ∈ Z)
    (x : V) (hx : x ∈ Z) :
    ∃ T : Finset V, (∀ t ∈ T, fib N t = fib N x) ∧ (m : ℝ) / (16 * (L + 1)) ≤ T.card ∧
      HasRail G Z T := by
  set B : Finset V := Finset.univ.filter (fun y => fib N y = fib N x) with hB
  have hBZ : ∀ b ∈ B, b ∈ Z := by
    intro b hb
    obtain ⟨n, hn, rfl⟩ := fib_eq_iff.1 (Finset.mem_filter.1 hb).2
    exact hZ n hn x hx
  have hBcard : B.card = m := by
    rw [← hm x]; congr 1; ext y; simp [hB, mem_orb]
  clear_value B
  subst hBcard
  set m := B.card with hm'
  have hBmem : ∀ y, y ∈ B ↔ fib N y = fib N x := fun y => by rw [hB]; simp
  have hxB : x ∈ B := (hBmem x).2 rfl
  have hm0 : 0 < m := Finset.card_pos.2 ⟨x, hxB⟩
  obtain ⟨P, hP, hPZ, hbal⟩ := exists_balanced_path G Z B
  let GZ : SimpleGraph V :=
    { Adj := fun u v => G.Adj u v ∧ u ∈ Z ∧ v ∈ Z
      symm := ⟨fun u v h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
      loopless := ⟨fun u h => h.1.ne rfl⟩ }
  have hGZ : GZ ≤ G := fun u v h => h.1
  have hex : ∃ n, ∃ T : Finset V, Separates GZ (B : Set V) {v | v ∈ P} T ∧ T.card = n :=
    ⟨_, Finset.univ, fun a _ _ _ hr => hr.mem_left (Finset.mem_univ a), rfl⟩
  set k := Nat.find hex with hk
  obtain ⟨T₀, hT₀, hT₀k⟩ := Nat.find_spec hex
  have hmin : ∀ T, Separates GZ (B : Set V) {v | v ∈ P} T → k ≤ T.card :=
    fun T hT => Nat.find_min' hex ⟨T, hT, rfl⟩
  obtain ⟨p, hp⟩ := menger GZ (B : Set V) {v | v ∈ P} k hmin
  obtain ⟨T, hTB, hTk, hrail⟩ := rail_of_disjPaths hGZ (Z := (Z : Set V))
    (fun u v h => h.2.2) (fun b hb => hBZ b hb) hP hPZ hp
  refine ⟨T, fun t ht => by
    exact (hBmem t).1 (hTB t ht), ?_, ⟨P, hrail⟩⟩
  suffices hkey : m ≤ 16 * (L + 1) * k by
    rw [hTk, div_le_iff₀ (by positivity)]
    have : ((m : ℕ) : ℝ) ≤ ((16 * (L + 1) * k : ℕ) : ℝ) := by exact_mod_cast hkey
    push_cast at this; linarith
  by_contra hlt
  push_neg at hlt
  have h4k : 4 * k ≤ m := by nlinarith
  set sT : Set V := {v | v ∈ Z ∧ v ∉ T₀} with hsT
  set R : Finset V := Z.filter (fun v => v ∉ T₀) with hR
  have hRZ : ∀ b z, ReachIn G sT b z → ReachIn GZ {v | v ∉ T₀} b z := by
    intro b z h
    refine ReachIn.closed (Q := fun z => ReachIn GZ {v | v ∉ T₀} b z)
      (ReachIn.refl h.mem_left.2) ?_ h
    intro a c ha has hcs hac
    exact ha.tail ⟨hac, has.1, hcs.1⟩ hcs.2
  have hsmall : ∀ b ∈ B, 2 * (B.filter (fun y => ReachIn G sT b y)).card ≤ m := by
    intro b hb
    refine le_trans (Nat.mul_le_mul_left _ (Finset.card_le_card ?_)) (hbal b)
    intro y hy
    simp only [Finset.mem_filter] at hy ⊢
    refine ⟨hy.1, hy.2.restrict.mono le_rfl ?_⟩
    rintro w ⟨hw, hbw⟩
    exact ⟨hw.1, fun hwP => hT₀ b hb w hwP (hRZ b w hbw)⟩
  let wt : Finset V → ℕ := fun F => (F.filter (fun y => fib N y = fib N x)).card
  let U : Finset V → Finset V := fun X => R.filter (fun z => ∃ b ∈ X, ReachIn G sT b z)
  have hUR : ∀ X, U X ⊆ R := fun X => Finset.filter_subset _ _
  have hsplit : ∀ X, wt (U X) + wt (R \ U X) = wt R := by
    intro X
    have he : (R \ U X).filter (fun y => fib N y = fib N x) =
        R.filter (fun y => fib N y = fib N x) \ (U X).filter (fun y => fib N y = fib N x) := by
      ext y; simp only [Finset.mem_filter, Finset.mem_sdiff]; tauto
    simp only [wt, he]
    rw [Finset.card_sdiff_of_subset (Finset.monotone_filter_left _ (hUR X))]
    have := Finset.card_le_card (Finset.monotone_filter_left (fun y => fib N y = fib N x) (hUR X))
    omega
  have hsep : ∀ X, wt (U X) * wt (R \ U X) ≤ m * (L + 1) * k := by
    intro X
    refine le_of_le_of_eq (separation_ineq_vt hX N hm Z L hL x hx hZ (U X) T₀ (R \ U X) ?_ ?_ ?_)
      (by rw [hT₀k])
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
    have hsub : B ⊆ R.filter (fun y => fib N y = fib N x) ∪ T₀ := by
      intro b hb
      by_cases hbT : b ∈ T₀
      · exact Finset.mem_union_right _ hbT
      · exact Finset.mem_union_left _ (Finset.mem_filter.2
          ⟨Finset.mem_filter.2 ⟨hBZ b hb, hbT⟩, (hBmem b).1 hb⟩)
    exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hsingle : ∀ b ∈ B, wt (U {b}) ≤ (B.filter (fun y => ReachIn G sT b y)).card := by
    intro b hb
    refine Finset.card_le_card ?_
    intro y hy
    simp only [U, Finset.mem_filter, Finset.mem_singleton, exists_eq_left] at hy
    rw [Finset.mem_filter, hBmem]
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
  set Y : Finset V := B.filter (fun b => b ∉ T₀) with hY
  have hUY : wt (U Y) = wt R := by
    refine le_antisymm (Finset.card_le_card (Finset.monotone_filter_left _ (hUR Y))) ?_
    refine Finset.card_le_card ?_
    intro z hz
    obtain ⟨hzR, hzN⟩ := Finset.mem_filter.1 hz
    have hzR' := Finset.mem_filter.1 hzR
    refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hzR, z, ?_, ReachIn.refl hzR'⟩, hzN⟩
    simp [hY, hBmem, hzN, hzR'.2]
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
