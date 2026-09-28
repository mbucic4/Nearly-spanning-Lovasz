module
public import RequestProject.VTLift
public import RequestProject.VTAttach
public import RequestProject.Lifting

/-!
# Corridors and the fibre-lifting theorem for a transitive action (Theorem A.9)
-/

@[expose] public section


open Classical

namespace Lovasz

/-- **Lemma 3.7** for a transitive action (as used in the proof of Theorem A.9).  If `W ∋ w`
has `b` elements and `l` is a list of `p > 16 b²` distinct points, there are disjoint translates
`W₀ = g₀ W`, `W₁ = g₁ W` and indices `i < j` with `l[i] ∈ W₀`, `l[j] ∈ W₁`, no entry strictly
between them in `W₀ ∪ W₁`, and `j - i > p / (8 b²)`. -/
theorem two_windows_act {Q Γ : Type*} [Group Γ] [MulAction Γ Q] [Fintype Γ] [Fintype Q]
    [DecidableEq Q]
    (hT : TransOn Γ Q) (W : Finset Q) (w : Q) (hw : w ∈ W)
    (l : List Q) (hl : l.Nodup) (hp : 16 * W.card ^ 2 < l.length) :
    ∃ g₀ g₁ : Γ, Disjoint (W.image (g₀ • ·)) (W.image (g₁ • ·)) ∧
      ∃ i j : ℕ, ∃ hij : i < j, ∃ hj : j < l.length,
        l[i] ∈ W.image (g₀ • ·) ∧ l[j] ∈ W.image (g₁ • ·) ∧
        (∀ k (hk : k < l.length), i < k → k < j →
          l[k] ∉ W.image (g₀ • ·) ∧ l[k] ∉ W.image (g₁ • ·)) ∧
        (l.length : ℝ) / (8 * W.card ^ 2) < (j : ℝ) - i := by
  set p := l.length with hpdef
  set b := W.card with hbdef
  have hb : 1 ≤ b := Finset.card_pos.2 ⟨w, hw⟩
  have hp0 : 0 < p := lt_of_le_of_lt (Nat.zero_le _) hp
  set f : ℕ → Q := fun k => l.getD k w with hfdef
  have hf : ∀ k (hk : k < p), f k = l[k] := fun k hk => List.getD_eq_getElem _ _ hk
  have hfinj : ∀ i j, i < p → j < p → f i = f j → i = j := by
    intro i j hi hj h
    rw [hf i hi, hf j hj] at h
    exact (List.Nodup.getElem_inj_iff hl).1 h
  obtain ⟨g0, hg0⟩ := hT w (f 0)
  set W0 := W.image (g0 • ·) with hW0
  have h0W0 : f 0 ∈ W0 := Finset.mem_image.2 ⟨w, hw, hg0⟩
  set r := p / (8 * b ^ 2) with hr
  set I0 := (Finset.range p).filter (fun i => f i ∈ W0) with hI0def
  have hI0 : I0.card ≤ b := by
    calc I0.card = (I0.image f).card := by
          refine (Finset.card_image_of_injOn ?_).symm
          intro i hi j hj h
          exact hfinj i j (Finset.mem_range.1 (Finset.mem_filter.1 hi).1)
            (Finset.mem_range.1 (Finset.mem_filter.1 hj).1) h
      _ ≤ W0.card := Finset.card_le_card (by
          intro x hx
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
          exact (Finset.mem_filter.1 hi).2)
      _ ≤ b := Finset.card_image_le
  set Nb := I0.biUnion (fun i => Finset.Icc (i - r) (i + r)) with hNbdef
  have hNb : Nb.card ≤ b * (2 * r + 1) := by
    refine Finset.card_biUnion_le.trans ?_
    calc ∑ i ∈ I0, (Finset.Icc (i - r) (i + r)).card ≤ ∑ _i ∈ I0, (2 * r + 1) := by
          apply Finset.sum_le_sum; intro i _; rw [Nat.card_Icc]; omega
      _ = I0.card * (2 * r + 1) := by simp
      _ ≤ b * (2 * r + 1) := by gcongr
  set F := W0 ∪ Nb.image f with hFdef
  have hF : F.card ≤ b + b * (2 * r + 1) :=
    (Finset.card_union_le _ _).trans (add_le_add Finset.card_image_le
      (Finset.card_image_le.trans hNb))
  -- counting over the acting group (the action on `Q` is transitive)
  have htop : ∀ a b : Q, fib (⊤ : Subgroup Γ) a = fib (⊤ : Subgroup Γ) b := by
    intro a b; obtain ⟨g, hg⟩ := hT b a; exact fib_eq_iff.2 ⟨g, Subgroup.mem_top g, hg⟩
  have hmQ : ∀ v : Q, (orb (⊤ : Subgroup Γ) v).card = Fintype.card Q := by
    intro v; rw [← Finset.card_univ]; congr 1
    ext y; simp only [Finset.mem_univ, iff_true]; exact mem_orb.2 (htop y v)
  set s := ((nset (⊤ : Subgroup Γ)).filter (fun g : Γ => g • w = w)).card with hs
  have hs0 : 0 < s :=
    Finset.card_pos.2 ⟨1, Finset.mem_filter.2 ⟨mem_nset.2 (Subgroup.mem_top _), one_smul _ _⟩⟩
  set P := (Finset.range p).image f with hPdef
  have hP : P.card = p := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj h
    exact hfinj i j (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) h
  set good := (nset (⊤ : Subgroup Γ)).filter (fun g => g • w ∈ P) with hgood
  have hgoodc : good.card = p * s := by
    have := card_filter_smul_mem_eq ⊤ hmQ w w rfl P (fun v _ => htop v w)
    rw [hP] at this
    rw [hgood]; convert this using 2 <;> first | (ext; simp) | (rw [hs]; congr 1; ext; simp)
  set bad := W.biUnion (fun x => (nset (⊤ : Subgroup Γ)).filter (fun g => g • x ∈ F)) with hbaddef
  have hbad : bad.card ≤ b * (F.card * s) := by
    refine Finset.card_biUnion_le.trans ?_
    calc ∑ x ∈ W, ((nset (⊤ : Subgroup Γ)).filter (fun g => g • x ∈ F)).card
        ≤ ∑ _x ∈ W, F.card * s := Finset.sum_le_sum fun x _ => by
          convert card_filter_smul_mem_le ⊤ hmQ w x F using 2 <;>
            first | (ext; simp) | (rw [hs]; congr 1; ext; simp)
      _ = b * (F.card * s) := by simp [b]
  have hlt0 : b * F.card < p := by
    have h1 : 8 * b ^ 2 * r ≤ p := by rw [mul_comm]; exact Nat.div_mul_le_self p _
    have h2 : b * (b + b * (2 * r + 1)) = 2 * (b ^ 2 * r) + 2 * b ^ 2 := by ring
    have h3 : b * F.card ≤ b * (b + b * (2 * r + 1)) := Nat.mul_le_mul_left _ hF
    have h4 : 8 * b ^ 2 * r = 8 * (b ^ 2 * r) := by ring
    omega
  have hlt : bad.card < good.card := by
    rw [hgoodc]
    calc bad.card ≤ b * F.card * s := by rw [mul_assoc]; exact hbad
      _ < p * s := Nat.mul_lt_mul_of_pos_right hlt0 hs0
  obtain ⟨g1, hg1G, hg1bad⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hW1F : ∀ x ∈ W, g1 • x ∉ F := fun x hx hxF =>
    hg1bad (Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hg1G).1, hxF⟩⟩)
  set W1 := W.image (g1 • ·) with hW1
  have hdisj : Disjoint W0 W1 := by
    rw [Finset.disjoint_left]
    intro a ha ha1
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha1
    exact hW1F x hx (Finset.mem_union_left _ ha)
  obtain ⟨i1, hi1, hg1⟩ := Finset.mem_image.1 (Finset.mem_filter.1 hg1G).2
  have hi1W1 : f i1 ∈ W1 := Finset.mem_image.2 ⟨w, hw, hg1.symm⟩
  have hex : ∃ j, j < p ∧ f j ∈ W1 := ⟨i1, Finset.mem_range.1 hi1, hi1W1⟩
  set j := Nat.find hex with hjdef
  have hj : j < p ∧ f j ∈ W1 := Nat.find_spec hex
  have hjmin : ∀ k < j, ¬ (k < p ∧ f k ∈ W1) := fun k hk => Nat.find_min hex hk
  have hj0 : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · exfalso; rw [h] at hj; exact Finset.disjoint_left.1 hdisj h0W0 hj.2
    · exact h
  set M := (Finset.range j).filter (fun i => f i ∈ W0) with hMdef
  have hMne : M.Nonempty := ⟨0, Finset.mem_filter.2 ⟨Finset.mem_range.2 hj0, h0W0⟩⟩
  set i := M.max' hMne with hidef
  have hiM : i ∈ M := Finset.max'_mem M hMne
  have hi : i < j ∧ f i ∈ W0 := by
    have := Finset.mem_filter.1 hiM; exact ⟨Finset.mem_range.1 this.1, this.2⟩
  have himax : ∀ k ∈ M, k ≤ i := fun k hk => Finset.le_max' M k hk
  have hfar : r < j - i := by
    by_contra hcon
    push_neg at hcon
    have hjN : j ∈ Nb := Finset.mem_biUnion.2 ⟨i, Finset.mem_filter.2
      ⟨Finset.mem_range.2 (by omega), hi.2⟩, Finset.mem_Icc.2 ⟨by omega, by omega⟩⟩
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.1 hj.2
    exact hW1F x hx (by rw [hxe]; exact Finset.mem_union_right _ (Finset.mem_image_of_mem f hjN))
  refine ⟨g0, g1, hdisj, i, j, hi.1, hj.1, ?_, ?_, ?_, ?_⟩
  · rw [← hf i (by omega)]; exact hi.2
  · rw [← hf j hj.1]; exact hj.2
  · intro k hk hik hkj
    rw [← hf k hk]
    refine ⟨fun h => ?_, fun h => hjmin k hkj ⟨hk, h⟩⟩
    have := himax k (Finset.mem_filter.2 ⟨Finset.mem_range.2 hkj, h⟩)
    omega
  · have hb2 : 0 < 8 * b ^ 2 := by positivity
    have h1 : p < 8 * b ^ 2 * (r + 1) := Nat.lt_mul_div_succ p hb2
    have h2 : p < (j - i) * (8 * b ^ 2) := by
      calc p < 8 * b ^ 2 * (r + 1) := h1
        _ ≤ 8 * b ^ 2 * (j - i) := Nat.mul_le_mul_left _ (by omega)
        _ = (j - i) * (8 * b ^ 2) := by ring
    have hcast : ((j - i : ℕ) : ℝ) = (j : ℝ) - i := by rw [Nat.cast_sub hi.1.le]
    have key : (p : ℝ) < ((j : ℝ) - i) * (8 * (b : ℝ) ^ 2) := by
      rw [← hcast]; exact_mod_cast h2
    have hpos : (0 : ℝ) < 8 * (b : ℝ) ^ 2 := by exact_mod_cast hb2
    exact (div_lt_iff₀ hpos).2 key


section Corridor

variable {V Γ : Type*} [Group Γ] [MulAction Γ V] [Fintype Γ]

/-- **Terminal alignment** in the proof of Theorem A.9: for a uniformly random `u ∈ N`,
`E |f(T₀) ∩ u T₁| = |T₀| |T₁| / m`; hence some `u` attains at least the average. -/
lemma exists_good_shift_vt (N : Subgroup Γ) {m : ℕ} (hm : ∀ v : V, (orb N v).card = m)
    (T0 T1 : Finset V) (e : V → V) (x1 : V) (hT1 : ∀ t ∈ T1, fib N t = fib N x1)
    (he : ∀ x ∈ T0, fib N (e x) = fib N x1) :
    ∃ u ∈ N, T0.card * T1.card ≤ (T0.filter (fun x => u⁻¹ • e x ∈ T1)).card * m := by
  set S := nset N
  set s := (S.filter (fun g : Γ => g • x1 = x1)).card with hs
  have hsm : s * m = S.card := by rw [← hm x1]; exact card_filter_smul_eq N rfl
  have hinner : ∀ x ∈ T0, (S.filter (fun u => u⁻¹ • e x ∈ T1)).card = T1.card * s := by
    intro x hx
    rw [← card_filter_smul_mem_eq N hm x1 (e x) (he x hx) T1 hT1]
    refine Finset.card_bij (fun u _ => u⁻¹) ?_ ?_ ?_
    · intro u hu
      obtain ⟨huS, hu1⟩ := Finset.mem_filter.1 hu
      exact Finset.mem_filter.2 ⟨mem_nset.2 (N.inv_mem (mem_nset.1 huS)), hu1⟩
    · intro u _ u' _ h; exact inv_injective h
    · intro u hu
      obtain ⟨huS, hu1⟩ := Finset.mem_filter.1 hu
      exact ⟨u⁻¹, Finset.mem_filter.2 ⟨mem_nset.2 (N.inv_mem (mem_nset.1 huS)), by simpa using hu1⟩,
        by simp⟩
  have hsum : ∑ u ∈ S, (T0.filter (fun x => u⁻¹ • e x ∈ T1)).card = T0.card * (T1.card * s) := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x hx => (Finset.card_filter _ _).symm.trans (hinner x hx)),
      Finset.sum_const, smul_eq_mul]
  obtain ⟨u, huS, hu⟩ := Finset.exists_le_of_sum_le (s := S)
    (f := fun _ => T0.card * T1.card)
    (g := fun u => (T0.filter (fun x => u⁻¹ • e x ∈ T1)).card * m)
    ⟨1, mem_nset.2 N.one_mem⟩ (by
      rw [Finset.sum_const, smul_eq_mul, ← Finset.sum_mul, hsum, ← hsm]
      exact le_of_eq (by ring))
  exact ⟨u, mem_nset.1 huS, hu⟩

end Corridor

/-- **Corridor lemma for a transitive action** (the common core of Theorem A.9).  Let `Γ` act
transitively on `X` by automorphisms, let `N ◁ Γ` have all orbits of size `m`, and let `W` be a
set of `b` orbits such that above every translate of `W`, and for every orbit `B` in that
translate, there is a rail with attachments from at least `τ` vertices of `B`.  Then
`p(X) ≥ c (τ²/m)^(1-η) p(X/N) / b²`. -/
theorem corridor_vt (h12 : CycleMatchingTheorem) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ (V Γ : Type) [Group Γ] [MulAction Γ V] [Fintype V] [Fintype Γ]
      (X : SimpleGraph V) (N : Subgroup Γ) [N.Normal] (m : ℕ), ActsOn X Γ → TransOn Γ V →
      (∀ v : V, (orb N v).card = m) →
      ∀ (W : Finset (Fib N V)) (τ : ℕ), W.Nonempty → 1 ≤ τ →
      (∀ g : Γ, ∀ B ∈ W.image (g • ·), ∃ T : Finset V,
          (∀ t ∈ T, fib N t = B) ∧ τ ≤ T.card ∧
          HasRail X {x | fib N x ∈ W.image (g • ·)} T) →
      c * ((τ : ℝ) ^ 2 / m) ^ (1 - η) * pathOrder (quotGraph X N) / (W.card : ℝ) ^ 2 ≤
        pathOrder X := by
  obtain ⟨a, ha, htr⟩ := two_rails h12 η hη0
  refine ⟨min (a / 8) (1 / 16), lt_min (by positivity) (by norm_num), ?_⟩
  intro V Γ _ _ _ _ X N _ m hX hT hm W τ hWne hτ hrail
  set Y := quotGraph X N with hY
  set p := pathOrder Y with hp
  set b := W.card with hb
  have hm0 : 0 < m := by
    obtain ⟨w, -⟩ := hWne
    obtain ⟨v, -⟩ := fib_surjective N w
    rw [← hm v]; exact Finset.card_pos.2 ⟨v, self_mem_orb N v⟩
  have hb1 : 1 ≤ b := hWne.card_pos
  set c := min (a / 8) (1 / 16) with hc
  have hc0 : 0 < c := lt_min (by positivity) (by norm_num)
  have hXp : ∀ l : List V, IsPathL X l → (l.length : ℝ) ≤ pathOrder X :=
    fun l hl => by exact_mod_cast hl.length_le_pathOrder
  set x := (τ : ℝ) ^ 2 / m with hx
  have hx0 : 0 ≤ x := by positivity
  by_cases hpb : 16 * b ^ 2 < p
  · obtain ⟨l, hl, hlen⟩ := exists_isPathL_length_eq_pathOrder Y
    obtain ⟨w, hw⟩ := hWne
    obtain ⟨g0, g1, hdisj, i, j, hij, hj, hi0, hj1, hbetw, hfar⟩ :=
      two_windows_act (hT.quot N) W w hw l hl.2 (by rw [hlen]; exact hpb)
    obtain ⟨hl'len, hl'head, hl'last, hl'mem⟩ := subpath_facts l i j hij.le hj
    set l' := (l.drop i).take (j - i + 1) with hl'
    have hl'path : IsPathL Y l' :=
      hl.infix ((List.take_prefix _ _).isInfix.trans (List.drop_suffix _ _).isInfix)
    set W0 := W.image (g0 • ·) with hW0
    set W1 := W.image (g1 • ·) with hW1
    have hl'W : ∀ z ∈ l', (z ∈ W0 → z = l[i]) ∧ (z ∈ W1 → z = l[j]) := by
      intro z hz
      obtain ⟨k, hk, hik, hkj, rfl⟩ := hl'mem z hz
      by_cases hki : k = i
      · subst hki
        exact ⟨fun _ => rfl, fun h => absurd h (Finset.disjoint_left.1 hdisj hi0)⟩
      by_cases hkj' : k = j
      · subst hkj'
        exact ⟨fun h => absurd hj1 (Finset.disjoint_left.1 hdisj h), fun _ => rfl⟩
      have := hbetw k hk (by omega) (by omega)
      exact ⟨fun h => absurd h this.1, fun h => absurd h this.2⟩
    have hne' : l' ≠ [] := by
      intro h; have := congrArg List.length h; simp only [List.length_nil] at this; omega
    obtain ⟨Lf, hLf, hLdisj⟩ := exists_disjoint_lifts hX N hm l' hne' hl'path
    have hl'h : l'.head hne' = l[i] := by
      have := List.head?_eq_some_head hne'; rw [hl'head] at this
      exact (Option.some.inj this).symm
    set e : V → V := fun y => ((Lf y).getLast?).getD y with he
    have hLp : ∀ y : V, fib N y = l[i] →
        IsPathL X (Lf y) ∧ (Lf y).map (fib N) = l' ∧ (Lf y).head? = some y := by
      intro y hy; exact hLf y (by rw [hl'h]; exact hy)
    have hLne : ∀ y : V, fib N y = l[i] → Lf y ≠ [] := by
      intro y hy h; have := (hLp y hy).2.2; rw [h] at this; simp at this
    have hLlast : ∀ y : V, fib N y = l[i] → (Lf y).getLast? = some (e y) := by
      intro y hy
      simp only [he, List.getLast?_eq_some_getLast (hLne y hy), Option.getD_some]
    have hLlen : ∀ y : V, fib N y = l[i] → (Lf y).length = j - i + 1 := by
      intro y hy; rw [← hl'len, ← (hLp y hy).2.1, List.length_map]
    have hLend : ∀ y : V, fib N y = l[i] → fib N (e y) = l[j] := by
      intro y hy
      have h1 := congrArg List.getLast? (hLp y hy).2.1
      rw [List.getLast?_map, hLlast y hy, hl'last] at h1
      exact Option.some.inj h1
    -- the two rails
    obtain ⟨T0, hT0, hτT0, R0, hR0⟩ := hrail g0 l[i] hi0
    obtain ⟨T1, hT1, hτT1, R1, hR1⟩ := hrail g1 l[j] hj1
    set Z0 : Set V := {y | fib N y ∈ W0} with hZ0
    set Z1 : Set V := {y | fib N y ∈ W1} with hZ1
    have hZdisj : Disjoint Z0 Z1 :=
      Set.disjoint_left.2 fun y h0 h1 => Finset.disjoint_left.1 hdisj h0 h1
    obtain ⟨y1, hy1⟩ := fib_surjective N l[j]
    obtain ⟨u, huN, hn⟩ := exists_good_shift_vt N hm T0 T1 e y1
      (fun t ht => (hT1 t ht).trans hy1.symm) (fun y hy => (hLend y (hT0 y hy)).trans hy1.symm)
    set K := T0.filter (fun y => u⁻¹ • e y ∈ T1) with hK
    set k := K.card with hk
    have hZ1n : (u • ·) '' Z1 = Z1 := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        show fib N (u • z) ∈ W1
        rw [fib_smul_of_mem huN]; exact hz
      · intro hy
        refine ⟨u⁻¹ • y, ?_, by simp⟩
        show fib N (u⁻¹ • y) ∈ W1
        rw [fib_smul_of_mem (N.inv_mem huN)]; exact hy
    obtain ⟨R1', hR1'⟩ := (HasRail.map_smul hX ⟨R1, hR1⟩ u)
    rw [hZ1n] at hR1'
    obtain ⟨hR0p, hR0Z, att0, hatt0, hdisj0⟩ := hR0
    obtain ⟨hR1p, hR1Z, att1, hatt1, hdisj1⟩ := hR1'
    let φ : Fin k → V := fun r => (K.equivFin.symm r : V)
    have hφK : ∀ r, φ r ∈ K := fun r => (K.equivFin.symm r).2
    have hφT0 : ∀ r, φ r ∈ T0 := fun r => (Finset.mem_filter.1 (hφK r)).1
    have hφinj : ∀ r r', φ r = φ r' → r = r' := by
      intro r r' h
      exact K.equivFin.symm.injective (Subtype.ext h)
    have hφB : ∀ r, fib N (φ r) = l[i] := fun r => hT0 _ (hφT0 r)
    have hmemT1' : ∀ r, e (φ r) ∈ T1.image (u • ·) := by
      intro r
      exact Finset.mem_image.2 ⟨_, (Finset.mem_filter.1 (hφK r)).2, by simp⟩
    have hinj : ∀ y : V, fib N y = l[i] → ∀ z ∈ Lf y, ∀ z' ∈ Lf y,
        fib N z = fib N z' → z = z' := by
      intro y hy
      have hnd : ((Lf y).map (fib N)).Nodup := by
        rw [(hLp y hy).2.1]; exact hl'path.2
      exact fun z hz z' hz' h => List.inj_on_of_nodup_map hnd hz hz' h
    have hproj : ∀ y : V, fib N y = l[i] → ∀ z ∈ Lf y, fib N z ∈ l' := by
      intro y hy z hz
      rw [← (hLp y hy).2.1]; exact List.mem_map_of_mem hz
    have hl0' : ∀ r, ∀ z ∈ Lf (φ r), z ∈ Z0 → z = φ r := by
      intro r z hz hz0
      have := (hl'W _ (hproj _ (hφB r) z hz)).1 hz0
      exact hinj _ (hφB r) z hz _ (List.mem_of_head? (hLp _ (hφB r)).2.2) (by rw [this, hφB r])
    have hl1' : ∀ r, ∀ z ∈ Lf (φ r), z ∈ Z1 → z = e (φ r) := by
      intro r z hz hz1
      have := (hl'W _ (hproj _ (hφB r) z hz)).2 hz1
      exact hinj _ (hφB r) z hz _ (List.mem_of_getLast? (hLlast _ (hφB r)))
        (by rw [this, hLend _ (hφB r)])
    have hdl' : ∀ r r', r ≠ r' → (Lf (φ r)).Disjoint (Lf (φ r')) := by
      intro r r' hrr'
      exact hLdisj _ _ (by rw [hl'h]; exact hφB r) (by rw [hl'h]; exact hφB r')
        (fun h => hrr' (hφinj r r' h))
    obtain ⟨C, hC1, hC2, hC3, hC4, hC5, hC6, hC7⟩ := connectors (G := X) Z0 Z1 hZdisj R0 R1'
      hR0Z hR1Z φ (fun r => e (φ r)) (fun r => att0 (φ r)) (fun r => att1 (e (φ r)))
      (fun r => Lf (φ r)) (fun r => hatt0 _ (hφT0 r)) (fun r => hatt1 _ (hmemT1' r))
      (fun r => (hLp _ (hφB r)).1) (fun r => (hLp _ (hφB r)).2.2) (fun r => hLlast _ (hφB r))
      hl0' hl1'
      (fun r r' hrr' => hdisj0 _ (hφT0 r) _ (hφT0 r') (fun h => hrr' (hφinj r r' h)))
      (fun r r' hrr' => hdisj1 _ (hmemT1' r) _ (hmemT1' r')
        (fun h => hrr' (hφinj r r' (by
          have h1 := hLdisj (φ r) (φ r') (by rw [hl'h]; exact hφB r) (by rw [hl'h]; exact hφB r')
          by_contra hne
          exact h1 hne (List.mem_of_getLast? (hLlast _ (hφB r)))
            (h ▸ List.mem_of_getLast? (hLlast _ (hφB r'))))))) hdl'
    clear_value φ e K k Z0 Z1 W0 W1 l' x c b p Y
    have hT0c : τ ≤ T0.card := hτT0
    have hT1c : τ ≤ T1.card := hτT1
    have hkm : τ ^ 2 ≤ k * m := by
      calc τ ^ 2 = τ * τ := by ring
        _ ≤ T0.card * T1.card := Nat.mul_le_mul hT0c hT1c
        _ ≤ k * m := hn
    have hk1 : 1 ≤ k := by
      refine Nat.pos_of_ne_zero (fun h => ?_)
      rw [h, zero_mul] at hkm
      have : 0 < τ ^ 2 := by positivity
      omega
    obtain ⟨l2, hl2, hl2len⟩ := htr X R0 R1' k C (j - i) hk1 hR0p hR1p
      (fun y h0 h1 => Set.disjoint_left.1 hZdisj (hR0Z y h0) (hR1Z y h1)) hC1 hC2 hC3 hC4 hC5 hC6
      (fun r => by have := hC7 r; rw [hLlen _ (hφB r)] at this; exact this)
    have hxk : x ≤ k := by
      rw [hx, div_le_iff₀ (by exact_mod_cast hm0)]; exact_mod_cast hkm
    have hD : (p : ℝ) / (8 * (b : ℝ) ^ 2) ≤ ((j - i : ℕ) : ℝ) := by
      rw [Nat.cast_sub hij.le]
      have := hfar; rw [hlen] at this; rw [hp, hb]; exact this.le
    have hc8 : c ≤ a / 8 := by rw [hc]; exact min_le_left _ _
    have hxpow : x ^ (1 - η) ≤ (k : ℝ) ^ (1 - η) :=
      Real.rpow_le_rpow hx0 hxk (by linarith)
    calc c * x ^ (1 - η) * (p : ℝ) / (b : ℝ) ^ 2
          ≤ (a / 8) * x ^ (1 - η) * (p : ℝ) / (b : ℝ) ^ 2 := by gcongr
      _ = a * ((p : ℝ) / (8 * (b : ℝ) ^ 2)) * x ^ (1 - η) := by
          field_simp
      _ ≤ a * ((j - i : ℕ) : ℝ) * (k : ℝ) ^ (1 - η) := by gcongr
      _ ≤ (l2.length : ℝ) - 1 := hl2len
      _ ≤ pathOrder X := by linarith [hXp l2 hl2]
  · push_neg at hpb
    obtain ⟨w, hw⟩ := hWne
    obtain ⟨T, hT', hτT, hTr⟩ := hrail 1 (1 • w) (Finset.mem_image_of_mem _ hw)
    have hτX : (τ : ℝ) ≤ pathOrder X := by
      exact_mod_cast hτT.trans hTr.card_le_pathOrder
    have hτm : τ ≤ m := by
      refine hτT.trans ?_
      rcases T.eq_empty_or_nonempty with h | ⟨t0, ht0⟩
      · rw [h]; exact Nat.zero_le _
      · rw [← hm t0]
        exact Finset.card_le_card fun t ht => mem_orb.2 ((hT' t ht).trans (hT' t0 ht0).symm)
    have hxτ : x ^ (1 - η) ≤ τ := by
      rcases le_or_gt x 1 with h | h
      · exact (Real.rpow_le_one hx0 h (by linarith)).trans (by exact_mod_cast hτ)
      · calc x ^ (1 - η) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h.le (by linarith)
          _ = x := Real.rpow_one x
          _ ≤ τ := by
            rw [hx, div_le_iff₀ (by exact_mod_cast hm0)]
            have : (τ : ℝ) ≤ m := by exact_mod_cast hτm
            have : (0 : ℝ) ≤ τ := by positivity
            nlinarith
    have hpb' : (p : ℝ) / (b : ℝ) ^ 2 ≤ 16 := by
      rw [div_le_iff₀ (by positivity)]; exact_mod_cast hpb
    have hc16 : c ≤ 1 / 16 := min_le_right _ _
    calc c * x ^ (1 - η) * (p : ℝ) / (b : ℝ) ^ 2
          = c * x ^ (1 - η) * ((p : ℝ) / (b : ℝ) ^ 2) := by ring
      _ ≤ (1 / 16) * (τ : ℝ) * 16 := by gcongr
      _ = τ := by ring
      _ ≤ _ := hτX

/-- **Theorem A.9** (fibre lifting for a transitive action). Fix `0 < η < 1`. There is
`c > 0` such that: if a finite group `Γ` acts transitively by automorphisms on a finite graph
`X`, `N ◁ Γ` has all orbits of size `m ≥ 2`, and any two vertices of the same `N`-orbit are
joined by a walk with at most `R ≥ 1` edges, then with `Y = X/N`,
`p(X) ≥ c m^(1-η) p(Y) / (R log (2m))⁴`. -/
theorem fibre_lifting_vt (h12 : CycleMatchingTheorem) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ (V Γ : Type) [Group Γ] [MulAction Γ V] [Fintype V] [Fintype Γ]
      (X : SimpleGraph V) (N : Subgroup Γ) [N.Normal] (m R : ℕ), ActsOn X Γ → TransOn Γ V →
      (∀ v : V, (orb N v).card = m) → 2 ≤ m → 1 ≤ R →
      (∀ u v : V, fib N u = fib N v → WalkLe X Set.univ u v R) →
      c * (m : ℝ) ^ (1 - η) * pathOrder (quotGraph X N) / ((R : ℝ) * Real.log (2 * m)) ^ 4 ≤
        pathOrder X := by
  obtain ⟨c0, hc0, hcor⟩ := corridor_vt h12 η hη0 hη1
  refine ⟨c0 / (256 * 20 ^ 4), by positivity, fun V Γ _ _ _ _ X N _ m R hX hT hm hm2 hR hwalk => ?_⟩
  rcases isEmpty_or_nonempty V with hV | ⟨⟨x0⟩⟩
  · have h0 : pathOrder X = 0 := by
      have := pathOrder_le_card X
      rw [Fintype.card_eq_zero] at this; omega
    have h1 : pathOrder (quotGraph X N) = 0 := by
      have := pathOrder_quotGraph_le hX N hm; omega
    rw [h0, h1]; simp
  obtain ⟨Z, hx0Z, hZinv, hWcard, hdiam⟩ := window_vt hX N hm R hR hwalk x0
  set L := (4 * Nat.log 2 m + 6) * R with hL
  set W := Z.image (fib N) with hW
  set τ := ⌈(m : ℝ) / (16 * (L + 1))⌉₊ with hτ
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  have hτ1 : 1 ≤ τ := Nat.one_le_iff_ne_zero.2 (by
    rw [hτ, ne_eq, Nat.ceil_eq_zero, not_le]; positivity)
  have hWne : W.Nonempty := ⟨_, Finset.mem_image_of_mem _ hx0Z⟩
  have hZmem : ∀ y : V, y ∈ Z ↔ fib N y ∈ W := by
    intro y
    constructor
    · intro hy; exact Finset.mem_image_of_mem _ hy
    · intro hy
      obtain ⟨z, hz, hzy⟩ := Finset.mem_image.1 hy
      obtain ⟨n, hn, rfl⟩ := fib_eq_iff.1 hzy.symm
      exact hZinv n hn z hz
  have hrail : ∀ g : Γ, ∀ B ∈ W.image (g • ·), ∃ T : Finset V,
      (∀ t ∈ T, fib N t = B) ∧ τ ≤ T.card ∧
      HasRail X {x | fib N x ∈ W.image (g • ·)} T := by
    intro g B hB
    obtain ⟨_, hz', rfl⟩ := Finset.mem_image.1 hB
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hz'
    obtain ⟨T0, hT0, hT0card, hT0rail⟩ := exists_rail_vt hX N hm Z L hdiam hZinv z hz
    refine ⟨T0.image (g • ·), ?_, ?_, ?_⟩
    · intro t ht
      obtain ⟨t0, ht0, rfl⟩ := Finset.mem_image.1 ht
      rw [← smul_fib, hT0 t0 ht0]
    · rw [Finset.card_image_of_injective _ (MulAction.injective g)]
      exact Nat.ceil_le.2 hT0card
    · have := hT0rail.map_smul hX g
      convert this using 1
      ext y
      simp only [Set.mem_setOf_eq, Finset.mem_image, Set.mem_image, Finset.mem_coe]
      constructor
      · rintro ⟨q, hq, hqy⟩
        refine ⟨g⁻¹ • y, (hZmem _).2 ?_, by simp⟩
        rw [← smul_fib, ← hqy, inv_smul_smul]; exact hq
      · rintro ⟨y', hy', rfl⟩
        exact ⟨fib N y', (hZmem y').1 hy', rfl⟩
  have hX' := hcor V Γ X N m hX hT hm W τ hWne hτ1 hrail
  have hb1 : (1 : ℝ) ≤ W.card := by exact_mod_cast hWne.card_pos
  have hbL : (W.card : ℝ) ≤ L + 1 := by
    have : W.card ≤ L := hWcard
    have : (W.card : ℝ) ≤ L := by exact_mod_cast this
    linarith
  have hLR := window_bound_le m R hm2 hR
  have hlg : 0 < Real.log (2 * m) := Real.log_pos (by linarith)
  exact lifting_arith m τ W.card L R _ _ _ c0 η hmR (by positivity) hb1 hbL
    (Nat.le_ceil _) (by rw [hL]; exact_mod_cast hLR) (by exact_mod_cast hR) hlg
    (by positivity) hc0 hη0 hη1 hX'

end Lovasz
