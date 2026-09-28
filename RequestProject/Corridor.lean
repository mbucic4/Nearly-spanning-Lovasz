module
public import RequestProject.TwoRailsLemma

/-!
# Corridors between two windows (Lemmas 3.7, 3.8 and the common core of 3.9 / 3.12)
-/

@[expose] public section


open Classical

namespace Lovasz

/-- **Lemma 3.7** (two windows on a long path), for the regular action of a finite group `Q`
on itself.  If `W ∋ w` has `b` elements and `l` is a list of `p > 16 b²` distinct elements,
there are disjoint translates `W₀ = g₀ W`, `W₁ = g₁ W` and indices `i < j` such that `l[i] ∈ W₀`,
`l[j] ∈ W₁`, no entry strictly between them lies in `W₀ ∪ W₁`, and `j - i > p / (8 b²)`. -/
theorem two_windows {Q : Type*} [Group Q] [DecidableEq Q] (W : Finset Q) (w : Q) (hw : w ∈ W)
    (l : List Q) (hl : l.Nodup) (hp : 16 * W.card ^ 2 < l.length) :
    ∃ g₀ g₁ : Q, Disjoint (W.image (g₀ * ·)) (W.image (g₁ * ·)) ∧
      ∃ i j : ℕ, ∃ hij : i < j, ∃ hj : j < l.length,
        l[i] ∈ W.image (g₀ * ·) ∧ l[j] ∈ W.image (g₁ * ·) ∧
        (∀ k (hk : k < l.length), i < k → k < j →
          l[k] ∉ W.image (g₀ * ·) ∧ l[k] ∉ W.image (g₁ * ·)) ∧
        (l.length : ℝ) / (8 * W.card ^ 2) < (j : ℝ) - i := by
  set p := l.length with hpdef
  set b := W.card with hbdef
  have hb : 1 ≤ b := Finset.card_pos.2 ⟨w, hw⟩
  have hp0 : 0 < p := lt_of_le_of_lt (Nat.zero_le _) hp
  set f : ℕ → Q := fun k => l.getD k 1 with hfdef
  have hf : ∀ k (hk : k < p), f k = l[k] := fun k hk => List.getD_eq_getElem _ _ hk
  have hfinj : ∀ i j, i < p → j < p → f i = f j → i = j := by
    intro i j hi hj h
    rw [hf i hi, hf j hj] at h
    exact (List.Nodup.getElem_inj_iff hl).1 h
  set g0 := f 0 * w⁻¹ with hg0
  set W0 := W.image (g0 * ·) with hW0
  have h0W0 : f 0 ∈ W0 := Finset.mem_image.2 ⟨w, hw, by simp [g0]⟩
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
  set bad := W.biUnion (fun x => F.image (· * x⁻¹)) with hbaddef
  have hbad : bad.card ≤ b * F.card := by
    refine Finset.card_biUnion_le.trans ?_
    calc ∑ x ∈ W, (F.image (· * x⁻¹)).card ≤ ∑ _x ∈ W, F.card := by
          apply Finset.sum_le_sum; intro x _; exact Finset.card_image_le
      _ = b * F.card := by simp [b]
  set G := (Finset.range p).image (fun i => f i * w⁻¹) with hGdef
  have hG : G.card = p := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj h
    exact hfinj i j (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) (mul_right_cancel h)
  have hlt : bad.card < G.card := by
    rw [hG]
    have h1 : 8 * b ^ 2 * r ≤ p := by rw [mul_comm]; exact Nat.div_mul_le_self p _
    have h2 : b * (b + b * (2 * r + 1)) = 2 * (b ^ 2 * r) + 2 * b ^ 2 := by ring
    have h3 : b * F.card ≤ b * (b + b * (2 * r + 1)) := Nat.mul_le_mul_left _ hF
    have h4 : 8 * b ^ 2 * r = 8 * (b ^ 2 * r) := by ring
    omega
  obtain ⟨g1, hg1G, hg1bad⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hW1F : ∀ x ∈ W, g1 * x ∉ F := fun x hx hxF =>
    hg1bad (Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_image.2 ⟨g1 * x, hxF, by simp⟩⟩)
  set W1 := W.image (g1 * ·) with hW1
  have hdisj : Disjoint W0 W1 := by
    rw [Finset.disjoint_left]
    intro a ha ha1
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha1
    exact hW1F x hx (Finset.mem_union_left _ ha)
  obtain ⟨i1, hi1, hg1⟩ := Finset.mem_image.1 hg1G
  have hi1W1 : f i1 ∈ W1 := Finset.mem_image.2 ⟨w, hw, by rw [← hg1]; simp⟩
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

variable {H : Type*} [Group H]

/-- **Lemma 3.8** (lifts of quotient paths). A path `l` in `Cay(H/N, S)` has a lift starting
at every vertex `x` of its initial coset, namely `x · ps` for a fixed list `ps`; these lifts
are paths in `Cay(H, S)` projecting onto `l`. -/
theorem lift_path (S : Set H) (N : Subgroup H) [N.Normal] (l : List (H ⧸ N))
    (hl : IsPathL (cay ((QuotientGroup.mk : H → H ⧸ N) '' S)) l) (hne : l ≠ []) :
    ∃ ps : List H, ps.length = l.length ∧ ps.head? = some 1 ∧
      ∀ x : H, (x : H ⧸ N) = l.head hne →
        IsPathL (cay S) (ps.map (x * ·)) ∧
          (ps.map (x * ·)).map (QuotientGroup.mk : H → H ⧸ N) = l := by
  induction l with
  | nil => exact absurd rfl hne
  | cons b l ih =>
    cases l with
    | nil =>
      refine ⟨[1], rfl, rfl, fun x hx => ⟨by simpa using isPathL_singleton (G := cay S) x, ?_⟩⟩
      simpa using hx
    | cons b' rest =>
      have hl' : IsPathL (cay ((QuotientGroup.mk : H → H ⧸ N) '' S)) (b' :: rest) :=
        hl.suffix (List.suffix_cons _ _)
      obtain ⟨ps', hlen', hhead', hps'⟩ := ih hl' (List.cons_ne_nil _ _)
      obtain ⟨x0, rfl⟩ := QuotientGroup.mk_surjective b
      have hadj := (List.isChain_cons_cons.1 hl.1).1
      obtain ⟨s, hs, hsadj⟩ := cay_quot_adj_lift N hadj
      refine ⟨1 :: ps'.map (s * ·), by simp [hlen'], rfl, fun x hx => ?_⟩
      have hx' : (x : H ⧸ N) = x0 := by simpa using hx
      have hxs : ((x * s : H) : H ⧸ N) = b' := by
        rw [hs, QuotientGroup.mk_mul, QuotientGroup.mk_mul, hx']
      obtain ⟨hP, hproj⟩ := hps' (x * s) (by simpa using hxs)
      have heq : (1 :: ps'.map (s * ·)).map (x * ·) = x :: ps'.map ((x * s) * ·) := by
        simp [Function.comp_def, mul_assoc]
      rw [heq]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · cases ps' with
        | nil => simp at hhead'
        | cons p ps'' =>
          simp only [List.head?_cons, Option.some.injEq] at hhead'
          subst hhead'
          simp only [List.map_cons, mul_one]
          refine List.IsChain.cons_cons (hsadj x hx') ?_
          simpa using hP.1
      · refine List.nodup_cons.2 ⟨?_, hP.2⟩
        intro hmem
        have : (x : H ⧸ N) ∈ (ps'.map ((x * s) * ·)).map (QuotientGroup.mk : H → H ⧸ N) :=
          List.mem_map_of_mem hmem
        rw [hproj, hx'] at this
        exact (List.nodup_cons.1 hl.2).1 this
      · simp only [List.map_cons, hx']
        rw [hproj]

/-- Every path in the quotient lifts to a path of the same order, so `p(X) ≥ p(Y)`. -/
theorem pathOrder_quot_le [Finite H] (S : Set H) (N : Subgroup H) [N.Normal] :
    pathOrder (cay ((QuotientGroup.mk : H → H ⧸ N) '' S)) ≤ pathOrder (cay S) := by
  obtain ⟨l, hl, hlen⟩ := exists_isPathL_length_eq_pathOrder
    (cay ((QuotientGroup.mk : H → H ⧸ N) '' S))
  rw [← hlen]
  by_cases hne : l = []
  · simp [hne]
  obtain ⟨ps, hps, -, hlift⟩ := lift_path S N l hl hne
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (l.head hne)
  obtain ⟨hP, -⟩ := hlift x hx
  calc l.length = (ps.map (x * ·)).length := by simp [hps]
    _ ≤ pathOrder (cay S) := hP.length_le_pathOrder

lemma card_le_of_coset [Finite H] (N : Subgroup H) (T : Finset H) (B : H ⧸ N)
    (hT : ∀ t ∈ T, (t : H ⧸ N) = B) : T.card ≤ Nat.card N := by
  have := Fintype.ofFinite N
  rcases T.eq_empty_or_nonempty with rfl | ⟨t0, ht0⟩
  · simp
  let f : H → N := fun t => if h : t0⁻¹ * t ∈ N then ⟨_, h⟩ else 1
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
  refine Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _) ?_
  intro x hx y hy hxy
  have hx' : t0⁻¹ * x ∈ N := QuotientGroup.eq.1 ((hT t0 ht0).trans (hT x hx).symm)
  have hy' : t0⁻¹ * y ∈ N := QuotientGroup.eq.1 ((hT t0 ht0).trans (hT y hy).symm)
  simp only [f, dif_pos hx', dif_pos hy', Subtype.mk.injEq] at hxy
  exact mul_left_cancel hxy

lemma exists_good_shift [Finite H] (N : Subgroup H) [N.Normal] (T0 T1 : Finset H) (s : H)
    (B1 : H ⧸ N) (hT1 : ∀ t ∈ T1, (t : H ⧸ N) = B1)
    (hT0s : ∀ x ∈ T0, ((x * s : H) : H ⧸ N) = B1) :
    ∃ n : N, T0.card * T1.card ≤
      (T0.filter (fun x => (n : H)⁻¹ * (x * s) ∈ T1)).card * Nat.card N := by
  have := Fintype.ofFinite N
  have hinner : ∀ x ∈ T0,
      (Finset.univ.filter (fun n : N => (n : H)⁻¹ * (x * s) ∈ T1)).card = T1.card := by
    intro x hx
    refine Finset.card_nbij' (fun n => (n : H)⁻¹ * (x * s))
      (fun t => if h : x * s * t⁻¹ ∈ N then ⟨_, h⟩ else 1) ?_ ?_ ?_ ?_
    · intro n hn; exact (Finset.mem_filter.1 hn).2
    · intro t ht
      have hmem : x * s * t⁻¹ ∈ N := by
        have h1 : t⁻¹ * (x * s) ∈ N :=
          QuotientGroup.eq.1 ((hT1 t ht).trans (hT0s x hx).symm)
        have := ‹N.Normal›.conj_mem _ h1 t
        simpa [mul_assoc] using this
      simp only [Finset.coe_filter, Set.mem_setOf_eq, dif_pos hmem, Finset.mem_univ, true_and]
      simpa [mul_assoc] using ht
    · intro n hn
      have hmem : x * s * ((n : H)⁻¹ * (x * s))⁻¹ ∈ N := by simp [mul_assoc]
      simp only [dif_pos hmem]
      ext; simp [mul_assoc]
    · intro t ht
      have hmem : x * s * t⁻¹ ∈ N := by
        have h1 : t⁻¹ * (x * s) ∈ N :=
          QuotientGroup.eq.1 ((hT1 t (Finset.mem_coe.1 ht)).trans (hT0s x hx).symm)
        have := ‹N.Normal›.conj_mem _ h1 t
        simpa [mul_assoc] using this
      simp only [dif_pos hmem]
      simp [mul_assoc]
  have hsum : ∑ n : N, (T0.filter (fun x => (n : H)⁻¹ * (x * s) ∈ T1)).card =
      T0.card * T1.card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x hx => (Finset.card_filter _ _).symm.trans (hinner x hx)),
      Finset.sum_const, smul_eq_mul]
  obtain ⟨n, -, hn⟩ := Finset.exists_le_of_sum_le (s := Finset.univ)
    (f := fun _ : N => T0.card * T1.card)
    (g := fun n : N => (T0.filter (fun x => (n : H)⁻¹ * (x * s) ∈ T1)).card * Nat.card N)
    Finset.univ_nonempty (by
      show ∑ _n : N, T0.card * T1.card ≤
        ∑ n : N, (T0.filter (fun x => (n : H)⁻¹ * (x * s) ∈ T1)).card * Nat.card N
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Finset.sum_mul, hsum,
        Nat.card_eq_fintype_card]
      exact le_of_eq (by ring))
  exact ⟨n, hn⟩


/-- **Corridor lemma** (the common core of Theorem 3.9 and Lemma 3.12).  Let `W` be a set of
`b` cosets of `N ◁ H` such that above every translate of `W`, and for every coset `B` in that
translate, there is a rail with attachments from at least `τ` vertices of `B`.  Then
`p(X) ≥ c (τ²/m)^(1-η) p(Y) / b²`. -/
theorem corridor (h12 : CycleMatchingTheorem) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ (H : Type) [Group H] [Finite H] (S : Set H) (N : Subgroup H) [N.Normal]
      (W : Finset (H ⧸ N)) (τ : ℕ), W.Nonempty → 1 ≤ τ →
      (∀ g : H ⧸ N, ∀ B ∈ W.image (g * ·), ∃ T : Finset H,
          (∀ t ∈ T, (t : H ⧸ N) = B) ∧ τ ≤ T.card ∧
          HasRail (cay S) {x | (x : H ⧸ N) ∈ W.image (g * ·)} T) →
      c * ((τ : ℝ) ^ 2 / Nat.card N) ^ (1 - η) *
          pathOrder (cay ((QuotientGroup.mk : H → H ⧸ N) '' S)) / (W.card : ℝ) ^ 2 ≤
        pathOrder (cay S) := by
  obtain ⟨a, ha, htr⟩ := two_rails h12 η hη0
  refine ⟨min (a / 8) (1 / 16), lt_min (by positivity) (by norm_num), ?_⟩
  intro H _ _ S N _ W τ hWne hτ hrail
  set Y := cay ((QuotientGroup.mk : H → H ⧸ N) '' S) with hY
  set p := pathOrder Y with hp
  set b := W.card with hb
  set m := Nat.card N with hm
  have hm0 : 0 < m := Nat.card_pos
  have hb1 : 1 ≤ b := hWne.card_pos
  set c := min (a / 8) (1 / 16) with hc
  have hc0 : 0 < c := lt_min (by positivity) (by norm_num)
  have hX : ∀ l : List H, IsPathL (cay S) l → (l.length : ℝ) ≤ pathOrder (cay S) :=
    fun l hl => by exact_mod_cast hl.length_le_pathOrder
  set x := (τ : ℝ) ^ 2 / m with hx
  have hx0 : 0 ≤ x := by positivity
  by_cases hpb : 16 * b ^ 2 < p
  · obtain ⟨l, hl, hlen⟩ := exists_isPathL_length_eq_pathOrder Y
    obtain ⟨w, hw⟩ := hWne
    obtain ⟨g0, g1, hdisj, i, j, hij, hj, hi0, hj1, hbetw, hfar⟩ :=
      two_windows W w hw l hl.2 (by rw [hlen]; exact hpb)
    obtain ⟨hl'len, hl'head, hl'last, hl'mem⟩ := subpath_facts l i j hij.le hj
    set l' := (l.drop i).take (j - i + 1) with hl'
    have hl'path : IsPathL Y l' :=
      hl.infix ((List.take_prefix _ _).isInfix.trans (List.drop_suffix _ _).isInfix)
    set W0 := W.image (g0 * ·) with hW0
    set W1 := W.image (g1 * ·) with hW1
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
    obtain ⟨ps, hpslen, hpshead, hlift⟩ := lift_path S N l' hl'path hne'
    have hl'h : l'.head hne' = l[i] := by
      have := List.head?_eq_some_head hne'; rw [hl'head] at this
      exact (Option.some.inj this).symm
    have hps_ne : ps ≠ [] := by
      intro h; rw [h] at hpslen; simp at hpslen; omega
    set sf := ps.getLast hps_ne with hsf
    set L : H → List H := fun x => ps.map (x * ·) with hL
    have hLhead : ∀ x, (L x).head? = some x := by
      intro x; simp [L, List.head?_map, hpshead]
    have hLlast : ∀ x, (L x).getLast? = some (x * sf) := by
      intro x; simp [L, List.getLast?_map, List.getLast?_eq_some_getLast hps_ne, sf]
    have hLlen : ∀ x, (L x).length = j - i + 1 := by
      intro x; simp [L, hpslen, hl'len]
    have hLp : ∀ x : H, (x : H ⧸ N) = l[i] →
        IsPathL (cay S) (L x) ∧ (L x).map (QuotientGroup.mk : H → H ⧸ N) = l' := by
      intro x hx; exact hlift x (by rw [hl'h]; exact hx)
    have hLend : ∀ x : H, (x : H ⧸ N) = l[i] → ((x * sf : H) : H ⧸ N) = l[j] := by
      intro x hx
      have h1 := congrArg List.getLast? (hLp x hx).2
      rw [List.getLast?_map, hLlast, hl'last] at h1
      exact Option.some.inj h1
    -- the two rails
    obtain ⟨T0, hT0, hτT0, R0, hR0⟩ := hrail g0 l[i] hi0
    obtain ⟨T1, hT1, hτT1, R1, hR1⟩ := hrail g1 l[j] hj1
    set Z0 : Set H := {x | (x : H ⧸ N) ∈ W0} with hZ0
    set Z1 : Set H := {x | (x : H ⧸ N) ∈ W1} with hZ1
    have hZdisj : Disjoint Z0 Z1 :=
      Set.disjoint_left.2 fun y h0 h1 => Finset.disjoint_left.1 hdisj h0 h1
    obtain ⟨n, hn⟩ := exists_good_shift N T0 T1 sf l[j] hT1
      (fun x hx => hLend x (hT0 x hx))
    set K := T0.filter (fun x => (n : H)⁻¹ * (x * sf) ∈ T1) with hK
    set k := K.card with hk
    have hZ1n : ((n : H) * ·) '' Z1 = Z1 := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        show ((n * z : H) : H ⧸ N) ∈ W1
        rw [mk_mul_left_of_mem N n.2]; exact hz
      · intro hy
        refine ⟨(n : H)⁻¹ * y, ?_, by simp⟩
        show (((n : H)⁻¹ * y : H) : H ⧸ N) ∈ W1
        rw [mk_mul_left_of_mem N (N.inv_mem n.2)]; exact hy
    obtain ⟨R1', hR1'⟩ := (HasRail.map_mul_left ⟨R1, hR1⟩ (n : H))
    rw [hZ1n] at hR1'
    obtain ⟨hR0p, hR0Z, att0, hatt0, hdisj0⟩ := hR0
    obtain ⟨hR1p, hR1Z, att1, hatt1, hdisj1⟩ := hR1'
    let φ : Fin k → H := fun r => (K.equivFin.symm r : H)
    have hφK : ∀ r, φ r ∈ K := fun r => (K.equivFin.symm r).2
    have hφT0 : ∀ r, φ r ∈ T0 := fun r => (Finset.mem_filter.1 (hφK r)).1
    have hφinj : ∀ r r', φ r = φ r' → r = r' := by
      intro r r' h
      exact K.equivFin.symm.injective (Subtype.ext h)
    have hφB : ∀ r, ((φ r : H) : H ⧸ N) = l[i] := fun r => hT0 _ (hφT0 r)
    have hmemT1' : ∀ r, φ r * sf ∈ T1.image ((n : H) * ·) := by
      intro r
      exact Finset.mem_image.2 ⟨_, (Finset.mem_filter.1 (hφK r)).2, by simp⟩
    have hinj : ∀ x : H, (x : H ⧸ N) = l[i] → ∀ y ∈ L x, ∀ y' ∈ L x,
        (y : H ⧸ N) = (y' : H ⧸ N) → y = y' := by
      intro x hx
      have hnd : ((L x).map (QuotientGroup.mk : H → H ⧸ N)).Nodup := by
        rw [(hLp x hx).2]; exact hl'path.2
      exact fun y hy y' hy' h => List.inj_on_of_nodup_map hnd hy hy' h
    have hproj : ∀ x : H, (x : H ⧸ N) = l[i] → ∀ y ∈ L x, (y : H ⧸ N) ∈ l' := by
      intro x hx y hy
      rw [← (hLp x hx).2]; exact List.mem_map_of_mem hy
    have hl0' : ∀ r, ∀ y ∈ L (φ r), y ∈ Z0 → y = φ r := by
      intro r y hy hy0
      have := (hl'W _ (hproj _ (hφB r) y hy)).1 hy0
      exact hinj _ (hφB r) y hy _ (List.mem_of_head? (hLhead _)) (by rw [this, hφB r])
    have hl1' : ∀ r, ∀ y ∈ L (φ r), y ∈ Z1 → y = φ r * sf := by
      intro r y hy hy1
      have := (hl'W _ (hproj _ (hφB r) y hy)).2 hy1
      exact hinj _ (hφB r) y hy _ (List.mem_of_getLast? (hLlast _))
        (by rw [this, hLend _ (hφB r)])
    have hdl' : ∀ r r', r ≠ r' → (L (φ r)).Disjoint (L (φ r')) := by
      intro r r' hrr' y hy hy'
      obtain ⟨p1, hp1, rfl⟩ := List.mem_map.1 hy
      obtain ⟨p2, hp2, he⟩ := List.mem_map.1 hy'
      have hm : ((φ r' * p1 : H) : H ⧸ N) = ((φ r * p1 : H) : H ⧸ N) := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hφB r, hφB r']
      have h1 : φ r' * p1 ∈ L (φ r') := List.mem_map_of_mem (f := (φ r' * ·)) hp1
      have h2 : φ r' * p2 ∈ L (φ r') := List.mem_map_of_mem (f := (φ r' * ·)) hp2
      have := hinj _ (hφB r') _ h1 _ h2 (by rw [hm]; exact congrArg _ he.symm)
      have hp12 : p1 = p2 := mul_left_cancel this
      subst hp12
      exact hrr' (hφinj r r' (mul_right_cancel he).symm)
    obtain ⟨C, hC1, hC2, hC3, hC4, hC5, hC6, hC7⟩ := connectors (G := cay S) Z0 Z1 hZdisj R0 R1'
      hR0Z hR1Z φ (fun r => φ r * sf) (fun r => att0 (φ r)) (fun r => att1 (φ r * sf))
      (fun r => L (φ r)) (fun r => hatt0 _ (hφT0 r)) (fun r => hatt1 _ (hmemT1' r))
      (fun r => (hLp _ (hφB r)).1) (fun r => hLhead _) (fun r => hLlast _) hl0' hl1'
      (fun r r' hrr' => hdisj0 _ (hφT0 r) _ (hφT0 r') (fun h => hrr' (hφinj r r' h)))
      (fun r r' hrr' => hdisj1 _ (hmemT1' r) _ (hmemT1' r')
        (fun h => hrr' (hφinj r r' (mul_right_cancel h)))) hdl'
    clear_value φ L sf K k Z0 Z1 W0 W1 l' x c m b p Y
    have hT0c : τ ≤ T0.card := hτT0
    have hT1c : τ ≤ T1.card := hτT1
    have hkm : τ ^ 2 ≤ k * m := by
      calc τ ^ 2 = τ * τ := by ring
        _ ≤ T0.card * T1.card := Nat.mul_le_mul hT0c hT1c
        _ ≤ k * m := by rw [hm]; exact hn
    have hk1 : 1 ≤ k := by
      refine Nat.pos_of_ne_zero (fun h => ?_)
      rw [h, zero_mul] at hkm
      have : 0 < τ ^ 2 := by positivity
      omega
    obtain ⟨l2, hl2, hl2len⟩ := htr (cay S) R0 R1' k C (j - i) hk1 hR0p hR1p
      (fun y h0 h1 => Set.disjoint_left.1 hZdisj (hR0Z y h0) (hR1Z y h1)) hC1 hC2 hC3 hC4 hC5 hC6
      (fun r => by have := hC7 r; rw [hLlen] at this; exact this)
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
      _ ≤ pathOrder (cay S) := by linarith [hX l2 hl2]
  · push_neg at hpb
    obtain ⟨w, hw⟩ := hWne
    obtain ⟨T, hT, hτT, hTr⟩ := hrail 1 (1 * w) (Finset.mem_image_of_mem _ hw)
    have hτX : (τ : ℝ) ≤ pathOrder (cay S) := by
      exact_mod_cast hτT.trans hTr.card_le_pathOrder
    have hτm : τ ≤ m := hτT.trans (card_le_of_coset N T _ hT)
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

end Lovasz
