module
public import RequestProject.Rails

/-!
# Small windows above a coset (Lemmas 3.2 and 3.3)
-/

@[expose] public section


open Classical

namespace Lovasz

variable {H : Type*} [Group H]

/-- **Lemma 3.2.** If `A ⊆ N` with `1 ≤ |A| ≤ |N|/2`, some `t ∈ N` has `|At \ A| ≥ |A|/2`. -/
theorem exists_translate_large [Finite H] (N : Subgroup H) (A : Finset H)
    (hA : ∀ a ∈ A, a ∈ N) (h1 : 1 ≤ A.card) (h2 : 2 * A.card ≤ Nat.card N) :
    ∃ t ∈ N, (A.card : ℝ) / 2 ≤ ((A.image (· * t)) \ A).card := by
  have := Fintype.ofFinite H
  set Nf : Finset H := Finset.univ.filter (· ∈ N) with hNf
  have hNcard : Nf.card = Nat.card N := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
    simp [hNf]
  have hcnt : ∀ t, ((A.image (· * t)) \ A).card = (A.filter (fun a => a * t ∉ A)).card := by
    intro t
    have : (A.image (· * t)) \ A = (A.filter (fun a => a * t ∉ A)).image (· * t) := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_image, Finset.mem_filter]; aesop
    rw [this, Finset.card_image_of_injective _ (mul_left_injective t)]
  have hrow : ∀ a ∈ A, (Nf.filter (fun t => a * t ∈ A)).card = A.card := by
    intro a ha
    refine Finset.card_bij (fun t _ => a * t) ?_ ?_ ?_
    · intro t ht; exact (Finset.mem_filter.1 ht).2
    · intro t _ t' _ h; exact mul_left_cancel h
    · intro b hb
      refine ⟨a⁻¹ * b, Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _,
        N.mul_mem (N.inv_mem (hA a ha)) (hA b hb)⟩, by simpa using hb⟩, by simp⟩
  have hsum : ∑ t ∈ Nf, ((A.image (· * t)) \ A).card = A.card * (Nat.card N - A.card) := by
    simp_rw [hcnt, Finset.card_filter]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (g := fun _ => Nat.card N - A.card)]
    · simp
    intro a ha
    rw [← Finset.card_filter, ← hNcard, ← hrow a ha]
    have := Finset.card_filter_add_card_filter_not (s := Nf) (fun t => a * t ∈ A)
    omega
  by_contra hcon
  push_neg at hcon
  have hlt : ∑ t ∈ Nf, (((A.image (· * t)) \ A).card : ℝ) < ∑ t ∈ Nf, (A.card : ℝ) / 2 := by
    apply Finset.sum_lt_sum_of_nonempty
    · exact ⟨1, Finset.mem_filter.2 ⟨Finset.mem_univ _, N.one_mem⟩⟩
    · intro t ht; exact hcon t (Finset.mem_filter.1 ht).2
  rw [← Nat.cast_sum, hsum, Finset.sum_const, hNcard, nsmul_eq_mul] at hlt
  have : A.card ≤ Nat.card N := by omega
  push_cast [this] at hlt
  have : (2 * A.card : ℝ) ≤ Nat.card N := by exact_mod_cast h2
  have : (1 : ℝ) ≤ A.card := by exact_mod_cast h1
  nlinarith

/-- The subproducts `t₁^{e₁} ⋯ t_r^{e_r}` (`eᵢ ∈ {0,1}`) of a list of group elements. -/
noncomputable def subprods : List H → Finset H
  | [] => {1}
  | t :: l => subprods l ∪ (subprods l).image (· * t)

lemma one_mem_subprods : ∀ l : List H, (1 : H) ∈ subprods l
  | [] => by simp [subprods]
  | t :: l => by simp only [subprods]; exact Finset.mem_union_left _ (one_mem_subprods l)

lemma subprods_mem {N : Subgroup H} :
    ∀ (l : List H), (∀ t ∈ l, t ∈ N) → ∀ a ∈ subprods l, a ∈ N
  | [], _, a, ha => by simp [subprods] at ha; subst ha; exact N.one_mem
  | t :: l, hl, a, ha => by
    simp only [subprods, Finset.mem_union, Finset.mem_image] at ha
    rcases ha with ha | ⟨b, hb, rfl⟩
    · exact subprods_mem l (fun x hx => hl x (by simp [hx])) a ha
    · exact N.mul_mem (subprods_mem l (fun x hx => hl x (by simp [hx])) b hb) (hl t (by simp))

/-- Iterating Lemma 3.2: after `i` steps the set of subproducts either has more than `m/2`
elements or at least `(3/2)^i` elements. -/
lemma exists_subprods_large [Finite H] (N : Subgroup H) (i : ℕ) :
    ∃ l : List H, (∀ t ∈ l, t ∈ N) ∧ l.length ≤ i ∧
      (Nat.card N < 2 * (subprods l).card ∨ ((3:ℝ) / 2) ^ i ≤ (subprods l).card) := by
  induction i with
  | zero => exact ⟨[], by simp, le_rfl, Or.inr (by simp [subprods])⟩
  | succ i ih =>
    obtain ⟨l, hlN, hlen, h⟩ := ih
    by_cases hbig : Nat.card N < 2 * (subprods l).card
    · exact ⟨l, hlN, by omega, Or.inl hbig⟩
    · rcases h with h | h
      · exact absurd h hbig
      push_neg at hbig
      have h1 : 1 ≤ (subprods l).card := Finset.card_pos.2 ⟨1, one_mem_subprods l⟩
      obtain ⟨t, htN, ht⟩ := exists_translate_large N (subprods l) (subprods_mem l hlN) h1 hbig
      refine ⟨t :: l, ?_, by simp; omega, Or.inr ?_⟩
      · intro x hx; simp at hx; rcases hx with rfl | hx; exact htN; exact hlN x hx
      · simp only [subprods]
        have : (subprods l ∪ (subprods l).image (· * t)).card =
            (subprods l).card + ((subprods l).image (· * t) \ subprods l).card := by
          rw [← Finset.card_union_of_disjoint Finset.disjoint_sdiff,
            Finset.union_sdiff_self_eq_union]
        rw [this]; push_cast; rw [pow_succ]; nlinarith

/-- Subproducts are realised by walks built from translates of the walks `1 → t`. -/
lemma subprods_walk (S : Set H) (N : Subgroup H) (Z : Set H)
    (hZ : ∀ n ∈ N, ∀ z ∈ Z, n * z ∈ Z) (h1 : (1 : H) ∈ Z) (R : ℕ) :
    ∀ l : List H, (∀ t ∈ l, t ∈ N) → (∀ t ∈ l, WalkLe (cay S) Z 1 t R) →
      ∀ a ∈ subprods l, ∀ n ∈ N, WalkLe (cay S) Z n (n * a) (l.length * R)
  | [], _, _, a, ha, n, hn => by
    simp [subprods] at ha; subst ha
    simpa using WalkLe.refl (G := cay S) (by simpa using hZ n hn 1 h1) 0
  | t :: l, hlN, hlw, a, ha, n, hn => by
    have hlN' : ∀ x ∈ l, x ∈ N := fun x hx => hlN x (by simp [hx])
    have hlw' : ∀ x ∈ l, WalkLe (cay S) Z 1 x R := fun x hx => hlw x (by simp [hx])
    simp only [subprods, Finset.mem_union, Finset.mem_image] at ha
    rcases ha with ha | ⟨b, hb, rfl⟩
    · exact (subprods_walk S N Z hZ h1 R l hlN' hlw' a ha n hn).mono_len
        (by simp [Nat.succ_mul])
    · have h₁ := subprods_walk S N Z hZ h1 R l hlN' hlw' b hb n hn
      have hnb : n * b ∈ N := N.mul_mem hn (subprods_mem l hlN' b hb)
      have h₂ := (hlw t (by simp)).map_mul_left_of_inv (n * b) (hZ _ hnb)
      rw [mul_one] at h₂
      have := h₁.trans h₂
      rw [mul_assoc] at this
      exact this.mono_len (by simp [Nat.succ_mul])

/-- **Lemma 3.3** (window). Let `N ◁ H`, and suppose any two elements of the same coset of `N`
are joined by a walk in `cay S` with at most `R ≥ 1` edges.  Then there is a union `Z` of
cosets of `N`, containing `N`, consisting of at most `L` cosets, such that any two vertices of
`Z` are joined by a walk inside `Z` with at most `L` edges, where `L = (4 ⌊log₂ m⌋ + 6) R`
and `m = |N|` (so `L ≤ C R log (2m)` when `m ≥ 2`, see `window_bound_le`). -/
theorem window [Finite H] (S : Set H) (N : Subgroup H) [N.Normal] (R : ℕ) (hR1 : 1 ≤ R)
    (hR : ∀ x y : H, (x : H ⧸ N) = y → WalkLe (cay S) Set.univ x y R) :
    ∃ Z : Finset H, (1 : H) ∈ Z ∧ (∀ n ∈ N, ∀ z ∈ Z, n * z ∈ Z) ∧
      (Z.image (QuotientGroup.mk : H → H ⧸ N)).card ≤ (4 * Nat.log 2 (Nat.card N) + 6) * R ∧
      ∀ u ∈ Z, ∀ v ∈ Z, WalkLe (cay S) Z u v ((4 * Nat.log 2 (Nat.card N) + 6) * R) := by
  have := Fintype.ofFinite H
  classical
  set m := Nat.card N with hm
  set j := Nat.log 2 m + 1 with hj
  obtain ⟨ts, htsN, htslen, hts⟩ := exists_subprods_large N (2 * j)
  have hbig : m < 2 * (subprods ts).card := by
    rcases hts with h | h
    · exact h
    have h2 : (m : ℝ) < 2 ^ j := by exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) m
    have h3 : (2 : ℝ) ^ j ≤ ((3 : ℝ) / 2) ^ (2 * j) := by
      rw [pow_mul]; gcongr; norm_num
    have : (m : ℝ) < 2 * (subprods ts).card := by
      have : (0 : ℝ) ≤ (subprods ts).card := by positivity
      linarith
    exact_mod_cast this
  -- the walks `γ t` from `1` to `t`
  have hγ : ∀ t ∈ ts, WalkLe (cay S) Set.univ 1 t R := fun t ht =>
    hR 1 t (by rw [QuotientGroup.mk_one]; exact ((QuotientGroup.eq_one_iff t).2 (htsN t ht)).symm)
  choose γ hγ' using hγ
  let γ' : H → List H := fun g => if hg : g ∈ ts then γ g hg else [1]
  have hγ'1 : ∀ g ∈ ts, (γ' g).IsChain (cay S).Adj ∧ (γ' g).head? = some 1 ∧
      (γ' g).getLast? = some g ∧ (γ' g).length ≤ R + 1 := by
    intro g hg
    simp only [γ', dif_pos hg]
    obtain ⟨h1, h2, h3, -, h5⟩ := hγ' g hg
    exact ⟨h1, h2, h3, h5⟩
  let V0 : Finset H := insert 1 (ts.toFinset.biUnion (fun g => (γ' g).toFinset))
  let Z : Finset H := Finset.univ.filter (fun z => ∃ v ∈ V0, z * v⁻¹ ∈ N)
  have hV0Z : ∀ v ∈ V0, v ∈ Z := fun v hv =>
    Finset.mem_filter.2 ⟨Finset.mem_univ _, v, hv, by simp [N.one_mem]⟩
  have hZinv : ∀ a ∈ N, ∀ z ∈ Z, a * z ∈ Z := by
    intro a ha z hz
    obtain ⟨-, v, hv, hzv⟩ := Finset.mem_filter.1 hz
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, v, hv, by
      rw [mul_assoc]; exact N.mul_mem ha hzv⟩
  have h1Z : (1 : H) ∈ Z := hV0Z 1 (Finset.mem_insert_self _ _)
  have hγZ : ∀ t ∈ ts, WalkLe (cay S) Z 1 t R := by
    intro t ht
    obtain ⟨h1, h2, h3, h4⟩ := hγ'1 t ht
    refine ⟨γ' t, h1, h2, h3, fun x hx => hV0Z x ?_, h4⟩
    exact Finset.mem_insert_of_mem (Finset.mem_biUnion.2
      ⟨t, List.mem_toFinset.2 ht, List.mem_toFinset.2 hx⟩)
  -- every vertex of `Z` is within `R` of `N`
  have hnear : ∀ u ∈ Z, ∃ n ∈ N, WalkLe (cay S) Z u n R := by
    intro u hu
    obtain ⟨-, v, hv, huv⟩ := Finset.mem_filter.1 hu
    refine ⟨u * v⁻¹, huv, ?_⟩
    have hv1 : WalkLe (cay S) Z 1 v R := by
      rcases Finset.mem_insert.1 hv with rfl | hv
      · exact WalkLe.refl h1Z R
      · obtain ⟨g, hg, hvg⟩ := Finset.mem_biUnion.1 hv
        have hg' := List.mem_toFinset.1 hg
        obtain ⟨h1, h2, -, h4⟩ := hγ'1 g hg'
        obtain ⟨l₁, l₂, hl⟩ := List.mem_iff_append.1 (List.mem_toFinset.1 hvg)
        have hpre : l₁ ++ [v] <+: γ' g := ⟨l₂, by rw [hl]; simp⟩
        refine ⟨l₁ ++ [v], h1.prefix hpre, ?_, by simp, fun x hx => hV0Z x ?_, ?_⟩
        · rw [← h2]
          cases l₁ with
          | nil => simp [hl]
          | cons a l₁ => simp [hl]
        · refine Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨g, hg, List.mem_toFinset.2 ?_⟩)
          exact hpre.subset hx
        · exact (hpre.length_le).trans h4
    have := (hv1.symm.map_mul_left_of_inv (u * v⁻¹) (hZinv _ huv))
    simpa using this
  refine ⟨Z, h1Z, hZinv, ?_, ?_⟩
  · -- counting cosets
    have himg : Z.image (QuotientGroup.mk : H → H ⧸ N) ⊆ V0.image QuotientGroup.mk := by
      intro q hq
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hq
      obtain ⟨-, v, hv, hzv⟩ := Finset.mem_filter.1 hz
      refine Finset.mem_image.2 ⟨v, hv, ?_⟩
      exact (mk_eq_of_mul_inv_mem N hzv).symm
    refine (Finset.card_le_card himg).trans ?_
    refine Finset.card_image_le.trans ?_
    have hsub : V0 ⊆ insert 1 (ts.toFinset.biUnion (fun g => (γ' g).tail.toFinset)) := by
      intro v hv
      rcases Finset.mem_insert.1 hv with rfl | hv
      · exact Finset.mem_insert_self _ _
      · obtain ⟨g, hg, hvg⟩ := Finset.mem_biUnion.1 hv
        obtain ⟨-, h2, -, -⟩ := hγ'1 g (List.mem_toFinset.1 hg)
        cases hc : γ' g with
        | nil => rw [hc] at h2; simp at h2
        | cons a l =>
          rw [hc] at h2 hvg
          simp only [List.head?_cons, Option.some.injEq] at h2
          subst h2
          rcases List.mem_cons.1 (List.mem_toFinset.1 hvg) with rfl | hvl
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨g, hg, by
              rw [hc]; exact List.mem_toFinset.2 hvl⟩)
    refine (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans ?_)
    have hsum : (ts.toFinset.biUnion (fun g => (γ' g).tail.toFinset)).card ≤ ts.length * R := by
      refine Finset.card_biUnion_le.trans ?_
      calc ∑ g ∈ ts.toFinset, (γ' g).tail.toFinset.card
          ≤ ∑ _g ∈ ts.toFinset, R := by
            apply Finset.sum_le_sum
            intro g hg
            obtain ⟨-, -, -, h4⟩ := hγ'1 g (List.mem_toFinset.1 hg)
            refine (List.toFinset_card_le _).trans ?_
            simp; omega
        _ = ts.toFinset.card * R := by simp
        _ ≤ ts.length * R := by gcongr; exact List.toFinset_card_le _
    have : ts.length * R ≤ (2 * j) * R := by gcongr
    rw [hj] at this
    nlinarith
  · -- diameter
    intro u hu v hv
    obtain ⟨nu, hnu, hu'⟩ := hnear u hu
    obtain ⟨nv, hnv, hv'⟩ := hnear v hv
    -- two large subsets of `N` intersect
    let Nf : Finset H := Finset.univ.filter (· ∈ N)
    have hNcard : Nf.card = m := by
      rw [hm, Nat.card_eq_fintype_card, ← Fintype.card_coe]
      simp [Nf]
    have hX : (subprods ts).image (nu * ·) ⊆ Nf := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, N.mul_mem hnu (subprods_mem ts htsN a ha)⟩
    have hY : (subprods ts).image (nv * ·) ⊆ Nf := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, N.mul_mem hnv (subprods_mem ts htsN a ha)⟩
    have hint : ((subprods ts).image (nu * ·) ∩ (subprods ts).image (nv * ·)).Nonempty := by
      rw [← Finset.card_pos]
      have h1 := Finset.card_union_add_card_inter ((subprods ts).image (nu * ·))
        ((subprods ts).image (nv * ·))
      have h2 := Finset.card_le_card (Finset.union_subset hX hY)
      rw [Finset.card_image_of_injective _ (mul_right_injective nu),
        Finset.card_image_of_injective _ (mul_right_injective nv)] at h1
      omega
    obtain ⟨x, hx⟩ := hint
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (Finset.mem_inter.1 hx).1
    obtain ⟨b, hb, hab⟩ := Finset.mem_image.1 (Finset.mem_inter.1 hx).2
    have w1 := subprods_walk S N Z hZinv h1Z R ts htsN hγZ a ha nu hnu
    have w2 := subprods_walk S N Z hZinv h1Z R ts htsN hγZ b hb nv hnv
    rw [hab] at w2
    have := ((hu'.trans w1).trans w2.symm).trans hv'.symm
    refine this.mono_len ?_
    have : ts.length ≤ 2 * j := htslen
    rw [hj] at this
    nlinarith

/-- The window size of Lemma 3.3 satisfies `L + 1 ≤ 20 R log (2m)`. -/
lemma window_bound_le (m R : ℕ) (hm : 2 ≤ m) (hR : 1 ≤ R) :
    (((4 * Nat.log 2 m + 6) * R : ℕ) : ℝ) + 1 ≤ 20 * R * Real.log (2 * m) := by
  have hl2 : 0.69 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlog : (Nat.log 2 m : ℝ) * Real.log 2 ≤ Real.log m := by
    have h := Nat.pow_log_le_self 2 (by omega : m ≠ 0)
    have : ((2:ℝ) ^ Nat.log 2 m) ≤ m := by exact_mod_cast h
    have := Real.log_le_log (by positivity) this
    rwa [Real.log_pow] at this
  have h4 : Real.log (2 * m) = Real.log 2 + Real.log m :=
    Real.log_mul (by norm_num) (by positivity)
  have hlm : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) (by exact_mod_cast hm)
  have hR' : (1:ℝ) ≤ R := by exact_mod_cast hR
  push_cast
  have hk : (Nat.log 2 m : ℝ) ≤ Real.log m / 0.69 := by
    rw [le_div_iff₀ (by norm_num)]; nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.log 2 m)]
  have h1 : (4 * (Nat.log 2 m : ℝ) + 6) * R + 1 ≤ (4 * (Real.log m / 0.69) + 7) * R := by
    have : (4 * (Nat.log 2 m : ℝ) + 6) * R ≤ (4 * (Real.log m / 0.69) + 6) * R := by gcongr
    linarith
  refine h1.trans ?_
  rw [h4]
  have : 4 * (Real.log m / 0.69) + 7 ≤ 20 * (Real.log 2 + Real.log m) := by
    have : Real.log m / 0.69 ≤ 1.5 * Real.log m := by
      rw [div_le_iff₀ (by norm_num)]; nlinarith
    linarith
  nlinarith

end Lovasz
