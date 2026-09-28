module
public import RequestProject.VTBasic
public import RequestProject.Window

/-!
# Windows above an orbit of a normal subgroup (Lemma A.5)
-/

@[expose] public section


open Classical

namespace Lovasz

variable {V Γ : Type*} [Group Γ] [MulAction Γ V] [Fintype Γ] {X : SimpleGraph V}

/-- The number of elements of `N` sending `a` to `a'` does not depend on the pair, when all
orbits have the same size. -/
lemma card_filter_smul_uniform (N : Subgroup Γ) {m : ℕ} (hm : ∀ v : V, (orb N v).card = m)
    {a a' b b' : V} (ha : fib N a' = fib N a) (hb : fib N b' = fib N b) :
    ((nset N).filter (fun g => g • a = a')).card = ((nset N).filter (fun g => g • b = b')).card := by
  have h1 := card_filter_smul_eq N ha
  have h2 := card_filter_smul_eq N hb
  rw [hm] at h1 h2
  have hm0 : 0 < m := by rw [← hm a]; exact Finset.card_pos.2 ⟨a, self_mem_orb N a⟩
  exact Nat.eq_of_mul_eq_mul_right hm0 (h1.trans h2.symm)

/-- **Averaging step of Lemma A.5.** If `A` is a subset of an orbit of size `m` with
`1 ≤ |A| ≤ m/2`, some `g ∈ N` has `|gA \ A| ≥ |A|/2`. -/
theorem exists_smul_large (N : Subgroup Γ) {m : ℕ} (hm : ∀ v : V, (orb N v).card = m) (x : V)
    (A : Finset V) (hA : ∀ a ∈ A, fib N a = fib N x) (h1 : 1 ≤ A.card) (h2 : 2 * A.card ≤ m) :
    ∃ g ∈ N, (A.card : ℝ) / 2 ≤ ((A.image (g • ·)) \ A).card := by
  set S := nset N
  set s := (S.filter (fun g : Γ => g • x = x)).card with hs
  have hsm : s * m = S.card := by rw [← hm x]; exact card_filter_smul_eq N rfl
  have hc : ∀ a ∈ A, ∀ a' ∈ A, (S.filter (fun g : Γ => g • a = a')).card = s := by
    intro a ha a' ha'
    exact card_filter_smul_uniform N hm ((hA a' ha').trans (hA a ha).symm) rfl
  have hcnt : ∀ g : Γ, ((A.image (g • ·)) \ A).card = (A.filter (fun a => g • a ∉ A)).card := by
    intro g
    have : (A.image (g • ·)) \ A = (A.filter (fun a => g • a ∉ A)).image (g • ·) := by
      ext y; simp only [Finset.mem_sdiff, Finset.mem_image, Finset.mem_filter]; aesop
    rw [this, Finset.card_image_of_injective _ (MulAction.injective g)]
  have hrow : ∀ a ∈ A, (S.filter (fun g => g • a ∈ A)).card = A.card * s := by
    intro a ha
    have := Finset.card_eq_sum_card_fiberwise (f := fun g => g • a)
      (s := S.filter (fun g => g • a ∈ A)) (t := A)
      (fun g hg => Finset.mem_coe.2 (Finset.mem_filter.1 hg).2)
    rw [this, Finset.sum_congr rfl (g := fun _ => s), Finset.sum_const, smul_eq_mul]
    intro a' ha'
    rw [← hc a ha a' ha', Finset.filter_filter]
    congr 1; ext g; simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hg, -, h⟩; exact ⟨hg, h⟩
    · rintro ⟨hg, h⟩; exact ⟨hg, by rw [h]; exact ha', h⟩
  have hsum : ∑ g ∈ S, ((A.image (g • ·)) \ A).card = A.card * (S.card - A.card * s) := by
    simp_rw [hcnt, Finset.card_filter]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (g := fun _ => S.card - A.card * s)]
    · simp
    intro a ha
    rw [← Finset.card_filter, ← hrow a ha]
    have := Finset.card_filter_add_card_filter_not (s := S) (fun g => g • a ∈ A)
    omega
  by_contra hcon
  push_neg at hcon
  have hS : S.Nonempty := ⟨1, mem_nset.2 N.one_mem⟩
  have hlt : ∑ g ∈ S, (((A.image (g • ·)) \ A).card : ℝ) < ∑ g ∈ S, (A.card : ℝ) / 2 := by
    apply Finset.sum_lt_sum_of_nonempty hS
    intro g hg; exact hcon g (mem_nset.1 hg)
  rw [← Nat.cast_sum, hsum, Finset.sum_const, nsmul_eq_mul] at hlt
  have hle : A.card * s ≤ S.card := by rw [← hsm, mul_comm s]; exact Nat.mul_le_mul_right _ (by omega)
  push_cast [hle] at hlt
  rw [← hsm] at hlt
  push_cast at hlt
  have : (2 * A.card : ℝ) ≤ m := by exact_mod_cast h2
  have : (1 : ℝ) ≤ A.card := by exact_mod_cast h1
  have hs0 : (0 : ℝ) ≤ s := by positivity
  nlinarith [mul_nonneg hs0 (by linarith : (0:ℝ) ≤ m - 2 * A.card)]

/-- The sets `A_i` of Lemma A.5: `A_{i+1} = A_i ∪ g_i A_i`. -/
noncomputable def iterA (x : V) : List Γ → Finset V
  | [] => {x}
  | g :: l => iterA x l ∪ (iterA x l).image (g • ·)

omit [Fintype Γ] in
lemma self_mem_iterA (x : V) : ∀ l : List Γ, x ∈ iterA x l
  | [] => by simp [iterA]
  | g :: l => by simp only [iterA]; exact Finset.mem_union_left _ (self_mem_iterA x l)

omit [Fintype Γ] in
lemma iterA_fib {N : Subgroup Γ} (x : V) :
    ∀ l : List Γ, (∀ g ∈ l, g ∈ N) → ∀ a ∈ iterA x l, fib N a = fib N x
  | [], _, a, ha => by simp [iterA] at ha; rw [ha]
  | g :: l, hl, a, ha => by
    simp only [iterA, Finset.mem_union, Finset.mem_image] at ha
    have hl' : ∀ y ∈ l, y ∈ N := fun y hy => hl y (by simp [hy])
    rcases ha with ha | ⟨b, hb, rfl⟩
    · exact iterA_fib x l hl' a ha
    · rw [fib_smul_of_mem (hl g (by simp))]; exact iterA_fib x l hl' b hb

lemma exists_iterA_large (N : Subgroup Γ) {m : ℕ} (hm : ∀ v : V, (orb N v).card = m) (x : V)
    (i : ℕ) : ∃ l : List Γ, (∀ g ∈ l, g ∈ N) ∧ l.length ≤ i ∧
      (m < 2 * (iterA x l).card ∨ ((3:ℝ) / 2) ^ i ≤ (iterA x l).card) := by
  induction i with
  | zero => exact ⟨[], by simp, le_rfl, Or.inr (by simp [iterA])⟩
  | succ i ih =>
    obtain ⟨l, hlN, hlen, h⟩ := ih
    by_cases hbig : m < 2 * (iterA x l).card
    · exact ⟨l, hlN, by omega, Or.inl hbig⟩
    · rcases h with h | h
      · exact absurd h hbig
      push_neg at hbig
      have h1 : 1 ≤ (iterA x l).card := Finset.card_pos.2 ⟨x, self_mem_iterA x l⟩
      obtain ⟨g, hgN, hg⟩ := exists_smul_large N hm x (iterA x l) (iterA_fib x l hlN) h1 hbig
      refine ⟨g :: l, ?_, by simp; omega, Or.inr ?_⟩
      · intro y hy; simp at hy; rcases hy with rfl | hy; exact hgN; exact hlN y hy
      · simp only [iterA]
        have : (iterA x l ∪ (iterA x l).image (g • ·)).card =
            (iterA x l).card + ((iterA x l).image (g • ·) \ iterA x l).card := by
          rw [← Finset.card_union_of_disjoint Finset.disjoint_sdiff,
            Finset.union_sdiff_self_eq_union]
        rw [this]; push_cast; rw [pow_succ]; nlinarith

omit [Fintype Γ] in
lemma iterA_walk (hX : ActsOn X Γ) (N : Subgroup Γ) (Z : Set V) (hZ : ∀ n ∈ N, ∀ z ∈ Z, n • z ∈ Z)
    (x : V) (hx : x ∈ Z) (R : ℕ) :
    ∀ l : List Γ, (∀ g ∈ l, g ∈ N) → (∀ g ∈ l, WalkLe X Z x (g • x) R) →
      ∀ a ∈ iterA x l, ∀ n ∈ N, WalkLe X Z (n • x) (n • a) (l.length * R)
  | [], _, _, a, ha, n, hn => by
    simp [iterA] at ha; subst ha
    simpa using WalkLe.refl (G := X) (hZ n hn _ hx) 0
  | g :: l, hlN, hlw, a, ha, n, hn => by
    have hlN' : ∀ y ∈ l, y ∈ N := fun y hy => hlN y (by simp [hy])
    have hlw' : ∀ y ∈ l, WalkLe X Z x (y • x) R := fun y hy => hlw y (by simp [hy])
    have hgN : g ∈ N := hlN g (by simp)
    simp only [iterA, Finset.mem_union, Finset.mem_image] at ha
    rcases ha with ha | ⟨b, hb, rfl⟩
    · exact (iterA_walk hX N Z hZ x hx R l hlN' hlw' a ha n hn).mono_len
        (by simp [Nat.succ_mul])
    · have h₁ := (hlw g (by simp)).map_smul_of_inv hX n (hZ n hn)
      have h₂ := iterA_walk hX N Z hZ x hx R l hlN' hlw' b hb (n * g) (N.mul_mem hn hgN)
      rw [mul_smul, mul_smul] at h₂
      rw [← mul_smul] at h₁ ⊢
      rw [mul_smul] at h₁ ⊢
      have := h₁.trans h₂
      exact this.mono_len (by simp [Nat.succ_mul]; omega)

/-- **Lemma A.5** (window lemma for normal orbits). Suppose all `N`-orbits have `m` elements
and any two vertices of the same orbit are joined by a walk with at most `R ≥ 1` edges.  For
every vertex `x` there is an `N`-invariant vertex set `Z ∋ x` (the preimage of a set `W` of
orbits) consisting of at most `L` orbits, such that any two vertices of `Z` are joined by a
walk inside `Z` with at most `L` edges, where `L = (4 ⌊log₂ m⌋ + 6) R`. -/
theorem window_vt [Fintype V] (hX : ActsOn X Γ) (N : Subgroup Γ) {m : ℕ}
    (hm : ∀ v : V, (orb N v).card = m) (R : ℕ) (hR1 : 1 ≤ R)
    (hR : ∀ u v : V, fib N u = fib N v → WalkLe X Set.univ u v R) (x : V) :
    ∃ Z : Finset V, x ∈ Z ∧ (∀ n ∈ N, ∀ z ∈ Z, n • z ∈ Z) ∧
      (Z.image (fib N)).card ≤ (4 * Nat.log 2 m + 6) * R ∧
      ∀ u ∈ Z, ∀ v ∈ Z, WalkLe X Z u v ((4 * Nat.log 2 m + 6) * R) := by
  set j := Nat.log 2 m + 1 with hj
  obtain ⟨ts, htsN, htslen, hts⟩ := exists_iterA_large N hm x (2 * j)
  have hbig : m < 2 * (iterA x ts).card := by
    rcases hts with h | h
    · exact h
    have h2 : (m : ℝ) < 2 ^ j := by exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) m
    have h3 : (2 : ℝ) ^ j ≤ ((3 : ℝ) / 2) ^ (2 * j) := by
      rw [pow_mul]; gcongr; norm_num
    have : (m : ℝ) < 2 * (iterA x ts).card := by
      have : (0 : ℝ) ≤ (iterA x ts).card := by positivity
      linarith
    exact_mod_cast this
  have hγ : ∀ t ∈ ts, WalkLe X Set.univ x (t • x) R := fun t ht =>
    hR x (t • x) (fib_smul_of_mem (htsN t ht) x).symm
  choose γ hγ' using hγ
  let γ' : Γ → List V := fun g => if hg : g ∈ ts then γ g hg else [x]
  have hγ'1 : ∀ g ∈ ts, (γ' g).IsChain X.Adj ∧ (γ' g).head? = some x ∧
      (γ' g).getLast? = some (g • x) ∧ (γ' g).length ≤ R + 1 := by
    intro g hg
    simp only [γ', dif_pos hg]
    obtain ⟨h1, h2, h3, -, h5⟩ := hγ' g hg
    exact ⟨h1, h2, h3, h5⟩
  let V0 : Finset V := insert x (ts.toFinset.biUnion (fun g => (γ' g).toFinset))
  let Z : Finset V := Finset.univ.filter (fun z => ∃ v ∈ V0, fib N z = fib N v)
  have hV0Z : ∀ v ∈ V0, v ∈ Z := fun v hv =>
    Finset.mem_filter.2 ⟨Finset.mem_univ _, v, hv, rfl⟩
  have hZinv : ∀ a ∈ N, ∀ z ∈ Z, a • z ∈ Z := by
    intro a ha z hz
    obtain ⟨-, v, hv, hzv⟩ := Finset.mem_filter.1 hz
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, v, hv, by rw [fib_smul_of_mem ha, hzv]⟩
  have hxZ : x ∈ Z := hV0Z x (Finset.mem_insert_self _ _)
  have hγZ : ∀ t ∈ ts, WalkLe X Z x (t • x) R := by
    intro t ht
    obtain ⟨h1, h2, h3, h4⟩ := hγ'1 t ht
    refine ⟨γ' t, h1, h2, h3, fun y hy => hV0Z y ?_, h4⟩
    exact Finset.mem_insert_of_mem (Finset.mem_biUnion.2
      ⟨t, List.mem_toFinset.2 ht, List.mem_toFinset.2 hy⟩)
  -- every vertex of `Z` is within `R` of the orbit of `x`
  have hnear : ∀ u ∈ Z, ∃ n ∈ N, WalkLe X Z u (n • x) R := by
    intro u hu
    obtain ⟨-, v, hv, huv⟩ := Finset.mem_filter.1 hu
    obtain ⟨n, hn, rfl⟩ := fib_eq_iff.1 huv
    refine ⟨n, hn, ?_⟩
    have hv1 : WalkLe X Z x v R := by
      rcases Finset.mem_insert.1 hv with rfl | hv
      · exact WalkLe.refl hxZ R
      · obtain ⟨g, hg, hvg⟩ := Finset.mem_biUnion.1 hv
        have hg' := List.mem_toFinset.1 hg
        obtain ⟨h1, h2, -, h4⟩ := hγ'1 g hg'
        obtain ⟨l₁, l₂, hl⟩ := List.mem_iff_append.1 (List.mem_toFinset.1 hvg)
        have hpre : l₁ ++ [v] <+: γ' g := ⟨l₂, by rw [hl]; simp⟩
        refine ⟨l₁ ++ [v], h1.prefix hpre, ?_, by simp, fun y hy => hV0Z y ?_, ?_⟩
        · rw [← h2]
          cases l₁ with
          | nil => simp [hl]
          | cons a l₁ => simp [hl]
        · refine Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨g, hg, List.mem_toFinset.2 ?_⟩)
          exact hpre.subset hy
        · exact (hpre.length_le).trans h4
    exact (hv1.symm.map_smul_of_inv hX n (hZinv n hn))
  refine ⟨Z, hxZ, hZinv, ?_, ?_⟩
  · -- counting orbits
    have himg : Z.image (fib N) ⊆ V0.image (fib N) := by
      intro q hq
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hq
      obtain ⟨-, v, hv, hzv⟩ := Finset.mem_filter.1 hz
      exact Finset.mem_image.2 ⟨v, hv, hzv.symm⟩
    refine (Finset.card_le_card himg).trans ?_
    refine Finset.card_image_le.trans ?_
    have hsub : V0 ⊆ insert x (ts.toFinset.biUnion (fun g => (γ' g).tail.toFinset)) := by
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
    have hsubO : ∀ n ∈ N, (iterA x ts).image (n • ·) ⊆ orb N x := by
      intro n hn y hy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hy
      exact mem_orb.2 (by rw [fib_smul_of_mem hn]; exact iterA_fib x ts htsN a ha)
    have hint : ((iterA x ts).image (nu • ·) ∩ (iterA x ts).image (nv • ·)).Nonempty := by
      rw [← Finset.card_pos]
      have h1 := Finset.card_union_add_card_inter ((iterA x ts).image (nu • ·))
        ((iterA x ts).image (nv • ·))
      have h2 := Finset.card_le_card (Finset.union_subset (hsubO nu hnu) (hsubO nv hnv))
      rw [Finset.card_image_of_injective _ (MulAction.injective nu),
        Finset.card_image_of_injective _ (MulAction.injective nv)] at h1
      rw [hm x] at h2
      omega
    obtain ⟨y, hy⟩ := hint
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (Finset.mem_inter.1 hy).1
    obtain ⟨b, hb, hab⟩ := Finset.mem_image.1 (Finset.mem_inter.1 hy).2
    have w1 := iterA_walk hX N Z hZinv x hxZ R ts htsN hγZ a ha nu hnu
    have w2 := iterA_walk hX N Z hZinv x hxZ R ts htsN hγZ b hb nv hnv
    rw [hab] at w2
    have := ((hu'.trans w1).trans w2.symm).trans hv'.symm
    refine this.mono_len ?_
    have : ts.length ≤ 2 * j := htslen
    rw [hj] at this
    nlinarith

end Lovasz
