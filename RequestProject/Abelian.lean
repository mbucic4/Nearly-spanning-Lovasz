module
public import RequestProject.Corridor
public import RequestProject.TreeContraction

/-!
# Abelian normal extensions (Lemmas 3.10, 3.11 and 3.12)
-/

@[expose] public section


open Classical

namespace Lovasz

/-- Boustrophedon step of Lemma 3.10: a path through `l`, translated alternately forwards and
backwards by `1, t, t², …, t^(r-1)`, gives a path through all the translates. -/
lemma boustrophedon {A : Type*} [Group A] (hcomm : ∀ a b : A, a * b = b * a) (T : Set A)
    (t : A) (ht : t ∈ T) (l : List A) (hl : IsPathL (cay T) l) (hne : l ≠ []) (r : ℕ)
    (hdist : ∀ i j : ℕ, ∀ a b : A, i < r → j < r → a ∈ l → b ∈ l → t ^ i * a = t ^ j * b →
      i = j) :
    ∃ P : List A, IsPathL (cay T) P ∧ ∀ x, x ∈ P ↔ ∃ i < r, ∃ a ∈ l, x = t ^ i * a := by
  let seg : ℕ → List A := fun i => (if Even i then l else l.reverse).map (t ^ i * ·)
  let c : ℕ → A := fun i => if Even i then l.getLast hne else l.head hne
  have hseglast : ∀ i, (seg i).getLast? = some (t ^ i * c i) := by
    intro i
    by_cases hi : Even i
    · simp [seg, c, hi, List.getLast?_eq_some_getLast hne]
    · simp [seg, c, hi, List.head?_eq_some_head hne]
  have hseghead : ∀ i, (seg (i + 1)).head? = some (t ^ (i + 1) * c i) := by
    intro i
    by_cases hi : Even i
    · have : ¬ Even (i + 1) := by simpa [Nat.even_add_one] using hi
      simp [seg, c, hi, this, List.getLast?_eq_some_getLast hne]
    · have : Even (i + 1) := by simpa [Nat.even_add_one] using hi
      simp [seg, c, hi, this, List.head?_eq_some_head hne]
  have hsegpath : ∀ i, IsPathL (cay T) (seg i) := by
    intro i
    by_cases hi : Even i
    · simp only [seg, hi, if_true]; exact hl.map_mul_left _
    · simp only [seg, hi, if_false]; exact hl.reverse.map_mul_left _
  have hsegmem : ∀ i x, x ∈ seg i ↔ ∃ a ∈ l, x = t ^ i * a := by
    intro i x
    by_cases hi : Even i
    · simp only [seg, hi, if_true, List.mem_map]
      constructor
      · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩
      · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩
    · simp only [seg, hi, if_false, List.mem_map, List.mem_reverse]
      constructor
      · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩
      · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩
  have hsegne : ∀ i, seg i ≠ [] := by
    intro i
    by_cases hi : Even i <;> simp [seg, hi, hne]
  have hcmem : ∀ i, c i ∈ l := by
    intro i
    by_cases hi : Even i
    · simp only [c, hi, if_true]; exact List.getLast_mem hne
    · simp only [c, hi, if_false]; exact List.head_mem hne
  have key : ∀ k ≤ r, ∃ P : List A, IsPathL (cay T) P ∧
      (∀ x, x ∈ P ↔ ∃ i < k, ∃ a ∈ l, x = t ^ i * a) ∧
      (0 < k → P.getLast? = (seg (k - 1)).getLast?) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨[], ⟨List.isChain_nil, List.nodup_nil⟩, by simp, by simp⟩
    | succ k ih =>
      intro hk
      obtain ⟨P, hP, hPmem, hPlast⟩ := ih (by omega)
      refine ⟨P ++ seg k, ⟨?_, ?_⟩, ?_, ?_⟩
      · rw [List.isChain_append]
        refine ⟨hP.1, (hsegpath k).1, ?_⟩
        intro x hx y hy
        rcases Nat.eq_zero_or_pos k with rfl | hk0
        · have : P = [] := by
            rcases P with _ | ⟨z, P⟩
            · rfl
            · exfalso
              obtain ⟨i, hi, -⟩ := (hPmem z).1 (by simp)
              omega
          simp [this] at hx
        · rw [hPlast hk0, hseglast] at hx
          obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
          rw [hseghead] at hy
          simp only [Nat.add_sub_cancel, Option.mem_def, Option.some.injEq] at hx hy
          subst hx hy
          have ht1 : t ≠ 1 := by
            intro h1
            have := hdist 0 1 (c k') (c k') (by omega) (by omega) (hcmem k') (hcmem k')
              (by simp [h1])
            omega
          have := cay_adj_mul_right_of_mem (x := t ^ k' * c k') (Or.inl ht) ht1
          convert this using 1
          rw [pow_succ, mul_assoc, mul_assoc, hcomm (c k') t]
      · rw [List.nodup_append]
        refine ⟨hP.2, (hsegpath k).2, ?_⟩
        intro x hx y hy hxy
        subst hxy
        obtain ⟨i, hi, a, ha, rfl⟩ := (hPmem _).1 hx
        obtain ⟨b, hb, hb'⟩ := (hsegmem k _).1 hy
        have := hdist i k a b (by omega) (by omega) ha hb hb'
        omega
      · intro x
        rw [List.mem_append, hPmem, hsegmem]
        constructor
        · rintro (⟨i, hi, a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
          · exact ⟨i, by omega, a, ha, rfl⟩
          · exact ⟨k, by omega, a, ha, rfl⟩
        · rintro ⟨i, hi, a, ha, rfl⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
          · exact Or.inl ⟨i, hi, a, ha, rfl⟩
          · exact Or.inr ⟨a, ha, rfl⟩
      · intro _
        rw [List.getLast?_append_of_ne_nil _ (hsegne k)]
        simp
  obtain ⟨P, hP, hPmem, -⟩ := key r le_rfl
  exact ⟨P, hP, hPmem⟩


/-- **Lemma 3.10.** Every connected Cayley graph of a finite abelian group has a Hamilton path. -/
theorem abelian_hamiltonian {A : Type*} [Group A] [Finite A]
    (hcomm : ∀ a b : A, a * b = b * a) (T : Set A) (hT : (cay T).Connected) :
    ∃ l : List A, IsPathL (cay T) l ∧ ∀ a, a ∈ l := by
  letI : CommGroup A := { ‹Group A› with mul_comm := hcomm }
  have hcl : Subgroup.closure T = ⊤ := cay_connected_iff.1 hT
  set Fs := T.toFinite.toFinset with hFs
  have key : ∀ U : Finset A, U ⊆ Fs → ∃ l : List A, IsPathL (cay T) l ∧
      ∀ a, a ∈ l ↔ a ∈ Subgroup.closure (U : Set A) := by
    intro U
    induction U using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨[1], isPathL_singleton 1, by simp⟩
    | insert t U htU ih =>
      intro hsub
      have htT : t ∈ T := by
        have := hsub (Finset.mem_insert_self t U); simpa [hFs] using this
      obtain ⟨l, hl, hlmem⟩ := ih ((Finset.subset_insert t U).trans hsub)
      set B := Subgroup.closure (U : Set A) with hB
      have hUle : B ≤ Subgroup.closure ((insert t U : Finset A) : Set A) :=
        Subgroup.closure_mono (by simp [Set.subset_insert])
      have htmem : t ∈ Subgroup.closure ((insert t U : Finset A) : Set A) :=
        Subgroup.subset_closure (by simp)
      by_cases htB : t ∈ B
      · refine ⟨l, hl, fun a => ?_⟩
        rw [hlmem]
        constructor
        · exact fun h => hUle h
        · intro h
          have : Subgroup.closure ((insert t U : Finset A) : Set A) ≤ B := by
            rw [Subgroup.closure_le]
            intro x hx
            simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
            rcases hx with rfl | hx
            · exact htB
            · exact Subgroup.subset_closure hx
          exact this h
      · have hex : ∃ r : ℕ, 0 < r ∧ t ^ r ∈ B :=
          ⟨orderOf t, (isOfFinOrder_of_finite t).orderOf_pos, by rw [pow_orderOf_eq_one]; exact B.one_mem⟩
        let r := Nat.find hex
        have hr : 0 < r ∧ t ^ r ∈ B := Nat.find_spec hex
        have hrmin : ∀ m, 0 < m → m < r → t ^ m ∉ B := fun m hm hmr hmB =>
          Nat.find_min hex hmr ⟨hm, hmB⟩
        have hr2 : 2 ≤ r := by
          by_contra h
          have : r = 1 := by omega
          apply htB; have := hr.2; rwa [‹r = 1›, pow_one] at this
        have hdist : ∀ i j : ℕ, ∀ a b : A, i < r → j < r → a ∈ l → b ∈ l →
            t ^ i * a = t ^ j * b → i = j := by
          have aux : ∀ i j : ℕ, ∀ a b : A, i < j → j < r → a ∈ B → b ∈ B →
              t ^ i * a ≠ t ^ j * b := by
            intro i j a b hij hj ha hb heq
            apply hrmin (j - i) (by omega) (by omega)
            have : t ^ (j - i) = a * b⁻¹ := by
              have h2 : t ^ j = t ^ (j - i) * t ^ i := by rw [← pow_add]; congr 1; omega
              rw [h2] at heq
              rw [eq_mul_inv_iff_mul_eq]
              calc t ^ (j - i) * b = (t ^ i)⁻¹ * (t ^ (j - i) * t ^ i * b) := by
                    simp [mul_comm, mul_assoc]
                _ = a := by rw [← heq]; simp
            rw [this]; exact B.mul_mem ha (B.inv_mem hb)
          intro i j a b hi hj ha hb heq
          rw [hlmem] at ha hb
          rcases lt_trichotomy i j with h | h | h
          · exact absurd heq (aux i j a b h hj ha hb)
          · exact h
          · exact absurd heq.symm (aux j i b a h hi hb ha)
        have hne : l ≠ [] := by
          intro h; have := (hlmem 1).2 B.one_mem; simp [h] at this
        obtain ⟨P, hP, hPmem⟩ := boustrophedon hcomm T t htT l hl hne r hdist
        refine ⟨P, hP, fun x => ?_⟩
        rw [hPmem]
        constructor
        · rintro ⟨i, -, a, ha, rfl⟩
          exact Subgroup.mul_mem _ (Subgroup.pow_mem _ htmem i) (hUle ((hlmem a).1 ha))
        · intro hx
          simp only [hlmem]
          induction hx using Subgroup.closure_induction with
          | mem x hx =>
            simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
            rcases hx with rfl | hx
            · exact ⟨1, by omega, 1, B.one_mem, by simp⟩
            · exact ⟨0, by omega, x, Subgroup.subset_closure hx, by simp⟩
          | one => exact ⟨0, by omega, 1, B.one_mem, by simp⟩
          | mul x y _ _ ihx ihy =>
            obtain ⟨i, hi, a, ha, rfl⟩ := ihx
            obtain ⟨j, hj, b, hb, rfl⟩ := ihy
            by_cases hij : i + j < r
            · exact ⟨i + j, hij, a * b, B.mul_mem ha hb, by
                rw [pow_add]; simp [mul_comm, mul_left_comm, mul_assoc]⟩
            · refine ⟨i + j - r, by omega, t ^ r * (a * b), B.mul_mem hr.2 (B.mul_mem ha hb), ?_⟩
              have h2 : t ^ i * t ^ j = t ^ (i + j - r) * t ^ r := by
                rw [← pow_add, ← pow_add]; congr 1; omega
              rw [show t ^ i * a * (t ^ j * b) = (t ^ i * t ^ j) * (a * b) by
                simp [mul_comm, mul_left_comm, mul_assoc], h2, mul_assoc]
          | inv x _ ihx =>
            obtain ⟨i, hi, a, ha, rfl⟩ := ihx
            rcases Nat.eq_zero_or_pos i with rfl | hi0
            · exact ⟨0, by omega, a⁻¹, B.inv_mem ha, by simp⟩
            · refine ⟨r - i, by omega, (t ^ r)⁻¹ * a⁻¹, B.mul_mem (B.inv_mem hr.2) (B.inv_mem ha), ?_⟩
              have h2 : t ^ r = t ^ (r - i) * t ^ i := by rw [← pow_add]; congr 1; omega
              rw [h2]
              simp [mul_comm, mul_left_comm]
  obtain ⟨l, hl, hlmem⟩ := key Fs (Finset.Subset.refl _)
  refine ⟨l, hl, fun a => (hlmem a).2 ?_⟩
  have : ((Fs : Finset A) : Set A) = T := by simp [hFs]
  rw [this, hcl]; exact Subgroup.mem_top a


variable {H : Type*} [Group H]

/-- **Lemma 3.11** (tree contraction), for a subgroup `K ≤ H` acting by left multiplication
on a connected `K`-invariant vertex set `Z` of `cay S`.  Contracting a system of translated
trees gives a connected Cayley graph `cay T'` of `K`; every path in it lifts to a path in `Z`
with at least as many vertices, and if `cay T'` has a Hamilton path then, for every `K`-orbit
`B` in `Z`, the set `Z` contains a path with pairwise disjoint attachments from all of `B`. -/
theorem tree_contraction [Finite H] (S : Set H) (K : Subgroup H) (Z : Finset H)
    (hZ : ∀ k ∈ K, ∀ z ∈ Z, k * z ∈ Z) (hconn : ∀ u ∈ Z, ∀ v ∈ Z, ReachIn (cay S) Z u v)
    (hne : Z.Nonempty) :
    ∃ T' : Set K, (cay T').Connected ∧
      (∀ l : List K, IsPathL (cay T') l →
        ∃ P : List H, IsPathL (cay S) P ∧ (∀ x ∈ P, x ∈ Z) ∧ l.length ≤ P.length) ∧
      ((∃ l : List K, IsPathL (cay T') l ∧ ∀ k, k ∈ l) →
        ∀ y ∈ Z, HasRail (cay S) Z (Z.filter (fun z => z * y⁻¹ ∈ K))) := by
  obtain ⟨T0, hT0ne, hT0Z, hdist, hconn0, hcover⟩ := exists_orbit_transversal S K Z hZ hconn hne
  refine ⟨contractGen S K T0, contract_connected hdist hT0Z hT0ne hcover hconn hZ, ?_, ?_⟩
  · intro l hl
    cases l with
    | nil => exact ⟨[], ⟨List.isChain_nil, List.nodup_nil⟩, by simp, by simp⟩
    | cons k l =>
      obtain ⟨P, hP, hPcell, hPcov, -⟩ := lift_contract_path hdist hT0ne hconn0 l k hl
      refine ⟨P, hP, fun x hx => ?_, length_le_of_meets_cells hdist hl.2 hPcov⟩
      obtain ⟨k', -, hk'⟩ := hPcell x hx
      exact cell_subset (Z := (Z : Set H)) hZ hT0Z k' hk'
  · rintro ⟨l, hl, hall⟩ y -
    cases l with
    | nil => exact absurd (hall 1) (by simp)
    | cons k l =>
      obtain ⟨P, hP, hPcell, hPcov, -⟩ := lift_contract_path hdist hT0ne hconn0 l k hl
      refine rail_of_meets_all_cells hdist hT0Z hcover hconn0 hZ hP (fun x hx => ?_)
        (fun k' => hPcov k' (hall k')) y
      obtain ⟨k', -, hk'⟩ := hPcell x hx
      exact cell_subset (Z := (Z : Set H)) hZ hT0Z k' hk'

/-- Greedy choice of at most `⌈log₂ |A|⌉` generators from a generating family. -/
lemma exists_small_generating [Finite H] (A : Subgroup H) (F : Set H)
    (hF : Subgroup.closure F = A) :
    ∃ l : List H, (∀ x ∈ l, x ∈ F) ∧ l.length ≤ Nat.clog 2 (Nat.card A) ∧
      Subgroup.closure {x | x ∈ l} = A := by
  have key : ∀ j : ℕ, ∃ l : List H, (∀ x ∈ l, x ∈ F) ∧ l.length ≤ j ∧
      (Subgroup.closure {x | x ∈ l} = A ∨ 2 ^ j ≤ Nat.card (Subgroup.closure {x | x ∈ l})) := by
    intro j
    induction j with
    | zero => exact ⟨[], by simp, le_rfl, Or.inr (by simp)⟩
    | succ j ih =>
      obtain ⟨l, hlF, hlen, h⟩ := ih
      by_cases hA : Subgroup.closure {x | x ∈ l} = A
      · exact ⟨l, hlF, by omega, Or.inl hA⟩
      · rcases h with h | h
        · exact absurd h hA
        have hle : Subgroup.closure {x | x ∈ l} ≤ A := by
          rw [← hF]; exact Subgroup.closure_mono (fun x hx => hlF x hx)
        obtain ⟨f, hfF, hf⟩ : ∃ f ∈ F, f ∉ Subgroup.closure {x | x ∈ l} := by
          by_contra hcon
          push_neg at hcon
          apply hA
          refine le_antisymm hle ?_
          rw [← hF]; exact (Subgroup.closure_le _).2 hcon
        refine ⟨f :: l, ?_, by simp; omega, Or.inr ?_⟩
        · intro x hx; simp at hx; rcases hx with rfl | hx; exact hfF; exact hlF x hx
        · have hlt : Subgroup.closure {x | x ∈ l} < Subgroup.closure {x | x ∈ f :: l} := by
            refine lt_of_le_of_ne (Subgroup.closure_mono (fun x hx => by
              simp only [Set.mem_setOf_eq, List.mem_cons] at hx ⊢; exact Or.inr hx)) ?_
            intro heq
            apply hf; rw [heq]; exact Subgroup.subset_closure (by simp)
          have hdvd := Subgroup.card_dvd_of_le hlt.le
          obtain ⟨r, hr⟩ := hdvd
          have hr1 : r ≠ 1 := by
            rintro rfl
            rw [mul_one] at hr
            exact hlt.ne (Subgroup.eq_of_le_of_card_ge hlt.le hr.le)
          have hr0 : r ≠ 0 := by
            rintro rfl; simp at hr; exact Nat.card_pos.ne' hr
          rw [pow_succ, hr]
          have : 2 ≤ r := by omega
          nlinarith
  obtain ⟨l, hlF, hlen, h⟩ := key (Nat.clog 2 (Nat.card A))
  refine ⟨l, hlF, hlen, ?_⟩
  rcases h with h | h
  · exact h
  · have hle : Subgroup.closure {x | x ∈ l} ≤ A := by
      rw [← hF]; exact Subgroup.closure_mono (fun x hx => hlF x hx)
    exact Subgroup.eq_of_le_of_card_ge hle ((Nat.le_pow_clog (by norm_num) _).trans h)

/-- The window of Lemma 3.12: the union `Z` of the cosets of `A` met by the word paths of a
small generating family is connected, `A`-invariant, and consists of at most `1 + R ⌈log₂ m⌉`
cosets. -/
lemma abelian_window [Finite H] (S : Set H) (A : Subgroup H) [A.Normal] (R : ℕ) (F : Set H)
    (hF : Subgroup.closure F = A) (hFw : ∀ f ∈ F, WalkLe (cay S) Set.univ 1 f R) :
    ∃ Z : Finset H, (1 : H) ∈ Z ∧ (∀ a ∈ A, ∀ z ∈ Z, a * z ∈ Z) ∧
      (∀ u ∈ Z, ∀ v ∈ Z, ReachIn (cay S) Z u v) ∧
      (Z.image (QuotientGroup.mk : H → H ⧸ A)).card ≤ 1 + R * Nat.clog 2 (Nat.card A) := by
  have := Fintype.ofFinite H
  obtain ⟨gens, hgF, hglen, hgcl⟩ := exists_small_generating A F hF
  choose γ hγ using hFw
  classical
  -- the walk attached to each generator (the one-vertex walk for elements outside `F`)
  let γ' : H → List H := fun g => if hg : g ∈ F then γ g hg else [1]
  have hγ'1 : ∀ g ∈ gens, (γ' g).IsChain (cay S).Adj ∧ (γ' g).head? = some 1 ∧
      (γ' g).getLast? = some g ∧ (γ' g).length ≤ R + 1 := by
    intro g hg
    simp only [γ', dif_pos (hgF g hg)]
    obtain ⟨h1, h2, h3, -, h5⟩ := hγ g (hgF g hg)
    exact ⟨h1, h2, h3, h5⟩
  let V0 : Finset H := insert 1 (gens.toFinset.biUnion (fun g => (γ' g).toFinset))
  let Z : Finset H := Finset.univ.filter (fun z => ∃ v ∈ V0, z * v⁻¹ ∈ A)
  have hV0Z : ∀ v ∈ V0, v ∈ Z := fun v hv =>
    Finset.mem_filter.2 ⟨Finset.mem_univ _, v, hv, by simp [A.one_mem]⟩
  have hZinv : ∀ a ∈ A, ∀ z ∈ Z, a * z ∈ Z := by
    intro a ha z hz
    obtain ⟨-, v, hv, hzv⟩ := Finset.mem_filter.1 hz
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, v, hv, by
      rw [mul_assoc]; exact A.mul_mem ha hzv⟩
  have hZinv' : ∀ a ∈ A, ((a * ·) '' (Z : Set H)) ⊆ Z := by
    rintro a ha _ ⟨z, hz, rfl⟩; exact hZinv a ha z hz
  have h1Z : (1 : H) ∈ Z := hV0Z 1 (Finset.mem_insert_self _ _)
  -- every element of `A` is reachable from `1` inside `Z`
  have hA : ∀ a ∈ A, ReachIn (cay S) Z 1 a := by
    intro a ha
    rw [← hgcl] at ha
    induction ha using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨h1, h2, h3, -⟩ := hγ'1 g hg
      refine reachIn_of_chain h1 (fun x hx => hV0Z x ?_) h2 h3
      exact Finset.mem_insert_of_mem (Finset.mem_biUnion.2
        ⟨g, List.mem_toFinset.2 hg, List.mem_toFinset.2 hx⟩)
    | one => exact ReachIn.refl h1Z
    | mul x y hx hy ihx ihy =>
      have hxA : x ∈ A := hgcl ▸ hx
      refine ihx.trans ?_
      have := (ihy.map_mul_left x).mono le_rfl (hZinv' x hxA)
      simpa using this
    | inv x hx ihx =>
      have hxA : x ∈ A := hgcl ▸ hx
      have := (ihx.map_mul_left x⁻¹).mono le_rfl (hZinv' x⁻¹ (A.inv_mem hxA))
      simpa using this.symm
  have hall : ∀ z ∈ Z, ReachIn (cay S) Z 1 z := by
    intro z hz
    obtain ⟨-, v, hv, hzv⟩ := Finset.mem_filter.1 hz
    have hv1 : ReachIn (cay S) Z 1 v := by
      rcases Finset.mem_insert.1 hv with rfl | hv
      · exact ReachIn.refl h1Z
      · obtain ⟨g, hg, hvg⟩ := Finset.mem_biUnion.1 hv
        have hg' := List.mem_toFinset.1 hg
        obtain ⟨h1, h2, -, -⟩ := hγ'1 g hg'
        obtain ⟨l₁, l₂, hl⟩ := List.mem_iff_append.1 (List.mem_toFinset.1 hvg)
        have hpre : l₁ ++ [v] <+: γ' g := ⟨l₂, by rw [hl]; simp⟩
        refine reachIn_of_chain (h1.prefix hpre) (fun x hx => hV0Z x ?_) ?_ (by simp)
        · refine Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨g, hg, List.mem_toFinset.2 ?_⟩)
          exact hpre.subset hx
        · rw [← h2]
          cases l₁ with
          | nil => simp [hl]
          | cons a l₁ => simp [hl]
    have := (hv1.map_mul_left (z * v⁻¹)).mono le_rfl (hZinv' _ hzv)
    simp only [mul_one, inv_mul_cancel_right] at this
    exact (hA _ hzv).trans this
  refine ⟨Z, h1Z, hZinv, fun u hu v hv => (hall u hu).symm.trans (hall v hv), ?_⟩
  -- counting cosets
  have himg : Z.image (QuotientGroup.mk : H → H ⧸ A) ⊆ V0.image QuotientGroup.mk := by
    intro q hq
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hq
    obtain ⟨-, v, hv, hzv⟩ := Finset.mem_filter.1 hz
    refine Finset.mem_image.2 ⟨v, hv, ?_⟩
    exact (mk_eq_of_mul_inv_mem A hzv).symm
  refine (Finset.card_le_card himg).trans ?_
  refine Finset.card_image_le.trans ?_
  have hsub : V0 ⊆ insert 1 (gens.toFinset.biUnion (fun g => (γ' g).tail.toFinset)) := by
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
  rw [add_comm]
  gcongr
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ g ∈ gens.toFinset, (γ' g).tail.toFinset.card
      ≤ ∑ _g ∈ gens.toFinset, R := by
        apply Finset.sum_le_sum
        intro g hg
        obtain ⟨-, -, -, h4⟩ := hγ'1 g (List.mem_toFinset.1 hg)
        refine (List.toFinset_card_le _).trans ?_
        simp; omega
    _ = gens.toFinset.card * R := by simp
    _ ≤ gens.length * R := by gcongr; exact List.toFinset_card_le _
    _ ≤ Nat.clog 2 (Nat.card A) * R := by gcongr
    _ = R * Nat.clog 2 (Nat.card A) := by ring

/-- **Lemma 3.12.** Let `A ◁ H` be abelian of order `m ≥ 2`, generated by elements whose
`S`-word length is at most `R`, and let `b = 1 + R ⌈log₂ m⌉`.  Then
`p(X) ≥ d_η m^(1-η) p(Y) / b²`, where `Y = Cay(H/A, S)`. -/
theorem abelian_lifting (h12 : CycleMatchingTheorem) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ d : ℝ, 0 < d ∧ ∀ (H : Type) [Group H] [Finite H] (S : Set H) (A : Subgroup H) [A.Normal]
      (R : ℕ), (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → 2 ≤ Nat.card A →
      (∃ F : Set H, Subgroup.closure F = A ∧ ∀ f ∈ F, WalkLe (cay S) Set.univ 1 f R) →
      d * (Nat.card A : ℝ) ^ (1 - η) *
          pathOrder (cay ((QuotientGroup.mk : H → H ⧸ A) '' S)) /
          ((1 + R * Nat.clog 2 (Nat.card A) : ℕ) : ℝ) ^ 2 ≤
        pathOrder (cay S) := by
  obtain ⟨c0, hc0, hcor⟩ := corridor h12 η hη0 hη1
  refine ⟨c0, hc0, fun H _ _ S A _ R hcomm hm ⟨F, hF, hFw⟩ => ?_⟩
  have := Fintype.ofFinite H
  obtain ⟨Z, h1Z, hZinv, hconn, hWcard⟩ := abelian_window S A R F hF hFw
  obtain ⟨T', hT', -, hham⟩ := tree_contraction S A Z hZinv hconn ⟨1, h1Z⟩
  have hcommA : ∀ a b : A, a * b = b * a := fun a b => Subtype.ext (hcomm a a.2 b b.2)
  obtain ⟨l, hl, hall⟩ := abelian_hamiltonian hcommA T' hT'
  have hrails := hham ⟨l, hl, hall⟩
  set W := Z.image (QuotientGroup.mk : H → H ⧸ A) with hW
  have hWne : W.Nonempty := ⟨_, Finset.mem_image_of_mem _ h1Z⟩
  have horbit : ∀ z ∈ Z, Nat.card A ≤ (Z.filter (fun y => y * z⁻¹ ∈ A)).card := by
    intro z hz
    have := Fintype.ofFinite A
    have hsub : Finset.image (fun a : A => (a : H) * z) Finset.univ ⊆
        Z.filter (fun y => y * z⁻¹ ∈ A) := by
      intro y hy
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hy
      exact Finset.mem_filter.2 ⟨hZinv a a.2 z hz, by simp⟩
    refine le_trans ?_ (Finset.card_le_card hsub)
    rw [Finset.card_image_of_injective _ (fun a b hab => Subtype.ext (mul_right_cancel hab)),
      Finset.card_univ, Nat.card_eq_fintype_card]
  have hrail : ∀ g : H ⧸ A, ∀ B ∈ W.image (g * ·), ∃ T : Finset H,
      (∀ t ∈ T, (t : H ⧸ A) = B) ∧ Nat.card A ≤ T.card ∧
      HasRail (cay S) {x | (x : H ⧸ A) ∈ W.image (g * ·)} T := by
    intro g B hB
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨_, hz', rfl⟩ := Finset.mem_image.1 hB
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hz'
    refine ⟨(Z.filter (fun y => y * z⁻¹ ∈ A)).image (h * ·), ?_, ?_, ?_⟩
    · intro t ht
      obtain ⟨t0, ht0, rfl⟩ := Finset.mem_image.1 ht
      rw [QuotientGroup.mk_mul, mk_eq_of_mul_inv_mem A (Finset.mem_filter.1 ht0).2]
    · rw [Finset.card_image_of_injective _ (mul_right_injective h)]
      exact horbit z hz
    · have := (hrails z hz).map_mul_left h
      convert this using 1
      ext x
      simp only [Set.mem_setOf_eq, Finset.mem_image, Set.mem_image, Finset.mem_coe, hW]
      constructor
      · rintro ⟨_, ⟨y, hy, rfl⟩, hx⟩
        refine ⟨h⁻¹ * x, mem_of_mk_eq A (Z := (Z : Set H)) hZinv hy ?_, by group⟩
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← hx]; group
      · rintro ⟨y, hy, rfl⟩
        exact ⟨_, ⟨y, hy, rfl⟩, by rw [QuotientGroup.mk_mul]⟩
  have hX := hcor H S A W (Nat.card A) hWne (by omega) hrail
  have hmR : (0 : ℝ) < Nat.card A := by exact_mod_cast Nat.card_pos
  have hsq : ((Nat.card A : ℝ) ^ 2 / Nat.card A) = Nat.card A := by field_simp
  rw [hsq] at hX
  refine le_trans ?_ hX
  have hb1 : (1 : ℝ) ≤ W.card := by exact_mod_cast hWne.card_pos
  have hbb : (W.card : ℝ) ≤ ((1 + R * Nat.clog 2 (Nat.card A) : ℕ) : ℝ) := by exact_mod_cast hWcard
  gcongr

end Lovasz
