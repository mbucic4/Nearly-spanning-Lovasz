module
public import Mathlib
public import RequestProject.GRLatticeCount

/-!
# Green–Ruzsa, a large box inside the lattice points of a cube

Let `L ≤ ℤ^ι` be a full-rank lattice (it contains `N ℤ^ι`).  We choose greedy short vectors
`v_j` (each of minimal sup norm outside the rational span of the previous ones), an auxiliary
integral coordinate system adapted to the flag they span, and dyadic moduli.  The counting lemma
of `GRLatticeCount` then shows that the lattice points of sup norm at most `M` number at most
`(4d)^d` times the size of the box `{∑ n_j v_j : |n_j| ≤ ℓ_j}`, which itself lies in the cube.
No volume or successive-minima theory is used.
-/

@[expose] public section

open Finset

namespace GreenRuzsa

variable {ι : Type} [Fintype ι]

/-! ### The sup norm -/

/-- The sup norm of an integer vector. -/
def supN (x : ι → ℤ) : ℕ := Finset.univ.sup fun i => (x i).natAbs

lemma natAbs_le_supN (x : ι → ℤ) (i : ι) : (x i).natAbs ≤ supN x :=
  Finset.le_sup (f := fun i => (x i).natAbs) (mem_univ i)

lemma supN_le_iff {x : ι → ℤ} {M : ℕ} : supN x ≤ M ↔ ∀ i, (x i).natAbs ≤ M := by
  simp [supN, Finset.sup_le_iff]

lemma supN_zero : supN (0 : ι → ℤ) = 0 := by
  simp [supN]

lemma eq_zero_of_supN_eq_zero {x : ι → ℤ} (h : supN x = 0) : x = 0 := by
  funext i
  have := natAbs_le_supN x i
  rw [h] at this
  simpa using this

lemma supN_add_le (x y : ι → ℤ) : supN (x + y) ≤ supN x + supN y := by
  rw [supN_le_iff]
  intro i
  exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add (natAbs_le_supN x i) (natAbs_le_supN y i))

lemma supN_neg (x : ι → ℤ) : supN (-x) = supN x := by
  simp [supN]

lemma supN_sub_le (x y : ι → ℤ) : supN (x - y) ≤ supN x + supN y := by
  rw [sub_eq_add_neg]
  exact (supN_add_le _ _).trans (by rw [supN_neg])

lemma supN_zsmul_le (n : ℤ) (x : ι → ℤ) : supN (n • x) ≤ n.natAbs * supN x := by
  rw [supN_le_iff]
  intro i
  simp only [Pi.smul_apply, smul_eq_mul, Int.natAbs_mul]
  exact Nat.mul_le_mul_left _ (natAbs_le_supN x i)

lemma le_supN_zsmul [Nonempty ι] (n : ℤ) (x : ι → ℤ) : n.natAbs * supN x ≤ supN (n • x) := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup (univ : Finset ι) univ_nonempty
    (fun i => (x i).natAbs)
  have : supN x = (x i).natAbs := hi
  rw [this]
  have := natAbs_le_supN (n • x) i
  simpa [Int.natAbs_mul] using this

lemma supN_sum_le {κ : Type*} (s : Finset κ) (f : κ → ι → ℤ) :
    supN (∑ j ∈ s, f j) ≤ ∑ j ∈ s, supN (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [supN_zero]
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (supN_add_le _ _).trans (Nat.add_le_add_left ih _)

/-- The lattice points of `L` in the cube of radius `M`. -/
noncomputable def cubePts (L : AddSubgroup (ι → ℤ)) (M : ℕ) : Finset (ι → ℤ) := by
  classical exact (Fintype.piFinset fun _ => Finset.Icc (-(M : ℤ)) M).filter (· ∈ L)

lemma mem_cubePts {L : AddSubgroup (ι → ℤ)} {M : ℕ} {x : ι → ℤ} :
    x ∈ cubePts L M ↔ x ∈ L ∧ supN x ≤ M := by
  classical
  simp only [cubePts, mem_filter, Fintype.mem_piFinset, mem_Icc, supN_le_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, fun i => by have := h1 i; omega⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => by have := h2 i; omega, h1⟩

/-! ### Greedy short vectors -/

/-- Rational coordinates. -/
def castQ (x : ι → ℤ) : ι → ℚ := fun i => (x i : ℚ)

omit [Fintype ι] in
lemma castQ_add (x y : ι → ℤ) : castQ (x + y) = castQ x + castQ y := by
  funext i; simp [castQ]

omit [Fintype ι] in
lemma castQ_zsmul (n : ℤ) (x : ι → ℤ) : castQ (n • x) = (n : ℚ) • castQ x := by
  funext i; simp [castQ]

omit [Fintype ι] in
lemma castQ_zero : castQ (0 : ι → ℤ) = 0 := by
  funext i; simp [castQ]

omit [Fintype ι] in
lemma castQ_sum {κ : Type*} (s : Finset κ) (f : κ → ι → ℤ) :
    castQ (∑ j ∈ s, f j) = ∑ j ∈ s, castQ (f j) := by
  funext i; simp [castQ]

omit [Fintype ι] in
lemma castQ_injective : Function.Injective (castQ : (ι → ℤ) → ι → ℚ) := by
  intro x y h
  funext i
  have := congrFun h i
  simpa [castQ] using this

/-- The rational span of a finite set of integer vectors. -/
def spanQ (S : Finset (ι → ℤ)) : Submodule ℚ (ι → ℚ) :=
  Submodule.span ℚ (castQ '' (S : Set (ι → ℤ)))

/-- Lattice vectors outside the rational span of `S`. -/
def goodSet (L : AddSubgroup (ι → ℤ)) (S : Finset (ι → ℤ)) : Set (ι → ℤ) :=
  {w | w ∈ L ∧ castQ w ∉ spanQ S}

open Classical in
/-- A shortest lattice vector outside the rational span of `S`. -/
noncomputable def nextVec (L : AddSubgroup (ι → ℤ)) (S : Finset (ι → ℤ)) : ι → ℤ :=
  if h : (goodSet L S).Nonempty then Function.argminOn supN (goodSet L S) h else 0

/-- The first `n` greedy vectors, as a finset. -/
noncomputable def greedySet (L : AddSubgroup (ι → ℤ)) : ℕ → Finset (ι → ℤ)
  | 0 => ∅
  | n + 1 => insert (nextVec L (greedySet L n)) (greedySet L n)

/-- The `n`-th greedy vector. -/
noncomputable def gv (L : AddSubgroup (ι → ℤ)) (n : ℕ) : ι → ℤ := nextVec L (greedySet L n)

section Greedy

variable (L : AddSubgroup (ι → ℤ))

lemma greedySet_coe (n : ℕ) : (greedySet L n : Set (ι → ℤ)) = gv L '' {m | m < n} := by
  induction n with
  | zero => simp [greedySet]
  | succ n ih =>
    rw [greedySet, coe_insert, ih]
    ext x
    simp only [Set.mem_insert_iff, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro (rfl | ⟨m, hm, rfl⟩)
      · exact ⟨n, by omega, rfl⟩
      · exact ⟨m, by omega, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hm | rfl
      · exact Or.inr ⟨m, hm, rfl⟩
      · exact Or.inl rfl

lemma greedySet_card_le (n : ℕ) : (greedySet L n).card ≤ n := by
  induction n with
  | zero => simp [greedySet]
  | succ n ih =>
    rw [greedySet]
    exact (card_insert_le _ _).trans (by omega)

lemma greedySet_mono {i j : ℕ} (h : i ≤ j) : greedySet L i ⊆ greedySet L j := by
  induction j, h using Nat.le_induction with
  | base => exact subset_rfl
  | succ j _ ih => exact ih.trans (by rw [greedySet]; exact subset_insert _ _)

omit [Fintype ι] in
lemma spanQ_mono {S T : Finset (ι → ℤ)} (h : S ⊆ T) : spanQ S ≤ spanQ T :=
  Submodule.span_mono (Set.image_mono (by exact_mod_cast h))

variable {L} [DecidableEq ι] {N : ℕ} (hN : 0 < N) (hNL : ∀ i, (N : ℤ) • (Pi.single i 1 : ι → ℤ) ∈ L)
include hN hNL

lemma goodSet_nonempty {n : ℕ} (hn : n < Fintype.card ι) : (goodSet L (greedySet L n)).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty, Set.eq_empty_iff_forall_notMem] at h
  have hall : ∀ w ∈ L, castQ w ∈ spanQ (greedySet L n) := by
    intro w hw
    by_contra hc
    exact h w ⟨hw, hc⟩
  have htop : spanQ (greedySet L n) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun ℚ ι).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h1 := hall _ (hNL i)
    rw [castQ_zsmul] at h1
    have h2 := Submodule.smul_mem (spanQ (greedySet L n)) ((N : ℚ)⁻¹) h1
    rw [smul_smul] at h2
    have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
    have : castQ (Pi.single i 1 : ι → ℤ) = Pi.basisFun ℚ ι i := by
      funext k
      simp [castQ, Pi.single_apply]
    simpa [hN', this] using h2
  have hle : Module.finrank ℚ (spanQ (greedySet L n)) ≤ n := by
    have := finrank_span_finset_le_card (R := ℚ) ((greedySet L n).image castQ)
    rw [coe_image] at this
    exact this.trans (card_image_le.trans (greedySet_card_le L n))
  rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card] at hle
  omega

lemma gv_spec {n : ℕ} (hn : n < Fintype.card ι) :
    gv L n ∈ L ∧ castQ (gv L n) ∉ spanQ (greedySet L n) ∧
      ∀ w ∈ L, castQ w ∉ spanQ (greedySet L n) → supN (gv L n) ≤ supN w := by
  have hne := goodSet_nonempty hN hNL hn
  have hgv : gv L n = Function.argminOn supN (goodSet L (greedySet L n)) hne := by
    classical
    simp only [gv, nextVec, dif_pos hne]
  rw [hgv]
  have hmem := Function.argminOn_mem supN _ hne
  exact ⟨hmem.1, hmem.2, fun w hw hw' =>
    Function.argminOn_le supN (goodSet L (greedySet L n)) (a := w) ⟨hw, hw'⟩⟩

lemma gv_mono {i j : ℕ} (hij : i ≤ j) (hj : j < Fintype.card ι) :
    supN (gv L i) ≤ supN (gv L j) := by
  obtain ⟨hjL, hjs, -⟩ := gv_spec hN hNL hj
  exact (gv_spec hN hNL (hij.trans_lt hj)).2.2 _ hjL fun h =>
    hjs (spanQ_mono (greedySet_mono L hij) h)

lemma one_le_supN_gv {j : ℕ} (hj : j < Fintype.card ι) : 1 ≤ supN (gv L j) := by
  obtain ⟨-, hjs, -⟩ := gv_spec hN hNL hj
  by_contra h
  push_neg at h
  have h0 := eq_zero_of_supN_eq_zero (Nat.lt_one_iff.1 h)
  rw [h0, castQ_zero] at hjs
  exact hjs (Submodule.zero_mem _)

lemma gv_linearIndependent :
    ∀ n ≤ Fintype.card ι, LinearIndependent ℚ (fun j : Fin n => castQ (gv L j)) := by
  intro n
  induction n with
  | zero => intro _; exact linearIndependent_empty_type
  | succ n ih =>
    intro hn
    have heq : (fun j : Fin (n + 1) => castQ (gv L j)) =
        Fin.snoc (fun j : Fin n => castQ (gv L j)) (castQ (gv L n)) := by
      funext j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simp
      · simp
    rw [heq, linearIndependent_fin_snoc]
    refine ⟨ih (by omega), ?_⟩
    have hrange : Set.range (fun j : Fin n => castQ (gv L j)) =
        castQ '' (greedySet L n : Set (ι → ℤ)) := by
      rw [greedySet_coe, ← Set.image_comp]
      ext x
      simp only [Set.mem_range, Set.mem_image, Set.mem_setOf_eq, Function.comp]
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨j, j.2, rfl⟩
      · rintro ⟨m, hm, rfl⟩
        exact ⟨⟨m, hm⟩, rfl⟩
    rw [hrange]
    exact (gv_spec hN hNL (by omega)).2.1

end Greedy

end GreenRuzsa
