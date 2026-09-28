module
public import Mathlib
public import RequestProject.GRLattice

/-!
# Green–Ruzsa, the lattice box theorem

For a full-rank lattice `L ≤ ℤ^ι` (containing `N ℤ^ι`, `N > 0`) and `M ≥ 0`, there are lattice
vectors `v_j` and lengths `ℓ_j` (`j < d = |ι|`) such that the box `{∑ n_j v_j : |n_j| ≤ ℓ_j}` lies in
the cube of radius `M`, is injectively parametrized, and the number of lattice points in the cube is
at most `(4d)^d ∏ (2ℓ_j + 1)`.
-/

@[expose] public section

open Finset

namespace GreenRuzsa

variable {ι : Type} [Fintype ι]

omit [Fintype ι] in
lemma castQ_eq_sum [Fintype ι] [DecidableEq ι] (x : ι → ℤ) :
    castQ x = ∑ i, (x i : ℚ) • (Pi.single i (1 : ℚ) : ι → ℚ) := by
  funext k
  simp [castQ, Finset.sum_apply, Pi.single_apply]

/-- Integer-valued forms proportional to the coordinate functionals of a rational basis. -/
lemma exists_int_forms [DecidableEq ι] {d : ℕ} (b : Module.Basis (Fin d) ℚ (ι → ℚ)) :
    ∃ (D : ℕ) (π : Fin d → (ι → ℤ) →+ ℤ), 0 < D ∧
      ∀ j x, (π j x : ℚ) = D * b.coord j (castQ x) := by
  set D : ℕ := ∏ j, ∏ i, (b.coord j (Pi.single i 1)).den with hDdef
  have hD : 0 < D := prod_pos fun j _ => prod_pos fun i _ => Rat.den_pos _
  have hint : ∀ j i, ∃ z : ℤ, (z : ℚ) = D * b.coord j (Pi.single i 1) := by
    intro j i
    have hdvd : (b.coord j (Pi.single i 1)).den ∣ D :=
      (dvd_prod_of_mem (fun i => (b.coord j (Pi.single i 1)).den) (mem_univ i)).trans
        (dvd_prod_of_mem (fun j => ∏ i, (b.coord j (Pi.single i 1)).den) (mem_univ j))
    obtain ⟨k, hk⟩ := hdvd
    refine ⟨k * (b.coord j (Pi.single i 1)).num, ?_⟩
    rw [hk]
    push_cast
    rw [← Rat.mul_den_eq_num]
    ring
  choose c hc using hint
  refine ⟨D, fun j => AddMonoidHom.mk' (fun x => ∑ i, x i * c j i)
    (by intro x y; simp [add_mul, sum_add_distrib]), hD, fun j x => ?_⟩
  simp only [AddMonoidHom.mk'_apply]
  push_cast
  rw [castQ_eq_sum, map_sum, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [hc, map_smul, smul_eq_mul]
  ring

/-- **The lattice box theorem.** -/
theorem lattice_box [DecidableEq ι] [Nonempty ι] (L : AddSubgroup (ι → ℤ)) (N : ℕ) (hN : 0 < N)
    (hNL : ∀ i, (N : ℤ) • (Pi.single i 1 : ι → ℤ) ∈ L) (M : ℕ) :
    ∃ (v : Fin (Fintype.card ι) → ι → ℤ) (ℓ : Fin (Fintype.card ι) → ℕ),
      (∀ j, v j ∈ L) ∧
      (∀ n : Fin (Fintype.card ι) → ℤ, (∀ j, |n j| ≤ ℓ j) → supN (∑ j, n j • v j) ≤ M) ∧
      (∀ n : Fin (Fintype.card ι) → ℤ, ∑ j, n j • v j = 0 → n = 0) ∧
      (cubePts L M).card ≤
        (4 * Fintype.card ι) ^ Fintype.card ι * ∏ j, (2 * ℓ j + 1) := by
  classical
  set d := Fintype.card ι with hddef
  have hd : 0 < d := Fintype.card_pos
  have hli := gv_linearIndependent hN hNL d le_rfl
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  set b := basisOfLinearIndependentOfCardEqFinrank hli
    (by simp [Module.finrank_fintype_fun_eq_card, hddef]) with hbdef
  have hbv : ∀ j, b j = castQ (gv L j) := fun j => by
    rw [hbdef, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hcoord : ∀ j k : Fin d, b.coord j (castQ (gv L k)) = if k = j then 1 else 0 := by
    intro j k
    rw [← hbv, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  have hspan : ∀ (j : Fin d) x, x ∈ spanQ (greedySet L j) → b.coord j x = 0 := by
    intro j x hx
    rw [spanQ, greedySet_coe, ← Set.image_comp] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, hk, rfl⟩ := hy
      have := hcoord j ⟨k, hk.trans j.2⟩
      simp only [Function.comp]
      rw [this, if_neg]
      intro h
      have := congrArg Fin.val h
      simp only at this
      simp only [Set.mem_setOf_eq] at hk
      omega
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul a x _ hx => rw [map_smul, hx, smul_zero]
  obtain ⟨D, π, hD, hπ⟩ := exists_int_forms b
  set πN : ℕ → (ι → ℤ) →+ ℤ := fun k => if h : k < d then π ⟨k, h⟩ else 0 with hπN
  have hπN' : ∀ (k : ℕ) (hk : k < d) x, πN k x = π ⟨k, hk⟩ x := fun k hk x => by
    simp [hπN, hk]
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  -- the forms vanish on later greedy vectors
  have hπgv : ∀ (k : ℕ) (hk : k < d) (j : ℕ) (hj : j < d),
      πN k (gv L j) = if j = k then (D : ℤ) else 0 := by
    intro k hk j hj
    rw [hπN' k hk]
    have := hπ ⟨k, hk⟩ (gv L j)
    rw [hcoord ⟨k, hk⟩ ⟨j, hj⟩] at this
    by_cases hjk : j = k
    · subst hjk
      rw [if_pos rfl] at this
      rw [if_pos rfl]
      exact_mod_cast (this.trans (mul_one _))
    · have hne : (⟨j, hj⟩ : Fin d) ≠ ⟨k, hk⟩ := fun h => hjk (Fin.ext_iff.1 h)
      rw [if_neg hne] at this
      rw [if_neg hjk]
      exact_mod_cast (this.trans (mul_zero _))
  set lam : ℕ → ℕ := fun k => supN (gv L k) with hlam
  have hlam1 : ∀ k < d, 1 ≤ lam k := fun k hk => one_le_supN_gv hN hNL hk
  have hex : ∀ k < d, ∃ e : ℕ, 2 * M < 2 ^ e * lam k := by
    intro k hk
    refine ⟨2 * M + 1, ?_⟩
    have h1 := Nat.lt_two_pow_self (n := 2 * M + 1)
    have h2 := hlam1 k hk
    nlinarith
  set e : ℕ → ℕ := fun k => if h : k < d then Nat.find (hex k h) else 0 with he
  set m : ℕ → ℕ := fun k => 2 ^ e k with hm
  have hm_spec : ∀ k < d, 2 * M < m k * lam k := by
    intro k hk
    simp only [hm, he, dif_pos hk]
    exact Nat.find_spec (hex k hk)
  have hm_upper : ∀ k < d, 0 < e k → m k * lam k ≤ 4 * M := by
    intro k hk hek
    have hmin : ¬ 2 * M < 2 ^ (e k - 1) * lam k := by
      have := Nat.find_min (hex k hk) (m := e k - 1) (by simp only [he, dif_pos hk] at hek ⊢; omega)
      exact this
    push_neg at hmin
    have : m k = 2 * 2 ^ (e k - 1) := by
      simp only [hm]
      rw [← pow_succ']
      congr 1
      omega
    rw [this]
    nlinarith
  have hdvd : ∀ i j, i ≤ j → j < d → m j ∣ m i := by
    intro i j hij hj
    refine pow_dvd_pow 2 ?_
    simp only [he, dif_pos hj, dif_pos (hij.trans_lt hj)]
    refine Nat.find_mono fun n hn => ?_
    have := gv_mono hN hNL hij hj
    calc 2 * M < 2 ^ n * lam i := hn
      _ ≤ 2 ^ n * lam j := Nat.mul_le_mul_left _ this
  have hsep : ∀ x ∈ L, (∀ k < d, πN k x = 0) → x = 0 := by
    intro x _ hx
    have hc : castQ x = 0 := by
      rw [← b.forall_coord_eq_zero_iff]
      intro j
      have h1 := hπ j x
      rw [← hπN' j j.2, hx j j.2] at h1
      simp only [Int.cast_zero] at h1
      rcases mul_eq_zero.1 h1.symm with h | h
      · exact absurd h hDq
      · exact h
    exact castQ_injective (hc.trans castQ_zero.symm)
  have hflag_gv : ∀ j < d, flagMem L d πN (j + 1) (gv L j) := by
    intro j hj
    refine ⟨(gv_spec hN hNL hj).1, fun k hk hkd => ?_⟩
    rw [hπgv k hkd j hj, if_neg (by omega)]
  have hb : ∀ j < d, ∃ (bj : ι → ℤ) (aj : ℤ), flagMem L d πN (j + 1) bj ∧ πN j bj = aj ∧
      0 < aj ∧ ∀ x, flagMem L d πN (j + 1) x → aj ∣ πN j x := by
    intro j hj
    have hP : ∃ n : ℕ, 0 < n ∧ ∃ x, flagMem L d πN (j + 1) x ∧ πN j x = n :=
      ⟨D, hD, gv L j, hflag_gv j hj, by rw [hπgv j hj j hj, if_pos rfl]⟩
    obtain ⟨hn0, x0, hx0, hx0v⟩ := Nat.find_spec hP
    refine ⟨x0, Nat.find hP, hx0, hx0v, by exact_mod_cast hn0, fun y hy => ?_⟩
    set n0 := Nat.find hP
    have hn0z : (0 : ℤ) < n0 := by exact_mod_cast hn0
    set r := πN j y % n0
    set q := πN j y / n0
    have hr0 : 0 ≤ r := Int.emod_nonneg _ hn0z.ne'
    have hrlt : r < n0 := Int.emod_lt_of_pos _ hn0z
    have hflag : flagMem L d πN (j + 1) (y - q • x0) := by
      refine ⟨L.sub_mem hy.1 (L.zsmul_mem hx0.1 _), fun k hk hkd => ?_⟩
      rw [map_sub, map_zsmul, hy.2 k hk hkd, hx0.2 k hk hkd, smul_zero, sub_zero]
    have hval : πN j (y - q • x0) = r := by
      simp only [map_sub, map_zsmul, smul_eq_mul, hx0v]
      have := Int.emod_add_mul_ediv (πN j y) n0
      simp only [r, q]
      linarith
    by_contra hndvd
    have hr : 0 < r := by
      rcases eq_or_lt_of_le hr0 with h | h
      · exact absurd (Int.dvd_of_emod_eq_zero h.symm) hndvd
      · exact h
    have := Nat.find_min hP (m := r.toNat) (by omega)
    exact this ⟨by omega, y - q • x0, hflag, by rw [hval]; omega⟩
  have hS : ∀ x ∈ cubePts L M, ∀ y ∈ cubePts L M, ∀ i < d, ∀ w, flagMem L d πN (i + 1) w →
      πN i w ≠ 0 → x - y ≠ (m i : ℤ) • w := by
    intro x hx y hy i hi w hw hwi heq
    have hnot : castQ w ∉ spanQ (greedySet L i) := by
      intro hmem
      have h1 := hspan ⟨i, hi⟩ _ hmem
      have h2 := hπ ⟨i, hi⟩ w
      rw [h1, mul_zero, ← hπN' i hi] at h2
      exact hwi (by exact_mod_cast h2)
    have hlw := (gv_spec hN hNL hi).2.2 w hw.1 hnot
    have hxy : supN (x - y) ≤ 2 * M := by
      have := supN_sub_le x y
      rw [mem_cubePts] at hx hy
      omega
    have hmw := le_supN_zsmul (m i : ℤ) w
    rw [← heq] at hmw
    simp only [Int.natAbs_natCast] at hmw
    have := hm_spec i hi
    have : m i * lam i ≤ m i * supN w := Nat.mul_le_mul_left _ hlw
    omega
  have hcount := card_le_prod_of_flag L d πN m (fun j _ => by positivity) hdvd hsep hb d le_rfl
    (cubePts L M) (fun x hx => ⟨(mem_cubePts.1 hx).1, fun k hk hkd => absurd hkd (by omega)⟩) hS
  -- the box
  set ℓ : Fin d → ℕ := fun j => M / (d * lam j) with hℓ
  refine ⟨fun j => gv L j, ℓ, fun j => (gv_spec hN hNL j.2).1, ?_, ?_, ?_⟩
  · intro n hn
    have hterm : ∀ j : Fin d, supN (n j • gv L j) ≤ M / d := by
      intro j
      refine (supN_zsmul_le _ _).trans ?_
      have h1 : (n j).natAbs ≤ ℓ j := by
        have := hn j
        have h' : ((n j).natAbs : ℤ) = |n j| := Int.natCast_natAbs _
        omega
      have h2 : ℓ j * (d * lam j) ≤ M := Nat.div_mul_le_self _ _
      rw [Nat.le_div_iff_mul_le hd]
      calc (n j).natAbs * supN (gv L j) * d ≤ ℓ j * lam j * d :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h1)
        _ = ℓ j * (d * lam j) := by ring
        _ ≤ M := h2
    calc supN (∑ j, n j • gv L j) ≤ ∑ j, supN (n j • gv L j) := supN_sum_le _ _
      _ ≤ ∑ _j : Fin d, M / d := sum_le_sum fun j _ => hterm j
      _ = d * (M / d) := by simp
      _ ≤ M := Nat.mul_div_le M d
  · intro n hn
    have h1 : ∑ j, (n j : ℚ) • castQ (gv L j) = 0 := by
      have := congrArg castQ hn
      rw [castQ_sum, castQ_zero] at this
      simp only [castQ_zsmul] at this
      exact this
    funext j
    have := Fintype.linearIndependent_iff.1 hli (fun j => (n j : ℚ)) h1 j
    exact_mod_cast this
  · have hmj : ∀ j : Fin d, m j ≤ 4 * d * (2 * ℓ j + 1) := by
      intro j
      by_cases hej : e j = 0
      · have : m j = 1 := by simp [hm, hej]
        rw [this]
        have : 1 ≤ 4 * d := by omega
        nlinarith
      · have h1 := hm_upper j j.2 (Nat.pos_of_ne_zero hej)
        have h3 := hlam1 j j.2
        have h2 : M < (ℓ j + 1) * (d * lam j) := by
          have hpos : 0 < d * lam j := Nat.mul_pos hd h3
          have e1 := Nat.div_add_mod M (d * lam j)
          have e2 := Nat.mod_lt M hpos
          simp only [hℓ]
          nlinarith
        have h4 : m j * lam j < 4 * d * (ℓ j + 1) * lam j := by nlinarith
        have h5 : m j < 4 * d * (ℓ j + 1) := Nat.lt_of_mul_lt_mul_right h4
        nlinarith
    calc (cubePts L M).card ≤ ∏ i ∈ range d, m i := hcount
      _ = ∏ j : Fin d, m j := prod_range _
      _ ≤ ∏ j : Fin d, (4 * d * (2 * ℓ j + 1)) := prod_le_prod' fun j _ => hmj j
      _ = (4 * d) ^ d * ∏ j, (2 * ℓ j + 1) := by
        rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]

end GreenRuzsa
