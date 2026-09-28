module
public import RequestProject.BGTSanders

/-!
# Escape norms and strong approximate groups (Sections 7–8 of Breuillard–Green–Tao)

* `Lovasz.BGT.escNorm`: the escape norm `‖g‖_{e,A}` of Definition 4.3;
* `Lovasz.BGT.IsStrongApproxGroup`: strong approximate groups (Definition 7.1);
* `Lovasz.BGT.escNorm_conj_le`: Theorem 8.1 (i), the conjugation property of the escape norm.
-/

@[expose] public section

open scoped Pointwise

namespace Lovasz.BGT

variable {G : Type*} [Group G]

/-! ### The escape norm -/

/-- The set of `n` such that `g, g², …, gⁿ` all lie in `A` (together with `g⁰ = 1`). -/
def escSet (A : Set G) (g : G) : Set ℕ := {n | ∀ i ≤ n, g ^ i ∈ A}

/-- **Definition 4.3** of Breuillard–Green–Tao: the escape norm
`‖g‖_{e,A} = inf {1/(n+1) : gⁱ ∈ A for all 0 ≤ i ≤ n}`. -/
noncomputable def escNorm (A : Set G) (g : G) : ℝ :=
  sInf ((fun n : ℕ => (1 : ℝ) / (n + 1)) '' escSet A g)

section EscNorm

variable {A : Set G} {g : G}

lemma zero_mem_escSet (hA : 1 ∈ A) : 0 ∈ escSet A g := by
  intro i hi
  rw [Nat.le_zero.1 hi, pow_zero]; exact hA

lemma escNorm_bddBelow : BddBelow ((fun n : ℕ => (1 : ℝ) / (n + 1)) '' escSet A g) :=
  ⟨0, by rintro _ ⟨n, -, rfl⟩; positivity⟩

lemma escNorm_nonneg (hA : 1 ∈ A) : 0 ≤ escNorm A g :=
  le_csInf ⟨_, 0, zero_mem_escSet hA, rfl⟩ (by rintro _ ⟨n, -, rfl⟩; positivity)

lemma escNorm_le_of_forall {n : ℕ} (h : ∀ i ≤ n, g ^ i ∈ A) : escNorm A g ≤ 1 / (n + 1) :=
  csInf_le escNorm_bddBelow ⟨n, h, rfl⟩

lemma escNorm_le_one (hA : 1 ∈ A) : escNorm A g ≤ 1 := by
  simpa using escNorm_le_of_forall (n := 0) (zero_mem_escSet (g := g) hA)

/-- If `n ‖g‖ < 1` then `g⁰, …, gⁿ ∈ A`. -/
lemma pow_mem_of_mul_escNorm_lt (hA : 1 ∈ A) {n : ℕ} (h : n * escNorm A g < 1) :
    ∀ i ≤ n, g ^ i ∈ A := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · intro i hi; rw [Nat.le_zero.1 hi, pow_zero]; exact hA
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlt : escNorm A g < 1 / n := by rw [lt_div_iff₀ hn']; linarith
  unfold escNorm at hlt
  obtain ⟨_, ⟨m, hm, rfl⟩, hlt'⟩ := exists_lt_of_csInf_lt
    (show ((fun n : ℕ => (1 : ℝ) / (n + 1)) '' escSet A g).Nonempty from
      ⟨_, 0, zero_mem_escSet hA, rfl⟩) hlt
  have : (n : ℝ) < m + 1 := by
    rw [div_lt_div_iff₀ (by positivity) hn'] at hlt'
    linarith
  have hnm : n ≤ m := by
    have : n < m + 1 := by exact_mod_cast this
    omega
  intro i hi
  exact hm i (hi.trans hnm)

lemma mem_of_escNorm_lt_one (hA : 1 ∈ A) (h : escNorm A g < 1) : g ∈ A := by
  have := pow_mem_of_mul_escNorm_lt hA (n := 1) (by simpa using h) 1 le_rfl
  simpa using this

lemma escNorm_eq_one_of_notMem (hA : 1 ∈ A) (h : g ∉ A) : escNorm A g = 1 :=
  le_antisymm (escNorm_le_one hA) (not_lt.1 fun h' => h (mem_of_escNorm_lt_one hA h'))

lemma escNorm_one (hA : 1 ∈ A) : escNorm A (1 : G) = 0 := by
  refine le_antisymm ?_ (escNorm_nonneg hA)
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  calc escNorm A (1 : G) ≤ 1 / (n + 1) := escNorm_le_of_forall (fun i _ => by simpa using hA)
    _ < 0 + ε := by linarith

lemma escSet_inv (hA : A⁻¹ = A) : escSet A g⁻¹ = escSet A g := by
  ext n
  simp only [escSet, Set.mem_setOf_eq, inv_pow]
  constructor
  · intro h i hi
    have := h i hi
    rw [← hA]; simpa using this
  · intro h i hi
    rw [← hA]; simpa using h i hi

lemma escNorm_inv (hA : A⁻¹ = A) : escNorm A g⁻¹ = escNorm A g := by
  simp only [escNorm, escSet_inv hA]

/-- If all powers of `g` lie in `A`, the escape norm vanishes. -/
lemma escNorm_eq_zero_of_forall (hA : 1 ∈ A) (h : ∀ i : ℕ, g ^ i ∈ A) : escNorm A g = 0 := by
  refine le_antisymm ?_ (escNorm_nonneg hA)
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  calc escNorm A g ≤ 1 / (n + 1) := escNorm_le_of_forall (fun i _ => h i)
    _ < 0 + ε := by linarith

/-- If `‖g‖ = 0` then all powers of `g` lie in `A`. -/
lemma pow_mem_of_escNorm_eq_zero (hA : 1 ∈ A) (h : escNorm A g = 0) (i : ℕ) : g ^ i ∈ A :=
  pow_mem_of_mul_escNorm_lt hA (n := i) (by rw [h]; simp) i le_rfl

end EscNorm

/-! ### Strong approximate groups -/

/-- The set of conjugates `S^B = {b⁻¹ s b : s ∈ S, b ∈ B}`. -/
def conjSet (S B : Set G) : Set G := {x | ∃ s ∈ S, ∃ b ∈ B, x = b⁻¹ * s * b}

/-- **Definition 7.1** of Breuillard–Green–Tao: a strong `K`-approximate group is a
`K`-approximate group `A` admitting a symmetric set `S` with `(S^{A⁴})^{1000K³} ⊆ A`, such that
* (first trapping condition) if `g, g², …, g¹⁰⁰⁰ ∈ A¹⁰⁰` then `g ∈ A`;
* (second trapping condition) if `g, g², …, g^{10⁶K³} ∈ A` then `g ∈ S`.

The (real) exponents are rounded in the direction that makes the hypotheses weaker: the exponent
`1000K³` is rounded down and `10⁶K³` is rounded up. -/
def IsStrongApproxGroup (K : ℝ) (A : Set G) : Prop :=
  IsBGTApproxGroup K A ∧ ∃ S : Set G, S⁻¹ = S ∧
    conjSet S (A ^ 4) ^ ⌊1000 * K ^ 3⌋₊ ⊆ A ∧
    (∀ g : G, (∀ i : ℕ, 1 ≤ i → i ≤ 1000 → g ^ i ∈ A ^ 100) → g ∈ A) ∧
    (∀ g : G, (∀ i : ℕ, 1 ≤ i → i ≤ ⌈10 ^ 6 * K ^ 3⌉₊ → g ^ i ∈ A) → g ∈ S)

/-- The first trapping condition, iterated: if `g⁰, …, gⁿ ∈ A¹⁰⁰`, then `gʲ ∈ A` whenever
`1000 j ≤ n`. -/
lemma pow_mem_of_first_trapping {A : Set G}
    (htrap : ∀ g : G, (∀ i : ℕ, 1 ≤ i → i ≤ 1000 → g ^ i ∈ A ^ 100) → g ∈ A)
    {g : G} {n : ℕ} (h : ∀ i ≤ n, g ^ i ∈ A ^ 100) {j : ℕ} (hj : 1000 * j ≤ n) : g ^ j ∈ A := by
  apply htrap
  intro i _ hi
  rw [← pow_mul]
  exact h _ (le_trans (by nlinarith) hj)

/-- The escape-norm consequence of the first trapping condition: if `g⁰, …, gⁿ ∈ A¹⁰⁰` then
`‖g‖ ≤ 1000/(n+1)`. -/
lemma escNorm_le_of_first_trapping {A : Set G}
    (htrap : ∀ g : G, (∀ i : ℕ, 1 ≤ i → i ≤ 1000 → g ^ i ∈ A ^ 100) → g ∈ A)
    {g : G} {n : ℕ} (h : ∀ i ≤ n, g ^ i ∈ A ^ 100) : escNorm A g ≤ 1000 / (n + 1) := by
  have h1 := escNorm_le_of_forall (A := A) (g := g) (n := n / 1000)
    (fun i hi => pow_mem_of_first_trapping htrap h (by
      have := Nat.mul_div_le n 1000
      nlinarith [Nat.mul_le_mul_left 1000 hi]))
  refine h1.trans ?_
  have : (n : ℝ) + 1 ≤ 1000 * ((n / 1000 : ℕ) + 1) := by
    have : n + 1 ≤ 1000 * (n / 1000 + 1) := by
      have := Nat.lt_div_mul_add (a := n) (b := 1000) (by norm_num)
      linarith
    exact_mod_cast this
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/-- **Theorem 8.1 (i)** of Breuillard–Green–Tao (conjugation property of the escape norm): if `A`
is a strong approximate group, `g ∈ A¹⁰` and `h ∈ A¹⁰`, then `‖h⁻¹ g h‖ ≤ 1000 ‖g‖`.  (The proof
works for all conjugators `h ∈ A⁴⁹`.) -/
theorem escNorm_conj_le {K : ℝ} {A : Set G} (hA : IsStrongApproxGroup K A) {g h : G}
    (hh : h ∈ A ^ 49) : escNorm A (h⁻¹ * g * h) ≤ 1000 * escNorm A g := by
  obtain ⟨⟨-, hA1, hAinv, -⟩, S, -, -, htrap, -⟩ := hA
  have hh' : h⁻¹ ∈ A ^ 49 := by
    have : (A ^ 49)⁻¹ = A ^ 49 := by rw [← inv_pow, hAinv]
    rw [← this]; exact Set.inv_mem_inv.2 hh
  -- conjugates of elements of `A` lie in `A¹⁰⁰`
  have hconj : ∀ i : ℕ, g ^ i ∈ A → (h⁻¹ * g * h) ^ i ∈ A ^ 100 := by
    intro i hi
    have e : (h⁻¹ * g * h) ^ i = h⁻¹ * g ^ i * h := by
      simpa using conj_pow (a := h⁻¹) (b := g) (i := i)
    rw [e]
    have : h⁻¹ * g ^ i * h ∈ A ^ 49 * A * A ^ 49 :=
      Set.mul_mem_mul (Set.mul_mem_mul hh' hi) hh
    rw [← pow_succ, ← pow_add] at this
    exact Set.pow_subset_pow_right hA1 (by norm_num) this
  rcases (escNorm_nonneg (g := g) hA1).lt_or_eq with hpos | hzero
  · set m := ⌈1 / escNorm A g⌉₊ with hm
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (by
      rw [hm]; exact (Nat.ceil_pos.2 (by positivity)).ne')
    have hmle : 1 / escNorm A g ≤ m := Nat.le_ceil _
    have hmlt : (m : ℝ) < 1 / escNorm A g + 1 := Nat.ceil_lt_add_one (by positivity)
    have hcast : ((m - 1 : ℕ) : ℝ) = m - 1 := by rw [Nat.cast_sub hm1, Nat.cast_one]
    have hn : ((m - 1 : ℕ) : ℝ) * escNorm A g < 1 := by
      rw [hcast]
      have : ((m : ℝ) - 1) < 1 / escNorm A g := by linarith
      calc ((m : ℝ) - 1) * escNorm A g < 1 / escNorm A g * escNorm A g :=
            mul_lt_mul_of_pos_right this hpos
        _ = 1 := by field_simp
    have hpow := pow_mem_of_mul_escNorm_lt hA1 hn
    have h1 := escNorm_le_of_first_trapping htrap (fun i hi => hconj i (hpow i hi))
    refine h1.trans ?_
    rw [hcast, sub_add_cancel, div_le_iff₀ (by linarith)]
    have : 1 ≤ escNorm A g * m := by
      rw [div_le_iff₀ hpos] at hmle; linarith
    nlinarith
  · rw [← hzero, mul_zero]
    refine le_of_eq (escNorm_eq_zero_of_forall hA1 fun j => ?_)
    refine pow_mem_of_first_trapping htrap (n := 1000 * j) (fun i _ => hconj i ?_) le_rfl
    exact pow_mem_of_escNorm_eq_zero hA1 hzero.symm i

end Lovasz.BGT
