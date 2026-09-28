module
public import Mathlib
public import RequestProject.GRBasic

/-!
# Green–Ruzsa, finite Fourier analysis by counting

All identities are finite sums over the characters `AddChar G ℂ` of a finite abelian group,
using only the dual orthogonality relation `∑_χ χ x = |G| · [x = 0]`.

* `sum_char_mul_conj`: `∑_χ (∑_x f x χ x) conj(∑_x g x χ x) = |G| ∑_x f x conj (g x)`.
* `exists_char_large`: a sparse set with polynomially bounded iterated sumsets has a
  nontrivial character whose sum over it is almost maximal.
* `norm_sub_one_sq_le`: large character sum on `A + A` forces `χ` close to `1` at EVERY point
  of `A`.
* `bogolyubov`: the Bohr set of the large spectrum of `A` lies in `4A`, and the large spectrum
  has at most `4 (|G|/|A|)²` elements.
-/

@[expose] public section

open Finset ComplexConjugate

namespace GreenRuzsa

variable {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The character sum of a finset. -/
noncomputable def csum (A : Finset G) (χ : AddChar G ℂ) : ℂ := ∑ a ∈ A, χ a

lemma sum_char_mul_conj (f g : G → ℂ) :
    ∑ χ : AddChar G ℂ, (∑ x, f x * χ x) * conj (∑ y, g y * χ y) =
      Fintype.card G * ∑ x, f x * conj (g x) := by
  have h1 : ∀ χ : AddChar G ℂ, (∑ x, f x * χ x) * conj (∑ y, g y * χ y) =
      ∑ x, ∑ y, f x * conj (g y) * χ (x - y) := by
    intro χ
    rw [map_sum, sum_mul_sum]
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
    rw [map_mul, ← AddChar.map_neg_eq_conj, sub_eq_add_neg, AddChar.map_add_eq_mul]
    ring
  simp_rw [h1]
  rw [sum_comm]
  simp_rw [sum_comm (s := (univ : Finset (AddChar G ℂ))), ← mul_sum,
    AddChar.sum_apply_eq_ite, sub_eq_zero]
  rw [mul_sum]
  refine sum_congr rfl fun x _ => ?_
  simp [mul_comm]

lemma sum_norm_sq_char (f : G → ℂ) :
    ∑ χ : AddChar G ℂ, ‖∑ x, f x * χ x‖ ^ 2 = Fintype.card G * ∑ x, ‖f x‖ ^ 2 := by
  have h := sum_char_mul_conj f f
  simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  exact_mod_cast h

omit [Fintype G] [DecidableEq G] in
lemma addChar_map_sum {τ : Type*} (s : Finset τ) (f : τ → G) (χ : AddChar G ℂ) :
    χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [sum_insert ha, prod_insert ha, AddChar.map_add_eq_mul, ih]

/-- A sum over a family of points, grouped by value. -/
lemma sum_family_eq {τ : Type*} (T : Finset τ) (u : τ → G) (χ : AddChar G ℂ) :
    ∑ t ∈ T, χ (u t) = ∑ x, ((T.filter fun t => u t = x).card : ℂ) * χ x := by
  rw [← sum_fiberwise T u (fun t => χ (u t))]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_congr rfl (g := fun _ => χ x) (fun t ht => by rw [(mem_filter.1 ht).2]), sum_const,
    nsmul_eq_mul]

/-- Parseval for a finset. -/
lemma sum_norm_sq_csum (A : Finset G) :
    ∑ χ : AddChar G ℂ, ‖csum A χ‖ ^ 2 = Fintype.card G * A.card := by
  have h := sum_norm_sq_char (fun x => if x ∈ A then (1 : ℂ) else 0)
  have e1 : ∀ χ : AddChar G ℂ, ∑ x, (if x ∈ A then (1 : ℂ) else 0) * χ x = csum A χ := by
    intro χ
    simp [csum, ite_mul, sum_ite_mem]
  simp_rw [e1] at h
  rw [h]
  congr 1
  simp [apply_ite]

omit [Fintype G] [DecidableEq G] in
lemma csum_zero (A : Finset G) : csum A 0 = A.card := by simp [csum]

omit [DecidableEq G] in
lemma norm_csum_le (A : Finset G) (χ : AddChar G ℂ) : ‖csum A χ‖ ≤ A.card := by
  refine (norm_sum_le _ _).trans ?_
  simp [AddChar.norm_apply]

/-! ### A sparse set with small iterated sumsets has a large nontrivial character sum -/

theorem exists_char_large (D : Finset G) (hD : D.Nonempty) (k : ℕ) (R ε : ℝ)
    (hgrowth : ((ksum (k + 1) D).card : ℝ) ≤ R * D.card) (hε1 : ε ≤ 1)
    (hnum : R * (D.card / Fintype.card G + (1 - ε) ^ (2 * k)) < 1) :
    ∃ χ : AddChar G ℂ, χ ≠ 0 ∧ (1 - ε) * D.card < ‖csum D χ‖ := by
  by_contra hcon
  push_neg at hcon
  set n := k + 1 with hn
  set T := Fintype.piFinset fun _ : Fin n => D with hT
  set u : (Fin n → G) → G := fun t => ∑ i, t i with hu
  set r : G → ℕ := fun x => (T.filter fun t => u t = x).card with hr
  set s : ℝ := (D.card : ℝ) with hs
  set g : ℝ := (Fintype.card G : ℝ) with hg
  set Q : ℝ := ∑ x, (r x : ℝ) ^ 2 with hQ
  have hs0 : 0 < s := by rw [hs]; exact_mod_cast hD.card_pos
  have hg0 : 0 < g := by rw [hg]; exact_mod_cast Fintype.card_pos
  -- the moment identity
  have hpow : ∀ χ : AddChar G ℂ, ∑ t ∈ T, χ (u t) = csum D χ ^ n := by
    intro χ
    simp only [hu, addChar_map_sum, hT]
    rw [← prod_univ_sum]
    simp [csum]
  have hmom : ∑ χ : AddChar G ℂ, ‖csum D χ‖ ^ (2 * n) = g * Q := by
    have h := sum_norm_sq_char (fun x => ((r x : ℕ) : ℂ))
    have e1 : ∀ χ : AddChar G ℂ, ∑ x, ((r x : ℕ) : ℂ) * χ x = csum D χ ^ n := by
      intro χ
      rw [← hpow, sum_family_eq]
    simp_rw [e1] at h
    rw [hQ, hg]
    simp_rw [norm_pow, ← pow_mul] at h
    rw [show 2 * n = n * 2 by ring, h]
    simp
  -- Cauchy–Schwarz
  have hsumr : ∑ x, (r x : ℝ) = s ^ n := by
    have : ∑ x, r x = T.card := by
      rw [hr]
      exact (card_eq_sum_card_fiberwise (fun t _ => mem_univ (u t))).symm
    rw [hT, Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin] at this
    rw [hs]
    exact_mod_cast this
  have hsupp : ∀ x, x ∉ ksum n D → r x = 0 := by
    intro x hx
    rw [hr, card_eq_zero, filter_eq_empty_iff]
    intro t ht hux
    exact hx (hux ▸ sum_mem_ksum t (Fintype.mem_piFinset.1 ht))
  have hCS : s ^ (2 * n) ≤ R * s * Q := by
    have h1 : ∑ x ∈ ksum n D, (r x : ℝ) = s ^ n := by
      rw [← hsumr, sum_subset (subset_univ _)]
      intro x _ hx
      simp [hsupp x hx]
    have h2 := sq_sum_le_card_mul_sum_sq (s := ksum n D) (f := fun x => (r x : ℝ))
    rw [h1] at h2
    have h3 : ∑ x ∈ ksum n D, (r x : ℝ) ^ 2 ≤ Q := by
      rw [hQ]
      exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => sq_nonneg _
    calc s ^ (2 * n) = (s ^ n) ^ 2 := by ring
      _ ≤ (ksum n D).card * ∑ x ∈ ksum n D, (r x : ℝ) ^ 2 := h2
      _ ≤ R * s * Q := by
          have hQ0 : 0 ≤ ∑ x ∈ ksum n D, (r x : ℝ) ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
          calc ((ksum n D).card : ℝ) * ∑ x ∈ ksum n D, (r x : ℝ) ^ 2
              ≤ (R * s) * ∑ x ∈ ksum n D, (r x : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hgrowth hQ0
            _ ≤ R * s * Q := by
                have hRs : 0 ≤ R * s := le_trans (by positivity) hgrowth
                exact mul_le_mul_of_nonneg_left h3 hRs
  -- the upper bound on the moment
  have hup : g * Q ≤ s ^ (2 * n) + (1 - ε) ^ (2 * k) * s ^ (2 * k) * (g * s) := by
    rw [← hmom, ← add_sum_erase _ _ (mem_univ (0 : AddChar G ℂ)), csum_zero]
    refine add_le_add (le_of_eq (by simp [hs])) ?_
    calc ∑ χ ∈ univ.erase 0, ‖csum D χ‖ ^ (2 * n)
        ≤ ∑ χ ∈ univ.erase 0, ((1 - ε) * s) ^ (2 * k) * ‖csum D χ‖ ^ 2 := by
          refine sum_le_sum fun χ hχ => ?_
          have h1 := hcon χ (ne_of_mem_erase hχ)
          have h0 : 0 ≤ (1 - ε) * s := mul_nonneg (by linarith) hs0.le
          rw [show 2 * n = 2 * k + 2 by omega, pow_add]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) h1 _) (sq_nonneg _)
      _ ≤ ∑ χ : AddChar G ℂ, ((1 - ε) * s) ^ (2 * k) * ‖csum D χ‖ ^ 2 :=
          sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun _ _ _ =>
            mul_nonneg (pow_nonneg (mul_nonneg (by linarith) hs0.le) _) (sq_nonneg _)
      _ = (1 - ε) ^ (2 * k) * s ^ (2 * k) * (g * s) := by
          rw [← mul_sum, sum_norm_sq_csum, mul_pow]
  -- combine
  have hkey : s ^ (2 * n) ≤ R * s ^ (2 * n) * (s / g + (1 - ε) ^ (2 * k)) := by
    have hR : 0 ≤ R := by
      by_contra hR
      push_neg at hR
      have : R * s * Q ≤ 0 := by
        have hQ0 : 0 ≤ Q := sum_nonneg fun _ _ => sq_nonneg _
        have : R * s ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hR.le hs0.le
        exact mul_nonpos_of_nonpos_of_nonneg this hQ0
      have : 0 < s ^ (2 * n) := by positivity
      linarith
    have e : s ^ (2 * n) = s ^ (2 * k) * s ^ 2 := by rw [← pow_add]; congr 1
    calc s ^ (2 * n) ≤ R * s * Q := hCS
      _ = R * s / g * (g * Q) := by field_simp
      _ ≤ R * s / g * (s ^ (2 * n) + (1 - ε) ^ (2 * k) * s ^ (2 * k) * (g * s)) :=
          mul_le_mul_of_nonneg_left hup (by positivity)
      _ = R * s ^ (2 * n) * (s / g + (1 - ε) ^ (2 * k)) := by
          rw [e]
          field_simp
  have hpos : 0 < s ^ (2 * n) := by positivity
  have : R * s ^ (2 * n) * (s / g + (1 - ε) ^ (2 * k)) < s ^ (2 * n) := by
    calc R * s ^ (2 * n) * (s / g + (1 - ε) ^ (2 * k))
        = s ^ (2 * n) * (R * (s / g + (1 - ε) ^ (2 * k))) := by ring
      _ < s ^ (2 * n) * 1 := mul_lt_mul_of_pos_left hnum hpos
      _ = s ^ (2 * n) := mul_one _
  linarith

end GreenRuzsa
