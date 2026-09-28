module
public import Mathlib

/-!
# Green–Ruzsa, roots-of-unity coordinates for characters

* `expQ q t = exp (2πi t / q)`, and `expQ q t = expQ q t' ↔ t ≡ t' (mod q)`.
* Every character with `χ^q = 1` is `g ↦ expQ q (ψ g)` for a homomorphism `ψ : G → ℤ/q`.
* A nontrivial character is `expQ q ∘ ψ` for a SURJECTIVE `ψ : G → ℤ/q` with `q ≥ 2`.
* The chord estimate `‖expQ q λ - 1‖ ≥ 4|λ|/q` for `|λ| ≤ q/2`, and `Re (expQ N t) ≥ 1/2`
  for `8|t| ≤ N`.
-/

@[expose] public section

open Complex

namespace GreenRuzsa

/-- The standard parametrization `t ↦ exp (2πi t / q)`. -/
noncomputable def expQ (q : ℕ) (t : ℤ) : ℂ := exp (2 * Real.pi * I * t / q)

lemma expQ_add (q : ℕ) (a b : ℤ) : expQ q (a + b) = expQ q a * expQ q b := by
  rw [expQ, expQ, expQ, ← exp_add]
  congr 1
  push_cast
  ring

lemma expQ_zero (q : ℕ) : expQ q 0 = 1 := by simp [expQ]

lemma expQ_eq_iff {q : ℕ} (hq : 0 < q) (a b : ℤ) :
    expQ q a = expQ q b ↔ (a : ZMod q) = b := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub, expQ, expQ, exp_eq_exp_iff_exists_int]
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, I_ne_zero]
  constructor
  · rintro ⟨n, hn⟩
    field_simp at hn
    refine ⟨-n, ?_⟩
    have : a = b + q * n := by exact_mod_cast hn
    linarith
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    have : (a : ℂ) = b - q * n := by exact_mod_cast (by linarith : a = b - q * n)
    rw [this]
    field_simp
    push_cast
    ring

lemma expQ_intCast_mod {q : ℕ} (hq : 0 < q) (t : ℤ) :
    expQ q t = expQ q ((t : ZMod q).val : ℤ) := by
  haveI : NeZero q := ⟨hq.ne'⟩
  rw [expQ_eq_iff hq, Int.cast_natCast, ZMod.natCast_zmod_val]

variable {G : Type*} [AddCommGroup G]

/-- Characters of exponent dividing `q` are given by homomorphisms to `ℤ/q`. -/
lemma addChar_param_of_pow (q : ℕ) (hq : 0 < q) (χ : AddChar G ℂ) (h : ∀ g, χ g ^ q = 1) :
    ∃ ψ : G →+ ZMod q, ∀ g (t : ℤ), (t : ZMod q) = ψ g → χ g = expQ q t := by
  haveI : NeZero q := ⟨hq.ne'⟩
  have hζ := Complex.isPrimitiveRoot_exp q hq.ne'
  have hex : ∀ g, ∃ i : ℕ, expQ q i = χ g := by
    intro g
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (h g)
    refine ⟨i, ?_⟩
    rw [← hi, expQ, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  choose i hi using hex
  refine ⟨AddMonoidHom.mk' (fun g => ((i g : ℤ) : ZMod q)) ?_, ?_⟩
  · intro g g'
    have : expQ q (i (g + g')) = expQ q ((i g : ℤ) + i g') := by
      rw [expQ_add, hi, hi, hi, AddChar.map_add_eq_mul]
    rw [expQ_eq_iff hq] at this
    simpa using this
  · intro g t ht
    rw [← hi g, expQ_eq_iff hq]
    simpa using ht.symm

lemma addChar_pow_card [Fintype G] (χ : AddChar G ℂ) (g : G) : χ g ^ Fintype.card G = 1 := by
  rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one]

/-- A nontrivial character is the standard parametrization of a surjection onto `ℤ/q`, `q ≥ 2`. -/
lemma addChar_param_surj [Fintype G] (χ : AddChar G ℂ) (hχ : ∃ g, χ g ≠ 1) :
    ∃ (q : ℕ) (ψ : G →+ ZMod q), 2 ≤ q ∧ Function.Surjective ψ ∧
      ∀ g (t : ℤ), (t : ZMod q) = ψ g → χ g = expQ q t := by
  classical
  have hP : ∃ q : ℕ, 0 < q ∧ ∀ g, χ g ^ q = 1 :=
    ⟨Fintype.card G, Fintype.card_pos, addChar_pow_card χ⟩
  set q := Nat.find hP with hqdef
  obtain ⟨hq, hpow⟩ := Nat.find_spec hP
  obtain ⟨ψ, hψ⟩ := addChar_param_of_pow q hq χ hpow
  haveI : NeZero q := ⟨hq.ne'⟩
  have hq2 : 2 ≤ q := by
    by_contra h2
    have : q = 1 := by omega
    obtain ⟨g, hg⟩ := hχ
    have h1 := hpow g
    rw [show Nat.find hP = 1 from this, pow_one] at h1
    exact hg h1
  refine ⟨q, ψ, hq2, ?_, hψ⟩
  -- surjectivity: otherwise the order of the range is a smaller exponent
  by_contra hns
  have hne : ψ.range ≠ ⊤ := by
    intro htop
    exact hns (AddMonoidHom.range_eq_top.1 htop)
  set r := Nat.card ψ.range
  have hrlt : r < q := by
    have hle : r ≤ Nat.card (ZMod q) := Nat.card_le_card_of_injective _ Subtype.coe_injective
    rw [Nat.card_zmod] at hle
    rcases eq_or_lt_of_le hle with h | h
    · exact absurd ((AddSubgroup.card_eq_iff_eq_top _).1 (by rw [Nat.card_zmod]; exact h)) hne
    · exact h
  have hr : 0 < r := Nat.card_pos
  have hrpow : ∀ g, χ g ^ r = 1 := by
    intro g
    have h1 : r • ψ g = 0 := by
      have := card_nsmul_eq_zero' (G := ψ.range) (x := ⟨ψ g, AddMonoidHom.mem_range.2 ⟨g, rfl⟩⟩)
      exact congrArg Subtype.val this
    rw [← AddChar.map_nsmul_eq_pow, hψ (r • g) 0 (by rw [map_nsmul, h1]; simp), expQ_zero]
  exact Nat.find_min hP hrlt ⟨hr, hrpow⟩

/-! ### Trigonometric estimates -/

/-- Chord estimate. -/
lemma four_mul_abs_div_le_norm_expQ_sub_one {q : ℕ} (hq : 0 < q) {t : ℤ}
    (ht : 2 * |t| ≤ q) : 4 * |(t : ℝ)| / q ≤ ‖expQ q t - 1‖ := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hexp : expQ q t = exp (I * ((2 * Real.pi * t / q : ℝ) : ℂ)) := by
    rw [expQ]
    congr 1
    push_cast
    ring
  rw [hexp, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_two]
  set x := 2 * Real.pi * t / q / 2 with hx
  have hx' : x = Real.pi * t / q := by rw [hx]; ring
  have htr : 2 * |(t : ℝ)| ≤ q := by exact_mod_cast ht
  have habs : |x| = Real.pi * |(t : ℝ)| / q := by
    rw [hx', abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hq']
  have hle : |x| ≤ Real.pi / 2 := by
    rw [habs, div_le_div_iff₀ hq' two_pos]
    nlinarith [Real.pi_pos]
  have hsin : 2 / Real.pi * |x| ≤ |Real.sin x| := by
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h] at hle ⊢
      exact (Real.mul_le_sin h hle).trans (le_abs_self _)
    · rw [abs_of_nonpos h] at hle ⊢
      have := Real.mul_le_sin (x := -x) (by linarith) hle
      rw [Real.sin_neg] at this
      exact this.trans (neg_le_abs _)
  rw [habs] at hsin
  have : 2 / Real.pi * (Real.pi * |(t : ℝ)| / q) = 2 * |(t : ℝ)| / q := by
    field_simp
  rw [this] at hsin
  calc 4 * |(t : ℝ)| / q = 2 * (2 * |(t : ℝ)| / q) := by ring
    _ ≤ 2 * |Real.sin x| := by linarith

/-- The real part of `expQ N t` is at least `1/2` when `8|t| ≤ N`. -/
lemma half_le_re_expQ {N : ℕ} (hN : 0 < N) {t : ℤ} (ht : 8 * |t| ≤ N) :
    1 / 2 ≤ (expQ N t).re := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hre : (expQ N t).re = Real.cos (2 * Real.pi * t / N) := by
    rw [expQ]
    have : (2 * Real.pi * I * t / N : ℂ) = ((2 * Real.pi * t / N : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [this, Complex.exp_ofReal_mul_I_re]
  rw [hre]
  have htr : 8 * |(t : ℝ)| ≤ N := by exact_mod_cast ht
  have hsq : (2 * Real.pi * t / N) ^ 2 ≤ Real.pi ^ 2 / 16 := by
    rw [div_pow, div_le_div_iff₀ (by positivity) (by norm_num)]
    have h1 : (t : ℝ) ^ 2 = |(t : ℝ)| ^ 2 := (sq_abs _).symm
    have h2 : 0 ≤ |(t : ℝ)| := abs_nonneg _
    have h3 : 64 * |(t : ℝ)| ^ 2 ≤ (N : ℝ) ^ 2 := by nlinarith
    nlinarith [Real.pi_pos]
  have hcos := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * t / N)
  have hpi := Real.pi_lt_d2
  have hpi2 : Real.pi ^ 2 < 10 := by nlinarith [Real.pi_pos]
  linarith

end GreenRuzsa
