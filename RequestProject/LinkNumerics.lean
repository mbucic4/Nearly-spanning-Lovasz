module
public import RequestProject.LinkMain

/-!
# Numerics for Lemma 5.1

We fix the parameters of the proof of Lemma 5.1:

* `K = L^c` where `L = log n`;
* `ℓ = ⌈2000 K L⌉` rounds of growth, each with probability `p = q / (20 (ℓ + 2))`;
* `E = L^(4c+10) / q^5`, `D = L^(5c+11) / q^5`;
* `x = exp(-(3L + 3))` for the union bound;

and check all numerical side conditions of `linking_whp` for `L ≥ 10^4 (c + 1)`.
-/

@[expose] public section


open scoped BigOperators
open Classical

namespace Lovasz

noncomputable section

/-- The number of growth rounds. -/
def ellN (c : ℕ) (L : ℝ) : ℕ := ⌈2000 * L ^ c * L⌉₊

/-- The probability of a growth round. -/
def pN (c : ℕ) (L q : ℝ) : ℝ := q / (20 * ((ellN c L : ℝ) + 2))

section num

variable {c : ℕ} {L q : ℝ}

lemma powc_split (L : ℝ) (a b : ℕ) : L ^ (a * c + b) = (L ^ c) ^ a * L ^ b := by
  rw [pow_add, mul_comm a c, pow_mul]

lemma num_L1 (hL : 10 ^ 4 * ((c : ℝ) + 1) ≤ L) : 10 ^ 4 ≤ L := by
  have : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  nlinarith

lemma num_K1 (hL : 10 ^ 4 * ((c : ℝ) + 1) ≤ L) : 1 ≤ L ^ c :=
  one_le_pow₀ (by linarith [num_L1 hL])

lemma ellN_ge (L : ℝ) : 2000 * L ^ c * L ≤ (ellN c L : ℝ) := Nat.le_ceil _

lemma ellN_le (hL : 10 ^ 4 * ((c : ℝ) + 1) ≤ L) : (ellN c L : ℝ) + 2 ≤ 2001 * L ^ c * L := by
  have h1 := num_L1 hL
  have h2 := num_K1 hL
  have h3 : (ellN c L : ℝ) < 2000 * L ^ c * L + 1 := Nat.ceil_lt_add_one (by positivity)
  nlinarith

lemma ellN_one (hL : 10 ^ 4 * ((c : ℝ) + 1) ≤ L) : 1 ≤ ellN c L := by
  have h1 := num_L1 hL
  have h2 := num_K1 hL
  have := ellN_ge (c := c) L
  have : (1 : ℝ) ≤ ellN c L := by nlinarith
  exact_mod_cast this

lemma pN_pos (hq0 : 0 < q) : 0 < pN c L q := by
  unfold pN; positivity

lemma pN_le_one (hq1 : q ≤ 1) : pN c L q ≤ 1 := by
  unfold pN
  rw [div_le_one (by positivity)]
  have : (0 : ℝ) ≤ ellN c L := Nat.cast_nonneg _
  linarith

lemma pN_mul (hq0 : 0 < q) : ((ellN c L : ℝ) + 2) * pN c L q = q / 20 := by
  unfold pN; field_simp

lemma one_div_pN (hq0 : 0 < q) : 1 / pN c L q = 20 * ((ellN c L : ℝ) + 2) / q := by
  unfold pN; field_simp

lemma rN_ge (hq0 : 0 < q) : 20 * ((ellN c L : ℝ) + 2) / q ≤ (⌈1 / pN c L q⌉₊ : ℝ) := by
  rw [← one_div_pN hq0]; exact Nat.le_ceil _

lemma rN_le (hL : 10 ^ 4 * ((c : ℝ) + 1) ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    (⌈1 / pN c L q⌉₊ : ℝ) ≤ 42100 * L ^ c * L / q := by
  have h1 := num_L1 hL
  have h2 := num_K1 hL
  have h3 : (⌈1 / pN c L q⌉₊ : ℝ) < 20 * ((ellN c L : ℝ) + 2) / q + 1 :=
    calc (⌈1 / pN c L q⌉₊ : ℝ) < 1 / pN c L q + 1 :=
          Nat.ceil_lt_add_one (by have := pN_pos hq0 (c := c) (L := L); positivity)
      _ = _ := by rw [one_div_pN hq0]
  have h4 := ellN_le hL
  rw [le_div_iff₀ hq0]
  have h5 : (⌈1 / pN c L q⌉₊ : ℝ) * q < (20 * ((ellN c L : ℝ) + 2) / q + 1) * q :=
    mul_lt_mul_of_pos_right h3 hq0
  have h6 : (20 * ((ellN c L : ℝ) + 2) / q + 1) * q = 20 * ((ellN c L : ℝ) + 2) + q := by
    field_simp
  nlinarith

lemma rN_pos (hq0 : 0 < q) : 0 < (⌈1 / pN c L q⌉₊ : ℝ) := by
  have := rN_ge (c := c) (L := L) hq0
  have : 0 < 20 * ((ellN c L : ℝ) + 2) / q := by positivity
  linarith

lemma num_hs (hL : 10 ^ 4 * ((c : ℝ) + 1) ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    4 * (⌈1 / pN c L q⌉₊ : ℝ) ^ 3 ≤ 2 * L ^ (9 * c + 21) / q ^ 10 := by
  have h1 := num_L1 hL
  have hK := num_K1 hL
  set K := L ^ c
  have hr := rN_le hL hq0 hq1
  have hr0 : (0 : ℝ) ≤ (⌈1 / pN c L q⌉₊ : ℝ) := Nat.cast_nonneg _
  set A := 42100 * K * L
  have hr3 : (⌈1 / pN c L q⌉₊ : ℝ) ^ 3 ≤ A ^ 3 / q ^ 3 := by
    rw [← div_pow]; exact pow_le_pow_left₀ hr0 hr 3
  rw [powc_split L 9 21]
  have hq3 : q ^ 10 ≤ q ^ 3 := pow_le_pow_of_le_one hq0.le hq1 (by norm_num)
  have hL18 : (2 * 42100 ^ 3 : ℝ) ≤ L ^ 18 := by
    calc (2 * 42100 ^ 3 : ℝ) ≤ (10 ^ 4) ^ 18 := by norm_num
      _ ≤ L ^ 18 := pow_le_pow_left₀ (by norm_num) h1 18
  have hK6 : 1 ≤ K ^ 6 := one_le_pow₀ hK
  have hA : 4 * A ^ 3 ≤ 2 * (K ^ 9 * L ^ 21) := by
    have e1 : 4 * A ^ 3 = (K ^ 3 * L ^ 3) * (4 * 42100 ^ 3) := by simp only [A]; ring
    have e2 : 2 * (K ^ 9 * L ^ 21) = (K ^ 3 * L ^ 3) * (2 * (K ^ 6 * L ^ 18)) := by ring
    rw [e1, e2]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    nlinarith
  calc 4 * (⌈1 / pN c L q⌉₊ : ℝ) ^ 3 ≤ 4 * (A ^ 3 / q ^ 3) := by linarith
    _ = 4 * A ^ 3 / q ^ 3 := by ring
    _ ≤ 2 * (K ^ 9 * L ^ 21) / q ^ 3 := by gcongr
    _ ≤ 2 * (K ^ 9 * L ^ 21) / q ^ 10 := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity) hq3

lemma num_exp45 : (5 * 2001 * 42100 ^ 3 : ℝ) ≤ Real.exp 45 := by
  have h := Real.exp_one_gt_d9
  have : Real.exp 45 = Real.exp 1 ^ 45 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  calc (5 * 2001 * 42100 ^ 3 : ℝ) ≤ 2.7182818283 ^ 45 := by norm_num
    _ ≤ Real.exp 1 ^ 45 := pow_le_pow_left₀ (by norm_num) h.le 45

lemma num_logfactor (hL : 10 ^ 4 * ((c : ℝ) + 1) ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    5 * (ellN c L : ℝ) * (⌈1 / pN c L q⌉₊ : ℝ) ^ 3 ≤
      Real.exp (45 + (4 * c + 4) * L + 3 / q) := by
  have h1 := num_L1 hL
  have hK := num_K1 hL
  have hr := rN_le hL hq0 hq1
  have hr0 : (0 : ℝ) ≤ (⌈1 / pN c L q⌉₊ : ℝ) := Nat.cast_nonneg _
  have hl := ellN_le hL
  set K := L ^ c
  have hr3 : (⌈1 / pN c L q⌉₊ : ℝ) ^ 3 ≤ (42100 * K * L) ^ 3 / q ^ 3 := by
    rw [← div_pow]; exact pow_le_pow_left₀ hr0 hr 3
  have hl' : (ellN c L : ℝ) ≤ 2001 * K * L := by linarith
  have step1 : 5 * (ellN c L : ℝ) * (⌈1 / pN c L q⌉₊ : ℝ) ^ 3 ≤
      (5 * 2001 * 42100 ^ 3) * (L ^ (4 * c + 4)) * (1 / q) ^ 3 := by
    have e : (5 * 2001 * 42100 ^ 3) * (L ^ (4 * c + 4)) * (1 / q) ^ 3 =
        5 * (2001 * K * L) * ((42100 * K * L) ^ 3 / q ^ 3) := by
      rw [powc_split L 4 4]; simp only [K]; field_simp
    rw [e]
    have : (0 : ℝ) ≤ ellN c L := Nat.cast_nonneg _
    gcongr
  have hLe : L ≤ Real.exp L := by have := Real.add_one_le_exp L; linarith
  have hqe : 1 / q ≤ Real.exp (1 / q) := by have := Real.add_one_le_exp (1 / q); linarith
  have step2 : L ^ (4 * c + 4) ≤ Real.exp ((4 * c + 4) * L) := by
    calc L ^ (4 * c + 4) ≤ Real.exp L ^ (4 * c + 4) := pow_le_pow_left₀ (by linarith) hLe _
      _ = Real.exp ((4 * c + 4) * L) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have step3 : (1 / q) ^ 3 ≤ Real.exp (3 / q) := by
    calc (1 / q) ^ 3 ≤ Real.exp (1 / q) ^ 3 := pow_le_pow_left₀ (by positivity) hqe _
      _ = Real.exp (3 / q) := by rw [← Real.exp_nat_mul]; ring_nf
  refine step1.trans ?_
  rw [Real.exp_add, Real.exp_add]
  gcongr
  exact num_exp45

lemma num_a (hL : 10 ^ 4 * ((c : ℝ) + 1) ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    L ^ 7 / (1.5e19 * q) ≤ q * (L ^ (4 * c + 10) / q ^ 5) /
      (200000 * (⌈1 / pN c L q⌉₊ : ℝ) ^ 3 * L ^ c) := by
  have h1 := num_L1 hL
  have hK := num_K1 hL
  have hr := rN_le hL hq0 hq1
  have hr0 : 0 < (⌈1 / pN c L q⌉₊ : ℝ) := rN_pos hq0
  set K := L ^ c
  set r := (⌈1 / pN c L q⌉₊ : ℝ)
  have hr3 : r ^ 3 ≤ (42100 * K * L) ^ 3 / q ^ 3 := by
    rw [← div_pow]; exact pow_le_pow_left₀ hr0.le hr 3
  rw [powc_split L 4 10, div_le_div_iff₀ (by positivity) (by positivity)]
  have e : q * (K ^ 4 * L ^ 10 / q ^ 5) * (1.5e19 * q) = (1.5e19 * K ^ 4 * L ^ 10) / q ^ 3 := by
    field_simp
  rw [e]
  have h2 : L ^ 7 * (200000 * r ^ 3 * K) ≤ L ^ 7 * (200000 * ((42100 * K * L) ^ 3 / q ^ 3) * K) := by
    gcongr
  have e2 : L ^ 7 * (200000 * ((42100 * K * L) ^ 3 / q ^ 3) * K) =
      (200000 * 42100 ^ 3) * K ^ 4 * L ^ 10 / q ^ 3 := by field_simp
  rw [e2] at h2
  refine h2.trans ?_
  gcongr
  norm_num

lemma num_hκ (hL : 10 ^ 4 * ((c : ℝ) + 1) ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1) (u : ℕ) (hu : 1 ≤ u) :
    5 * (ellN c L : ℝ) * (⌈1 / pN c L q⌉₊ : ℝ) ^ 3 * Real.exp (-(q * (L ^ (4 * c + 10) / q ^ 5 * u) /
      (200000 * (⌈1 / pN c L q⌉₊ : ℝ) ^ 3 * L ^ c))) ≤ Real.exp (-(3 * L + 3)) ^ u := by
  have h1 := num_L1 hL
  set a := q * (L ^ (4 * c + 10) / q ^ 5) / (200000 * (⌈1 / pN c L q⌉₊ : ℝ) ^ 3 * L ^ c)
  have ha := num_a hL hq0 hq1 (c := c)
  have hB := num_logfactor hL hq0 hq1 (c := c)
  set B := 45 + (4 * c + 4) * L + 3 / q
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  -- `a` is large
  have hbig : B + 3 * L + 3 ≤ a := by
    refine le_trans ?_ ha
    have hL7 : L ^ 7 = L ^ 6 * L := by ring
    have hL6 : (10 ^ 4 : ℝ) ^ 6 * ((c : ℝ) + 1) ≤ L ^ 6 := by
      have h6 : (10 ^ 4 * ((c : ℝ) + 1)) ^ 6 ≤ L ^ 6 := pow_le_pow_left₀ (by positivity) hL 6
      have h7 : (c : ℝ) + 1 ≤ ((c : ℝ) + 1) ^ 6 := by
        have : (1 : ℝ) ≤ c + 1 := by linarith
        calc (c : ℝ) + 1 = ((c : ℝ) + 1) ^ 1 := (pow_one _).symm
          _ ≤ ((c : ℝ) + 1) ^ 6 := pow_le_pow_right₀ this (by norm_num)
      calc (10 ^ 4 : ℝ) ^ 6 * ((c : ℝ) + 1) ≤ (10 ^ 4) ^ 6 * ((c : ℝ) + 1) ^ 6 := by gcongr
        _ = (10 ^ 4 * ((c : ℝ) + 1)) ^ 6 := by ring
        _ ≤ L ^ 6 := h6
    rw [le_div_iff₀ (by positivity)]
    simp only [B]
    have hqi : 3 / q * (1.5e19 * q) = 4.5e19 := by field_simp; norm_num
    have : (45 + (4 * c + 4) * L + 3 / q + 3 * L + 3) * (1.5e19 * q) =
        (48 + (4 * c + 7) * L) * (1.5e19 * q) + 4.5e19 := by rw [← hqi]; ring
    rw [this]
    have h2 : (48 + (4 * c + 7) * L) * (1.5e19 * q) ≤ (48 + (4 * c + 7) * L) * 1.5e19 := by
      have : 0 ≤ 48 + (4 * c + 7) * L := by positivity
      nlinarith
    have h3 : (48 + (4 * c + 7) * L) * 1.5e19 + 4.5e19 ≤ L ^ 6 * L := by
      have : (48 + (4 * (c : ℝ) + 7) * L) * 1.5e19 + 4.5e19 ≤ (1e24 * ((c : ℝ) + 1)) * L := by
        nlinarith
      have : (1e24 * ((c : ℝ) + 1)) * L ≤ L ^ 6 * L := by
        have : 1e24 * ((c : ℝ) + 1) ≤ L ^ 6 := by norm_num at hL6 ⊢; linarith
        nlinarith
      linarith
    nlinarith
  have hB0 : 0 ≤ B := by positivity
  have hu' : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have e1 : q * (L ^ (4 * c + 10) / q ^ 5 * u) / (200000 * (⌈1 / pN c L q⌉₊ : ℝ) ^ 3 * L ^ c) =
      a * u := by simp only [a]; ring
  rw [e1, ← Real.exp_nat_mul]
  calc 5 * (ellN c L : ℝ) * (⌈1 / pN c L q⌉₊ : ℝ) ^ 3 * Real.exp (-(a * u))
      ≤ Real.exp B * Real.exp (-(a * u)) := by gcongr
    _ = Real.exp (B - a * u) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (u * -(3 * L + 3)) := by
        refine Real.exp_le_exp.2 ?_
        have : (B + 3 * L + 3) * u ≤ a * u := mul_le_mul_of_nonneg_right hbig (by positivity)
        nlinarith

lemma num_grow {n : ℕ} (hn : 1 ≤ n) (hL : 10 ^ 4 * ((c : ℝ) + 1) ≤ Real.log n) :
    (n : ℝ) ≤ (1 + 1 / (1000 * Real.log n ^ c)) ^ ellN c (Real.log n) := by
  set L := Real.log n
  have h1 := num_L1 hL
  have hK := num_K1 hL
  set K := L ^ c
  set y := 1 / (1000 * K)
  have hy0 : 0 < y := by positivity
  have hy1 : y ≤ 1 := by
    simp only [y]; rw [div_le_one (by positivity)]; linarith
  have hlog : 1 / (2000 * K) ≤ Real.log (1 + y) := by
    have := Real.one_sub_inv_le_log_of_pos (x := 1 + y) (by linarith)
    have e : 1 - (1 + y)⁻¹ = y / (1 + y) := by field_simp; ring
    rw [e] at this
    refine le_trans ?_ this
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    simp only [y]
    field_simp
    nlinarith
  have hl := ellN_ge (c := c) L
  have hmain : L ≤ (ellN c L : ℝ) * Real.log (1 + y) := by
    calc L = 2000 * K * L * (1 / (2000 * K)) := by field_simp
      _ ≤ (ellN c L : ℝ) * Real.log (1 + y) := by
          apply mul_le_mul hl hlog (by positivity) (by positivity)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  calc (n : ℝ) = Real.exp L := (Real.exp_log hn0).symm
    _ ≤ Real.exp ((ellN c L : ℝ) * Real.log (1 + y)) := Real.exp_le_exp.2 hmain
    _ = (1 + y) ^ ellN c L := by
        rw [← Real.log_pow, Real.exp_log (by positivity)]

lemma num_k {n : ℕ} (hn : 1 ≤ n) (hL : 10 ^ 4 * ((c : ℝ) + 1) ≤ Real.log n) :
    ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤ 1.5 * Real.log n := by
  have h1 := num_L1 hL
  have h2 : ((2 : ℕ) : ℝ) ^ Nat.log 2 n ≤ (n : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : n ≠ 0)
  have h3 : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
    have := Real.log_le_log (by positivity) h2
    rw [Real.log_pow] at this
    simpa using this
  have h4 := Real.log_two_gt_d9
  push_cast
  have h5 : (Nat.log 2 n : ℝ) * 0.69 ≤ Real.log n := by
    have : (Nat.log 2 n : ℝ) * 0.69 ≤ (Nat.log 2 n : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    linarith
  nlinarith

lemma num_Λ (hL : 10 ^ 4 * ((c : ℝ) + 1) ≤ L) {k : ℕ} (hk : (k : ℝ) ≤ 1.5 * L) :
    ((2 * (1 + (1 + ellN c L) + k * (1 + ellN c L)) + 1 : ℕ) : ℝ) ≤ 7000 * L ^ c * L ^ 2 := by
  have h1 := num_L1 hL
  have hK := num_K1 hL
  have hl := ellN_le hL (c := c)
  push_cast
  have hl0 : (0 : ℝ) ≤ ellN c L := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have e : 2 * (1 + (1 + (ellN c L : ℝ)) + k * (1 + ellN c L)) + 1 =
      3 + 2 * (1 + ellN c L) * (1 + k) := by ring
  rw [e]
  have h2 : 2 * (1 + (ellN c L : ℝ)) * (1 + k) ≤ 2 * (2001 * L ^ c * L) * (1.6 * L) := by
    apply mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
  have h3 : (3 : ℝ) ≤ 100 * L ^ c * L ^ 2 := by
    have : (1 : ℝ) ≤ L ^ 2 := one_le_pow₀ (by linarith)
    nlinarith
  nlinarith

lemma num_Λ1 (hL : 10 ^ 4 * ((c : ℝ) + 1) ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1) {Λ : ℝ}
    (hΛ : Λ ≤ 7000 * L ^ c * L ^ 2) (hΛ0 : 0 ≤ Λ) :
    8 * (L ^ (5 * c + 11) / q ^ 5 + 1) * Λ + 4 ≤ q * (100 * L ^ (7 * c + 19) / q ^ 6) := by
  have h1 := num_L1 hL
  have hK := num_K1 hL
  rw [powc_split L 5 11, powc_split L 7 19]
  set K := L ^ c
  have hq5 : q ^ 5 ≤ 1 := pow_le_one₀ hq0.le hq1
  have hD1 : 1 ≤ K ^ 5 * L ^ 11 / q ^ 5 := by
    rw [le_div_iff₀ (by positivity), one_mul]
    have : 1 ≤ K ^ 5 * L ^ 11 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hK)
      (one_le_pow₀ (by linarith))
    linarith
  have e : q * (100 * (K ^ 7 * L ^ 19) / q ^ 6) = 100 * (K ^ 7 * L ^ 19) / q ^ 5 := by
    field_simp
  rw [e]
  have h2 : 8 * (K ^ 5 * L ^ 11 / q ^ 5 + 1) * Λ + 4 ≤
      20 * (K ^ 5 * L ^ 11 / q ^ 5) * (7000 * K * L ^ 2) := by
    have hΛ1 : 4 ≤ 4 * Λ ∨ Λ < 1 := by
      rcases le_or_gt 1 Λ with h | h
      · left; linarith
      · right; exact h
    have hKL : (1 : ℝ) ≤ 7000 * K * L ^ 2 := by
      have : (1 : ℝ) ≤ L ^ 2 := one_le_pow₀ (by linarith)
      nlinarith
    have hD0 : 0 ≤ K ^ 5 * L ^ 11 / q ^ 5 := by positivity
    nlinarith
  have e3 : 20 * (K ^ 5 * L ^ 11 / q ^ 5) * (7000 * K * L ^ 2) =
      140000 * (K ^ 6 * L ^ 13) / q ^ 5 := by field_simp; norm_num
  rw [e3] at h2
  refine h2.trans (div_le_div_of_nonneg_right ?_ (by positivity))
  · have hL6 : (1400 : ℝ) ≤ K * L ^ 6 := by
      have : (1400 : ℝ) ≤ L ^ 6 := by
        calc (1400 : ℝ) ≤ (10 ^ 4) ^ 6 := by norm_num
          _ ≤ L ^ 6 := pow_le_pow_left₀ (by norm_num) h1 6
      nlinarith
    have e2 : 100 * (K ^ 7 * L ^ 19) = (K ^ 6 * L ^ 13) * (100 * (K * L ^ 6)) := by ring
    rw [e2]
    have : 0 ≤ K ^ 6 * L ^ 13 := by positivity
    nlinarith

lemma num_Λ2 (hL : 10 ^ 4 * ((c : ℝ) + 1) ≤ L) (hq0 : 0 < q) {Λ n : ℝ}
    (hΛ : Λ ≤ 7000 * L ^ c * L ^ 2) (hΛ0 : 0 ≤ Λ) (hn : 0 ≤ n) :
    2 * (L ^ (5 * c + 11) / q ^ 5) * Λ * n ≤ 0.55 * q * n * (100 * L ^ (7 * c + 19) / q ^ 6) := by
  have h1 := num_L1 hL
  have hK := num_K1 hL
  rw [powc_split L 5 11, powc_split L 7 19]
  set K := L ^ c
  have e : 0.55 * q * n * (100 * (K ^ 7 * L ^ 19) / q ^ 6) = n * (55 * (K ^ 7 * L ^ 19) / q ^ 5) := by
    field_simp; ring
  rw [e]
  have e2 : 2 * (K ^ 5 * L ^ 11 / q ^ 5) * Λ * n = n * (2 * (K ^ 5 * L ^ 11) * Λ / q ^ 5) := by
    ring
  rw [e2]
  refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ?_ (by positivity)) hn
  have hL6 : (14000 : ℝ) ≤ 55 * (K * L ^ 6) := by
    have : (14000 : ℝ) ≤ L ^ 6 := by
      calc (14000 : ℝ) ≤ (10 ^ 4) ^ 6 := by norm_num
        _ ≤ L ^ 6 := pow_le_pow_left₀ (by norm_num) h1 6
    nlinarith
  have h3 : 2 * (K ^ 5 * L ^ 11) * Λ ≤ 2 * (K ^ 5 * L ^ 11) * (7000 * K * L ^ 2) :=
    mul_le_mul_of_nonneg_left hΛ (by positivity)
  have e3 : 2 * (K ^ 5 * L ^ 11) * (7000 * K * L ^ 2) = (K ^ 6 * L ^ 13) * 14000 := by ring
  have e4 : 55 * (K ^ 7 * L ^ 19) = (K ^ 6 * L ^ 13) * (55 * (K * L ^ 6)) := by ring
  rw [e4]
  have : 0 ≤ K ^ 6 * L ^ 13 := by positivity
  nlinarith

lemma exp_neg_three_le : Real.exp (-3) ≤ 0.05 := by
  have h := Real.exp_one_gt_d9
  have e : Real.exp (-3) = (Real.exp 1 ^ 3)⁻¹ := by
    rw [← Real.exp_nat_mul, ← Real.exp_neg]; norm_num
  rw [e, inv_le_comm₀ (by positivity) (by norm_num)]
  calc (0.05 : ℝ)⁻¹ ≤ 2.7182818283 ^ 3 := by norm_num
    _ ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) h.le 3

lemma num_tail {n : ℕ} (hn : 1 ≤ n) (hL : 10 ^ 4 * ((c : ℝ) + 1) ≤ Real.log n) (hq0 : 0 < q)
    (hq1 : q ≤ 1) (hqn : 2 * Real.log n ^ (9 * c + 21) < q ^ 10 * n) :
    2 ≤ 0.55 * q * n ∧
    (n : ℝ) * Real.exp (-(0.13 * q * (100 * Real.log n ^ (7 * c + 19) / q ^ 6))) ≤ 1 ∧
    (n : ℝ) ^ 2 * Real.exp (-(3 * Real.log n + 3)) ≤ 1 ∧
    6 * (n : ℝ) ^ 2 * Real.exp (-(3 * Real.log n + 3)) +
      2 * n * Real.exp (-(0.13 * q * (100 * Real.log n ^ (7 * c + 19) / q ^ 6))) +
      Real.exp (-(0.0025 * q * n)) ≤ 1 / n := by
  set L := Real.log n
  have h1 := num_L1 hL
  have hK := num_K1 hL
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnL : (n : ℝ) = Real.exp L := (Real.exp_log hn0).symm
  have hL1 : (1 : ℝ) ≤ L := by linarith
  -- `q n` is large
  have hq10 : q ^ 10 ≤ q := by
    calc q ^ 10 ≤ q ^ 1 := pow_le_pow_of_le_one hq0.le hq1 (by norm_num)
      _ = q := pow_one q
  have hL21 : L ^ 21 ≤ L ^ (9 * c + 21) := pow_le_pow_right₀ hL1 (by omega)
  have hqn' : 2 * L ^ 21 ≤ q * n := by
    have : q ^ 10 * n ≤ q * n := mul_le_mul_of_nonneg_right hq10 hn0.le
    linarith
  have hL20 : (10 ^ 4 : ℝ) ^ 20 ≤ L ^ 20 := pow_le_pow_left₀ (by norm_num) h1 20
  have hL21' : L ^ 21 = L ^ 20 * L := by ring
  have hbig : 10000 * L + 10000 ≤ L ^ 21 := by
    rw [hL21']; nlinarith
  -- `q Kx` is large
  have hqK : 100 * L ≤ q * (100 * L ^ (7 * c + 19) / q ^ 6) := by
    have e : q * (100 * L ^ (7 * c + 19) / q ^ 6) = 100 * L ^ (7 * c + 19) / q ^ 5 := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    have hq5 : q ^ 5 ≤ 1 := pow_le_one₀ hq0.le hq1
    have : L ≤ L ^ (7 * c + 19) := by
      calc L = L ^ 1 := (pow_one L).symm
        _ ≤ L ^ (7 * c + 19) := pow_le_pow_right₀ hL1 (by omega)
    have : 0 ≤ L := by linarith
    nlinarith
  have e3 := exp_neg_three_le
  have hA : Real.exp (-(0.13 * q * (100 * L ^ (7 * c + 19) / q ^ 6))) ≤
      Real.exp (-3) * Real.exp (-L) * Real.exp (-L) := by
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith)
  have hB : Real.exp (-(0.0025 * q * n)) ≤ Real.exp (-3) * Real.exp (-L) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith)
  have hnx : (n : ℝ) ^ 2 * Real.exp (-(3 * L + 3)) = Real.exp (-3) * Real.exp (-L) := by
    rw [hnL, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; push_cast; ring
  have hLn : (n : ℝ) * Real.exp (-L) = 1 := by
    rw [hnL, ← Real.exp_add]; simp
  have he0 := Real.exp_pos (-L)
  have he3 := Real.exp_pos (-3)
  refine ⟨by nlinarith, ?_, ?_, ?_⟩
  · calc (n : ℝ) * Real.exp (-(0.13 * q * (100 * L ^ (7 * c + 19) / q ^ 6)))
        ≤ n * (Real.exp (-3) * Real.exp (-L) * Real.exp (-L)) :=
          mul_le_mul_of_nonneg_left hA hn0.le
      _ = Real.exp (-3) * Real.exp (-L) := by
          have : (n : ℝ) * (Real.exp (-3) * Real.exp (-L) * Real.exp (-L)) =
              Real.exp (-3) * Real.exp (-L) * (n * Real.exp (-L)) := by ring
          rw [this, hLn, mul_one]
      _ ≤ 1 := by
          have : Real.exp (-L) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
          nlinarith
  · rw [hnx]
    have : Real.exp (-L) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    nlinarith
  · have hdiv : 1 / (n : ℝ) = Real.exp (-L) := by
      rw [eq_comm, eq_div_iff hn0.ne', mul_comm, hLn]
    rw [hdiv]
    have h2 : 2 * n * Real.exp (-(0.13 * q * (100 * L ^ (7 * c + 19) / q ^ 6))) ≤
        2 * Real.exp (-3) * Real.exp (-L) := by
      have := mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℝ) ≤ 2 * n)
      have e : 2 * (n : ℝ) * (Real.exp (-3) * Real.exp (-L) * Real.exp (-L)) =
          2 * Real.exp (-3) * Real.exp (-L) * (n * Real.exp (-L)) := by ring
      rw [e, hLn, mul_one] at this
      exact this
    have h6 : 6 * (n : ℝ) ^ 2 * Real.exp (-(3 * L + 3)) = 6 * (Real.exp (-3) * Real.exp (-L)) := by
      rw [mul_assoc, hnx]
    rw [h6]
    nlinarith

lemma num_hrL (hL : 10 ^ 4 * ((c : ℝ) + 1) ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    13 * L ^ c ≤ (⌈1 / pN c L q⌉₊ : ℝ) := by
  have h1 := num_L1 hL
  have hK := num_K1 hL
  refine le_trans ?_ (rN_ge hq0)
  rw [le_div_iff₀ hq0]
  have hl := ellN_ge (c := c) L
  have : 13 * L ^ c ≤ 20 * ((ellN c L : ℝ) + 2) := by nlinarith
  have : 13 * L ^ c * q ≤ 13 * L ^ c := by nlinarith
  linarith

lemma num_hEq (hL : 10 ^ 4 * ((c : ℝ) + 1) ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    100000 * L ^ c + 50 ≤ q * (L ^ (4 * c + 10) / q ^ 5) := by
  have h1 := num_L1 hL
  have hK := num_K1 hL
  rw [powc_split L 4 10]
  set K := L ^ c
  have e : q * (K ^ 4 * L ^ 10 / q ^ 5) = K ^ 4 * L ^ 10 / q ^ 4 := by field_simp
  rw [e, le_div_iff₀ (by positivity)]
  have hq4 : q ^ 4 ≤ 1 := pow_le_one₀ hq0.le hq1
  have hL10 : (10 ^ 4 : ℝ) ^ 10 ≤ L ^ 10 := pow_le_pow_left₀ (by norm_num) h1 10
  have hK4 : K ≤ K ^ 4 := by
    calc K = K ^ 1 := (pow_one K).symm
      _ ≤ K ^ 4 := pow_le_pow_right₀ hK (by norm_num)
  have : 100000 * K + 50 ≤ K ^ 4 * L ^ 10 := by nlinarith
  have : (100000 * K + 50) * q ^ 4 ≤ 100000 * K + 50 := by
    have : 0 ≤ 100000 * K + 50 := by positivity
    nlinarith
  linarith

lemma num_hDs (hq0 : 0 < q) :
    2 * (L ^ (5 * c + 11) / q ^ 5) * (L ^ (4 * c + 10) / q ^ 5) = 2 * L ^ (9 * c + 21) / q ^ 10 := by
  have : L ^ (9 * c + 21) = L ^ (5 * c + 11) * L ^ (4 * c + 10) := by
    rw [← pow_add]; congr 1; ring
  rw [this]; field_simp

lemma num_hDE (hL : 10 ^ 4 * ((c : ℝ) + 1) ≤ L) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    100 * (L ^ (4 * c + 10) / q ^ 5 + 1) * L ^ c ≤ L ^ (5 * c + 11) / q ^ 5 := by
  have h1 := num_L1 hL
  have hK := num_K1 hL
  rw [powc_split L 4 10, powc_split L 5 11]
  set K := L ^ c
  have hq5 : q ^ 5 ≤ 1 := pow_le_one₀ hq0.le hq1
  have hE1 : 1 ≤ K ^ 4 * L ^ 10 / q ^ 5 := by
    rw [le_div_iff₀ (by positivity), one_mul]
    have : 1 ≤ K ^ 4 * L ^ 10 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hK)
      (one_le_pow₀ (by linarith))
    linarith
  have h2 : 100 * (K ^ 4 * L ^ 10 / q ^ 5 + 1) * K ≤ 200 * (K ^ 4 * L ^ 10 / q ^ 5) * K := by
    nlinarith
  refine h2.trans (le_of_eq_of_le (b := 200 * (K ^ 5 * L ^ 10) / q ^ 5) (by field_simp) ?_)
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have e : K ^ 5 * L ^ 11 = (K ^ 5 * L ^ 10) * L := by ring
  rw [e]
  have : 0 ≤ K ^ 5 * L ^ 10 := by positivity
  nlinarith

end num

section expander

variable {V : Type*} {G : SimpleGraph V}

/-- In an expander, the robustness parameter `s` is less than the number of vertices. -/
lemma IsExpander.s_lt_card {U : Finset V} {β : ℝ} {c : ℕ} {s : ℝ} (hexp : IsExpander G U β c s)
    (hβ : 0 < β) (hn : 2 ≤ U.card) : s < U.card := by
  by_contra hs
  push_neg at hs
  obtain ⟨u, hu⟩ : U.Nonempty := Finset.card_pos.1 (by omega)
  set F : Finset (Sym2 V) := (U.filter (G.Adj u)).image (fun v => s(u, v))
  have hF : (F.card : ℝ) ≤ s * ({u} : Finset V).card := by
    rw [Finset.card_singleton, Nat.cast_one, mul_one]
    have : F.card ≤ U.card := Finset.card_image_le.trans (Finset.card_filter_le _ _)
    exact le_trans (by exact_mod_cast this) hs
  have h := hexp {u} (Finset.singleton_subset_iff.2 hu) F (by simp) (by simp; omega) hF
  have hempty : extNb G U {u} F = ∅ := by
    ext v
    simp only [extNb, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton,
      Finset.notMem_empty, iff_false, not_and, not_exists]
    intro hvU x hx hadj hF'
    subst hx
    exact hF' (Finset.mem_image.2 ⟨v, Finset.mem_filter.2 ⟨hvU.1, hadj⟩, rfl⟩)
  rw [hempty, Finset.card_empty, Nat.cast_zero, Finset.card_singleton, Nat.cast_one,
    mul_one] at h
  have hL : 0 < Real.log U.card := Real.log_pos (by exact_mod_cast (by omega : 1 < U.card))
  have : 0 < β / Real.log U.card ^ c := by positivity
  linarith

end expander

end

end Lovasz
