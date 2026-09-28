module
public import RequestProject.Numerics12

/-!
# Theorem 1.2 (the cycle-and-matching theorem)

We derive Theorem 1.2 from the two results of the cited work on sublinear expanders that the
paper uses: the expander decomposition (Lemma 2.3, `ExpanderDecomposition`) and the linking
lemma (Lemma 2.4, `LinkingLemma`).

Given `ε`, cut both halves of the cycle into intervals of length `t = ⌊n^(ε/3)⌋`.  If many pairs
of intervals are joined by at least two edges of `M` we find a path directly (the dense case of
Claim 2.12); otherwise the interval graph is almost `t`-regular, and the expander decomposition
together with the probabilistic core of the proof yields the path.
-/

@[expose] public section


open Filter Real Classical

namespace Lovasz

set_option maxHeartbeats 1000000 in
/-- **Theorem 1.2** (the cycle-and-matching theorem), assuming Lemmas 2.3 and 2.4 of the paper
(which it quotes from the literature on sublinear expanders). -/
theorem cycle_matching_theorem (hD : ExpanderDecomposition) (hL : LinkingLemma 114) :
    CycleMatchingTheorem := by
  suffices key : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ f : Fin n → Fin n,
      Function.Bijective f → ∃ l : List (Fin (2 * n)), IsPathL (cycleMatchGraph n f) l ∧
        (n : ℝ) ^ (1 - ε) ≤ countPairs (fun i j => matchAdj n f i j ∨ matchAdj n f j i) l by
    intro ε hε
    by_cases h1 : ε ≤ 1
    · exact key ε hε h1
    · obtain ⟨n₀, hn₀⟩ := key 1 one_pos le_rfl
      refine ⟨max n₀ 1, fun n hn f hf => ?_⟩
      obtain ⟨l, hl, hc⟩ := hn₀ n (le_of_max_le_left hn) f hf
      refine ⟨l, hl, le_trans ?_ hc⟩
      have : (1 : ℝ) ≤ n := by exact_mod_cast (le_of_max_le_right hn)
      exact Real.rpow_le_rpow_of_exponent_le this (by linarith)
  intro ε hε hε1
  obtain ⟨N₀L, hLb⟩ := hL
  obtain ⟨N₀D, hDb⟩ := hD
  -- the parameters
  set a := ε / 3 with ha_def
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 / 3 := by rw [ha_def]; linarith
  set γ := a ^ 2 / 16 with hγ_def
  set K := ⌈8 / a⌉₊ + 1 with hK_def
  have hγ0 : 0 < γ := by positivity
  have hγle : γ ≤ a / 48 := by rw [hγ_def]; nlinarith
  have hK1 : 1 ≤ K := by omega
  have hKa : 4 < a / 2 * K := by
    have : 8 / a ≤ (⌈8 / a⌉₊ : ℝ) := Nat.le_ceil _
    have e : a / 2 * (8 / a) = 4 := by field_simp; ring
    have : (K : ℝ) = ⌈8 / a⌉₊ + 1 := by rw [hK_def]; push_cast; ring
    nlinarith
  -- eventual facts in the number of intervals
  have hnum := linking_numeric 114 N₀L K (ε₀ := a / 2) (γ := γ) (α := a / 4) (by positivity) hγ0
    (by positivity) (by rw [hγ_def]; nlinarith) (by rw [hγ_def]; nlinarith) hKa hK1
  have hXf := ev_X_facts N₀D (e := a / 2) (by positivity)
  have hkb := ev_k_bound ((4 : ℝ) ^ (1 / a)) (b := 2 * γ / a) (α := a / 4)
    (by rw [hγ_def]; field_simp; nlinarith) (by positivity)
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 (hnum.and (hXf.and hkb))
  -- eventual facts in `n`
  set e := (1 - a) * (1 - a - γ) with he_def
  have he1 : 1 - ε < e := by rw [he_def, hγ_def]; nlinarith
  have he0 : 0 < e := by rw [he_def, hγ_def]; nlinarith
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 ((floors ha0 (by linarith)).and
    ((ev_nat (ev_rpow_ge (show 0 < 1 - a by linarith) X₀)).and
    ((ev_dense_final (ε := ε) (a := a) (by linarith)).and
    ((ev_sparse_final he1 he0).and (ev_E ha0)))))
  refine ⟨n₀, fun n hn f hf => ?_⟩
  obtain ⟨⟨ht2, ht_lo, ht_hi, hQ, hX_lo, hX_hi, hn0, hnle⟩, hbig, hd, hs, hE⟩ := hn₀ n hn
  set t := ⌊(n : ℝ) ^ a⌋₊ with ht_def
  set X : ℝ := ((2 * Conc.nQ n t : ℕ) : ℝ) with hX_def
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  obtain ⟨⟨hx1, hcol, hq1, n8, hEt⟩, ⟨hND, hX3, h56, h2l, hcov⟩, hk6⟩ := hX₀ X (hbig.trans hX_lo)
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht2
  -- `t ≥ X^(a/2)`
  have htX : X ^ (a / 2) ≤ (t : ℝ) := by
    have : X ^ (a / 2) ≤ (n : ℝ) ^ (a / 2) :=
      Real.rpow_le_rpow (by linarith) hX_hi (by positivity)
    linarith
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n7', n9, n10⟩ := hEt t htX
  set L := Real.log X with hL_def
  have hL1 : 1 < L := by
    rw [hL_def, Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hLn : L ≤ Real.log n := Real.log_le_log (by linarith) hX_hi
  have hw : 0 < L ^ 56 := by positivity
  by_cases hdense : X < 4 * (Conc.heavy t f).card * L ^ 56
  · -- the dense case of Claim 2.12
    obtain ⟨l, hl, hc⟩ := Conc.dense_path (f := f) hn0 ht2 hQ hf.1
    refine ⟨l, hl, ?_⟩
    set c := countPairs (Conc.Mrel n f) l
    have hc' : 2 * ((Conc.heavy t f).card : ℝ) ≤ t * c := by exact_mod_cast hc
    have hlog : L ^ 56 ≤ Real.log n ^ 56 := pow_le_pow_left₀ (by linarith) hLn _
    have hna : (0 : ℝ) < (n : ℝ) ^ a := by positivity
    have hsplit : (n : ℝ) ^ (1 - a) = (n : ℝ) ^ a * (n : ℝ) ^ (1 - 2 * a) := by
      rw [← Real.rpow_add (by linarith)]; ring_nf
    have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
    -- `n^(1-a) ≤ X < 2 t c L^56 ≤ 2 n^a c (log n)^56`
    have h1 : X < 2 * (n : ℝ) ^ a * c * Real.log n ^ 56 := by
      have e1 : 4 * ((Conc.heavy t f).card : ℝ) * L ^ 56 =
          (2 * (Conc.heavy t f).card) * (2 * L ^ 56) := by ring
      have e2 : (t * c) * (2 * L ^ 56) ≤ ((n : ℝ) ^ a * c) * (2 * Real.log n ^ 56) :=
        mul_le_mul (mul_le_mul_of_nonneg_right ht_hi hc0) (by linarith) (by positivity)
          (by positivity)
      have e3 := mul_le_mul_of_nonneg_right hc' (show (0 : ℝ) ≤ 2 * L ^ 56 by positivity)
      have e4 : ((n : ℝ) ^ a * c) * (2 * Real.log n ^ 56) =
          2 * (n : ℝ) ^ a * c * Real.log n ^ 56 := by ring
      linarith
    have h2 : (n : ℝ) ^ a * (2 * Real.log n ^ 56 * (n : ℝ) ^ (1 - ε)) <
        (n : ℝ) ^ a * (2 * Real.log n ^ 56 * c) := by
      have hA := mul_le_mul_of_nonneg_left hd hna.le
      have e5 : (n : ℝ) ^ a * (2 * Real.log n ^ 56 * c) =
          2 * (n : ℝ) ^ a * c * Real.log n ^ 56 := by ring
      rw [← hsplit] at hA
      linarith
    have hlpos : 0 < 2 * Real.log n ^ 56 := by
      have : 0 < Real.log n := by linarith
      positivity
    have h3 := lt_of_mul_lt_mul_left h2 hna.le
    have h4 := lt_of_mul_lt_mul_left h3 hlpos.le
    exact h4.le
  · -- the sparse case: expander decomposition and the probabilistic core
    push_neg at hdense
    have hUc : ((Finset.univ : Finset (Fin (2 * Conc.nQ n t))).card : ℝ) = X := by
      simp [hX_def]
    have hdeg := Conc.degree_sum_IG (t := t) hf
    have hdegR : ((2 * (2 * Conc.nQ n t * t) : ℕ) : ℝ) ≤
        ((∑ I, degIn (Conc.IG t f) Finset.univ I : ℕ) : ℝ) +
          2 * t * ((Conc.heavy t f).card : ℝ) + 2 * n := by exact_mod_cast hdeg
    have hnleR : (n : ℝ) ≤ (Conc.nQ n t : ℝ) * t + t + 1 := by exact_mod_cast hnle
    push_cast at hdegR
    have hXQ : X = 2 * (Conc.nQ n t : ℝ) := by rw [hX_def]; push_cast; ring
    have hheavy : 2 * t * ((Conc.heavy t f).card : ℝ) ≤ t * X / (2 * L ^ 56) := by
      rw [le_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left hdense (show (0 : ℝ) ≤ t by positivity)
      calc 2 * t * ((Conc.heavy t f).card : ℝ) * (2 * L ^ 56) =
          t * (4 * (Conc.heavy t f).card * L ^ 56) := by ring
        _ ≤ t * X := this
    have h3t : 2 * (t : ℝ) + 2 ≤ t * X / (2 * L ^ 56) := by
      rw [le_div_iff₀ (by positivity)]
      have h6 := mul_le_mul_of_nonneg_left h56 (show (0 : ℝ) ≤ t by positivity)
      have h7 : (2 * (t : ℝ) + 2) * (2 * L ^ 56) ≤ (3 * t) * (2 * L ^ 56) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have e : (3 * (t : ℝ)) * (2 * L ^ 56) = t * (6 * L ^ 56) := by ring
      linarith
    have hsumdeg : (t : ℝ) * (1 - L ^ (-(56 : ℝ))) * X ≤
        ∑ v ∈ (Finset.univ : Finset (Fin (2 * Conc.nQ n t))),
          (degIn (Conc.IG t f) Finset.univ v : ℝ) := by
      have e56 : L ^ (-(56 : ℝ)) = 1 / L ^ 56 := by
        rw [Real.rpow_neg (by linarith), show (56 : ℝ) = ((56 : ℕ) : ℝ) by norm_num,
          Real.rpow_natCast]; simp
      rw [e56]
      have e1 : (t : ℝ) * (1 - 1 / L ^ 56) * X = t * X - t * X / L ^ 56 := by
        field_simp
      have e2 : t * X / L ^ 56 = 2 * (t * X / (2 * L ^ 56)) := by field_simp
      rw [e1, e2]
      have hXt : (t : ℝ) * X = 2 * ((Conc.nQ n t : ℝ) * t) := by rw [hXQ]; ring
      linarith
    obtain ⟨m, W, H, -, hWd, hH, hexp, havg, hmin, hcovW⟩ := hDb (Fin (2 * Conc.nQ n t))
      (Conc.IG t f) Finset.univ (t : ℝ) (L ^ (-(56 : ℝ)))
      (by have : (N₀D : ℝ) ≤ ((Finset.univ : Finset (Fin (2 * Conc.nQ n t))).card : ℝ) := by
            rw [hUc]; exact hND
          exact_mod_cast this)
      (by rw [hUc]; linarith) (Real.rpow_nonneg (by linarith) _) (by rw [hUc])
      (fun v _ => by exact_mod_cast Conc.degIn_IG_le hf.1 v) (by rw [hUc]; exact hsumdeg)
    rw [hUc] at hcovW
    have hSX : X / 2 ≤ ∑ i, ((W i).card : ℝ) := by
      have := mul_le_mul_of_nonneg_right (show (1 : ℝ) / 2 ≤ 1 - Real.log (Real.log (Real.log X)) ^ 2 /
        Real.log (Real.log X) by linarith) (show (0 : ℝ) ≤ X by linarith)
      linarith
    have hne : ∃ i, (W i).Nonempty := by
      by_contra hcon
      push_neg at hcon
      have : ∑ i, ((W i).card : ℝ) = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [hcon i]; simp
      linarith
    -- the parameters of the core
    set r := X ^ (-γ) with hr_def
    have hX0 : 0 < X := by linarith
    have hr0 : 0 < r := Real.rpow_pos_of_pos hX0 _
    set y := (4 / r ^ 2) ^ (1 / a) with hy_def
    have hr2 : 4 / r ^ 2 = 4 * X ^ (2 * γ) := by
      have : r ^ 2 = (X ^ (2 * γ))⁻¹ := by
        rw [hr_def, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le, ← Real.rpow_neg hX0.le]
        congr 1; push_cast; ring
      rw [this, div_inv_eq_mul]
    have hy : y = (4 : ℝ) ^ (1 / a) * X ^ (2 * γ / a) := by
      rw [hy_def, hr2, Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hX0.le]
      ring_nf
    have hy0 : 0 < y := by rw [hy]; positivity
    set k := ⌈y⌉₊ with hk_def
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 (Nat.pos_iff_ne_zero.1 (Nat.ceil_pos.2 hy0))
    have hky : y ≤ k := Nat.le_ceil _
    have hkp : (k : ℝ) ^ (-a) ≤ r ^ 2 / 4 := by
      have h1 : (k : ℝ) ^ (-a) ≤ y ^ (-a) :=
        Real.rpow_le_rpow_of_nonpos hy0 hky (by linarith)
      have h2 : y ^ (-a) = r ^ 2 / 4 := by
        rw [hy_def, ← Real.rpow_mul (by positivity), show 1 / a * -a = -1 by field_simp,
          Real.rpow_neg_one, inv_div]
      linarith
    have hkA : 6 * (k : ℝ) ≤ X ^ (a / 4) := by
      have : (k : ℝ) < y + 1 := Nat.ceil_lt_add_one hy0.le
      rw [hy] at this
      linarith
    obtain ⟨l, hl, hc⟩ := Conc.main_case hLb hn0 ht2 hQ hf W H hWd hH hexp havg hmin hne
      (A := X ^ (a / 4)) (r := r) (q := X ^ (-γ / 7)) (δ := a) (k := k) (Kc := K)
      hk1 ha0 (by linarith) hkp hkA hK1 hr0 (Real.rpow_pos_of_pos hX0 _) hq1 hcol
      n1 n2 (by exact_mod_cast n3) n5 n6 n7 n7' n8 n9 n10 hX3
    refine ⟨l, hl, ?_⟩
    set S := ∑ i, ((W i).card : ℝ)
    set c := countPairs (Conc.Mrel n f) l
    -- `X^(1-a-γ) / 4 ≤ r S^(1-a) / 2`
    have hS0 : 0 < S := by linarith
    have hSa : (X / 2) ^ (1 - a) ≤ S ^ (1 - a) :=
      Real.rpow_le_rpow (by linarith) hSX (by linarith)
    have hX2 : X ^ (1 - a) / 2 ≤ (X / 2) ^ (1 - a) := by
      rw [Real.div_rpow hX0.le (by norm_num)]
      have : (2 : ℝ) ^ (1 - a) ≤ 2 := by
        calc (2 : ℝ) ^ (1 - a) ≤ 2 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 2 := Real.rpow_one 2
      have hpos : 0 < (2 : ℝ) ^ (1 - a) := by positivity
      exact div_le_div_of_nonneg_left (by positivity) hpos this
    have hmul : r * X ^ (1 - a) = X ^ (1 - a - γ) := by
      rw [hr_def, ← Real.rpow_add hX0]; ring_nf
    have hcount : X ^ (1 - a - γ) / 4 ≤ c + 1 := by
      have : r * (X ^ (1 - a) / 2) ≤ r * S ^ (1 - a) :=
        mul_le_mul_of_nonneg_left (hX2.trans hSa) hr0.le
      have e : r * (X ^ (1 - a) / 2) = X ^ (1 - a - γ) / 2 := by rw [← hmul]; ring
      have e' : r * (S ^ (1 - a) / 2) = r * S ^ (1 - a) / 2 := by ring
      linarith
    -- `n^e ≤ X^(1-a-γ)`
    have hne' : (n : ℝ) ^ e ≤ X ^ (1 - a - γ) := by
      rw [he_def, Real.rpow_mul (by linarith)]
      exact Real.rpow_le_rpow (by positivity) hX_lo (by linarith)
    have : (c : ℝ) = countPairs (fun i j => matchAdj n f i j ∨ matchAdj n f j i) l := rfl
    rw [← this]
    linarith

end Lovasz
