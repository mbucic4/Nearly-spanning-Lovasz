module
public import RequestProject.LinkUnion

/-!
# Lemma 5.1 with explicit side conditions

We combine the three good events (Corollary 5.6 for well-expanding sets, (T3) and the size of
the random set) with the deterministic part (`t1_of_goodE`, `linkProp_of_T`).  The numerical
side conditions are hypotheses here; they are verified for large `|U|` in
`RequestProject/LinkNumerics.lean`.
-/

@[expose] public section


open scoped BigOperators
open Classical

namespace Lovasz

noncomputable section

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- **Lemma 5.1** (with explicit numerical side conditions). -/
theorem linking_whp {U : Finset V} {c : ℕ} {s q p E D Kx x : ℝ} {ℓ k : ℕ}
    (hexp : IsExpander G U (1 / 16) c s) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hℓ1 : 1 ≤ ℓ) (hℓp : (ℓ + 2) * p ≤ q / 20)
    (hL : 1 ≤ Real.log U.card ^ c)
    (hrL : 13 * Real.log U.card ^ c ≤ (⌈1 / p⌉₊ : ℝ)) (hs : 4 * (⌈1 / p⌉₊ : ℝ) ^ 3 ≤ s)
    (hEq : 100000 * Real.log U.card ^ c + 50 ≤ q * E)
    (hgrowN : (U.card : ℝ) ≤ (1 + 1 / (1000 * Real.log U.card ^ c)) ^ ℓ)
    (hn : 3 ≤ U.card) (hx : 0 ≤ x) (hnx : (U.card : ℝ) ^ 2 * x ≤ 1)
    (hκ : ∀ u : ℕ, 1 ≤ u → 5 * ℓ * (⌈1 / p⌉₊ : ℝ) ^ 3 * Real.exp (-(q * (E * u) /
        (200000 * (⌈1 / p⌉₊ : ℝ) ^ 3 * Real.log U.card ^ c))) ≤ x ^ u)
    (hDs : 2 * D * E ≤ s) (hDE : 100 * (E + 1) * Real.log U.card ^ c ≤ D)
    (hE0 : 0 ≤ E) (hk : U.card < 2 ^ k)
    (hθ : 2 ≤ 0.55 * q * U.card) (hKx : 0 < Kx)
    (hΛ1 : 8 * (D + 1) * (2 * (1 + (1 + ℓ) + k * (1 + ℓ)) + 1 : ℕ) + 4 ≤ q * Kx)
    (hΛ2 : 2 * D * (2 * (1 + (1 + ℓ) + k * (1 + ℓ)) + 1 : ℕ) * U.card ≤ 0.55 * q * U.card * Kx)
    (hT3n : (U.card : ℝ) * Real.exp (-(0.13 * q * Kx)) ≤ 1)
    (hsum : 6 * (U.card : ℝ) ^ 2 * x + 2 * U.card * Real.exp (-(0.13 * q * Kx)) +
      Real.exp (-(0.0025 * q * U.card)) ≤ 1 / U.card) :
    1 - 1 / (U.card : ℝ) ≤ ppr (fun _ : V => bern q)
      (fun y => LinkProp G U (U.filter (fun v => y v = true)) Kx) := by
  have hμ := isPD_bern (ι := V) hq0.le hq1
  have hn1 : 1 ≤ U.card := by omega
  have hK0 : 0 < Real.log U.card ^ c := by linarith
  have hD1 : 1 ≤ D := by
    have : 0 ≤ 100 * E * Real.log U.card ^ c := by positivity
    nlinarith
  -- the deterministic implication
  have hdet : ∀ y, GoodEProp G U y (0.55 * q * U.card) E (1 + ℓ) ∧ T3Prop G U y q Kx ∧
      ((U.filter (fun v => y v = true)).card : ℝ) < 2 * (0.55 * q * U.card) →
      LinkProp G U (U.filter (fun v => y v = true)) Kx := by
    rintro y ⟨hG, hT3, hR⟩
    have hT1 := t1_of_goodE hexp hG hE0 hK0 hDs hDE hD1
    have hm2 : 3 * (2 * U.card / 3) ≤ 2 * U.card := Nat.mul_div_le _ _
    have hm1 : 1 ≤ 2 * U.card / 3 := by omega
    have hθm : (0.55 * q * U.card) / 2 ≤ ((2 * U.card / 3 : ℕ) : ℝ) := by
      have h1 : ((2 * U.card / 3 : ℕ) : ℝ) ≥ (2 * U.card : ℝ) / 3 - 1 := by
        have := Nat.lt_div_mul_add (a := 2 * U.card) (b := 3) (by norm_num)
        have h2 : ((2 * U.card : ℕ) : ℝ) < ((2 * U.card / 3 : ℕ) : ℝ) * 3 + 3 := by exact_mod_cast this
        push_cast at h2
        linarith
      have hn3 : (3 : ℝ) ≤ U.card := by exact_mod_cast hn
      have : (0.55 * q * U.card) ≤ 0.55 * U.card := by
        have : (0 : ℝ) ≤ U.card := by positivity
        nlinarith
      linarith
    exact linkProp_of_T hT1 hT3 hm1 hm2 hk hq0.le (by linarith) hR hθ hθm hKx hΛ1 hΛ2
  -- the three failure probabilities
  have hf1 := goodE_fail_le hexp hq0 hq1 hp0 hp1 hℓ1 hℓp hL hrL hs hEq hgrowN hn1 hx hnx hκ
  have hf2 := t3_fail_le (G := G) (U := U) hq0 hq1 hT3n
  have hf3 := R_fail_le (U := U) hq0 hq1
  have h1 : ppr (fun _ : V => bern q) (fun y => GoodEProp G U y (0.55 * q * U.card) E (1 + ℓ) ∧ (T3Prop G U y q Kx ∧
      ((U.filter (fun v => y v = true)).card : ℝ) < 2 * (0.55 * q * U.card))) ≤
      ppr (fun _ : V => bern q) (fun y => LinkProp G U (U.filter (fun v => y v = true)) Kx) :=
    ppr_mono hμ fun y hy => hdet y hy
  have h2 := ppr_and_ge hμ (fun y => GoodEProp G U y (0.55 * q * U.card) E (1 + ℓ))
    (fun y => T3Prop G U y q Kx ∧ ((U.filter (fun v => y v = true)).card : ℝ) < 2 * (0.55 * q * U.card))
  have h3 : ppr (fun _ : V => bern q) (fun y => ¬ (T3Prop G U y q Kx ∧
      ((U.filter (fun v => y v = true)).card : ℝ) < 2 * (0.55 * q * U.card))) ≤
      ppr (fun _ : V => bern q) (fun y => ¬ T3Prop G U y q Kx) +
      ppr (fun _ : V => bern q)
        (fun y => ¬ ((U.filter (fun v => y v = true)).card : ℝ) < 2 * (0.55 * q * U.card)) := by
    refine (ppr_mono hμ fun y hy => ?_).trans (ppr_or_le hμ _ _)
    by_contra hc
    push_neg at hc
    exact hy ⟨hc.1, hc.2⟩
  have h4 := ppr_not hμ (fun y => GoodEProp G U y (0.55 * q * U.card) E (1 + ℓ))
  have h4' : ppr (fun _ : V => bern q) (fun y => ¬ GoodEProp G U y (0.55 * q * U.card) E (1 + ℓ)) ≤ 6 * (U.card : ℝ) ^ 2 * x :=
    hf1
  linarith

end

end Lovasz
