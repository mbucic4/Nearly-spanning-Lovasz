module
public import RequestProject.FlexibleReduction
public import RequestProject.BGTMain
public import RequestProject.UltraTower
public import RequestProject.FlexibleWitness

/-!
# Flexible regularization, and the unconditional long-path theorems

`Lovasz.flexibleRegularization` proves `FlexibleRegularization` by the uniformity argument: if it
failed for some `K`, choose for each `n` a finite `K`-approximate group `A n` with no flexible
witnesses all of whose parameters are at most `n`.  In the ultraproduct along a nonprincipal
ultrafilter, the internal Sanders tower (`UltraModel.exists_towerData`) gives the locally compact
model, where subgroup trapping, the compact NSS quotient and the full-fibre sandwich produce
internal flexible data with ONE standard parameter tuple
(`UltraModel.TowerData.exists_internal_flexible_data`).  The transfer theorem
(`Ultra.hasFlexibleTrapping_transfer`), the localisation and covering transfers, and one cofinite
threshold give a coordinate `n` contradicting the choice of `A n`.  Only finitely many
ultrafilter-large sets are intersected.

Consequently `FiniteBGTCore` and the Cayley and vertex-transitive long-path theorems hold
unconditionally.

(This file is not a `module` because it imports non-module files.)
-/

@[expose] public section


open Filter
open scoped Pointwise

namespace Lovasz

/-- **Flexible regularization** (proved). -/
theorem flexibleRegularization : FlexibleRegularization := by
  intro K hK
  by_contra hcon
  have hbad : ∀ b : ℕ, ∃ (G : Type) (_ : Group G) (_ : Finite G) (A : Set G),
      IsApproximateSubgroup K A ∧ ∀ (B S : Set G) (κ p m N q r : ℕ), κ ≤ b → p ≤ b → m ≤ b →
        N ≤ b → q ≤ b → r ≤ b → BGT.HasFlexibleTrapping κ p m N B S → B ⊆ A ^ q →
          ¬ (A.ncard : ℝ) ≤ r * B.ncard := by
    intro b
    by_contra h
    apply hcon
    refine ⟨b, fun G _ _ A hA => ?_⟩
    by_contra h'
    apply h
    refine ⟨G, inferInstance, inferInstance, A, hA, ?_⟩
    intro B S κ p m N q r hκ hp hm hN hq hr htrap hBA hAB
    exact h' ⟨B, S, κ, p, m, N, q, r, hκ, hp, hm, hN, hq, hr, htrap, hBA, hAB⟩
  choose G hGrp hFin A hA hno using hbad
  letI : ∀ n, Group (G n) := hGrp
  haveI : ∀ n, Finite (G n) := hFin
  have hA' : ∀ n, IsBGTApproxGroup (2 * K) (A n) := fun n =>
    isBGTApproxGroup_of_isApproximateSubgroup (hA n)
  set U : Ultrafilter ℕ := hyperfilter ℕ with hUdef
  have hU : (U : Filter ℕ) ≤ cofinite := hyperfilter_le_cofinite
  obtain ⟨T, hTA⟩ := UltraModel.exists_towerData (by linarith : (1 : ℝ) ≤ 2 * K) G A hA' hU
  obtain ⟨Bs, Ss, κ, p, m, Nlen, k, q, r, t, y, hκ, hp, hm, hN, hk, h1, hBinv, ht, hcov, hSinv,
    hconj, htrap1, htrap2, hBq, hcovA⟩ := T.exists_internal_flexible_data
  rw [hTA] at hBq hcovA
  have e1 := Ultra.hasFlexibleTrapping_transfer Bs Ss t hκ hp hm hN hk h1 hBinv ht hcov hSinv
    hconj htrap1 htrap2
  have e2 : ∀ᶠ n in (U : Filter ℕ), Bs n ⊆ A n ^ q := by
    rw [← Ultra.internal_pow, Ultra.internal_subset_iff] at hBq
    exact hBq
  have e3 : ∀ᶠ n in (U : Filter ℕ), (A n).ncard ≤ r * (Bs n).ncard :=
    Ultra.eventually_ncard_le_of_subset_translates y A Bs hcovA
  have e4 : ∀ᶠ n in (U : Filter ℕ), κ ≤ n ∧ p ≤ n ∧ m ≤ n ∧ Nlen ≤ n ∧ q ≤ n ∧ r ≤ n := by
    apply hU
    rw [Nat.cofinite_eq_atTop]
    exact eventually_atTop.2 ⟨κ + p + m + Nlen + q + r, fun n hn => by omega⟩
  obtain ⟨n, ⟨⟨h1n, h2n⟩, h3n⟩, hκn, hpn, hmn, hNn, hqn, hrn⟩ := (((e1.and e2).and e3).and e4).exists
  exact hno n (Bs n) (Ss n) κ p m Nlen q r hκn hpn hmn hNn hqn hrn h1n h2n (by exact_mod_cast h3n)

/-- **The finite structure theorem `FiniteBGTCore`** (unconditional). -/
theorem finiteBGTCore : FiniteBGTCore :=
  finiteBGTCore_of_flexibleRegularization flexibleRegularization

/-- **Theorem 3.17, Cayley case** (unconditional): for every `ε > 0`, every sufficiently large
connected finite Cayley graph has a path with at least `|H|^(1-ε)` edges. -/
theorem cayley_long_path_unconditional :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (H : Type) [Group H] [Finite H] (S : Set H),
      (cay S).Connected → n₀ ≤ Nat.card H →
      ∃ l : List H, IsPathL (cay S) l ∧ (Nat.card H : ℝ) ^ (1 - ε) ≤ (l.length : ℝ) - 1 :=
  cayley_long_path_of_flexibleRegularization flexibleRegularization

/-- **Theorem A.1, vertex-transitive case** (unconditional). -/
theorem vt_long_path_unconditional :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (X : SimpleGraph V),
      X.Connected → VertexTransitive X → n₀ ≤ Fintype.card V →
      ∃ l : List V, IsPathL X l ∧ (Fintype.card V : ℝ) ^ (1 - ε) ≤ (l.length : ℝ) - 1 :=
  vt_long_path_of_flexibleRegularization flexibleRegularization

end Lovasz
