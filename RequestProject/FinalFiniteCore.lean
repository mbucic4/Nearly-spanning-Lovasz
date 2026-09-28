module
public import RequestProject.BGTFiniteCore
public import RequestProject.BGTReduction
public import RequestProject.FinalBGT
public import RequestProject.TointonNormal

/-!
# The main theorems assuming only the reduced finite structure theorem

* Cayley case: assumes only `FiniteBGTCore`.
* Vertex-transitive case: assumes `FiniteBGTCore` and the rank form of the Green–Ruzsa theorem for
  finite abelian groups (`Tointon.GreenRuzsaRank`), from which Tointon's normal-closure lemma is
  derived in `TointonNormal.lean`.

Both hypotheses follow from Theorem 1.6 of Breuillard–Green–Tao (`finiteBGTCore_of_main`,
`greenRuzsaRank_of_BGTMain`), but are much weaker than it.

Finally, `FiniteBGTCore` is itself reduced (`finiteBGTCore_of_regularization`) to regularization
(`StrongRegularization`) and step-independent uniformization for finite nilpotent groups
(`NilpotentFiniteCore`), giving `cayley_long_path_of_regularization` and
`vt_long_path_of_regularization`.
-/

@[expose] public section


namespace Lovasz

/-- **Theorem 3.17** (Cayley case) assuming only the reduced finite structure theorem
`FiniteBGTCore`. -/
theorem cayley_long_path_of_finiteCore (hC : FiniteBGTCore) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (H : Type) [Group H] [Finite H] (S : Set H),
      (cay S).Connected → n₀ ≤ Nat.card H →
      ∃ l : List H, IsPathL (cay S) l ∧ (Nat.card H : ℝ) ^ (1 - ε) ≤ (l.length : ℝ) - 1 :=
  cayley_long_path_of_TT (tesseraTointon_cayley_of_boundedPower (bgtBoundedPower_of_finiteCore hC))

/-- **Theorem A.1** (vertex-transitive case) assuming only the reduced finite structure theorem
`FiniteBGTCore` and the rank form of the Green–Ruzsa theorem for finite abelian groups. -/
theorem vt_long_path_of_finiteCore (hC : FiniteBGTCore) (hGR : Tointon.GreenRuzsaRank) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (X : SimpleGraph V),
      X.Connected → VertexTransitive X → n₀ ≤ Fintype.card V →
      ∃ l : List V, IsPathL X l ∧ (Fintype.card V : ℝ) ^ (1 - ε) ≤ (l.length : ℝ) - 1 :=
  vt_long_path_of_TT (tesseraTointon_cayley_of_boundedPower (bgtBoundedPower_of_finiteCore hC))
    (tesseraTointonVT_of_boundedPower (bgtBoundedPower_of_finiteCore hC)
      (Tointon.normalClosure_subset_pow_of_greenRuzsa hGR))

/-- **Theorem 3.17** (Cayley case) assuming only regularization and step-independent
uniformization for finite nilpotent groups. -/
theorem cayley_long_path_of_regularization (hR : StrongRegularization)
    (hN : NilpotentFiniteCore) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (H : Type) [Group H] [Finite H] (S : Set H),
      (cay S).Connected → n₀ ≤ Nat.card H →
      ∃ l : List H, IsPathL (cay S) l ∧ (Nat.card H : ℝ) ^ (1 - ε) ≤ (l.length : ℝ) - 1 :=
  cayley_long_path_of_finiteCore (finiteBGTCore_of_regularization hR hN)

/-- **Theorem A.1** (vertex-transitive case) assuming only regularization, step-independent
uniformization for finite nilpotent groups, and the rank form of Green–Ruzsa. -/
theorem vt_long_path_of_regularization (hR : StrongRegularization) (hN : NilpotentFiniteCore)
    (hGR : Tointon.GreenRuzsaRank) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (X : SimpleGraph V),
      X.Connected → VertexTransitive X → n₀ ≤ Fintype.card V →
      ∃ l : List V, IsPathL X l ∧ (Fintype.card V : ℝ) ^ (1 - ε) ≤ (l.length : ℝ) - 1 :=
  vt_long_path_of_finiteCore (finiteBGTCore_of_regularization hR hN) hGR

end Lovasz
