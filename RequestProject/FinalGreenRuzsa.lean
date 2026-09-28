module
public import RequestProject.FinalNilpotent
public import RequestProject.GRFinal

/-!
# Consequences of the unconditional Green–Ruzsa rank theorem

`Tointon.greenRuzsaRank` (in `GRFinal.lean`) proves `Tointon.GreenRuzsaRank` without any
hypothesis.  Hence `NilpotentFiniteCore` holds unconditionally, and both long-path theorems
follow from the single remaining hypothesis `StrongRegularization`.  (They are NOT unconditional:
`StrongRegularization` is still an explicit hypothesis.)

(This file is not a `module` because it imports the non-module file `FinalNilpotent.lean`.)
-/

@[expose] public section


namespace Lovasz

/-- The step-independent structure theorem for approximate groups in finite nilpotent groups,
now unconditional. -/
theorem nilpotentFiniteCore : NilpotentFiniteCore :=
  nilpotentFiniteCore_of_greenRuzsa Tointon.greenRuzsaRank

/-- **Theorem 3.17** (Cayley case) assuming only the regularization input. -/
theorem cayley_long_path_of_regularization_only (hR : StrongRegularization) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (H : Type) [Group H] [Finite H] (S : Set H),
      (cay S).Connected → n₀ ≤ Nat.card H →
      ∃ l : List H, IsPathL (cay S) l ∧ (Nat.card H : ℝ) ^ (1 - ε) ≤ (l.length : ℝ) - 1 :=
  cayley_long_path_of_regularization_greenRuzsa hR Tointon.greenRuzsaRank

/-- **Theorem A.1** (vertex-transitive case) assuming only the regularization input. -/
theorem vt_long_path_of_regularization_only (hR : StrongRegularization) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (X : SimpleGraph V),
      X.Connected → VertexTransitive X → n₀ ≤ Fintype.card V →
      ∃ l : List V, IsPathL X l ∧ (Fintype.card V : ℝ) ^ (1 - ε) ≤ (l.length : ℝ) - 1 :=
  vt_long_path_of_regularization_greenRuzsa hR Tointon.greenRuzsaRank

end Lovasz
