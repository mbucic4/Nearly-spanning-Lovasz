module
public import RequestProject.FinalTT
public import RequestProject.TTCayley
public import RequestProject.TTVT

/-!
# The main theorems assuming only results on approximate groups

`tesseraTointon_cayley_of_BGT` (in `TTCayley.lean`) derives Theorem 3.16 (the Cayley form of the
Tessera–Tointon structure theorem) from the Breuillard–Green–Tao theorem.  Combined with the
proofs of Theorem 1.2 and Theorem 3.17, the Cayley case of the main theorem now depends only on
the Breuillard–Green–Tao theorem.

`tesseraTointonVT_of_BGT` (in `TTVT.lean`) derives Lemma A.2 from the Breuillard–Green–Tao theorem
and Tointon's normal-closure lemma for nilpotent approximate groups, so the vertex-transitive case
depends only on these two results from the approximate-groups literature.
-/

@[expose] public section


namespace Lovasz

/-- **Theorem 3.16** follows from the Breuillard–Green–Tao theorem. -/
theorem tesseraTointonCayley_of_BGT (hB : BreuillardGreenTao) : TesseraTointonCayley :=
  tesseraTointon_cayley_of_BGT hB

/-- **Theorem 3.17**: every connected Cayley graph of order `n ≥ n₀(ε)` contains a path with at
least `n^(1-ε)` edges, assuming only the Breuillard–Green–Tao theorem. -/
theorem cayley_long_path_of_BGT (hB : BreuillardGreenTao) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (H : Type) [Group H] [Finite H] (S : Set H),
      (cay S).Connected → n₀ ≤ Nat.card H →
      ∃ l : List H, IsPathL (cay S) l ∧ (Nat.card H : ℝ) ^ (1 - ε) ≤ (l.length : ℝ) - 1 :=
  cayley_long_path_of_TT (tesseraTointonCayley_of_BGT hB)

/-- **Theorem A.1**: every connected vertex-transitive graph of order `n ≥ n₀(ε)` contains a path
with at least `n^(1-ε)` edges, assuming only the Breuillard–Green–Tao theorem and Tointon's
normal-closure lemma. -/
theorem vt_long_path_of_BGT (hB : BreuillardGreenTao) (hT : TointonNormalClosure) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (X : SimpleGraph V),
      X.Connected → VertexTransitive X → n₀ ≤ Fintype.card V →
      ∃ l : List V, IsPathL X l ∧ (Fintype.card V : ℝ) ^ (1 - ε) ≤ (l.length : ℝ) - 1 :=
  vt_long_path_of_TT (tesseraTointonCayley_of_BGT hB) (tesseraTointonVT_of_BGT hB hT)

end Lovasz
