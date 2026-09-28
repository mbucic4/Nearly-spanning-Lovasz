module
public import RequestProject.FinalBGT
public import RequestProject.GreenRuzsaFromBGT

/-!
# The main theorems assuming only the main theorem of Breuillard–Green–Tao

Both results that were previously assumed from the approximate-groups literature are now derived
from a single statement, Theorem 1.6 of Breuillard–Green–Tao, *The structure of approximate groups*
(`BGTMainTheorem`):

* the Gromov-type Corollary 11.2 / Remark 11.4 used by Tessera–Tointon (`BreuillardGreenTao`), by
  `breuillardGreenTao_of_main`;
* Tointon's normal-closure lemma (`TointonNormalClosure`, Proposition 7.3 of Tointon's *Freiman's
  theorem in an arbitrary nilpotent group*), by `tointonNormalClosure_of_BGTMain`, via our
  formalization of Tointon's Sections 6–7 and the abelian case of Theorem 1.6.
-/

@[expose] public section


namespace Lovasz

/-- **Theorem 3.17**: every connected Cayley graph of order `n ≥ n₀(ε)` contains a path with at
least `n^(1-ε)` edges, assuming only Theorem 1.6 of Breuillard–Green–Tao. -/
theorem cayley_long_path_of_BGTMain (hM : BGTMainTheorem) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (H : Type) [Group H] [Finite H] (S : Set H),
      (cay S).Connected → n₀ ≤ Nat.card H →
      ∃ l : List H, IsPathL (cay S) l ∧ (Nat.card H : ℝ) ^ (1 - ε) ≤ (l.length : ℝ) - 1 :=
  cayley_long_path_of_BGT (breuillardGreenTao_of_main hM)

/-- **Theorem A.1**: every connected vertex-transitive graph of order `n ≥ n₀(ε)` contains a path
with at least `n^(1-ε)` edges, assuming only Theorem 1.6 of Breuillard–Green–Tao. -/
theorem vt_long_path_of_BGTMain (hM : BGTMainTheorem) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (X : SimpleGraph V),
      X.Connected → VertexTransitive X → n₀ ≤ Fintype.card V →
      ∃ l : List V, IsPathL X l ∧ (Fintype.card V : ℝ) ^ (1 - ε) ≤ (l.length : ℝ) - 1 :=
  vt_long_path_of_BGT (breuillardGreenTao_of_main hM) (tointonNormalClosure_of_BGTMain hM)

end Lovasz
