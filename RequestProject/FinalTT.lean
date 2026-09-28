module
public import RequestProject.FinalLinking
public import RequestProject.LinkLemma

/-!
# The main theorems, assuming only the Tessera–Tointon results

Lemma 2.3 (`expander_decomposition`) and Lemma 2.4 (`linking_lemma`) are now both proved, so:

* Theorem 1.2 holds unconditionally;
* the Cayley case (Theorem 3.17) assumes only the Tessera–Tointon theorem (Theorem 3.16);
* the vertex-transitive case (Theorem A.1) assumes only Theorem 3.16 and Lemma A.2, which the
  paper also takes from the work of Tessera and Tointon.
-/

@[expose] public section


namespace Lovasz

/-- **Theorem 1.2** (the cycle-and-matching theorem), with no hypotheses. -/
theorem cycle_matching_theorem_proved : CycleMatchingTheorem :=
  cycle_matching_theorem_of_linking (linking_lemma 114)

/-- **Theorem 3.17**: every connected Cayley graph of order `n ≥ n₀(ε)` contains a path with at
least `n^(1-ε)` edges, assuming only the Tessera–Tointon theorem (Theorem 3.16). -/
theorem cayley_long_path_of_TT (hTT : TesseraTointonCayley) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (H : Type) [Group H] [Finite H] (S : Set H),
      (cay S).Connected → n₀ ≤ Nat.card H →
      ∃ l : List H, IsPathL (cay S) l ∧ (Nat.card H : ℝ) ^ (1 - ε) ≤ (l.length : ℝ) - 1 :=
  cayley_long_path_of_linking (linking_lemma 114) hTT

/-- **Theorem A.1**: every connected vertex-transitive graph of order `n ≥ n₀(ε)` contains a path
with at least `n^(1-ε)` edges, assuming only the Tessera–Tointon results used in the paper
(Theorem 3.16 and Lemma A.2). -/
theorem vt_long_path_of_TT (hTT : TesseraTointonCayley) (hTTvt : TesseraTointonVT) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (X : SimpleGraph V),
      X.Connected → VertexTransitive X → n₀ ≤ Fintype.card V →
      ∃ l : List V, IsPathL X l ∧ (Fintype.card V : ℝ) ^ (1 - ε) ≤ (l.length : ℝ) - 1 :=
  vt_long_path_of_linking (linking_lemma 114) hTT hTTvt

end Lovasz
