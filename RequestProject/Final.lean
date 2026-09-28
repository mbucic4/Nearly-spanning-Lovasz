module
public import RequestProject.Main
public import RequestProject.Theorem12

/-!
# Near-linear paths in Cayley graphs, with Theorem 1.2 proved

Combining `cycle_matching_theorem` (Theorem 1.2, derived in this project from Lemmas 2.3 and 2.4
of the paper, which the paper quotes from the literature on sublinear expanders) with
`cayley_long_path` (Theorem 3.17), the only remaining hypotheses are the three results the paper
cites: the expander decomposition lemma, the linking lemma and the Tessera–Tointon structure
theorem.
-/

@[expose] public section


namespace Lovasz

/-- **Theorem 3.17**, with Theorem 1.2 proved: every connected Cayley graph of order `n ≥ n₀(ε)`
contains a path with at least `n^(1-ε)` edges, assuming only the results quoted by the paper
(Lemma 2.3, Lemma 2.4 and Theorem 3.16). -/
theorem cayley_long_path_of_cited (hD : ExpanderDecomposition) (hL : LinkingLemma 114)
    (hTT : TesseraTointonCayley) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (H : Type) [Group H] [Finite H] (S : Set H),
      (cay S).Connected → n₀ ≤ Nat.card H →
      ∃ l : List H, IsPathL (cay S) l ∧ (Nat.card H : ℝ) ^ (1 - ε) ≤ (l.length : ℝ) - 1 :=
  cayley_long_path (cycle_matching_theorem hD hL) hTT

end Lovasz
