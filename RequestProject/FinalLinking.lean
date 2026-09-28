module
public import RequestProject.VTMain
public import RequestProject.DecompMain

/-!
# The main theorems with Lemma 2.3 proved

`expander_decomposition` proves Lemma 2.3 of the paper (the packing of a nearly regular graph by
nearly regular robust sublinear expanders, Lemma 4.1 of the cited work on sublinear expanders).
Hence the only result from the sublinear-expander literature that remains a hypothesis is the
linking lemma (Lemma 2.4).
-/

@[expose] public section


namespace Lovasz

/-- **Theorem 1.2** (the cycle-and-matching theorem), assuming only Lemma 2.4 of the paper. -/
theorem cycle_matching_theorem_of_linking (hL : LinkingLemma 114) : CycleMatchingTheorem :=
  cycle_matching_theorem expander_decomposition hL

/-- **Theorem 3.17**: every connected Cayley graph of order `n ≥ n₀(ε)` contains a path with at
least `n^(1-ε)` edges, assuming only Lemma 2.4 and the Tessera–Tointon theorem (3.16). -/
theorem cayley_long_path_of_linking (hL : LinkingLemma 114) (hTT : TesseraTointonCayley) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (H : Type) [Group H] [Finite H] (S : Set H),
      (cay S).Connected → n₀ ≤ Nat.card H →
      ∃ l : List H, IsPathL (cay S) l ∧ (Nat.card H : ℝ) ^ (1 - ε) ≤ (l.length : ℝ) - 1 :=
  cayley_long_path_of_cited expander_decomposition hL hTT

/-- **Theorem A.1**: every connected vertex-transitive graph of order `n ≥ n₀(ε)` contains a path
with at least `n^(1-ε)` edges, assuming only Lemma 2.4, Theorem 3.16 and Lemma A.2. -/
theorem vt_long_path_of_linking (hL : LinkingLemma 114) (hTT : TesseraTointonCayley)
    (hTTvt : TesseraTointonVT) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (X : SimpleGraph V),
      X.Connected → VertexTransitive X → n₀ ≤ Fintype.card V →
      ∃ l : List V, IsPathL X l ∧ (Fintype.card V : ℝ) ^ (1 - ε) ≤ (l.length : ℝ) - 1 :=
  vt_long_path_of_cited expander_decomposition hL hTT hTTvt

end Lovasz
