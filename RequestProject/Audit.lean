module
public import RequestProject.FlexibleRegularizationProof
public import RequestProject.FinalTT
public import RequestProject.DecompMain
public import RequestProject.LinkLemma
public import RequestProject.GRFinal
public import RequestProject.FinalGreenRuzsa

/-!
# Axiom audit of the main theorems

Each `#guard_msgs` block below pins the exact output of `#print axioms`.  If any of these
theorems ever came to depend on `sorryAx` or on any axiom other than the three standard ones
(`propext`, `Classical.choice`, `Quot.sound`), this file would fail to build.

The statement of the Cayley theorem is also pinned, and a non-vacuity check shows that its
hypotheses are satisfied by a connected Cayley graph of every order `n ≥ 1`.

(This file is not a `module` because it imports non-module files.)
-/

@[expose] public section


/-- info: 'Lovasz.cayley_long_path_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lovasz.cayley_long_path_unconditional

/-- info: 'Lovasz.vt_long_path_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lovasz.vt_long_path_unconditional

/-- info: 'Lovasz.cycle_matching_theorem_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lovasz.cycle_matching_theorem_proved

/-- info: 'Lovasz.flexibleRegularization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lovasz.flexibleRegularization

/-- info: 'Lovasz.finiteBGTCore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lovasz.finiteBGTCore

/-- info: 'Lovasz.expander_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lovasz.expander_decomposition

/-- info: 'Lovasz.linking_lemma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lovasz.linking_lemma

/-- info: 'Tointon.greenRuzsaRank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tointon.greenRuzsaRank

/-- info: 'Lovasz.nilpotentFiniteCore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lovasz.nilpotentFiniteCore

namespace Lovasz.Audit

/-- The Cayley theorem (Theorem 3.17) has exactly this statement, with no hypotheses. -/
example :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (H : Type) [Group H] [Finite H] (S : Set H),
      (cay S).Connected → n₀ ≤ Nat.card H →
      ∃ l : List H, IsPathL (cay S) l ∧ (Nat.card H : ℝ) ^ (1 - ε) ≤ (l.length : ℝ) - 1 :=
  cayley_long_path_unconditional

/-- The vertex-transitive theorem (Theorem A.1) has exactly this statement, with no
hypotheses. -/
example :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (X : SimpleGraph V),
      X.Connected → VertexTransitive X → n₀ ≤ Fintype.card V →
      ∃ l : List V, IsPathL X l ∧ (Fintype.card V : ℝ) ^ (1 - ε) ≤ (l.length : ℝ) - 1 :=
  vt_long_path_unconditional

/-- Non-vacuity: for every `n ≥ 1` the cyclic group of order `n` has a connected Cayley graph
of order `n`, so the hypotheses of the Cayley theorem can be met at every order. -/
example (n : ℕ) [NeZero n] :
    (cay (Set.univ : Set (Multiplicative (ZMod n)))).Connected ∧
      Nat.card (Multiplicative (ZMod n)) = n := by
  refine ⟨cay_connected_iff.2 (Subgroup.closure_univ), ?_⟩
  simp [Nat.card_eq_fintype_card, ZMod.card]

/-- Non-vacuity in use: applying the theorem with `ε = 1/2` to cyclic groups gives, for all
large `n`, a path in a connected Cayley graph of order `n` with at least `√n` edges. -/
example : ∃ n₀ : ℕ, ∀ n : ℕ, [NeZero n] → n₀ ≤ n →
    ∃ l : List (Multiplicative (ZMod n)), IsPathL (cay Set.univ) l ∧
      (n : ℝ) ^ (1 - (1 / 2 : ℝ)) ≤ (l.length : ℝ) - 1 := by
  obtain ⟨n₀, hn₀⟩ := cayley_long_path_unconditional (1 / 2) (by norm_num)
  refine ⟨n₀, fun n _ hn => ?_⟩
  have hcard : Nat.card (Multiplicative (ZMod n)) = n := by
    simp [Nat.card_eq_fintype_card, ZMod.card]
  obtain ⟨l, hl, hlen⟩ := hn₀ (Multiplicative (ZMod n)) Set.univ
    (cay_connected_iff.2 Subgroup.closure_univ) (by rw [hcard]; exact hn)
  exact ⟨l, hl, by rw [hcard] at hlen; exact hlen⟩

end Lovasz.Audit
