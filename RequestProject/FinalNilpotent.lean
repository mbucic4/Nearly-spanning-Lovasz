module
public import RequestProject.NilTransfer
public import RequestProject.FinalFiniteCore

/-!
# Discharging `NilpotentFiniteCore` from the rank form of Green–Ruzsa

`nilpotentFiniteCore_of_greenRuzsa` proves the step-independent structure theorem for approximate
groups in finite nilpotent groups, `NilpotentFiniteCore`, assuming only `Tointon.GreenRuzsaRank`
(the rank form of the Green–Ruzsa theorem for finite abelian groups).  The proof is the nilpotent
case of Tointon, *Approximate subgroups of residually nilpotent groups* (Propositions 3.1, 4.1
and 5.1), formalised in `NilLayers.lean`, `NilCentral.lean` and `NilAssembly.lean`.

Consequently the long-path theorems need only `StrongRegularization` and `GreenRuzsaRank`.

(This file is not a `module` because it imports the non-module files `BGTReduction.lean` and
`FinalFiniteCore.lean`, where `NilpotentFiniteCore` and the long-path theorems live.)
-/

@[expose] public section


open scoped Pointwise

namespace Lovasz

/-- **Step-independent structure of approximate groups in finite nilpotent groups**, from the rank
form of the Green–Ruzsa theorem.  With `κ = ⌈K⌉` one may take `cover = κ^(18κ⁶ + 2)`,
`step = κ⁶`, and a radius given by an explicit recurrence in `κ`; none depends on the group or on
its nilpotency class. -/
theorem nilpotentFiniteCore_of_greenRuzsa (hGR : Tointon.GreenRuzsaRank) :
    NilpotentFiniteCore := by
  intro K hK
  set κ := ⌈K⌉₊ with hκdef
  have hκ : 1 ≤ κ := by
    have : (1 : ℝ) ≤ κ := hK.trans (Nat.le_ceil K)
    exact_mod_cast this
  refine ⟨κ ^ (18 * κ ^ 6 + 2), κ ^ 6,
    (Finset.range (κ ^ 6 + 1)).sup (fun t => (Tointon.sched hGR κ t).1) + 2, ?_⟩
  intro G _ _ _ A hA
  have hA' : IsApproximateSubgroup (κ : ℝ) A := hA.mono (Nat.le_ceil K)
  obtain ⟨C, hcard, hlcs⟩ := Tointon.exists_large_piece_bounded_lcs hGR hκ hA'
  refine ⟨C, ?_, hlcs⟩
  classical
  haveI := Fintype.ofFinite G
  set P : Set G := A ^ 2 ∩ (C : Set G) with hP
  obtain ⟨T, hT, hTcard⟩ := exists_coset_cover_card_mul_le A.toFinset P.toFinset C
    (by intro x hx; simp only [Set.coe_toFinset] at hx; exact hx.2)
  refine ⟨T, ?_, by simpa using hT⟩
  -- `|A P| ≤ |A³| ≤ κ² |A| ≤ κ^(18κ⁶ + 2) |P|`
  have hAfin : IsApproximateSubgroup (κ : ℝ) ((A.toFinset : Finset G) : Set G) := by
    rwa [Set.coe_toFinset]
  have h3 : ((A.toFinset ^ 3 : Finset G).card : ℝ) ≤ (κ : ℝ) ^ 2 * A.toFinset.card := by
    simpa using hAfin.card_pow_le (n := 3)
  have hsub : A.toFinset * P.toFinset ⊆ A.toFinset ^ 3 := by
    intro x hx
    rw [← Finset.mem_coe, Finset.coe_mul, Set.coe_toFinset, Set.coe_toFinset] at hx
    rw [← Finset.mem_coe, Finset.coe_pow, Set.coe_toFinset, pow_succ']
    obtain ⟨a, ha, p, hp, rfl⟩ := hx
    exact Set.mul_mem_mul ha hp.1
  have hPpos : 0 < P.toFinset.card := by
    refine Finset.card_pos.2 ⟨1, ?_⟩
    rw [Set.mem_toFinset]
    exact ⟨Set.one_mem_pow hA.one_mem, C.one_mem⟩
  have hAcard : A.toFinset.card = A.ncard := (Set.ncard_eq_toFinset_card' A).symm
  have hPcard : P.toFinset.card = P.ncard := (Set.ncard_eq_toFinset_card' P).symm
  have h3' : (A.toFinset ^ 3 : Finset G).card ≤ κ ^ 2 * A.toFinset.card := by exact_mod_cast h3
  have key : T.card * P.toFinset.card ≤ κ ^ (18 * κ ^ 6 + 2) * P.toFinset.card := by
    calc T.card * P.toFinset.card ≤ (A.toFinset * P.toFinset).card := hTcard
      _ ≤ (A.toFinset ^ 3 : Finset G).card := Finset.card_le_card hsub
      _ ≤ κ ^ 2 * A.toFinset.card := h3'
      _ ≤ κ ^ 2 * (κ ^ (18 * κ ^ 6) * P.toFinset.card) := by
          rw [hAcard, hPcard]; exact Nat.mul_le_mul_left _ hcard
      _ = κ ^ (18 * κ ^ 6 + 2) * P.toFinset.card := by ring
  exact Nat.le_of_mul_le_mul_right key hPpos

/-- **Theorem 3.17** (Cayley case) assuming only regularization and the rank form of the
Green–Ruzsa theorem. -/
theorem cayley_long_path_of_regularization_greenRuzsa (hR : StrongRegularization)
    (hGR : Tointon.GreenRuzsaRank) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (H : Type) [Group H] [Finite H] (S : Set H),
      (cay S).Connected → n₀ ≤ Nat.card H →
      ∃ l : List H, IsPathL (cay S) l ∧ (Nat.card H : ℝ) ^ (1 - ε) ≤ (l.length : ℝ) - 1 :=
  cayley_long_path_of_regularization hR (nilpotentFiniteCore_of_greenRuzsa hGR)

/-- **Theorem A.1** (vertex-transitive case) assuming only regularization and the rank form of
the Green–Ruzsa theorem. -/
theorem vt_long_path_of_regularization_greenRuzsa (hR : StrongRegularization)
    (hGR : Tointon.GreenRuzsaRank) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (X : SimpleGraph V),
      X.Connected → VertexTransitive X → n₀ ≤ Fintype.card V →
      ∃ l : List V, IsPathL X l ∧ (Fintype.card V : ℝ) ^ (1 - ε) ≤ (l.length : ℝ) - 1 :=
  vt_long_path_of_regularization hR (nilpotentFiniteCore_of_greenRuzsa hGR) hGR

end Lovasz
