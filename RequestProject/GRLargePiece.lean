module
public import Mathlib

/-!
# A large-piece adapter for the abelian Green–Ruzsa input

If a `K`-approximate subgroup `A` of an abelian group has a large piece `P ⊆ A^m`
(`|P| ≥ η |A|`) lying in `H · ⟨F⟩` for a subgroup `H` and a short set `F ⊆ A^m`, then all of `A`
lies in `H · ⟨X⟩` for a set `X ⊆ A^m` with `|X| ≤ ⌊K^m / η⌋ + |F|`.  This uses only Ruzsa
covering and commutativity; it is a step towards the rank form of the Green–Ruzsa theorem
(`Tointon.GreenRuzsaRank`), which is proved in `GRFinal.lean` (`Tointon.greenRuzsaRank`).
-/

@[expose] public section

open scoped Pointwise

namespace Tointon

/-- **Large-piece adapter.** -/
theorem large_piece_adapter {Z : Type*} [CommGroup Z] [DecidableEq Z] {K η : ℝ}
    {A P : Finset Z} (hA : IsApproximateSubgroup K (A : Set Z)) {m d : ℕ} (hm : 1 ≤ m)
    (hη : 0 < η) (hPA : (P : Set Z) ⊆ (A : Set Z) ^ m) (hPcard : η * A.card ≤ P.card)
    (H : Subgroup Z) (F : Finset Z) (hF : (F : Set Z) ⊆ (A : Set Z) ^ m) (hFd : F.card ≤ d)
    (hPHF : (P : Set Z) ⊆ (H : Set Z) * (Subgroup.closure (F : Set Z) : Set Z)) :
    ∃ X : Finset Z, (X : Set Z) ⊆ (A : Set Z) ^ m ∧ X.card ≤ ⌊K ^ m / η⌋₊ + d ∧
      (A : Set Z) ⊆ (H : Set Z) * (Subgroup.closure (X : Set Z) : Set Z) := by
  have hA1 : (1 : Z) ∈ A := by exact_mod_cast hA.one_mem
  have hK : 0 ≤ K := zero_le_one.trans hA.one_le
  have hApos : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.2 ⟨1, hA1⟩
  have hPpos : (0 : ℝ) < P.card := lt_of_lt_of_le (mul_pos hη hApos) hPcard
  have hP : P.Nonempty := Finset.card_pos.1 (by exact_mod_cast hPpos)
  -- `|A P| ≤ |A^(m+1)| ≤ K^m |A| ≤ (K^m / η) |P|`
  have hAP : A * P ⊆ A ^ (m + 1) := by
    intro x hx
    rw [← Finset.mem_coe, Finset.coe_mul] at hx
    rw [← Finset.mem_coe, Finset.coe_pow, pow_succ']
    obtain ⟨a, ha, p, hp, rfl⟩ := hx
    exact Set.mul_mem_mul ha (hPA hp)
  have hcard : ((A * P).card : ℝ) ≤ K ^ m / η * P.card := by
    calc ((A * P).card : ℝ) ≤ (A ^ (m + 1)).card := by exact_mod_cast Finset.card_le_card hAP
      _ ≤ K ^ m * A.card := by simpa using hA.card_pow_le (n := m + 1)
      _ = K ^ m / η * (η * A.card) := by field_simp
      _ ≤ K ^ m / η * P.card := by
          gcongr
  obtain ⟨T, hTA, hTcard, hAT⟩ := Finset.ruzsa_covering_mul hP hcard
  refine ⟨T ∪ F, ?_, ?_, ?_⟩
  · rw [Finset.coe_union]
    refine Set.union_subset (fun t ht => ?_) hF
    have : (A : Set Z) ⊆ (A : Set Z) ^ m := by
      calc (A : Set Z) = (A : Set Z) ^ 1 := (pow_one _).symm
        _ ⊆ (A : Set Z) ^ m := Set.pow_subset_pow_right hA.one_mem hm
    exact this (hTA ht)
  · refine (Finset.card_union_le _ _).trans (Nat.add_le_add ?_ hFd)
    exact Nat.le_floor hTcard
  · intro x hx
    have hx' := hAT hx
    rw [← Finset.mem_coe, Finset.coe_mul, Finset.coe_div] at hx'
    obtain ⟨t, ht, y, hy, rfl⟩ := hx'
    obtain ⟨p, hp, q, hq, rfl⟩ := hy
    obtain ⟨h₁, hh₁, f₁, hf₁, rfl⟩ := hPHF hp
    obtain ⟨h₂, hh₂, f₂, hf₂, rfl⟩ := hPHF hq
    have hsub : Subgroup.closure (F : Set Z) ≤ Subgroup.closure ((T ∪ F : Finset Z) : Set Z) :=
      Subgroup.closure_mono (by rw [Finset.coe_union]; exact Set.subset_union_right)
    refine ⟨h₁ * h₂⁻¹, H.mul_mem hh₁ (H.inv_mem hh₂), t * f₁ * f₂⁻¹, ?_, ?_⟩
    · refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ (hsub hf₁)) (Subgroup.inv_mem _ (hsub hf₂))
      exact Subgroup.subset_closure (by rw [Finset.coe_union]; exact Or.inl ht)
    · show h₁ * h₂⁻¹ * (t * f₁ * f₂⁻¹) = t * (h₁ * f₁ / (h₂ * f₂))
      simp only [div_eq_mul_inv, mul_inv_rev]
      ac_rfl

end Tointon
