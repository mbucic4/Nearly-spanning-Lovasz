module
public import Mathlib
public import RequestProject.GRBasic

/-!
# Green–Ruzsa, compression of a cyclic coordinate

If `ψ : G → ℤ/q` is surjective (`q ≥ 2`) and its centred representatives are at most
`q / (16 s)` in absolute value on `A ∋ 0`, then `a ↦ (a - λ(a) z₀, λ(a) mod (q - 1))` is a
normalized Freiman `s`-isomorphism of `A` into the strictly smaller group `ker ψ × ℤ/(q-1)`.
The group `G` is NOT assumed to split.
-/

@[expose] public section

open Finset

namespace GreenRuzsa

variable {G : Type} [AddCommGroup G] [Fintype G]

theorem exists_compression (A : Finset G) (s q : ℕ) (hq : 2 ≤ q) (ψ : G →+ ZMod q)
    (hψ : Function.Surjective ψ) (hsmall : ∀ a ∈ A, 16 * s * |(ψ a).valMinAbs| ≤ q) :
    ∃ (G'' : Type) (_ : AddCommGroup G'') (_ : Fintype G''),
      Fintype.card G'' < Fintype.card G ∧ ∃ c : G → G'', IsFIso s A c ∧ c 0 = 0 := by
  classical
  haveI : NeZero q := ⟨by omega⟩
  haveI : NeZero (q - 1) := ⟨by omega⟩
  obtain ⟨z₀, hz₀⟩ := hψ 1
  set lam : G → ℤ := fun g => (ψ g).valMinAbs with hlam
  have hlamq : ∀ g, ((lam g : ℤ) : ZMod q) = ψ g := fun g => ZMod.coe_valMinAbs _
  have hker : ∀ g, g - lam g • z₀ ∈ ψ.ker := by
    intro g
    rw [AddMonoidHom.mem_ker, map_sub, map_zsmul, hz₀, zsmul_one, hlamq, sub_self]
  refine ⟨ψ.ker × ZMod (q - 1), inferInstance, inferInstance, ?_, ?_⟩
  · -- cardinality
    have hcard : Nat.card G = Nat.card ψ.ker * q := by
      rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup ψ.ker,
        Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv,
        Nat.card_zmod, mul_comm]
    rw [Fintype.card_prod, ZMod.card, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      hcard]
    have : 0 < Nat.card ψ.ker := Nat.card_pos
    exact Nat.mul_lt_mul_of_pos_left (by omega) this
  · refine ⟨fun g => (⟨g - lam g • z₀, hker g⟩, ((lam g : ℤ) : ZMod (q - 1))), ?_, ?_⟩
    · intro a b ha hb
      set Δ : ℤ := ∑ i, lam (a i) - ∑ i, lam (b i) with hΔ
      -- the size of `Δ`
      have hΔq : 8 * |Δ| ≤ q := by
        rcases Nat.eq_zero_or_pos s with hs | hs
        · subst hs
          simp [hΔ]
        · have hsum : ∀ c : Fin s → G, (∀ i, c i ∈ A) → 16 * |∑ i, lam (c i)| ≤ q := by
            intro c hc
            have h1 : |∑ i, lam (c i)| ≤ ∑ i, |lam (c i)| := Finset.abs_sum_le_sum_abs _ _
            have h2 : ∑ i : Fin s, 16 * s * |lam (c i)| ≤ ∑ _i : Fin s, (q : ℤ) :=
              sum_le_sum fun i _ => hsmall _ (hc i)
            rw [← mul_sum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
            have hs' : (0 : ℤ) < s := by exact_mod_cast hs
            have : (s : ℤ) * (16 * ∑ i, |lam (c i)|) ≤ s * q := by linarith
            have := le_of_mul_le_mul_left this hs'
            linarith
          have h1 := hsum a ha
          have h2 := hsum b hb
          have : |Δ| ≤ |∑ i, lam (a i)| + |∑ i, lam (b i)| := abs_sub _ _
          linarith
      have hΔ0 : ∀ m : ℕ, 8 * m > q → ((m : ℤ) ∣ Δ) → Δ = 0 := by
        intro m hm hdvd
        refine Int.eq_zero_of_abs_lt_dvd hdvd ?_
        have : (8 : ℤ) * m > q := by exact_mod_cast hm
        nlinarith [abs_nonneg Δ]
      have hsumG : ∀ c : Fin s → G, ∑ i, (c i - lam (c i) • z₀) =
          ∑ i, c i - (∑ i, lam (c i)) • z₀ := by
        intro c
        rw [sum_sub_distrib, sum_smul]
      simp only [Prod.ext_iff, Prod.fst_sum, Prod.snd_sum, Subtype.ext_iff,
        AddSubgroup.val_finset_sum, hsumG]
      constructor
      · rintro ⟨h1, h2⟩
        have hd : ((q - 1 : ℕ) : ℤ) ∣ Δ := by
          rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
          rw [hΔ, Int.cast_sub]
          push_cast
          rw [h2, sub_self]
        have := hΔ0 (q - 1) (by omega) hd
        have heq : ∑ i, lam (a i) = ∑ i, lam (b i) := by linarith
        rw [heq] at h1
        exact sub_left_injective h1
      · intro h
        have hd : (q : ℤ) ∣ Δ := by
          rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hΔ]
          push_cast
          simp only [hlamq]
          rw [← map_sum, ← map_sum, h, sub_self]
        have := hΔ0 q (by omega) hd
        have heq : ∑ i, lam (a i) = ∑ i, lam (b i) := by linarith
        refine ⟨by rw [h, heq], ?_⟩
        rw [← Int.cast_sum, ← Int.cast_sum, heq]
    · ext
      · simp [hlam]
      · simp [hlam]

end GreenRuzsa
