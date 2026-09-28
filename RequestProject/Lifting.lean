module
public import RequestProject.Corridor
public import RequestProject.Window
public import RequestProject.Attach

/-!
# The small-diameter-fibre lifting theorem (Theorem 3.9)
-/

@[expose] public section


open Classical

namespace Lovasz

lemma lifting_arith (m τ b L R lg pY pX c0 η : ℝ) (hm : 2 ≤ m) (hL0 : 0 ≤ L) (hb1 : 1 ≤ b)
    (hbL : b ≤ L + 1) (hτ : m / (16 * (L + 1)) ≤ τ) (hLR : L + 1 ≤ 20 * R * lg) (hR : 1 ≤ R)
    (hlg : 0 < lg) (hpY : 0 ≤ pY) (hc0 : 0 < c0) (hη0 : 0 < η) (hη1 : η < 1)
    (hX : c0 * (τ ^ 2 / m) ^ (1 - η) * pY / b ^ 2 ≤ pX) :
    c0 / (256 * 20 ^ 4) * m ^ (1 - η) * pY / (R * lg) ^ 4 ≤ pX := by
  refine le_trans ?_ hX
  have hL1 : 0 < L + 1 := by linarith
  have hτ0 : 0 < τ := lt_of_lt_of_le (by positivity) hτ
  have h1 : m / (256 * (L + 1) ^ 2) ≤ τ ^ 2 / m := by
    rw [div_le_div_iff₀ (by positivity) (by linarith)]
    have : m ≤ τ * (16 * (L + 1)) := by rwa [div_le_iff₀ (by positivity)] at hτ
    nlinarith
  have hy : 1 ≤ 256 * (L + 1) ^ 2 := by nlinarith
  have h2 : m ^ (1 - η) / (256 * (L + 1) ^ 2) ≤ (τ ^ 2 / m) ^ (1 - η) := by
    calc m ^ (1 - η) / (256 * (L + 1) ^ 2) ≤ m ^ (1 - η) / (256 * (L + 1) ^ 2) ^ (1 - η) := by
          gcongr
          calc (256 * (L + 1) ^ 2) ^ (1 - η) ≤ (256 * (L + 1) ^ 2) ^ (1:ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hy (by linarith)
            _ = _ := Real.rpow_one _
      _ = (m / (256 * (L + 1) ^ 2)) ^ (1 - η) :=
          (Real.div_rpow (by linarith) (by positivity) _).symm
      _ ≤ (τ ^ 2 / m) ^ (1 - η) := Real.rpow_le_rpow (by positivity) h1 (by linarith)
  have h3 : (L + 1) ^ 4 ≤ 20 ^ 4 * (R * lg) ^ 4 := by
    rw [← mul_pow]; gcongr; linarith
  have hRlg : 0 < R * lg := by positivity
  calc c0 / (256 * 20 ^ 4) * m ^ (1 - η) * pY / (R * lg) ^ 4
      = c0 * m ^ (1 - η) * pY / (256 * (20 ^ 4 * (R * lg) ^ 4)) := by
        field_simp
    _ ≤ c0 * m ^ (1 - η) * pY / (256 * (L + 1) ^ 4) := by
        gcongr
    _ = c0 * (m ^ (1 - η) / (256 * (L + 1) ^ 2)) * pY / (L + 1) ^ 2 := by
        field_simp
    _ ≤ c0 * (τ ^ 2 / m) ^ (1 - η) * pY / b ^ 2 := by
        gcongr

/-- **Theorem 3.9.** Let `N ◁ H` have order `m ≥ 2` and suppose every coset of `N` has ambient
diameter at most `R ≥ 1` in `X = Cay(H, S)`.  Then, with `Y = Cay(H/N, S)`,
`p(X) ≥ c_η m^(1-η) p(Y) / (R log (2m))⁴`. -/
theorem fibre_lifting (h12 : CycleMatchingTheorem) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ (H : Type) [Group H] [Finite H] (S : Set H) (N : Subgroup H) [N.Normal]
      (R : ℕ), 2 ≤ Nat.card N → 1 ≤ R →
      (∀ x y : H, (x : H ⧸ N) = y → WalkLe (cay S) Set.univ x y R) →
      c * (Nat.card N : ℝ) ^ (1 - η) *
          pathOrder (cay ((QuotientGroup.mk : H → H ⧸ N) '' S)) /
          ((R : ℝ) * Real.log (2 * Nat.card N)) ^ 4 ≤
        pathOrder (cay S) := by
  obtain ⟨c0, hc0, hcor⟩ := corridor h12 η hη0 hη1
  refine ⟨c0 / (256 * 20 ^ 4), by positivity, fun H _ _ S N _ R hm hR hwalk => ?_⟩
  obtain ⟨Z, h1Z, hZinv, hWcard, hdiam⟩ := window S N R hR hwalk
  set L := (4 * Nat.log 2 (Nat.card N) + 6) * R with hL
  set W := Z.image (QuotientGroup.mk : H → H ⧸ N) with hW
  set τ := ⌈(Nat.card N : ℝ) / (16 * (L + 1))⌉₊ with hτ
  have hmR : (2 : ℝ) ≤ Nat.card N := by exact_mod_cast hm
  have hτ1 : 1 ≤ τ := Nat.one_le_iff_ne_zero.2 (by
    rw [hτ, ne_eq, Nat.ceil_eq_zero, not_le]; positivity)
  have hWne : W.Nonempty := ⟨_, Finset.mem_image_of_mem _ h1Z⟩
  have hrail : ∀ g : H ⧸ N, ∀ B ∈ W.image (g * ·), ∃ T : Finset H,
      (∀ t ∈ T, (t : H ⧸ N) = B) ∧ τ ≤ T.card ∧
      HasRail (cay S) {x | (x : H ⧸ N) ∈ W.image (g * ·)} T := by
    intro g B hB
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨_, hz', rfl⟩ := Finset.mem_image.1 hB
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hz'
    obtain ⟨T0, hT0, hT0card, hT0rail⟩ := exists_rail S N Z L hdiam hZinv z hz
    refine ⟨T0.image (h * ·), ?_, ?_, ?_⟩
    · intro t ht
      obtain ⟨t0, ht0, rfl⟩ := Finset.mem_image.1 ht
      rw [QuotientGroup.mk_mul, mk_eq_of_mul_inv_mem N (hT0 t0 ht0)]
    · rw [Finset.card_image_of_injective _ (mul_right_injective h)]
      exact Nat.ceil_le.2 hT0card
    · have := hT0rail.map_mul_left h
      convert this using 1
      ext x
      simp only [Set.mem_setOf_eq, Finset.mem_image, Set.mem_image, Finset.mem_coe, hW]
      constructor
      · rintro ⟨_, ⟨y, hy, rfl⟩, hx⟩
        refine ⟨h⁻¹ * x, mem_of_mk_eq N (Z := (Z : Set H)) hZinv hy ?_, by group⟩
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← hx]; group
      · rintro ⟨y, hy, rfl⟩
        exact ⟨_, ⟨y, hy, rfl⟩, by rw [QuotientGroup.mk_mul]⟩
  have hX := hcor H S N W τ hWne hτ1 hrail
  have hb1 : (1 : ℝ) ≤ W.card := by exact_mod_cast hWne.card_pos
  have hbL : (W.card : ℝ) ≤ L + 1 := by
    have : W.card ≤ L := hWcard
    have : (W.card : ℝ) ≤ L := by exact_mod_cast this
    linarith
  have hLR := window_bound_le (Nat.card N) R hm hR
  have hlg : 0 < Real.log (2 * Nat.card N) := Real.log_pos (by linarith)
  exact lifting_arith (Nat.card N) τ W.card L R _ _ _ c0 η hmR (by positivity) hb1 hbL
    (Nat.le_ceil _) (by rw [hL]; exact_mod_cast hLR) (by exact_mod_cast hR) hlg
    (by positivity) hc0 hη0 hη1 hX

end Lovasz
