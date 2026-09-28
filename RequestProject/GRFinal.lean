module
public import Mathlib
public import RequestProject.GRPieceTransfer
public import RequestProject.GRLargePiece
public import RequestProject.TointonStep

/-!
# The rank form of the Green–Ruzsa theorem for finite abelian groups

`Tointon.greenRuzsaRank` proves `Tointon.GreenRuzsaRank` unconditionally.  With `κ = ⌈K⌉`,
the power is `4` and the rank bound is `⌊K⁴ C⌋ + R`, where `R = 4 · modelBound(κ)²` and
`C = (32 R)^R` depend only on `κ`.

The proof runs in `Additive Z`: a dense Freiman model (`GRModel`), the weak Bogolyubov lemma
(`GRBogolyubov`), a large coset box in a Bohr set (`GRBohrBox`, via the lattice counting of
`GRLatticeBox`), transfer of the box through the local Freiman isomorphism (`GRPieceTransfer`),
and finally the large-piece adapter `Tointon.large_piece_adapter`.
-/

@[expose] public section

open Finset
open scoped Pointwise

namespace GreenRuzsa

variable {Z : Type} [CommGroup Z]

lemma toMul_mem_pow_of_mem_ksum [DecidableEq (Additive Z)] {A : Finset (Additive Z)}
    {B : Set Z} (hAB : ∀ a ∈ A, Additive.toMul a ∈ B) {k : ℕ} {x : Additive Z}
    (hx : x ∈ ksum k A) : Additive.toMul x ∈ B ^ k := by
  obtain ⟨a, ha, rfl⟩ := mem_ksum.1 hx
  rw [toMul_sum]
  clear hx
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.prod_univ_succ, pow_succ']
    exact Set.mul_mem_mul (hAB _ (ha 0)) (ih (fun i => a i.succ) (fun i => ha _))

lemma toMul_mem_closure {W : Finset (Additive Z)} {w : Additive Z}
    (hw : w ∈ AddSubgroup.closure (W : Set (Additive Z))) :
    Additive.toMul w ∈ Subgroup.closure (Additive.toMul '' (W : Set (Additive Z))) := by
  induction hw using AddSubgroup.closure_induction with
  | mem x hx => exact Subgroup.subset_closure ⟨x, hx, rfl⟩
  | zero => exact Subgroup.one_mem _
  | add x y _ _ hx hy => exact Subgroup.mul_mem _ hx hy
  | neg x _ hx => exact Subgroup.inv_mem _ hx

end GreenRuzsa

namespace Tointon

open GreenRuzsa

/-- **The rank form of the Green–Ruzsa theorem** for finite abelian groups, proved
unconditionally. -/
theorem greenRuzsaRank : GreenRuzsaRank := by
  intro K hK
  set κ := ⌈K⌉₊ with hκdef
  have hκ : 1 ≤ κ := by
    have : (1 : ℝ) ≤ κ := hK.trans (Nat.le_ceil K)
    exact_mod_cast this
  set C := grLoss κ with hC
  set R := grRank κ with hR
  have hMB : 0 < modelBound κ := by unfold modelBound; positivity
  have hRpos : 0 < R := by rw [hR, grRank]; positivity
  have hCpos : 0 < C := by rw [hC, grLoss]; positivity
  refine ⟨⌊K ^ 4 / (1 / (C : ℝ))⌋₊ + R, 4, ?_⟩
  intro Z _ _ B hB
  classical
  haveI : Fintype Z := Fintype.ofFinite Z
  -- the additive copy of `B`
  set A : Finset (Additive Z) := univ.filter fun x => Additive.toMul x ∈ B with hAdef
  have hmemA : ∀ x, x ∈ A ↔ Additive.toMul x ∈ B := fun x => by simp [hAdef]
  have hA : AddApprox κ A := by
    refine ⟨(hmemA 0).2 (by simpa using hB.one_mem), fun a ha => ?_, ?_⟩
    · rw [hmemA] at ha ⊢
      have : (Additive.toMul a)⁻¹ ∈ B⁻¹ := Set.inv_mem_inv.2 ha
      rw [hB.inv_eq_self] at this
      simpa using this
    · obtain ⟨F, hFcard, hF⟩ := hB.sq_covBySMul
      refine ⟨F.image Additive.ofMul, (card_image_le).trans ?_, ?_⟩
      · have : (F.card : ℝ) ≤ κ := hFcard.trans (Nat.le_ceil K)
        exact_mod_cast this
      · intro a ha b hb
        rw [hmemA] at ha hb
        have hab : Additive.toMul a * Additive.toMul b ∈ B ^ 2 := by
          rw [sq]; exact Set.mul_mem_mul ha hb
        obtain ⟨f, hf, c, hc, hfc⟩ := Set.mem_smul.1 (hF hab)
        refine ⟨Additive.ofMul f, mem_image_of_mem _ hf, Additive.ofMul c,
          (hmemA _).2 (by simpa using hc), ?_⟩
        apply Additive.toMul.injective
        simp only [toMul_add, toMul_ofMul]
        exact hfc.symm
  obtain ⟨P, H, W, hPA, hHA, hWA, hWcard, hAP, hPHW⟩ := exists_large_piece κ hκ _ A hA
  have hAB : ∀ a ∈ A, Additive.toMul a ∈ B := fun a ha => (hmemA a).1 ha
  -- back to the multiplicative group
  set AZ : Finset Z := A.image Additive.toMul with hAZ
  have hAZB : (AZ : Set Z) = B := by
    ext x
    simp only [hAZ, coe_image, Set.mem_image, mem_coe, hmemA]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx; exact ⟨Additive.ofMul x, by simpa using hx, rfl⟩
  have hAZcard : AZ.card = A.card := card_image_of_injective _ Additive.toMul.injective
  set PZ : Finset Z := P.image Additive.toMul with hPZ
  set WZ : Finset Z := W.image Additive.toMul with hWZ
  set HZ : Subgroup Z := Subgroup.toAddSubgroup.symm H with hHZ
  have hmemHZ : ∀ x, x ∈ HZ ↔ Additive.ofMul x ∈ H := fun x => by simp [hHZ]
  have hBZ : IsApproximateSubgroup K (AZ : Set Z) := by rw [hAZB]; exact hB
  have hPZA : (PZ : Set Z) ⊆ (AZ : Set Z) ^ 4 := by
    rw [hAZB]
    intro x hx
    obtain ⟨p, hp, rfl⟩ := mem_image.1 (mem_coe.1 hx)
    exact toMul_mem_pow_of_mem_ksum hAB (hPA hp)
  have hWZA : (WZ : Set Z) ⊆ (AZ : Set Z) ^ 4 := by
    rw [hAZB]
    intro x hx
    obtain ⟨w, hw, rfl⟩ := mem_image.1 (mem_coe.1 hx)
    exact toMul_mem_pow_of_mem_ksum hAB (hWA hw)
  have hη : (0 : ℝ) < 1 / (C : ℝ) := by positivity
  have hPcard : 1 / (C : ℝ) * AZ.card ≤ PZ.card := by
    rw [hAZcard, hPZ, card_image_of_injective _ Additive.toMul.injective]
    have : (A.card : ℝ) ≤ C * P.card := by exact_mod_cast hAP
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    linarith
  have hWZcard : WZ.card ≤ R := (card_image_le).trans hWcard
  have hPHWZ : (PZ : Set Z) ⊆ (HZ : Set Z) * (Subgroup.closure (WZ : Set Z) : Set Z) := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := mem_image.1 (mem_coe.1 hx)
    obtain ⟨h, hh, w, hw, rfl⟩ := hPHW p hp
    refine Set.mul_mem_mul ((hmemHZ _).2 (by simpa using hh)) ?_
    have := toMul_mem_closure hw
    rw [hWZ, coe_image]
    exact this
  obtain ⟨X, hXA, hXcard, hBX⟩ := large_piece_adapter hBZ (by norm_num : 1 ≤ 4) hη hPZA
    hPcard HZ WZ hWZA hWZcard hPHWZ
  refine ⟨HZ, X, ?_, ?_, hXcard, ?_⟩
  · intro x hx
    rw [SetLike.mem_coe, hmemHZ] at hx
    simpa using toMul_mem_pow_of_mem_ksum hAB (hHA _ hx)
  · rw [← hAZB]; exact hXA
  · rw [← hAZB]; exact hBX

end Tointon
