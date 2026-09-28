module
public import Mathlib
public import RequestProject.GRModel
public import RequestProject.GRBohrBox

/-!
# Green–Ruzsa, transfer of a coset box through a local Freiman isomorphism

Combining the dense Freiman model, the weak Bogolyubov lemma and the coset-box lemma, and
transporting the box back through the local Freiman `2`-isomorphism `4A' → 4A`, every
`κ`-approximate group `A` in a finite abelian group contains, inside `4A`, a large piece
`P` (`|A| ≤ C |P|`) lying in `H + ⟨W⟩` with `H ⊆ 4A` a subgroup and `W ⊆ 4A`, `|W| ≤ R`.
-/

@[expose] public section

open Finset

namespace GreenRuzsa

/-- Local additivity on a coset box determines the map on the whole box. -/
lemma box_transfer {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (Dom : Set X) (F : X → Y)
    (hadd : ∀ x y, x ∈ Dom → y ∈ Dom → x + y ∈ Dom → F (x + y) = F x + F y)
    (hneg : ∀ x, x ∈ Dom → -x ∈ Dom → F (-x) = -F x)
    (H : AddSubgroup X) {d : ℕ} (g : Fin d → X) (ℓ : Fin d → ℕ)
    (hbox : ∀ h ∈ H, ∀ n : Fin d → ℤ, (∀ j, |n j| ≤ ℓ j) → h + ∑ j, n j • g j ∈ Dom) :
    ∀ h ∈ H, ∀ n : Fin d → ℤ, (∀ j, |n j| ≤ ℓ j) →
      F (h + ∑ j, n j • g j) = F h + ∑ j, n j • (if 0 < ℓ j then F (g j) else 0) := by
  classical
  suffices hsuff : ∀ m : ℕ, ∀ h ∈ H, ∀ n : Fin d → ℤ, (∀ j, |n j| ≤ ℓ j) →
      ∑ j, (n j).natAbs = m →
      F (h + ∑ j, n j • g j) = F h + ∑ j, n j • (if 0 < ℓ j then F (g j) else 0) from
    fun h hh n hn => hsuff _ h hh n hn rfl
  intro m
  induction m with
  | zero =>
    intro h _ n _ hm
    have hn0 : n = 0 := by
      funext j
      have := (sum_eq_zero_iff.1 hm) j (mem_univ j)
      simpa using this
    subst hn0
    simp
  | succ m ih =>
    intro h hh n hn hm
    obtain ⟨j₀, hj₀⟩ : ∃ j₀, n j₀ ≠ 0 := by
      by_contra hall
      push_neg at hall
      simp [hall] at hm
    set σ : ℤ := if 0 < n j₀ then 1 else -1 with hσ
    set n' : Fin d → ℤ := n - σ • Pi.single j₀ 1 with hn'
    have hσabs : σ = 1 ∨ σ = -1 := by rw [hσ]; split_ifs <;> simp
    have hlj₀ : 1 ≤ ℓ j₀ := by
      have := hn j₀
      have : (1 : ℤ) ≤ |n j₀| := Int.one_le_abs hj₀
      omega
    have hn'j : ∀ j, n' j = if j = j₀ then n j₀ - σ else n j := by
      intro j
      by_cases hj : j = j₀
      · subst hj; simp [hn']
      · simp [hn', hj]
    have hn'b : ∀ j, |n' j| ≤ ℓ j := by
      intro j
      rw [hn'j]
      split_ifs with hj
      · subst hj
        have := hn j
        rw [hσ]
        split_ifs with hpos <;> rw [abs_le] at this ⊢ <;> constructor <;> omega
      · exact hn j
    have hn'sum : ∑ j, (n' j).natAbs = m := by
      have e1 : ∑ j, (n j).natAbs = (n j₀).natAbs + ∑ j ∈ univ.erase j₀, (n j).natAbs :=
        (add_sum_erase _ _ (mem_univ j₀)).symm
      have e2 : ∑ j, (n' j).natAbs = (n' j₀).natAbs + ∑ j ∈ univ.erase j₀, (n' j).natAbs :=
        (add_sum_erase _ _ (mem_univ j₀)).symm
      have e3 : ∑ j ∈ univ.erase j₀, (n' j).natAbs = ∑ j ∈ univ.erase j₀, (n j).natAbs :=
        sum_congr rfl fun j hj => by rw [hn'j, if_neg (ne_of_mem_erase hj)]
      have e4 : (n' j₀).natAbs + 1 = (n j₀).natAbs := by
        rw [hn'j, if_pos rfl, hσ]
        split_ifs with hpos <;> omega
      omega
    have hsplit : h + ∑ j, n j • g j = (h + ∑ j, n' j • g j) + σ • g j₀ := by
      rw [hn']
      simp only [Pi.sub_apply, sub_smul, sum_sub_distrib, Pi.smul_apply, Pi.single_apply,
        smul_eq_mul, mul_ite, mul_one, mul_zero, ite_smul, zero_smul, sum_ite_eq', mem_univ,
        if_true]
      abel
    have hstep : σ • g j₀ ∈ Dom ∧ F (σ • g j₀) = σ • F (g j₀) := by
      have hb : ∀ τ : ℤ, (τ = 1 ∨ τ = -1) → τ • g j₀ ∈ Dom := by
        intro τ hτ
        have := hbox 0 H.zero_mem (τ • Pi.single j₀ 1) (fun j => by
          by_cases hj : j = j₀
          · subst hj; rcases hτ with rfl | rfl <;> simp <;> omega
          · simp [hj])
        simpa [Pi.single_apply, ite_smul] using this
      refine ⟨hb σ hσabs, ?_⟩
      rcases hσabs with h1 | h1
      · rw [h1, one_smul, one_smul]
      · rw [h1, neg_one_smul, neg_one_smul]
        have h1' := hb 1 (Or.inl rfl)
        have h2' := hb (-1) (Or.inr rfl)
        rw [one_smul] at h1'
        rw [neg_one_smul] at h2'
        exact hneg _ h1' h2'
    rw [hsplit, hadd _ _ (hbox h hh n' hn'b) hstep.1 (hsplit ▸ hbox h hh n hn), hstep.2,
      ih h hh n' hn'b hn'sum, add_assoc]
    congr 1
    rw [hn']
    simp only [Pi.sub_apply, sub_smul, sum_sub_distrib, Pi.smul_apply, Pi.single_apply,
      smul_eq_mul, mul_ite, mul_one, mul_zero, ite_smul, zero_smul, sum_ite_eq', mem_univ,
      if_true, if_pos (show 0 < ℓ j₀ by omega)]
    abel

/-- The rank bound `R = 4 · modelBound(κ)²`. -/
noncomputable def grRank (κ : ℕ) : ℕ := 4 * modelBound κ ^ 2

/-- The density loss `C = (32 R)^R`. -/
noncomputable def grLoss (κ : ℕ) : ℕ := (32 * grRank κ) ^ grRank κ

lemma card_Icc_neg (ℓ : ℕ) : (Finset.Icc (-(ℓ : ℤ)) ℓ).card = 2 * ℓ + 1 := by
  rw [Int.card_Icc]
  omega

/-- **A large structured piece inside `4A`.** -/
theorem exists_large_piece (κ : ℕ) (hκ : 1 ≤ κ) (G : Type) [AddCommGroup G] [Fintype G]
    [DecidableEq G] (A : Finset G) (hA : AddApprox κ A) :
    ∃ (P : Finset G) (H : AddSubgroup G) (W : Finset G),
      P ⊆ ksum 4 A ∧ (∀ h ∈ H, h ∈ ksum 4 A) ∧ W ⊆ ksum 4 A ∧ W.card ≤ grRank κ ∧
      A.card ≤ grLoss κ * P.card ∧
      ∀ p ∈ P, ∃ h ∈ H, ∃ w ∈ AddSubgroup.closure (W : Set G), p = h + w := by
  classical
  obtain ⟨G', i1, i2, φ, hφ, hφ0, hcardG'⟩ := exists_dense_model κ hκ G A hA
  have h0 := hA.zero_mem
  set A' := A.image φ with hA'def
  have hcardA : A'.card = A.card := hφ.card_image (by norm_num) h0 hφ0
  have hA' : AddApprox κ A' := hA.image hφ (by norm_num) hφ0
  have hA'ne : A'.Nonempty := ⟨0, hA'.zero_mem⟩
  set Γ := largeSpec A' with hΓ
  have hΓne : Γ.Nonempty := ⟨0, zero_mem_largeSpec A'⟩
  -- the number of characters
  have hd : Γ.card ≤ grRank κ := by
    have h1 := card_largeSpec_mul_le A' hA'ne
    have hApos : (0 : ℝ) < A'.card := by exact_mod_cast hA'ne.card_pos
    have h2 : (Fintype.card G' : ℝ) ≤ modelBound κ * A'.card := by
      rw [hcardA]; exact_mod_cast hcardG'
    have h3 : (Γ.card : ℝ) * (A'.card : ℝ) ^ 2 ≤ 4 * modelBound κ ^ 2 * (A'.card : ℝ) ^ 2 := by
      calc (Γ.card : ℝ) * (A'.card : ℝ) ^ 2 ≤ 4 * (Fintype.card G' : ℝ) ^ 2 := h1
        _ ≤ 4 * (modelBound κ * A'.card) ^ 2 := by gcongr
        _ = 4 * modelBound κ ^ 2 * (A'.card : ℝ) ^ 2 := by ring
    have h4 := le_of_mul_le_mul_right h3 (by positivity)
    rw [grRank]
    exact_mod_cast h4
  obtain ⟨H', g, ℓ, hBohr, hinj, hcount⟩ := bohr_box Γ hΓne
  set Dom : Set G' := (ksum 4 A' : Set G') with hDom
  have hboxDom : ∀ h ∈ H', ∀ n : Fin Γ.card → ℤ, (∀ j, |n j| ≤ ℓ j) → h + ∑ j, n j • g j ∈ Dom := by
    intro h hh n hn
    exact mem_ksum_four_of_bohr A' hA'ne hA'.neg_mem _ fun χ hχ => hBohr h hh n hn χ hχ
  set F := invExt A φ with hF
  have hadd : ∀ x y, x ∈ Dom → y ∈ Dom → x + y ∈ Dom → F (x + y) = F x + F y :=
    fun x y hx hy hxy => invExt_add hφ h0 hφ0 hx hy hxy
  have hneg : ∀ x, x ∈ Dom → -x ∈ Dom → F (-x) = -F x :=
    fun x hx hnx => invExt_neg hφ h0 hφ0 hx hnx
  have hFmem : ∀ x ∈ Dom, F x ∈ ksum 4 A := fun x hx => invExt_mem hφ h0 hφ0 hx
  have hFbox := box_transfer Dom F hadd hneg H' g ℓ hboxDom
  have hH'Dom : ∀ h ∈ H', h ∈ Dom := fun h hh => by
    simpa using hboxDom h hh 0 (fun j => by simp)
  -- the transported subgroup
  let H : AddSubgroup G :=
    { carrier := F '' (H' : Set G')
      add_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a + b, H'.add_mem ha hb,
          hadd a b (hH'Dom a ha) (hH'Dom b hb) (hH'Dom _ (H'.add_mem ha hb))⟩
      zero_mem' := ⟨0, H'.zero_mem, invExt_zero hφ h0 hφ0⟩
      neg_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨-a, H'.neg_mem ha, hneg a (hH'Dom a ha) (hH'Dom _ (H'.neg_mem ha))⟩ }
  set w : Fin Γ.card → G := fun j => if 0 < ℓ j then F (g j) else 0 with hw
  set W : Finset G := univ.image w with hW
  set Box : Finset (Fin Γ.card → ℤ) := Fintype.piFinset fun j => Icc (-(ℓ j : ℤ)) (ℓ j) with hBox
  set Hs : Finset G' := univ.filter fun x => x ∈ H' with hHs
  set P' : Finset G' := (Hs ×ˢ Box).image fun p => p.1 + ∑ j, p.2 j • g j with hP'
  have hBoxmem : ∀ n ∈ Box, ∀ j, |n j| ≤ ℓ j := by
    intro n hn j
    have := Fintype.mem_piFinset.1 hn j
    rw [mem_Icc] at this
    exact abs_le.2 this
  have hP'Dom : ∀ x ∈ P', x ∈ Dom := by
    intro x hx
    obtain ⟨⟨h, n⟩, hp, rfl⟩ := mem_image.1 hx
    rw [mem_product] at hp
    exact hboxDom h (by simpa [hHs] using hp.1) n (hBoxmem n hp.2)
  have hP'card : P'.card = Hs.card * ∏ j, (2 * ℓ j + 1) := by
    rw [hP', card_image_of_injOn, card_product, hBox, Fintype.card_piFinset]
    · simp only [card_Icc_neg]
    · rintro ⟨h₁, n₁⟩ hp₁ ⟨h₂, n₂⟩ hp₂ heq
      rw [mem_coe, mem_product] at hp₁ hp₂
      obtain ⟨e1, e2⟩ := hinj h₁ (by simpa [hHs] using hp₁.1) h₂ (by simpa [hHs] using hp₂.1)
        n₁ n₂ (hBoxmem n₁ hp₁.2) (hBoxmem n₂ hp₂.2) heq
      rw [e1, e2]
  set P : Finset G := P'.image F with hP
  have hPcard : P.card = P'.card :=
    card_image_of_injOn fun x hx y hy hxy =>
      invExt_injOn hφ h0 hφ0 (hP'Dom x hx) (hP'Dom y hy) hxy
  refine ⟨P, H, W, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hp
    exact hFmem x (hP'Dom x hx)
  · rintro _ ⟨a, ha, rfl⟩
    exact hFmem a (hH'Dom a ha)
  · intro x hx
    obtain ⟨j, -, rfl⟩ := mem_image.1 hx
    simp only [hw]
    split_ifs with hj
    · refine hFmem _ ?_
      have := hboxDom 0 H'.zero_mem (Pi.single j 1) (fun k => by
        by_cases hk : k = j
        · subst hk; simp; omega
        · simp [hk])
      simpa [Pi.single_apply] using this
    · exact mem_ksum.2 ⟨fun _ => 0, fun _ => h0, by simp⟩
  · exact card_image_le.trans (by simpa using hd)
  · have h1 : A.card ≤ Fintype.card G' := by
      rw [← hcardA]; exact card_le_univ _
    have h2 : (32 * Γ.card) ^ Γ.card ≤ grLoss κ := by
      rw [grLoss]
      calc (32 * Γ.card) ^ Γ.card ≤ (32 * grRank κ) ^ Γ.card := Nat.pow_le_pow_left (by omega) _
        _ ≤ (32 * grRank κ) ^ grRank κ := by
          refine Nat.pow_le_pow_right ?_ hd
          have : 1 ≤ Γ.card := hΓne.card_pos
          omega
    calc A.card ≤ Fintype.card G' := h1
      _ ≤ (32 * Γ.card) ^ Γ.card * (Hs.card * ∏ j, (2 * ℓ j + 1)) := by
          convert hcount using 3
      _ ≤ grLoss κ * P.card := by
          rw [hPcard, hP'card]
          exact Nat.mul_le_mul_right _ h2
  · intro p hp
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hp
    obtain ⟨⟨h, n⟩, hpn, rfl⟩ := mem_image.1 hx
    rw [mem_product] at hpn
    have hh : h ∈ H' := by simpa [hHs] using hpn.1
    refine ⟨F h, ⟨h, hh, rfl⟩, ∑ j, n j • w j, ?_, hFbox h hh n (hBoxmem n hpn.2)⟩
    refine AddSubgroup.sum_mem _ fun j _ => AddSubgroup.zsmul_mem _ ?_ _
    exact AddSubgroup.subset_closure (by simp [hW])

end GreenRuzsa
