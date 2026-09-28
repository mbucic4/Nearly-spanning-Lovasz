module
public import Mathlib
public import RequestProject.GRLatticeBox
public import RequestProject.GRRoots

/-!
# Green–Ruzsa, a large coset box inside a Bohr set

For `d` characters of a finite abelian group `G`, there are a subgroup `H`, steps `g_j` and
lengths `ℓ_j` (`j < d`) such that every `h + ∑ n_j g_j` (`h ∈ H`, `|n_j| ≤ ℓ_j`) lies in the Bohr
set `{x : Re χ x ≥ 1/2 for all χ}`, this parametrization is injective, and
`|G| ≤ (32 d)^d |H| ∏ (2 ℓ_j + 1)`.
-/

@[expose] public section

open Finset

namespace GreenRuzsa

lemma natAbs_sub_le_of_div_eq {N a b : ℕ} (hb : b < N)
    (h : 8 * a / N = 8 * b / N) : ((a : ℤ) - b).natAbs ≤ N / 8 := by
  have hN : 0 < N := by omega
  have e1 := Nat.div_add_mod (8 * a) N
  have e2 := Nat.div_add_mod (8 * b) N
  have r1 := Nat.mod_lt (8 * a) hN
  have r2 := Nat.mod_lt (8 * b) hN
  rw [h] at e1
  set X := N * (8 * b / N)
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  omega

variable {G : Type} [AddCommGroup G] [Fintype G]

open Classical in
theorem bohr_box (Γ : Finset (AddChar G ℂ)) (hΓ : Γ.Nonempty) :
    ∃ (H : AddSubgroup G) (g : Fin Γ.card → G) (ℓ : Fin Γ.card → ℕ),
      (∀ h ∈ H, ∀ n : Fin Γ.card → ℤ, (∀ j, |n j| ≤ ℓ j) →
        ∀ χ ∈ Γ, 1 / 2 ≤ (χ (h + ∑ j, n j • g j)).re) ∧
      (∀ h ∈ H, ∀ h' ∈ H, ∀ n n' : Fin Γ.card → ℤ, (∀ j, |n j| ≤ ℓ j) → (∀ j, |n' j| ≤ ℓ j) →
        h + ∑ j, n j • g j = h' + ∑ j, n' j • g j → h = h' ∧ n = n') ∧
      Fintype.card G ≤ (32 * Γ.card) ^ Γ.card *
        ((univ.filter fun x => x ∈ H).card * ∏ j, (2 * ℓ j + 1)) := by
  classical
  set ι := ↥Γ
  haveI : Nonempty ι := hΓ.to_subtype
  have hd : Fintype.card ι = Γ.card := Fintype.card_coe Γ
  set N := Fintype.card G with hNdef
  have hN : 0 < N := Fintype.card_pos
  haveI : NeZero N := ⟨hN.ne'⟩
  choose ψ hψ using fun i : ι => addChar_param_of_pow N hN (i : AddChar G ℂ)
    (addChar_pow_card (i : AddChar G ℂ))
  set Ψ : G →+ (ι → ZMod N) := AddMonoidHom.mk' (fun g i => ψ i g)
    (by intro a b; funext i; simp) with hΨ
  set red : (ι → ℤ) →+ (ι → ZMod N) := AddMonoidHom.compLeft (Int.castAddHom (ZMod N)) ι
    with hred
  have hred_apply : ∀ x i, red x i = (x i : ZMod N) := fun x i => rfl
  set L : AddSubgroup (ι → ℤ) := Ψ.range.comap red with hL
  have hNL : ∀ i, (N : ℤ) • (Pi.single i 1 : ι → ℤ) ∈ L := by
    intro i
    rw [hL, AddSubgroup.mem_comap]
    have : red ((N : ℤ) • (Pi.single i 1 : ι → ℤ)) = 0 := by
      funext k
      rw [hred_apply]
      simp
    rw [this]
    exact zero_mem _
  set M := N / 8 with hM
  obtain ⟨v, ℓ, hvL, hnorm, hindep, hcount⟩ := lattice_box L N hN hNL M
  have hlift : ∀ j, ∃ g, Ψ g = red (v j) := fun j => by
    have := hvL j
    rw [hL, AddSubgroup.mem_comap, AddMonoidHom.mem_range] at this
    exact this
  choose g hg using hlift
  set H := Ψ.ker with hH
  set Hs := univ.filter fun x => x ∈ H with hHs
  -- reindex from `Fin (card ι)` to `Fin Γ.card`
  set e : Fin Γ.card ≃ Fin (Fintype.card ι) := finCongr hd.symm with he
  have hΨbox : ∀ h ∈ H, ∀ n : Fin (Fintype.card ι) → ℤ,
      Ψ (h + ∑ j, n j • g j) = red (∑ j, n j • v j) := by
    intro h hh n
    rw [map_add, AddMonoidHom.mem_ker.1 hh, zero_add, map_sum, map_sum]
    simp only [map_zsmul, hg]
  have hsmall : ∀ n : Fin (Fintype.card ι) → ℤ, (∀ j, |n j| ≤ ℓ j) →
      ∀ i, 8 * |(∑ j, n j • v j) i| ≤ N := by
    intro n hn i
    have h1 := natAbs_le_supN (∑ j, n j • v j) i
    have h2 := hnorm n hn
    have h3 : ((∑ j, n j • v j) i).natAbs ≤ N / 8 := h1.trans h2
    have h4 : (((∑ j, n j • v j) i).natAbs : ℤ) ≤ ((N / 8 : ℕ) : ℤ) := by exact_mod_cast h3
    rw [Int.natCast_natAbs] at h4
    have h5 : ((N / 8 : ℕ) : ℤ) * 8 ≤ N := by exact_mod_cast Nat.div_mul_le_self N 8
    linarith
  refine ⟨H, fun j => g (e j), fun j => ℓ (e j), ?_, ?_, ?_⟩
  · -- the box lies in the Bohr set
    intro h hh n hn χ hχ
    set n' : Fin (Fintype.card ι) → ℤ := fun j => n (e.symm j) with hn'
    have hsum : ∑ j, n j • g (e j) = ∑ j, n' j • g j := by
      rw [← e.symm.sum_comp]
      simp [hn']
    have hn'b : ∀ j, |n' j| ≤ ℓ j := fun j => by
      simpa [hn'] using hn (e.symm j)
    rw [hsum]
    set i : ι := ⟨χ, hχ⟩
    set t := (∑ j, n' j • v j) i
    have hχp : χ (h + ∑ j, n' j • g j) = expQ N t := by
      refine hψ i _ t ?_
      have := congrFun (hΨbox h hh n') i
      simp only [hΨ, AddMonoidHom.mk'_apply] at this
      rw [this, hred_apply]
    rw [hχp]
    exact half_le_re_expQ hN (hsmall n' hn'b i)
  · -- injectivity
    intro h hh h' hh' n₁ n₂ hn₁ hn₂ heq
    set m₁ : Fin (Fintype.card ι) → ℤ := fun j => n₁ (e.symm j)
    set m₂ : Fin (Fintype.card ι) → ℤ := fun j => n₂ (e.symm j)
    have hs₁ : ∑ j, n₁ j • g (e j) = ∑ j, m₁ j • g j := by
      rw [← e.symm.sum_comp]; simp [m₁]
    have hs₂ : ∑ j, n₂ j • g (e j) = ∑ j, m₂ j • g j := by
      rw [← e.symm.sum_comp]; simp [m₂]
    have hb₁ : ∀ j, |m₁ j| ≤ ℓ j := fun j => by simpa [m₁] using hn₁ (e.symm j)
    have hb₂ : ∀ j, |m₂ j| ≤ ℓ j := fun j => by simpa [m₂] using hn₂ (e.symm j)
    rw [hs₁, hs₂] at heq
    have hred : red (∑ j, m₁ j • v j) = red (∑ j, m₂ j • v j) := by
      rw [← hΨbox h hh, ← hΨbox h' hh', heq]
    have hx : ∑ j, m₁ j • v j = ∑ j, m₂ j • v j := by
      funext i
      have h1 := congrFun hred i
      rw [hred_apply, hred_apply, ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
      have a1 := hsmall m₁ hb₁ i
      have a2 := hsmall m₂ hb₂ i
      have := Int.eq_zero_of_abs_lt_dvd h1 (by
        have hN' : (0 : ℤ) < N := by exact_mod_cast hN
        have c1 := le_abs_self ((∑ j, m₁ j • v j) i)
        have c2 := neg_abs_le ((∑ j, m₁ j • v j) i)
        have c3 := le_abs_self ((∑ j, m₂ j • v j) i)
        have c4 := neg_abs_le ((∑ j, m₂ j • v j) i)
        rw [abs_lt]
        constructor <;> linarith)
      linarith
    have hm : m₁ = m₂ := by
      have := hindep (m₁ - m₂) (by
        simp only [Pi.sub_apply, sub_smul, sum_sub_distrib, hx, sub_self])
      exact sub_eq_zero.1 this
    have hn : n₁ = n₂ := by
      funext j
      have := congrFun hm (e j)
      simpa [m₁, m₂] using this
    refine ⟨?_, hn⟩
    rw [hm] at heq
    exact add_right_cancel heq
  · -- counting
    set Qs := univ.image Ψ with hQs
    have hcardG : N = Qs.card * Hs.card := by
      show Fintype.card G = _
      rw [← card_univ, card_eq_sum_card_fiberwise (f := Ψ) (t := Qs)
        (fun x _ => mem_image_of_mem _ (mem_univ x))]
      rw [sum_const_nat]
      intro y hy
      obtain ⟨g₀, -, rfl⟩ := mem_image.1 hy
      refine card_nbij' (fun x => x - g₀) (fun x => x + g₀) ?_ ?_ ?_ ?_
      · intro x hx
        simp only [coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hx ⊢
        simp [hHs, hH, AddMonoidHom.mem_ker, map_sub, hx]
      · intro x hx
        simp only [hHs, hH, coe_filter, Set.mem_setOf_eq, mem_univ, true_and,
          AddMonoidHom.mem_ker] at hx ⊢
        simp [map_add, hx]
      · intro x _; simp
      · intro x _; simp
    -- pigeonhole on the residue cells
    set cell : (ι → ZMod N) → (ι → ℕ) := fun q i => 8 * (q i).val / N with hcell
    set T := Fintype.piFinset fun _ : ι => range 8 with hT
    have hmaps : ∀ q ∈ Qs, cell q ∈ T := by
      intro q _
      rw [hT, Fintype.mem_piFinset]
      intro i
      rw [mem_range, hcell]
      simp only
      rw [Nat.div_lt_iff_lt_mul hN]
      have := ZMod.val_lt (q i)
      omega
    have hTcard : T.card = 8 ^ Fintype.card ι := by simp [hT]
    have hQne : Qs.Nonempty := ⟨Ψ 0, mem_image_of_mem _ (mem_univ _)⟩
    obtain ⟨y, -, hy⟩ := exists_le_card_fiber_of_nsmul_le_card_of_maps_to (M := ℚ)
      (b := (Qs.card : ℚ) / 8 ^ Fintype.card ι) hmaps ⟨cell (Ψ 0), hmaps _ (mem_image_of_mem _
        (mem_univ _))⟩ (by rw [hTcard, nsmul_eq_mul]; push_cast; field_simp; rfl)
    set F := Qs.filter fun q => cell q = y with hF
    have hQF : Qs.card ≤ 8 ^ Fintype.card ι * F.card := by
      have : (Qs.card : ℚ) ≤ 8 ^ Fintype.card ι * F.card := by
        rw [div_le_iff₀ (by positivity)] at hy
        linarith
      exact_mod_cast this
    have hFcube : F.card ≤ (cubePts L M).card := by
      rcases F.eq_empty_or_nonempty with hFe | ⟨q₀, hq₀⟩
      · simp [hFe]
      · have hq₀' := mem_filter.1 hq₀
        refine card_le_card_of_injOn (fun q i => ((q i).val : ℤ) - ((q₀ i).val : ℤ)) ?_ ?_
        · intro q hq
          have hq' := mem_filter.1 hq
          rw [mem_coe, mem_cubePts]
          constructor
          · rw [hL, AddSubgroup.mem_comap]
            have : red (fun i => ((q i).val : ℤ) - ((q₀ i).val : ℤ)) = q - q₀ := by
              funext i
              rw [hred_apply]
              simp
            rw [this]
            obtain ⟨a, -, ha⟩ := mem_image.1 hq'.1
            obtain ⟨b, -, hb⟩ := mem_image.1 hq₀'.1
            rw [← ha, ← hb, ← map_sub]
            exact AddMonoidHom.mem_range.2 ⟨_, rfl⟩
          · rw [supN_le_iff]
            intro i
            have hc : cell q i = cell q₀ i := by rw [hq'.2, hq₀'.2]
            exact natAbs_sub_le_of_div_eq (ZMod.val_lt _) hc
        · intro q _ q' _ hqq
          funext i
          have := congrFun hqq i
          simp only [sub_left_inj, Nat.cast_inj] at this
          exact ZMod.val_injective _ this
    rw [hcardG]
    have h32 : (32 * Γ.card) ^ Γ.card = 8 ^ Fintype.card ι * (4 * Fintype.card ι) ^ Fintype.card ι := by
      rw [hd, ← mul_pow]; ring_nf
    have hprod : ∏ j, (2 * ℓ (e j) + 1) = ∏ j, (2 * ℓ j + 1) :=
      Fintype.prod_equiv e _ _ (fun _ => rfl)
    rw [hprod, h32]
    calc Qs.card * Hs.card ≤ 8 ^ Fintype.card ι * (cubePts L M).card * Hs.card := by
          refine Nat.mul_le_mul_right _ (hQF.trans (Nat.mul_le_mul_left _ hFcube))
      _ ≤ 8 ^ Fintype.card ι * ((4 * Fintype.card ι) ^ Fintype.card ι * ∏ j, (2 * ℓ j + 1)) *
            Hs.card := by
          refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hcount)
      _ = _ := by
          rw [hHs]
          ring_nf
          congr

end GreenRuzsa
