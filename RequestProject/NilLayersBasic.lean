module
public import RequestProject.NilChain
public import RequestProject.TointonStep

/-!
# Tools for the preliminary layer construction

Finite algebraic and counting lemmas used in the construction of the preliminary layers
(Tointon, *Approximate subgroups of residually nilpotent groups*, Proposition 3.1):

* `NormalIn H C`: `H` is normalised by every element of `C`;
* `Tointon.trapSubgroup`: the relative form of Tointon's Lemma 3.2 — if `P³ ∩ W ⊆ P H`, then
  `P H ∩ W` is a subgroup normalised by `C = ⟨P⟩ H`;
* `Tointon.relSeries`: the lower central series of `C` relative to a normal subgroup `H`;
* `Tointon.card_le_centralizer_mod`: a large piece of `A²` centralises an element modulo a
  trapped subgroup (a variant of Tointon's Lemma 2.6 adapted to this setting).
-/

@[expose] public section

open scoped Pointwise
open scoped commutatorElement

namespace Tointon

variable {G : Type*} [Group G]

/-- `H` is normalised by every element of `C`. -/
def NormalIn (H C : Subgroup G) : Prop := ∀ c ∈ C, ∀ h ∈ H, c * h * c⁻¹ ∈ H

lemma NormalIn.mono {H C C' : Subgroup G} (h : NormalIn H C) (hC : C' ≤ C) : NormalIn H C' :=
  fun c hc => h c (hC hc)

lemma normalIn_sup {H₁ H₂ K C : Subgroup G} (h₁ : ∀ c ∈ C, ∀ h ∈ H₁, c * h * c⁻¹ ∈ K)
    (h₂ : ∀ c ∈ C, ∀ h ∈ H₂, c * h * c⁻¹ ∈ K) (hK : K = H₁ ⊔ H₂) : NormalIn K C := by
  intro c hc x hx
  have : H₁ ⊔ H₂ ≤ K.comap (MulAut.conj c).toMonoidHom := by
    refine sup_le ?_ ?_
    · intro y hy; simpa [MulAut.conj_apply] using h₁ c hc y hy
    · intro y hy; simpa [MulAut.conj_apply] using h₂ c hc y hy
  rw [← hK] at this
  simpa [MulAut.conj_apply] using this hx

/-- A symmetric set whose elements normalise `X` generates a subgroup of the normaliser. -/
lemma closure_le_normalizer_of_conj {S : Set G} {X : Subgroup G} (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hconj : ∀ s ∈ S, ∀ x ∈ X, s * x * s⁻¹ ∈ X) :
    Subgroup.closure S ≤ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.closure_le]
  intro s hs
  rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hconj s hs x, fun h => ?_⟩
  have := hconj s⁻¹ (hS s hs) _ h
  simpa [mul_assoc] using this

lemma normalIn_of_le_normalizer {H C : Subgroup G}
    (h : C ≤ Subgroup.normalizer (H : Set G)) : NormalIn H C :=
  fun _ hc x hx => (Subgroup.mem_normalizer_iff.1 (h hc) x).1 hx

section Trap

variable {P : Set G} {H W C : Subgroup G}

/-- The relative form of Tointon's Lemma 3.2.  Let `P ⊆ C` be symmetric with `1 ∈ P`, let `H ≤ W`
be subgroups of `C` normalised by `C`, and suppose `P³ ∩ W ⊆ P H`.  Then `P H ∩ W` is a
subgroup. -/
def trapSubgroup (hP1 : (1 : G) ∈ P) (hPinv : P⁻¹ = P) (hPC : P ⊆ C) (hHW : H ≤ W)
    (hHn : NormalIn H C) (htrap : ∀ g ∈ P ^ 3, g ∈ W → g ∈ P * (H : Set G)) :
    Subgroup G where
  carrier := {g | g ∈ P * (H : Set G) ∧ g ∈ W}
  one_mem' := ⟨⟨1, hP1, 1, H.one_mem, one_mul 1⟩, W.one_mem⟩
  mul_mem' := by
    rintro x y ⟨⟨p, hp, h, hh, rfl⟩, hxW⟩ ⟨⟨p', hp', h', hh', rfl⟩, hyW⟩
    have hp'C : p' ∈ C := hPC hp'
    have hconj : p'⁻¹ * h * p' ∈ H := by
      simpa using hHn p'⁻¹ (C.inv_mem hp'C) h hh
    have hpp'W : p * p' ∈ W := by
      have e : p * p' = (p * h) * (p' * h') * h'⁻¹ * (p'⁻¹ * h * p')⁻¹ := by group
      rw [e]
      exact W.mul_mem (W.mul_mem (W.mul_mem hxW hyW) (W.inv_mem (hHW hh')))
        (W.inv_mem (hHW hconj))
    have hpp'3 : p * p' ∈ P ^ 3 := by
      have : (3 : ℕ) = 1 + 1 + 1 := rfl
      rw [this, pow_add, pow_add, pow_one]
      exact ⟨p * p', Set.mul_mem_mul hp hp', 1, hP1, mul_one _⟩
    obtain ⟨q, hq, k, hk, hqk⟩ := htrap _ hpp'3 hpp'W
    refine ⟨⟨q, hq, k * (p'⁻¹ * h * p') * h', H.mul_mem (H.mul_mem hk hconj) hh', ?_⟩,
      W.mul_mem hxW hyW⟩
    have e : p * h * (p' * h') = (p * p') * (p'⁻¹ * h * p') * h' := by group
    rw [e, ← hqk]; simp only [mul_assoc]
  inv_mem' := by
    rintro x ⟨⟨p, hp, h, hh, rfl⟩, hxW⟩
    refine ⟨⟨p⁻¹, ?_, p * h⁻¹ * p⁻¹, hHn p (hPC hp) _ (H.inv_mem hh), by group⟩, W.inv_mem hxW⟩
    rw [← hPinv]; simpa using hp

variable (hP1 : (1 : G) ∈ P) (hPinv : P⁻¹ = P) (hPC : P ⊆ C) (hHW : H ≤ W)
    (hHn : NormalIn H C) (htrap : ∀ g ∈ P ^ 3, g ∈ W → g ∈ P * (H : Set G))

lemma mem_trapSubgroup {g : G} :
    g ∈ trapSubgroup hP1 hPinv hPC hHW hHn htrap ↔ g ∈ P * (H : Set G) ∧ g ∈ W := Iff.rfl

include htrap in
/-- The trapped subgroup is normalised by `C = ⟨P⟩ H`. -/
lemma normalIn_trapSubgroup (hWC : W ≤ C) (hWn : NormalIn W C) (hgen : C ≤ Subgroup.closure P ⊔ H) :
    NormalIn (trapSubgroup hP1 hPinv hPC hHW hHn htrap) C := by
  set X := trapSubgroup hP1 hPinv hPC hHW hHn htrap
  apply normalIn_of_le_normalizer
  refine hgen.trans (sup_le ?_ ?_)
  · apply closure_le_normalizer_of_conj
    · intro s hs; rw [← hPinv]; simpa using hs
    · rintro q hq x ⟨⟨p, hp, h, hh, rfl⟩, hxW⟩
      have hqC : q ∈ C := hPC hq
      have hxW' : q * (p * h) * q⁻¹ ∈ W := hWn q hqC _ hxW
      have hqh : q * h * q⁻¹ ∈ H := hHn q hqC h hh
      have hqpW : q * p * q⁻¹ ∈ W := by
        have e : q * p * q⁻¹ = q * (p * h) * q⁻¹ * (q * h * q⁻¹)⁻¹ := by group
        rw [e]; exact W.mul_mem hxW' (W.inv_mem (hHW hqh))
      have hqp3 : q * p * q⁻¹ ∈ P ^ 3 := by
        have hqinv : q⁻¹ ∈ P := by rw [← hPinv]; simpa using hq
        have : (3 : ℕ) = 1 + 1 + 1 := rfl
        rw [this, pow_add, pow_add, pow_one]
        exact Set.mul_mem_mul (Set.mul_mem_mul hq hp) hqinv
      obtain ⟨p'', hp'', h'', hh'', he⟩ := htrap _ hqp3 hqpW
      refine ⟨⟨p'', hp'', h'' * (q * h * q⁻¹), H.mul_mem hh'' hqh, ?_⟩, hxW'⟩
      have e : q * (p * h) * q⁻¹ = (q * p * q⁻¹) * (q * h * q⁻¹) := by group
      rw [e, ← he]; simp only [mul_assoc]
  · intro h₀ hh₀
    rw [Subgroup.mem_normalizer_iff]
    have fwd : ∀ k ∈ H, ∀ x ∈ X, k * x * k⁻¹ ∈ X := by
      rintro k hk x ⟨⟨p, hp, h, hh, rfl⟩, hxW⟩
      have hkC : k ∈ C := hWC (hHW hk)
      have hpC : p ∈ C := hPC hp
      refine ⟨⟨p, hp, (p⁻¹ * k * p) * h * k⁻¹, ?_, by group⟩, hWn k hkC _ hxW⟩
      refine H.mul_mem (H.mul_mem ?_ hh) (H.inv_mem hk)
      simpa using hHn p⁻¹ (C.inv_mem hpC) k hk
    intro x
    refine ⟨fwd h₀ hh₀ x, fun hx => ?_⟩
    have := fwd h₀⁻¹ (H.inv_mem hh₀) _ hx
    simpa [mul_assoc] using this

end Trap

section RelSeries

/-- The lower central series of `C` relative to `H`: `W₀ = C`, `W_{l+1} = [W_l, C] H`. -/
def relSeries (C H : Subgroup G) : ℕ → Subgroup G
  | 0 => C
  | l + 1 => ⁅relSeries C H l, C⁆ ⊔ H

variable {C H : Subgroup G}

lemma relSeries_le (hHC : H ≤ C) : ∀ l, relSeries C H l ≤ C
  | 0 => le_rfl
  | l + 1 => by
    refine sup_le ?_ hHC
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have := relSeries_le hHC l ha
    rw [commutatorElement_def]
    exact C.mul_mem (C.mul_mem (C.mul_mem this hb) (C.inv_mem this)) (C.inv_mem hb)

lemma le_relSeries (hHC : H ≤ C) : ∀ l, H ≤ relSeries C H l
  | 0 => hHC
  | _ + 1 => le_sup_right

lemma commutator_mem_relSeries {l : ℕ} {w c : G} (hw : w ∈ relSeries C H l) (hc : c ∈ C) :
    ⁅w, c⁆ ∈ relSeries C H (l + 1) :=
  Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hw hc)

lemma normalIn_relSeries (hHn : NormalIn H C) : ∀ l, NormalIn (relSeries C H l) C
  | 0 => fun c hc x hx => C.mul_mem (C.mul_mem hc hx) (C.inv_mem hc)
  | l + 1 => by
    refine normalIn_sup ?_ ?_ rfl
    · intro c hc x hx
      apply Subgroup.mem_sup_left
      have hsub : ⁅relSeries C H l, C⁆ ≤ (⁅relSeries C H l, C⁆).comap (MulAut.conj c).toMonoidHom := by
        rw [Subgroup.commutator_le]
        intro a ha b hb
        simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        have e : c * ⁅a, b⁆ * c⁻¹ = ⁅c * a * c⁻¹, c * b * c⁻¹⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact Subgroup.commutator_mem_commutator (normalIn_relSeries hHn l c hc a ha)
          (C.mul_mem (C.mul_mem hc hb) (C.inv_mem hc))
      simpa [MulAut.conj_apply] using hsub hx
    · intro c hc x hx
      exact Subgroup.mem_sup_right (hHn c hc x hx)

/-- The relative series is dominated by `H ⊔ γ_l(G)`. -/
lemma relSeries_le_sup_lcs (hHC : H ≤ C) (hHn : NormalIn H C) :
    ∀ l, relSeries C H l ≤ H ⊔ (⊤ : Subgroup G).lowerCentralSeries l
  | 0 => by simp
  | l + 1 => by
    refine sup_le ?_ le_sup_left
    rw [Subgroup.commutator_le]
    intro w hw c hc
    have hw' := relSeries_le_sup_lcs hHC hHn l hw
    have hmem : w ∈ ((H ⊔ (⊤ : Subgroup G).lowerCentralSeries l : Subgroup G) : Set G) := hw'
    rw [Subgroup.mul_normal] at hmem
    obtain ⟨h, hh, x, hx, rfl⟩ := hmem
    have e : ⁅h * x, c⁆ = (h * ⁅x, c⁆ * h⁻¹) * ⁅h, c⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_right ?_) (Subgroup.mem_sup_left ?_)
    · have hxc : ⁅x, c⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries (l + 1) := by
        rw [Subgroup.lowerCentralSeries_succ]
        exact Subgroup.commutator_mem_commutator hx trivial
      exact (inferInstance : ((⊤ : Subgroup G).lowerCentralSeries (l + 1)).Normal).conj_mem _ hxc h
    · have e2 : ⁅h, c⁆ = h * (c * h⁻¹ * c⁻¹) := by simp only [commutatorElement_def]; group
      rw [e2]
      exact H.mul_mem hh (hHn c hc _ (H.inv_mem hh))

lemma exists_relSeries_le [Group.IsNilpotent G] (hHC : H ≤ C) (hHn : NormalIn H C) :
    ∃ s, relSeries C H s ≤ H := by
  obtain ⟨s, hs⟩ := nilpotent_iff_lowerCentralSeries.1 (inferInstance : Group.IsNilpotent G)
  refine ⟨s, (relSeries_le_sup_lcs hHC hHn s).trans ?_⟩
  rw [hs, sup_bot_eq]

end RelSeries

section Counting

variable [Finite G]

lemma ncard_le_card_mul_ncard {F : Finset G} {X Y : Set G} (h : X ⊆ (F : Set G) * Y) :
    X.ncard ≤ F.card * Y.ncard := by
  classical
  have hY : Y = ((Set.toFinite Y).toFinset : Set G) := (Set.Finite.coe_toFinset _).symm
  rw [hY, ← Finset.coe_mul] at h
  calc X.ncard ≤ ((F * (Set.toFinite Y).toFinset : Finset G) : Set G).ncard :=
        Set.ncard_le_ncard h (Finset.finite_toSet _)
    _ = (F * (Set.toFinite Y).toFinset).card := Set.ncard_coe_finset _
    _ ≤ F.card * (Set.toFinite Y).toFinset.card := Finset.card_mul_le
    _ = F.card * Y.ncard := by rw [Set.ncard_eq_toFinset_card Y]

omit [Finite G] in
/-- Tointon's Lemma 2.2: `A^m ∩ W` is covered by `κ^(m-1)` left translates of `A² ∩ W`. -/
lemma exists_cover_pow_inter {κ : ℕ} {A : Set G} (hA : IsApproximateSubgroup (κ : ℝ) A)
    (W : Subgroup G) {m : ℕ} (hm : 2 ≤ m) :
    ∃ F : Finset G, F.card ≤ κ ^ (m - 1) ∧ A ^ m ∩ W ⊆ (F : Set G) * (A ^ 2 ∩ W) := by
  obtain ⟨F, hF, hcov⟩ := hA.pow_inter_pow_covBySMul_sq_inter_sq
    (IsApproximateSubgroup.subgroup (H := W)) hm (le_refl 2)
  have hW2 : ((W : Set G)) ^ 2 = W := coe_set_pow (by norm_num) W
  rw [hW2] at hcov
  refine ⟨F, ?_, ?_⟩
  · have : (F.card : ℝ) ≤ (κ : ℝ) ^ (m - 1) := by simpa using hF
    exact_mod_cast this
  · simpa [smul_eq_mul] using hcov

/-- The elements of `C` whose commutator with `γ` lies in `D`: the preimage of the centraliser of
`γ` in `C / D`. -/
def centMod (C D : Subgroup G) (hDn : NormalIn D C) (γ : G) : Subgroup G where
  carrier := {g | g ∈ C ∧ ⁅γ, g⁆ ∈ D}
  one_mem' := ⟨C.one_mem, by simp [D.one_mem]⟩
  mul_mem' := by
    rintro g g' ⟨hg, hgD⟩ ⟨hg', hg'D⟩
    refine ⟨C.mul_mem hg hg', ?_⟩
    have e : ⁅γ, g * g'⁆ = ⁅γ, g⁆ * (g * ⁅γ, g'⁆ * g⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]; exact D.mul_mem hgD (hDn g hg _ hg'D)
  inv_mem' := by
    rintro g ⟨hg, hgD⟩
    refine ⟨C.inv_mem hg, ?_⟩
    have e : ⁅γ, g⁻¹⁆ = g⁻¹ * ⁅γ, g⁆⁻¹ * g⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]; exact hDn g⁻¹ (C.inv_mem hg) _ (D.inv_mem hgD)

omit [Finite G] in
lemma mem_centMod {C D : Subgroup G} {hDn : NormalIn D C} {γ g : G} :
    g ∈ centMod C D hDn γ ↔ g ∈ C ∧ ⁅γ, g⁆ ∈ D := Iff.rfl

/-- **A large centraliser modulo a trapped subgroup.**  Suppose `D` is normalised by `C`,
`W` satisfies `A² ∩ W ⊆ D`, and `γ ∈ A⁶ ∩ C` has `⁅γ, x⁆ ∈ W` for all `x ∈ A² ∩ C`.
Then `|A² ∩ C| ≤ κ¹⁸ |A² ∩ C'|`, where `C'` is the centraliser of `γ` modulo `D`. -/
theorem card_le_centMod {κ : ℕ} {A : Set G} (hA : IsApproximateSubgroup (κ : ℝ) A)
    {C D W : Subgroup G} (hDn : NormalIn D C) (hWD : A ^ 2 ∩ (W : Set G) ⊆ D)
    {γ : G} (hγ : γ ∈ A ^ 6) (hγW : ∀ x ∈ A ^ 2 ∩ (C : Set G), ⁅γ, x⁆ ∈ W) :
    (A ^ 2 ∩ (C : Set G)).ncard ≤ κ ^ 18 * (A ^ 2 ∩ (centMod C D hDn γ : Set G)).ncard := by
  classical
  set P := A ^ 2 ∩ (C : Set G) with hPdef
  set C' := centMod C D hDn γ with hC'
  obtain ⟨F, hFcard, hFcov⟩ := exists_cover_pow_inter hA W (m := 16) (by norm_num)
  have hpt : ∀ x, x ∈ P → ∃ f ∈ F, ∃ y ∈ A ^ 2 ∩ (W : Set G), ⁅γ, x⁆ = f * y := by
    intro x hx
    have h16 : ⁅γ, x⁆ ∈ A ^ 16 := commutator_mem_pow hA.inv_eq_self hγ hx.1
    obtain ⟨f, hf, y, hy, he⟩ := hFcov ⟨h16, hγW x hx⟩
    exact ⟨f, hf, y, hy, he.symm⟩
  choose! f hfF y hy hxy using hpt
  set Pf := (Set.toFinite P).toFinset with hPf
  have hmaps : Set.MapsTo f (Pf : Set G) (F : Set G) := by
    intro x hx
    rw [hPf, Set.Finite.coe_toFinset] at hx
    exact hfF x hx
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  have hPcard : P.ncard = Pf.card := Set.ncard_eq_toFinset_card P
  -- the fibre bound
  have hfib : ∀ b ∈ F, (Pf.filter fun x => f x = b).card ≤
      (A ^ 4 ∩ (C' : Set G)).ncard := by
    intro b hb
    set X := Pf.filter fun x => f x = b
    rcases X.eq_empty_or_nonempty with hX | ⟨a, ha⟩
    · rw [hX]; simp
    · have haP : a ∈ P := by
        have := (Finset.mem_filter.1 ha).1
        rwa [hPf, Set.Finite.mem_toFinset] at this
      have hfa : f a = b := (Finset.mem_filter.1 ha).2
      have hinj : Set.InjOn (fun x => a⁻¹ * x) (X : Set G) := by
        intro x _ x' _ h; simpa using h
      have hmapsX : Set.MapsTo (fun x => a⁻¹ * x) (X : Set G) (A ^ 4 ∩ (C' : Set G)) := by
        intro x hx
        have hxP : x ∈ P := by
          have := (Finset.mem_filter.1 hx).1
          rwa [hPf, Set.Finite.mem_toFinset] at this
        have hfx : f x = b := (Finset.mem_filter.1 hx).2
        have haC : a ∈ C := haP.2
        have hxC : x ∈ C := hxP.2
        refine ⟨?_, C.mul_mem (C.inv_mem haC) hxC, ?_⟩
        · have hainv : a⁻¹ ∈ A ^ 2 := by
            rw [← inv_pow_eq_self hA.inv_eq_self 2]; simpa using haP.1
          have : (4 : ℕ) = 2 + 2 := rfl
          rw [this, pow_add]
          exact Set.mul_mem_mul hainv hxP.1
        · have e : ⁅γ, a⁻¹ * x⁆ = a⁻¹ * (⁅γ, a⁆⁻¹ * ⁅γ, x⁆) * a⁻¹⁻¹ := by
            simp only [commutatorElement_def]; group
          rw [e]
          refine hDn a⁻¹ (C.inv_mem haC) _ ?_
          rw [hxy a haP, hxy x hxP, hfa, hfx]
          have hya := hWD (hy a haP)
          have hyx := hWD (hy x hxP)
          have e2 : (b * y a)⁻¹ * (b * y x) = (y a)⁻¹ * y x := by group
          rw [e2]
          exact D.mul_mem (D.inv_mem hya) hyx
      calc X.card = (X : Set G).ncard := (Set.ncard_coe_finset X).symm
        _ = ((fun x => a⁻¹ * x) '' (X : Set G)).ncard := hinj.ncard_image.symm
        _ ≤ (A ^ 4 ∩ (C' : Set G)).ncard :=
          Set.ncard_le_ncard (Set.image_subset_iff.2 hmapsX) (Set.toFinite _)
  -- covering `A⁴ ∩ C'` by translates of `A² ∩ C'`
  obtain ⟨F', hF'card, hF'cov⟩ := exists_cover_pow_inter hA C' (m := 4) (by norm_num)
  have h4 := ncard_le_card_mul_ncard hF'cov
  calc P.ncard = Pf.card := hPcard
    _ = ∑ b ∈ F, (Pf.filter fun x => f x = b).card := hsum
    _ ≤ ∑ _b ∈ F, (A ^ 4 ∩ (C' : Set G)).ncard := Finset.sum_le_sum hfib
    _ = F.card * (A ^ 4 ∩ (C' : Set G)).ncard := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ κ ^ 15 * (F'.card * (A ^ 2 ∩ (C' : Set G)).ncard) := Nat.mul_le_mul hFcard h4
    _ ≤ κ ^ 15 * (κ ^ 3 * (A ^ 2 ∩ (C' : Set G)).ncard) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hF'card)
    _ = κ ^ 18 * (A ^ 2 ∩ (C' : Set G)).ncard := by ring

end Counting

end Tointon
