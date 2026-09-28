module
public import Mathlib

/-!
# Green–Ruzsa, basic additive combinatorics

Iterated sumsets `ksum k A`, additive approximate groups `AddApprox κ A`, normalized Freiman
isomorphisms `IsFIso s A φ` (given by tuples indexed by `Fin s`), the transport of approximate
group coverings through Freiman `3`-isomorphisms, polynomial growth of abelian approximate groups,
and the local Freiman `2`-isomorphism on fourfold sumsets induced by a Freiman `8`-isomorphism.
-/

@[expose] public section

open scoped Pointwise
open Finset

namespace GreenRuzsa

variable {G G' G'' : Type*} [AddCommGroup G] [AddCommGroup G'] [AddCommGroup G'']

/-- The `k`-fold sumset `A + ⋯ + A`. -/
noncomputable def ksum [DecidableEq G] (k : ℕ) (A : Finset G) : Finset G :=
  (Fintype.piFinset fun _ : Fin k => A).image fun a => ∑ i, a i

lemma mem_ksum [DecidableEq G] {k : ℕ} {A : Finset G} {x : G} :
    x ∈ ksum k A ↔ ∃ a : Fin k → G, (∀ i, a i ∈ A) ∧ ∑ i, a i = x := by
  simp [ksum]

lemma sum_mem_ksum [DecidableEq G] {k : ℕ} {A : Finset G} (a : Fin k → G) (ha : ∀ i, a i ∈ A) :
    ∑ i, a i ∈ ksum k A := mem_ksum.2 ⟨a, ha, rfl⟩

lemma mem_ksum_two [DecidableEq G] {A : Finset G} {x : G} :
    x ∈ ksum 2 A ↔ ∃ a ∈ A, ∃ b ∈ A, a + b = x := by
  rw [mem_ksum]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a 0, ha 0, a 1, ha 1, by simp [Fin.sum_univ_two]⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨![a, b], by simp [Fin.forall_fin_two, ha, hb], by simp [Fin.sum_univ_two]⟩

lemma mem_ksum_one [DecidableEq G] {A : Finset G} {x : G} : x ∈ ksum 1 A ↔ x ∈ A := by
  rw [mem_ksum]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa using ha 0
  · intro hx
    exact ⟨fun _ => x, fun _ => hx, by simp⟩

/-- `k (m A) ⊆ (k m) A`. -/
lemma ksum_ksum_subset [DecidableEq G] (A : Finset G) (n k : ℕ) :
    ksum n (ksum k A) ⊆ ksum (n * k) A := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := mem_ksum.1 hx
  choose b hb hbs using fun i => mem_ksum.1 (ha i)
  rw [mem_ksum]
  refine ⟨fun j => b (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2, fun j => hb _ _, ?_⟩
  rw [Fintype.sum_equiv finProdFinEquiv.symm _ (fun p => b p.1 p.2) (fun _ => rfl),
    Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => hbs i

/-- An additive approximate group, with an integer covering constant `κ`. -/
structure AddApprox (κ : ℕ) (A : Finset G) : Prop where
  zero_mem : (0 : G) ∈ A
  neg_mem : ∀ a ∈ A, -a ∈ A
  cover : ∃ X : Finset G, X.card ≤ κ ∧ ∀ a ∈ A, ∀ b ∈ A, ∃ x ∈ X, ∃ c ∈ A, a + b = x + c

/-- A (not necessarily normalized) Freiman `s`-isomorphism from `A` onto its image. -/
def IsFIso (s : ℕ) (A : Finset G) (φ : G → G') : Prop :=
  ∀ a b : Fin s → G, (∀ i, a i ∈ A) → (∀ i, b i ∈ A) →
    (∑ i, φ (a i) = ∑ i, φ (b i) ↔ ∑ i, a i = ∑ i, b i)

section FIso

variable {s : ℕ} {A : Finset G} {φ : G → G'}

/-- Padding with zeros: an `s`-isomorphism is a `k`-isomorphism for `k ≤ s`. -/
lemma IsFIso.mono (h : IsFIso s A φ) {k : ℕ} (hks : k ≤ s) (h0 : (0 : G) ∈ A)
    (hφ0 : φ 0 = 0) : IsFIso k A φ := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hks
  intro a b ha hb
  have hmem : ∀ c : Fin k → G, (∀ i, c i ∈ A) →
      ∀ i, Fin.append c (fun _ : Fin r => (0 : G)) i ∈ A := by
    intro c hc i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [hc, h0]
  have := h _ _ (hmem a ha) (hmem b hb)
  simpa [Fin.sum_univ_add, hφ0] using this

lemma IsFIso.rel1 (h : IsFIso s A φ) (hs : 1 ≤ s) (h0 : (0 : G) ∈ A) (hφ0 : φ 0 = 0)
    {a b : G} (ha : a ∈ A) (hb : b ∈ A) : φ a = φ b ↔ a = b := by
  have := h.mono hs h0 hφ0 (fun _ => a) (fun _ => b) (fun _ => ha) (fun _ => hb)
  simpa using this

lemma IsFIso.injOn (h : IsFIso s A φ) (hs : 1 ≤ s) (h0 : (0 : G) ∈ A) (hφ0 : φ 0 = 0) :
    Set.InjOn φ A := fun _ ha _ hb hab => (h.rel1 hs h0 hφ0 ha hb).1 hab

lemma IsFIso.card_image [DecidableEq G'] (h : IsFIso s A φ) (hs : 1 ≤ s) (h0 : (0 : G) ∈ A)
    (hφ0 : φ 0 = 0) : (A.image φ).card = A.card :=
  Finset.card_image_of_injOn (h.injOn hs h0 hφ0)

lemma IsFIso.rel2 (h : IsFIso s A φ) (hs : 2 ≤ s) (h0 : (0 : G) ∈ A) (hφ0 : φ 0 = 0)
    {a b c d : G} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A) :
    φ a + φ b = φ c + φ d ↔ a + b = c + d := by
  have := h.mono hs h0 hφ0 ![a, b] ![c, d] (by simp [Fin.forall_fin_two, ha, hb])
    (by simp [Fin.forall_fin_two, hc, hd])
  simpa [Fin.sum_univ_two] using this

lemma IsFIso.rel3 (h : IsFIso s A φ) (hs : 3 ≤ s) (h0 : (0 : G) ∈ A) (hφ0 : φ 0 = 0)
    {a b c d e f : G} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A) (he : e ∈ A)
    (hf : f ∈ A) : φ a + φ b + φ c = φ d + φ e + φ f ↔ a + b + c = d + e + f := by
  have := h.mono hs h0 hφ0 ![a, b, c] ![d, e, f] (by simp [Fin.forall_fin_succ, ha, hb, hc])
    (by simp [Fin.forall_fin_succ, hd, he, hf])
  simpa [Fin.sum_univ_three] using this

lemma IsFIso.map_neg (h : IsFIso s A φ) (hs : 2 ≤ s) (h0 : (0 : G) ∈ A) (hφ0 : φ 0 = 0)
    {a : G} (ha : a ∈ A) (hna : -a ∈ A) : φ (-a) = -φ a := by
  have := (h.rel2 hs h0 hφ0 ha hna h0 h0).2 (by simp)
  rw [hφ0, add_zero] at this
  exact eq_neg_of_add_eq_zero_right this

lemma IsFIso.comp [DecidableEq G'] {c : G' → G''} (hφ : IsFIso s A φ)
    (hc : IsFIso s (A.image φ) c) : IsFIso s A (c ∘ φ) := by
  intro a b ha hb
  simp only [Function.comp]
  rw [hc (fun i => φ (a i)) (fun i => φ (b i)) (fun i => mem_image_of_mem _ (ha i))
    (fun i => mem_image_of_mem _ (hb i))]
  exact hφ a b ha hb

/-- A normalized Freiman `3`-isomorphism transports an approximate-group structure. -/
lemma AddApprox.image [DecidableEq G'] {κ : ℕ} (hA : AddApprox κ A) (h : IsFIso s A φ)
    (hs : 3 ≤ s) (hφ0 : φ 0 = 0) : AddApprox κ (A.image φ) := by
  have h0 := hA.zero_mem
  refine ⟨by simpa [hφ0] using mem_image_of_mem φ h0, ?_, ?_⟩
  · intro y hy
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hy
    rw [← h.map_neg (by omega) h0 hφ0 ha (hA.neg_mem a ha)]
    exact mem_image_of_mem _ (hA.neg_mem a ha)
  · classical
    obtain ⟨X, hXcard, hX⟩ := hA.cover
    let P : G → Prop := fun x => ∃ b : Fin 3 → G, (∀ i, b i ∈ A) ∧ x = b 0 + b 1 - b 2
    let rep : G → G' := fun x =>
      if hx : P x then φ (hx.choose 0) + φ (hx.choose 1) - φ (hx.choose 2) else 0
    refine ⟨X.image rep, (card_image_le).trans hXcard, ?_⟩
    intro y₁ hy₁ y₂ hy₂
    obtain ⟨a₁, ha₁, rfl⟩ := mem_image.1 hy₁
    obtain ⟨a₂, ha₂, rfl⟩ := mem_image.1 hy₂
    obtain ⟨x, hx, a₃, ha₃, hrel⟩ := hX a₁ ha₁ a₂ ha₂
    have hP : P x := ⟨![a₁, a₂, a₃], by simp [Fin.forall_fin_succ, ha₁, ha₂, ha₃],
      by simp [hrel]⟩
    refine ⟨rep x, mem_image_of_mem _ hx, φ a₃, mem_image_of_mem _ ha₃, ?_⟩
    have hb := hP.choose_spec
    set b := hP.choose
    have hrep : rep x = φ (b 0) + φ (b 1) - φ (b 2) := by simp only [rep, dif_pos hP, b]
    have key : φ a₁ + φ a₂ + φ (b 2) = φ (b 0) + φ (b 1) + φ a₃ := by
      rw [h.rel3 hs h0 hφ0 ha₁ ha₂ (hb.1 2) (hb.1 0) (hb.1 1) ha₃]
      have := hb.2
      linear_combination (norm := abel) hrel + this
    rw [hrep]
    linear_combination (norm := abel) key

end FIso

section Growth

variable [DecidableEq G]

lemma ksum_repr {A : Finset G} {X : Finset G}
    (hX : ∀ a ∈ A, ∀ b ∈ A, ∃ x ∈ X, ∃ c ∈ A, a + b = x + c) :
    ∀ m : ℕ, ∀ y ∈ ksum (m + 1) A, ∃ a ∈ A, ∃ c : X → ℕ, (∑ x, c x ≤ m) ∧
      y = a + ∑ x, c x • (x : G) := by
  intro m
  induction m with
  | zero =>
    intro y hy
    rw [mem_ksum_one] at hy
    exact ⟨y, hy, 0, by simp, by simp⟩
  | succ m ih =>
    intro y hy
    obtain ⟨a, ha, rfl⟩ := mem_ksum.1 hy
    rw [Fin.sum_univ_castSucc]
    obtain ⟨a', ha', c, hc, hceq⟩ :=
      ih _ (sum_mem_ksum (fun i => a (Fin.castSucc i)) fun i => ha _)
    obtain ⟨x, hx, a'', ha'', hrel⟩ := hX a' ha' _ (ha (Fin.last _))
    refine ⟨a'', ha'', c + Pi.single ⟨x, hx⟩ 1, ?_, ?_⟩
    · simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
        if_true]
      omega
    · rw [hceq]
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      have : ∑ z : X, (Pi.single (⟨x, hx⟩ : X) 1 : X → ℕ) z • (z : G) = x := by
        rw [Finset.sum_eq_single (⟨x, hx⟩ : X)]
        · simp
        · intro b _ hb
          simp [hb]
        · simp
      rw [this]
      linear_combination (norm := abel) hrel

/-- **Polynomial growth.** `|mA| ≤ m^κ |A|` for an abelian `κ`-approximate group. -/
lemma AddApprox.card_ksum_le {κ : ℕ} {A : Finset G} (hA : AddApprox κ A) (m : ℕ) (hm : 1 ≤ m) :
    (ksum m A).card ≤ m ^ κ * A.card := by
  obtain ⟨X, hXcard, hX⟩ := hA.cover
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hm
  have hsub : ksum (m + 1) A ⊆
      (A ×ˢ Fintype.piFinset (fun _ : X => Finset.range (m + 1))).image
        (fun p => p.1 + ∑ x : X, p.2 x • (x : G)) := by
    intro y hy
    obtain ⟨a, ha, c, hc, rfl⟩ := ksum_repr hX m y hy
    refine mem_image.2 ⟨(a, c), ?_, rfl⟩
    simp only [mem_product, Fintype.mem_piFinset, mem_range]
    refine ⟨ha, fun x => ?_⟩
    have := Finset.single_le_sum (f := c) (fun _ _ => Nat.zero_le _) (mem_univ x)
    omega
  calc (ksum (m + 1) A).card ≤ _ := card_le_card hsub
    _ ≤ _ := card_image_le
    _ = A.card * (m + 1) ^ X.card := by simp [card_product]
    _ ≤ (m + 1) ^ κ * A.card := by
        rw [mul_comm]
        exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) hXcard)

lemma AddApprox.card_ksum_two_le {κ : ℕ} {A : Finset G} (hA : AddApprox κ A) :
    (ksum 2 A).card ≤ κ * A.card := by
  obtain ⟨X, hXcard, hX⟩ := hA.cover
  have : ksum 2 A ⊆ (X ×ˢ A).image (fun p => p.1 + p.2) := by
    intro y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_ksum_two.1 hy
    obtain ⟨x, hx, c, hc, hrel⟩ := hX a ha b hb
    exact mem_image.2 ⟨(x, c), mem_product.2 ⟨hx, hc⟩, hrel.symm⟩
  calc (ksum 2 A).card ≤ _ := card_le_card this
    _ ≤ _ := card_image_le
    _ = X.card * A.card := card_product _ _
    _ ≤ κ * A.card := Nat.mul_le_mul_right _ hXcard

lemma subset_ksum_two {A : Finset G} (h0 : (0 : G) ∈ A) : A ⊆ ksum 2 A := fun a ha =>
  mem_ksum_two.2 ⟨a, ha, 0, h0, add_zero a⟩

end Growth

section Extension

/-! ### The local `2`-isomorphism on fourfold sumsets -/

variable [DecidableEq G] [DecidableEq G'] {A : Finset G} {φ : G → G'}

omit [AddCommGroup G] [DecidableEq G] in
lemma mem_ksum_image {k : ℕ} {y : G'} :
    y ∈ ksum k (A.image φ) ↔ ∃ a : Fin k → G, (∀ i, a i ∈ A) ∧ ∑ i, φ (a i) = y := by
  rw [mem_ksum]
  constructor
  · rintro ⟨b, hb, rfl⟩
    choose a ha hab using fun i => mem_image.1 (hb i)
    exact ⟨a, ha, by simp [hab]⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨fun i => φ (a i), fun i => mem_image_of_mem _ (ha i), rfl⟩

open Classical in
/-- The inverse map `4 φ(A) → 4 A` induced by a Freiman isomorphism `φ`. -/
noncomputable def invExt (A : Finset G) (φ : G → G') (y : G') : G :=
  if h : ∃ a : Fin 4 → G, (∀ i, a i ∈ A) ∧ ∑ i, φ (a i) = y then ∑ i, h.choose i else 0

variable (h8 : IsFIso 8 A φ) (h0 : (0 : G) ∈ A) (hφ0 : φ 0 = 0)
include h8 h0 hφ0

omit [DecidableEq G] [DecidableEq G'] in
lemma invExt_spec (a : Fin 4 → G) (ha : ∀ i, a i ∈ A) :
    invExt A φ (∑ i, φ (a i)) = ∑ i, a i := by
  have hex : ∃ b : Fin 4 → G, (∀ i, b i ∈ A) ∧ ∑ i, φ (b i) = ∑ i, φ (a i) := ⟨a, ha, rfl⟩
  classical
  rw [invExt, dif_pos hex]
  exact ((h8.mono (by norm_num) h0 hφ0) _ _ hex.choose_spec.1 ha).1 hex.choose_spec.2

omit [DecidableEq G] [DecidableEq G'] in
lemma invExt_zero : invExt A φ 0 = 0 := by
  have := invExt_spec h8 h0 hφ0 (fun _ => 0) (fun _ => h0)
  simpa [hφ0] using this

lemma invExt_mem {y : G'} (hy : y ∈ ksum 4 (A.image φ)) : invExt A φ y ∈ ksum 4 A := by
  obtain ⟨a, ha, rfl⟩ := mem_ksum_image.1 hy
  rw [invExt_spec h8 h0 hφ0 a ha]
  exact sum_mem_ksum a ha

omit [DecidableEq G] in
lemma invExt_rel {y₁ y₂ y₃ y₄ : G'} (h₁ : y₁ ∈ ksum 4 (A.image φ))
    (h₂ : y₂ ∈ ksum 4 (A.image φ)) (h₃ : y₃ ∈ ksum 4 (A.image φ))
    (h₄ : y₄ ∈ ksum 4 (A.image φ)) :
    invExt A φ y₁ + invExt A φ y₂ = invExt A φ y₃ + invExt A φ y₄ ↔ y₁ + y₂ = y₃ + y₄ := by
  obtain ⟨a₁, ha₁, rfl⟩ := mem_ksum_image.1 h₁
  obtain ⟨a₂, ha₂, rfl⟩ := mem_ksum_image.1 h₂
  obtain ⟨a₃, ha₃, rfl⟩ := mem_ksum_image.1 h₃
  obtain ⟨a₄, ha₄, rfl⟩ := mem_ksum_image.1 h₄
  rw [invExt_spec h8 h0 hφ0 a₁ ha₁, invExt_spec h8 h0 hφ0 a₂ ha₂,
    invExt_spec h8 h0 hφ0 a₃ ha₃, invExt_spec h8 h0 hφ0 a₄ ha₄]
  have hm : ∀ b c : Fin 4 → G, (∀ i, b i ∈ A) → (∀ i, c i ∈ A) → ∀ i, Fin.append b c i ∈ A := by
    intro b c hb hc i
    exact Fin.addCases (fun i => by rw [Fin.append_left]; exact hb i)
      (fun i => by rw [Fin.append_right]; exact hc i) i
  have h8' : IsFIso (4 + 4) A φ := h8
  have := h8' (Fin.append a₁ a₂) (Fin.append a₃ a₄) (hm _ _ ha₁ ha₂) (hm _ _ ha₃ ha₄)
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right] at this
  exact this.symm

omit [DecidableEq G] in
lemma invExt_add {x y : G'} (hx : x ∈ ksum 4 (A.image φ)) (hy : y ∈ ksum 4 (A.image φ))
    (hxy : x + y ∈ ksum 4 (A.image φ)) :
    invExt A φ (x + y) = invExt A φ x + invExt A φ y := by
  have h0' : (0 : G') ∈ ksum 4 (A.image φ) :=
    mem_ksum_image.2 ⟨fun _ => 0, fun _ => h0, by simp [hφ0]⟩
  have := (invExt_rel h8 h0 hφ0 hx hy hxy h0').2 (by simp)
  rw [invExt_zero h8 h0 hφ0, add_zero] at this
  exact this.symm

omit [DecidableEq G] in
lemma invExt_neg {x : G'} (hx : x ∈ ksum 4 (A.image φ)) (hnx : -x ∈ ksum 4 (A.image φ)) :
    invExt A φ (-x) = -invExt A φ x := by
  have h0' : (0 : G') ∈ ksum 4 (A.image φ) :=
    mem_ksum_image.2 ⟨fun _ => 0, fun _ => h0, by simp [hφ0]⟩
  have := (invExt_rel h8 h0 hφ0 hx hnx h0' h0').2 (by simp)
  rw [invExt_zero h8 h0 hφ0, add_zero] at this
  exact eq_neg_of_add_eq_zero_right this

omit [DecidableEq G] in
lemma invExt_injOn : Set.InjOn (invExt A φ) (ksum 4 (A.image φ) : Set G') := by
  intro x hx y hy hxy
  have h0' : (0 : G') ∈ ksum 4 (A.image φ) :=
    mem_ksum_image.2 ⟨fun _ => 0, fun _ => h0, by simp [hφ0]⟩
  have := (invExt_rel h8 h0 hφ0 hx h0' hy h0').1 (by rw [hxy])
  simpa using this

end Extension

end GreenRuzsa
