module
public import Mathlib

/-!
# Sanders–Croot–Sisask theory (Section 5 of Breuillard–Green–Tao)

This file formalizes, for finite subsets of a (global) group, Section 5 of Breuillard, Green and
Tao, *The structure of approximate groups*:

* `Lovasz.IsBGTApproxGroup`: Definition 1.2 (approximate groups);
* `Lovasz.BGT.isBGTApproxGroup_sq_of_card_pow_five_le`: Corollary 5.2;
* `Lovasz.BGT.sanders_small_neighbourhoods`: Theorem 5.3 (Sanders' small neighbourhoods theorem);
* `Lovasz.BGT.exists_inter_inv_mul_large`: Lemma 5.8 / Corollary 5.9;
* `Lovasz.BGT.sanders_small_normal_neighbourhoods`: Theorem 5.6 (small normal neighbourhoods).
-/

@[expose] public section

open scoped Pointwise
open Finset MulOpposite

namespace Lovasz

/-- **Definition 1.2** of Breuillard–Green–Tao, for a set in a (global) group: a `K`-approximate
group is a finite set `A` containing the identity, symmetric, and such that `A · A ⊆ X · A` for some
symmetric set `X ⊆ A³` with `|X| ≤ K`. -/
def IsBGTApproxGroup {G : Type*} [Group G] (K : ℝ) (A : Set G) : Prop :=
  A.Finite ∧ 1 ∈ A ∧ A⁻¹ = A ∧
    ∃ X : Finset G, (X : Set G)⁻¹ = X ∧ (X : Set G) ⊆ A ^ 3 ∧ (X.card : ℝ) ≤ K ∧
      A * A ⊆ (X : Set G) * A

namespace BGT

variable {G : Type*} [Group G] [DecidableEq G]

/-! ### Overlaps of right translates -/

/-- The size of the overlap of `X` with its right translate by `g`. -/
def ov (X : Finset G) (g : G) : ℕ := #(X ∩ op g • X)

lemma ov_one (X : Finset G) : ov X 1 = #X := by simp [ov]

lemma ov_mul (X : Finset G) (g h : G) : ov X g + ov X h ≤ ov X (g * h) + #X := by
  set P := op h • (X ∩ op g • X) with hP
  set Q := X ∩ op h • X with hQ
  have hP' : P = op h • X ∩ op (g * h) • X := by
    rw [hP, smul_finset_inter, smul_smul, ← op_mul]
  have hPc : #P = ov X g := by rw [hP, card_smul_finset]; rfl
  have hU : P ∪ Q ⊆ op h • X := by
    rw [hP']
    exact union_subset inter_subset_left inter_subset_right
  have hI : P ∩ Q ⊆ X ∩ op (g * h) • X := by
    rw [hP', hQ]
    intro x hx
    simp only [mem_inter] at hx ⊢
    exact ⟨hx.2.1, hx.1.2⟩
  have h1 := card_union_add_card_inter P Q
  have h2 := card_le_card hU
  have h3 := card_le_card hI
  rw [card_smul_finset] at h2
  calc ov X g + ov X h = #P + #Q := by rw [hPc]; rfl
    _ ≤ #(X ∩ op (g * h) • X) + #X := by omega

lemma ov_pow (X S : Finset G) (δ : ℝ) (hS : ∀ s ∈ S, (1 - δ) * #X ≤ ov X s) (k : ℕ) :
    ∀ g ∈ S ^ k, (1 - k * δ) * #X ≤ ov X g := by
  induction k with
  | zero =>
    intro g hg
    rw [pow_zero, mem_one] at hg
    subst hg
    simp [ov_one]
  | succ k ih =>
    intro g hg
    rw [pow_succ] at hg
    obtain ⟨a, ha, s, hs, rfl⟩ := mem_mul.1 hg
    have h1 := ih a ha
    have h2 := hS s hs
    have h3 : ((ov X a : ℕ) : ℝ) + ov X s ≤ ov X (a * s) + #X := by
      exact_mod_cast ov_mul X a s
    push_cast
    nlinarith

lemma mem_inv_mul_of_ov_pos (X : Finset G) (g : G) (h : 0 < ov X g) : g ∈ X⁻¹ * X := by
  obtain ⟨x, hx⟩ := card_pos.1 h
  rw [mem_inter] at hx
  obtain ⟨y, hy, hyx⟩ := mem_smul_finset.1 hx.2
  rw [op_smul_eq_mul] at hyx
  exact mem_mul.2 ⟨y⁻¹, inv_mem_inv hy, x, hx.1, by rw [← hyx]; group⟩

/-! ### Powers of approximate groups -/

lemma card_pow_succ_le_of_approx {K : ℝ} {A : Finset G} (hA : IsBGTApproxGroup K (A : Set G))
    (n : ℕ) : (#(A ^ (n + 1)) : ℝ) ≤ K ^ n * #A := by
  obtain ⟨-, -, -, X, -, -, hXK, hcov⟩ := hA
  have hcov' : A * A ⊆ X * A := by
    rw [← coe_subset, coe_mul, coe_mul]; exact hcov
  have hsub : ∀ n : ℕ, A ^ (n + 1) ⊆ X ^ n * A := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc A ^ (n + 1 + 1) = A ^ (n + 1) * A := pow_succ _ _
        _ ⊆ X ^ n * A * A := mul_subset_mul_right ih
        _ = X ^ n * (A * A) := mul_assoc _ _ _
        _ ⊆ X ^ n * (X * A) := mul_subset_mul_left hcov'
        _ = X ^ (n + 1) * A := by rw [pow_succ, mul_assoc]
  have h1 : #(A ^ (n + 1)) ≤ #X ^ n * #A :=
    (card_le_card (hsub n)).trans (card_mul_le.trans (Nat.mul_le_mul_right _ card_pow_le))
  have h2 : ((#X : ℕ) : ℝ) ^ n ≤ K ^ n := pow_le_pow_left₀ (by positivity) hXK n
  calc (#(A ^ (n + 1)) : ℝ) ≤ (#X : ℝ) ^ n * #A := by exact_mod_cast h1
    _ ≤ K ^ n * #A := by gcongr

/-! ### The pigeonhole step -/

lemma exists_step (K δ : ℝ) (J : ℕ) (hδ1 : δ ≤ 1) (hJ : (1 - δ) ^ J * K < 1)
    (a : ℕ → ℝ) (lo : ℝ) (hlo : 0 < lo) (h0 : a 0 ≤ K * lo) (hlow : ∀ j, lo ≤ a j) :
    ∃ j < J, (1 - δ) * a j ≤ a (j + 1) := by
  by_contra hcon
  push_neg at hcon
  have key : ∀ j ≤ J, a j ≤ (1 - δ) ^ j * a 0 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro hj
      have hj' := ih (by omega)
      calc a (j + 1) ≤ (1 - δ) * a j := (hcon j (by omega)).le
        _ ≤ (1 - δ) * ((1 - δ) ^ j * a 0) := by gcongr
        _ = (1 - δ) ^ (j + 1) * a 0 := by ring
  have h1 := key J le_rfl
  have h2 := hlow J
  have hp : 0 ≤ (1 - δ) ^ J := pow_nonneg (by linarith) _
  have h3 : (1 - δ) ^ J * a 0 ≤ (1 - δ) ^ J * (K * lo) := mul_le_mul_of_nonneg_left h0 hp
  nlinarith

/-- The minimal size of `A B` over subsets `B ⊆ A` of density at least `t` (`|A| f(t)` in the
notation of the paper). -/
noncomputable def minDoubling (A : Finset G) (t : ℝ) : ℕ :=
  sInf {n | ∃ B ⊆ A, t * #A ≤ #B ∧ #(A * B) = n}

lemma minDoubling_spec (A : Finset G) {t : ℝ} (ht : t ≤ 1) :
    ∃ B ⊆ A, t * #A ≤ #B ∧ #(A * B) = minDoubling A t := by
  have hne : {n | ∃ B ⊆ A, t * #A ≤ #B ∧ #(A * B) = n}.Nonempty :=
    ⟨_, A, subset_rfl, by nlinarith [(Nat.cast_nonneg #A : (0 : ℝ) ≤ #A)], rfl⟩
  obtain ⟨B, hB, h1, h2⟩ := Nat.sInf_mem hne
  exact ⟨B, hB, h1, h2⟩

lemma minDoubling_le (A B : Finset G) {t : ℝ} (hB : B ⊆ A) (h : t * #A ≤ #B) :
    minDoubling A t ≤ #(A * B) :=
  Nat.sInf_le ⟨B, hB, h, rfl⟩

lemma card_le_minDoubling (A : Finset G) (hA : A.Nonempty) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    #A ≤ minDoubling A t := by
  obtain ⟨B, -, h1, h2⟩ := minDoubling_spec A ht1
  have hA' : (0 : ℝ) < #A := by exact_mod_cast hA.card_pos
  have hB : B.Nonempty := by
    rw [← card_pos]
    have : (0 : ℝ) < #B := by nlinarith
    exact_mod_cast this
  rw [← h2]
  exact card_le_card_mul_right hB

/-! ### The energy / Cauchy–Schwarz step -/

lemma exists_large_overlap (A B : Finset G) (hA : A.Nonempty) (hB : B ⊆ A) (K : ℝ)
    (hAA : (#(A * A) : ℝ) ≤ K * #A) :
    ∃ a₀ ∈ A, ((#B : ℝ)) ^ 2 ≤ K * ∑ a ∈ A, (#(op a • B ∩ op a₀ • B) : ℝ) := by
  set U := B * A with hU
  set f : G → G → ℝ := fun a x => if x ∈ op a • B then 1 else 0 with hf
  have hsub : ∀ a ∈ A, op a • B ⊆ U := by
    intro a ha x hx
    obtain ⟨b, hb, rfl⟩ := mem_smul_finset.1 hx
    rw [op_smul_eq_mul]
    exact mul_mem_mul hb ha
  have h1 : ∀ a ∈ A, ∀ a₀ ∈ A,
      (#(op a • B ∩ op a₀ • B) : ℝ) = ∑ x ∈ U, f a x * f a₀ x := by
    intro a ha a₀ _
    have : op a • B ∩ op a₀ • B = U.filter (fun x => x ∈ op a • B ∧ x ∈ op a₀ • B) := by
      ext x
      simp only [mem_inter, mem_filter]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨hsub a ha h1, h1, h2⟩
      · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩
    rw [this, natCast_card_filter]
    refine sum_congr rfl fun x _ => ?_
    simp only [hf]
    split_ifs <;> simp_all
  have h2 : ∀ a ∈ A, ∑ x ∈ U, f a x = #B := by
    intro a ha
    have : op a • B = U.filter (fun x => x ∈ op a • B) := by
      ext x
      simp only [mem_filter]
      exact ⟨fun h => ⟨hsub a ha h, h⟩, fun h => h.2⟩
    rw [← card_smul_finset (op a) B, this, natCast_card_filter]
  have hT : ∑ a₀ ∈ A, ∑ a ∈ A, (#(op a • B ∩ op a₀ • B) : ℝ) =
      ∑ x ∈ U, (∑ a ∈ A, f a x) ^ 2 := by
    calc ∑ a₀ ∈ A, ∑ a ∈ A, (#(op a • B ∩ op a₀ • B) : ℝ)
        = ∑ a₀ ∈ A, ∑ a ∈ A, ∑ x ∈ U, f a x * f a₀ x :=
          sum_congr rfl fun a₀ ha₀ => sum_congr rfl fun a ha => h1 a ha a₀ ha₀
      _ = ∑ a₀ ∈ A, ∑ x ∈ U, ∑ a ∈ A, f a x * f a₀ x :=
          sum_congr rfl fun _ _ => sum_comm
      _ = ∑ x ∈ U, ∑ a₀ ∈ A, ∑ a ∈ A, f a x * f a₀ x := sum_comm
      _ = ∑ x ∈ U, (∑ a ∈ A, f a x) ^ 2 := by
          refine sum_congr rfl fun x _ => ?_
          rw [sq, sum_mul_sum, sum_comm]
  have hS : ∑ x ∈ U, ∑ a ∈ A, f a x = #A * #B := by
    rw [sum_comm, sum_congr rfl h2, sum_const, nsmul_eq_mul]
  have hUcard : (#U : ℝ) ≤ K * #A := by
    have : U ⊆ A * A := mul_subset_mul_right hB
    exact le_trans (by exact_mod_cast card_le_card this) hAA
  have hCS := sq_sum_le_card_mul_sum_sq (s := U) (f := fun x => ∑ a ∈ A, f a x)
  rw [hS, ← hT] at hCS
  have hA' : (0 : ℝ) < #A := by exact_mod_cast hA.card_pos
  have hTnn : 0 ≤ ∑ a₀ ∈ A, ∑ a ∈ A, (#(op a • B ∩ op a₀ • B) : ℝ) :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => Nat.cast_nonneg _
  have key : ∑ _a₀ ∈ A, ((#B : ℝ)) ^ 2 ≤
      ∑ a₀ ∈ A, K * ∑ a ∈ A, (#(op a • B ∩ op a₀ • B) : ℝ) := by
    rw [sum_const, nsmul_eq_mul, ← mul_sum]
    have h3 : ((#A : ℝ) * #B) ^ 2 ≤ K * #A *
        ∑ a₀ ∈ A, ∑ a ∈ A, (#(op a • B ∩ op a₀ • B) : ℝ) :=
      hCS.trans (mul_le_mul_of_nonneg_right hUcard hTnn)
    have h4 : (#A : ℝ) * (#A * #B ^ 2) ≤
        (#A : ℝ) * (K * ∑ a₀ ∈ A, ∑ a ∈ A, (#(op a • B ∩ op a₀ • B) : ℝ)) := by
      nlinarith
    exact le_of_mul_le_mul_left h4 hA'
  obtain ⟨a₀, ha₀, h⟩ := exists_le_of_sum_le hA key
  exact ⟨a₀, ha₀, h⟩

/-- The core of the proof of Theorem 5.3, at a fixed density `t` at which the pigeonhole
condition (5.1) holds. -/
lemma sanders_step (A : Finset G) (hA1 : 1 ∈ A) (hAinv : A⁻¹ = A) (K : ℝ) (hK : 1 ≤ K)
    (hAA : (#(A * A) : ℝ) ≤ K * #A) (t δ : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hstep : (1 - δ) * minDoubling A t ≤ minDoubling A (t ^ 2 / (2 * K))) :
    ∃ S₀ : Finset G, 1 ∈ S₀ ∧ S₀⁻¹ = S₀ ∧ S₀ ⊆ A * A ∧ t ^ 2 / (2 * K) * #A ≤ #S₀ ∧
      ∀ k : ℕ, k * δ < 1 → S₀ ^ k ⊆ A * A * A * A := by
  have hA : A.Nonempty := ⟨1, hA1⟩
  have hA' : (0 : ℝ) < #A := by exact_mod_cast hA.card_pos
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = t ^ 2 / (2 * K) := ⟨_, rfl⟩
  rw [← hc] at hstep ⊢
  have hc0 : 0 < c := by rw [hc]; positivity
  have hct : c ≤ t := by
    rw [hc, div_le_iff₀ (by positivity)]; nlinarith
  obtain ⟨B, hBA, hBt, hBmin⟩ := minDoubling_spec A ht1
  obtain ⟨a₀, ha₀, hen⟩ := exists_large_overlap A B hA hBA K hAA
  set C := A.filter (fun a => c * #A ≤ #(op a • B ∩ op a₀ • B)) with hCdef
  have hBle : (#B : ℝ) ≤ #A := by exact_mod_cast card_le_card hBA
  -- the set `C` is large
  have hC : c * #A ≤ #C := by
    have hsplit := sum_filter_add_sum_filter_not A
      (fun a => c * #A ≤ #(op a • B ∩ op a₀ • B)) (fun a => (#(op a • B ∩ op a₀ • B) : ℝ))
    have hin : ∑ a ∈ C, (#(op a • B ∩ op a₀ • B) : ℝ) ≤ #C * #A := by
      rw [← nsmul_eq_mul, ← sum_const]
      refine sum_le_sum fun a _ => ?_
      have : #(op a • B ∩ op a₀ • B) ≤ #(op a • B) := card_le_card inter_subset_left
      rw [card_smul_finset] at this
      exact le_trans (by exact_mod_cast this) hBle
    have hout : ∑ a ∈ A.filter (fun a => ¬ c * #A ≤ #(op a • B ∩ op a₀ • B)),
        (#(op a • B ∩ op a₀ • B) : ℝ) ≤ #A * (c * #A) := by
      calc _ ≤ ∑ a ∈ A.filter (fun a => ¬ c * #A ≤ #(op a • B ∩ op a₀ • B)), c * #A :=
            sum_le_sum fun a ha => (not_le.1 (mem_filter.1 ha).2).le
        _ = #(A.filter (fun a => ¬ c * #A ≤ #(op a • B ∩ op a₀ • B))) * (c * #A) := by
            rw [sum_const, nsmul_eq_mul]
        _ ≤ #A * (c * #A) := by
            gcongr; exact filter_subset _ _
    have htot : ∑ a ∈ A, (#(op a • B ∩ op a₀ • B) : ℝ) ≤ #C * #A + #A * (c * #A) := by
      rw [← hsplit]; exact add_le_add hin hout
    have hB2 : (t * #A) ^ 2 ≤ (#B : ℝ) ^ 2 := by
      have : 0 ≤ t * #A := by positivity
      gcongr
    have h2c : t ^ 2 = 2 * K * c := by rw [hc]; field_simp
    have hmain : 2 * K * c * #A * #A ≤ K * (#C * #A + #A * (c * #A)) := by
      calc 2 * K * c * #A * #A = (t * #A) ^ 2 := by rw [mul_pow, h2c]; ring
        _ ≤ #B ^ 2 := hB2
        _ ≤ K * ∑ a ∈ A, (#(op a • B ∩ op a₀ • B) : ℝ) := hen
        _ ≤ K * (#C * #A + #A * (c * #A)) := by gcongr
    have hK0 : (0 : ℝ) < K := by linarith
    have : K * #A * (c * #A) ≤ K * #A * #C := by nlinarith
    exact le_of_mul_le_mul_left this (mul_pos hK0 hA')
  -- the set `S₀`
  set S₀ : Finset G := insert 1 (C.image (fun a => a₀ * a⁻¹) ∪ C.image (fun a => a * a₀⁻¹))
    with hS₀
  have hCA : C ⊆ A := filter_subset _ _
  have hinvA : ∀ a ∈ A, a⁻¹ ∈ A := by
    intro a ha; rw [← hAinv]; exact inv_mem_inv ha
  refine ⟨S₀, mem_insert_self _ _, ?_, ?_, ?_, ?_⟩
  · ext x
    simp only [S₀, mem_inv', mem_insert, mem_union, mem_image]
    constructor
    · rintro (h | ⟨a, ha, h⟩ | ⟨a, ha, h⟩)
      · left; simpa using h
      · right; right; exact ⟨a, ha, by rw [← inv_inv x, ← h]; group⟩
      · right; left; exact ⟨a, ha, by rw [← inv_inv x, ← h]; group⟩
    · rintro (h | ⟨a, ha, h⟩ | ⟨a, ha, h⟩)
      · left; simp [h]
      · right; right; exact ⟨a, ha, by rw [← h]; group⟩
      · right; left; exact ⟨a, ha, by rw [← h]; group⟩
  · intro x hx
    simp only [S₀, mem_insert, mem_union, mem_image] at hx
    rcases hx with rfl | ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
    · simpa using mul_mem_mul hA1 hA1
    · exact mul_mem_mul ha₀ (hinvA a (hCA ha))
    · exact mul_mem_mul (hCA ha) (hinvA a₀ ha₀)
  · have h1 : #(C.image (fun a => a₀ * a⁻¹)) = #C :=
      card_image_of_injective _ (fun a b hab => by simpa using hab)
    have h2 : C.image (fun a => a₀ * a⁻¹) ⊆ S₀ := fun x hx =>
      mem_insert_of_mem (mem_union_left _ hx)
    have h3 := card_le_card h2
    rw [h1] at h3
    exact hC.trans (by exact_mod_cast h3)
  · -- the overlap estimate for elements of `S₀`
    set X := A * B with hX
    have hBne : B.Nonempty := by
      rw [← card_pos]
      have : (0 : ℝ) < #B := lt_of_lt_of_le (by positivity) hBt
      exact_mod_cast this
    have hXne : X.Nonempty := hA.mul hBne
    have hX' : (0 : ℝ) < #X := by exact_mod_cast hXne.card_pos
    have hlarge : ∀ h ∈ S₀, c * #A ≤ #(B ∩ op h • B) := by
      intro h hh
      simp only [S₀, mem_insert, mem_union, mem_image] at hh
      rcases hh with rfl | ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
      · simp only [op_one, one_smul, inter_self]
        exact le_trans (mul_le_mul_of_nonneg_right hct hA'.le) hBt
      · have e : #(B ∩ op (a₀ * a⁻¹) • B) = #(op a • B ∩ op a₀ • B) := by
          rw [← card_smul_finset (op a), smul_finset_inter, smul_smul, ← op_mul]
          simp
        rw [e]; exact (mem_filter.1 ha).2
      · have e : #(B ∩ op (a * a₀⁻¹) • B) = #(op a • B ∩ op a₀ • B) := by
          rw [← card_smul_finset (op a₀), smul_finset_inter, smul_smul, ← op_mul, inter_comm]
          simp
        rw [e]; exact (mem_filter.1 ha).2
    have hov : ∀ h ∈ S₀, (1 - δ) * #X ≤ ov X h := by
      intro h hh
      have hD : B ∩ op h • B ⊆ A := inter_subset_left.trans hBA
      have hm := minDoubling_le A _ hD (hlarge h hh)
      have hsub : A * (B ∩ op h • B) ⊆ X ∩ op h • X := by
        intro x hx
        obtain ⟨a, ha, d, hd, rfl⟩ := mem_mul.1 hx
        rw [mem_inter] at hd
        obtain ⟨b, hb, rfl⟩ := mem_smul_finset.1 hd.2
        rw [mem_inter]
        refine ⟨mul_mem_mul ha hd.1, mem_smul_finset.2 ⟨a * b, mul_mem_mul ha hb, ?_⟩⟩
        simp [mul_assoc]
      have h1 : minDoubling A c ≤ ov X h := hm.trans (card_le_card hsub)
      calc (1 - δ) * (#X : ℝ) = (1 - δ) * minDoubling A t := by rw [hX, hBmin]
        _ ≤ minDoubling A c := hstep
        _ ≤ ov X h := by exact_mod_cast h1
    intro k hk g hg
    have h1 := ov_pow X S₀ δ hov k g hg
    have hpos : 0 < ov X g := by
      have : (0 : ℝ) < ov X g := lt_of_lt_of_le (by nlinarith) h1
      exact_mod_cast this
    have hmem := mem_inv_mul_of_ov_pos X g hpos
    have hXinv : X⁻¹ ⊆ A * A := by
      rw [hX, mul_inv_rev]
      refine mul_subset_mul ?_ (by rw [hAinv])
      calc B⁻¹ ⊆ A⁻¹ := inv_subset_inv hBA
        _ = A := hAinv
    have : X⁻¹ * X ⊆ A * A * A * A := by
      calc X⁻¹ * X ⊆ A * A * (A * A) := mul_subset_mul hXinv (mul_subset_mul_left hBA)
        _ = A * A * A * A := by rw [mul_assoc (A * A)]
    exact this hmem

end BGT

end Lovasz

namespace Lovasz.BGT

variable {G : Type*} [Group G] [DecidableEq G]

/-- **Corollary 5.2** of Breuillard–Green–Tao: if `A` is symmetric, contains the identity and
`|A⁵| ≤ L |A|`, then `A²` is a `2L`-approximate group. -/
lemma isBGTApproxGroup_sq_of_card_pow_five_le {A : Finset G} (hA1 : 1 ∈ A) (hAinv : A⁻¹ = A)
    {L : ℝ} (hL : (#(A ^ 5) : ℝ) ≤ L * #A) : IsBGTApproxGroup (2 * L) ((A ^ 2 : Finset G) : Set G) := by
  have hA : A.Nonempty := ⟨1, hA1⟩
  have hcov : (#(A ^ 4 * A) : ℝ) ≤ L * #A := by rw [← pow_succ]; exact hL
  obtain ⟨F, hFA, hFL, hAF⟩ := ruzsa_covering_mul hA hcov
  have hdiv : A / A = A ^ 2 := by rw [div_eq_mul_inv, hAinv, sq]
  rw [hdiv] at hAF
  have hpowinv : ∀ n : ℕ, (A ^ n)⁻¹ = A ^ n := fun n => by rw [← inv_pow, hAinv]
  refine ⟨finite_toSet _, ?_, ?_, F ∪ F⁻¹, ?_, ?_, ?_, ?_⟩
  · rw [mem_coe]; exact one_mem_pow hA1
  · rw [← coe_inv, hpowinv]
  · rw [coe_union, coe_inv, Set.union_inv, inv_inv, Set.union_comm]
  · rw [← coe_pow, coe_subset, ← pow_mul]
    refine union_subset ?_ ?_
    · exact hFA.trans (pow_subset_pow_right hA1 (by norm_num))
    · calc F⁻¹ ⊆ (A ^ 4)⁻¹ := inv_subset_inv hFA
        _ = A ^ 4 := hpowinv 4
        _ ⊆ A ^ (2 * 3) := pow_subset_pow_right hA1 (by norm_num)
  · have h1 : (#(F ∪ F⁻¹) : ℝ) ≤ #F + #F⁻¹ := by exact_mod_cast card_union_le _ _
    rw [card_inv] at h1
    linarith
  · rw [← coe_mul, ← coe_mul, coe_subset, ← pow_add]
    exact hAF.trans (mul_subset_mul_right subset_union_left)

/-- The sequence of densities used in the pigeonhole argument of Theorem 5.3. -/
noncomputable def tseq (K : ℝ) : ℕ → ℝ
  | 0 => 1
  | j + 1 => tseq K j ^ 2 / (2 * K)

lemma tseq_pos {K : ℝ} (hK : 0 < K) (j : ℕ) : 0 < tseq K j := by
  induction j with
  | zero => simp [tseq]
  | succ j ih => simp only [tseq]; positivity

lemma tseq_le_one {K : ℝ} (hK : 1 ≤ K) (j : ℕ) : tseq K j ≤ 1 := by
  induction j with
  | zero => simp [tseq]
  | succ j ih =>
    simp only [tseq]
    have h0 := tseq_pos (by linarith : (0 : ℝ) < K) j
    rw [div_le_one (by positivity)]
    nlinarith

lemma tseq_antitone {K : ℝ} (hK : 1 ≤ K) : Antitone (tseq K) := by
  refine antitone_nat_of_succ_le fun j => ?_
  simp only [tseq]
  have h0 := tseq_pos (by linarith : (0 : ℝ) < K) j
  have h1 := tseq_le_one hK j
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- **Theorem 5.3** of Breuillard–Green–Tao (Sanders' small neighbourhoods theorem), for global
approximate groups: for every `K ≥ 1` and `m` there are `K'` and `c > 0` such that for every
`K`-approximate group `A` there is a `K'`-approximate group `S` with `|S| ≥ c |A|` and
`S^m ⊆ A⁴`. -/
theorem sanders_small_neighbourhoods (K : ℝ) (hK : 1 ≤ K) (m : ℕ) :
    ∃ K' c : ℝ, 0 < c ∧ ∀ {G : Type*} [Group G] (A : Set G), IsBGTApproxGroup K A →
      ∃ S : Set G, IsBGTApproxGroup K' S ∧ c * A.ncard ≤ S.ncard ∧ S ^ m ⊆ A ^ 4 := by
  set δ : ℝ := 1 / (2 * m + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by rw [hδ, div_le_one (by positivity)]; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
  have hmδ : (2 * m : ℕ) * δ < 1 := by
    rw [hδ]; push_cast
    rw [mul_one_div, div_lt_one (by positivity)]; linarith
  have hK0 : (0 : ℝ) < K := by linarith
  obtain ⟨J, hJ⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hK0) (by linarith : 1 - δ < 1)
  have hJ' : (1 - δ) ^ J * K < 1 := by
    have := mul_lt_mul_of_pos_right hJ hK0
    rwa [inv_mul_cancel₀ hK0.ne'] at this
  set c := tseq K J with hc
  have hc0 : 0 < c := tseq_pos hK0 J
  refine ⟨2 * (K ^ 9 / c), c, hc0, ?_⟩
  intro G _ A hA
  classical
  obtain ⟨A', rfl⟩ := hA.1.exists_finset_coe
  have hA1 : 1 ∈ A' := hA.2.1
  have hAinv : A'⁻¹ = A' := by
    have := hA.2.2.1
    rw [← coe_inv, coe_inj] at this
    exact this
  have hAne : A'.Nonempty := ⟨1, hA1⟩
  have hA' : (0 : ℝ) < #A' := by exact_mod_cast hAne.card_pos
  have hAA : (#(A' * A') : ℝ) ≤ K * #A' := by
    have := card_pow_succ_le_of_approx hA 1
    rwa [pow_one, one_add_one_eq_two, sq] at this
  obtain ⟨j, hjJ, hj⟩ := exists_step K δ J hδ1 hJ' (fun j => (minDoubling A' (tseq K j) : ℝ))
    (#A' : ℝ) hA'
    (by
      have := minDoubling_le A' A' (t := tseq K 0) subset_rfl (by simp [tseq])
      exact le_trans (by exact_mod_cast this) hAA)
    (fun j => by
      exact_mod_cast card_le_minDoubling A' hAne (tseq_pos hK0 j) (tseq_le_one hK j))
  obtain ⟨S₀, hS1, hSinv, hSA, hScard, hSpow⟩ :=
    sanders_step A' hA1 hAinv K hK hAA (tseq K j) δ (tseq_pos hK0 j) (tseq_le_one hK j) hj
  have hcj : c ≤ tseq K j ^ 2 / (2 * K) := tseq_antitone hK (show j + 1 ≤ J by omega)
  have hS0c : c * #A' ≤ #S₀ := le_trans (mul_le_mul_of_nonneg_right hcj hA'.le) hScard
  have hS0le : S₀ ⊆ S₀ ^ 2 := by
    simpa using pow_subset_pow_right hS1 (show 1 ≤ 2 by norm_num)
  refine ⟨((S₀ ^ 2 : Finset G) : Set G), ?_, ?_, ?_⟩
  · apply isBGTApproxGroup_sq_of_card_pow_five_le hS1 hSinv
    have h1 : S₀ ^ 5 ⊆ A' ^ (9 + 1) := by
      calc S₀ ^ 5 ⊆ (A' * A') ^ 5 := pow_subset_pow_left hSA
        _ = A' ^ (9 + 1) := by rw [← sq, ← pow_mul]
    have h2 := card_pow_succ_le_of_approx hA 9
    calc (#(S₀ ^ 5) : ℝ) ≤ #(A' ^ (9 + 1)) := by exact_mod_cast card_le_card h1
      _ ≤ K ^ 9 * #A' := h2
      _ = K ^ 9 / c * (c * #A') := by field_simp
      _ ≤ K ^ 9 / c * #S₀ := by gcongr
  · rw [Set.ncard_coe_finset, Set.ncard_coe_finset]
    exact hS0c.trans (by exact_mod_cast card_le_card hS0le)
  · rw [← coe_pow, ← coe_pow, coe_subset, ← pow_mul]
    have := hSpow (2 * m) hmδ
    calc S₀ ^ (2 * m) ⊆ A' * A' * A' * A' := this
      _ = A' ^ 4 := by simp [pow_succ]

/-! ### Lemma 5.8 and Corollary 5.9 -/

/-- **Lemma 5.8** of Breuillard–Green–Tao, in a form not referring to an ambient approximate group:
for finite nonempty `P, Q` there is `B ⊆ Q` with `|P| |Q| ≤ |B| |P⁻¹ Q|` and
`B B⁻¹ ⊆ P P⁻¹ ∩ Q Q⁻¹`. -/
lemma exists_subset_mul_inv_subset (P Q : Finset G) (hP : P.Nonempty) (hQ : Q.Nonempty) :
    ∃ B ⊆ Q, (#P : ℝ) * #Q ≤ #B * #(P⁻¹ * Q) ∧ B * B⁻¹ ⊆ P * P⁻¹ ∧ B * B⁻¹ ⊆ Q * Q⁻¹ := by
  have hPQ : (P⁻¹ * Q).Nonempty := hP.inv.mul hQ
  have ht : (0 : ℝ) < #(P⁻¹ * Q) := by exact_mod_cast hPQ.card_pos
  obtain ⟨x, -, hfib⟩ := exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s := P ×ˢ Q) (t := P⁻¹ * Q) (f := fun pq => pq.1⁻¹ * pq.2)
    (fun pq hpq => by
      rw [mem_product] at hpq
      exact mul_mem_mul (inv_mem_inv hpq.1) hpq.2) hPQ
    (b := (#P * #Q : ℝ) / #(P⁻¹ * Q))
    (by rw [nsmul_eq_mul, mul_div_cancel₀ _ ht.ne', card_product]; push_cast; rfl)
  set B := Q.filter (fun q => q * x⁻¹ ∈ P) with hB
  have hfB : #((P ×ˢ Q).filter (fun pq => pq.1⁻¹ * pq.2 = x)) ≤ #B := by
    refine card_le_card_of_injOn (fun pq => pq.2) ?_ ?_
    · intro pq hpq
      simp only [coe_filter, mem_product, Set.mem_setOf_eq] at hpq
      simp only [hB, coe_filter, Set.mem_setOf_eq]
      refine ⟨hpq.1.2, ?_⟩
      rw [← hpq.2]; simpa using hpq.1.1
    · intro pq hpq pq' hpq' h
      simp only [coe_filter, mem_product, Set.mem_setOf_eq] at hpq hpq'
      simp only at h
      have : pq.1 = pq'.1 := by
        have e1 : pq.1 = pq.2 * x⁻¹ := by rw [← hpq.2]; group
        have e2 : pq'.1 = pq'.2 * x⁻¹ := by rw [← hpq'.2]; group
        rw [e1, e2, h]
      exact Prod.ext this h
  refine ⟨B, filter_subset _ _, ?_, ?_, ?_⟩
  · have h1 : (#P * #Q : ℝ) / #(P⁻¹ * Q) ≤ #B := hfib.trans (by exact_mod_cast hfB)
    rwa [div_le_iff₀ ht] at h1
  · intro z hz
    obtain ⟨b, hb, c, hc, rfl⟩ := mem_mul.1 hz
    rw [mem_inv'] at hc
    have hb' := (mem_filter.1 hb).2
    have hc' := (mem_filter.1 hc).2
    refine mem_mul.2 ⟨b * x⁻¹, hb', (c⁻¹ * x⁻¹)⁻¹, inv_mem_inv hc', ?_⟩
    group
  · exact mul_subset_mul (filter_subset _ _) (inv_subset_inv (filter_subset _ _))

/-- Conjugation of powers: if `g⁻¹ T g ⊆ U` then `g⁻¹ Tⁿ g ⊆ Uⁿ`. -/
lemma conj_mem_pow {T U : Finset G} {g : G} (h : ∀ t ∈ T, g⁻¹ * t * g ∈ U) (n : ℕ) :
    ∀ y ∈ T ^ n, g⁻¹ * y * g ∈ U ^ n := by
  induction n with
  | zero =>
    intro y hy
    rw [pow_zero, mem_one] at hy
    subst hy
    simp
  | succ n ih =>
    intro y hy
    rw [pow_succ] at hy ⊢
    obtain ⟨a, ha, t, ht, rfl⟩ := mem_mul.1 hy
    refine mem_mul.2 ⟨g⁻¹ * a * g, ih a ha, g⁻¹ * t * g, h t ht, ?_⟩
    group

/-- **Corollary 5.9** of Breuillard–Green–Tao (iterated Lemma 5.8), in a quantitative form: given
a base set `P₀` and sets `Q f` (`f ∈ F`) inside a common set `U` with `|U⁻¹ U| ≤ β N` and
`|Q f| ≥ α N`, there is `B ⊆ U` with `|B| ≥ (α/β)^|F| |P₀|` such that `B B⁻¹` lies in `P₀ P₀⁻¹` and
in every `Q f (Q f)⁻¹`. -/
lemma exists_common_mul_inv (P₀ U : Finset G) (Q : G → Finset G) (N α β : ℝ) (hα : 0 < α)
    (hβ : 0 < β) (hN : 0 < N) (hP₀U : P₀ ⊆ U) (hP₀ : P₀.Nonempty) (F : Finset G)
    (hQU : ∀ f ∈ F, Q f ⊆ U) (hQ : ∀ f ∈ F, α * N ≤ #(Q f)) (hU : (#(U⁻¹ * U) : ℝ) ≤ β * N) :
    ∃ B ⊆ U, (α / β) ^ #F * #P₀ ≤ #B ∧ B * B⁻¹ ⊆ P₀ * P₀⁻¹ ∧
      ∀ f ∈ F, B * B⁻¹ ⊆ Q f * (Q f)⁻¹ := by
  induction F using Finset.induction_on with
  | empty => exact ⟨P₀, hP₀U, by simp, subset_rfl, by simp⟩
  | insert a F haF ih =>
    obtain ⟨B, hBU, hBc, hBP, hBQ⟩ :=
      ih (fun f hf => hQU f (mem_insert_of_mem hf)) (fun f hf => hQ f (mem_insert_of_mem hf))
    have hP0c : (0 : ℝ) < #P₀ := by exact_mod_cast hP₀.card_pos
    have hBpos : (0 : ℝ) < #B := lt_of_lt_of_le (by positivity) hBc
    have hBne : B.Nonempty := by rw [← card_pos]; exact_mod_cast hBpos
    have hQa := hQ a (mem_insert_self _ _)
    have hQapos : (0 : ℝ) < #(Q a) := lt_of_lt_of_le (by positivity) hQa
    have hQne : (Q a).Nonempty := by rw [← card_pos]; exact_mod_cast hQapos
    obtain ⟨B', hB'Q, hB'c, hB'P, hB'Q'⟩ := exists_subset_mul_inv_subset B (Q a) hBne hQne
    have hQaU := hQU a (mem_insert_self _ _)
    have hsub : B⁻¹ * Q a ⊆ U⁻¹ * U := mul_subset_mul (inv_subset_inv hBU) hQaU
    have hcard : (#(B⁻¹ * Q a) : ℝ) ≤ β * N := le_trans (by exact_mod_cast card_le_card hsub) hU
    refine ⟨B', hB'Q.trans hQaU, ?_, hB'P.trans hBP, ?_⟩
    · rw [card_insert_of_notMem haF, pow_succ]
      have h1 : #B * (α * N) ≤ #B' * (β * N) := by
        calc #B * (α * N) ≤ #B * #(Q a) := by gcongr
          _ ≤ #B' * #(B⁻¹ * Q a) := hB'c
          _ ≤ #B' * (β * N) := by gcongr
      have h2 : (α / β) * #B ≤ #B' := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hβ]
        nlinarith
      calc (α / β) ^ #F * (α / β) * #P₀ = (α / β) * ((α / β) ^ #F * #P₀) := by ring
        _ ≤ (α / β) * #B := by gcongr
        _ ≤ #B' := h2
    · intro f hf
      rcases mem_insert.1 hf with rfl | hf
      · exact hB'Q'
      · exact hB'P.trans (hBQ f hf)

/-- **Theorem 5.6** of Breuillard–Green–Tao (small normal neighbourhoods), for global approximate
groups: if `A` is a `K`-approximate group and `S ⊆ A⁴` is a `K'`-approximate group with
`|S| ≥ δ |A|`, then there is a `K''`-approximate group `T` with `|T| ≥ c |A|` such that
`x⁻¹ T^m x ⊆ S⁴` for every `x ∈ A⁴`; the constants `K''` and `c > 0` depend only on
`K, K', δ, m`. -/
theorem sanders_small_normal_neighbourhoods (K K' δ : ℝ) (hK : 1 ≤ K) (hK' : 1 ≤ K') (hδ : 0 < δ)
    (m : ℕ) :
    ∃ K'' c : ℝ, 0 < c ∧ ∀ {G : Type*} [Group G] (A S : Set G), IsBGTApproxGroup K A →
      IsBGTApproxGroup K' S → S ⊆ A ^ 4 → δ * A.ncard ≤ S.ncard →
      ∃ T : Set G, IsBGTApproxGroup K'' T ∧ c * A.ncard ≤ T.ncard ∧
        ∀ x ∈ A ^ 4, ∀ y ∈ T ^ m, x⁻¹ * y * x ∈ S ^ 4 := by
  obtain ⟨K₁, c₁, hc₁, h53⟩ := sanders_small_neighbourhoods K' hK' (4 * m + 4)
  have hK0 : (0 : ℝ) < K := by linarith
  set α := c₁ * δ with hα
  have hα0 : 0 < α := by positivity
  set β := K ^ 39 with hβ
  have hβ0 : 0 < β := by positivity
  set L := K ^ 19 / α with hL
  set N₀ := ⌈L⌉₊ with hN₀
  set ρ := min (α / β) 1 with hρ
  have hρ0 : 0 < ρ := lt_min (by positivity) one_pos
  have hρ1 : ρ ≤ 1 := min_le_right _ _
  set c₂ := ρ ^ N₀ * α with hc₂
  have hc₂0 : 0 < c₂ := by positivity
  refine ⟨2 * (K ^ 159 / c₂), c₂, hc₂0, ?_⟩
  intro G _ A S hA hS hSA hSc
  classical
  obtain ⟨S₀s, hS₀ap, hS₀c, hS₀pow⟩ := h53 S hS
  obtain ⟨A', rfl⟩ := hA.1.exists_finset_coe
  obtain ⟨S', rfl⟩ := hS.1.exists_finset_coe
  obtain ⟨S₀, rfl⟩ := hS₀ap.1.exists_finset_coe
  rw [Set.ncard_coe_finset, Set.ncard_coe_finset] at hSc
  rw [Set.ncard_coe_finset, Set.ncard_coe_finset] at hS₀c
  rw [← coe_pow, ← coe_pow, coe_subset] at hS₀pow
  rw [← coe_pow, coe_subset] at hSA
  have hA1 : 1 ∈ A' := hA.2.1
  have hS1 : 1 ∈ S₀ := hS₀ap.2.1
  have hS'1 : 1 ∈ S' := hS.2.1
  have hS₀inv : S₀⁻¹ = S₀ := by
    have := hS₀ap.2.2.1
    rw [← coe_inv, coe_inj] at this
    exact this
  have hAne : A'.Nonempty := ⟨1, hA1⟩
  have hS₀ne : S₀.Nonempty := ⟨1, hS1⟩
  have hA' : (0 : ℝ) < #A' := by exact_mod_cast hAne.card_pos
  -- sizes and containments
  have hS₀size : α * #A' ≤ #S₀ := by
    calc α * #A' = c₁ * (δ * #A') := by ring
      _ ≤ c₁ * #S' := by gcongr
      _ ≤ #S₀ := hS₀c
  have hS₀S : S₀ ⊆ S' ^ 4 := by
    refine subset_trans ?_ hS₀pow
    simpa using pow_subset_pow_right hS1 (show 1 ≤ 4 * m + 4 by omega)
  have hS₀A : S₀ ⊆ A' ^ 16 := by
    calc S₀ ⊆ S' ^ 4 := hS₀S
      _ ⊆ (A' ^ 4) ^ 4 := pow_subset_pow_left hSA
      _ = A' ^ 16 := by rw [← pow_mul]
  have hcardA : ∀ n : ℕ, (#(A' ^ (n + 1)) : ℝ) ≤ K ^ n * #A' := card_pow_succ_le_of_approx hA
  -- Ruzsa covering
  have hRz : (#(A' ^ 4 * S₀) : ℝ) ≤ L * #S₀ := by
    have h1 : A' ^ 4 * S₀ ⊆ A' ^ (19 + 1) := by
      calc A' ^ 4 * S₀ ⊆ A' ^ 4 * A' ^ 16 := mul_subset_mul_left hS₀A
        _ = A' ^ (19 + 1) := by rw [← pow_add]
    calc (#(A' ^ 4 * S₀) : ℝ) ≤ #(A' ^ (19 + 1)) := by exact_mod_cast card_le_card h1
      _ ≤ K ^ 19 * #A' := hcardA 19
      _ = L * (α * #A') := by rw [hL]; field_simp
      _ ≤ L * #S₀ := by gcongr
  obtain ⟨F, hFA, hFL, hAF⟩ := ruzsa_covering_mul hS₀ne hRz
  have hS₀div : S₀ / S₀ = S₀ * S₀ := by rw [div_eq_mul_inv, hS₀inv]
  rw [hS₀div] at hAF
  have hFN : #F ≤ N₀ := by
    have : (#F : ℝ) ≤ N₀ := hFL.trans (Nat.le_ceil _)
    exact_mod_cast this
  -- iterate Lemma 5.8
  have hU : (#((A' ^ 20)⁻¹ * A' ^ 20) : ℝ) ≤ β * #A' := by
    have e : (A' ^ 20)⁻¹ * A' ^ 20 = A' ^ (39 + 1) := by
      have hAinv : A'⁻¹ = A' := by
        have := hA.2.2.1
        rw [← coe_inv, coe_inj] at this
        exact this
      rw [← inv_pow, hAinv, ← pow_add]
    rw [e]; exact hcardA 39
  obtain ⟨B, hBU, hBc, hBP, hBQ⟩ := exists_common_mul_inv S₀ (A' ^ 20) (fun f => f • S₀) (#A')
    α β hα0 hβ0 hA'
    (hS₀A.trans (pow_subset_pow_right hA1 (by norm_num))) hS₀ne F
    (fun f hf => by
      intro z hz
      obtain ⟨s, hs, rfl⟩ := mem_smul_finset.1 hz
      rw [smul_eq_mul, show 20 = 4 + 16 by rfl, pow_add]
      exact mul_mem_mul (hFA hf) (hS₀A hs))
    (fun f _ => by rw [card_smul_finset]; exact hS₀size) hU
  -- the set `T`
  set T := B * B⁻¹ with hT
  have hBsize : c₂ * #A' ≤ #B := by
    have h1 : ρ ^ N₀ ≤ (α / β) ^ #F := by
      calc ρ ^ N₀ ≤ ρ ^ #F := pow_le_pow_of_le_one hρ0.le hρ1 hFN
        _ ≤ (α / β) ^ #F := pow_le_pow_left₀ hρ0.le (min_le_left _ _) _
    calc c₂ * #A' = ρ ^ N₀ * (α * #A') := by rw [hc₂]; ring
      _ ≤ (α / β) ^ #F * #S₀ := by gcongr
      _ ≤ #B := hBc
  have hBne : B.Nonempty := by
    rw [← card_pos]
    have : (0 : ℝ) < #B := lt_of_lt_of_le (by positivity) hBsize
    exact_mod_cast this
  have hT1 : 1 ∈ T := by
    obtain ⟨b, hb⟩ := hBne
    exact mem_mul.2 ⟨b, hb, b⁻¹, inv_mem_inv hb, mul_inv_cancel b⟩
  have hTinv : T⁻¹ = T := by rw [hT, mul_inv_rev, inv_inv]
  have hTS : T ⊆ S₀ * S₀ := by
    have := hBP
    rwa [hS₀inv] at this
  have hTsize : c₂ * #A' ≤ #T := hBsize.trans (by exact_mod_cast card_le_card_mul_right hBne.inv)
  have hTle : T ⊆ T ^ 2 := by simpa using pow_subset_pow_right hT1 (show 1 ≤ 2 by norm_num)
  refine ⟨((T ^ 2 : Finset G) : Set G), ?_, ?_, ?_⟩
  · apply isBGTApproxGroup_sq_of_card_pow_five_le hT1 hTinv
    have h1 : T ^ 5 ⊆ A' ^ (159 + 1) := by
      calc T ^ 5 ⊆ (S₀ * S₀) ^ 5 := pow_subset_pow_left hTS
        _ ⊆ (A' ^ 16 * A' ^ 16) ^ 5 := pow_subset_pow_left (mul_subset_mul hS₀A hS₀A)
        _ = A' ^ (159 + 1) := by rw [← pow_add, ← pow_mul]
    calc (#(T ^ 5) : ℝ) ≤ #(A' ^ (159 + 1)) := by exact_mod_cast card_le_card h1
      _ ≤ K ^ 159 * #A' := hcardA 159
      _ = K ^ 159 / c₂ * (c₂ * #A') := by field_simp
      _ ≤ K ^ 159 / c₂ * #T := by gcongr
  · rw [Set.ncard_coe_finset, Set.ncard_coe_finset]
    exact hTsize.trans (by exact_mod_cast card_le_card hTle)
  · intro x hx y hy
    rw [← coe_pow, mem_coe] at hx
    have hy' : y ∈ T ^ (2 * m) := by
      rw [pow_mul]; rw [← coe_pow, mem_coe] at hy; exact hy
    rw [← coe_pow, mem_coe]
    obtain ⟨f, hf, s, hs, rfl⟩ := mem_mul.1 (hAF hx)
    have hconj : ∀ t ∈ T, f⁻¹ * t * f ∈ S₀ * S₀ := by
      intro t ht
      obtain ⟨u, hu, v, hv, rfl⟩ := mem_mul.1 (hBQ f hf ht)
      obtain ⟨s₁, hs₁, rfl⟩ := mem_smul_finset.1 hu
      rw [mem_inv'] at hv
      obtain ⟨s₂, hs₂, hs₂e⟩ := mem_smul_finset.1 hv
      rw [smul_eq_mul] at hs₂e ⊢
      have hv' : v = s₂⁻¹ * f⁻¹ := by rw [← inv_inv v, ← hs₂e]; group
      refine mem_mul.2 ⟨s₁, hs₁, s₂⁻¹, ?_, by rw [hv']; group⟩
      rw [← hS₀inv]; exact inv_mem_inv hs₂
    have h1 := conj_mem_pow hconj (2 * m) y hy'
    rw [← sq, ← pow_mul] at h1
    have hs2 : s ∈ S₀ ^ 2 := by rw [sq]; exact hs
    have hs2' : s⁻¹ ∈ S₀ ^ 2 := by
      have e2 : (S₀ ^ 2)⁻¹ = S₀ ^ 2 := by rw [← inv_pow, hS₀inv]
      rw [← e2]; exact inv_mem_inv hs2
    have hmem : s⁻¹ * (f⁻¹ * y * f) * s ∈ S₀ ^ (4 * m + 4) := by
      rw [show 4 * m + 4 = 2 + 2 * (2 * m) + 2 by ring, pow_add, pow_add]
      exact mul_mem_mul (mul_mem_mul hs2' h1) hs2
    have e : (f * s)⁻¹ * y * (f * s) = s⁻¹ * (f⁻¹ * y * f) * s := by group
    rw [e]
    exact hS₀pow hmem

end Lovasz.BGT
