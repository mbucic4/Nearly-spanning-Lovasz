module
public import RequestProject.BGTEscape

/-!
# Tools for Gleason's lemmas (Section 8 of Breuillard–Green–Tao)

Difference operators, convolutions, word metrics built from a weight, and the two "bump"
functions `φ` (Lemma 8.3) and `ψ` (Lemma 8.4) of the proof of Theorem 8.1.
-/

@[expose] public section

open scoped Pointwise
open Finset Function

namespace Lovasz.BGT

variable {G : Type*} [Group G]

/-! ### Difference operators and convolutions -/

/-- The difference operator `∂_g f (x) = f(g⁻¹ x) - f(x)`. -/
def dif (g : G) (f : G → ℝ) : G → ℝ := fun x => f (g⁻¹ * x) - f x

lemma dif_mul (g h : G) (f : G → ℝ) (x : G) :
    dif (g * h) f x = dif h f (g⁻¹ * x) + dif g f x := by
  simp only [dif, mul_inv_rev, mul_assoc]; ring

lemma dif_one (f : G → ℝ) (x : G) : dif 1 f x = 0 := by simp [dif]

/-- Taylor's formula (8.4): `∂_{gⁿ} f = n ∂_g f + ∑_{i<n} ∂_{gⁱ} ∂_g f`. -/
lemma dif_pow (g : G) (f : G → ℝ) (x : G) (n : ℕ) :
    dif (g ^ n) f x = n * dif g f x + ∑ i ∈ range n, dif (g ^ i) (dif g f) x := by
  induction n with
  | zero => simp [dif]
  | succ n ih =>
    rw [pow_succ, dif_mul, sum_range_succ, ih]
    simp only [dif, Nat.cast_succ]
    ring

/-- The commutator identity `∂_g ∂_h f - ∂_h ∂_g f = (∂_{[g,h]} f)(g⁻¹ h⁻¹ x)` with
`[g,h] = g⁻¹ h⁻¹ g h`. -/
lemma dif_comm (g h : G) (f : G → ℝ) (x : G) :
    dif g (dif h f) x - dif h (dif g f) x = dif (g⁻¹ * h⁻¹ * g * h) f (g⁻¹ * h⁻¹ * x) := by
  simp only [dif]
  rw [show (g⁻¹ * h⁻¹ * g * h)⁻¹ * (g⁻¹ * h⁻¹ * x) = h⁻¹ * (g⁻¹ * x) by group,
    mul_assoc g⁻¹ h⁻¹ x]
  ring

/-- Convolution `(f * k)(x) = ∑_y f(y) k(y⁻¹ x)`. -/
noncomputable def conv (f k : G → ℝ) : G → ℝ := fun x => ∑ᶠ y, f y * k (y⁻¹ * x)

omit [Group G] in
lemma support_mul_finite {f : G → ℝ} (hf : (support f).Finite) (k : G → ℝ) :
    (support fun y => f y * k y).Finite :=
  hf.subset (support_mul_subset_left _ _)

lemma support_dif_finite {f : G → ℝ} (hf : (support f).Finite) (g : G) :
    (support (dif g f)).Finite := by
  have : support (dif g f) ⊆ (fun y => g * y) '' support f ∪ support f := by
    intro y hy
    by_cases h : f y = 0
    · left
      refine ⟨g⁻¹ * y, ?_, by simp⟩
      intro h'
      apply hy
      simp [dif, h, h']
    · right; exact h
  exact (hf.image _ |>.union hf).subset this

lemma dif_conv_left {f : G → ℝ} (hf : (support f).Finite) (k : G → ℝ) (g x : G) :
    dif g (conv f k) x = conv (dif g f) k x := by
  simp only [dif, conv]
  have h1 : ∑ᶠ y, f y * k (y⁻¹ * (g⁻¹ * x)) = ∑ᶠ y, f (g⁻¹ * y) * k (y⁻¹ * x) := by
    rw [← finsum_comp_equiv (Equiv.mulLeft g⁻¹)]
    congr 1; ext y
    simp [mul_assoc]
  rw [h1, ← finsum_sub_distrib]
  · congr 1; ext y; ring
  · exact support_mul_finite (hf.preimage (mul_right_injective _).injOn) _
  · exact support_mul_finite hf _

lemma dif_conv_right {f : G → ℝ} (hf : (support f).Finite) (k : G → ℝ) (h x : G) :
    dif h (conv f k) x = ∑ᶠ y, f y * dif (y⁻¹ * h * y) k (y⁻¹ * x) := by
  simp only [dif, conv]
  rw [← finsum_sub_distrib (support_mul_finite hf _) (support_mul_finite hf _)]
  congr 1; ext y
  simp only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
  ring

omit [Group G] in
/-- Bounding a finite sum. -/
lemma abs_finsum_le {f : G → ℝ} (s : Finset G) (hs : support f ⊆ s) {B : ℝ}
    (hB : ∀ y ∈ s, |f y| ≤ B) : |∑ᶠ y, f y| ≤ #s * B := by
  rw [finsum_eq_sum_of_support_subset f hs]
  calc |∑ y ∈ s, f y| ≤ ∑ y ∈ s, |f y| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _y ∈ s, B := sum_le_sum hB
    _ = #s * B := by rw [sum_const, nsmul_eq_mul]

/-! ### Word metrics from a weight -/

/-- The word metric `d(g) = inf {∑ w(gᵢ) : g = g₁ ⋯ gₙ}` associated with a weight `w`. -/
noncomputable def wdist (w : G → ℝ) (g : G) : ℝ :=
  sInf {s | ∃ l : List G, l.prod = g ∧ (l.map w).sum = s}

section Wdist

variable {w : G → ℝ} (hw0 : ∀ g, 0 ≤ w g)
include hw0

omit [Group G] in
lemma list_sum_nonneg (l : List G) : 0 ≤ (l.map w).sum :=
  List.sum_nonneg (by simp only [List.mem_map]; rintro _ ⟨a, -, rfl⟩; exact hw0 a)

lemma wdist_bddBelow (g : G) : BddBelow {s | ∃ l : List G, l.prod = g ∧ (l.map w).sum = s} :=
  ⟨0, by rintro _ ⟨l, -, rfl⟩; exact list_sum_nonneg hw0 l⟩

lemma wdist_nonneg (g : G) : 0 ≤ wdist w g :=
  le_csInf ⟨_, [g], by simp, rfl⟩ (by rintro _ ⟨l, -, rfl⟩; exact list_sum_nonneg hw0 l)

lemma wdist_le_list {g : G} (l : List G) (hl : l.prod = g) : wdist w g ≤ (l.map w).sum :=
  csInf_le (wdist_bddBelow hw0 g) ⟨l, hl, rfl⟩

lemma wdist_le (g : G) : wdist w g ≤ w g := by
  simpa using wdist_le_list hw0 [g] (by simp)

lemma wdist_one : wdist w (1 : G) = 0 :=
  le_antisymm (by simpa using wdist_le_list hw0 ([] : List G) (by simp)) (wdist_nonneg hw0 1)

omit hw0 in
lemma le_wdist {g : G} {c : ℝ} (h : ∀ l : List G, l.prod = g → c ≤ (l.map w).sum) :
    c ≤ wdist w g :=
  le_csInf ⟨_, [g], by simp, rfl⟩ (by rintro _ ⟨l, hl, rfl⟩; exact h l hl)

lemma wdist_mul (g h : G) : wdist w (g * h) ≤ wdist w g + wdist w h := by
  have key : ∀ l₁ l₂ : List G, l₁.prod = g → l₂.prod = h →
      wdist w (g * h) ≤ (l₁.map w).sum + (l₂.map w).sum := by
    intro l₁ l₂ h₁ h₂
    have := wdist_le_list hw0 (l₁ ++ l₂) (by rw [List.prod_append, h₁, h₂])
    simpa using this
  have h1 : ∀ l₂ : List G, l₂.prod = h → wdist w (g * h) - (l₂.map w).sum ≤ wdist w g :=
    fun l₂ h₂ => le_wdist fun l₁ h₁ => by linarith [key l₁ l₂ h₁ h₂]
  have h2 : wdist w (g * h) - wdist w g ≤ wdist w h :=
    le_wdist fun l₂ h₂ => by linarith [h1 l₂ h₂]
  linarith

lemma wdist_list_prod_le (l : List G) : wdist w l.prod ≤ (l.map (wdist w)).sum := by
  induction l with
  | nil => simp [wdist_one hw0]
  | cons a l ih =>
    simp only [List.prod_cons, List.map_cons, List.sum_cons]
    linarith [wdist_mul hw0 a l.prod]

lemma wdist_inv (hwinv : ∀ g, w g⁻¹ = w g) (g : G) : wdist w g⁻¹ = wdist w g := by
  have key : ∀ g : G, wdist w g⁻¹ ≤ wdist w g := by
    intro g
    refine le_wdist fun l hl => ?_
    have := wdist_le_list hw0 (l.map (·⁻¹)).reverse (by rw [← List.prod_inv_reverse, hl])
    simpa [List.map_reverse, Function.comp_def, hwinv] using this
  exact le_antisymm (key g) (by simpa using key g⁻¹)

/-- If every weight is at least `ε`, then `d(z) ≥ ε` for `z ≠ 1`. -/
lemma le_wdist_of_ne_one {ε : ℝ} (hε : ∀ g, ε ≤ w g) {z : G} (hz : z ≠ 1) : ε ≤ wdist w z := by
  refine le_wdist fun l hl => ?_
  cases l with
  | nil => exact absurd hl.symm (by simpa using hz)
  | cons a l =>
    simp only [List.map_cons, List.sum_cons]
    linarith [hε a, list_sum_nonneg hw0 l]

end Wdist

/-! ### The function `φ` of Lemma 8.3 -/

section Phi

variable (w : G → ℝ) (A : Finset G) (hA : A.Nonempty)

/-- `D = min(1, inf {d(z) : z ∉ A})`. -/
noncomputable def wD : ℝ := sInf (insert 1 (wdist w '' ((A : Set G)ᶜ)))

/-- The distance `d(x, A) = min_{b ∈ A} d(x b⁻¹)`. -/
noncomputable def wdistA (x : G) : ℝ := A.inf' hA fun b => wdist w (x * b⁻¹)

/-- **Lemma 8.3**: the function `φ(x) = max(0, 1 - d(x, A)/D)`. -/
noncomputable def phi (x : G) : ℝ := max 0 (1 - wdistA w A hA x / wD w A)

variable {w A}
variable (hw0 : ∀ g, 0 ≤ w g)
include hw0

omit hA in
lemma wD_bddBelow : BddBelow (insert (1 : ℝ) (wdist w '' ((A : Set G)ᶜ))) := by
  refine ⟨0, ?_⟩
  rintro _ (rfl | ⟨z, -, rfl⟩)
  · norm_num
  · exact wdist_nonneg hw0 z

omit hA in
lemma wD_le_one : wD w A ≤ 1 := csInf_le (wD_bddBelow hw0) (Set.mem_insert _ _)

omit hA in
lemma wD_le {z : G} (hz : z ∉ A) : wD w A ≤ wdist w z :=
  csInf_le (wD_bddBelow hw0) (Set.mem_insert_of_mem _ ⟨z, hz, rfl⟩)

omit hA hw0 in
lemma le_wD {c : ℝ} (hc : c ≤ 1) (h : ∀ z, z ∉ A → c ≤ wdist w z) : c ≤ wD w A :=
  le_csInf (Set.insert_nonempty _ _) (by rintro _ (rfl | ⟨z, hz, rfl⟩); exacts [hc, h z hz])

omit hA in
lemma mem_of_wdist_lt_wD {z : G} (h : wdist w z < wD w A) : z ∈ A := by
  by_contra hz; exact absurd (wD_le hw0 hz) (not_le.2 h)

lemma wdistA_nonneg (x : G) : 0 ≤ wdistA w A hA x := by
  obtain ⟨b, hb, hb'⟩ := A.exists_mem_eq_inf' hA fun b => wdist w (x * b⁻¹)
  rw [wdistA, hb']; exact wdist_nonneg hw0 _

lemma wdistA_eq_zero {x : G} (hx : x ∈ A) : wdistA w A hA x = 0 := by
  refine le_antisymm ?_ (wdistA_nonneg hA hw0 x)
  calc wdistA w A hA x ≤ wdist w (x * x⁻¹) := inf'_le _ hx
    _ = 0 := by rw [mul_inv_cancel, wdist_one hw0]

lemma wdistA_le (hwinv : ∀ g, w g⁻¹ = w g) (g x : G) :
    wdistA w A hA (g⁻¹ * x) ≤ wdist w g + wdistA w A hA x := by
  obtain ⟨b, hb, hb'⟩ := A.exists_mem_eq_inf' hA fun b => wdist w (x * b⁻¹)
  have h1 : wdistA w A hA (g⁻¹ * x) ≤ wdist w (g⁻¹ * x * b⁻¹) := inf'_le _ hb
  rw [show wdistA w A hA x = wdist w (x * b⁻¹) from hb']
  refine h1.trans ?_
  rw [mul_assoc, ← wdist_inv hw0 hwinv g]
  exact wdist_mul hw0 _ _

lemma wdistA_le' (hwinv : ∀ g, w g⁻¹ = w g) (g x : G) :
    wdistA w A hA x ≤ wdist w g + wdistA w A hA (g⁻¹ * x) := by
  have := wdistA_le hA hw0 hwinv g⁻¹ (g⁻¹ * x)
  rwa [inv_inv, ← mul_assoc, mul_inv_cancel, one_mul, wdist_inv hw0 hwinv] at this

omit hw0 in
lemma phi_nonneg (x : G) : 0 ≤ phi w A hA x := le_max_left _ _

omit hA in
lemma wD_pos_of {ε : ℝ} (hε1 : ε ≤ 1) (hε : ∀ g, ε ≤ w g) (hA1 : (1 : G) ∈ A) :
    ε ≤ wD w A :=
  le_wD hε1 fun z hz => le_wdist_of_ne_one hw0 hε (by rintro rfl; exact hz hA1)

lemma phi_le_one (hD : 0 < wD w A) (x : G) : phi w A hA x ≤ 1 := by
  have := wdistA_nonneg hA hw0 x
  refine max_le zero_le_one ?_
  have : 0 ≤ wdistA w A hA x / wD w A := div_nonneg this hD.le
  linarith

lemma phi_eq_one {x : G} (hx : x ∈ A) : phi w A hA x = 1 := by
  simp [phi, wdistA_eq_zero hA hw0 hx]

lemma phi_mem [DecidableEq G] (hD : 0 < wD w A) {x : G} (hx : phi w A hA x ≠ 0) : x ∈ A * A := by
  have hlt : wdistA w A hA x < wD w A := by
    by_contra hc
    push_neg at hc
    apply hx
    refine max_eq_left ?_
    rw [sub_nonpos, le_div_iff₀ hD, one_mul]; exact hc
  obtain ⟨b, hb, hb'⟩ := A.exists_mem_eq_inf' hA fun b => wdist w (x * b⁻¹)
  rw [wdistA, hb'] at hlt
  have := mem_of_wdist_lt_wD hw0 hlt
  exact mem_mul.2 ⟨x * b⁻¹, this, b, hb, by group⟩

/-- The Lipschitz bound of Lemma 8.3 (iii): `|∂_g φ| ≤ d(g)/D`. -/
lemma abs_dif_phi_le (hwinv : ∀ g, w g⁻¹ = w g) (hD : 0 < wD w A) (g x : G) :
    |dif g (phi w A hA) x| ≤ wdist w g / wD w A := by
  simp only [dif, phi]
  have h1 := wdistA_le hA hw0 hwinv g x
  have h2 := wdistA_le' hA hw0 hwinv g x
  have key : ∀ a b : ℝ, |max 0 (1 - a / wD w A) - max 0 (1 - b / wD w A)| ≤ |a - b| / wD w A := by
    intro a b
    calc |max 0 (1 - a / wD w A) - max 0 (1 - b / wD w A)| ≤ |(1 - a / wD w A) - (1 - b / wD w A)| :=
          by rw [max_comm 0, max_comm 0]; exact abs_max_sub_max_le_abs _ _ _
      _ = |a - b| / wD w A := by
          rw [show (1 - a / wD w A) - (1 - b / wD w A) = (b - a) / wD w A by ring, abs_div,
            abs_of_pos hD, abs_sub_comm]
  refine (key _ _).trans ?_
  gcongr
  rw [abs_le]; constructor <;> linarith

end Phi

/-! ### The function `ψ` of Lemma 8.4 -/

section Psi

open Classical in
/-- **Lemma 8.4**: `ψ(x) = #{i < N : x ∈ Qⁱ A} / N`, a "Lipschitz" bump function for shifts by
elements of `Q`. -/
noncomputable def psi (Q A : Set G) (N : ℕ) (x : G) : ℝ :=
  (#((range N).filter (fun i => x ∈ Q ^ i * A)) : ℝ) / N

variable {Q A : Set G} {N : ℕ}

lemma psi_nonneg (x : G) : 0 ≤ psi Q A N x := by unfold psi; positivity

lemma psi_le_one (x : G) : psi Q A N x ≤ 1 := by
  classical
  unfold psi
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  rw [div_le_one (by exact_mod_cast hN)]
  exact_mod_cast (card_filter_le _ _).trans (card_range N).le

lemma psi_eq_one (hQ1 : (1 : G) ∈ Q) (hN : 0 < N) {x : G} (hx : x ∈ A) : psi Q A N x = 1 := by
  classical
  unfold psi
  rw [filter_true_of_mem, card_range, div_self (by exact_mod_cast hN.ne')]
  intro i _
  exact ⟨1, Set.one_mem_pow hQ1, x, hx, one_mul x⟩

lemma psi_mem (hQ1 : (1 : G) ∈ Q) (hQN : Q ^ N ⊆ A) {x : G} (hx : psi Q A N x ≠ 0) :
    x ∈ A * A := by
  classical
  unfold psi at hx
  have : ((range N).filter (fun i => x ∈ Q ^ i * A)).Nonempty := by
    rw [← card_pos]
    by_contra h
    apply hx
    simp only [not_lt, Nat.le_zero] at h
    simp [h]
  obtain ⟨i, hi⟩ := this
  rw [mem_filter, mem_range] at hi
  exact Set.mul_subset_mul_right ((Set.pow_subset_pow_right hQ1 hi.1.le).trans hQN) hi.2

open Classical in
lemma card_filter_le_succ {x y : G}
    (h : ∀ i, x ∈ Q ^ i * A → y ∈ Q ^ (i + 1) * A) :
    (#((range N).filter (fun i => x ∈ Q ^ i * A)) : ℝ) ≤
      #((range N).filter (fun i => y ∈ Q ^ i * A)) + 1 := by
  classical
  have hsub : (range N).filter (fun i => x ∈ Q ^ i * A) ⊆
      insert (N - 1) (((range N).filter (fun i => y ∈ Q ^ i * A)).image (fun j => j - 1)) := by
    intro i hi
    rw [mem_filter, mem_range] at hi
    rw [mem_insert, mem_image]
    by_cases hiN : i = N - 1
    · left; exact hiN
    · right
      refine ⟨i + 1, ?_, by simp⟩
      rw [mem_filter, mem_range]
      exact ⟨by omega, h i hi.2⟩
  have h1 := (card_le_card hsub).trans (card_insert_le _ _)
  have h2 := card_image_le (s := (range N).filter (fun i => y ∈ Q ^ i * A)) (f := fun j => j - 1)
  have h3 : #((range N).filter (fun i => x ∈ Q ^ i * A)) ≤
      #((range N).filter (fun i => y ∈ Q ^ i * A)) + 1 := by omega
  exact_mod_cast h3

/-- The Lipschitz bound of Lemma 8.4 (iii): `|∂_q ψ| ≤ 1/N` for `q ∈ Q`. -/
lemma abs_dif_psi_le (hQinv : Q⁻¹ = Q) {q : G} (hq : q ∈ Q) (x : G) :
    |dif q (psi Q A N) x| ≤ 1 / N := by
  classical
  have hq' : q⁻¹ ∈ Q := by rw [← hQinv]; exact Set.inv_mem_inv.2 hq
  have step : ∀ r ∈ Q, ∀ z : G, ∀ i, z ∈ Q ^ i * A → r * z ∈ Q ^ (i + 1) * A := by
    intro r hr z i hz
    rw [pow_succ', mul_assoc]
    exact Set.mul_mem_mul hr hz
  have h1 := card_filter_le_succ (N := N) (x := x) (y := q⁻¹ * x) (fun i hi => step _ hq' _ i hi)
  have h2 := card_filter_le_succ (N := N) (x := q⁻¹ * x) (y := x)
    (fun i hi => by simpa using step _ hq _ i hi)
  simp only [dif, psi]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← sub_div, abs_div, abs_of_pos hN', div_le_div_iff_of_pos_right hN', abs_le]
  constructor <;> linarith

end Psi

end Lovasz.BGT
