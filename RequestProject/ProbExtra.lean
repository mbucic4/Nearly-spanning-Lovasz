module
public import RequestProject.Coupling

/-!
# Further tools for finite product probability spaces

* conditioning on one coordinate ("slicing"), used for sequential exposure of random sets;
* Chernoff bounds with a free exponential parameter;
* independence of functions of disjoint sets of coordinates, and a Chernoff bound for
  counts of events depending on pairwise disjoint sets of coordinates;
* random sets exposed in several independent rounds.
-/

@[expose] public section


open scoped BigOperators
open Classical

namespace Lovasz

noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

section slice

variable {μ : ι → κ → ℝ}

/-- If, whatever the other coordinates are, the average of `F` over the coordinate `j` is at
most `δ`, then the expectation of `F` is at most `δ`. -/
lemma pex_le_of_slice (hμ : IsPD μ) (j : ι) {F : (ι → κ) → ℝ} {δ : ℝ}
    (h : ∀ x, ∑ k, μ j k * F (Function.update x j k) ≤ δ) : pex μ F ≤ δ := by
  have h1 : pex μ F = pex μ (fun x => ∑ k, μ j k * F (Function.update x j k)) := by
    rw [pex_eq_sum_condFun j, pex_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pex_const_mul, pex_update hμ]
  rw [h1]
  calc pex μ (fun x => ∑ k, μ j k * F (Function.update x j k)) ≤ pex μ (fun _ => δ) :=
        pex_mono hμ h
    _ = δ := pex_const hμ δ

lemma ppr_le_of_slice (hμ : IsPD μ) (j : ι) {P : (ι → κ) → Prop} {δ : ℝ}
    (h : ∀ x, ∑ k, μ j k * (if P (Function.update x j k) then 1 else 0) ≤ δ) : ppr μ P ≤ δ :=
  pex_le_of_slice hμ j h

/-- `ppr_le_of_slice` for an arbitrary decidable-equality instance on the coordinates. -/
lemma ppr_le_of_slice_dec [inst : DecidableEq ι] (hμ : IsPD μ) (j : ι) {P : (ι → κ) → Prop}
    {δ : ℝ} (h : ∀ x, ∑ k, μ j k *
      (if P (@Function.update ι (fun _ => κ) inst x j k) then 1 else 0) ≤ δ) : ppr μ P ≤ δ := by
  obtain rfl : inst = (fun a b => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
  exact ppr_le_of_slice hμ j h

/-- If the expectation of `f` is less than `c`, some outcome has `f < c`. -/
lemma exists_lt_of_pex_lt (hμ : IsPD μ) {f : (ι → κ) → ℝ} {c : ℝ} (h : pex μ f < c) :
    ∃ x, f x < c := by
  by_contra hne
  push_neg at hne
  have := pex_mono hμ (f := fun _ => c) hne
  rw [pex_const hμ] at this
  linarith

end slice

section chernoff

/-- Lower-tail Chernoff bound with a free parameter `λ ≥ 0`. -/
lemma chernoff_lower_lam {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (S : Finset ι) (a : ℝ) {l : ℝ}
    (hl : 0 ≤ l) :
    ppr (fun (_ : ι) => bern q) (fun x => (cntT S x : ℝ) ≤ a) ≤
      Real.exp (l * a - (1 - Real.exp (-l)) * q * S.card) := by
  have hμ := isPD_bern (ι := ι) hq0 hq1
  have h1 : ppr (fun (_ : ι) => bern q) (fun x => (cntT S x : ℝ) ≤ a) ≤
      pex (fun _ => bern q) (fun x => Real.exp (l * a) *
        ∏ i, (if i ∈ S ∧ x i = true then Real.exp (-l) else 1)) := by
    refine pex_mono hμ fun x => ?_
    rw [prod_ite_pow, ← Real.exp_nat_mul, ← Real.exp_add]
    split_ifs with h
    · exact Real.one_le_exp (by nlinarith)
    · exact (Real.exp_pos _).le
  refine h1.trans ?_
  rw [pex_const_mul, pex_bern_prod_ite]
  have h2 : 1 - q + q * Real.exp (-l) ≤ Real.exp (-(1 - Real.exp (-l)) * q) := by
    have := Real.add_one_le_exp (-(1 - Real.exp (-l)) * q); linarith
  have h3 : 0 ≤ 1 - q + q * Real.exp (-l) := by
    have := Real.exp_pos (-l); nlinarith
  calc Real.exp (l * a) * (1 - q + q * Real.exp (-l)) ^ S.card
      ≤ Real.exp (l * a) * Real.exp (-(1 - Real.exp (-l)) * q) ^ S.card :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h3 h2 _) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf

/-- Upper-tail Chernoff bound with a free parameter `λ ≥ 0`. -/
lemma chernoff_upper_lam {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (S : Finset ι) (a : ℝ) {l : ℝ}
    (hl : 0 ≤ l) :
    ppr (fun (_ : ι) => bern q) (fun x => a ≤ cntT S x) ≤
      Real.exp ((Real.exp l - 1) * q * S.card - l * a) := by
  have hμ := isPD_bern (ι := ι) hq0 hq1
  have h1 : ppr (fun (_ : ι) => bern q) (fun x => a ≤ cntT S x) ≤
      pex (fun _ => bern q) (fun x => Real.exp (-(l * a)) *
        ∏ i, (if i ∈ S ∧ x i = true then Real.exp l else 1)) := by
    refine pex_mono hμ fun x => ?_
    rw [prod_ite_pow, ← Real.exp_nat_mul, ← Real.exp_add]
    split_ifs with h
    · exact Real.one_le_exp (by nlinarith)
    · exact (Real.exp_pos _).le
  refine h1.trans ?_
  rw [pex_const_mul, pex_bern_prod_ite]
  have h2 : 1 - q + q * Real.exp l ≤ Real.exp ((Real.exp l - 1) * q) := by
    have := Real.add_one_le_exp ((Real.exp l - 1) * q); linarith
  have h3 : 0 ≤ 1 - q + q * Real.exp l := by
    have := Real.exp_pos l; nlinarith
  calc Real.exp (-(l * a)) * (1 - q + q * Real.exp l) ^ S.card
      ≤ Real.exp (-(l * a)) * Real.exp ((Real.exp l - 1) * q) ^ S.card :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h3 h2 _) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf

end chernoff

section indep

variable {μ : ι → κ → ℝ}

/-- `F` depends only on the coordinates in `A`. -/
def DepOn (F : (ι → κ) → ℝ) (A : Finset ι) : Prop :=
  ∀ x y, (∀ i ∈ A, x i = y i) → F x = F y

omit [Fintype ι] [Fintype κ] in
lemma DepOn.indepOf {F : (ι → κ) → ℝ} {A : Finset ι} (hF : DepOn F A) {j : ι} (hj : j ∉ A) :
    IndepOf F j := fun x k => hF _ _ fun i hi => by
  have : i ≠ j := fun h => hj (h ▸ hi)
  simp [Function.update_of_ne this]

/-- Functions of disjoint sets of coordinates are uncorrelated. -/
lemma pex_mul_indep (hμ : IsPD μ) (A : Finset ι) : ∀ {F G : (ι → κ) → ℝ}, DepOn F A →
    (∀ j ∈ A, IndepOf G j) → pex μ (fun x => F x * G x) = pex μ F * pex μ G := by
  induction A using Finset.induction_on with
  | empty =>
    intro F G hF _
    by_cases hne : Nonempty (ι → κ)
    · obtain ⟨x0⟩ := hne
      have hc : F = fun _ => F x0 := funext fun x => hF x x0 (by simp)
      rw [hc, pex_const hμ, pex_const_mul]
    · have : ∀ f : (ι → κ) → ℝ, pex μ f = 0 := fun f => by
        unfold pex
        exact Finset.sum_eq_zero fun x _ => absurd ⟨x⟩ hne
      rw [this, this, this, zero_mul]
  | insert a A ha ih =>
    intro F G hF hG
    have hGa : IndepOf G a := hG a (Finset.mem_insert_self _ _)
    have hk : ∀ k, DepOn (fun x => F (Function.update x a k)) A := by
      intro k x y hxy
      refine hF _ _ fun i hi => ?_
      rcases Finset.mem_insert.1 hi with rfl | hi
      · simp
      · have : i ≠ a := fun h => ha (h ▸ hi)
        simp [Function.update_of_ne this, hxy i hi]
    rw [pex_eq_sum_condFun a, pex_eq_sum_condFun a F, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← pex_update hμ, ← pex_update hμ]
    have : (fun x => F (Function.update x a k) * G (Function.update x a k)) =
        (fun x => F (Function.update x a k) * G x) := funext fun x => by rw [hGa x k]
    rw [this, ih (hk k) (fun j hj => hG j (Finset.mem_insert_of_mem hj))]
    ring

/-- The expectation of a product of functions of pairwise disjoint sets of coordinates. -/
lemma pex_prod_indep (hμ : IsPD μ) {α : Type*} (T : Finset α) (g : α → (ι → κ) → ℝ)
    (A : α → Finset ι) (hdep : ∀ c ∈ T, DepOn (g c) (A c))
    (hdisj : ∀ c ∈ T, ∀ d ∈ T, c ≠ d → Disjoint (A c) (A d)) :
    pex μ (fun x => ∏ c ∈ T, g c x) = ∏ c ∈ T, pex μ (g c) := by
  induction T using Finset.induction_on with
  | empty => simp [pex_const hμ]
  | insert c T hc ih =>
    simp only [Finset.prod_insert hc]
    rw [pex_mul_indep hμ (A c) (hdep c (Finset.mem_insert_self _ _)) (fun j hj x k => ?_)]
    · rw [ih (fun d hd => hdep d (Finset.mem_insert_of_mem hd))
        (fun d hd e he hde => hdisj d (Finset.mem_insert_of_mem hd) e
          (Finset.mem_insert_of_mem he) hde)]
    · refine Finset.prod_congr rfl fun d hd => ?_
      have hcd : c ≠ d := fun h => hc (h ▸ hd)
      have hj' : j ∉ A d := fun h => Finset.disjoint_left.1
        (hdisj c (Finset.mem_insert_self _ _) d (Finset.mem_insert_of_mem hd) hcd) hj h
      exact (hdep d (Finset.mem_insert_of_mem hd)).indepOf hj' x k

/-- A Chernoff bound for the number of events that occur, when the events depend on pairwise
disjoint sets of coordinates and each has probability at least `π`. -/
lemma chernoff_indep (hμ : IsPD μ) {α : Type*} (T : Finset α) (E : α → (ι → κ) → Prop)
    (A : α → Finset ι) (hdep : ∀ c ∈ T, ∀ x y, (∀ i ∈ A c, x i = y i) → (E c x ↔ E c y))
    (hdisj : ∀ c ∈ T, ∀ d ∈ T, c ≠ d → Disjoint (A c) (A d)) {π : ℝ}
    (hπ : ∀ c ∈ T, π ≤ ppr μ (E c)) (a : ℝ) :
    ppr μ (fun x => ((T.filter (fun c => E c x)).card : ℝ) ≤ a) ≤
      Real.exp (a - (1 - Real.exp (-1)) * π * T.card) := by
  set g : α → (ι → κ) → ℝ := fun c x => if E c x then Real.exp (-1) else 1
  have hprod : ∀ x, ∏ c ∈ T, g c x = Real.exp (-((T.filter (fun c => E c x)).card : ℝ)) := by
    intro x
    simp only [g]
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const, ← Real.exp_nat_mul]
    ring_nf
  have h1 : ppr μ (fun x => ((T.filter (fun c => E c x)).card : ℝ) ≤ a) ≤
      pex μ (fun x => Real.exp a * ∏ c ∈ T, g c x) := by
    refine pex_mono hμ fun x => ?_
    rw [hprod, ← Real.exp_add]
    split_ifs with h
    · exact Real.one_le_exp (by linarith)
    · exact (Real.exp_pos _).le
  refine h1.trans ?_
  rw [pex_const_mul, pex_prod_indep hμ T g A (fun c hc x y hxy => by
    simp only [g]; rw [propext (hdep c hc x y hxy)]) hdisj]
  have hc1 : 0 ≤ 1 - Real.exp (-1) := by
    have := Real.exp_le_one_iff.2 (show (-1 : ℝ) ≤ 0 by norm_num); linarith
  have h2 : ∀ c ∈ T, pex μ (g c) ≤ Real.exp (-((1 - Real.exp (-1)) * π)) := by
    intro c hc
    have e : pex μ (g c) = 1 - (1 - Real.exp (-1)) * ppr μ (E c) := by
      have : g c = fun x => 1 - (1 - Real.exp (-1)) * (if E c x then 1 else 0) := by
        funext x; simp only [g]; split_ifs <;> ring
      rw [this, pex_sub, pex_const hμ, pex_const_mul]; rfl
    rw [e]
    have := Real.add_one_le_exp (-((1 - Real.exp (-1)) * π))
    have := hπ c hc
    nlinarith
  have h3 : ∀ c ∈ T, 0 ≤ pex μ (g c) := fun c _ =>
    pex_nonneg hμ fun x => by simp only [g]; split_ifs <;> positivity
  calc Real.exp a * ∏ c ∈ T, pex μ (g c)
      ≤ Real.exp a * ∏ c ∈ T, Real.exp (-((1 - Real.exp (-1)) * π)) :=
        mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ h3 h2) (Real.exp_pos _).le
    _ = _ := by
      rw [Finset.prod_const, ← Real.exp_nat_mul, ← Real.exp_add]; ring_nf

/-- Probability that a set of `r` coordinates contains no `true` entry. -/
lemma ppr_none_true {q : ℝ} (S : Finset ι) :
    ppr (fun (_ : ι) => bern q) (fun x => ∀ i ∈ S, x i = false) = (1 - q) ^ S.card := by
  have e : ppr (fun (_ : ι) => bern q) (fun x => ∀ i ∈ S, x i = false) =
      pex (fun _ => bern q) (fun x => ∏ i, (if i ∈ S ∧ x i = true then (0 : ℝ) else 1)) := by
    unfold ppr
    congr 1
    funext x
    by_cases h : ∀ i ∈ S, x i = false
    · rw [if_pos h]; symm
      exact Finset.prod_eq_one fun i _ => if_neg (by
        rintro ⟨hi, hx⟩; rw [h i hi] at hx; exact Bool.false_ne_true hx)
    · rw [if_neg h]; push_neg at h
      obtain ⟨i, hi, hx⟩ := h
      refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
      rw [if_pos ⟨hi, by simpa using hx⟩]
  rw [e, pex_bern_prod_ite]; ring_nf

end indep

section rounds

variable {V : Type*} [Fintype V]

omit [Fintype V] in
/-- The union of independent random sets with parameters `p j` is a random set with parameter
`1 - ∏ (1 - p j)`. -/
lemma pushD_any_rounds {m : ℕ} (p : Fin m → ℝ) :
    pushD (fun (_ : V) (z : Fin m → Bool) => ∏ j, bern (p j) (z j))
      (fun z => decide (∃ j, z j = true)) = fun _ => bern (1 - ∏ j, (1 - p j)) := by
  have htot : ∑ z : Fin m → Bool, ∏ j, bern (p j) (z j) = 1 := by
    rw [← Fintype.prod_sum (fun j b => bern (p j) b)]; simp [bern]
  have hfalse : ∑ z : Fin m → Bool, (∏ j, bern (p j) (z j)) *
      (if ∀ j, z j = false then (1 : ℝ) else 0) = ∏ j, (1 - p j) := by
    have : ∀ z : Fin m → Bool, (∏ j, bern (p j) (z j)) *
        (if ∀ j, z j = false then (1 : ℝ) else 0) =
        ∏ j, (bern (p j) (z j) * if z j = false then (1 : ℝ) else 0) := by
      intro z
      rw [Finset.prod_mul_distrib]
      congr 1
      by_cases h : ∀ j, z j = false
      · simp [h]
      · push_neg at h
        obtain ⟨j, hj⟩ := h
        rw [if_neg (by push_neg; exact ⟨j, hj⟩)]
        exact (Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])).symm
    simp only [this]
    rw [← Fintype.prod_sum (fun j b => bern (p j) b * if b = false then 1 else 0)]
    simp [bern]
  funext i c
  unfold pushD
  rw [Finset.sum_filter]
  cases c
  · show _ = 1 - (1 - ∏ j, (1 - p j))
    rw [sub_sub_cancel, ← hfalse]
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases h : ∃ j, z j = true
    · have : ¬ ∀ j, z j = false := by
        obtain ⟨j, hj⟩ := h; intro h'; simp [h' j] at hj
      rw [if_neg (by simpa using h), if_neg this]; ring
    · have : ∀ j, z j = false := by push_neg at h; simpa using h
      rw [if_pos (by simpa using h), if_pos this]; ring
  · have hsplit : ∀ z : Fin m → Bool, ∏ j, bern (p j) (z j) =
        (if decide (∃ j, z j = true) = true then ∏ j, bern (p j) (z j) else 0) +
          (∏ j, bern (p j) (z j)) * (if ∀ j, z j = false then (1 : ℝ) else 0) := by
      intro z
      by_cases h : ∃ j, z j = true
      · have : ¬ ∀ j, z j = false := by
          obtain ⟨j, hj⟩ := h; intro h'; simp [h' j] at hj
        rw [if_pos (decide_eq_true h), if_neg this]; ring
      · have : ∀ j, z j = false := by push_neg at h; simpa using h
        rw [if_neg (by simpa using h), if_pos this]; ring
    have := htot
    rw [Finset.sum_congr rfl (fun z _ => hsplit z)] at this
    rw [Finset.sum_add_distrib, hfalse] at this
    show _ = 1 - ∏ j, (1 - p j)
    rw [← eq_sub_of_add_eq this]
    exact Finset.sum_congr (by congr) fun x _ => by dsimp only; congr

/-- The distribution of the rounds, round by round. -/
def roundD {m : ℕ} (p : Fin m → ℝ) (j : Fin m) (z : V → Bool) : ℝ := ∏ v, bern (p j) (z v)

lemma isPD_roundD {m : ℕ} {p : Fin m → ℝ} (h0 : ∀ j, 0 ≤ p j) (h1 : ∀ j, p j ≤ 1) :
    IsPD (roundD (V := V) p) :=
  isPD_prod (ν := fun j (_ : V) => bern (p j)) (fun j => isPD_bern (h0 j) (h1 j))

/-- A random set with parameter `1 - ∏ (1 - p j)` is the union of `m` independent rounds. -/
lemma ppr_rounds {m : ℕ} (p : Fin m → ℝ) (P : (V → Bool) → Prop) :
    ppr (fun _ : V => bern (1 - ∏ j, (1 - p j))) P =
      ppr (roundD p) (fun Y => P (fun v => decide (∃ j, Y j v = true))) := by
  rw [← pushD_any_rounds (V := V) p, ← ppr_map]
  unfold ppr roundD
  rw [← pex_curry (fun (_ : V) (j : Fin m) => bern (p j))
      (fun w => if P (fun v => decide (∃ j, w (v, j) = true)) then 1 else 0),
    ← pex_curry (fun (j : Fin m) (_ : V) => bern (p j))
      (fun w => if P (fun v => decide (∃ j, w (j, v) = true)) then 1 else 0),
    pex_reindex (Equiv.prodComm (Fin m) V)]
  rfl

end rounds

end

end Lovasz
