module
public import Mathlib

/-!
# Finite product probability spaces

A finite product probability space is given by a finite index type `ι`, a finite value type
`κ` and, for every coordinate `i`, a probability vector `μ i : κ → ℝ`.  Outcomes are functions
`x : ι → κ` with weight `∏ i, μ i (x i)`.  We develop expectations, probabilities, the union
bound, Markov's inequality, conditioning on one coordinate, pushforwards along coordinatewise
maps, regrouping of coordinates, Chernoff-type tail bounds and monotonicity of up-closed events
in the Bernoulli parameters.
-/

@[expose] public section


open scoped BigOperators
open Classical

namespace Lovasz

noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The weight of an outcome in the product space. -/
def pwt (μ : ι → κ → ℝ) (x : ι → κ) : ℝ := ∏ i, μ i (x i)

/-- Expectation in the product space. -/
def pex (μ : ι → κ → ℝ) (f : (ι → κ) → ℝ) : ℝ := ∑ x, pwt μ x * f x

/-- Probability of an event in the product space. -/
def ppr (μ : ι → κ → ℝ) (P : (ι → κ) → Prop) : ℝ := pex μ (fun x => if P x then 1 else 0)

/-- `μ` is a family of probability vectors. -/
def IsPD (μ : ι → κ → ℝ) : Prop := (∀ i k, 0 ≤ μ i k) ∧ ∀ i, ∑ k, μ i k = 1

/-- The Bernoulli distribution with parameter `q` on `Bool`. -/
def bern (q : ℝ) (b : Bool) : ℝ := if b then q else 1 - q

omit [Fintype ι] in
lemma isPD_bern {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) : IsPD (fun (_ : ι) => bern q) := by
  refine ⟨fun i k => ?_, fun i => ?_⟩
  · cases k <;> simp [bern] <;> linarith
  · simp [bern]

section basic

variable {μ : ι → κ → ℝ}

lemma pwt_nonneg (hμ : IsPD μ) (x : ι → κ) : 0 ≤ pwt μ x :=
  Finset.prod_nonneg fun i _ => hμ.1 i (x i)

lemma sum_pwt (hμ : IsPD μ) : ∑ x, pwt μ x = 1 := by
  unfold pwt
  rw [← Fintype.prod_sum (fun i k => μ i k)]
  simp [hμ.2]

lemma pex_prod (g : ι → κ → ℝ) :
    pex μ (fun x => ∏ i, g i (x i)) = ∏ i, ∑ k, μ i k * g i k := by
  unfold pex pwt
  rw [Fintype.prod_sum (fun i k => μ i k * g i k)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.prod_mul_distrib]

lemma pex_add (f g : (ι → κ) → ℝ) : pex μ (fun x => f x + g x) = pex μ f + pex μ g := by
  unfold pex; rw [← Finset.sum_add_distrib]; congr 1; ext x; ring

lemma pex_sub (f g : (ι → κ) → ℝ) : pex μ (fun x => f x - g x) = pex μ f - pex μ g := by
  unfold pex; rw [← Finset.sum_sub_distrib]; congr 1; ext x; ring

lemma pex_const_mul (c : ℝ) (f : (ι → κ) → ℝ) : pex μ (fun x => c * f x) = c * pex μ f := by
  unfold pex; rw [Finset.mul_sum]; congr 1; ext x; ring

lemma pex_sum {α : Type*} (s : Finset α) (f : α → (ι → κ) → ℝ) :
    pex μ (fun x => ∑ a ∈ s, f a x) = ∑ a ∈ s, pex μ (f a) := by
  unfold pex
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]

lemma pex_const (hμ : IsPD μ) (c : ℝ) : pex μ (fun _ => c) = c := by
  unfold pex; rw [← Finset.sum_mul, sum_pwt hμ, one_mul]

lemma pex_mono (hμ : IsPD μ) {f g : (ι → κ) → ℝ} (h : ∀ x, f x ≤ g x) : pex μ f ≤ pex μ g :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (pwt_nonneg hμ x)

lemma pex_nonneg (hμ : IsPD μ) {f : (ι → κ) → ℝ} (h : ∀ x, 0 ≤ f x) : 0 ≤ pex μ f := by
  simpa [pex_const hμ] using pex_mono hμ (f := fun _ => 0) h

lemma ppr_nonneg (hμ : IsPD μ) (P : (ι → κ) → Prop) : 0 ≤ ppr μ P :=
  pex_nonneg hμ fun x => by split_ifs <;> norm_num

lemma ppr_mono (hμ : IsPD μ) {P Q : (ι → κ) → Prop} (h : ∀ x, P x → Q x) :
    ppr μ P ≤ ppr μ Q :=
  pex_mono hμ fun x => by
    by_cases hp : P x
    · simp [hp, h x hp]
    · simp only [hp, if_false]; split_ifs <;> norm_num

lemma ppr_le_one (hμ : IsPD μ) (P : (ι → κ) → Prop) : ppr μ P ≤ 1 := by
  have := ppr_mono hμ (P := P) (Q := fun _ => True) (fun _ _ => trivial)
  simpa [ppr, pex_const hμ] using this

lemma ppr_true (hμ : IsPD μ) : ppr μ (fun _ => True) = 1 := by
  simp [ppr, pex_const hμ]

lemma ppr_not (hμ : IsPD μ) (P : (ι → κ) → Prop) : ppr μ (fun x => ¬ P x) = 1 - ppr μ P := by
  rw [← ppr_true hμ, ppr, ppr, ppr, ← pex_sub]
  congr 1; ext x; by_cases h : P x <;> simp [h]

lemma ppr_or_le (hμ : IsPD μ) (P Q : (ι → κ) → Prop) :
    ppr μ (fun x => P x ∨ Q x) ≤ ppr μ P + ppr μ Q := by
  rw [ppr, ppr, ppr, ← pex_add]
  refine pex_mono hμ fun x => ?_
  by_cases hp : P x <;> by_cases hq : Q x <;> simp [hp, hq]

lemma ppr_exists_le (hμ : IsPD μ) {α : Type*} (s : Finset α) (P : α → (ι → κ) → Prop) :
    ppr μ (fun x => ∃ a ∈ s, P a x) ≤ ∑ a ∈ s, ppr μ (P a) := by
  unfold ppr
  rw [← pex_sum]
  refine pex_mono hμ fun x => ?_
  split_ifs with h
  · obtain ⟨a, ha, hP⟩ := h
    calc (1 : ℝ) = if P a x then 1 else 0 := by simp [hP]
      _ ≤ ∑ a ∈ s, if P a x then 1 else 0 :=
        Finset.single_le_sum (f := fun a => if P a x then (1:ℝ) else 0)
          (fun b _ => by split_ifs <;> norm_num) ha
  · exact Finset.sum_nonneg fun b _ => by split_ifs <;> norm_num

lemma exists_of_ppr_pos {P : (ι → κ) → Prop} (h : 0 < ppr μ P) : ∃ x, P x := by
  by_contra hne
  push_neg at hne
  simp [ppr, pex, hne] at h

lemma ppr_and_ge (hμ : IsPD μ) (P Q : (ι → κ) → Prop) :
    ppr μ P - ppr μ (fun x => ¬ Q x) ≤ ppr μ (fun x => P x ∧ Q x) := by
  rw [ppr, ppr, ppr, ← pex_sub]
  refine pex_mono hμ fun x => ?_
  by_cases hp : P x <;> by_cases hq : Q x <;> simp [hp, hq]

/-- Markov's inequality. -/
lemma markov (hμ : IsPD μ) {f : (ι → κ) → ℝ} (hf : ∀ x, 0 ≤ f x) {a : ℝ} (ha : 0 < a) :
    ppr μ (fun x => a ≤ f x) ≤ pex μ f / a := by
  rw [le_div_iff₀ ha, ppr, mul_comm, ← pex_const_mul]
  refine pex_mono hμ fun x => ?_
  split_ifs with h
  · linarith
  · simpa using hf x

end basic

section cond

variable {μ : ι → κ → ℝ}

/-- The product of the weights of the coordinates other than `j`. -/
def restWt (μ : ι → κ → ℝ) (j : ι) (y : {i // i ≠ j} → κ) : ℝ := ∏ i : {i // i ≠ j}, μ i (y i)

omit [Fintype κ] in
lemma pwt_split (j : ι) (x : ι → κ) :
    pwt μ x = μ j (x j) * restWt μ j ((Equiv.piSplitAt j (fun _ => κ)) x).2 := by
  unfold pwt restWt
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ j]
  rfl

/-- The conditional expectation given that coordinate `j` takes the value `k`. -/
def condFun (μ : ι → κ → ℝ) (j : ι) (F : (ι → κ) → ℝ) (k : κ) : ℝ :=
  ∑ y, restWt μ j y * F ((Equiv.piSplitAt j (fun _ => κ)).symm (k, y))

lemma pex_eq_sum_condFun (j : ι) (F : (ι → κ) → ℝ) :
    pex μ F = ∑ k, μ j k * condFun μ j F k := by
  unfold pex condFun
  rw [← (Equiv.piSplitAt j (fun _ => κ)).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [pwt_split j]
  simp only [Equiv.apply_symm_apply]
  have : (Equiv.piSplitAt j (fun _ => κ)).symm (k, y) j = k := by
    simp [Equiv.piSplitAt]
  rw [this]; ring

omit [Fintype ι] [Fintype κ] in
lemma piSplitAt_symm_update (j : ι) (a k : κ) (y : {i // i ≠ j} → κ) :
    Function.update ((Equiv.piSplitAt j (fun _ => κ)).symm (a, y)) j k =
      (Equiv.piSplitAt j (fun _ => κ)).symm (k, y) := by
  funext i
  by_cases h : i = j
  · subst h; simp [Equiv.piSplitAt]
  · simp [Equiv.piSplitAt, Function.update, h]

lemma pex_update (hμ : IsPD μ) (j : ι) (F : (ι → κ) → ℝ) (k : κ) :
    pex μ (fun x => F (Function.update x j k)) = condFun μ j F k := by
  rw [pex_eq_sum_condFun j]
  have : ∀ a, condFun μ j (fun x => F (Function.update x j k)) a = condFun μ j F k := by
    intro a
    unfold condFun
    refine Finset.sum_congr rfl fun y _ => ?_
    dsimp only
    rw [piSplitAt_symm_update]
  simp only [this, ← Finset.sum_mul, hμ.2 j, one_mul]

/-- `F` does not depend on coordinate `j`. -/
def IndepOf (F : (ι → κ) → ℝ) (j : ι) : Prop := ∀ x k, F (Function.update x j k) = F x

lemma pex_eq_condFun (hμ : IsPD μ) {F : (ι → κ) → ℝ} {j : ι} (hF : IndepOf F j) (k : κ) :
    pex μ F = condFun μ j F k := by
  rw [← pex_update hμ j F k]
  exact congrArg _ (funext fun x => (hF x k).symm)

lemma pex_indep_mul (hμ : IsPD μ) {F : (ι → κ) → ℝ} {j : ι} (hF : IndepOf F j) (g : κ → ℝ) :
    pex μ (fun x => g (x j) * F x) = (∑ k, μ j k * g k) * pex μ F := by
  rw [pex_eq_sum_condFun j, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : condFun μ j (fun x => g (x j) * F x) k = g k * condFun μ j F k := by
    unfold condFun
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have : (Equiv.piSplitAt j (fun _ => κ)).symm (k, y) j = k := by
      simp [Equiv.piSplitAt]
    dsimp only
    rw [this]; ring
  rw [h1, ← pex_eq_condFun hμ hF k]; ring

omit [Fintype κ] in
lemma restWt_congr {μ' : ι → κ → ℝ} {j : ι} (h : ∀ i, i ≠ j → μ' i = μ i) :
    restWt μ' j = restWt μ j := by
  funext y
  unfold restWt
  exact Finset.prod_congr rfl fun i _ => by rw [h i i.2]

lemma condFun_congr {μ' : ι → κ → ℝ} {j : ι} (h : ∀ i, i ≠ j → μ' i = μ i) :
    condFun μ' j = condFun μ j := by
  funext F k
  unfold condFun
  rw [restWt_congr h]

end cond

section bernoulli

/-- Coordinatewise order on Boolean outcomes. -/
def BLe (x y : ι → Bool) : Prop := ∀ i, x i = true → y i = true

/-- An up-closed event. -/
def UpClosed (P : (ι → Bool) → Prop) : Prop := ∀ x y, BLe x y → P x → P y

lemma ppr_bern_mono_one {q q' : ι → ℝ} (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (hq'0 : ∀ i, 0 ≤ q' i) (hq'1 : ∀ i, q' i ≤ 1) (j : ι) (hj : q j ≤ q' j)
    (hoff : ∀ i, i ≠ j → q' i = q i) {P : (ι → Bool) → Prop} (hP : UpClosed P) :
    ppr (fun i => bern (q i)) P ≤ ppr (fun i => bern (q' i)) P := by
  have hμ : IsPD (fun i => bern (q i)) :=
    ⟨fun i k => (isPD_bern (ι := Unit) (hq0 i) (hq1 i)).1 () k,
      fun i => (isPD_bern (ι := Unit) (hq0 i) (hq1 i)).2 ()⟩
  have hμ' : IsPD (fun i => bern (q' i)) :=
    ⟨fun i k => (isPD_bern (ι := Unit) (hq'0 i) (hq'1 i)).1 () k,
      fun i => (isPD_bern (ι := Unit) (hq'0 i) (hq'1 i)).2 ()⟩
  unfold ppr
  rw [pex_eq_sum_condFun j, pex_eq_sum_condFun j,
    condFun_congr (μ' := fun i => bern (q' i)) (μ := fun i => bern (q i)) (j := j)
      (fun i hi => by simp [hoff i hi])]
  set F : (ι → Bool) → ℝ := fun x => if P x then 1 else 0
  have hmono : condFun (fun i => bern (q i)) j F false ≤
      condFun (fun i => bern (q i)) j F true := by
    rw [← pex_update hμ, ← pex_update hμ]
    refine pex_mono hμ fun x => ?_
    simp only [F]
    by_cases h : P (Function.update x j false)
    · have : P (Function.update x j true) := hP _ _ (fun i hi => by
        by_cases hij : i = j
        · subst hij; simp
        · simpa [Function.update, hij] using hi) h
      simp [h, this]
    · simp only [h, if_false]; split_ifs <;> norm_num
  simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
    Finset.sum_insert, Finset.sum_singleton, bern, if_true, Bool.false_eq_true, if_false]
  nlinarith

/-- Monotonicity of up-closed events in the Bernoulli parameters. -/
lemma ppr_bern_mono {q q' : ι → ℝ} (hq0 : ∀ i, 0 ≤ q i) (hqq' : ∀ i, q i ≤ q' i)
    (hq'1 : ∀ i, q' i ≤ 1) {P : (ι → Bool) → Prop} (hP : UpClosed P) :
    ppr (fun i => bern (q i)) P ≤ ppr (fun i => bern (q' i)) P := by
  let qs : Finset ι → ι → ℝ := fun s i => if i ∈ s then q' i else q i
  have h0 : ∀ s i, 0 ≤ qs s i := fun s i => by
    simp only [qs]; split_ifs
    · exact (hq0 i).trans (hqq' i)
    · exact hq0 i
  have h1 : ∀ s i, qs s i ≤ 1 := fun s i => by
    simp only [qs]; split_ifs
    · exact hq'1 i
    · exact (hqq' i).trans (hq'1 i)
  have key : ∀ s : Finset ι, ppr (fun i => bern (q i)) P ≤ ppr (fun i => bern (qs s i)) P := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [qs]
    | insert j s hj ih =>
      refine ih.trans (ppr_bern_mono_one (h0 s) (h1 s) (h0 _) (h1 _) j ?_ (fun i hi => ?_) hP)
      · simp [qs, hj, hqq' j]
      · simp [qs, hi]
  have := key Finset.univ
  simpa [qs] using this

end bernoulli

section maps

variable {κ' : Type*} [Fintype κ']

/-- The pushforward of a family of distributions along `φ`. -/
def pushD (μ : ι → κ → ℝ) (φ : κ → κ') (i : ι) (b : κ') : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k => φ k = b), μ i k

lemma pex_map (μ : ι → κ → ℝ) (φ : κ → κ') (F : (ι → κ') → ℝ) :
    pex μ (fun x => F (fun i => φ (x i))) = pex (pushD μ φ) F := by
  unfold pex pwt pushD
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := fun x : ι → κ => fun i => φ (x i))]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.prod_univ_sum, Finset.sum_mul]
  have hs : (Finset.univ.filter fun x : ι → κ => (fun i => φ (x i)) = y) =
      Fintype.piFinset (fun i => Finset.univ.filter fun k => φ k = y i) := by
    ext x; simp [Fintype.mem_piFinset, funext_iff]
  rw [hs]
  refine Finset.sum_congr rfl fun x hx => ?_
  have : (fun i => φ (x i)) = y := by
    funext i; simpa using (Fintype.mem_piFinset.1 hx) i
  dsimp only
  rw [this]

omit [Fintype ι] in
lemma isPD_pushD {μ : ι → κ → ℝ} (hμ : IsPD μ) (φ : κ → κ') : IsPD (pushD μ φ) := by
  refine ⟨fun i b => Finset.sum_nonneg fun k _ => hμ.1 i k, fun i => ?_⟩
  unfold pushD
  rw [Finset.sum_fiberwise (s := Finset.univ) (g := φ) (f := fun k => μ i k), hμ.2 i]

lemma ppr_map (μ : ι → κ → ℝ) (φ : κ → κ') (P : (ι → κ') → Prop) :
    ppr μ (fun x => P (fun i => φ (x i))) = ppr (pushD μ φ) P :=
  pex_map μ φ (fun y => if P y then 1 else 0)

/-- Reindexing along an equivalence of index types. -/
lemma pex_reindex {ι' : Type*} [Fintype ι'] (e : ι ≃ ι') (μ : ι' → κ → ℝ)
    (F : (ι' → κ) → ℝ) :
    pex μ F = pex (fun i => μ (e i)) (fun x => F (fun i' => x (e.symm i'))) := by
  unfold pex pwt
  refine Fintype.sum_equiv (Equiv.arrowCongr e.symm (Equiv.refl κ)) _ _ fun x => ?_
  have h1 : ∏ i', μ i' (x i') = ∏ i, μ (e i) (x (e i)) := (e.prod_comp _).symm
  rw [h1]
  simp [Equiv.arrowCongr]

/-- Regrouping the coordinates of a product index `ι × β`. -/
lemma pex_curry {β : Type*} [Fintype β] [DecidableEq β] (ν : ι → β → κ → ℝ) (F : (ι × β → κ) → ℝ) :
    pex (fun p : ι × β => ν p.1 p.2) F =
      pex (fun i (z : β → κ) => ∏ b, ν i b (z b)) (fun X => F (fun p => X p.1 p.2)) := by
  unfold pex pwt
  have := Fintype.sum_equiv (Equiv.curry ι β κ) (fun x => (∏ p, ν p.1 p.2 (x p)) * F x)
    (fun X => (∏ i, ∏ b, ν i b (X i b)) * F (fun p => X p.1 p.2))
    (fun x => by rw [Fintype.prod_prod_type]; rfl)
  convert this using 1
  exact Finset.sum_congr (by congr; exact Subsingleton.elim _ _) fun x _ => rfl

omit [Fintype ι] in
lemma isPD_prod {β : Type*} [Fintype β] [DecidableEq β] {ν : ι → β → κ → ℝ} (hν : ∀ i, IsPD (ν i)) :
    IsPD (fun i (z : β → κ) => ∏ b, ν i b (z b)) := by
  refine ⟨fun i z => Finset.prod_nonneg fun b _ => (hν i).1 b (z b), fun i => ?_⟩
  rw [← Fintype.prod_sum (fun b k => ν i b k)]
  simp [(hν i).2]

end maps

section chernoff

/-- The number of coordinates in `S` equal to `true`. -/
def cntT (S : Finset ι) (x : ι → Bool) : ℕ := (S.filter (fun i => x i = true)).card

lemma prod_ite_pow (S : Finset ι) (x : ι → Bool) (c : ℝ) :
    ∏ i, (if i ∈ S ∧ x i = true then c else 1) = c ^ cntT S x := by
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  congr 1
  unfold cntT
  congr 1; ext i; simp

lemma pex_bern_prod_ite {q : ℝ} (S : Finset ι) (c : ℝ) :
    pex (fun _ => bern q) (fun x => ∏ i, (if i ∈ S ∧ x i = true then c else 1)) =
      (1 - q + q * c) ^ S.card := by
  rw [pex_prod (fun i b => if i ∈ S ∧ b = true then c else 1)]
  have : ∀ i, (∑ k, bern q k * (if i ∈ S ∧ k = true then c else 1)) =
      if i ∈ S then 1 - q + q * c else 1 := by
    intro i
    by_cases hi : i ∈ S
    · simp [bern, hi]; ring
    · simp [bern, hi]
  simp only [this]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  congr 1; congr 1; ext i; simp

/-- Upper-tail Chernoff bound. -/
lemma chernoff_upper {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (S : Finset ι) (a : ℝ) :
    ppr (fun (_ : ι) => bern q) (fun x => a ≤ cntT S x) ≤
      Real.exp ((Real.exp 1 - 1) * q * S.card - a) := by
  have hμ := isPD_bern (ι := ι) hq0 hq1
  have h1 : ppr (fun (_ : ι) => bern q) (fun x => a ≤ cntT S x) ≤
      pex (fun _ => bern q) (fun x => Real.exp (-a) *
        ∏ i, (if i ∈ S ∧ x i = true then Real.exp 1 else 1)) := by
    refine pex_mono hμ fun x => ?_
    rw [prod_ite_pow, ← Real.exp_nat_mul, mul_one, ← Real.exp_add]
    split_ifs with h
    · exact Real.one_le_exp (by linarith)
    · exact (Real.exp_pos _).le
  refine h1.trans ?_
  rw [pex_const_mul, pex_bern_prod_ite]
  have h2 : 1 - q + q * Real.exp 1 ≤ Real.exp ((Real.exp 1 - 1) * q) := by
    have := Real.add_one_le_exp ((Real.exp 1 - 1) * q); linarith
  have h3 : 0 ≤ 1 - q + q * Real.exp 1 := by
    have := Real.exp_pos 1; nlinarith
  calc Real.exp (-a) * (1 - q + q * Real.exp 1) ^ S.card
      ≤ Real.exp (-a) * Real.exp ((Real.exp 1 - 1) * q) ^ S.card :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h3 h2 _) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf

/-- Lower-tail Chernoff bound. -/
lemma chernoff_lower {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (S : Finset ι) (a : ℝ) :
    ppr (fun (_ : ι) => bern q) (fun x => (cntT S x : ℝ) ≤ a) ≤
      Real.exp (a - (1 - Real.exp (-1)) * q * S.card) := by
  have hμ := isPD_bern (ι := ι) hq0 hq1
  have h1 : ppr (fun (_ : ι) => bern q) (fun x => (cntT S x : ℝ) ≤ a) ≤
      pex (fun _ => bern q) (fun x => Real.exp a *
        ∏ i, (if i ∈ S ∧ x i = true then Real.exp (-1) else 1)) := by
    refine pex_mono hμ fun x => ?_
    rw [prod_ite_pow, ← Real.exp_nat_mul, ← Real.exp_add]
    split_ifs with h
    · exact Real.one_le_exp (by linarith)
    · exact (Real.exp_pos _).le
  refine h1.trans ?_
  rw [pex_const_mul, pex_bern_prod_ite]
  have h2 : 1 - q + q * Real.exp (-1) ≤ Real.exp (-(1 - Real.exp (-1)) * q) := by
    have := Real.add_one_le_exp (-(1 - Real.exp (-1)) * q); linarith
  have h3 : 0 ≤ 1 - q + q * Real.exp (-1) := by
    have := Real.exp_pos (-1); nlinarith
  calc Real.exp a * (1 - q + q * Real.exp (-1)) ^ S.card
      ≤ Real.exp a * Real.exp (-(1 - Real.exp (-1)) * q) ^ S.card :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h3 h2 _) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf

end chernoff

end

end Lovasz
