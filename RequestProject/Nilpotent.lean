module
public import RequestProject.Abelian

/-!
# Induction on the nilpotency class (Lemma 3.13, Propositions 3.14 and 3.15)

We use Mathlib's indexing of the lower central series: `(⊤ : Subgroup K).lowerCentralSeries 0 = K`, so the
paper's `γ_{i+1}(K)` is `(⊤ : Subgroup K).lowerCentralSeries i`, and "class at most `c`" is
`(⊤ : Subgroup K).lowerCentralSeries c = ⊥`.
-/

@[expose] public section


open Classical
open scoped commutatorElement

namespace Lovasz

/-- The lower central series commutes with surjective homomorphisms. -/
lemma lcs_map_surj {K L : Type*} [Group K] [Group L] (f : K →* L) (hf : Function.Surjective f)
    (c : ℕ) : ((⊤ : Subgroup K).lowerCentralSeries c).map f = (⊤ : Subgroup L).lowerCentralSeries c := by
  rw [Subgroup.map_lowerCentralSeries, Subgroup.map_top_of_surjective f hf]

lemma lcs_quot_eq_bot {K : Type*} [Group K] (c : ℕ) :
    (⊤ : Subgroup (K ⧸ (⊤ : Subgroup K).lowerCentralSeries c)).lowerCentralSeries c = ⊥ := by
  rw [← lcs_map_surj (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)]
  exact (QuotientGroup.map_mk'_self _)

lemma clog_bound (D m : ℕ) (hm : 2 ≤ m) :
    ((1 + D * Nat.clog 2 m : ℕ) : ℝ) ≤ (D + 1) / Real.log 2 * Real.log (2 * m) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := m) (by omega)
  have hc1 : 1 ≤ Nat.clog 2 m := Nat.succ_le_of_lt (Nat.clog_pos (by norm_num) (by omega))
  have h2 : ((Nat.clog 2 m : ℕ) : ℝ) - 1 < Real.log m / Real.log 2 := by
    rw [lt_div_iff₀ hl2]
    have : ((2 : ℝ) ^ (Nat.clog 2 m).pred) < m := by exact_mod_cast h1
    have h3 := Real.log_lt_log (by positivity) this
    rw [Real.log_pow] at h3
    have : (((Nat.clog 2 m).pred : ℕ) : ℝ) = (Nat.clog 2 m : ℝ) - 1 := by
      rw [Nat.pred_eq_sub_one, Nat.cast_sub hc1]; simp
    rw [this] at h3; linarith
  have h4 : Real.log (2 * m) = Real.log 2 + Real.log m :=
    Real.log_mul (by norm_num) (by positivity)
  have hlm : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
  have h5 : (Nat.clog 2 m : ℝ) ≤ Real.log (2 * m) / Real.log 2 := by
    rw [h4, add_div, div_self hl2.ne']; linarith
  have h6 : 1 ≤ Real.log (2 * m) / Real.log 2 := by
    rw [h4, add_div, div_self hl2.ne']; have := div_nonneg hlm hl2.le; linarith
  push_cast
  calc 1 + (D : ℝ) * Nat.clog 2 m ≤ 1 + D * (Real.log (2 * m) / Real.log 2) := by gcongr
    _ ≤ (D + 1) * (Real.log (2 * m) / Real.log 2) := by nlinarith
    _ = (D + 1) / Real.log 2 * Real.log (2 * m) := by ring

lemma step_arith (n m q b pY pX ac d Cc η : ℝ) (c : ℕ) (hc : 1 ≤ c) (hn : n = q * m)
    (hm : 2 ≤ m) (hq : 1 ≤ q) (hb : 1 ≤ b) (hbC : b ≤ Cc * Real.log (2 * n)) (hac : 0 < ac)
    (hd : 0 < d) (hCc : 0 < Cc) (hY : ac * q ^ (1 - η) / Real.log (2 * q) ^ (2 * (c - 1)) ≤ pY)
    (hX : d * m ^ (1 - η) * pY / b ^ 2 ≤ pX) :
    d * ac / Cc ^ 2 * n ^ (1 - η) / Real.log (2 * n) ^ (2 * c) ≤ pX := by
  have hn2 : 2 ≤ n := by rw [hn]; nlinarith
  have hlq : 0 < Real.log (2 * q) := Real.log_pos (by linarith)
  have hL : 0 < Real.log (2 * n) := Real.log_pos (by linarith)
  have hlqn : Real.log (2 * q) ≤ Real.log (2 * n) :=
    Real.log_le_log (by linarith) (by rw [hn]; nlinarith)
  refine le_trans ?_ hX
  have hpY : 0 ≤ ac * q ^ (1 - η) / Real.log (2 * q) ^ (2 * (c - 1)) := by positivity
  have e : n ^ (1 - η) = m ^ (1 - η) * q ^ (1 - η) := by
    rw [← Real.mul_rpow (by linarith) (by linarith), hn, mul_comm]
  have e2 : Real.log (2 * n) ^ (2 * c) =
      Real.log (2 * n) ^ (2 * (c - 1)) * Real.log (2 * n) ^ 2 := by
    rw [← pow_add]; congr 1; omega
  calc d * ac / Cc ^ 2 * n ^ (1 - η) / Real.log (2 * n) ^ (2 * c)
      = d * m ^ (1 - η) * (ac * q ^ (1 - η) / Real.log (2 * n) ^ (2 * (c - 1))) /
          (Cc * Real.log (2 * n)) ^ 2 := by
        rw [e, e2]; field_simp
    _ ≤ d * m ^ (1 - η) * (ac * q ^ (1 - η) / Real.log (2 * q) ^ (2 * (c - 1))) / b ^ 2 := by
        gcongr
    _ ≤ d * m ^ (1 - η) * pY / b ^ 2 := by gcongr

/-- Increasing the logarithmic exponent by two costs at most a factor `(log 2)⁻²`. -/
lemma log_pow_step (n pX a η : ℝ) (e : ℕ) (hn : 1 ≤ n) (ha : 0 < a)
    (h : a * n ^ (1 - η) / Real.log (2 * n) ^ e ≤ pX) :
    a * Real.log 2 ^ 2 * n ^ (1 - η) / Real.log (2 * n) ^ (e + 2) ≤ pX := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : Real.log 2 ≤ Real.log (2 * n) := Real.log_le_log (by norm_num) (by linarith)
  refine le_trans ?_ h
  have hLp : 0 < Real.log (2 * n) := by linarith
  rw [pow_add, div_le_div_iff₀ (by positivity) (by positivity)]
  have : 0 ≤ a * n ^ (1 - η) * Real.log (2 * n) ^ e := by positivity
  have h2 : Real.log 2 ^ 2 ≤ Real.log (2 * n) ^ 2 := by gcongr
  nlinarith

/-- Letters `T ∪ T⁻¹`. -/
def letters {K : Type*} [Group K] (T : Set K) : Set K := {t | t ∈ T ∨ t⁻¹ ∈ T}

/-- Left-normed commutators `⁅⋯⁅⁅t₀, t₁⁆, t₂⁆, …, t_j⁆` of letters. -/
def commSet {K : Type*} [Group K] (T : Set K) : ℕ → Set K
  | 0 => letters T
  | j + 1 => {g | ∃ x ∈ commSet T j, ∃ t ∈ letters T, g = ⁅x, t⁆}

lemma lcs_succ_eq {K : Type*} [Group K] (j : ℕ) :
    (⊤ : Subgroup K).lowerCentralSeries (j + 1) = ⁅(⊤ : Subgroup K).lowerCentralSeries j, ⊤⁆ := rfl

lemma commSet_sub_lcs {K : Type*} [Group K] (T : Set K) :
    ∀ j, commSet T j ⊆ (⊤ : Subgroup K).lowerCentralSeries j
  | 0 => fun _ _ => by simp [lowerCentralSeries_zero]
  | j + 1 => by
    rintro g ⟨x, hx, t, -, rfl⟩
    rw [lcs_succ_eq]
    exact Subgroup.commutator_mem_commutator (commSet_sub_lcs T j hx) (Subgroup.mem_top t)

/-- `γ_{j+1}(K)` is generated modulo `γ_{j+2}(K)` by left-normed commutators of generators. -/
lemma lcs_eq_closure_sup {K : Type*} [Group K] (T : Set K) (hT : Subgroup.closure T = ⊤) :
    ∀ j, (⊤ : Subgroup K).lowerCentralSeries j = Subgroup.closure (commSet T j) ⊔ (⊤ : Subgroup K).lowerCentralSeries (j + 1)
  | 0 => by
    rw [lowerCentralSeries_zero, eq_comm, eq_top_iff, ← hT]
    exact le_sup_of_le_left (Subgroup.closure_mono fun t ht => Or.inl ht)
  | j + 1 => by
    have ih := lcs_eq_closure_sup T hT j
    set M := Subgroup.closure (commSet T (j + 1)) ⊔ (⊤ : Subgroup K).lowerCentralSeries (j + 2) with hM
    have hMle : M ≤ (⊤ : Subgroup K).lowerCentralSeries (j + 1) :=
      sup_le ((Subgroup.closure_le _).2 (commSet_sub_lcs T (j+1)))
        ((⊤ : Subgroup K).lowerCentralSeries_antitone (Nat.le_succ _))
    refine le_antisymm ?_ hMle
    have hcomm2 : ∀ g ∈ (⊤ : Subgroup K).lowerCentralSeries (j + 1), ∀ z : K, ⁅g, z⁆ ∈ M := fun g hg z =>
      Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator hg (Subgroup.mem_top z))
    have hconj : ∀ m ∈ M, ∀ g : K, g * m * g⁻¹ ∈ M := by
      intro m hm g
      have h1 : g * m * g⁻¹ = ⁅m, g⁆⁻¹ * m := by simp only [commutatorElement_def]; group
      rw [h1]
      exact M.mul_mem (M.inv_mem (hcomm2 m (hMle hm) g)) hm
    have step1 : ∀ x ∈ commSet T j, ∀ z : K, ⁅x, z⁆ ∈ M := by
      intro x hx z
      have hz : z ∈ Subgroup.closure (letters T) := by
        have : Subgroup.closure T ≤ Subgroup.closure (letters T) :=
          Subgroup.closure_mono fun t ht => Or.inl ht
        exact this (hT ▸ Subgroup.mem_top z)
      induction hz using Subgroup.closure_induction with
      | mem t ht => exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨x, hx, t, ht, rfl⟩)
      | one => simp
      | mul z w _ _ hz hw =>
        have : ⁅x, z * w⁆ = ⁅x, z⁆ * (z * ⁅x, w⁆ * z⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [this]; exact M.mul_mem hz (hconj _ hw z)
      | inv z _ hz =>
        have : ⁅x, z⁻¹⁆ = z⁻¹ * ⁅x, z⁆⁻¹ * z⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [this]; exact hconj _ (M.inv_mem hz) _
    rw [lcs_succ_eq]
    refine Subgroup.commutator_le.2 fun x hx z _ => ?_
    rw [ih, ← Subgroup.closure_eq ((⊤ : Subgroup K).lowerCentralSeries (j + 1)), ← Subgroup.closure_union] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact step1 x hx z
      · exact hcomm2 x hx z
    | one => simp
    | mul x y _ _ hx hy =>
      have : ⁅x * y, z⁆ = x * ⁅y, z⁆ * x⁻¹ * ⁅x, z⁆ := by
        simp only [commutatorElement_def]; group
      rw [this]; exact M.mul_mem (hconj _ hy x) hx
    | inv x _ hx =>
      have : ⁅x⁻¹, z⁆ = x⁻¹ * ⁅x, z⁆⁻¹ * x⁻¹⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [this]; exact hconj _ (M.inv_mem hx) _

/-- Left-normed `(j+1)`-fold commutators of letters are words of length `≤ 3 · 2^j - 2`. -/
lemma commSet_word {K : Type*} [Group K] (T : Set K) :
    ∀ j, ∀ f ∈ commSet T j, ∃ l : List K, l.length ≤ 3 * 2 ^ j - 2 ∧
      (∀ x ∈ l, x ∈ T ∨ x⁻¹ ∈ T) ∧ l.prod = f
  | 0, f, hf => ⟨[f], by simp, by simpa [commSet, letters] using hf, by simp⟩
  | j + 1, f, hf => by
    obtain ⟨x, hx, t, ht, rfl⟩ := hf
    obtain ⟨l, hlen, hl, hprod⟩ := commSet_word T j x hx
    refine ⟨l ++ [t] ++ (l.map (·⁻¹)).reverse ++ [t⁻¹], ?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_map, List.length_reverse, List.length_singleton]
      have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
      rw [pow_succ]; omega
    · intro y hy
      simp only [List.mem_append, List.mem_singleton, List.mem_map, List.mem_reverse] at hy
      rcases hy with ((hy | rfl) | ⟨z, hz, rfl⟩) | rfl
      · exact hl y hy
      · exact ht
      · rcases hl z hz with h | h
        · right; simpa using h
        · left; exact h
      · rcases ht with h | h
        · right; simpa using h
        · left; exact h
    · rw [List.prod_append, List.prod_append, List.prod_append, ← List.prod_inv_reverse, hprod]
      simp [commutatorElement_def]

/-- **Lemma 3.13.** Let `T` generate `K` and suppose `γ_{c+2}(K) = 1`.  Then `A = γ_{c+1}(K)`
is central and is generated by elements which are products of at most `3 · 2^c - 2` letters
from `T ∪ T⁻¹` (left-normed commutators of generators). -/
theorem lcs_short_generators {K : Type*} [Group K] (T : Set K) (hT : Subgroup.closure T = ⊤)
    (c : ℕ) (hc : (⊤ : Subgroup K).lowerCentralSeries (c + 1) = ⊥) :
    (∀ a ∈ (⊤ : Subgroup K).lowerCentralSeries c, ∀ g : K, a * g = g * a) ∧
      ∃ F : Set K, Subgroup.closure F = (⊤ : Subgroup K).lowerCentralSeries c ∧
        ∀ f ∈ F, ∃ l : List K, l.length ≤ 3 * 2 ^ c - 2 ∧ (∀ x ∈ l, x ∈ T ∨ x⁻¹ ∈ T) ∧
          l.prod = f := by
  refine ⟨fun a ha g => ?_, commSet T c, ?_, commSet_word T c⟩
  · have : ⁅a, g⁆ ∈ (⊤ : Subgroup K).lowerCentralSeries (c + 1) := by
      rw [lcs_succ_eq]; exact Subgroup.commutator_mem_commutator ha (Subgroup.mem_top g)
    rw [hc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  · rw [lcs_eq_closure_sup T hT c, hc, sup_bot_eq]

/-- **Proposition 3.14.** For `c ≥ 1`, every connected Cayley graph `C` of a finite nilpotent
group `K` of class at most `c` satisfies `p(C) ≥ a |K|^(1-η) / (log (2|K|))^(2(c-1))`. -/
theorem nilpotent_bound (h12 : CycleMatchingTheorem) (c : ℕ) (hc : 1 ≤ c) (η : ℝ)
    (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ a : ℝ, 0 < a ∧ ∀ (K : Type) [Group K] [Finite K] (T : Set K), (cay T).Connected →
      (⊤ : Subgroup K).lowerCentralSeries c = ⊥ →
      a * (Nat.card K : ℝ) ^ (1 - η) / Real.log (2 * Nat.card K) ^ (2 * (c - 1)) ≤
        pathOrder (cay T) := by
  induction c, hc using Nat.le_induction with
  | base =>
    refine ⟨1, one_pos, fun K _ _ T hT hK => ?_⟩
    have hcomm : ∀ a b : K, a * b = b * a := by
      intro a b
      have : ⁅a, b⁆ ∈ (⊤ : Subgroup K).lowerCentralSeries 1 := by
        rw [lowerCentralSeries_one]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [hK, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    obtain ⟨l, hl, hall⟩ := abelian_hamiltonian hcomm T hT
    have := Fintype.ofFinite K
    have hcard : Nat.card K ≤ l.length := by
      rw [Nat.card_eq_fintype_card, ← List.toFinset_card_of_nodup hl.2]
      exact Finset.card_le_card (fun a _ => List.mem_toFinset.2 (hall a))
    have h1 : (Nat.card K : ℝ) ^ (1 - η) ≤ Nat.card K := by
      have : (1 : ℝ) ≤ Nat.card K := by exact_mod_cast Nat.card_pos
      calc (Nat.card K : ℝ) ^ (1 - η) ≤ (Nat.card K : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le this (by linarith)
        _ = Nat.card K := Real.rpow_one _
    simp only [one_mul, Nat.sub_self, mul_zero, pow_zero, div_one]
    calc (Nat.card K : ℝ) ^ (1 - η) ≤ Nat.card K := h1
      _ ≤ l.length := by exact_mod_cast hcard
      _ ≤ pathOrder (cay T) := by exact_mod_cast hl.length_le_pathOrder
  | succ c hc ih =>
    obtain ⟨ac, hac, hbd⟩ := ih
    obtain ⟨d, hd, hab⟩ := abelian_lifting h12 η hη0 hη1
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    set D : ℕ := 3 * 2 ^ c - 2 with hD
    set Cc : ℝ := (D + 1) / Real.log 2 with hCc
    have hCc0 : 0 < Cc := by positivity
    refine ⟨min (ac * Real.log 2 ^ 2) (d * ac / Cc ^ 2), by positivity,
      fun K _ _ T hT hK => ?_⟩
    have hn1 : (1 : ℝ) ≤ Nat.card K := by exact_mod_cast Nat.card_pos
    have hexp : 2 * (c + 1 - 1) = 2 * (c - 1) + 2 := by omega
    by_cases hA : (⊤ : Subgroup K).lowerCentralSeries c = ⊥
    · have h := log_pow_step _ _ _ _ _ hn1 hac (hbd K T hT hA)
      rw [← hexp] at h
      refine le_trans ?_ h
      gcongr
      · exact pow_nonneg (Real.log_nonneg (by linarith)) _
      · exact min_le_left _ _
    · obtain ⟨hcent, F, hF, hFw⟩ := lcs_short_generators T (cay_connected_iff.1 hT) c hK
      set A := (⊤ : Subgroup K).lowerCentralSeries c with hAdef
      have hm : 2 ≤ Nat.card A := by
        have := (Subgroup.one_lt_card_iff_ne_bot A).2 hA
        omega
      have hY := hbd (K ⧸ A) ((QuotientGroup.mk : K → K ⧸ A) '' T) (cay_quot_connected A hT)
        (lcs_quot_eq_bot c)
      have hX := hab K T A D (fun a ha b _ => hcent a ha b) hm ⟨F, hF, fun f hf => by
        obtain ⟨l, hlen, hl, hprod⟩ := hFw f hf
        rw [← hprod]
        exact (walkLe_of_word T l hl).mono_len hlen⟩
      have hnmq : Nat.card K = Nat.card (K ⧸ A) * Nat.card A :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup A
      have hbC := clog_bound D (Nat.card A) hm
      have hmn : Real.log (2 * (Nat.card A : ℝ)) ≤ Real.log (2 * Nat.card K) := by
        apply Real.log_le_log (by positivity)
        have : Nat.card A ≤ Nat.card K := by
          rw [hnmq]; exact Nat.le_mul_of_pos_left _ Nat.card_pos
        have : (Nat.card A : ℝ) ≤ Nat.card K := by exact_mod_cast this
        linarith
      have hstep := step_arith (Nat.card K) (Nat.card A) (Nat.card (K ⧸ A))
        ((1 + D * Nat.clog 2 (Nat.card A) : ℕ) : ℝ) _ _ ac d Cc η c hc
        (by exact_mod_cast hnmq) (by exact_mod_cast hm) (by exact_mod_cast Nat.card_pos)
        (by exact_mod_cast (show 1 ≤ 1 + D * Nat.clog 2 (Nat.card A) by omega))
        (hbC.trans (by gcongr)) hac hd hCc0 hY hX
      have hexp' : 2 * (c + 1 - 1) = 2 * c := by omega
      rw [hexp']
      refine le_trans ?_ hstep
      gcongr
      · exact pow_nonneg (Real.log_nonneg (by linarith)) _
      · exact min_le_right _ _

lemma index_arith (n n' k a P η : ℝ) (e : ℕ) (hn' : 1 ≤ n') (hk : 1 ≤ k) (hnn : n ≤ k * n')
    (hn'n : n' ≤ n) (ha : 0 < a) (hη0 : 0 < η) (hη1 : η < 1)
    (h : a * n' ^ (1 - η) / Real.log (2 * n') ^ e ≤ P) :
    a / k * n ^ (1 - η) / Real.log (2 * n) ^ e ≤ P := by
  refine le_trans ?_ h
  have hl' : 0 < Real.log (2 * n') := Real.log_pos (by linarith)
  have hll : Real.log (2 * n') ≤ Real.log (2 * n) := Real.log_le_log (by linarith) (by linarith)
  have h1 : n ^ (1 - η) ≤ k * n' ^ (1 - η) := by
    calc n ^ (1 - η) ≤ (k * n') ^ (1 - η) := Real.rpow_le_rpow (by linarith) hnn (by linarith)
      _ = k ^ (1 - η) * n' ^ (1 - η) := Real.mul_rpow (by linarith) (by linarith)
      _ ≤ k * n' ^ (1 - η) := by
        gcongr
        calc k ^ (1 - η) ≤ k ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hk (by linarith)
          _ = k := Real.rpow_one k
  have h2 : a / k * n ^ (1 - η) ≤ a * n' ^ (1 - η) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith [Real.rpow_nonneg (show (0:ℝ) ≤ n' by linarith) (1 - η)]
  calc a / k * n ^ (1 - η) / Real.log (2 * n) ^ e ≤ a * n' ^ (1 - η) / Real.log (2 * n) ^ e := by
        gcongr
        exact pow_nonneg (by linarith) _
    _ ≤ a * n' ^ (1 - η) / Real.log (2 * n') ^ e := by
        gcongr

/-- **Proposition 3.15.** If `H` contains a nilpotent subgroup of class at most `c` and index
at most `k`, then every connected Cayley graph `X` of `H` satisfies
`p(X) ≥ a |H|^(1-η) / (log (2|H|))^(2c)`. -/
theorem virtually_nilpotent_bound (h12 : CycleMatchingTheorem) (c k : ℕ) (hk : 1 ≤ k) (η : ℝ)
    (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ a : ℝ, 0 < a ∧ ∀ (H : Type) [Group H] [Finite H] (S : Set H) (K : Subgroup H),
      (cay S).Connected → (⊤ : Subgroup K).lowerCentralSeries c = ⊥ → K.index ≤ k →
      a * (Nat.card H : ℝ) ^ (1 - η) / Real.log (2 * Nat.card H) ^ (2 * c) ≤
        pathOrder (cay S) := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · refine ⟨1 / k, by positivity, fun H _ _ S K hS hK hKk => ?_⟩
    have hK1 : Nat.card K = 1 := by
      rw [lowerCentralSeries_zero] at hK
      rw [← Subgroup.card_top (G := K), hK, Subgroup.card_bot]
    have hH : Nat.card H ≤ k := by rw [← K.index_mul_card, hK1, mul_one]; exact hKk
    have hn1 : (1 : ℝ) ≤ Nat.card H := by exact_mod_cast Nat.card_pos
    have hP : (1 : ℝ) ≤ pathOrder (cay S) := by exact_mod_cast one_le_pathOrder (cay S)
    simp only [mul_zero, pow_zero, div_one]
    have h1 : (Nat.card H : ℝ) ^ (1 - η) ≤ Nat.card H := by
      calc (Nat.card H : ℝ) ^ (1 - η) ≤ (Nat.card H : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
        _ = Nat.card H := Real.rpow_one _
    have hk' : (Nat.card H : ℝ) ≤ k := by exact_mod_cast hH
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    rw [one_div, inv_mul_le_iff₀ hk0]
    nlinarith
  · obtain ⟨a, ha, hnb⟩ := nilpotent_bound h12 c hc η hη0 hη1
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    refine ⟨a / k * Real.log 2 ^ 2, by positivity, fun H _ _ S K hS hK hKk => ?_⟩
    have := Fintype.ofFinite H
    obtain ⟨T', hT', hlift, -⟩ := tree_contraction S K Finset.univ (by simp)
      (fun u _ v _ => by simpa using reachIn_univ_of_reachable (hS.preconnected u v))
      Finset.univ_nonempty
    have hC := hnb K T' hT' hK
    have hp : pathOrder (cay T') ≤ pathOrder (cay S) := by
      obtain ⟨l, hl, hlen⟩ := exists_isPathL_length_eq_pathOrder (cay T')
      obtain ⟨P, hP, -, hPl⟩ := hlift l hl
      rw [← hlen]; exact hPl.trans hP.length_le_pathOrder
    have hcardK : (1 : ℝ) ≤ Nat.card K := by exact_mod_cast Nat.card_pos
    have hHK : (Nat.card H : ℝ) ≤ k * Nat.card K := by
      rw [← K.index_mul_card]; push_cast
      gcongr
    have hKH : (Nat.card K : ℝ) ≤ Nat.card H := by
      rw [← K.index_mul_card]; push_cast
      have : (1 : ℝ) ≤ K.index := by exact_mod_cast Nat.one_le_iff_ne_zero.2 K.index_ne_zero_of_finite
      nlinarith
    have h1 := index_arith _ _ k a _ η _ hcardK (by exact_mod_cast hk) hHK hKH ha hη0 hη1 hC
    have h2 := log_pow_step _ _ _ η _ (hcardK.trans hKH) (by positivity) h1
    have hexp : 2 * (c - 1) + 2 = 2 * c := by omega
    rw [hexp] at h2
    exact h2.trans (by exact_mod_cast hp)

end Lovasz
