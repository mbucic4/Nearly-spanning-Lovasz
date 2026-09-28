module
public import RequestProject.Lifting
public import RequestProject.Nilpotent


@[expose] public section

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# Near-linear paths in Cayley graphs (Theorem 3.17)

The two results the paper imports are stated as explicit hypotheses:
* `CycleMatchingTheorem` — Theorem 1.2 (proved in Section 2 of the paper);
* `TesseraTointonCayley` — Theorem 3.16, the Cayley form of the finitary structure theorem of
  Tessera and Tointon.
-/

namespace Lovasz

/-- **Theorem 3.16** (Tessera–Tointon, Cayley form).  For every `0 < λ < 1` there are
integers `c, k, n₀` such that for every connected Cayley graph `X = Cay(H, S)` with
`|H| = n ≥ n₀` there is `N ◁ H` such that
(i) every coset of `N` has ambient diameter at most `n^λ` in `X`, and
(ii) `H/N` has a normal nilpotent subgroup of class at most `c` and index at most `k`. -/
def TesseraTointonCayley : Prop :=
  ∀ lam : ℝ, 0 < lam → lam < 1 → ∃ c k n₀ : ℕ, ∀ (H : Type) [Group H] [Finite H] (S : Set H),
    (cay S).Connected → n₀ ≤ Nat.card H →
    ∃ N : Subgroup H, ∃ _ : N.Normal,
      (∀ x y : H, (x : H ⧸ N) = y → ((cay S).dist x y : ℝ) ≤ (Nat.card H : ℝ) ^ lam) ∧
      ∃ K : Subgroup (H ⧸ N), K.Normal ∧
        (⊤ : Subgroup K).lowerCentralSeries c = ⊥ ∧ K.index ≤ k

/-- Asymptotic absorption of constants and logarithms. -/
lemma eventually_bound (a : ℝ) (K : ℕ) (ε : ℝ) (ha : 0 < a) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (n : ℝ) ^ (1 - ε) + 1 ≤ a * (n : ℝ) ^ (1 - ε / 2) / Real.log (2 * n) ^ K := by
  have h1 := (isLittleO_log_rpow_rpow_atTop (K : ℝ) (half_pos hε)).comp_tendsto
    (Filter.tendsto_id.const_mul_atTop' (show (0:ℝ) < 2 by norm_num))
  have h2 := h1.bound (show 0 < a / (4 * 2 ^ (ε / 2)) by positivity)
  have h3 := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually h2
  have h4 := h3.and (Filter.eventually_ge_atTop 1)
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 h4
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨hb, hn1⟩ := hn₀ n hn
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  simp only [Function.comp, id] at hb
  have hlog : 0 < Real.log (2 * n) := Real.log_pos (by linarith)
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity),
    Real.rpow_natCast, Real.mul_rpow (by norm_num) (by linarith)] at hb
  have hb' : Real.log (2 * n) ^ K ≤ a / 4 * n ^ (ε / 2) := by
    calc _ ≤ a / (4 * 2 ^ (ε / 2)) * (2 ^ (ε / 2) * n ^ (ε / 2)) := hb
      _ = a / 4 * n ^ (ε / 2) := by field_simp
  rw [le_div_iff₀ (by positivity)]
  have hp : (1:ℝ) ≤ n ^ (1 - ε) := Real.one_le_rpow hn1' (by linarith)
  have hsplit : (n : ℝ) ^ (1 - ε / 2) = n ^ (1 - ε) * n ^ (ε / 2) := by
    rw [← Real.rpow_add (by linarith)]; ring_nf
  rw [hsplit]
  nlinarith [Real.rpow_nonneg (show (0:ℝ) ≤ n by linarith) (ε / 2), pow_pos hlog K]

/-- The numerical bookkeeping at the end of the proof of Theorem 3.17 (case `m ≥ 2`). -/
lemma final_arith (ε a cη n m q R pY pX : ℝ) (c : ℕ) (ha : 0 < a) (hcη : 0 < cη)
    (hn : n = q * m) (hm : 2 ≤ m) (hq : 1 ≤ q) (hR1 : 1 ≤ R) (hR : R ≤ n ^ (ε / 16))
    (hY : a * q ^ (1 - ε / 4) / Real.log (2 * q) ^ (2 * c) ≤ pY)
    (hX : cη * m ^ (1 - ε / 4) * pY / (R * Real.log (2 * m)) ^ 4 ≤ pX) :
    cη * a * n ^ (1 - ε / 2) / Real.log (2 * n) ^ (2 * c + 4) ≤ pX := by
  have hn1 : 2 ≤ n := by rw [hn]; nlinarith
  have hlq : 0 < Real.log (2 * q) := Real.log_pos (by linarith)
  have hlm : 0 < Real.log (2 * m) := Real.log_pos (by linarith)
  have hlqn : Real.log (2 * q) ≤ Real.log (2 * n) :=
    Real.log_le_log (by linarith) (by rw [hn]; nlinarith)
  have hlmn : Real.log (2 * m) ≤ Real.log (2 * n) :=
    Real.log_le_log (by linarith) (by rw [hn]; nlinarith)
  refine le_trans ?_ hX
  have hpY : 0 ≤ a * q ^ (1 - ε / 4) / Real.log (2 * q) ^ (2 * c) := by positivity
  have e : m ^ (1 - ε / 4) * q ^ (1 - ε / 4) = n ^ (1 - ε / 2) * (n ^ (ε / 16)) ^ 4 := by
    rw [← Real.mul_rpow (by linarith) (by linarith), mul_comm m q, ← hn,
      ← Real.rpow_natCast, ← Real.rpow_mul (by linarith), ← Real.rpow_add (by linarith)]
    ring_nf
  have hL : 0 < Real.log (2 * n) := Real.log_pos (by linarith)
  have hnp : 0 < n ^ (ε / 16) := by positivity
  calc cη * a * n ^ (1 - ε / 2) / Real.log (2 * n) ^ (2 * c + 4)
      = cη * (m ^ (1 - ε / 4) * q ^ (1 - ε / 4)) * a /
          (Real.log (2 * n) ^ (2 * c) * (n ^ (ε / 16) * Real.log (2 * n)) ^ 4) := by
        rw [e]; field_simp; ring
    _ = cη * m ^ (1 - ε / 4) * (a * q ^ (1 - ε / 4) / Real.log (2 * n) ^ (2 * c)) /
          (n ^ (ε / 16) * Real.log (2 * n)) ^ 4 := by
        field_simp
    _ ≤ cη * m ^ (1 - ε / 4) * (a * q ^ (1 - ε / 4) / Real.log (2 * q) ^ (2 * c)) /
          (R * Real.log (2 * m)) ^ 4 := by
        gcongr
    _ ≤ cη * m ^ (1 - ε / 4) * pY / (R * Real.log (2 * m)) ^ 4 := by gcongr

/-- The numerical bookkeeping at the end of the proof of Theorem 3.17 (case `m = 1`). -/
lemma final_arith_one (ε a b n pY : ℝ) (c : ℕ) (hε : 0 < ε) (hb : 0 < b) (hba : b ≤ a)
    (hn : 2 ≤ n) (hY : a * n ^ (1 - ε / 4) / Real.log (2 * n) ^ (2 * c) ≤ pY) :
    b * n ^ (1 - ε / 2) / Real.log (2 * n) ^ (2 * c + 4) ≤ pY := by
  have hL : 1 ≤ Real.log (2 * n) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  refine le_trans ?_ hY
  have h1 : n ^ (1 - ε / 2) ≤ n ^ (1 - ε / 4) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h2 : Real.log (2 * n) ^ (2 * c) ≤ Real.log (2 * n) ^ (2 * c + 4) :=
    pow_le_pow_right₀ hL (by omega)
  have h3 : 0 < Real.log (2 * n) ^ (2 * c) := by positivity
  have ha : 0 ≤ a := by linarith
  have h4 : 0 ≤ a * n ^ (1 - ε / 4) := by positivity
  calc b * n ^ (1 - ε / 2) / Real.log (2 * n) ^ (2 * c + 4)
      ≤ a * n ^ (1 - ε / 4) / Real.log (2 * n) ^ (2 * c + 4) := by gcongr
    _ ≤ a * n ^ (1 - ε / 4) / Real.log (2 * n) ^ (2 * c) := by gcongr

/-- **Theorem 3.17.** Every connected Cayley graph of order `n` contains a path of length at
least `n^(1-o(1))`: for every `ε > 0` there is `n₀` such that every connected Cayley graph of
a group of order `n ≥ n₀` contains a path with at least `n^(1-ε)` edges. -/
theorem cayley_long_path (h12 : CycleMatchingTheorem) (hTT : TesseraTointonCayley) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (H : Type) [Group H] [Finite H] (S : Set H),
      (cay S).Connected → n₀ ≤ Nat.card H →
      ∃ l : List H, IsPathL (cay S) l ∧ (Nat.card H : ℝ) ^ (1 - ε) ≤ (l.length : ℝ) - 1 := by
  suffices key : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ n₀ : ℕ, ∀ (H : Type) [Group H] [Finite H]
      (S : Set H), (cay S).Connected → n₀ ≤ Nat.card H →
      ∃ l : List H, IsPathL (cay S) l ∧ (Nat.card H : ℝ) ^ (1 - ε) ≤ (l.length : ℝ) - 1 by
    intro ε hε
    by_cases h1 : ε ≤ 1
    · exact key ε hε h1
    · obtain ⟨n₀, hn₀⟩ := key 1 one_pos le_rfl
      refine ⟨max n₀ 1, fun H _ _ S hS hn => ?_⟩
      obtain ⟨l, hl, hlen⟩ := hn₀ H S hS (le_of_max_le_left hn)
      refine ⟨l, hl, le_trans ?_ hlen⟩
      have : (1:ℝ) ≤ Nat.card H := by exact_mod_cast (le_of_max_le_right hn)
      exact Real.rpow_le_rpow_of_exponent_le this (by linarith)
  intro ε hε hε1
  obtain ⟨cη, hcη, hlift⟩ := fibre_lifting h12 (ε / 4) (by positivity) (by linarith)
  obtain ⟨c, k, n1, hTT'⟩ := hTT (ε / 16) (by positivity) (by linarith)
  obtain ⟨a, ha, hvn⟩ := virtually_nilpotent_bound h12 c (max k 1) (le_max_right _ _) (ε / 4)
    (by positivity) (by linarith)
  obtain ⟨n2, hn2⟩ := eventually_bound (min a (cη * a)) (2 * c + 4) ε (by positivity) hε hε1
  refine ⟨max (max n1 n2) 2, fun H _ _ S hS hn => ?_⟩
  obtain ⟨l, hl, hlen⟩ := exists_isPathL_length_eq_pathOrder (cay S)
  refine ⟨l, hl, ?_⟩
  rw [hlen]
  suffices hP : (Nat.card H : ℝ) ^ (1 - ε) + 1 ≤ pathOrder (cay S) by linarith
  refine le_trans (hn2 _ (le_trans (le_max_right _ _) (le_of_max_le_left hn))) ?_
  have hn2' : 2 ≤ Nat.card H := le_of_max_le_right hn
  have hnR : (2 : ℝ) ≤ Nat.card H := by exact_mod_cast hn2'
  obtain ⟨N, hN, hdiam, K, hK, hKc, hKk⟩ :=
    hTT' H S hS (le_trans (le_max_left _ _) (le_of_max_le_left hn))
  have hnmq : Nat.card H = Nat.card (H ⧸ N) * Nat.card N :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hY := hvn (H ⧸ N) ((QuotientGroup.mk : H → H ⧸ N) '' S) K (cay_quot_connected N hS) hKc
    (hKk.trans (le_max_left _ _))
  have hm1 : 1 ≤ Nat.card N := Nat.card_pos
  have hq1 : 1 ≤ Nat.card (H ⧸ N) := Nat.card_pos
  rcases Nat.lt_or_ge (Nat.card N) 2 with hm | hm
  · -- `N` is trivial: `X` and `Y` have the same number of vertices
    have hm' : Nat.card N = 1 := by omega
    rw [hm', mul_one] at hnmq
    rw [← hnmq] at hY
    refine le_trans (final_arith_one ε a _ _ _ c hε (by positivity) (min_le_left _ _) hnR hY) ?_
    exact_mod_cast pathOrder_quot_le S N
  · -- the fibres have ambient diameter at most `R = ⌊n^(ε/16)⌋`
    set R := ⌊(Nat.card H : ℝ) ^ (ε / 16)⌋₊ with hRdef
    have hR1 : 1 ≤ R := by
      rw [hRdef, Nat.one_le_floor_iff]
      exact Real.one_le_rpow (by linarith) (by positivity)
    have hwalk : ∀ x y : H, (x : H ⧸ N) = y → WalkLe (cay S) Set.univ x y R := by
      intro x y hxy
      obtain ⟨p, hp⟩ := (hS.preconnected x y).exists_walk_length_eq_dist
      refine ⟨p.support, p.isChain_adj_support, ?_, ?_, fun _ _ => trivial, ?_⟩
      · cases p <;> simp
      · rw [List.getLast?_eq_some_getLast (by simp), SimpleGraph.Walk.getLast_support]
      · rw [SimpleGraph.Walk.length_support, hp]
        have := Nat.le_floor (hdiam x y hxy)
        omega
    have hX := hlift H S N R hm hR1 hwalk
    have hRle : (R : ℝ) ≤ (Nat.card H : ℝ) ^ (ε / 16) := Nat.floor_le (by positivity)
    refine le_trans ?_ (final_arith ε a cη (Nat.card H) (Nat.card N) (Nat.card (H ⧸ N)) R _ _ c
      ha hcη (by exact_mod_cast hnmq) (by exact_mod_cast hm) (by exact_mod_cast hq1)
      (by exact_mod_cast hR1) hRle hY hX)
    gcongr
    · exact pow_nonneg (Real.log_nonneg (by linarith)) _
    · exact min_le_right _ _

end Lovasz
