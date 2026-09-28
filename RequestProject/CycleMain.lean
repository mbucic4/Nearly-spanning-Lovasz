module
public import RequestProject.Watkins
public import RequestProject.FlexibleRegularizationProof

/-!
# From long paths to long cycles

Theorem 1.1 of the paper asks for long *cycles*.  The paper deduces it from the path version
(Theorem A.1, Theorem 3.17 in the Cayley case) via Watkins' theorem and a path-to-cycle theorem
for `3`-connected graphs (Bondy–Locke).

This file carries out that reduction.  Watkins' part is proved (`vt_kconnected_three`), and a
degree-two graph is handled directly.  The path-to-cycle step is isolated as the property
`PathToCycleSubpoly`: every finite `3`-connected graph with a long path contains a cycle whose
length is at least the path length to the power `1 - δ`.  The Bondy–Locke theorem (a linear
bound) implies it (`pathToCycleSubpoly_of_linear`).
-/

@[expose] public section


open Classical

namespace Lovasz

/-- **Path-to-cycle property** (any sub-polynomial loss).  For every `δ > 0`, every finite
`3`-connected graph containing a path with `ℓ ≥ L₀` edges contains a cycle with at least
`ℓ ^ (1 - δ)` edges. -/
def PathToCycleSubpoly : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ L₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), KConnected G 3 →
    ∀ l : List V, IsPathL G l → (L₀ : ℝ) ≤ (l.length : ℝ) - 1 →
      ∃ c : List V, IsCycleL G c ∧ ((l.length : ℝ) - 1) ^ (1 - δ) ≤ c.length

/-- **Linear path-to-cycle property** with constant `κ`: every finite `3`-connected graph
containing a path with `ℓ` edges contains a cycle with at least `κ ℓ` edges.  The Bondy–Locke
theorem states this with `κ = 2/5`. -/
def PathToCycleLinear (κ : ℝ) : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), KConnected G 3 →
    ∀ l : List V, IsPathL G l → ∃ c : List V, IsCycleL G c ∧ κ * ((l.length : ℝ) - 1) ≤ c.length

/-- A linear path-to-cycle bound gives the sub-polynomial one. -/
theorem pathToCycleSubpoly_of_linear {κ : ℝ} (hκ : 0 < κ) (h : PathToCycleLinear κ) :
    PathToCycleSubpoly := by
  intro δ hδ
  -- `ℓ^(1-δ) ≤ κ ℓ` once `ℓ ≥ κ^(-1/δ)`
  obtain ⟨L₀, hL₀⟩ : ∃ L₀ : ℕ, ∀ x : ℝ, (L₀ : ℝ) ≤ x → x ^ (1 - δ) ≤ κ * x := by
    obtain ⟨L₀, hL⟩ := exists_nat_ge (max 1 (κ⁻¹ ^ (1 / δ)))
    refine ⟨L₀, fun x hx => ?_⟩
    have hx1 : 1 ≤ x := le_trans (le_trans (le_max_left _ _) hL) hx
    have hx0 : 0 < x := by linarith
    have hxk : κ⁻¹ ^ (1 / δ) ≤ x := le_trans (le_trans (le_max_right _ _) hL) hx
    have h1 : κ⁻¹ ≤ x ^ δ := by
      have := Real.rpow_le_rpow (by positivity) hxk hδ.le
      rwa [← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ hδ.ne', Real.rpow_one]
        at this
    have h2 : x ^ (1 - δ) * x ^ δ = x := by
      rw [← Real.rpow_add hx0]; simp
    have h3 : 0 < x ^ (1 - δ) := Real.rpow_pos_of_pos hx0 _
    calc x ^ (1 - δ) = x ^ (1 - δ) * (κ * κ⁻¹) := by rw [mul_inv_cancel₀ hκ.ne', mul_one]
      _ ≤ x ^ (1 - δ) * (κ * x ^ δ) := by gcongr
      _ = κ * x := by rw [mul_left_comm, h2]
  refine ⟨L₀, fun V _ G hG l hl hlen => ?_⟩
  obtain ⟨c, hc, hcl⟩ := h V G hG l hl
  exact ⟨c, hc, le_trans (hL₀ _ hlen) hcl⟩

section Degree

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma degree_iso (φ : G ≃g G) (v : V) : G.degree (φ v) = G.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  have : G.neighborFinset (φ v) = (G.neighborFinset v).image φ := by
    ext w
    obtain ⟨w', rfl⟩ := φ.surjective w
    simp [SimpleGraph.mem_neighborFinset, φ.map_adj_iff]
  rw [this, Finset.card_image_of_injective _ φ.injective]

/-- A vertex-transitive graph is regular. -/
lemma degree_eq_of_vt (hvt : VertexTransitive G) (u v : V) : G.degree v = G.degree u := by
  obtain ⟨φ, hφ⟩ := hvt u v
  rw [← hφ, degree_iso]

/-- A path with three vertices has a middle vertex of degree at least two. -/
lemma two_le_degree_of_path {a b c : V} {t : List V} (hl : IsPathL G (a :: b :: c :: t)) :
    2 ≤ G.degree b := by
  have hc := hl.1
  rw [List.isChain_cons_cons, List.isChain_cons_cons] at hc
  have hac : a ≠ c := by
    have := hl.2
    simp at this
    exact fun h => this.1.2.1 h
  have hsub : ({a, c} : Finset V) ⊆ G.neighborFinset b := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [SimpleGraph.mem_neighborFinset]
    rcases hx with rfl | rfl
    · exact hc.1.symm
    · exact hc.2.1
  have := Finset.card_le_card hsub
  rw [Finset.card_pair hac, SimpleGraph.card_neighborFinset_eq_degree] at this
  exact this

end Degree

/-- **Long cycles from long paths.**  In a finite connected vertex-transitive graph `X`, every
path with at least three vertices yields a cycle whose length is either at least the path's
number of vertices (degree two), or given by the path-to-cycle property (degree at least three,
where `X` is `3`-connected by Watkins' theorem). -/
theorem vt_cycle_of_path {V : Type} [Fintype V] {X : SimpleGraph V} (hconn : X.Connected)
    (hvt : VertexTransitive X) {l : List V} (hl : IsPathL X l) (h3 : 3 ≤ l.length) :
    (∃ c : List V, IsCycleL X c ∧ l.length ≤ c.length) ∨ KConnected X 3 := by
  obtain ⟨v0⟩ := hconn.nonempty
  set d := X.degree v0
  have hreg : ∀ v, X.degree v = d := fun v => degree_eq_of_vt hvt v0 v
  obtain ⟨a, b, c, t, rfl⟩ : ∃ a b c t, l = a :: b :: c :: t := by
    match l, h3 with
    | a :: b :: c :: t, _ => exact ⟨a, b, c, t, rfl⟩
  have hd2 : 2 ≤ d := by rw [← hreg b]; exact two_le_degree_of_path hl
  rcases Nat.lt_or_ge d 3 with hd | hd
  · -- degree two: a longest path closes up
    left
    have hd2' : ∀ v, X.degree v = 2 := fun v => by rw [hreg v]; omega
    obtain ⟨m, hm, hmlen⟩ := exists_isPathL_length_eq_pathOrder X
    have hle : (a :: b :: c :: t).length ≤ m.length := by rw [hmlen]; exact hl.length_le_pathOrder
    refine ⟨m, isCycleL_of_longest_of_degree_two hd2' hm (fun l' hl' => ?_) (le_trans h3 hle),
      hle⟩
    rw [hmlen]; exact hl'.length_le_pathOrder
  · right
    exact vt_kconnected_three hconn hvt (fun v => by rw [hreg v]; exact hd)

/-- **Theorem 1.1 (conditional on the path-to-cycle property).**  For every `ε > 0` there is
`n₀` such that every connected vertex-transitive graph of order `n ≥ n₀` contains a cycle of
length at least `n^(1-ε)`.  Watkins' theorem and the degree-two case are proved; the only
hypothesis is `PathToCycleSubpoly`. -/
theorem vt_long_cycle_of_pathToCycle (hPC : PathToCycleSubpoly) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (X : SimpleGraph V),
      X.Connected → VertexTransitive X → n₀ ≤ Fintype.card V →
      ∃ (v : V) (c : X.Walk v v), c.IsCycle ∧ (Fintype.card V : ℝ) ^ (1 - ε) ≤ c.length := by
  intro ε hε
  set ε' := min ε (1 / 2) with hε'
  have hε'0 : 0 < ε' := lt_min hε (by norm_num)
  have hε'1 : ε' ≤ 1 / 2 := min_le_right _ _
  have hε'ε : ε' ≤ ε := min_le_left _ _
  set η := ε' / 4 with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨n₁, hn₁⟩ := vt_long_path_unconditional η hη0
  obtain ⟨L₀, hL₀⟩ := hPC η hη0
  obtain ⟨n₂, hn₂⟩ := exists_nat_ge ((max (L₀ : ℝ) 3) ^ 2)
  refine ⟨max (max n₁ n₂) 1, fun V _ X hconn hvt hn => ?_⟩
  set n := Fintype.card V with hndef
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
  have hn2 : ((max (L₀ : ℝ) 3) ^ 2) ≤ n :=
    le_trans hn₂ (by exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn)
  obtain ⟨l, hl, hllen⟩ := hn₁ V X hconn hvt (le_trans (le_trans (le_max_left _ _)
    (le_max_left _ _)) hn)
  -- `n^(1-η) ≥ √n ≥ max L₀ 3`
  have hsq : max (L₀ : ℝ) 3 ≤ (n : ℝ) ^ (1 - η) := by
    have h1 : (n : ℝ) ^ ((1 : ℝ) / 2) ≤ (n : ℝ) ^ (1 - η) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    have h2 : max (L₀ : ℝ) 3 ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := by
      have hm0 : 0 ≤ max (L₀ : ℝ) 3 := le_trans (by norm_num) (le_max_right _ _)
      have := Real.rpow_le_rpow (by positivity) hn2 (by norm_num : (0 : ℝ) ≤ 1 / 2)
      rwa [← Real.rpow_natCast, ← Real.rpow_mul hm0, show ((2 : ℕ) : ℝ) * (1 / 2) = 1 by norm_num,
        Real.rpow_one] at this
    linarith
  have hlen3 : (3 : ℝ) ≤ (l.length : ℝ) - 1 := le_trans (le_trans (le_max_right _ _) hsq) hllen
  have hlenL : (L₀ : ℝ) ≤ (l.length : ℝ) - 1 := le_trans (le_trans (le_max_left _ _) hsq) hllen
  have h3 : 3 ≤ l.length := by
    have : (3 : ℝ) ≤ l.length := by linarith
    exact_mod_cast this
  -- the target exponent
  have htarget : (n : ℝ) ^ (1 - ε) ≤ (n : ℝ) ^ ((1 - η) * (1 - η)) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by nlinarith)
  have hpow : (n : ℝ) ^ ((1 - η) * (1 - η)) ≤ ((l.length : ℝ) - 1) ^ (1 - η) := by
    rw [Real.rpow_mul (by linarith)]
    exact Real.rpow_le_rpow (by positivity) hllen (by linarith)
  rcases vt_cycle_of_path hconn hvt hl h3 with ⟨c, hc, hcl⟩ | hK
  · obtain ⟨v, w, hw, hwl⟩ := hc.exists_walk_isCycle
    refine ⟨v, w, hw, ?_⟩
    rw [hwl]
    have hle1 : ((l.length : ℝ) - 1) ^ (1 - η) ≤ (l.length : ℝ) - 1 := by
      have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ (l.length : ℝ) - 1)
        (by linarith : 1 - η ≤ 1)
      rwa [Real.rpow_one] at this
    have : (l.length : ℝ) ≤ c.length := by exact_mod_cast hcl
    linarith
  · obtain ⟨c, hc, hcl⟩ := hL₀ V X hK l hl hlenL
    obtain ⟨v, w, hw, hwl⟩ := hc.exists_walk_isCycle
    refine ⟨v, w, hw, ?_⟩
    rw [hwl]
    linarith

/-- Cayley graphs are vertex-transitive. -/
lemma vertexTransitive_cay {H : Type*} [Group H] (S : Set H) : VertexTransitive (cay S) := by
  intro u v
  refine ⟨⟨Equiv.mulLeft (v * u⁻¹), fun {x y} => ?_⟩, by simp⟩
  exact cay_adj_mul_left (S := S) (v * u⁻¹)

/-- **Theorem 1.1 for Cayley graphs (conditional on the path-to-cycle property).** -/
theorem cayley_long_cycle_of_pathToCycle (hPC : PathToCycleSubpoly) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (H : Type) [Group H] [Finite H] (S : Set H),
      (cay S).Connected → n₀ ≤ Nat.card H →
      ∃ (v : H) (c : (cay S).Walk v v), c.IsCycle ∧ (Nat.card H : ℝ) ^ (1 - ε) ≤ c.length := by
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := vt_long_cycle_of_pathToCycle hPC ε hε
  refine ⟨n₀, fun H _ _ S hconn hn => ?_⟩
  have := Fintype.ofFinite H
  rw [Nat.card_eq_fintype_card] at hn ⊢
  exact hn₀ H (cay S) hconn (vertexTransitive_cay S) hn

end Lovasz
