module
public import RequestProject.CycleMain

/-!
# Cycle covers of a path and the path-to-cycle comparison

Bondy–Locke (and Locke, for `k`-connected graphs) prove their path-to-cycle comparison by
exhibiting a fixed number `r` of cycles that together cover every edge of the path at least `q`
times (for `3`-connected graphs: `r = 5`, `q = 2`, or `r = 10`, `q = 4`).  A double count then
shows that one of the cycles has at least `(q / r) ℓ` edges, where `ℓ` is the number of edges of
the path.

This file isolates that double count, which needs no connectivity at all:

* `pathEdges l`, `cycEdges c`: the undirected edges of a list path and of a cyclic list;
* `exists_long_of_edge_cover`: if `r > 0` lists `C i` cover every edge of the path `l` at least
  `q` times, then `q * (l.length - 1) ≤ r * (C i).length` for some `i`;
* `PathCycleCover q r`: every finite `3`-connected graph with a path admits `r` cycles covering
  every path edge at least `q` times (the form in which Bondy–Locke/Locke state their result);
* `pathToCycleLinear_of_cover`: `PathCycleCover q r` implies `PathToCycleLinear (q / r)`.

It also records the elementary two-slot matching fact used when gluing local routings.
-/

@[expose] public section


open Classical

namespace Lovasz

variable {V : Type*}

/-- The undirected edges of a list path, in order: `s(l[k], l[k+1])` for `k + 1 < l.length`. -/
def pathEdges (l : List V) : List (Sym2 V) := List.zipWith (fun a b => s(a, b)) l l.tail

/-- The undirected edges of the closed walk with cyclic vertex sequence `c`, including the closing
edge from the last vertex back to the first. -/
def cycEdges (c : List V) : List (Sym2 V) := List.zipWith (fun a b => s(a, b)) c (c.rotate 1)

lemma length_pathEdges (l : List V) : (pathEdges l).length = l.length - 1 := by
  simp [pathEdges]

lemma length_cycEdges (c : List V) : (cycEdges c).length = c.length := by
  simp [cycEdges]

lemma pathEdges_cons_cons (a b : V) (t : List V) :
    pathEdges (a :: b :: t) = s(a, b) :: pathEdges (b :: t) := rfl

lemma mem_of_mem_pathEdges {l : List V} {e : Sym2 V} (he : e ∈ pathEdges l) :
    ∀ x ∈ e, x ∈ l := by
  induction l with
  | nil => simp [pathEdges] at he
  | cons a t ih =>
    cases t with
    | nil => simp [pathEdges] at he
    | cons b t =>
      rw [pathEdges_cons_cons, List.mem_cons] at he
      rcases he with rfl | he
      · intro x hx
        rcases Sym2.mem_iff.1 hx with rfl | rfl <;> simp
      · intro x hx
        exact List.mem_cons_of_mem _ (ih he x hx)

/-- The edges of a path with distinct vertices are distinct. -/
lemma nodup_pathEdges {l : List V} (hl : l.Nodup) : (pathEdges l).Nodup := by
  induction l with
  | nil => simp [pathEdges]
  | cons a t ih =>
    cases t with
    | nil => simp [pathEdges]
    | cons b t =>
      rw [pathEdges_cons_cons, List.nodup_cons]
      refine ⟨fun h => ?_, ih hl.of_cons⟩
      exact (List.nodup_cons.1 hl).1 (mem_of_mem_pathEdges h a (Sym2.mem_mk_left a b))

section
variable {G : SimpleGraph V}

private lemma zipWith_cons_append_single (f : V → V → Sym2 V) (y : V) :
    ∀ (x : V) (t : List V), List.zipWith f (x :: t) (t ++ [y]) =
      List.zipWith f (x :: t) t ++ [f ((x :: t).getLast (by simp)) y]
  | x, [] => by simp
  | x, z :: t => by
    rw [List.cons_append, List.zipWith_cons_cons, zipWith_cons_append_single f y z t]
    simp

lemma pathEdges_subset_edgeSet {l : List V} (hl : l.IsChain G.Adj) :
    ∀ e ∈ pathEdges l, e ∈ G.edgeSet := by
  induction l with
  | nil => simp [pathEdges]
  | cons a t ih =>
    cases t with
    | nil => simp [pathEdges]
    | cons b t =>
      rw [List.isChain_cons_cons] at hl
      intro e he
      rw [pathEdges_cons_cons, List.mem_cons] at he
      rcases he with rfl | he
      · exact hl.1
      · exact ih hl.2 e he

/-- Every listed edge of a cycle is an edge of the graph. -/
lemma cycEdges_subset_edgeSet {c : List V} (hc : IsCycleL G c) :
    ∀ e ∈ cycEdges c, e ∈ G.edgeSet := by
  obtain ⟨⟨hch, -⟩, hlen, hclose⟩ := hc
  match c, hch, hlen, hclose with
  | x :: t, hch, _, hclose =>
    intro e he
    rw [cycEdges, List.rotate_cons_succ, List.rotate_zero, zipWith_cons_append_single] at he
    rcases List.mem_append.1 he with he | he
    · exact pathEdges_subset_edgeSet hch e he
    · rw [List.mem_singleton] at he
      subst he
      have := hclose x rfl ((x :: t).getLast (by simp)) (List.getLast?_eq_some_getLast _)
      exact this
end

/-- **Double counting for cycle covers.**  If `r > 0` lists `C i` (for instance cycles) contain,
between them, every edge of a path `l` at least `q` times, then one of them has length at least
`q / r` times the number of edges of `l`. -/
theorem exists_long_of_edge_cover {l : List V} (hl : l.Nodup) {q r : ℕ} (hr : 0 < r)
    (C : Fin r → List V)
    (hcov : ∀ e ∈ pathEdges l, q ≤ (Finset.univ.filter fun i => e ∈ cycEdges (C i)).card) :
    ∃ i, q * (l.length - 1) ≤ r * (C i).length := by
  set E := (pathEdges l).toFinset with hE
  have hEcard : E.card = l.length - 1 := by
    rw [hE, List.toFinset_card_of_nodup (nodup_pathEdges hl), length_pathEdges]
  -- sum over edges of the number of covering cycles
  have h1 : q * E.card ≤ ∑ e ∈ E, (Finset.univ.filter fun i => e ∈ cycEdges (C i)).card := by
    rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun e he => hcov e (List.mem_toFinset.1 he)
  have h2 : ∑ e ∈ E, (Finset.univ.filter fun i => e ∈ cycEdges (C i)).card =
      ∑ i, (E.filter fun e => e ∈ cycEdges (C i)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have h3 : ∀ i, (E.filter fun e => e ∈ cycEdges (C i)).card ≤ (C i).length := by
    intro i
    calc (E.filter fun e => e ∈ cycEdges (C i)).card ≤ (cycEdges (C i)).toFinset.card := by
          apply Finset.card_le_card
          intro e he
          exact List.mem_toFinset.2 (Finset.mem_filter.1 he).2
      _ ≤ (cycEdges (C i)).length := List.toFinset_card_le _
      _ = (C i).length := length_cycEdges _
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun i => (C i).length)
    ⟨⟨0, hr⟩, Finset.mem_univ _⟩
  refine ⟨i₀, ?_⟩
  calc q * (l.length - 1) = q * E.card := by rw [hEcard]
    _ ≤ ∑ i, (E.filter fun e => e ∈ cycEdges (C i)).card := h1.trans h2.le
    _ ≤ ∑ _i : Fin r, (C i₀).length :=
        Finset.sum_le_sum fun i _ => (h3 i).trans (hi₀ i (Finset.mem_univ _))
    _ = r * (C i₀).length := by simp

/-- **Cycle-cover property** with parameters `q` and `r`: every finite `3`-connected graph `G`
and every path `l` of `G` admit an indexed family of `r` cycles of `G` (repetitions allowed)
containing every edge of `l` at least `q` times.  Bondy–Locke's proof of their comparison theorem
gives this with `q = 2`, `r = 5`; Locke's construction for connectivity `3` gives `q = 4`,
`r = 10`. -/
def PathCycleCover (q r : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), KConnected G 3 →
    ∀ l : List V, IsPathL G l → ∃ C : Fin r → List V, (∀ i, IsCycleL G (C i)) ∧
      ∀ e ∈ pathEdges l, q ≤ (Finset.univ.filter fun i => e ∈ cycEdges (C i)).card

/-- A cycle cover with `r > 0` cycles covering each path edge `q` times gives the linear
path-to-cycle comparison with constant `q / r`. -/
theorem pathToCycleLinear_of_cover {q r : ℕ} (hr : 0 < r) (h : PathCycleCover q r) :
    PathToCycleLinear ((q : ℝ) / r) := by
  intro V _ G hG l hl
  obtain ⟨C, hC, hcov⟩ := h V G hG l hl
  obtain ⟨i, hi⟩ := exists_long_of_edge_cover hl.2 hr C hcov
  refine ⟨C i, hC i, ?_⟩
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  rcases Nat.eq_zero_or_pos l.length with h0 | hpos
  · rw [h0]
    have : (0 : ℝ) ≤ (C i).length := by positivity
    have : (0 : ℝ) ≤ (q : ℝ) / r := by positivity
    push_cast
    nlinarith
  · have hcast : ((l.length - 1 : ℕ) : ℝ) = (l.length : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    have hi' : (q : ℝ) * ((l.length : ℝ) - 1) ≤ r * (C i).length := by
      rw [← hcast]; exact_mod_cast hi
    rw [div_mul_eq_mul_div, div_le_iff₀ hr']
    linarith

/-- A cycle cover with `q, r > 0` gives the sub-polynomial path-to-cycle property used by the
final cycle theorems. -/
theorem pathToCycleSubpoly_of_cover {q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (h : PathCycleCover q r) : PathToCycleSubpoly :=
  pathToCycleSubpoly_of_linear (by positivity) (pathToCycleLinear_of_cover hr h)

/-- **Two-slot matching.**  Given two slots on each side, with at most one marked slot on each
side, some bijection between the sides never matches a marked slot with a marked slot. -/
theorem exists_perm_avoiding_marks (a b : Fin 2 → Bool)
    (ha : (Finset.univ.filter fun i => a i = true).card ≤ 1)
    (hb : (Finset.univ.filter fun i => b i = true).card ≤ 1) :
    ∃ σ : Equiv.Perm (Fin 2), ∀ i, ¬ (a i = true ∧ b (σ i) = true) := by
  revert a b
  decide

end Lovasz
