module
public import RequestProject.Rails

/-!
# The cycle-and-matching theorem (statement of Theorem 1.2)

`CycleMatchingTheorem` is the statement of Theorem 1.2 of the paper.  The cycle `L` has
vertex sequence `0, 1, …, 2n-1` (in `Fin (2n)`), and the perfect matching `M` joins `i < n`
with `n + f i`, where `f : Fin n → Fin n` is a bijection.
-/

@[expose] public section


open Classical

namespace Lovasz

/-- Cycle adjacency on `Fin (2n)`: `j = i + 1 (mod 2n)`. -/
def cycAdj (n : ℕ) (i j : Fin (2 * n)) : Prop := j.val = (i.val + 1) % (2 * n)

/-- Matching adjacency: `i < n` is matched with `n + f i`. -/
def matchAdj (n : ℕ) (f : Fin n → Fin n) (i j : Fin (2 * n)) : Prop :=
  ∃ h : i.val < n, j.val = n + (f ⟨i.val, h⟩).val

/-- The graph `L ∪ M`: a `2n`-cycle together with a perfect matching between its halves. -/
def cycleMatchGraph (n : ℕ) (f : Fin n → Fin n) : SimpleGraph (Fin (2 * n)) :=
  SimpleGraph.fromRel (fun i j => cycAdj n i j ∨ matchAdj n f i j)

/-- The number of consecutive pairs `(a, b)` of a list satisfying `r a b`. -/
noncomputable def countPairs {α : Type*} (r : α → α → Prop) : List α → ℕ
  | a :: b :: l => (if r a b then 1 else 0) + countPairs r (b :: l)
  | _ => 0

/-- **Theorem 1.2** (the cycle-and-matching theorem): for every `ε > 0` and all sufficiently
large `n`, if `L` is a `2n`-cycle and `M` a perfect matching between its two halves, then
`L ∪ M` contains a path using at least `n^(1-ε)` edges of `M`. -/
def CycleMatchingTheorem : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ f : Fin n → Fin n, Function.Bijective f →
    ∃ l : List (Fin (2 * n)), IsPathL (cycleMatchGraph n f) l ∧
      (n : ℝ) ^ (1 - ε) ≤ countPairs (fun i j => matchAdj n f i j ∨ matchAdj n f j i) l

end Lovasz
