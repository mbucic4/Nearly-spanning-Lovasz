module
public import Mathlib

/-!
# Bondy–Locke: chord systems, the skeleton graph and vines

This file sets up the purely combinatorial side of the proof of the Bondy–Locke theorem
(J. A. Bondy and S. C. Locke, *Relative lengths of paths and cycles in 3-connected graphs*,
Discrete Math. 33 (1981) 111–122).

The path `L = w₀ w₁ ⋯ w_ℓ` is replaced by the positions `0, 1, …, ℓ`.  A *chord* `(a, b)` with
`a < b` records a path of the ambient graph from `w_a` to `w_b` whose interior avoids `L`
(and the interiors of all other chords).  A *chord system* (`ChordSys`) is a set of chords such
that distinct chords have distinct origins (except `0`) and distinct termini (except `ℓ`), and
every interior position `0 < j < ℓ` is jumped over by two distinct chords.  This is exactly what
three internally disjoint `w₀ – w_ℓ` paths provide.

The *skeleton* `skel C` is the graph on `ℕ` whose edges are the path edges `{t, t+1}` and the
chords.  Cycles of the skeleton lift to cycles of the ambient graph of at least the same length.

A *vine* (`Vine`, with `Vine.Partial` / `Vine.IsVine`) is a sequence of chords
`(u 0, v 0), …, (u (m-1), v (m-1))` with
`0 = u 0 < u 1 < v 0 ≤ u 2 < v 1 ≤ u 3 < ⋯ < v (m-1) = ℓ`, as in Section 2 of the paper
(indices here start at `0`).
-/

@[expose] public section

namespace BondyLocke

/-- A path in `G`, given by its vertex list (consecutive entries adjacent, no repetition). -/
def IsPathN {α : Type*} (G : SimpleGraph α) (l : List α) : Prop := l.IsChain G.Adj ∧ l.Nodup

/-- A cycle in `G`, given by its cyclic vertex list: a path with at least three vertices whose
last vertex is adjacent to its first.  It has `l.length` edges. -/
def IsCycleN {α : Type*} (G : SimpleGraph α) (l : List α) : Prop :=
  IsPathN G l ∧ 3 ≤ l.length ∧ ∀ a ∈ l.head?, ∀ b ∈ l.getLast?, G.Adj b a

/-- A *chord system* on the positions `0, …, ℓ`. -/
structure ChordSys (ℓ : ℕ) (C : Set (ℕ × ℕ)) : Prop where
  lt : ∀ c ∈ C, c.1 < c.2
  le : ∀ c ∈ C, c.2 ≤ ℓ
  origin : ∀ c ∈ C, ∀ c' ∈ C, c.1 = c'.1 → c ≠ c' → c.1 = 0
  term : ∀ c ∈ C, ∀ c' ∈ C, c.2 = c'.2 → c ≠ c' → c.2 = ℓ
  cover : ∀ j, 0 < j → j < ℓ →
    ∃ c ∈ C, ∃ c' ∈ C, c ≠ c' ∧ c.1 < j ∧ j < c.2 ∧ c'.1 < j ∧ j < c'.2

/-- The skeleton graph: path edges `{t, t+1}` together with the chords of `C`. -/
def skel (C : Set (ℕ × ℕ)) : SimpleGraph ℕ where
  Adj s t := s ≠ t ∧ (s + 1 = t ∨ t + 1 = s ∨ (s, t) ∈ C ∨ (t, s) ∈ C)
  symm := by
    constructor
    intro s t h
    exact ⟨h.1.symm, by rcases h.2 with h | h | h | h <;> tauto⟩
  loopless := ⟨fun s h => h.1 rfl⟩

/-- A (finite) sequence of chords `(u k, v k)`, `k < m`. -/
structure Vine where
  m : ℕ
  u : ℕ → ℕ
  v : ℕ → ℕ

namespace Vine

/-- A *partial vine* with chords in `C`: it starts at `0` and consecutive chords overlap, while
chords two apart do not. -/
structure Partial (C : Set (ℕ × ℕ)) (P : Vine) : Prop where
  pos : 0 < P.m
  u0 : P.u 0 = 0
  step : ∀ k, k + 1 < P.m → P.u k < P.u (k + 1) ∧ P.u (k + 1) < P.v k ∧ P.v k < P.v (k + 1)
  gap : ∀ k, k + 2 < P.m → P.v k ≤ P.u (k + 2)
  lastlt : P.u (P.m - 1) < P.v (P.m - 1)
  mem : ∀ k < P.m, (P.u k, P.v k) ∈ C

/-- The terminus of the last chord. -/
def last (P : Vine) : ℕ := P.v (P.m - 1)

/-- A (complete) vine on the positions `0, …, ℓ` with chords in `C`. -/
def IsVine (ℓ : ℕ) (C : Set (ℕ × ℕ)) (P : Vine) : Prop := P.Partial C ∧ P.last = ℓ

end Vine

/-- Two vines are *disjoint* if they have no chord in common.  (For chords from a chord system
this implies the disjointness conditions of Bondy–Locke.) -/
def Disj (P Q : Vine) : Prop := ∀ k < P.m, ∀ k' < Q.m, (P.u k, P.v k) ≠ (Q.u k', Q.v k')

/-- No double zone `(Q.u (j+1), Q.v j)` of `Q` crosses a double zone `(P.u (i+1), P.v i)` of `P`
from the left (configuration (5) of the paper). -/
def NoCross (P Q : Vine) : Prop :=
  ∀ i j, i + 1 < P.m → j + 1 < Q.m →
    ¬ (Q.u (j + 1) < P.u (i + 1) ∧ P.u (i + 1) < Q.v j ∧ Q.v j < P.v i)

/-- No double zone of `P` contains a single zone `[Q.v j, Q.u (j+2)]` of `Q`
(configuration (4) of the paper). -/
def NoContain (P Q : Vine) : Prop :=
  ∀ i j, i + 1 < P.m → j + 2 < Q.m → ¬ (P.u (i + 1) < Q.v j ∧ Q.u (j + 2) < P.v i)

/-- *Totally disjoint* vines: neither configuration (4) nor (5) occurs, in either order. -/
def TD (P Q : Vine) : Prop := NoCross P Q ∧ NoCross Q P ∧ NoContain P Q ∧ NoContain Q P

end BondyLocke
