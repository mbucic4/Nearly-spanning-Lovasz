module
public import RequestProject.BondyLocke.Normalize

/-!
# Bondy–Locke: routing cycles through totally disjoint vines

Let `P`, `Q` be totally disjoint vines.  Their double zones form disjoint *boxes*
(Section 4 of Bondy–Locke): a pair `(P.u (i+1), P.v i)` of `P`, a pair of `Q`, or a quadruple
`P.u (i+1) < Q.u (j+1) < Q.v j < P.v i` (or the same with `P` and `Q` exchanged).  Between two
boxes the path is crossed by exactly three *strands*: the path itself (`L`), one chord of `P`
and one chord of `Q`.  A cycle through `0` and `ℓ` crosses each such gap on two of the three
strands, i.e. in one of the states `LP`, `LQ`, `PQ`.

We process the boxes from left to right, maintaining for every state a pair of partial *rails*
(two paths of the skeleton starting at `0`).  For each box type we route the rails through the
box; the routings used here form a coupling of the state distribution `(3, 3, 1)` with itself
covering every edge of the path with weight at least `2` out of `7` (a variant of the routing of
Bondy–Locke, who obtain `4` out of `10`; the routes are chosen so that consecutive boxes sharing
a vertex never conflict).  Averaging gives a cycle containing at least `2ℓ/7` vertices.
-/

@[expose] public section

namespace BondyLocke

open Vine

section rails

variable {C : Set (ℕ × ℕ)}

lemma skel_adj_succ (C : Set (ℕ × ℕ)) (z : ℕ) : (skel C).Adj z (z + 1) :=
  ⟨by omega, Or.inl rfl⟩

lemma skel_adj_chord {ℓ : ℕ} (hC : ChordSys ℓ C) {p q : ℕ} (h : (p, q) ∈ C) :
    (skel C).Adj p q :=
  ⟨(hC.lt _ h).ne, Or.inr (Or.inr (Or.inl h))⟩

lemma chain_range' (C : Set (ℕ × ℕ)) (s n : ℕ) : (List.range' s n).IsChain (skel C).Adj :=
  (List.isChain_range' s n 1).imp (fun a b h => by subst h; exact skel_adj_succ C a)

lemma chain_range'_rev (C : Set (ℕ × ℕ)) (s n : ℕ) :
    (List.range' s n).reverse.IsChain (skel C).Adj := by
  rw [List.isChain_reverse]
  exact (List.isChain_range' s n 1).imp (fun a b h => by subst h; exact (skel_adj_succ C a).symm)

/-- A rail at frontier `f` ending at `e`: a path of the skeleton from `0` to `e` using only
positions `≤ f`. -/
def RailOK (C : Set (ℕ × ℕ)) (f e : ℕ) (r : List ℕ) : Prop :=
  IsPathN (skel C) r ∧ r.head? = some 0 ∧ r.getLast? = some e ∧ ∀ z ∈ r, z ≤ f

/-- Two rails meet only at `0`. -/
def DisjR (r₁ r₂ : List ℕ) : Prop := ∀ z ∈ r₁, z ∈ r₂ → z = 0

/-- A valid pair of rails for a state containing the path strand: the first rail ends at the
frontier `f`, the second at `a` (the origin of the current chord of the other strand). -/
def VLA (C : Set (ℕ × ℕ)) (f a : ℕ) (rL rA : List ℕ) : Prop :=
  RailOK C f f rL ∧ RailOK C f a rA ∧ DisjR rL rA

/-- A valid pair of rails for the state `PQ`. -/
def VAB (C : Set (ℕ × ℕ)) (f a b : ℕ) (rA rB : List ℕ) : Prop :=
  RailOK C f a rA ∧ RailOK C f b rB ∧ DisjR rA rB

lemma DisjR.symm {r₁ r₂ : List ℕ} (h : DisjR r₁ r₂) : DisjR r₂ r₁ :=
  fun z h2 h1 => h z h1 h2

lemma RailOK.mono {f f' e : ℕ} {r : List ℕ} (h : RailOK C f e r) (hf : f ≤ f') :
    RailOK C f' e r :=
  ⟨h.1, h.2.1, h.2.2.1, fun z hz => (h.2.2.2 z hz).trans hf⟩

lemma RailOK.length_pos {f e : ℕ} {r : List ℕ} (h : RailOK C f e r) : 1 ≤ r.length := by
  have := h.2.1
  cases r with
  | nil => simp at this
  | cons _ _ => simp

lemma RailOK.eq_zero_of_length {f e : ℕ} {r : List ℕ} (h : RailOK C f e r) (h1 : r.length ≤ 1) :
    e = 0 := by
  have h0 := h.2.1
  have he := h.2.2.1
  match r, h1 with
  | [], _ => simp at h0
  | [z], _ =>
    simp at h0 he
    rw [← he, h0]

lemma RailOK.append {f f' e e' : ℕ} {r s : List ℕ} (hr : RailOK C f e r)
    (hs : s.IsChain (skel C).Adj) (hsn : s.Nodup) (hjoin : ∀ y ∈ s.head?, (skel C).Adj e y)
    (hlast : (r ++ s).getLast? = some e') (hbig : ∀ z ∈ s, f < z ∧ z ≤ f') (hff : f ≤ f') :
    RailOK C f' e' (r ++ s) := by
  obtain ⟨⟨hch, hnd⟩, h0, he, hle⟩ := hr
  refine ⟨⟨?_, ?_⟩, ?_, hlast, ?_⟩
  · rw [List.isChain_append]
    refine ⟨hch, hs, fun x hx y hy => ?_⟩
    rw [he] at hx
    simp only [Option.mem_def, Option.some.injEq] at hx
    subst hx
    exact hjoin y hy
  · rw [List.nodup_append]
    refine ⟨hnd, hsn, fun a ha b hb hab => ?_⟩
    have := hle a ha
    have := (hbig b hb).1
    omega
  · cases r with
    | nil => simp at h0
    | cons x t => simpa using h0
  · intro z hz
    rcases List.mem_append.1 hz with hz | hz
    · exact (hle z hz).trans hff
    · exact (hbig z hz).2

/-- Extend a rail ending at the frontier `f` along the path up to `a`. -/
lemma RailOK.up {f f' a : ℕ} {r : List ℕ} (hr : RailOK C f f r) (hfa : f ≤ a) (haf : a ≤ f') :
    RailOK C f' a (r ++ List.range' (f + 1) (a - f)) ∧
      (r ++ List.range' (f + 1) (a - f)).length = r.length + (a - f) := by
  refine ⟨hr.append (chain_range' C _ _) List.nodup_range' ?_ ?_ ?_ (hfa.trans haf), by simp⟩
  · intro y hy
    rw [List.head?_range'] at hy
    split_ifs at hy with h
    · simp at hy
    · simp only [Option.mem_def, Option.some.injEq] at hy
      subst hy; exact skel_adj_succ C f
  · rw [List.getLast?_append, List.getLast?_range']
    split_ifs with h
    · have : a = f := by omega
      subst this; simpa using hr.2.2.1
    · simp only [Option.some_or]; congr 1; omega
  · intro z hz
    rw [List.mem_range'_1] at hz
    omega

/-- Extend a rail ending at `e` by a chord `e → d` and then along the path up to `b`. -/
lemma RailOK.chordUp {f f' e d b : ℕ} {r : List ℕ} (hr : RailOK C f e r)
    (hadj : (skel C).Adj e d) (hfd : f < d) (hdb : d ≤ b) (hbf : b ≤ f') :
    RailOK C f' b (r ++ List.range' d (b - d + 1)) ∧
      (r ++ List.range' d (b - d + 1)).length = r.length + (b - d + 1) := by
  refine ⟨hr.append (chain_range' C _ _) List.nodup_range' ?_ ?_ ?_ (by omega), by simp⟩
  · intro y hy
    rw [List.head?_range'] at hy
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Option.mem_def,
      Option.some.injEq] at hy
    subst hy; exact hadj
  · rw [List.getLast?_append, List.getLast?_range']
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Option.some_or]
    congr 1; omega
  · intro z hz
    rw [List.mem_range'_1] at hz
    omega

/-- Extend a rail ending at `e` by a chord `e → d` and then backwards along the path down
to `c`. -/
lemma RailOK.chordDown {f f' e c d : ℕ} {r : List ℕ} (hr : RailOK C f e r)
    (hadj : (skel C).Adj e d) (hfc : f < c) (hcd : c ≤ d) (hdf : d ≤ f') :
    RailOK C f' c (r ++ (List.range' c (d - c + 1)).reverse) ∧
      (r ++ (List.range' c (d - c + 1)).reverse).length = r.length + (d - c + 1) := by
  refine ⟨hr.append (chain_range'_rev C _ _) (List.nodup_reverse.2 List.nodup_range') ?_ ?_ ?_
    (by omega), by simp⟩
  · intro y hy
    rw [List.head?_reverse, List.getLast?_range'] at hy
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Option.mem_def,
      Option.some.injEq] at hy
    rw [← hy, show c + (d - c + 1) - 1 = d by omega]; exact hadj
  · rw [List.getLast?_append, List.getLast?_reverse, List.head?_range']
    simp
  · intro z hz
    rw [List.mem_reverse, List.mem_range'_1] at hz
    omega

lemma DisjR.append {f : ℕ} {r₁ r₂ s₁ s₂ : List ℕ} (h : DisjR r₁ r₂) (hr₁ : ∀ z ∈ r₁, z ≤ f)
    (hr₂ : ∀ z ∈ r₂, z ≤ f) (hs₁ : ∀ z ∈ s₁, f < z) (hs₂ : ∀ z ∈ s₂, f < z)
    (hs : ∀ z ∈ s₁, z ∉ s₂) : DisjR (r₁ ++ s₁) (r₂ ++ s₂) := by
  intro z h1 h2
  rcases List.mem_append.1 h1 with h1 | h1 <;> rcases List.mem_append.1 h2 with h2 | h2
  · exact h z h1 h2
  · have := hr₁ z h1; have := hs₂ z h2; omega
  · have := hr₂ z h2; have := hs₁ z h1; omega
  · exact absurd h2 (hs z h1)

lemma DisjR.append_left {f : ℕ} {r₁ r₂ s₁ : List ℕ} (h : DisjR r₁ r₂)
    (hr₂ : ∀ z ∈ r₂, z ≤ f) (hs₁ : ∀ z ∈ s₁, f < z) : DisjR (r₁ ++ s₁) r₂ := by
  intro z h1 h2
  rcases List.mem_append.1 h1 with h1 | h1
  · exact h z h1 h2
  · have := hr₂ z h2; have := hs₁ z h1; omega

/-- Closing two rails `0 → p` and `0 → q` with `p ∼ q` into a cycle. -/
lemma close_cycle {G : SimpleGraph ℕ} {A B : List ℕ} {p q : ℕ} (hA : IsPathN G A)
    (hB : IsPathN G B) (hA0 : A.head? = some 0) (hB0 : B.head? = some 0)
    (hAl : A.getLast? = some p) (hBl : B.getLast? = some q) (hpq : G.Adj p q) (hd : DisjR A B)
    (h3 : 3 ≤ A.length + B.length - 1) :
    IsCycleN G (A ++ B.tail.reverse) ∧ (A ++ B.tail.reverse).length = A.length + B.length - 1 := by
  obtain ⟨B', rfl⟩ : ∃ B', B = 0 :: B' := by
    cases B with
    | nil => simp at hB0
    | cons x t => simp at hB0; exact ⟨t, by rw [hB0]⟩
  obtain ⟨hBc, hBn⟩ := hB
  rw [List.isChain_cons] at hBc
  have h0B' : 0 ∉ B' := (List.nodup_cons.1 hBn).1
  have hA' : A ≠ [] := by rintro rfl; simp at hA0
  simp only [List.tail_cons]
  refine ⟨⟨⟨?_, ?_⟩, by simp only [List.length_append, List.length_reverse, List.length_cons] at h3 ⊢; omega, ?_⟩,
    by simp only [List.length_append, List.length_reverse, List.length_cons]; omega⟩
  · rw [List.isChain_append]
    refine ⟨hA.1, ?_, ?_⟩
    · rw [List.isChain_reverse]
      exact hBc.2.imp (fun a b h => h.symm)
    · intro x hx y hy
      rw [hAl] at hx
      simp only [Option.mem_def, Option.some.injEq] at hx
      subst hx
      rw [List.head?_reverse] at hy
      cases B' with
      | nil => simp at hy
      | cons b t =>
        rw [List.getLast?_cons_cons] at hBl
        rw [hBl] at hy
        simp only [Option.mem_def, Option.some.injEq] at hy
        subst hy; exact hpq
  · rw [List.nodup_append]
    refine ⟨hA.2, List.nodup_reverse.2 (List.nodup_cons.1 hBn).2, fun a ha b hb hab => ?_⟩
    subst hab
    rw [List.mem_reverse] at hb
    have := hd a ha (List.mem_cons_of_mem _ hb)
    subst this
    exact h0B' hb
  · intro a ha b hb
    rw [List.head?_append, hA0] at ha
    simp only [Option.some_or, Option.mem_def, Option.some.injEq] at ha
    subst ha
    rw [List.getLast?_append, List.getLast?_reverse] at hb
    cases B' with
    | nil =>
      simp only [List.head?_nil, Option.none_or, hAl, Option.mem_def, Option.some.injEq] at hb
      subst hb
      simp at hBl
      subst hBl; exact hpq
    | cons b' t =>
      simp only [List.head?_cons, Option.some_or, Option.mem_def, Option.some.injEq] at hb
      subst hb
      exact (hBc.1 b' (by simp)).symm

lemma exists_best {p : List ℕ → List ℕ → Prop} {x₁ y₁ x₂ y₂ : List ℕ} (h₁ : p x₁ y₁)
    (h₂ : p x₂ y₂) : ∃ x y, p x y ∧ x₁.length + y₁.length ≤ x.length + y.length ∧
      x₂.length + y₂.length ≤ x.length + y.length := by
  rcases le_total (x₁.length + y₁.length) (x₂.length + y₂.length) with h | h
  · exact ⟨x₂, y₂, h₂, h, le_rfl⟩
  · exact ⟨x₁, y₁, h₁, le_rfl, h⟩

end rails

section routing

variable {ℓ : ℕ} {C : Set (ℕ × ℕ)}

/-- The configuration at a gap with left end `f`, where the current chords are `P i`
and `Q j`. -/
structure Config (P Q : Vine) (f i j : ℕ) : Prop where
  hi : i < P.m
  hj : j < Q.m
  hu : P.u i ≤ f
  hv : f < P.v i
  hx : Q.u j ≤ f
  hy : f < Q.v j
  hnu : i + 1 < P.m → f ≤ P.u (i + 1)
  hnx : j + 1 < Q.m → f ≤ Q.u (j + 1)

lemma Config.symm {P Q : Vine} {f i j : ℕ} (h : Config P Q f i j) : Config Q P f j i :=
  ⟨h.hj, h.hi, h.hx, h.hy, h.hu, h.hv, h.hnx, h.hnu⟩

/-- The routing claim at a gap: from valid rails for the three states, a long cycle. -/
def Claim (ℓ : ℕ) (C : Set (ℕ × ℕ)) (P Q : Vine) (f i j : ℕ) : Prop :=
  ∀ r₁ r₂ r₃ r₄ r₅ r₆ : List ℕ, VLA C f (P.u i) r₁ r₂ → VLA C f (Q.u j) r₃ r₄ →
    VAB C f (P.u i) (Q.u j) r₅ r₆ → ∃ c, IsCycleN (skel C) c ∧ (∀ z ∈ c, z ≤ ℓ) ∧
      3 * (r₁.length + r₂.length) + 3 * (r₃.length + r₄.length) + (r₅.length + r₆.length) +
        2 * (ℓ - f) ≤ 7 * c.length + 6

lemma Claim.symm {P Q : Vine} {f i j : ℕ} (h : Claim ℓ C Q P f j i) : Claim ℓ C P Q f i j := by
  intro r₁ r₂ r₃ r₄ r₅ r₆ h12 h34 h56
  obtain ⟨c, hc, hcl, hlen⟩ := h r₃ r₄ r₁ r₂ r₆ r₅ h34 h12 ⟨h56.2.1, h56.1, h56.2.2.symm⟩
  exact ⟨c, hc, hcl, by omega⟩

/-- The last gap: close the rails. -/
lemma final_claim (hC : ChordSys ℓ C) {P Q : Vine} (hg : Good ℓ C P Q) {f i j : ℕ}
    (hcfg : Config P Q f i j) (hi : i + 1 = P.m) (hj : j + 1 = Q.m) : Claim ℓ C P Q f i j := by
  intro r₁ r₂ r₃ r₄ r₅ r₆ h12 h34 h56
  have hPv : P.v i = ℓ := by
    have := hg.1.2; unfold last at this; rwa [show P.m - 1 = i by omega] at this
  have hQv : Q.v j = ℓ := by
    have := hg.2.1.2; unfold last at this; rwa [show Q.m - 1 = j by omega] at this
  have hfl : f < ℓ := hPv ▸ hcfg.hv
  have hmP := hg.1.1.mem i hcfg.hi
  have hmQ := hg.2.1.1.mem j hcfg.hj
  rw [hPv] at hmP
  rw [hQv] at hmQ
  have aP : (skel C).Adj (P.u i) ℓ := skel_adj_chord hC hmP
  have aQ : (skel C).Adj (Q.u j) ℓ := skel_adj_chord hC hmQ
  -- the cycle for a state `L?`
  have hL : ∀ (a : ℕ) (rL rA : List ℕ), VLA C f a rL rA → (skel C).Adj a ℓ →
      ∃ c, IsCycleN (skel C) c ∧ (∀ z ∈ c, z ≤ ℓ) ∧
        c.length = rL.length + (ℓ - f) + rA.length - 1 := by
    intro a rL rA ⟨hL, hA, hd⟩ haℓ
    obtain ⟨hL', hlen⟩ := hL.up (a := ℓ) (f' := ℓ) hfl.le le_rfl
    have h1 := hL.length_pos
    have h2 := hA.length_pos
    have h3 : 3 ≤ (rL ++ List.range' (f + 1) (ℓ - f)).length + rA.length - 1 := by
      rw [hlen]
      by_cases hl1 : rL.length ≤ 1
      · have := hL.eq_zero_of_length hl1
        exfalso
        have := hcfg.hu; have := hcfg.hx
        apply hg.2.2 i hcfg.hi j hcfg.hj
        rw [show P.u i = 0 by omega, show Q.u j = 0 by omega, hPv, hQv]
      · omega
    obtain ⟨hc, hclen⟩ := close_cycle hL'.1 hA.1 hL'.2.1 hA.2.1 hL'.2.2.1 hA.2.2.1 haℓ.symm
      (hd.append_left hA.2.2.2 (fun z hz => by rw [List.mem_range'_1] at hz; omega)) h3
    refine ⟨_, hc, fun z hz => ?_, by rw [hclen, hlen]⟩
    rcases List.mem_append.1 hz with hz | hz
    · exact hL'.2.2.2 z hz
    · rw [List.mem_reverse] at hz
      have := hA.2.2.2 z (List.mem_of_mem_tail hz); omega
  obtain ⟨c₁, hc₁, hc₁l, hlen₁⟩ := hL _ _ _ h12 aP
  obtain ⟨c₂, hc₂, hc₂l, hlen₂⟩ := hL _ _ _ h34 aQ
  -- the cycle for the state `PQ`
  obtain ⟨c₃, hc₃, hc₃l, hlen₃⟩ : ∃ c, IsCycleN (skel C) c ∧ (∀ z ∈ c, z ≤ ℓ) ∧
      c.length = r₅.length + r₆.length := by
    obtain ⟨hA, hB, hd⟩ := h56
    obtain ⟨hA', hlen⟩ := hA.chordUp (f' := ℓ) aP hfl le_rfl le_rfl
    have h1 := hA.length_pos
    have h2 := hB.length_pos
    have h3 : 3 ≤ (r₅ ++ List.range' ℓ (ℓ - ℓ + 1)).length + r₆.length - 1 := by
      rw [hlen]
      by_contra hcon
      have e1 := hA.eq_zero_of_length (by omega)
      have e2 := hB.eq_zero_of_length (by omega)
      apply hg.2.2 i hcfg.hi j hcfg.hj
      rw [e1, e2, hPv, hQv]
    obtain ⟨hc, hclen⟩ := close_cycle hA'.1 hB.1 hA'.2.1 hB.2.1 hA'.2.2.1 hB.2.2.1 aQ.symm
      (hd.append_left hB.2.2.2 (fun z hz => by rw [List.mem_range'_1] at hz; omega)) h3
    refine ⟨_, hc, fun z hz => ?_, by rw [hclen, hlen]; omega⟩
    rcases List.mem_append.1 hz with hz | hz
    · exact hA'.2.2.2 z hz
    · rw [List.mem_reverse] at hz
      have := hB.2.2.2 z (List.mem_of_mem_tail hz); omega
  have := h12.1.length_pos; have := h12.2.1.length_pos
  have := h34.1.length_pos; have := h34.2.1.length_pos
  rcases le_total c₁.length c₂.length with h | h <;>
    rcases le_total c₂.length c₃.length with h' | h' <;>
    rcases le_total c₁.length c₃.length with h'' | h''
  all_goals first
    | exact ⟨c₁, hc₁, hc₁l, by omega⟩
    | exact ⟨c₂, hc₂, hc₂l, by omega⟩
    | exact ⟨c₃, hc₃, hc₃l, by omega⟩

/-- Routing through a pair box `(P.u (i+1), P.v i)` of `P`. -/
lemma pair_step (hC : ChordSys ℓ C) {P Q : Vine} (hg : Good ℓ C P Q) {f i j : ℕ}
    (hcfg : Config P Q f i j) (hi : i + 1 < P.m)
    (IH : Claim ℓ C P Q (P.v i) (i + 1) j) : Claim ℓ C P Q f i j := by
  intro r₁ r₂ r₃ r₄ r₅ r₆ h12 h34 h56
  have hP := hg.1.1
  have hstep := hP.step i hi
  have hfa : f ≤ P.u (i + 1) := hcfg.hnu hi
  have hbl : P.v i < ℓ := Vine.IsVine.v_lt_ell hg.1 hi
  have aP : (skel C).Adj (P.u i) (P.v i) := skel_adj_chord hC (hP.mem i hcfg.hi)
  have hf := hcfg.hv
  -- new rails for `LP`: `L → P_{i+1}` and `P_i → L`
  obtain ⟨hL1, hlL1⟩ := h12.2.1.chordUp (f' := P.v i) aP hf le_rfl le_rfl
  obtain ⟨hP1, hlP1⟩ := h12.1.up (f' := P.v i) hfa hstep.2.1.le
  have V1 : VLA C (P.v i) (P.u (i + 1)) (r₂ ++ List.range' (P.v i) (P.v i - P.v i + 1))
      (r₁ ++ List.range' (f + 1) (P.u (i + 1) - f)) := by
    refine ⟨hL1, hP1, DisjR.append h12.2.2.symm h12.2.1.2.2.2 h12.1.2.2.2 ?_ ?_ ?_⟩
    all_goals intro z hz; simp only [List.mem_range'_1] at hz ⊢; omega
  -- new rails for `LQ`: either `L → L` or `P_i → L`
  obtain ⟨hL2, hlL2⟩ := h34.1.up (f' := P.v i) hf.le le_rfl
  have V2a : VLA C (P.v i) (Q.u j) (r₃ ++ List.range' (f + 1) (P.v i - f)) r₄ :=
    ⟨hL2, h34.2.1.mono hf.le, DisjR.append_left h34.2.2 h34.2.1.2.2.2
      (fun z hz => by rw [List.mem_range'_1] at hz; omega)⟩
  obtain ⟨hL2', hlL2'⟩ := h56.1.chordUp (f' := P.v i) aP hf le_rfl le_rfl
  have V2b : VLA C (P.v i) (Q.u j) (r₅ ++ List.range' (P.v i) (P.v i - P.v i + 1)) r₆ :=
    ⟨hL2', h56.2.1.mono hf.le, DisjR.append_left h56.2.2 h56.2.1.2.2.2
      (fun z hz => by rw [List.mem_range'_1] at hz; omega)⟩
  obtain ⟨r₃', r₄', V2, hb1, hb2⟩ := exists_best V2a V2b
  -- new rails for `PQ`: `L → P_{i+1}`
  obtain ⟨hP3, hlP3⟩ := h34.1.up (f' := P.v i) hfa hstep.2.1.le
  have V3 : VAB C (P.v i) (P.u (i + 1)) (Q.u j) (r₃ ++ List.range' (f + 1) (P.u (i + 1) - f))
      r₄ :=
    ⟨hP3, h34.2.1.mono hf.le, DisjR.append_left h34.2.2 h34.2.1.2.2.2
      (fun z hz => by rw [List.mem_range'_1] at hz; omega)⟩
  obtain ⟨c, hc, hcl, hlen⟩ := IH _ _ _ _ _ _ V1 V2 V3
  refine ⟨c, hc, hcl, ?_⟩
  rw [hlL1, hlP1, hlP3] at hlen
  rw [hlL2] at hb1
  rw [hlL2'] at hb2
  omega

/-- Routing through a quadruple box `P.u (i+1) < Q.u (j+1) < Q.v j < P.v i`. -/
lemma quad_step (hC : ChordSys ℓ C) {P Q : Vine} (hg : Good ℓ C P Q) (htd : TD P Q)
    {f i j : ℕ} (hcfg : Config P Q f i j) (hi : i + 1 < P.m) (hj : j + 1 < Q.m)
    (hac : P.u (i + 1) < Q.u (j + 1)) (hcb : Q.u (j + 1) < P.v i)
    (IH : Claim ℓ C P Q (P.v i) (i + 1) (j + 1)) : Claim ℓ C P Q f i j := by
  intro r₁ r₂ r₃ r₄ r₅ r₆ h12 h34 h56
  have hP := hg.1.1
  have hQ := hg.2.1.1
  have hstep := hP.step i hi
  have hQstep := hQ.step j hj
  have hfa : f ≤ P.u (i + 1) := hcfg.hnu hi
  have hbl : P.v i < ℓ := Vine.IsVine.v_lt_ell hg.1 hi
  -- `Q.v j < P.v i` (no crossing)
  have hdb : Q.v j < P.v i := by
    rcases Nat.lt_trichotomy (Q.v j) (P.v i) with h | h | h
    · exact h
    · have := hg.v_ne hC hcfg.hi hcfg.hj h.symm; omega
    · exact absurd ⟨hac, hcb, h⟩ (htd.2.1 j i hj hi)
  have aP : (skel C).Adj (P.u i) (P.v i) := skel_adj_chord hC (hP.mem i hcfg.hi)
  have aQ : (skel C).Adj (Q.u j) (Q.v j) := skel_adj_chord hC (hQ.mem j hcfg.hj)
  have hf := hcfg.hv
  -- abbreviations: `a < c < d < b`
  set a := P.u (i + 1) with ha
  set b := P.v i with hb
  set c := Q.u (j + 1) with hc
  set d := Q.v j with hd
  have hcd : c < d := hQstep.2.1
  -- the pieces
  obtain ⟨Pa1, lPa1⟩ := h12.1.up (f' := b) hfa (by omega)
  obtain ⟨Pa3, lPa3⟩ := h34.1.up (f' := b) hfa (by omega)
  obtain ⟨Qc1, lQc1⟩ := h12.1.up (f' := b) (show f ≤ c by omega) (by omega)
  obtain ⟨Qc3, lQc3⟩ := h34.1.up (f' := b) (show f ≤ c by omega) (by omega)
  obtain ⟨Lb2, lLb2⟩ := h12.2.1.chordUp (f' := b) aP hf le_rfl le_rfl
  obtain ⟨Lb5, lLb5⟩ := h56.1.chordUp (f' := b) aP hf le_rfl le_rfl
  obtain ⟨Ld4, lLd4⟩ := h34.2.1.chordUp (f' := b) aQ (show f < d by omega) hdb.le le_rfl
  obtain ⟨Qd4, lQd4⟩ := h34.2.1.chordDown (f' := b) aQ (show f < c by omega) hcd.le hdb.le
  obtain ⟨Qd6, lQd6⟩ := h56.2.1.chordDown (f' := b) aQ (show f < c by omega) hcd.le hdb.le
  have b1 := h12.1.2.2.2
  have b2 := h12.2.1.2.2.2
  have b3 := h34.1.2.2.2
  have b4 := h34.2.1.2.2.2
  have b5 := h56.1.2.2.2
  have b6 := h56.2.1.2.2.2
  -- new `LP` rails: `LP → LP` or `LQ → LP`
  have V1a : VLA C b a (r₂ ++ List.range' b (b - b + 1)) (r₁ ++ List.range' (f + 1) (a - f)) := by
    refine ⟨Lb2, Pa1, DisjR.append h12.2.2.symm b2 b1 ?_ ?_ ?_⟩
    all_goals intro z hz; simp only [List.mem_range'_1] at hz ⊢; omega
  have V1b : VLA C b a (r₄ ++ List.range' d (b - d + 1)) (r₃ ++ List.range' (f + 1) (a - f)) := by
    refine ⟨Ld4, Pa3, DisjR.append h34.2.2.symm b4 b3 ?_ ?_ ?_⟩
    all_goals intro z hz; simp only [List.mem_range'_1] at hz ⊢; omega
  obtain ⟨s₁, s₂, V1, e1a, e1b⟩ := exists_best V1a V1b
  -- new `LQ` rails: `LP → LQ`, `LQ → LQ` or `PQ → LQ`
  have V2a : VLA C b c (r₂ ++ List.range' b (b - b + 1)) (r₁ ++ List.range' (f + 1) (c - f)) := by
    refine ⟨Lb2, Qc1, DisjR.append h12.2.2.symm b2 b1 ?_ ?_ ?_⟩
    all_goals intro z hz; simp only [List.mem_range'_1] at hz ⊢; omega
  have V2b : VLA C b c (r₄ ++ List.range' d (b - d + 1)) (r₃ ++ List.range' (f + 1) (c - f)) := by
    refine ⟨Ld4, Qc3, DisjR.append h34.2.2.symm b4 b3 ?_ ?_ ?_⟩
    all_goals intro z hz; simp only [List.mem_range'_1] at hz ⊢; omega
  have V2c : VLA C b c (r₅ ++ List.range' b (b - b + 1))
      (r₆ ++ (List.range' c (d - c + 1)).reverse) := by
    refine ⟨Lb5, Qd6, DisjR.append h56.2.2 b5 b6 ?_ ?_ ?_⟩
    all_goals intro z hz; simp only [List.mem_range'_1, List.mem_reverse] at hz ⊢; omega
  obtain ⟨t₁, t₂, V2', e2a, e2b⟩ := exists_best V2a V2b
  obtain ⟨t₁', t₂', V2, e2c, e2d⟩ := exists_best V2' V2c
  -- new `PQ` rails: `LQ → PQ`
  have V3 : VAB C b a c (r₃ ++ List.range' (f + 1) (a - f))
      (r₄ ++ (List.range' c (d - c + 1)).reverse) := by
    refine ⟨Pa3, Qd4, DisjR.append h34.2.2 b3 b4 ?_ ?_ ?_⟩
    all_goals intro z hz; simp only [List.mem_range'_1, List.mem_reverse] at hz ⊢; omega
  obtain ⟨cy, hcy, hcyl, hlen⟩ := IH _ _ _ _ _ _ V1 V2 V3
  refine ⟨cy, hcy, hcyl, ?_⟩
  rw [lPa3, lQd4] at hlen
  rw [lLb2, lPa1] at e1a
  rw [lLd4, lPa3] at e1b
  rw [lLb2, lQc1] at e2a
  rw [lLd4, lQc3] at e2b
  rw [lLb5, lQd6] at e2d
  omega

/-- The configuration after a pair box of `P`. -/
lemma Config.pair {P Q : Vine} (hg : Good ℓ C P Q) {f i j : ℕ}
    (hcfg : Config P Q f i j) (hi : i + 1 < P.m)
    (hnq : ¬ (j + 1 < Q.m ∧ Q.u (j + 1) < P.v i)) : Config P Q (P.v i) (i + 1) j := by
  have hP := hg.1.1
  have hQ := hg.2.1.1
  have hstep := hP.step i hi
  have hbl : P.v i < ℓ := Vine.IsVine.v_lt_ell hg.1 hi
  refine ⟨hi, hcfg.hj, hstep.2.1.le, hstep.2.2, by have := hcfg.hx; have := hcfg.hv; omega,
    ?_, fun h => ?_, fun h => ?_⟩
  · by_cases hj : j + 1 < Q.m
    · have h1 : P.v i ≤ Q.u (j + 1) := by by_contra h; exact hnq ⟨hj, by omega⟩
      have := (hQ.step j hj).2.1
      omega
    · have hl := hg.2.1.2
      unfold last at hl
      rw [show j = Q.m - 1 by have := hcfg.hj; omega, hl]
      exact hbl
  · have := hP.gap i h; rwa [show i + 1 + 1 = i + 2 from rfl]
  · by_contra h'; exact hnq ⟨h, by omega⟩

/-- The configuration after a quadruple box. -/
lemma Config.quad {P Q : Vine} (hg : Good ℓ C P Q) (htd : TD P Q)
    {i j : ℕ} (hi : i + 1 < P.m) (hj : j + 1 < Q.m)
    (hac : P.u (i + 1) < Q.u (j + 1)) (hcb : Q.u (j + 1) < P.v i) :
    Config P Q (P.v i) (i + 1) (j + 1) := by
  have hP := hg.1.1
  have hQ := hg.2.1.1
  have hstep := hP.step i hi
  have hQstep := hQ.step j hj
  have hbl : P.v i < ℓ := Vine.IsVine.v_lt_ell hg.1 hi
  -- no configuration (4): the next single zone of `Q` is not inside `(P.u (i+1), P.v i)`
  have hnext : j + 2 < Q.m → P.v i ≤ Q.u (j + 2) := by
    intro hj2
    by_contra hcon
    exact htd.2.2.1 i j hi hj2 ⟨by omega, by omega⟩
  refine ⟨hi, hj, hstep.2.1.le, hstep.2.2, hcb.le, ?_, fun h => ?_, fun h => hnext h⟩
  · by_cases hj2 : j + 2 < Q.m
    · have := hnext hj2
      have := (hQ.step (j + 1) hj2).2.1
      rw [show j + 1 + 1 = j + 2 from rfl] at this
      omega
    · have hl := hg.2.1.2
      unfold last at hl
      rw [show j + 1 = Q.m - 1 by omega, hl]
      exact hbl
  · have := hP.gap i h; rwa [show i + 1 + 1 = i + 2 from rfl]

/-- The routing claim holds at every configuration. -/
theorem claim_of_config (hC : ChordSys ℓ C) :
    ∀ n, ∀ P Q : Vine, Good ℓ C P Q → TD P Q → ∀ f i j, (P.m - i) + (Q.m - j) = n →
      Config P Q f i j → Claim ℓ C P Q f i j := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P Q hg htd f i j hn hcfg
  -- a box of `P` comes first
  have pstep : ∀ P Q : Vine, Good ℓ C P Q → TD P Q → ∀ f i j, (P.m - i) + (Q.m - j) = n →
      Config P Q f i j → i + 1 < P.m → (j + 1 < Q.m → P.u (i + 1) < Q.u (j + 1)) →
      Claim ℓ C P Q f i j := by
    intro P Q hg htd f i j hn hcfg hi hPt
    have := hcfg.hi; have := hcfg.hj
    by_cases hq : j + 1 < Q.m ∧ Q.u (j + 1) < P.v i
    · exact quad_step hC hg htd hcfg hi hq.1 (hPt hq.1) hq.2
        (ih _ (by omega) P Q hg htd _ _ _ rfl (Config.quad hg htd hi hq.1 (hPt hq.1) hq.2))
    · exact pair_step hC hg hcfg hi
        (ih _ (by omega) P Q hg htd _ _ _ rfl (hcfg.pair hg hi hq))
  have htd' : TD Q P := ⟨htd.2.1, htd.1, htd.2.2.2, htd.2.2.1⟩
  by_cases hPfirst : i + 1 < P.m ∧ (j + 1 < Q.m → P.u (i + 1) < Q.u (j + 1))
  · exact pstep P Q hg htd f i j hn hcfg hPfirst.1 hPfirst.2
  by_cases hQfirst : j + 1 < Q.m ∧ (i + 1 < P.m → Q.u (j + 1) < P.u (i + 1))
  · exact Claim.symm (pstep Q P hg.symm htd' f j i (by omega) hcfg.symm hQfirst.1 hQfirst.2)
  -- no boxes remain
  have hi : i + 1 = P.m := by
    by_contra hne
    have hi' : i + 1 < P.m := by have := hcfg.hi; omega
    have hj' : j + 1 < Q.m := by
      by_contra h; exact hPfirst ⟨hi', fun h' => absurd h' h⟩
    have h1 : ¬ P.u (i + 1) < Q.u (j + 1) := fun h => hPfirst ⟨hi', fun _ => h⟩
    have h2 : ¬ Q.u (j + 1) < P.u (i + 1) := fun h => hQfirst ⟨hj', fun _ => h⟩
    have heq : P.u (i + 1) = Q.u (j + 1) := by omega
    have := hg.u_ne hC hi' hj' heq
    have := Vine.IsVine.u_pos hg.1 (by omega) hi'
    omega
  have hj : j + 1 = Q.m := by
    by_contra hne
    have hj' : j + 1 < Q.m := by have := hcfg.hj; omega
    exact hQfirst ⟨hj', fun h => by omega⟩
  exact final_claim hC hg hcfg hi hj

/-- **Routing theorem.**  If `P` and `Q` are totally disjoint vines of a chord system on
`0, …, ℓ`, the skeleton has a cycle with at least `(2ℓ + 8) / 7` vertices, all in `0, …, ℓ`. -/
theorem long_cycle_of_td (hC : ChordSys ℓ C) {P Q : Vine} (hg : Good ℓ C P Q) (htd : TD P Q) :
    ∃ c, IsCycleN (skel C) c ∧ (∀ z ∈ c, z ≤ ℓ) ∧ 2 * ℓ + 8 ≤ 7 * c.length := by
  have hP := hg.1.1
  have hQ := hg.2.1.1
  have hcfg : Config P Q 0 0 0 := by
    refine ⟨hP.pos, hQ.pos, by rw [hP.u0], ?_, by rw [hQ.u0], ?_, fun _ => by omega,
      fun _ => by omega⟩
    · have := hP.u_lt_v hP.pos; omega
    · have := hQ.u_lt_v hQ.pos; omega
  have r0 : ∀ e, e = 0 → RailOK C 0 e [0] := by
    intro e he
    subst he
    exact ⟨⟨List.isChain_singleton 0, List.nodup_singleton 0⟩, rfl, rfl, by simp⟩
  have d0 : DisjR [0] [0] := by intro z hz _; simpa using hz
  obtain ⟨c, hc, hcl, hlen⟩ := claim_of_config hC _ P Q hg htd 0 0 0 rfl hcfg [0] [0] [0] [0]
    [0] [0] ⟨r0 0 rfl, r0 _ hP.u0, d0⟩ ⟨r0 0 rfl, r0 _ hQ.u0, d0⟩ ⟨r0 _ hP.u0, r0 _ hQ.u0, d0⟩
  refine ⟨c, hc, hcl, ?_⟩
  simp at hlen
  omega

end routing

end BondyLocke
