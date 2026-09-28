module
public import RequestProject.Walks

/-!
# Cayley graphs

`cay S` is the undirected Cayley graph of a group `H` with respect to `S`: vertices are the
elements of `H`, and `x` is adjacent to `x * s` for `s ∈ S ∪ S⁻¹`, loops being discarded.
For `S = S⁻¹` this is exactly `Cay(H, S)` of the paper.  The quotient Cayley graph
`Cay(H/N, S)` is `cay (QuotientGroup.mk '' S)`.
-/

@[expose] public section


open Classical

namespace Lovasz

variable {H : Type*} [Group H]

/-- The (undirected, loopless) Cayley graph of `H` with respect to `S`. -/
def cay (S : Set H) : SimpleGraph H := SimpleGraph.fromRel (fun x y => x⁻¹ * y ∈ S)

variable {S : Set H}

lemma cay_adj {x y : H} : (cay S).Adj x y ↔ x ≠ y ∧ (x⁻¹ * y ∈ S ∨ y⁻¹ * x ∈ S) := by
  simp [cay, SimpleGraph.fromRel_adj]

lemma cay_adj_mul_left (g : H) {x y : H} : (cay S).Adj (g * x) (g * y) ↔ (cay S).Adj x y := by
  simp [cay_adj, mul_assoc]

lemma cay_adj_mul_right_of_mem {x s : H} (hs : s ∈ S ∨ s⁻¹ ∈ S) (hne : s ≠ 1) :
    (cay S).Adj x (x * s) := by
  rw [cay_adj]
  refine ⟨by simpa using hne, ?_⟩
  rcases hs with hs | hs
  · left; simpa using hs
  · right; simpa [mul_assoc] using hs

lemma IsPathL.map_mul_left {l : List H} (h : IsPathL (cay S) l) (g : H) :
    IsPathL (cay S) (l.map (g * ·)) := by
  refine ⟨?_, h.2.map (mul_right_injective g)⟩
  rw [List.isChain_map]
  exact h.1.imp fun a b hab => (cay_adj_mul_left g).2 hab

lemma ReachIn.map_mul_left {s : Set H} {u v : H} (h : ReachIn (cay S) s u v) (g : H) :
    ReachIn (cay S) ((g * ·) '' s) (g * u) (g * v) := by
  refine ReachIn.closed (Q := fun x => ReachIn (cay S) ((g * ·) '' s) (g * u) (g * x))
    (ReachIn.refl ⟨u, h.1, rfl⟩) ?_ h
  intro a b ha _ hb hab
  exact ha.tail ((cay_adj_mul_left g).2 hab) ⟨b, hb, rfl⟩

lemma WalkLe.map_mul_left {s : Set H} {u v : H} {L : ℕ} (h : WalkLe (cay S) s u v L) (g : H) :
    WalkLe (cay S) ((g * ·) '' s) (g * u) (g * v) L := by
  obtain ⟨l, h1, h2, h3, h4, h5⟩ := h
  refine ⟨l.map (g * ·), ?_, by simp [h2], by simp [List.getLast?_map, h3], ?_, by simpa using h5⟩
  · rw [List.isChain_map]; exact h1.imp fun a b hab => (cay_adj_mul_left g).2 hab
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact ⟨y, h4 y hy, rfl⟩

/-- Left translation of a walk in an invariant set. -/
lemma WalkLe.map_mul_left_of_inv {s : Set H} {u v : H} {L : ℕ} (h : WalkLe (cay S) s u v L)
    (g : H) (hs : ∀ x ∈ s, g * x ∈ s) :
    WalkLe (cay S) s (g * u) (g * v) L := by
  refine (h.map_mul_left g).mono_set ?_
  rintro _ ⟨x, hx, rfl⟩; exact hs x hx

/-- A product of at most `n` letters from `T ∪ T⁻¹` is joined to `1` by a walk in `cay T` with
at most `n` edges. -/
lemma walkLe_of_word (T : Set H) (l : List H) (hl : ∀ x ∈ l, x ∈ T ∨ x⁻¹ ∈ T) :
    WalkLe (cay T) Set.univ 1 l.prod l.length := by
  induction l using List.reverseRecOn with
  | nil => exact WalkLe.refl (Set.mem_univ _) 0
  | append_singleton l x ih =>
    have ih := ih (fun y hy => hl y (by simp [hy]))
    rw [List.prod_append, List.prod_singleton, List.length_append, List.length_singleton]
    refine ih.of_eq_or_adj ?_ trivial
    by_cases hx : x = 1
    · left; simp [hx]
    · right; exact cay_adj_mul_right_of_mem (hl x (by simp)) hx

/-! ### Quotients -/

section Quotient

variable (N : Subgroup H) [N.Normal]

lemma cay_quot_adj_of_adj {x y : H} (h : (cay S).Adj x y)
    (hne : (x : H ⧸ N) ≠ (y : H ⧸ N)) :
    (cay ((QuotientGroup.mk : H → H ⧸ N) '' S)).Adj (x : H ⧸ N) (y : H ⧸ N) := by
  rw [cay_adj] at h ⊢
  refine ⟨hne, ?_⟩
  rcases h.2 with h | h
  · left; exact ⟨_, h, by simp⟩
  · right; exact ⟨_, h, by simp⟩

/-- An edge of the quotient Cayley graph lifts to every vertex of its initial coset, via
right multiplication by a fixed element. -/
lemma cay_quot_adj_lift {x : H} {b : H ⧸ N}
    (h : (cay ((QuotientGroup.mk : H → H ⧸ N) '' S)).Adj (x : H ⧸ N) b) :
    ∃ s : H, b = ((x * s : H) : H ⧸ N) ∧
      ∀ y : H, (y : H ⧸ N) = (x : H ⧸ N) → (cay S).Adj y (y * s) := by
  rw [cay_adj] at h
  obtain ⟨hne, h⟩ := h
  rcases h with ⟨s, hs, hsb⟩ | ⟨s, hs, hsb⟩
  · refine ⟨s, ?_, ?_⟩
    · rw [QuotientGroup.mk_mul, hsb]; group
    · intro y hy
      rw [cay_adj]
      refine ⟨?_, Or.inl (by simpa using hs)⟩
      intro heq
      apply hne
      have : ((y * s : H) : H ⧸ N) = b := by rw [QuotientGroup.mk_mul, hsb, hy]; group
      rw [← this, ← heq, hy]
  · refine ⟨s⁻¹, ?_, ?_⟩
    · rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hsb]; group
    · intro y hy
      rw [cay_adj]
      refine ⟨?_, Or.inr (by simpa [mul_assoc] using hs)⟩
      intro heq
      apply hne
      have : ((y * s⁻¹ : H) : H ⧸ N) = b := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hsb, hy]; group
      rw [← this, ← heq, hy]

/-- Left multiplication by an element of a normal subgroup preserves every coset. -/
lemma mk_mul_left_of_mem {n : H} (hn : n ∈ N) (x : H) :
    ((n * x : H) : H ⧸ N) = (x : H ⧸ N) := by
  rw [QuotientGroup.eq]
  have : (n * x)⁻¹ * x = x⁻¹ * n⁻¹ * x := by group
  rw [this]
  simpa using (inferInstance : N.Normal).conj_mem _ (N.inv_mem hn) x⁻¹

/-- A left-`N`-invariant set is a union of cosets. -/
lemma mem_of_mk_eq {Z : Set H} (hZ : ∀ n ∈ N, ∀ z ∈ Z, n * z ∈ Z) {y z : H} (hz : z ∈ Z)
    (hyz : (y : H ⧸ N) = (z : H ⧸ N)) : y ∈ Z := by
  have h1 : z⁻¹ * y ∈ N := QuotientGroup.eq.1 hyz.symm
  have h2 : y * z⁻¹ ∈ N := by
    have := (inferInstance : N.Normal).conj_mem _ h1 z
    simpa [mul_assoc] using this
  have := hZ _ h2 z hz
  simpa using this

/-- For normal `N`, `t * x⁻¹ ∈ N` iff `t` and `x` lie in the same coset. -/
lemma mk_eq_of_mul_inv_mem {t x : H} (h : t * x⁻¹ ∈ N) : (t : H ⧸ N) = (x : H ⧸ N) := by
  rw [QuotientGroup.eq]
  have := (inferInstance : N.Normal).conj_mem _ (N.inv_mem h) x⁻¹
  simpa [mul_assoc] using this

end Quotient

/-! ### Connectivity -/

lemma cay_reachable_mul_left (g : H) {a b : H} (h : (cay S).Reachable a b) :
    (cay S).Reachable (g * a) (g * b) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h ⊢
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail ((cay_adj_mul_left g).2 hbc)

lemma cay_reachable_one_iff_mem_closure [Finite H] {g : H} :
    (cay S).Reachable 1 g ↔ g ∈ Subgroup.closure S := by
  constructor
  · intro h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => exact Subgroup.one_mem _
    | @tail b c _ hbc ih =>
      rw [cay_adj] at hbc
      have hc : c = b * (b⁻¹ * c) := by group
      rcases hbc.2 with h | h
      · rw [hc]; exact Subgroup.mul_mem _ ih (Subgroup.subset_closure h)
      · rw [hc]
        have : b⁻¹ * c = (c⁻¹ * b)⁻¹ := by group
        rw [this]
        exact Subgroup.mul_mem _ ih (Subgroup.inv_mem _ (Subgroup.subset_closure h))
  · intro h
    induction h using Subgroup.closure_induction with
    | mem x hx =>
      by_cases hx1 : x = 1
      · subst hx1; rfl
      · have := cay_adj_mul_right_of_mem (S := S) (x := 1) (Or.inl hx) hx1
        simpa using this.reachable
    | one => rfl
    | mul x y _ _ hx hy =>
      refine hx.trans ?_
      simpa using cay_reachable_mul_left x hy
    | inv x _ hx =>
      simpa using (cay_reachable_mul_left x⁻¹ hx).symm

lemma cay_connected_iff [Finite H] : (cay S).Connected ↔ Subgroup.closure S = ⊤ := by
  constructor
  · intro h
    rw [eq_top_iff]
    intro g _
    exact cay_reachable_one_iff_mem_closure.1 (h.preconnected 1 g)
  · intro h
    have hr : ∀ g, (cay S).Reachable 1 g := fun g =>
      cay_reachable_one_iff_mem_closure.2 (h ▸ Subgroup.mem_top g)
    exact ⟨fun u v => (hr u).symm.trans (hr v)⟩

lemma cay_quot_connected [Finite H] (N : Subgroup H) [N.Normal] (h : (cay S).Connected) :
    (cay ((QuotientGroup.mk : H → H ⧸ N) '' S)).Connected := by
  rw [cay_connected_iff] at h ⊢
  have := MonoidHom.map_closure (QuotientGroup.mk' N) S
  rw [h, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at this
  exact this.symm

end Lovasz
