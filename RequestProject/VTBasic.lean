module
public import RequestProject.Rails

/-!
# Group actions on graphs and quotients by normal subgroups (setup for Appendix A)

Throughout the appendix, a group `Γ` acts on the vertex set `V` of a graph `X` by
automorphisms (`ActsOn X Γ`).  For a subgroup `N ≤ Γ`, `Fib N` is the set of `N`-orbits and
`fib N v` the orbit of `v`; `quotGraph X N` is the quotient graph `X/N` whose vertices are the
`N`-orbits, two distinct orbits being adjacent when an edge of `X` joins them.
-/

@[expose] public section


open Classical

namespace Lovasz

variable {V Γ : Type*} [Group Γ] [MulAction Γ V]

/-- `Γ` acts on `X` by graph automorphisms. -/
def ActsOn (X : SimpleGraph V) (Γ : Type*) [Group Γ] [MulAction Γ V] : Prop :=
  ∀ g : Γ, ∀ u v : V, X.Adj u v → X.Adj (g • u) (g • v)

/-- The action is transitive on vertices. -/
def TransOn (Γ V : Type*) [Group Γ] [MulAction Γ V] : Prop := ∀ u v : V, ∃ g : Γ, g • u = v

/-- The set of `N`-orbits. -/
abbrev Fib (N : Subgroup Γ) (V : Type*) [MulAction Γ V] := MulAction.orbitRel.Quotient N V

/-- The `N`-orbit of a vertex. -/
def fib (N : Subgroup Γ) (v : V) : Fib N V := Quotient.mk (MulAction.orbitRel N V) v

lemma fib_eq_iff {N : Subgroup Γ} {u v : V} : fib N u = fib N v ↔ ∃ g ∈ N, g • v = u := by
  unfold fib
  rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩; exact ⟨g, g.2, hg⟩
  · rintro ⟨g, hg, h⟩; exact ⟨⟨g, hg⟩, h⟩

lemma fib_surjective (N : Subgroup Γ) : Function.Surjective (fib N : V → Fib N V) :=
  fun q => Quotient.inductionOn q fun v => ⟨v, rfl⟩

lemma fib_smul_of_mem {N : Subgroup Γ} {g : Γ} (hg : g ∈ N) (v : V) : fib N (g • v) = fib N v :=
  fib_eq_iff.2 ⟨g, hg, rfl⟩

/-- The action of `Γ` on the `N`-orbits, for normal `N`. -/
instance fibAction (N : Subgroup Γ) [hN : N.Normal] : MulAction Γ (Fib N V) where
  smul g := Quotient.map (g • ·) (by
    intro u v h
    have h' : fib N u = fib N v := Quotient.sound h
    obtain ⟨n, hn, rfl⟩ := fib_eq_iff.1 h'
    apply Quotient.exact (s := MulAction.orbitRel N V)
    show fib N (g • n • v) = fib N (g • v)
    exact fib_eq_iff.2 ⟨g * n * g⁻¹, hN.conj_mem n hn g, by simp [mul_smul]⟩)
  one_smul q := Quotient.inductionOn q fun v => by
    show fib N ((1 : Γ) • v) = fib N v; rw [one_smul]
  mul_smul g h q := Quotient.inductionOn q fun v => by
    show fib N ((g * h) • v) = fib N (g • h • v); rw [mul_smul]

lemma smul_fib (N : Subgroup Γ) [N.Normal] (g : Γ) (v : V) : g • fib N v = fib N (g • v) := rfl

/-- The quotient graph `X/N`. -/
def quotGraph (X : SimpleGraph V) (N : Subgroup Γ) : SimpleGraph (Fib N V) :=
  SimpleGraph.fromRel (fun p q => ∃ u v, fib N u = p ∧ fib N v = q ∧ X.Adj u v)

variable {X : SimpleGraph V}

lemma quotGraph_adj {N : Subgroup Γ} {p q : Fib N V} :
    (quotGraph X N).Adj p q ↔ p ≠ q ∧ ∃ u v, fib N u = p ∧ fib N v = q ∧ X.Adj u v := by
  simp only [quotGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | ⟨u, v, hu, hv, huv⟩⟩
    · exact ⟨hne, h⟩
    · exact ⟨hne, v, u, hv, hu, huv.symm⟩
  · rintro ⟨hne, h⟩; exact ⟨hne, Or.inl h⟩

lemma quotGraph_adj_of_adj {N : Subgroup Γ} {u v : V} (h : X.Adj u v) (hne : fib N u ≠ fib N v) :
    (quotGraph X N).Adj (fib N u) (fib N v) :=
  quotGraph_adj.2 ⟨hne, u, v, rfl, rfl, h⟩

lemma ActsOn.adj_iff (hX : ActsOn X Γ) (g : Γ) {u v : V} : X.Adj (g • u) (g • v) ↔ X.Adj u v :=
  ⟨fun h => by simpa using hX g⁻¹ _ _ h, hX g u v⟩

lemma ActsOn.quot (hX : ActsOn X Γ) (N : Subgroup Γ) [N.Normal] :
    ActsOn (quotGraph X N) Γ := by
  intro g p q h
  obtain ⟨hne, u, v, rfl, rfl, huv⟩ := quotGraph_adj.1 h
  refine quotGraph_adj.2 ⟨fun he => hne ?_, g • u, g • v, rfl, rfl, hX g u v huv⟩
  have := congrArg (g⁻¹ • ·) he
  simpa [smul_fib] using this

lemma TransOn.quot (hT : TransOn Γ V) (N : Subgroup Γ) [N.Normal] : TransOn Γ (Fib N V) := by
  intro p q
  obtain ⟨u, rfl⟩ := fib_surjective N p
  obtain ⟨v, rfl⟩ := fib_surjective N q
  obtain ⟨g, hg⟩ := hT u v
  exact ⟨g, by rw [smul_fib, hg]⟩

/-! ### Translating paths, walks and rails -/

lemma IsPathL.map_smul (hX : ActsOn X Γ) {l : List V} (h : IsPathL X l) (g : Γ) :
    IsPathL X (l.map (g • ·)) := by
  refine ⟨?_, h.2.map (MulAction.injective g)⟩
  rw [List.isChain_map]
  exact h.1.imp fun a b hab => hX g a b hab

lemma ReachIn.map_smul (hX : ActsOn X Γ) {s : Set V} {u v : V} (h : ReachIn X s u v) (g : Γ) :
    ReachIn X ((g • ·) '' s) (g • u) (g • v) := by
  refine ReachIn.closed (Q := fun x => ReachIn X ((g • ·) '' s) (g • u) (g • x))
    (ReachIn.refl ⟨u, h.1, rfl⟩) ?_ h
  intro a b ha _ hb hab
  exact ha.tail (hX g a b hab) ⟨b, hb, rfl⟩

lemma WalkLe.map_smul (hX : ActsOn X Γ) {s : Set V} {u v : V} {L : ℕ} (h : WalkLe X s u v L)
    (g : Γ) : WalkLe X ((g • ·) '' s) (g • u) (g • v) L := by
  obtain ⟨l, h1, h2, h3, h4, h5⟩ := h
  refine ⟨l.map (g • ·), ?_, by simp [h2], by simp [List.getLast?_map, h3], ?_, by simpa using h5⟩
  · rw [List.isChain_map]; exact h1.imp fun a b hab => hX g a b hab
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact ⟨y, h4 y hy, rfl⟩

lemma WalkLe.map_smul_of_inv (hX : ActsOn X Γ) {s : Set V} {u v : V} {L : ℕ}
    (h : WalkLe X s u v L) (g : Γ) (hs : ∀ x ∈ s, g • x ∈ s) : WalkLe X s (g • u) (g • v) L := by
  refine (h.map_smul hX g).mono_set ?_
  rintro _ ⟨x, hx, rfl⟩; exact hs x hx

lemma HasRail.map_smul (hX : ActsOn X Γ) {Z : Set V} {T : Finset V} (h : HasRail X Z T) (g : Γ) :
    HasRail X ((g • ·) '' Z) (T.image (g • ·)) := by
  obtain ⟨P, hP, hPZ, att, hatt, hdisj⟩ := h
  refine ⟨P.map (g • ·), hP.map_smul hX g, ?_, fun x => (att (g⁻¹ • x)).map (g • ·), ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact ⟨y, hPZ y hy, rfl⟩
  · intro t ht
    obtain ⟨t, ht0, rfl⟩ := Finset.mem_image.1 ht
    simp only [inv_smul_smul]
    obtain ⟨h1, h2, ⟨x, hx, h3⟩, h4, h5⟩ := hatt t ht0
    refine ⟨h1.map_smul hX g, by simp [h2], ⟨g • x, List.mem_map_of_mem hx, ?_⟩, ?_, ?_⟩
    · simp [List.getLast?_map, h3]
    · intro y hy
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
      exact ⟨z, h4 z hz, rfl⟩
    · intro y hy hyP
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
      obtain ⟨z', hz', hzz'⟩ := List.mem_map.1 hyP
      have : z' = z := MulAction.injective g hzz'
      subst this
      simp [List.getLast?_map, h5 z' hz hz']
  · intro t ht t' ht' hne
    obtain ⟨t, ht0, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨t', ht0', rfl⟩ := Finset.mem_image.1 ht'
    simp only [inv_smul_smul]
    have hne' : t ≠ t' := fun h => hne (by rw [h])
    intro y hy hy'
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    obtain ⟨z', hz', hzz'⟩ := List.mem_map.1 hy'
    have : z' = z := MulAction.injective g hzz'
    subst this
    exact hdisj t ht0 t' ht0' hne' hz hz'

/-! ### Orbit counting -/

section Counting

variable [Fintype Γ]

/-- The elements of `N`, as a finset. -/
noncomputable def nset (N : Subgroup Γ) : Finset Γ := Finset.univ.filter (· ∈ N)

lemma mem_nset {N : Subgroup Γ} {g : Γ} : g ∈ nset N ↔ g ∈ N := by simp [nset]

/-- The `N`-orbit of `v`, as a finset. -/
noncomputable def orb (N : Subgroup Γ) (v : V) : Finset V := (nset N).image (· • v)

lemma mem_orb {N : Subgroup Γ} {u v : V} : u ∈ orb N v ↔ fib N u = fib N v := by
  rw [fib_eq_iff]; simp [orb, mem_nset]

lemma self_mem_orb (N : Subgroup Γ) (v : V) : v ∈ orb N v := mem_orb.2 rfl

lemma orb_eq_of_fib_eq {N : Subgroup Γ} {u v : V} (h : fib N u = fib N v) : orb N u = orb N v := by
  ext w; rw [mem_orb, mem_orb, h]

/-- Every point of an orbit is hit by the same number of group elements:
`#{g ∈ N : g • a = b} · |N a| = |N|`. -/
lemma card_filter_smul_eq (N : Subgroup Γ) {a b : V} (hb : fib N b = fib N a) :
    ((nset N).filter (fun g => g • a = b)).card * (orb N a).card = (nset N).card := by
  have hfib : ∀ c ∈ orb N a, ((nset N).filter (fun g => g • a = c)).card =
      ((nset N).filter (fun g => g • a = a)).card := by
    intro c hc
    obtain ⟨g0, hg0, rfl⟩ := Finset.mem_image.1 hc
    have hg0N := mem_nset.1 hg0
    refine Finset.card_bij (fun g _ => g0⁻¹ * g) ?_ ?_ ?_
    · intro g hg
      obtain ⟨hgN, hga⟩ := Finset.mem_filter.1 hg
      refine Finset.mem_filter.2 ⟨mem_nset.2 (N.mul_mem (N.inv_mem hg0N) (mem_nset.1 hgN)), ?_⟩
      rw [mul_smul, hga, inv_smul_smul]
    · intro g _ g' _ h; exact mul_left_cancel h
    · intro g hg
      obtain ⟨hgN, hga⟩ := Finset.mem_filter.1 hg
      refine ⟨g0 * g, Finset.mem_filter.2 ⟨mem_nset.2 (N.mul_mem hg0N (mem_nset.1 hgN)), ?_⟩,
        by simp⟩
      rw [mul_smul, hga]
  have hsum := Finset.card_eq_sum_card_fiberwise (f := fun g => g • a) (s := nset N)
    (t := orb N a) (fun g hg => Finset.mem_coe.2 (Finset.mem_image_of_mem (· • a) hg))
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul] at hsum
  rw [hsum, hfib b (mem_orb.2 hb), mul_comm]

/-- Orbits of a normal subgroup under a transitive action all have the same size. -/
lemma card_orb_eq (N : Subgroup Γ) [hN : N.Normal] (hT : TransOn Γ V) (u v : V) :
    (orb N u).card = (orb N v).card := by
  obtain ⟨g, rfl⟩ := hT u v
  refine Finset.card_bij (fun w _ => g • w) ?_ ?_ ?_
  · intro w hw
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hw
    refine Finset.mem_image.2 ⟨g * n * g⁻¹, mem_nset.2 (hN.conj_mem n (mem_nset.1 hn) g), ?_⟩
    simp [mul_smul]
  · intro w _ w' _ h; exact MulAction.injective g h
  · intro w hw
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hw
    refine ⟨(g⁻¹ * n * g) • u, Finset.mem_image.2 ⟨g⁻¹ * n * g, mem_nset.2 ?_, rfl⟩, ?_⟩
    · have := hN.conj_mem n (mem_nset.1 hn) g⁻¹; simpa using this
    · simp [mul_smul]

end Counting

end Lovasz
