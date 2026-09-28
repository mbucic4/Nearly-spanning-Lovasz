module
public import RequestProject.BondyLocke.Defs

/-!
# Bondy–Locke: lifting skeleton cycles

Suppose the positions `0, …, ℓ` are mapped injectively into a graph `G` by `φ`, and every edge
`{s, t}` of a graph `H` on the positions is realised in `G` by a path
`φ s, R s t, φ t` whose interior `R s t` avoids the image of `φ`, where interiors of distinct
edges are disjoint.  Then every cycle of `H` on the positions `0, …, ℓ` gives a cycle of `G`
which is at least as long (`lift_cycle`).
-/

@[expose] public section

namespace BondyLocke

variable {V : Type*}

/-- Data realising the edges of `H` (on positions `≤ ℓ`) by internally disjoint paths of `G`. -/
structure LiftData (G : SimpleGraph V) (H : SimpleGraph ℕ) (ℓ : ℕ) (φ : ℕ → V)
    (R : ℕ → ℕ → List V) : Prop where
  inj : ∀ s t, s ≤ ℓ → t ≤ ℓ → φ s = φ t → s = t
  chain : ∀ s t, s ≤ ℓ → t ≤ ℓ → H.Adj s t → (φ s :: (R s t ++ [φ t])).IsChain G.Adj
  nodup : ∀ s t, s ≤ ℓ → t ≤ ℓ → H.Adj s t → (R s t).Nodup
  off : ∀ s t, s ≤ ℓ → t ≤ ℓ → H.Adj s t → ∀ z ∈ R s t, ∀ u, u ≤ ℓ → z ≠ φ u
  disj : ∀ s t s' t', s ≤ ℓ → t ≤ ℓ → s' ≤ ℓ → t' ≤ ℓ → H.Adj s t → H.Adj s' t' →
    ∀ z ∈ R s t, z ∈ R s' t' → (s = s' ∧ t = t') ∨ (s = t' ∧ t = s')

/-- The lift of a list of positions: each step `x, y` is replaced by `φ x, R x y`. -/
def liftP (φ : ℕ → V) (R : ℕ → ℕ → List V) : List ℕ → List V
  | [] => []
  | [x] => [φ x]
  | x :: y :: t => φ x :: (R x y ++ liftP φ R (y :: t))

lemma chain_glue_mid {G : SimpleGraph V} {A B : List V} {b : V}
    (hA : (A ++ [b]).IsChain G.Adj) (hB : (b :: B).IsChain G.Adj) :
    (A ++ b :: B).IsChain G.Adj := by
  rw [List.isChain_append] at hA ⊢
  refine ⟨hA.1, hB, fun x hx y hy => ?_⟩
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
  subst hy
  exact hA.2.2 x hx b (by simp)

lemma adj_of_chain_append_singleton {G : SimpleGraph V} {A : List V} {y w : V}
    (hA : (A ++ [y]).IsChain G.Adj) (hw : A.getLast? = some w) : G.Adj w y := by
  rw [List.isChain_append] at hA
  exact hA.2.2 w hw y (by simp)

section lift

variable {G : SimpleGraph V} {H : SimpleGraph ℕ} {ℓ : ℕ} {φ : ℕ → V} {R : ℕ → ℕ → List V}

lemma liftP_spec (hD : LiftData G H ℓ φ R) :
    ∀ (t : List ℕ) (x : ℕ), (x :: t).IsChain H.Adj → (x :: t).Nodup → (∀ z ∈ x :: t, z ≤ ℓ) →
      (liftP φ R (x :: t)).IsChain G.Adj ∧ (liftP φ R (x :: t)).Nodup ∧
      (liftP φ R (x :: t)).head? = some (φ x) ∧
      (liftP φ R (x :: t)).getLast? = (x :: t).getLast?.map φ ∧
      (x :: t).length ≤ (liftP φ R (x :: t)).length ∧
      ∀ z ∈ liftP φ R (x :: t), (∃ u ∈ x :: t, z = φ u) ∨
        ∃ s s', [s, s'] <:+: (x :: t) ∧ H.Adj s s' ∧ z ∈ R s s' := by
  intro t
  induction t with
  | nil =>
    intro x _ _ _
    refine ⟨List.isChain_singleton _, List.nodup_singleton _, rfl, rfl, le_rfl, ?_⟩
    intro z hz
    simp only [liftP, List.mem_singleton] at hz
    exact Or.inl ⟨x, by simp, hz⟩
  | cons y t ih =>
    intro x hc hnd hle
    rw [List.isChain_cons_cons] at hc
    have hxl : x ≤ ℓ := hle x (by simp)
    have hyl : y ≤ ℓ := hle y (by simp)
    have hle' : ∀ z ∈ y :: t, z ≤ ℓ := fun z hz => hle z (List.mem_cons_of_mem _ hz)
    have hx_nm : x ∉ y :: t := (List.nodup_cons.1 hnd).1
    obtain ⟨ihc, ihn, ihh, ihl, ihlen, ihm⟩ := ih y hc.2 (List.nodup_cons.1 hnd).2 hle'
    have hunf : liftP φ R (x :: y :: t) = φ x :: (R x y ++ liftP φ R (y :: t)) := rfl
    obtain ⟨P', hP'⟩ : ∃ P', liftP φ R (y :: t) = φ y :: P' := by
      cases h : liftP φ R (y :: t) with
      | nil => rw [h] at ihh; simp at ihh
      | cons a P' => rw [h] at ihh; simp at ihh; exact ⟨P', by rw [ihh]⟩
    -- membership in the tail lift
    have hmem' : ∀ z ∈ liftP φ R (y :: t), (∃ u ∈ y :: t, z = φ u) ∨
        ∃ s s', [s, s'] <:+: (x :: y :: t) ∧ H.Adj s s' ∧ z ∈ R s s' := by
      intro z hz
      rcases ihm z hz with h | ⟨s, s', hi, ha, hr⟩
      · exact Or.inl h
      · exact Or.inr ⟨s, s', hi.trans (List.suffix_cons _ _).isInfix, ha, hr⟩
    refine ⟨?_, ?_, by rw [hunf]; rfl, ?_, ?_, ?_⟩
    · rw [hunf, hP', ← List.cons_append]
      exact chain_glue_mid (by simpa using hD.chain x y hxl hyl hc.1) (hP' ▸ ihc)
    · rw [hunf, List.nodup_cons, List.nodup_append]
      refine ⟨?_, hD.nodup x y hxl hyl hc.1, ihn, ?_⟩
      · rw [List.mem_append, not_or]
        refine ⟨fun h => hD.off x y hxl hyl hc.1 _ h x hxl rfl, fun h => ?_⟩
        rcases ihm _ h with ⟨u, hu, he⟩ | ⟨s, s', hi, ha, hr⟩
        · have := hD.inj x u hxl (hle' u hu) he
          exact hx_nm (this ▸ hu)
        · exact hD.off s s' (hle' s (hi.subset (by simp))) (hle' s' (hi.subset (by simp))) ha
            _ hr x hxl rfl
      · intro z hz z' hz' hzz
        subst hzz
        rcases ihm _ hz' with ⟨u, hu, he⟩ | ⟨s, s', hi, ha, hr⟩
        · exact hD.off x y hxl hyl hc.1 _ hz u (hle' u hu) he
        · have hs := hi.subset (show s ∈ [s, s'] by simp)
          have hs' := hi.subset (show s' ∈ [s, s'] by simp)
          rcases hD.disj x y s s' hxl hyl (hle' s hs) (hle' s' hs') hc.1 ha z hz hr with
            ⟨h1, -⟩ | ⟨h1, -⟩
          · exact hx_nm (by rw [h1]; exact hs)
          · exact hx_nm (by rw [h1]; exact hs')
    · rw [hunf, ← List.cons_append, List.getLast?_append, ihl, List.getLast?_cons_cons,
        List.getLast?_eq_some_getLast (by simp)]
      simp
    · rw [hunf]; simp only [List.length_cons, List.length_append] at ihlen ⊢; omega
    · intro z hz
      rw [hunf, List.mem_cons, List.mem_append] at hz
      rcases hz with rfl | hz | hz
      · exact Or.inl ⟨x, by simp, rfl⟩
      · exact Or.inr ⟨x, y, ⟨[], t, by simp⟩, hc.1, hz⟩
      · rcases hmem' z hz with ⟨u, hu, he⟩ | h
        · exact Or.inl ⟨u, List.mem_cons_of_mem _ hu, he⟩
        · exact Or.inr h

/-- In a list without repetition having at least three entries, the pair (last, first) is not
a pair of consecutive entries, in either order. -/
lemma not_infix_ends {c : List ℕ} (hnd : c.Nodup) (h3 : 3 ≤ c.length) {x b s s' : ℕ}
    (hx : c.head? = some x) (hb : c.getLast? = some b) (hi : [s, s'] <:+: c)
    (he : (s = b ∧ s' = x) ∨ (s = x ∧ s' = b)) : False := by
  obtain ⟨A, B, rfl⟩ := hi
  have hss : s ≠ s' := by
    intro h; subst h; simp [List.nodup_append] at hnd
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases List.eq_nil_or_concat B with rfl | ⟨B', z, rfl⟩
    · simp at hb; exact hss hb.symm
    · rw [List.concat_eq_append] at hb hnd
      rw [← List.append_assoc, List.getLast?_append, List.getLast?_singleton] at hb
      simp only [Option.some_or, Option.some.injEq] at hb
      subst hb
      simp [List.nodup_append] at hnd
  · rcases A with _ | ⟨a, A⟩
    · rcases List.eq_nil_or_concat B with rfl | ⟨B', z, rfl⟩
      · simp at h3
      · rw [List.concat_eq_append] at hb hnd
        rw [← List.append_assoc, List.getLast?_append, List.getLast?_singleton] at hb
        simp only [Option.some_or, Option.some.injEq] at hb
        subst hb
        simp [List.nodup_append] at hnd
    · have : a = s := by simpa using hx
      subst this
      simp [List.nodup_append] at hnd

/-- **Lifting cycles.** -/
theorem lift_cycle (hD : LiftData G H ℓ φ R) {c : List ℕ} (hc : IsCycleN H c)
    (hcl : ∀ z ∈ c, z ≤ ℓ) : ∃ c', IsCycleN G c' ∧ c.length ≤ c'.length := by
  obtain ⟨⟨hch, hnd⟩, h3, hclose⟩ := hc
  obtain ⟨x, t, rfl⟩ : ∃ x t, c = x :: t := by
    cases c with
    | nil => simp at h3
    | cons x t => exact ⟨x, t, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, (x :: t).getLast? = some b := by
    cases h : (x :: t).getLast? with
    | none => simp at h
    | some b => exact ⟨b, rfl⟩
  have hbx : H.Adj b x := hclose x rfl b hb
  have hbm : b ∈ x :: t := List.mem_of_getLast? hb
  have hxl : x ≤ ℓ := hcl x (by simp)
  have hbl : b ≤ ℓ := hcl b hbm
  obtain ⟨pc, pn, ph, pl, plen, pm⟩ := liftP_spec hD t x hch hnd hcl
  rw [hb, Option.map_some] at pl
  obtain ⟨P0, hP0⟩ : ∃ P0, liftP φ R (x :: t) = P0 ++ [φ b] := by
    rw [List.getLast?_eq_some_iff] at pl; simpa using pl
  have hchord := hD.chain b x hbl hxl hbx
  refine ⟨liftP φ R (x :: t) ++ R b x, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · rw [hP0, List.append_assoc, List.singleton_append]
    refine chain_glue_mid (hP0 ▸ pc) ?_
    rw [← List.cons_append] at hchord
    exact (List.isChain_append.1 hchord).1
  · rw [List.nodup_append]
    refine ⟨pn, hD.nodup b x hbl hxl hbx, ?_⟩
    intro z hz z' hz' hzz
    subst hzz
    rcases pm z hz with ⟨u, hu, he⟩ | ⟨s, s', hi, ha, hr⟩
    · exact hD.off b x hbl hxl hbx _ hz' u (hcl u hu) he
    · have hs := hi.subset (show s ∈ [s, s'] by simp)
      have hs' := hi.subset (show s' ∈ [s, s'] by simp)
      exact not_infix_ends hnd h3 rfl hb hi
        (hD.disj s s' b x (hcl s hs) (hcl s' hs') hbl hxl ha hbx z hr hz')
  · simp only [List.length_append]; omega
  · intro a ha w hw
    rw [List.head?_append, ph] at ha
    simp only [Option.some_or, Option.mem_def, Option.some.injEq] at ha
    subst ha
    rw [hP0, List.append_assoc, List.singleton_append, List.getLast?_append] at hw
    rw [← List.cons_append] at hchord
    have key : (φ b :: R b x).getLast? = some w := by
      cases h : (φ b :: R b x).getLast? with
      | none => simp at h
      | some w' =>
        rw [h] at hw
        cases h' : P0.getLast? <;> simp_all
    exact adj_of_chain_append_singleton hchord key
  · simp only [List.length_append]; omega

end lift

end BondyLocke
