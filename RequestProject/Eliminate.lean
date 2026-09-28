module
public import RequestProject.Orient

/-!
# Eliminating a block (Claim 2.15)

Given a circuit in which the block `G` is active, and an instance of the linking event of
Lemma 2.6 for the interval graph of `G`, we obtain a circuit in which `G` is no longer active
and which uses at least `bound` more matching edges.
-/

@[expose] public section


open Classical

namespace Lovasz

namespace Geo

variable {V ι β : Type*} {g : Geo V ι β}

/-- **Claim 2.15** (one step of the elimination of blocks). -/
theorem eliminate_block {A : Set ι} {G : β} {H : SimpleGraph ι} {U Vs Y : Finset ι}
    {me : ι → ι → V × V} {bound : ℝ} (hblk : g.BlockOK G H U me) (hL : LinkEvent H U Vs Y bound)
    {cs : List (List V)} (hc : g.Circ (g.actI A) cs)
    (hB : ∀ v ∈ cs.flatten, g.vb v = some G → g.iv v ∈ Vs ∪ Y)
    (hU : ∀ v ∈ cs.flatten, g.actI A v → g.vb v = some G → g.iv v ∈ U)
    (hG : ∃ v ∈ cs.flatten, g.actI A v ∧ g.vb v = some G) :
    ∃ cs', g.Circ (g.actI (A \ g.GI G)) cs' ∧
      (g.sz (g.actI A) cs : ℝ) + bound ≤ g.sz (g.actI (A \ g.GI G)) cs' ∧
      (∀ v ∈ cs'.flatten, v ∈ cs.flatten ∨ g.vb v = some G) ∧
      (∀ v ∈ cs.flatten, v ∈ cs'.flatten) := by
  -- a strand ending at an active vertex of `G`
  have hG' : ∃ σ ∈ cs, g.actI A (g.lt σ) ∧ g.vb (g.lt σ) = some G := by
    obtain ⟨v, hv, hva, hvG⟩ := hG
    obtain ⟨σ, hσ, hvσ⟩ := List.mem_flatten.1 hv
    rcases g.mem_ends_of_act (hc.strand σ hσ) hvσ hva with rfl | rfl
    · obtain ⟨q, hq, hq2⟩ := exists_cpairs_snd hσ
      have hj := hc.join q hq
      rw [hq2] at hj
      rcases hj with ⟨h1, -, G', h3, h4⟩ | ⟨-, h2, -⟩
      · exact ⟨q.1, mem_of_mem_cpairs_fst hq, h1, by rw [h3, ← h4, hvG]⟩
      · exact absurd hva h2
    · exact ⟨σ, hσ, hva, hvG⟩
  obtain ⟨Rs, k0, hRs, hflat⟩ := g.exists_runs hc hG'
  have hvRs : ∀ v, (∃ R ∈ Rs, v ∈ R.flatten) ↔ v ∈ cs.flatten := by
    intro v
    have e : Rs.flatten.flatten.Perm cs.flatten := by
      rw [hflat]; exact (List.rotate_perm cs k0).flatten
    rw [← e.mem_iff, List.flatten_flatten, List.mem_flatten]
    constructor
    · rintro ⟨R, hR, hv⟩; exact ⟨R.flatten, List.mem_map.2 ⟨R, hR, rfl⟩, hv⟩
    · rintro ⟨_, hl, hv⟩; obtain ⟨R, hR, rfl⟩ := List.mem_map.1 hl; exact ⟨R, hR, hv⟩
  have hendsRs : ∀ e, g.IsEnd Rs e → e ∈ cs.flatten ∧ g.actI A e ∧ g.vb e = some G := by
    rintro e ⟨R, hR, rfl | rfl⟩
    · have hr := hRs.run R hR
      exact ⟨(hvRs _).1 ⟨R, hR, g.rhd_mem hr⟩, hr.hd_act, hr.hd_G⟩
    · have hr := hRs.run R hR
      exact ⟨(hvRs _).1 ⟨R, hR, g.rlt_mem hr⟩, hr.lt_act, hr.lt_G⟩
  obtain ⟨A', hA', Rs', hRs', hsz1, hP, hends, hmem, hdeact, hold⟩ :=
    g.normalize _ A Rs rfl hRs
  -- the linking event
  obtain ⟨As, hAs, hAi, hAe, P, hPA, hbound⟩ := hL (Rs'.map g.junc)
    (by simpa using hRs'.ne) (jEntries_nodup_of_pairwise hP) (by
      intro v hv
      obtain ⟨p, hp, hvp⟩ := mem_jEntries.1 hv
      obtain ⟨R', hR', rfl⟩ := List.mem_map.1 hp
      have key : ∀ e, g.IsEnd Rs e → g.iv e ∈ U ∧ (g.iv e ∈ Vs ∨ g.iv e ∈ Y) := by
        intro e he
        obtain ⟨h1, h2, h3⟩ := hendsRs e he
        exact ⟨hU e h1 h2 h3, Finset.mem_union.1 (hB e h1 h3)⟩
      rcases hvp with rfl | rfl
      · exact key _ (hends R' hR').1
      · exact key _ (hends R' hR').2)
  have hpre : g.LinkPre A' G H U (Vs ∪ Y) me Rs' As := by
    refine ⟨hblk, hRs', hP, ?_, hAs, hAi, hAe⟩
    intro R' hR' v hv hvG
    rcases hmem R' hR' v hv with hv' | ⟨J, hJA, hJA', hvJ⟩
    · exact hB v ((hvRs v).1 hv') hvG
    · obtain ⟨e, he, heJ⟩ := hdeact J hJA hJA'
      obtain ⟨h1, -, h3⟩ := hendsRs e he
      have := hB e h1 h3
      have e1 : g.iv v = J := by simp [iv, hvJ]
      have e2 : g.iv e = J := by simp [iv, heJ]
      rwa [e1, ← e2]
  obtain ⟨Ro, hLH, hsum, hv1, hv2⟩ := hpre.orient_runs
  obtain ⟨cs', hc', hsz', hv1', hv2'⟩ := hLH.assemble
  -- the deactivated intervals belong to `G`
  have hAeq : A' \ g.GI G = A \ g.GI G := by
    ext J
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨hA' h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨by_contra fun h3 => ?_, h2⟩
      obtain ⟨e, he, heJ⟩ := hdeact J h1 h3
      exact h2 (blk_of_vb heJ (hendsRs e he).2.2)
  rw [hAeq] at hc' hsz'
  refine ⟨cs', hc', ?_, ?_, ?_⟩
  · have e0 : g.sz (g.actI A) cs = (Rs.map (g.szR (g.actI A))).sum := by
      rw [← g.sz_rotate _ cs k0, ← hflat]; exact (hRs.circ g).2
    have h1 := hsz' P hPA
    have h2 : (P.length : ℝ) - 1 ≤ ((P.length - 1 : ℕ) : ℝ) := by
      rcases Nat.eq_zero_or_pos P.length with h | h
      · simp [h]
      · rw [Nat.cast_sub h]; simp
    have h3 : ((g.sz (g.actI A) cs + (P.length - 1) : ℕ) : ℝ) ≤
        g.sz (g.actI (A \ g.GI G)) cs' := by
      exact_mod_cast (by omega : g.sz (g.actI A) cs + (P.length - 1) ≤
        g.sz (g.actI (A \ g.GI G)) cs')
    push_cast at h3
    linarith
  · intro v hv
    rcases hv1' v hv with ⟨R, hR, hvR⟩ | hvG
    · obtain ⟨R', hR', hvR'⟩ := hv1 R hR v hvR
      rcases hmem R' hR' v hvR' with hv' | ⟨J, hJA, hJA', hvJ⟩
      · exact Or.inl ((hvRs v).1 hv')
      · obtain ⟨e, he, heJ⟩ := hdeact J hJA hJA'
        exact Or.inr (vb_of_blk hvJ (blk_of_vb heJ (hendsRs e he).2.2))
    · exact Or.inr hvG
  · intro v hv
    obtain ⟨R, hR, hvR⟩ := (hvRs v).2 hv
    obtain ⟨R', hR', hvR'⟩ := hold R hR v hvR
    obtain ⟨R'', hR'', hvR''⟩ := hv2 R' hR' v hvR'
    exact hv2' R'' hR'' v hvR''

end Geo

end Lovasz
