module
public import RequestProject.Eliminate

/-!
# Eliminating all blocks

Applying Claim 2.15 to every block in turn, we turn a circuit into a path of `L ∪ M` using at
least as many edges of `M` as the circuit plus the sum of the gains.
-/

@[expose] public section


open Classical

namespace Lovasz

namespace Geo

variable {V ι β : Type*} {g : Geo V ι β}

/-- **Eliminating all blocks**: the final step of the proof of Theorem 1.2. -/
theorem eliminate_all (H : β → SimpleGraph ι) (U Vs Y : β → Finset ι) (me : β → ι → ι → V × V)
    (bound : β → ℝ) (S : Finset β) : ∀ (A : Set ι) (cs : List (List V)),
    (∀ J ∈ A, ∃ G ∈ S, g.blk J = some G) → g.Circ (g.actI A) cs →
    (∀ G ∈ S, g.BlockOK G (H G) (U G) (me G)) →
    (∀ G ∈ S, LinkEvent (H G) (U G) (Vs G) (Y G) (bound G)) →
    (∀ G ∈ S, ∀ v ∈ cs.flatten, g.vb v = some G → g.iv v ∈ Vs G ∪ Y G) →
    (∀ G ∈ S, ∀ v ∈ cs.flatten, g.actI A v → g.vb v = some G → g.iv v ∈ U G) →
    (∀ G ∈ S, ∃ v ∈ cs.flatten, g.actI A v ∧ g.vb v = some G) →
    ∃ l, IsPathL g.Γ l ∧
      (g.sz (g.actI A) cs : ℝ) + ∑ G ∈ S, bound G ≤ countPairs g.Mp l + 1 := by
  induction S using Finset.induction_on with
  | empty =>
    intro A cs hA hc _ _ _ _ _
    have hna : ∀ v ∈ cs.flatten, ¬ g.actI A v := by
      rintro v - ⟨J, -, hJ⟩
      obtain ⟨G, hG, -⟩ := hA J hJ
      simp at hG
    obtain ⟨hp, hsz⟩ := hc.path g hna
    refine ⟨cs.flatten, hp, ?_⟩
    simp only [Finset.sum_empty, add_zero]
    exact_mod_cast hsz
  | insert G S hGS ih =>
    intro A cs hA hc hblk hL hB hU hG
    obtain ⟨cs', hc', hsz, hv1, hv2⟩ := eliminate_block (hblk G (by simp)) (hL G (by simp)) hc
      (hB G (by simp)) (hU G (by simp)) (hG G (by simp))
    have hne : ∀ G' ∈ S, G' ≠ G := fun G' hG' h => hGS (h ▸ hG')
    have hact : ∀ G' ∈ S, ∀ v, g.vb v = some G' →
        (g.actI (A \ g.GI G) v ↔ g.actI A v) := by
      intro G' hG' v hv
      rw [g.actI_diff_GI]
      constructor
      · exact fun h => h.1
      · intro h; refine ⟨h, ?_⟩; rw [hv]; simpa using hne G' hG'
    obtain ⟨l, hl, hsz'⟩ := ih (A \ g.GI G) cs' (by
        rintro J ⟨hJA, hJG⟩
        obtain ⟨G', hG', hJ⟩ := hA J hJA
        rcases Finset.mem_insert.1 hG' with rfl | hG'
        · exact absurd hJ hJG
        · exact ⟨G', hG', hJ⟩) hc'
      (fun G' hG' => hblk G' (by simp [hG'])) (fun G' hG' => hL G' (by simp [hG']))
      (by
        intro G' hG' v hv hvG
        rcases hv1 v hv with hv | hv
        · exact hB G' (by simp [hG']) v hv hvG
        · rw [hv, Option.some.injEq] at hvG; exact absurd hvG.symm (hne G' hG'))
      (by
        intro G' hG' v hv hva hvG
        rcases hv1 v hv with hv | hv
        · exact hU G' (by simp [hG']) v hv ((hact G' hG' v hvG).1 hva) hvG
        · rw [hv, Option.some.injEq] at hvG; exact absurd hvG.symm (hne G' hG'))
      (by
        intro G' hG'
        obtain ⟨v, hv, hva, hvG⟩ := hG G' (by simp [hG'])
        exact ⟨v, hv2 v hv, (hact G' hG' v hvG).2 hva, hvG⟩)
    refine ⟨l, hl, ?_⟩
    rw [Finset.sum_insert hGS]
    linarith

end Geo

end Lovasz
