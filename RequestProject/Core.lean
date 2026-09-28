module
public import RequestProject.Decomp
public import RequestProject.LinkingCore

/-!
# The probabilistic core of the proof of Theorem 1.2

Starting from a circuit visiting the blocks, we decompose it into block-simple circuits, select a
heavy component of a random subfamily (Lemma 2.8), couple the jump ends with random sets
(Lemma 2.7), apply the linking lemma (Lemma 2.6) to every block and finally eliminate all blocks
(Claim 2.15).
-/

@[expose] public section


open scoped BigOperators
open Classical

namespace Lovasz

noncomputable section

namespace Geo

variable {V ι β : Type*} {g : Geo V ι β}

/-- The two ends of a junction are distinct. -/
lemma Circ.lt_ne_hd {act : V → Prop} {cs : List (List V)} (h : g.Circ act cs)
    {p : List V × List V} (hp : p ∈ cpairs cs) : g.lt p.1 ≠ g.hd p.2 := by
  obtain ⟨k, hne, h1, h2⟩ := exists_rotate_wrap hp
  have hc := Circ.rotate g h k
  set Z := cs.rotate k
  obtain ⟨a, t, hZ⟩ := List.exists_cons_of_ne_nil hne
  have kL : Z.getLast hne = (a :: t).getLast (by simp) := by simp only [hZ]
  have kH : Z.head hne = (a :: t).head (by simp) := by simp only [hZ]
  rw [h1] at kL
  rw [h2] at kH
  have hsa := hc.strand a (by rw [hZ]; simp)
  have ha : a ≠ [] := g.ne_nil_of_strand hsa
  rcases eq_or_ne t [] with rfl | ht
  · have e1 : p.1 = a := by rw [kL]; simp
    have e2 : p.2 = a := by rw [kH]; simp
    rw [e1, e2]
    obtain ⟨b, u, rfl⟩ := List.exists_cons_of_ne_nil ha
    have hu : u ≠ [] := by rintro rfl; have := hsa.two_le; simp at this
    have hnd : (b :: u).Nodup := by
      have := hc.nodup; rw [hZ] at this; simpa using this
    rw [g.lt_eq_getLast (by simp), List.getLast_cons hu, g.hd_eq_head (by simp), List.head_cons]
    intro e
    exact (List.nodup_cons.1 hnd).1 (e ▸ List.getLast_mem hu)
  · have e1 : p.1 = t.getLast ht := by rw [kL, List.getLast_cons ht]
    have e2 : p.2 = a := by rw [kH]; simp
    have hb := hc.strand (t.getLast ht) (by rw [hZ]; exact List.mem_cons_of_mem _ (List.getLast_mem ht))
    have hnd := hc.nodup
    rw [hZ, List.flatten_cons, List.nodup_append] at hnd
    rw [e1, e2]
    intro e
    have hx1 : g.hd a ∈ a := g.hd_mem ha
    have hx2 : g.hd a ∈ t.flatten := List.mem_flatten.2 ⟨_, List.getLast_mem ht,
      e ▸ g.lt_mem (g.ne_nil_of_strand hb)⟩
    exact hnd.2.2 _ hx1 _ hx2 rfl

/-- An active vertex of a circuit lies on a jump of its block. -/
lemma Circ.jumpAt_of_vertex {act : V → Prop} {cs : List (List V)} (h : g.Circ act cs) {v : V}
    (hv : v ∈ cs.flatten) (hva : act v) {G : β} (hvG : g.vb v = some G) : g.JumpAt act cs G := by
  obtain ⟨σ, hσ, hvσ⟩ := List.mem_flatten.1 hv
  have hst := h.strand σ hσ
  rcases g.mem_strand_cases hst hvσ with rfl | rfl | hin
  · obtain ⟨q, hq, rfl⟩ := exists_cpairs_snd hσ
    have hqa := h.act_hd hq hva
    obtain ⟨-, hqG⟩ := h.jump_of_act hq hqa
    exact ⟨q, hq, hqa, by rw [← hqG, hvG]⟩
  · exact jumpAt_iff.2 ⟨σ, hσ, hva, hvG⟩
  · exact absurd hva (hst.inner_na v hin)

end Geo

/-- One block's share of the union bound: coupling the jump ends of the selected pieces with a
random set of intervals (Lemma 2.7), the linking event fails with small probability. -/
lemma coupling_link_fail {κ ι : Type} [Fintype κ] [Fintype ι] (E : Finset κ) (e₁ e₂ : κ → ι)
    (hdeg : ∀ v, (E.filter (fun c => e₁ c = v)).card + (E.filter (fun c => e₂ c = v)).card ≤ 2)
    {r η : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (Ev : Finset ι → Prop)
    (hEv : 1 - η ≤ ppr (fun _ : ι => bern r) (fun y => Ev (Finset.univ.filter (fun v => y v = true)))) :
    ppr (fun _ : κ => bern (r ^ 2 / 4))
      (fun x => ¬ ∃ Y, endsSet E e₁ e₂ x ⊆ Y ∧ Ev Y) ≤ η := by
  have hsq : 2 * Real.sqrt (r ^ 2 / 4) = r := by
    rw [Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 4), Real.sqrt_sq hr0,
      show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]; ring
  have h := coupling_domination E e₁ e₂ hdeg (p := r ^ 2 / 4) (by positivity) (by nlinarith)
    (fun A => ¬ ∃ Y, A ⊆ Y ∧ Ev Y)
    (fun A B hAB hA ⟨Y, hY, hEY⟩ => hA ⟨Y, hAB.trans hY, hEY⟩)
  rw [hsq] at h
  have hμ : IsPD (fun _ : ι => bern r) := isPD_bern hr0 hr1
  refine h.trans ((ppr_mono hμ fun y hy => fun hE => hy ⟨_, subset_rfl, hE⟩).trans ?_)
  rw [ppr_not hμ]; linarith


namespace Geo

variable {V ι β : Type*} {g : Geo V ι β}

lemma vb_eq_some {v : V} {G : β} : g.vb v = some G ↔ ∃ J, g.ivOf v = some J ∧ g.blk J = some G := by
  unfold vb; exact Option.bind_eq_some_iff

lemma actI_iff {Pr : β → Prop} {v : V} :
    g.actI {J | ∃ G, g.blk J = some G ∧ Pr G} v ↔ ∃ G, g.vb v = some G ∧ Pr G := by
  unfold actI
  simp only [Set.mem_setOf_eq, vb_eq_some]
  constructor
  · rintro ⟨J, h1, G, h2, h3⟩; exact ⟨G, ⟨J, h1, h2⟩, h3⟩
  · rintro ⟨G, ⟨J, h1, h2⟩, h3⟩; exact ⟨J, h1, G, h2, h3⟩

lemma iv_eq {v : V} {J : ι} (h : g.ivOf v = some J) : g.iv v = J := by
  simp [iv, h]

end Geo

open Geo in
/-- **The probabilistic core of the proof of Theorem 1.2.** -/
theorem core_path {V ι β : Type} [Fintype ι] [Fintype β] (g : Geo V ι β) {c N₀ Kc : ℕ}
    (hL : LinkingBody c N₀)
    (H : β → SimpleGraph ι) (U : β → Finset ι) (me : β → ι → ι → V × V)
    (hblk : ∀ G, g.BlockOK G (H G) (U G) (me G))
    (hU : ∀ J G, g.blk J = some G → J ∈ U G)
    (cs : List (List V)) (hcs : g.Circ (g.actI {J | ∃ G, g.blk J = some G ∧ True}) cs)
    (hj : ∃ G, g.JumpAt (g.actI {J | ∃ G, g.blk J = some G ∧ True}) cs G)
    {x E A r q D s δ : ℝ} {k : ℕ} (hk : 1 ≤ k) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hkp : (k : ℝ) ^ (-δ) ≤ r ^ 2 / 4) (hkA : 6 * (k : ℝ) ≤ A)
    (hKc : 1 ≤ Kc) (hr : 0 < r) (hq : 0 < q) (hq1 : q < 1) (hcol : 10 * r + 3 * q ≤ 1)
    (hE : E ≤ 4 * D) (hmin : ∀ G, ∀ v ∈ U G, D ≤ degIn (H G) (U G) v)
    (hmax : ∀ G, ∀ v ∈ U G, (degIn (H G) (U G) v : ℝ) ≤ 4 * D)
    (hUx : ∀ G, ((U G).card : ℝ) ≤ x) (hexp : ∀ G, IsExpander (H G) (U G) (1 / 8) c s)
    (hs : E / (8 * Real.log x ^ c) ≤ s)
    (n1 : A ≤ E / 128) (n2 : 13 ≤ E) (n3 : 4 * c * Real.log 2 ≤ Real.log (E / 4))
    (n4 : Real.log 2 ≤ Real.log (E / 4)) (n5 : 48 * Real.log x ^ c * A ≤ E / 4)
    (n6 : (N₀ : ℝ) ≤ E / 8)
    (n7 : 2 * Real.log x ^ (9 * c + 21) / (q / Kc) ^ 10 ≤ E / (8 * Real.log x ^ c))
    (n7' : 2 * Real.log x ^ (9 * c + 21) / (q / Kc) ^ 10 ≤ E / 64)
    (n8 : 100 * Real.log x ^ (7 * c + 19) / (q / Kc) ^ 6 ≤ 31 / 32 / (120 * r) - 1)
    (n9 : x * Real.exp (-(12 * r * E)) + x * Real.exp (2 * A - r * E / 13) +
      Real.exp (1 - r * E / 2) + 3 * (8 / E) ^ Kc ≤ x ^ (-3 : ℝ))
    (n10 : 4 ≤ r * E) (hx1 : 1 ≤ x)
    (hprob : (Fintype.card β : ℝ) * x ^ (-3 : ℝ) <
      (∑ G ∈ Finset.univ.filter (g.JumpAt (g.actI {J | ∃ G, g.blk J = some G ∧ True}) cs),
        ((U G).card : ℝ)) ^ (-δ) / 2) :
    ∃ l, IsPathL g.Γ l ∧
      r * ((∑ G ∈ Finset.univ.filter (g.JumpAt (g.actI {J | ∃ G, g.blk J = some G ∧ True}) cs),
        ((U G).card : ℝ)) ^ (1 - δ) / 2) ≤ countPairs g.Mp l + 1 := by
  set act₀ := g.actI {J | ∃ G, g.blk J = some G ∧ True} with hact₀
  have hact₀' : ∀ v, act₀ v ↔ ∃ G, g.vb v = some G := fun v => by
    rw [hact₀, actI_iff]; simp
  obtain ⟨P, hP1, hP2, hP3, hP4⟩ := Circ.decomp (g := g) cs.length cs le_rfl hcs hj
  set m := P.length with hm_def
  have hm : 0 < m := by
    obtain ⟨G, hG⟩ := hj
    obtain ⟨c₁, hc₁, -⟩ := (hP3 G).2 hG
    exact List.length_pos_of_mem hc₁
  set pc : Fin m → List (List V) := fun i => P.get i with hpc_def
  have hpc : ∀ i, pc i ∈ P := fun i => List.get_mem P i
  have hpcC : ∀ i, g.Circ act₀ (pc i) := fun i => (hP1 _ (hpc i)).1
  have hpcS : ∀ i, g.BSimple act₀ (pc i) := fun i => (hP1 _ (hpc i)).2.1
  set Vs : Fin m → Finset β := fun i => Finset.univ.filter (g.JumpAt act₀ (pc i)) with hVs_def
  have hVs : ∀ i G, G ∈ Vs i ↔ g.JumpAt act₀ (pc i) G := fun i G => by simp [hVs_def]
  have hdisj : ∀ i j, i ≠ j → ∀ v ∈ (pc i).flatten, v ∉ (pc j).flatten := by
    have hnd : (P.map List.flatten).flatten.Nodup := hP2.nodup_iff.2 hcs.nodup
    rw [List.nodup_flatten] at hnd
    have hpw := List.pairwise_iff_getElem.1 hnd.2
    intro i j hij v hvi hvj
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
    · exact hpw i j (by simp; exact (Fin.isLt _)) (by simp; exact (Fin.isLt _)) h (by simpa [hpc_def] using hvi)
        (by simpa [hpc_def] using hvj)
    · exact hpw j i (by simp; exact (Fin.isLt _)) (by simp; exact (Fin.isLt _)) h (by simpa [hpc_def] using hvj)
        (by simpa [hpc_def] using hvi)
  have hpcne : ∀ i, ∃ v, v ∈ (pc i).flatten := by
    intro i
    obtain ⟨σ, hσ⟩ := List.exists_mem_of_ne_nil _ (hpcC i).ne
    exact ⟨g.hd σ, List.mem_flatten.2 ⟨σ, hσ, g.hd_mem (g.ne_nil_of_strand ((hpcC i).strand σ hσ))⟩⟩
  have hpcinj : ∀ i j, pc i = pc j → i = j := by
    intro i j e
    by_contra hij
    obtain ⟨v, hv⟩ := hpcne i
    exact hdisj i j hij v hv (e ▸ hv)
  have hpcsurj : ∀ c ∈ P, ∃ i, pc i = c := fun c hc => by
    obtain ⟨n, hn⟩ := List.mem_iff_get.1 hc
    exact ⟨n, hn⟩
  set c₀ : Fin m := ⟨0, hm⟩
  have hconn : ∀ i ∈ (Finset.univ : Finset (Fin m)), ReachC Vs Finset.univ c₀ i := by
    have lift : ∀ a b, Relation.ReflTransGen (fun a b => a ∈ P ∧ b ∈ P ∧
        ∃ G, g.JumpAt act₀ a G ∧ g.JumpAt act₀ b G) a b →
        ∀ i₁, pc i₁ = a → ∃ j, pc j = b ∧ ReachC Vs Finset.univ i₁ j := by
      intro a b hab
      induction hab with
      | refl => exact fun i₁ h => ⟨i₁, h, Relation.ReflTransGen.refl⟩
      | @tail b' b _ hbb ih =>
        intro i₁ h
        obtain ⟨j', hj', hr⟩ := ih i₁ h
        obtain ⟨-, hb, G, hG1, hG2⟩ := hbb
        obtain ⟨j, hj⟩ := hpcsurj b hb
        refine ⟨j, hj, hr.tail ⟨Finset.mem_univ _, Finset.mem_univ _, G, ?_⟩⟩
        rw [Finset.mem_inter, hVs, hVs, hj', hj]
        exact ⟨hG1, hG2⟩
    intro i _
    obtain ⟨j, hj, hr⟩ := lift _ _ (hP4 _ (hpc c₀) _ (hpc i)) c₀ rfl
    rwa [hpcinj j i hj] at hr
  set W := ∑ G ∈ Finset.univ.filter (g.JumpAt act₀ cs), ((U G).card : ℝ) with hW_def
  have hcov : wsum (fun G => (U G).card) (cov Vs Finset.univ) = W := by
    have : cov Vs Finset.univ = Finset.univ.filter (g.JumpAt act₀ cs) := by
      ext G
      simp only [cov, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter, hVs]
      rw [← hP3]
      constructor
      · rintro ⟨i, hi⟩; exact ⟨pc i, hpc i, hi⟩
      · rintro ⟨c', hc', hG⟩
        obtain ⟨i, rfl⟩ := hpcsurj c' hc'
        exact ⟨i, hG⟩
    rw [this, wsum]
  have hWpos : 0 < W := by
    obtain ⟨G, p, hp, hpa, hpG⟩ := hj
    obtain ⟨J, hJ1, hJ2⟩ := vb_eq_some.1 hpG
    have hJU := hU J G hJ2
    have h1 : (0 : ℝ) < (U G).card := by exact_mod_cast Finset.card_pos.2 ⟨J, hJU⟩
    refine lt_of_lt_of_le h1 ?_
    exact Finset.single_le_sum (f := fun G => ((U G).card : ℝ)) (fun _ _ => Nat.cast_nonneg _)
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, p, hp, hpa, hpG⟩)
  have hr1 : r ≤ 1 := by linarith
  obtain ⟨Hs, -, hH3, hHprob⟩ := heavy_component (Vs := Vs) (fun G => (U G).card) hk hδ0 hδ1 hkp
    (by nlinarith) Finset.univ c₀ (Finset.mem_univ _) hconn (by rw [hcov]; exact hWpos)
  rw [hcov] at hHprob
  -- the jump of piece `i` in block `G`
  have hjex : ∀ G i, ∃ p : List V × List V, g.JumpAt act₀ (pc i) G →
      p ∈ cpairs (pc i) ∧ act₀ (g.lt p.1) ∧ g.vb (g.lt p.1) = some G := by
    intro G i
    by_cases h : g.JumpAt act₀ (pc i) G
    · obtain ⟨p, hp⟩ := h; exact ⟨p, fun _ => hp⟩
    · exact ⟨([], []), fun h' => absurd h' h⟩
  choose jp hjp using hjex
  set e₁ : β → Fin m → ι := fun G i => g.iv (g.lt (jp G i).1) with he₁
  set e₂ : β → Fin m → ι := fun G i => g.iv (g.hd (jp G i).2) with he₂
  set EG : β → Finset (Fin m) := fun G => Finset.univ.filter (fun i => G ∈ Vs i) with hEG
  set VD : β → Finset ι := fun G => (Hs.filter (fun i => G ∈ Vs i)).image (e₁ G) ∪
    (Hs.filter (fun i => G ∈ Vs i)).image (e₂ G) with hVD
  set Good : β → (Fin m → Bool) → Prop := fun G y =>
    ∃ Y, endsSet (EG G) (e₁ G) (e₂ G) y ⊆ Y ∧ LinkEvent (H G) (U G) (VD G) Y (r * (U G).card)
    with hGood
  -- the ends of the jumps lie in the block
  have hjp' : ∀ G i, G ∈ Vs i → jp G i ∈ cpairs (pc i) ∧ act₀ (g.lt (jp G i).1) ∧
      g.vb (g.lt (jp G i).1) = some G := fun G i h => hjp G i ((hVs i G).1 h)
  have hend : ∀ G i, G ∈ Vs i → e₁ G i ∈ U G ∧ e₂ G i ∈ U G := by
    intro G i hGi
    obtain ⟨hp, hpa, hpG⟩ := hjp' G i hGi
    obtain ⟨hpa2, hpG2⟩ := (hpcC i).jump_of_act hp hpa
    obtain ⟨J, hJ1, hJ2⟩ := vb_eq_some.1 hpG
    obtain ⟨J', hJ1', hJ2'⟩ := vb_eq_some.1 (hpG2.trans hpG)
    exact ⟨by rw [he₁]; dsimp only; rw [iv_eq hJ1]; exact hU J G hJ2,
      by rw [he₂]; dsimp only; rw [iv_eq hJ1']; exact hU J' G hJ2'⟩
  have hdeg : ∀ G J, ((EG G).filter (fun i => e₁ G i = J)).card +
      ((EG G).filter (fun i => e₂ G i = J)).card ≤ 2 := by
    intro G J
    set F₁ := (EG G).filter (fun i => e₁ G i = J)
    set F₂ := (EG G).filter (fun i => e₂ G i = J)
    have hF : ∀ i, i ∈ F₁ ∨ i ∈ F₂ → G ∈ Vs i := by
      rintro i (hi | hi) <;> exact (Finset.mem_filter.1 (Finset.mem_filter.1 hi).1).2
    have hm1 : ∀ i, G ∈ Vs i → g.lt (jp G i).1 ∈ (pc i).flatten := fun i hi =>
      List.mem_flatten.2 ⟨_, mem_of_mem_cpairs_fst (hjp' G i hi).1,
        g.lt_mem (g.ne_nil_of_strand ((hpcC i).strand _ (mem_of_mem_cpairs_fst (hjp' G i hi).1)))⟩
    have hm2 : ∀ i, G ∈ Vs i → g.hd (jp G i).2 ∈ (pc i).flatten := fun i hi =>
      List.mem_flatten.2 ⟨_, mem_of_mem_cpairs_snd (hjp' G i hi).1,
        g.hd_mem (g.ne_nil_of_strand ((hpcC i).strand _ (mem_of_mem_cpairs_snd (hjp' G i hi).1)))⟩
    have hinj1 : Set.InjOn (fun i => g.lt (jp G i).1) F₁ := by
      intro i hi j hj e
      by_contra hij
      exact hdisj i j hij _ (hm1 i (hF i (Or.inl hi))) (by
        simp only at e; rw [e]; exact hm1 j (hF j (Or.inl hj)))
    have hinj2 : Set.InjOn (fun i => g.hd (jp G i).2) F₂ := by
      intro i hi j hj e
      by_contra hij
      exact hdisj i j hij _ (hm2 i (hF i (Or.inr hi))) (by
        simp only at e; rw [e]; exact hm2 j (hF j (Or.inr hj)))
    have hdj : Disjoint (F₁.image (fun i => g.lt (jp G i).1)) (F₂.image (fun i => g.hd (jp G i).2)) := by
      rw [Finset.disjoint_left]
      intro v hv1 hv2
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hv1
      obtain ⟨j, hj, e⟩ := Finset.mem_image.1 hv2
      by_cases hij : i = j
      · subst hij
        exact (hpcC i).lt_ne_hd (hjp' G i (hF i (Or.inl hi))).1 e.symm
      · exact hdisj i j hij _ (hm1 i (hF i (Or.inl hi))) (e ▸ hm2 j (hF j (Or.inr hj)))
    have hsub : F₁.image (fun i => g.lt (jp G i).1) ∪ F₂.image (fun i => g.hd (jp G i).2) ⊆
        {g.lo J, g.hi J} := by
      intro v hv
      rcases Finset.mem_union.1 hv with hv | hv
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hv
        have hGi := hF i (Or.inl hi)
        obtain ⟨hp, hpa, -⟩ := hjp' G i hGi
        obtain ⟨J', hJ1, hJ2⟩ := ((hpcC i).strand _ (mem_of_mem_cpairs_fst hp)).lt_bd hpa
        have : J' = J := by
          have := (Finset.mem_filter.1 hi).2; rw [he₁] at this; dsimp only at this
          rwa [iv_eq hJ1] at this
        subst this
        rcases hJ2 with h | h <;> simp [h]
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hv
        have hGi := hF i (Or.inr hi)
        obtain ⟨hp, hpa, -⟩ := hjp' G i hGi
        have hpa2 := ((hpcC i).jump_of_act hp hpa).1
        obtain ⟨J', hJ1, hJ2⟩ := ((hpcC i).strand _ (mem_of_mem_cpairs_snd hp)).hd_bd hpa2
        have : J' = J := by
          have := (Finset.mem_filter.1 hi).2; rw [he₂] at this; dsimp only at this
          rwa [iv_eq hJ1] at this
        subst this
        rcases hJ2 with h | h <;> simp [h]
    calc F₁.card + F₂.card = (F₁.image (fun i => g.lt (jp G i).1)).card +
          (F₂.image (fun i => g.hd (jp G i).2)).card := by
          rw [Finset.card_image_of_injOn hinj1, Finset.card_image_of_injOn hinj2]
      _ = (F₁.image (fun i => g.lt (jp G i).1) ∪ F₂.image (fun i => g.hd (jp G i).2)).card :=
          (Finset.card_union_of_disjoint hdj).symm
      _ ≤ ({g.lo J, g.hi J} : Finset V).card := Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two
  have hfail : ∀ G, ppr (fun _ => bern (r ^ 2 / 4)) (fun y => ¬ Good G y) ≤ x ^ (-3 : ℝ) := by
    intro G
    have hVDU : VD G ⊆ U G := by
      intro J hJ
      rcases Finset.mem_union.1 hJ with hJ | hJ <;>
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hJ
        have := hend G i (Finset.mem_filter.1 hi).2
        first | exact this.1 | exact this.2
    have hVDc : ((VD G).card : ℝ) ≤ A := by
      have h1 : (VD G).card ≤ 2 * (3 * k) := by
        refine (Finset.card_union_le _ _).trans ?_
        have := hH3 G
        have a1 := Finset.card_image_le (s := Hs.filter (fun i => G ∈ Vs i)) (f := e₁ G)
        have a2 := Finset.card_image_le (s := Hs.filter (fun i => G ∈ Vs i)) (f := e₂ G)
        omega
      have : ((VD G).card : ℝ) ≤ 2 * (3 * k) := by exact_mod_cast h1
      linarith
    exact coupling_link_fail (EG G) (e₁ G) (e₂ G) (hdeg G) hr.le hr1 _
      (linking_core hL (H G) (U G) (VD G) hKc hr hq hq1 hcol hE (hmin G) (hmax G) (hUx G)
        (hexp G) hs hVDU hVDc n1 n2 n3 n4 n5 n6 n7 n7' n8 n9 n10 hx1)
  -- the union bound
  obtain ⟨y, hheavy, hgood⟩ : ∃ y : Fin m → Bool, W ^ (1 - δ) / 2 ≤
      wsum (fun G => (U G).card) (compV Vs (Finset.univ.filter (fun c => y c = true) ∪ Hs) {c₀}) ∧
      ∀ G, Good G y := by
    have hμ : IsPD (fun (_ : Fin m) => bern (r ^ 2 / 4)) := isPD_bern (by positivity) (by nlinarith)
    have h1 := ppr_and_ge hμ (fun y => W ^ (1 - δ) / 2 ≤ wsum (fun G => (U G).card)
      (compV Vs (Finset.univ.filter (fun c => y c = true) ∪ Hs) {c₀})) (fun y => ∀ G, Good G y)
    have h2 : ppr (fun _ => bern (r ^ 2 / 4)) (fun y => ¬ ∀ G, Good G y) ≤
        (Fintype.card β : ℝ) * x ^ (-3 : ℝ) := by
      refine (ppr_mono hμ (Q := fun y => ∃ G ∈ (Finset.univ : Finset β), ¬ Good G y)
        (fun y hy => by push_neg at hy; obtain ⟨G, hG⟩ := hy; exact ⟨G, Finset.mem_univ _, hG⟩)).trans ?_
      refine (ppr_exists_le hμ _ _).trans ?_
      refine (Finset.sum_le_sum fun G _ => hfail G).trans ?_
      simp
    refine exists_of_ppr_pos (lt_of_lt_of_le ?_ h1)
    rw [sub_pos]
    refine lt_of_lt_of_le (h2.trans_lt hprob) ?_
    convert hHprob
  set B := Finset.univ.filter (fun c => y c = true) ∪ Hs with hB
  have hc₀B : c₀ ∈ B := by
    by_contra hc
    have : compV Vs B {c₀} = ∅ := by
      ext G; simp [compV, hc]
    rw [this] at hheavy
    have : 0 < W ^ (1 - δ) := Real.rpow_pos_of_pos hWpos _
    simp [wsum] at hheavy
    linarith
  obtain ⟨Z, hZc, hZv, hZj⟩ := merge_component (g := g) pc Vs hVs hpcC hdisj B hc₀B
  set K := B.filter (fun j => ReachC Vs B c₀ j) with hK
  set S := Finset.univ.filter (g.JumpAt act₀ Z) with hS
  have hSw : W ^ (1 - δ) / 2 ≤ ∑ G ∈ S, ((U G).card : ℝ) := by
    have : compV Vs B {c₀} = S := by
      ext G
      simp only [compV, Finset.mem_biUnion, hS, Finset.mem_filter, Finset.mem_univ, true_and,
        hZj, hK, Finset.mem_singleton, exists_eq_left]
      constructor
      · rintro ⟨i, hi, h⟩
        split_ifs at h with h'
        · exact ⟨i, ⟨hi, h'.2⟩, (hVs i G).1 h⟩
        · simp at h
      · rintro ⟨i, ⟨hi, h'⟩, h⟩
        exact ⟨i, hi, by rw [if_pos ⟨hc₀B, h'⟩]; exact (hVs i G).2 h⟩
    rw [this] at hheavy
    exact hheavy
  set A' : Set ι := {J | ∃ G, g.blk J = some G ∧ G ∈ S} with hA'
  have hZ' : g.Circ (g.actI A') Z := by
    refine hZc.restrict (fun v hv => ?_) (fun p hp hpa => ?_)
    · rw [hA', actI_iff] at hv; rw [hact₀']
      obtain ⟨G, h, -⟩ := hv; exact ⟨G, h⟩
    · obtain ⟨G, hG⟩ := (hact₀' _).1 hpa
      have hGS : G ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, p, hp, hpa, hG⟩
      obtain ⟨-, hG2⟩ := hZc.jump_of_act hp hpa
      rw [hA', actI_iff, actI_iff]
      exact ⟨⟨G, hG, hGS⟩, ⟨G, hG2.trans hG, hGS⟩⟩
  choose Y hY using hgood
  have hBx : ∀ G ∈ S, ∀ v ∈ Z.flatten, g.vb v = some G → g.iv v ∈ VD G ∪ Y G := by
    intro G _ v hv hvG
    obtain ⟨i, hiK, hvi⟩ := (hZv v).1 hv
    have hva : act₀ v := (hact₀' v).2 ⟨G, hvG⟩
    have hGi : G ∈ Vs i := (hVs i G).2 ((hpcC i).jumpAt_of_vertex hvi hva hvG)
    obtain ⟨hp, hpa, hpG⟩ := hjp' G i hGi
    have hiB := (Finset.mem_filter.1 hiK).1
    have key : g.iv v = e₁ G i ∨ g.iv v = e₂ G i := by
      rcases (hpcC i).bsimple_vertex (hpcS i) hp hpa hpG hvi hva hvG with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr (by rw [h])
    rcases Finset.mem_union.1 hiB with hy | hH
    · refine Finset.mem_union_right _ ((hY G).1 ?_)
      have hi' : i ∈ (EG G).filter (fun c => y c = true) :=
        Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hGi⟩,
          (Finset.mem_filter.1 hy).2⟩
      rcases key with h | h
      · rw [h]; exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hi')
      · rw [h]; exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hi')
    · refine Finset.mem_union_left _ ?_
      have hi' : i ∈ Hs.filter (fun c => G ∈ Vs c) := Finset.mem_filter.2 ⟨hH, hGi⟩
      rcases key with h | h
      · rw [h]; exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hi')
      · rw [h]; exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hi')
  have hUx' : ∀ G ∈ S, ∀ v ∈ Z.flatten, g.actI A' v → g.vb v = some G → g.iv v ∈ U G := by
    intro G _ v _ _ hvG
    obtain ⟨J, hJ1, hJ2⟩ := vb_eq_some.1 hvG
    rw [iv_eq hJ1]; exact hU J G hJ2
  have hGx : ∀ G ∈ S, ∃ v ∈ Z.flatten, g.actI A' v ∧ g.vb v = some G := by
    intro G hGS
    obtain ⟨p, hp, hpa, hpG⟩ := (Finset.mem_filter.1 hGS).2
    refine ⟨g.lt p.1, List.mem_flatten.2 ⟨p.1, mem_of_mem_cpairs_fst hp,
      g.lt_mem (g.ne_nil_of_strand (hZc.strand _ (mem_of_mem_cpairs_fst hp)))⟩, ?_, hpG⟩
    rw [hA', actI_iff]; exact ⟨G, hpG, hGS⟩
  obtain ⟨l, hl, hcount⟩ := g.eliminate_all H U VD Y me (fun G => r * (U G).card) S A' Z
    (by rintro J ⟨G, h1, h2⟩; exact ⟨G, h2, h1⟩) hZ' (fun G _ => hblk G)
    (fun G _ => (hY G).2) hBx hUx' hGx
  refine ⟨l, hl, ?_⟩
  have h0 : (0 : ℝ) ≤ g.sz (g.actI A') Z := Nat.cast_nonneg _
  rw [← Finset.mul_sum] at hcount
  nlinarith

end

end Lovasz
