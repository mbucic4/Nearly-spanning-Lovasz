module
public import RequestProject.Loop
public import RequestProject.LoadedMain

/-!
# Decomposing and merging circuits

A circuit whose jumps visit some block twice splits into two shorter circuits; iterating, every
circuit decomposes into *block-simple* circuits (visiting every block at most once).  Conversely,
two vertex-disjoint circuits with a jump in a common block merge into one circuit.
-/

@[expose] public section


open Classical

namespace Lovasz

section lists

variable {α : Type*}

lemma exists_split_lpairs {l : List α} {p : α × α} (hp : p ∈ lpairs l) :
    ∃ l₁ l₂, l = l₁ ++ p.1 :: p.2 :: l₂ := by
  induction l with
  | nil => simp at hp
  | cons a t ih =>
    cases t with
    | nil => simp at hp
    | cons b t =>
      rw [lpairs_cons_cons, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact ⟨[], t, rfl⟩
      · obtain ⟨l₁, l₂, e⟩ := ih hp
        exact ⟨a :: l₁, l₂, by rw [e]; rfl⟩

lemma exists_cpairs_fst {l : List α} {x : α} (hx : x ∈ l) : ∃ q ∈ cpairs l, q.1 = x := by
  have hne : l ≠ [] := List.ne_nil_of_mem hx
  rw [cpairs_eq_lpairs_append' l hne]
  rcases List.mem_iff_append.1 hx with ⟨s, t, rfl⟩
  cases t with
  | nil =>
    refine ⟨((s ++ [x]).getLast hne, (s ++ [x]).head hne), by simp, by simp⟩
  | cons b t =>
    refine ⟨(x, b), List.mem_append_left _ ?_, rfl⟩
    rw [show s ++ x :: b :: t = s ++ x :: b :: t from rfl]
    rcases eq_or_ne s [] with rfl | hs
    · simp
    · rw [lpairs_append_cons s x _ hs]; simp
where
  cpairs_eq_lpairs_append' (l : List α) (h : l ≠ []) :
      cpairs l = lpairs l ++ [(l.getLast h, l.head h)] := by
    obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil h
    rw [cpairs_cons, lpairs_append_singleton _ _ (by simp)]; rfl

lemma cpairs_eq_lpairs_append_gen (l : List α) (h : l ≠ []) :
    cpairs l = lpairs l ++ [(l.getLast h, l.head h)] :=
  exists_cpairs_fst.cpairs_eq_lpairs_append' l h

lemma exists_rotate_wrap {l : List α} {p : α × α} (hp : p ∈ cpairs l) :
    ∃ k, ∃ h : l.rotate k ≠ [], (l.rotate k).getLast h = p.1 ∧ (l.rotate k).head h = p.2 := by
  have hne : l ≠ [] := by rintro rfl; simp at hp
  rw [cpairs_eq_lpairs_append_gen l hne, List.mem_append, List.mem_singleton] at hp
  rcases hp with hp | rfl
  · obtain ⟨l₁, l₂, e⟩ := exists_split_lpairs hp
    refine ⟨l₁.length + 1, ?_, ?_⟩
    · simp [hne]
    have hr : l.rotate (l₁.length + 1) = p.2 :: l₂ ++ (l₁ ++ [p.1]) := by
      rw [e, show l₁ ++ p.1 :: p.2 :: l₂ = (l₁ ++ [p.1]) ++ (p.2 :: l₂) by simp,
        List.rotate_append_length_eq' ]; simp
    simp [hr]
  · exact ⟨0, by simpa using hne, by simp, by simp⟩
where
  List.rotate_append_length_eq' {l₁ l₂ : List α} {k : ℕ} (hk : k = l₁.length) :
      (l₁ ++ l₂).rotate k = l₂ ++ l₁ := by
    subst hk; exact List.rotate_append_length_eq l₁ l₂

lemma exists_rotate_split {l : List α} {p q : α × α} (hp : p ∈ cpairs l) (hq : q ∈ cpairs l)
    (hpq : p ≠ q) : ∃ k X Y, ∃ (hX : X ≠ []) (hY : Y ≠ []), l.rotate k = X ++ Y ∧
      X.getLast hX = q.1 ∧ Y.head hY = q.2 ∧ Y.getLast hY = p.1 ∧ X.head hX = p.2 := by
  obtain ⟨k, hne, h1, h2⟩ := exists_rotate_wrap hp
  have hq' : q ∈ cpairs (l.rotate k) := mem_cpairs_rotate.2 hq
  rw [cpairs_eq_lpairs_append_gen _ hne, List.mem_append, List.mem_singleton] at hq'
  rcases hq' with hq' | hq'
  · obtain ⟨l₁, l₂, e⟩ := exists_split_lpairs hq'
    refine ⟨k, l₁ ++ [q.1], q.2 :: l₂, by simp, by simp, by rw [e]; simp, by simp, rfl, ?_, ?_⟩
    · rw [← h1]; simp only [e]; simp
    · rw [← h2]; simp only [e]
      cases l₁ <;> simp
  · exact absurd (by rw [hq', h1, h2]) hpq

end lists

namespace Geo

variable {V ι β : Type*} (g : Geo V ι β)

/-- The circuit `cs` has a jump in the block `G`. -/
def JumpAt (act : V → Prop) (cs : List (List V)) (G : β) : Prop :=
  ∃ p ∈ cpairs cs, act (g.lt p.1) ∧ g.vb (g.lt p.1) = some G

/-- A circuit is *block-simple* if no two of its junctions are jumps in the same block. -/
def BSimple (act : V → Prop) (cs : List (List V)) : Prop :=
  ∀ G, ∀ p ∈ cpairs cs, ∀ q ∈ cpairs cs, act (g.lt p.1) → g.vb (g.lt p.1) = some G →
    act (g.lt q.1) → g.vb (g.lt q.1) = some G → p = q

variable {g}

/-- A jump junction: both ends are active and in the same block. -/
lemma Circ.jump_of_act {act : V → Prop} {cs : List (List V)} (h : g.Circ act cs)
    {p : List V × List V} (hp : p ∈ cpairs cs) (ha : act (g.lt p.1)) :
    act (g.hd p.2) ∧ g.vb (g.hd p.2) = g.vb (g.lt p.1) := by
  rcases h.join p hp with ⟨-, h2, G, h3, h4⟩ | ⟨h1, -, -⟩
  · exact ⟨h2, h4.trans h3.symm⟩
  · exact absurd ha h1

lemma Circ.act_hd {act : V → Prop} {cs : List (List V)} (h : g.Circ act cs)
    {p : List V × List V} (hp : p ∈ cpairs cs) (ha : act (g.hd p.2)) :
    act (g.lt p.1) := by
  rcases h.join p hp with ⟨h1, -⟩ | ⟨-, h2, -⟩
  · exact h1
  · exact absurd ha h2

/-- Cutting a rotated circuit `X ++ Y` at two jumps in the same block. -/
lemma Circ.cut {act : V → Prop} {cs X Y : List (List V)} (h : g.Circ act cs) {k : ℕ}
    (hXY : cs.rotate k = X ++ Y) (hX : X ≠ []) {G : β}
    (hl : act (g.lt (X.getLast hX))) (hlG : g.vb (g.lt (X.getLast hX)) = some G)
    (hh : act (g.hd (X.head hX))) (hhG : g.vb (g.hd (X.head hX)) = some G) :
    g.Circ act X := by
  have hc := Circ.rotate g h k
  rw [hXY] at hc
  refine ⟨hX, fun σ hσ => hc.strand σ (List.mem_append_left _ hσ),
    (List.sublist_append_left _ _).flatten.nodup (by simpa using hc.nodup), ?_⟩
  intro p hp
  rw [cpairs_eq_lpairs_append_gen X hX, List.mem_append, List.mem_singleton] at hp
  rcases hp with hp | rfl
  · refine hc.join p ?_
    rcases eq_or_ne Y [] with rfl | hY
    · simpa using lpairs_sub_cpairs hp
    · rw [cpairs_eq_lpairs_append_gen _ (by simp [hX]), lpairs_append X Y hX hY]
      exact List.mem_append_left _ (List.mem_append_left _ hp)
  · exact Or.inl ⟨hl, hh, G, hlG, hhG⟩

lemma jumpAt_iff {act : V → Prop} {cs : List (List V)} {G : β} :
    g.JumpAt act cs G ↔ ∃ σ ∈ cs, act (g.lt σ) ∧ g.vb (g.lt σ) = some G := by
  constructor
  · rintro ⟨p, hp, h1, h2⟩; exact ⟨p.1, mem_of_mem_cpairs_fst hp, h1, h2⟩
  · rintro ⟨σ, hσ, h1, h2⟩
    obtain ⟨q, hq, rfl⟩ := exists_cpairs_fst hσ
    exact ⟨q, hq, h1, h2⟩

lemma Circ.split {act : V → Prop} {cs : List (List V)} (h : g.Circ act cs)
    (hns : ¬ g.BSimple act cs) :
    ∃ X Y G, g.Circ act X ∧ g.Circ act Y ∧ X.length < cs.length ∧ Y.length < cs.length ∧
      (X ++ Y).flatten.Perm cs.flatten ∧ g.JumpAt act X G ∧ g.JumpAt act Y G ∧
      (∀ G', g.JumpAt act X G' ∨ g.JumpAt act Y G' ↔ g.JumpAt act cs G') := by
  simp only [BSimple, not_forall] at hns
  obtain ⟨G, p, hp, q, hq, hpa, hpG, hqa, hqG, hpq⟩ := hns
  obtain ⟨k, X, Y, hX, hY, e, h1, h2, h3, h4⟩ := exists_rotate_split hp hq hpq
  obtain ⟨hpa2, hpG2⟩ := h.jump_of_act hp hpa
  obtain ⟨hqa2, hqG2⟩ := h.jump_of_act hq hqa
  have hlen : X.length + Y.length = cs.length := by
    rw [← List.length_append, ← e, List.length_rotate]
  have hXl := List.length_pos_of_ne_nil hX
  have hYl := List.length_pos_of_ne_nil hY
  have e' : cs.rotate (k + X.length) = Y ++ X := by
    rw [← List.rotate_rotate, e, List.rotate_append_length_eq]
  have hcX : g.Circ act X := h.cut e hX (by rw [h1]; exact hqa) (by rw [h1]; exact hqG)
    (by rw [h4]; exact hpa2) (by rw [h4, hpG2]; exact hpG)
  have hcY : g.Circ act Y := h.cut e' hY (by rw [h3]; exact hpa) (by rw [h3]; exact hpG)
    (by rw [h2]; exact hqa2) (by rw [h2, hqG2]; exact hqG)
  refine ⟨X, Y, G, hcX, hcY, by omega, by omega, ?_, ?_, ?_, ?_⟩
  · rw [← e]; exact (List.rotate_perm cs k).flatten
  · exact jumpAt_iff.2 ⟨_, List.getLast_mem hX, by rw [h1]; exact hqa, by rw [h1]; exact hqG⟩
  · exact jumpAt_iff.2 ⟨_, List.getLast_mem hY, by rw [h3]; exact hpa, by rw [h3]; exact hpG⟩
  · intro G'
    simp only [jumpAt_iff]
    constructor
    · rintro (⟨σ, hσ, h⟩ | ⟨σ, hσ, h⟩)
      · exact ⟨σ, (List.mem_rotate (n := k)).1 (by rw [e]; exact List.mem_append_left _ hσ), h⟩
      · exact ⟨σ, (List.mem_rotate (n := k)).1 (by rw [e]; exact List.mem_append_right _ hσ), h⟩
    · rintro ⟨σ, hσ, h⟩
      have : σ ∈ X ++ Y := by rw [← e]; exact List.mem_rotate.2 hσ
      rcases List.mem_append.1 this with hσ | hσ
      · exact Or.inl ⟨σ, hσ, h⟩
      · exact Or.inr ⟨σ, hσ, h⟩

/-- **Decomposition** of a circuit into block-simple circuits. -/
theorem Circ.decomp {act : V → Prop} : ∀ (n : ℕ) (cs : List (List V)), cs.length ≤ n →
    g.Circ act cs → (∃ G, g.JumpAt act cs G) →
    ∃ P : List (List (List V)),
      (∀ c ∈ P, g.Circ act c ∧ g.BSimple act c ∧ ∃ G, g.JumpAt act c G) ∧
      (P.map List.flatten).flatten.Perm cs.flatten ∧
      (∀ G, (∃ c ∈ P, g.JumpAt act c G) ↔ g.JumpAt act cs G) ∧
      (∀ c ∈ P, ∀ c' ∈ P, Relation.ReflTransGen
        (fun a b => a ∈ P ∧ b ∈ P ∧ ∃ G, g.JumpAt act a G ∧ g.JumpAt act b G) c c') := by
  intro n
  induction n with
  | zero =>
    intro cs hl h _
    exact absurd (List.length_eq_zero_iff.1 (by omega)) h.ne
  | succ n ih =>
    intro cs hl h hj
    by_cases hs : g.BSimple act cs
    · refine ⟨[cs], by simpa using ⟨h, hs, hj⟩, by simp, by simp, ?_⟩
      intro c hc c' hc'
      simp only [List.mem_singleton] at hc hc'
      subst hc hc'
      exact Relation.ReflTransGen.refl
    obtain ⟨X, Y, G, hX, hY, hXl, hYl, hperm, hGX, hGY, hJ⟩ := h.split hs
    obtain ⟨PX, hPX1, hPX2, hPX3, hPX4⟩ := ih X (by omega) hX ⟨G, hGX⟩
    obtain ⟨PY, hPY1, hPY2, hPY3, hPY4⟩ := ih Y (by omega) hY ⟨G, hGY⟩
    refine ⟨PX ++ PY, ?_, ?_, ?_, ?_⟩
    · intro c hc
      rcases List.mem_append.1 hc with hc | hc
      · exact hPX1 c hc
      · exact hPY1 c hc
    · simp only [List.map_append, List.flatten_append]
      exact (hPX2.append hPY2).trans (by simpa using hperm)
    · intro G'
      rw [← hJ, ← hPX3, ← hPY3]
      simp only [List.mem_append]
      constructor
      · rintro ⟨c, hc | hc, h⟩
        · exact Or.inl ⟨c, hc, h⟩
        · exact Or.inr ⟨c, hc, h⟩
      · rintro (⟨c, hc, h⟩ | ⟨c, hc, h⟩)
        · exact ⟨c, Or.inl hc, h⟩
        · exact ⟨c, Or.inr hc, h⟩
    · obtain ⟨cX, hcX, hcXG⟩ := (hPX3 G).2 hGX
      obtain ⟨cY, hcY, hcYG⟩ := (hPY3 G).2 hGY
      have mX : ∀ c ∈ PX, ∀ c' ∈ PX, Relation.ReflTransGen (fun a b => a ∈ PX ++ PY ∧
          b ∈ PX ++ PY ∧ ∃ G, g.JumpAt act a G ∧ g.JumpAt act b G) c c' := by
        intro c hc c' hc'
        induction hPX4 c hc c' hc' with
        | refl => exact Relation.ReflTransGen.refl
        | tail _ hbc ih =>
          exact (ih hbc.1).tail ⟨List.mem_append_left _ hbc.1,
            List.mem_append_left _ hbc.2.1, hbc.2.2⟩
      have mY : ∀ c ∈ PY, ∀ c' ∈ PY, Relation.ReflTransGen (fun a b => a ∈ PX ++ PY ∧
          b ∈ PX ++ PY ∧ ∃ G, g.JumpAt act a G ∧ g.JumpAt act b G) c c' := by
        intro c hc c' hc'
        induction hPY4 c hc c' hc' with
        | refl => exact Relation.ReflTransGen.refl
        | tail _ hbc ih =>
          exact (ih hbc.1).tail ⟨List.mem_append_right _ hbc.1,
            List.mem_append_right _ hbc.2.1, hbc.2.2⟩
      intro c hc c' hc'
      rcases List.mem_append.1 hc with hc | hc <;> rcases List.mem_append.1 hc' with hc' | hc'
      · exact mX c hc c' hc'
      · exact ((mX c hc cX hcX).tail ⟨List.mem_append_left _ hcX, List.mem_append_right _ hcY,
          G, hcXG, hcYG⟩).trans (mY cY hcY c' hc')
      · exact ((mY c hc cY hcY).tail ⟨List.mem_append_right _ hcY, List.mem_append_left _ hcX,
          G, hcYG, hcXG⟩).trans (mX cX hcX c' hc')
      · exact mY c hc c' hc'

/-- **Merging** two vertex-disjoint circuits with jumps in a common block. -/
lemma Circ.merge2 {act : V → Prop} {X Y : List (List V)} (hX : g.Circ act X) (hY : g.Circ act Y)
    (hd : (X ++ Y).flatten.Nodup) {G : β} (hGX : g.JumpAt act X G) (hGY : g.JumpAt act Y G) :
    ∃ Z, g.Circ act Z ∧ Z.flatten.Perm (X ++ Y).flatten ∧
      ∀ G', g.JumpAt act Z G' ↔ g.JumpAt act X G' ∨ g.JumpAt act Y G' := by
  obtain ⟨p, hp, hpa, hpG⟩ := hGX
  obtain ⟨q, hq, hqa, hqG⟩ := hGY
  obtain ⟨hpa2, hpG2⟩ := hX.jump_of_act hp hpa
  obtain ⟨hqa2, hqG2⟩ := hY.jump_of_act hq hqa
  obtain ⟨k, hk, hk1, hk2⟩ := exists_rotate_wrap hp
  obtain ⟨m, hm, hm1, hm2⟩ := exists_rotate_wrap hq
  set X' := X.rotate k
  set Y' := Y.rotate m
  have hX' := Circ.rotate g hX k
  have hY' := Circ.rotate g hY m
  have hpermF : (X' ++ Y').flatten.Perm (X ++ Y).flatten := by
    simp only [List.flatten_append]
    exact (List.rotate_perm X k).flatten.append (List.rotate_perm Y m).flatten
  refine ⟨X' ++ Y', ⟨by simp [hk], ?_, hpermF.nodup_iff.2 hd, ?_⟩, hpermF, ?_⟩
  · intro σ hσ
    rcases List.mem_append.1 hσ with hσ | hσ
    · exact hX'.strand σ hσ
    · exact hY'.strand σ hσ
  · intro r hr
    have hr' := (cpairs_append X' Y' hk hm).mem_iff.1 hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr'
    rcases hr' with (hr' | hr') | hr' | hr'
    · exact hX'.join r (lpairs_sub_cpairs hr')
    · exact hY'.join r (lpairs_sub_cpairs hr')
    · subst hr'
      rw [hk1, hm2]
      exact Or.inl ⟨hpa, hqa2, G, hpG, by rw [hqG2, hqG]⟩
    · subst hr'
      rw [hm1, hk2]
      exact Or.inl ⟨hqa, hpa2, G, hqG, by rw [hpG2, hpG]⟩
  · intro G'
    simp only [jumpAt_iff, List.mem_append]
    constructor
    · rintro ⟨σ, hσ | hσ, h⟩
      · exact Or.inl ⟨σ, List.mem_rotate.1 hσ, h⟩
      · exact Or.inr ⟨σ, List.mem_rotate.1 hσ, h⟩
    · rintro (⟨σ, hσ, h⟩ | ⟨σ, hσ, h⟩)
      · exact ⟨σ, Or.inl (List.mem_rotate.2 hσ), h⟩
      · exact ⟨σ, Or.inr (List.mem_rotate.2 hσ), h⟩


lemma mem_strand_cases {act : V → Prop} {σ : List V} (h : g.StrandOK act σ) {v : V}
    (hv : v ∈ σ) : v = g.hd σ ∨ v = g.lt σ ∨ v ∈ sInner σ := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil (g.ne_nil_of_strand h)
  have ht : t ≠ [] := by rintro rfl; have := h.two_le; simp at this
  rw [g.lt_eq_getLast (by simp), List.getLast_cons ht, sInner, List.tail_cons]
  rcases List.mem_cons.1 hv with rfl | hv
  · exact Or.inl rfl
  · rw [← List.dropLast_append_getLast ht, List.mem_append, List.mem_singleton] at hv
    rcases hv with hv | hv
    · exact Or.inr (Or.inr hv)
    · exact Or.inr (Or.inl hv)

/-- In a block-simple circuit, the active vertices in a block `G` are the two ends of its unique
jump in `G`. -/
lemma Circ.bsimple_vertex {act : V → Prop} {cs : List (List V)} (h : g.Circ act cs)
    (hs : g.BSimple act cs) {G : β} {p : List V × List V} (hp : p ∈ cpairs cs)
    (hpa : act (g.lt p.1)) (hpG : g.vb (g.lt p.1) = some G) {v : V} (hv : v ∈ cs.flatten)
    (hva : act v) (hvG : g.vb v = some G) : v = g.lt p.1 ∨ v = g.hd p.2 := by
  obtain ⟨σ, hσ, hvσ⟩ := List.mem_flatten.1 hv
  have hst := h.strand σ hσ
  rcases g.mem_strand_cases hst hvσ with rfl | rfl | hin
  · obtain ⟨q, hq, rfl⟩ := exists_cpairs_snd hσ
    have hqa := h.act_hd hq hva
    obtain ⟨-, hqG⟩ := h.jump_of_act hq hqa
    have := hs G p hp q hq hpa hpG hqa (by rw [← hqG, hvG])
    subst this
    exact Or.inr rfl
  · obtain ⟨q, hq, rfl⟩ := exists_cpairs_fst hσ
    have := hs G p hp q hq hpa hpG hva hvG
    subst this
    exact Or.inl rfl
  · exact absurd hva (hst.inner_na v hin)

/-- Weakening the activity predicate of a circuit. -/
lemma Circ.restrict {act act' : V → Prop} {cs : List (List V)} (h : g.Circ act cs)
    (himp : ∀ v, act' v → act v)
    (hj : ∀ p ∈ cpairs cs, act (g.lt p.1) → act' (g.lt p.1) ∧ act' (g.hd p.2)) :
    g.Circ act' cs := by
  refine ⟨h.ne, fun σ hσ => ?_, h.nodup, fun p hp => ?_⟩
  · have hs := h.strand σ hσ
    exact ⟨hs.two_le, hs.chain, fun v hv h' => hs.inner_na v hv (himp v h'),
      fun h' => hs.hd_bd (himp _ h'), fun h' => hs.lt_bd (himp _ h')⟩
  · rcases h.join p hp with ⟨h1, h2, G, h3, h4⟩ | ⟨h1, h2, h3⟩
    · obtain ⟨h1', h2'⟩ := hj p hp h1
      exact Or.inl ⟨h1', h2', G, h3, h4⟩
    · exact Or.inr ⟨fun h' => h1 (himp _ h'), fun h' => h2 (himp _ h'), h3⟩

section merge

variable {κ : Type*}

/-- `Z` is a circuit merging the pieces `c i`, `i ∈ T`. -/
def Merges (act : V → Prop) (c : κ → List (List V)) (T : Finset κ) (Z : List (List V)) : Prop :=
  g.Circ act Z ∧ (∀ v, v ∈ Z.flatten ↔ ∃ i ∈ T, v ∈ (c i).flatten) ∧
    (∀ G, g.JumpAt act Z G ↔ ∃ i ∈ T, g.JumpAt act (c i) G)

lemma merges_single {act : V → Prop} {c : κ → List (List V)} {i : κ} (h : g.Circ act (c i)) :
    g.Merges act c {i} (c i) := ⟨h, by simp, by simp⟩

lemma Merges.add {act : V → Prop} {c : κ → List (List V)} {T : Finset κ} {Z : List (List V)}
    (hM : g.Merges act c T Z) {j : κ} (hc : g.Circ act (c j))
    (hdisj : ∀ i ∈ T, ∀ v ∈ (c i).flatten, v ∉ (c j).flatten)
    {G : β} (hG : ∃ i ∈ T, g.JumpAt act (c i) G) (hGj : g.JumpAt act (c j) G) :
    ∃ Z', g.Merges act c (insert j T) Z' := by
  obtain ⟨hZ, hv, hJ⟩ := hM
  have hd : (Z ++ c j).flatten.Nodup := by
    rw [List.flatten_append, List.nodup_append]
    refine ⟨hZ.nodup, hc.nodup, fun a ha b hb hab => ?_⟩
    subst hab
    obtain ⟨i, hi, hai⟩ := (hv a).1 ha
    exact hdisj i hi a hai hb
  obtain ⟨Z', hZ', hperm, hJ'⟩ := hZ.merge2 hc hd ((hJ G).2 hG) hGj
  refine ⟨Z', hZ', fun v => ?_, fun G' => ?_⟩
  · rw [hperm.mem_iff, List.flatten_append, List.mem_append, hv]
    simp only [Finset.mem_insert, exists_eq_or_imp]
    exact or_comm
  · rw [hJ', hJ]
    simp only [Finset.mem_insert, exists_eq_or_imp]
    exact or_comm

/-- Merging all pieces of a connected component of a family of block-simple pieces. -/
theorem merge_component {act : V → Prop} (c : κ → List (List V)) (Vs : κ → Finset β)
    (hVs : ∀ i G, G ∈ Vs i ↔ g.JumpAt act (c i) G) (hc : ∀ i, g.Circ act (c i))
    (hdisj : ∀ i j, i ≠ j → ∀ v ∈ (c i).flatten, v ∉ (c j).flatten)
    (B : Finset κ) {i₀ : κ} (hi₀ : i₀ ∈ B) :
    ∃ Z, g.Merges act c (B.filter (fun j => ReachC Vs B i₀ j)) Z := by
  set K := B.filter (fun j => ReachC Vs B i₀ j) with hK
  have hi₀K : i₀ ∈ K := Finset.mem_filter.2 ⟨hi₀, Relation.ReflTransGen.refl⟩
  have step : ∀ j, ReachC Vs B i₀ j → ∀ T Z, i₀ ∈ T → T ⊆ K → g.Merges act c T Z →
      ∃ T' Z', T ⊆ T' ∧ j ∈ T' ∧ T' ⊆ K ∧ g.Merges act c T' Z' := by
    intro j hj
    induction hj with
    | refl => exact fun T Z h0 hT hM => ⟨T, Z, subset_rfl, h0, hT, hM⟩
    | @tail a b hab hb ih =>
      intro T Z h0 hT hM
      obtain ⟨T', Z', h1, h2, h3, h4⟩ := ih T Z h0 hT hM
      by_cases hbT : b ∈ T'
      · exact ⟨T', Z', h1, hbT, h3, h4⟩
      obtain ⟨-, hbB, G, hG⟩ := id hb
      rw [Finset.mem_inter] at hG
      obtain ⟨Z'', hZ''⟩ := h4.add (hc b)
        (fun i hi v hv hv' => hdisj i b (fun e => hbT (e ▸ hi)) v hv hv')
        ⟨a, h2, (hVs a G).1 hG.1⟩ ((hVs b G).1 hG.2)
      refine ⟨insert b T', Z'', h1.trans (Finset.subset_insert _ _), Finset.mem_insert_self _ _,
        Finset.insert_subset (Finset.mem_filter.2 ⟨hbB, hab.tail hb⟩) h3, hZ''⟩
  have key : ∀ S : Finset κ, S ⊆ K → ∃ T Z, S ⊆ T ∧ i₀ ∈ T ∧ T ⊆ K ∧ g.Merges act c T Z := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact fun _ => ⟨{i₀}, c i₀, by simp, by simp, by simpa using hi₀K,
        g.merges_single (hc i₀)⟩
    | insert j S hjS ih =>
      intro hS
      obtain ⟨T, Z, h1, h2, h3, h4⟩ := ih ((Finset.subset_insert _ _).trans hS)
      obtain ⟨T', Z', h1', h2', h3', h4'⟩ := step j (Finset.mem_filter.1 (hS (by simp))).2
        T Z h2 h3 h4
      exact ⟨T', Z', Finset.insert_subset h2' (h1.trans h1'), h1' h2, h3', h4'⟩
  obtain ⟨T, Z, h1, -, h3, h4⟩ := key K subset_rfl
  rw [show T = K from le_antisymm h3 h1] at h4
  exact ⟨Z, h4⟩

end merge

end Geo

end Lovasz
