module
public import RequestProject.TwoRails
public import RequestProject.Linking

/-!
# Circuits of strands (machinery for the proof of Theorem 1.2)

We work in an abstract *geometry*: a host graph `Γ` (the graph `L ∪ M`), a matching relation
`Mp` (the edges of `M`), a partial map `ivOf` sending vertices to *intervals*, a partial map
`blk` sending intervals to *blocks* (the expanders of the decomposition), two distinguished
boundary vertices `lo J ≠ hi J` of every interval and *segments* `seg u v` (the subpath of `L`
between two vertices of the same interval).

A *circuit* is a cyclic list of *strands* (paths of `Γ`) whose consecutive pairs are either
*jumps* (both ends active and in the same block) or genuine edges of `Γ` (both ends inactive).
Here "active" is given by a predicate `act`.
-/

@[expose] public section


open Classical

namespace Lovasz

/-! ### Consecutive pairs of lists -/

section pairs

variable {α : Type*}

/-- Consecutive pairs of a list. -/
def lpairs (l : List α) : List (α × α) := l.zip l.tail

/-- Consecutive pairs of a cyclic list. -/
def cpairs (l : List α) : List (α × α) := lpairs (l ++ l.take 1)

@[simp] lemma lpairs_nil : lpairs ([] : List α) = [] := rfl
@[simp] lemma lpairs_singleton (a : α) : lpairs [a] = [] := rfl
@[simp] lemma lpairs_cons_cons (a b : α) (l : List α) :
    lpairs (a :: b :: l) = (a, b) :: lpairs (b :: l) := rfl

lemma lpairs_append_cons (l₁ : List α) (b : α) (l₂ : List α) (hl : l₁ ≠ []) :
    lpairs (l₁ ++ b :: l₂) = lpairs l₁ ++ (l₁.getLast hl, b) :: lpairs (b :: l₂) := by
  induction l₁ with
  | nil => exact absurd rfl hl
  | cons a t ih =>
    cases t with
    | nil => simp
    | cons c t =>
      simp only [List.cons_append, lpairs_cons_cons, List.getLast_cons_cons]
      rw [← List.cons_append, ih (by simp)]

lemma lpairs_append_singleton (l : List α) (b : α) (hl : l ≠ []) :
    lpairs (l ++ [b]) = lpairs l ++ [(l.getLast hl, b)] := by
  rw [lpairs_append_cons l b [] hl]; rfl

@[simp] lemma cpairs_nil : cpairs ([] : List α) = [] := rfl

lemma cpairs_cons (a : α) (t : List α) : cpairs (a :: t) = lpairs (a :: t ++ [a]) := rfl

lemma length_lpairs (l : List α) : (lpairs l).length = l.length - 1 := by
  simp [lpairs]

lemma length_cpairs (l : List α) : (cpairs l).length = l.length := by
  cases l with
  | nil => rfl
  | cons a t => rw [cpairs_cons, length_lpairs]; simp

lemma cpairs_append (X Y : List α) (hX : X ≠ []) (hY : Y ≠ []) :
    (cpairs (X ++ Y)).Perm (lpairs X ++ lpairs Y ++
      [(X.getLast hX, Y.head hY), (Y.getLast hY, X.head hX)]) := by
  obtain ⟨a, X', rfl⟩ := List.exists_cons_of_ne_nil hX
  obtain ⟨b, Y', rfl⟩ := List.exists_cons_of_ne_nil hY
  have e : a :: X' ++ b :: Y' ++ (a :: X' ++ b :: Y').take 1 = (a :: X') ++ b :: (Y' ++ [a]) := by
    simp
  rw [cpairs, e, lpairs_append_cons _ _ _ hX, ← List.cons_append,
    lpairs_append_singleton _ _ (by simp)]
  simp only [List.head_cons, List.append_assoc]
  refine List.Perm.append_left _ ?_
  exact List.perm_middle.symm.trans (by simp)

lemma cpairs_append_comm (A B : List α) : (cpairs (A ++ B)).Perm (cpairs (B ++ A)) := by
  rcases eq_or_ne A [] with rfl | hA
  · simp
  rcases eq_or_ne B [] with rfl | hB
  · simp
  refine (cpairs_append A B hA hB).trans (List.Perm.trans ?_ (cpairs_append B A hB hA).symm)
  exact (List.perm_append_comm.append_right _).trans (List.Perm.append_left _ (List.Perm.swap _ _ _))

lemma cpairs_rotate (l : List α) (k : ℕ) : (cpairs (l.rotate k)).Perm (cpairs l) := by
  rw [← List.rotate_mod]
  rcases Nat.eq_zero_or_pos l.length with h | h
  · rw [List.length_eq_zero_iff.1 h]; simp
  rw [List.rotate_eq_drop_append_take (Nat.mod_lt _ h).le]
  conv_rhs => rw [← List.take_append_drop (k % l.length) l]
  exact cpairs_append_comm _ _

lemma mem_cpairs_rotate {l : List α} {k : ℕ} {p : α × α} :
    p ∈ cpairs (l.rotate k) ↔ p ∈ cpairs l := (cpairs_rotate l k).mem_iff

end pairs

/-! ### Geometries -/

/-- The abstract geometry in which circuits live. -/
structure Geo (V ι β : Type*) where
  /-- the host graph `L ∪ M` -/
  Γ : SimpleGraph V
  /-- the matching `M` -/
  Mp : V → V → Prop
  /-- the interval containing a vertex -/
  ivOf : V → Option ι
  /-- the block containing an interval -/
  blk : ι → Option β
  /-- first boundary vertex of an interval -/
  lo : ι → V
  /-- second boundary vertex of an interval -/
  hi : ι → V
  /-- the segment between two vertices of an interval -/
  seg : V → V → List V
  /-- a default vertex -/
  dflt : V
  /-- a default interval -/
  dI : ι
  Mp_symm : ∀ {u v}, Mp u v → Mp v u
  Mp_adj : ∀ {u v}, Mp u v → Γ.Adj u v
  Mp_uniq : ∀ {u v w}, Mp u v → Mp u w → v = w
  lo_ne_hi : ∀ J, lo J ≠ hi J
  iv_lo : ∀ J, ivOf (lo J) = some J
  iv_hi : ∀ J, ivOf (hi J) = some J
  seg_head : ∀ {J u v}, ivOf u = some J → ivOf v = some J → (seg u v).head? = some u
  seg_last : ∀ {J u v}, ivOf u = some J → ivOf v = some J → (seg u v).getLast? = some v
  seg_chain : ∀ {J u v}, ivOf u = some J → ivOf v = some J → (seg u v).IsChain Γ.Adj
  seg_nodup : ∀ {J u v}, ivOf u = some J → ivOf v = some J → (seg u v).Nodup
  seg_iv : ∀ {J u v}, ivOf u = some J → ivOf v = some J → ∀ x ∈ seg u v, ivOf x = some J
  seg_orient : ∀ {J w₁ w₂}, ivOf w₁ = some J → ivOf w₂ = some J → w₁ ≠ w₂ →
    (seg (lo J) w₁).Disjoint (seg w₂ (hi J)) ∨ (seg (hi J) w₁).Disjoint (seg w₂ (lo J))

/-- Inner vertices of a strand. -/
def sInner {V : Type*} (σ : List V) : List V := σ.tail.dropLast

namespace Geo

variable {V ι β : Type*} (g : Geo V ι β)

/-- The block of a vertex. -/
def vb (v : V) : Option β := (g.ivOf v).bind g.blk

/-- Vertices of intervals of blocks in `S`. -/
def actS (S : Finset β) (v : V) : Prop := ∃ G ∈ S, g.vb v = some G

/-- `v` is a boundary vertex of its interval. -/
def IsBd (v : V) : Prop := ∃ J, g.ivOf v = some J ∧ (v = g.lo J ∨ v = g.hi J)

/-- First vertex of a strand. -/
def hd (σ : List V) : V := σ.headD g.dflt

/-- Last vertex of a strand. -/
def lt (σ : List V) : V := σ.getLastD g.dflt


/-- A strand: a path of `Γ` with at least two vertices whose inner vertices are inactive and
whose active ends are boundary vertices. -/
structure StrandOK (act : V → Prop) (σ : List V) : Prop where
  two_le : 2 ≤ σ.length
  chain : σ.IsChain g.Γ.Adj
  inner_na : ∀ v ∈ sInner σ, ¬ act v
  hd_bd : act (g.hd σ) → g.IsBd (g.hd σ)
  lt_bd : act (g.lt σ) → g.IsBd (g.lt σ)

/-- An admissible junction between the end `u` of a strand and the start `v` of the next:
either a jump (both active, in the same block) or an edge of `Γ` (both inactive). -/
def JoinOK (act : V → Prop) (u v : V) : Prop :=
  (act u ∧ act v ∧ ∃ G, g.vb u = some G ∧ g.vb v = some G) ∨ (¬ act u ∧ ¬ act v ∧ g.Γ.Adj u v)

/-- A circuit of strands. -/
structure Circ (act : V → Prop) (cs : List (List V)) : Prop where
  ne : cs ≠ []
  strand : ∀ σ ∈ cs, g.StrandOK act σ
  nodup : cs.flatten.Nodup
  join : ∀ p ∈ cpairs cs, g.JoinOK act (g.lt p.1) (g.hd p.2)

/-- The contribution of a junction to the size: `1` if it is a genuine edge of `M`. -/
noncomputable def joinVal (act : V → Prop) (u v : V) : ℕ := if ¬ act u ∧ g.Mp u v then 1 else 0

/-- The size of a circuit: the number of edges of `M` it uses. -/
noncomputable def sz (act : V → Prop) (cs : List (List V)) : ℕ :=
  (cs.map (countPairs g.Mp)).sum + ((cpairs cs).map (fun p => g.joinVal act (g.lt p.1) (g.hd p.2))).sum

end Geo


/-! ### Counting pairs via `lpairs` -/

section count

variable {α : Type*}

lemma countPairs_eq_lpairs (r : α → α → Prop) (l : List α) :
    countPairs r l = ((lpairs l).map (fun p => if r p.1 p.2 then 1 else 0)).sum := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases t with
    | nil => rfl
    | cons b t => rw [countPairs, ih]; simp

lemma lpairs_append (l₁ l₂ : List α) (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) :
    lpairs (l₁ ++ l₂) = lpairs l₁ ++ (l₁.getLast h₁, l₂.head h₂) :: lpairs l₂ := by
  obtain ⟨b, t, rfl⟩ := List.exists_cons_of_ne_nil h₂
  exact lpairs_append_cons l₁ b t h₁

lemma countPairs_append (r : α → α → Prop) (l₁ l₂ : List α) (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) :
    countPairs r (l₁ ++ l₂) = countPairs r l₁ + (if r (l₁.getLast h₁) (l₂.head h₂) then 1 else 0) +
      countPairs r l₂ := by
  simp only [countPairs_eq_lpairs, lpairs_append l₁ l₂ h₁ h₂, List.map_append, List.map_cons,
    List.sum_append, List.sum_cons]
  ring

lemma countPairs_mono_append_left (r : α → α → Prop) (l₁ l₂ : List α) :
    countPairs r l₁ ≤ countPairs r (l₁ ++ l₂) := by
  rcases eq_or_ne l₁ [] with rfl | h₁
  · simp [countPairs_eq_lpairs]
  rcases eq_or_ne l₂ [] with rfl | h₂
  · simp
  rw [countPairs_append r l₁ l₂ h₁ h₂]; omega

lemma countPairs_mono_append_right (r : α → α → Prop) (l₁ l₂ : List α) :
    countPairs r l₂ ≤ countPairs r (l₁ ++ l₂) := by
  rcases eq_or_ne l₁ [] with rfl | h₁
  · simp
  rcases eq_or_ne l₂ [] with rfl | h₂
  · simp [countPairs_eq_lpairs]
  rw [countPairs_append r l₁ l₂ h₁ h₂]; omega

lemma countPairs_reverse (r : α → α → Prop) (hr : ∀ a b, r a b → r b a) (l : List α) :
    countPairs r l.reverse = countPairs r l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases t with
    | nil => rfl
    | cons b t =>
      rw [List.reverse_cons, countPairs_append r _ _ (by simp) (by simp), ih, countPairs]
      have hl : (b :: t).reverse.getLast (by simp) = b := by simp
      simp only [hl, List.head_cons]
      have : countPairs r [a] = 0 := rfl
      rw [this]
      have hiff : r b a ↔ r a b := ⟨hr b a, hr a b⟩
      simp only [hiff]; ring

lemma mem_of_mem_cpairs_fst {l : List α} {p : α × α} (hp : p ∈ cpairs l) : p.1 ∈ l := by
  cases l with
  | nil => simp at hp
  | cons a t =>
    rw [cpairs_cons] at hp
    have := (List.of_mem_zip hp).1
    simp only [List.cons_append, List.mem_cons, List.mem_append] at this ⊢
    tauto

lemma mem_of_mem_cpairs_snd {l : List α} {p : α × α} (hp : p ∈ cpairs l) : p.2 ∈ l := by
  cases l with
  | nil => simp at hp
  | cons a t =>
    rw [cpairs_cons] at hp
    have := List.tail_subset _ (List.of_mem_zip hp).2
    simp only [List.cons_append, List.mem_cons, List.mem_append] at this ⊢
    tauto

end count

namespace Geo

variable {V ι β : Type*} (g : Geo V ι β)

/-- The endpoints of the strands of a circuit. -/
def ends (cs : List (List V)) : List V := cs.flatMap (fun σ => [g.hd σ, g.lt σ])

lemma hd_eq_head {σ : List V} (h : σ ≠ []) : g.hd σ = σ.head h := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil h; rfl

lemma lt_eq_getLast {σ : List V} (h : σ ≠ []) : g.lt σ = σ.getLast h := by
  unfold lt; rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast h]; rfl

lemma hd_mem {σ : List V} (h : σ ≠ []) : g.hd σ ∈ σ := by
  rw [g.hd_eq_head h]; exact List.head_mem h

lemma lt_mem {σ : List V} (h : σ ≠ []) : g.lt σ ∈ σ := by
  rw [g.lt_eq_getLast h]; exact List.getLast_mem h

lemma ne_nil_of_strand {act : V → Prop} {σ : List V} (h : g.StrandOK act σ) : σ ≠ [] := by
  rintro rfl; have := h.two_le; simp at this

/-! #### Changing the activity predicate -/

lemma StrandOK.congr {act act' : V → Prop} {σ : List V} (h : g.StrandOK act σ)
    (hc : ∀ v ∈ σ, act v ↔ act' v) : g.StrandOK act' σ := by
  have hne := g.ne_nil_of_strand h
  refine ⟨h.two_le, h.chain, fun v hv => ?_, fun ha => ?_, fun ha => ?_⟩
  · rw [← hc v (List.tail_subset _ (List.dropLast_subset _ hv))]; exact h.inner_na v hv
  · exact h.hd_bd ((hc _ (g.hd_mem hne)).2 ha)
  · exact h.lt_bd ((hc _ (g.lt_mem hne)).2 ha)

lemma JoinOK.congr {act act' : V → Prop} {u v : V} (h : g.JoinOK act u v) (hu : act u ↔ act' u)
    (hv : act v ↔ act' v) : g.JoinOK act' u v := by
  unfold JoinOK at *; rw [← hu, ← hv]; exact h

lemma JoinOK.symm {act : V → Prop} {u v : V} (h : g.JoinOK act u v) : g.JoinOK act v u := by
  rcases h with ⟨h1, h2, G, h3, h4⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl ⟨h2, h1, G, h4, h3⟩
  · exact Or.inr ⟨h2, h1, h3.symm⟩

lemma Circ.congr {act act' : V → Prop} {cs : List (List V)} (h : g.Circ act cs)
    (hc : ∀ v ∈ cs.flatten, act v ↔ act' v) : g.Circ act' cs := by
  refine ⟨h.ne, fun σ hσ => (h.strand σ hσ).congr g (fun v hv => hc v
    (List.mem_flatten.2 ⟨σ, hσ, hv⟩)), h.nodup, fun p hp => (h.join p hp).congr g ?_ ?_⟩
  · have h1 := mem_of_mem_cpairs_fst hp
    exact hc _ (List.mem_flatten.2 ⟨_, h1, g.lt_mem (g.ne_nil_of_strand (h.strand _ h1))⟩)
  · have h1 := mem_of_mem_cpairs_snd hp
    exact hc _ (List.mem_flatten.2 ⟨_, h1, g.hd_mem (g.ne_nil_of_strand (h.strand _ h1))⟩)

/-! #### Rotation -/

lemma Circ.rotate {act : V → Prop} {cs : List (List V)} (h : g.Circ act cs) (k : ℕ) :
    g.Circ act (cs.rotate k) := by
  refine ⟨?_, fun σ hσ => h.strand σ (List.mem_rotate.1 hσ), ?_, fun p hp =>
    h.join p (mem_cpairs_rotate.1 hp)⟩
  · intro h'; exact h.ne (List.rotate_eq_nil_iff.1 h')
  · exact (List.Perm.flatten (List.rotate_perm cs k)).nodup_iff.2 h.nodup

lemma sz_rotate (act : V → Prop) (cs : List (List V)) (k : ℕ) :
    g.sz act (cs.rotate k) = g.sz act cs := by
  unfold sz
  rw [((List.rotate_perm cs k).map _).sum_eq, ((cpairs_rotate cs k).map _).sum_eq]

/-! #### Flattening -/

lemma chain_flatten {cs : List (List V)} (hne : ∀ σ ∈ cs, σ ≠ [])
    (hch : ∀ σ ∈ cs, σ.IsChain g.Γ.Adj) (hj : ∀ p ∈ lpairs cs, g.Γ.Adj (g.lt p.1) (g.hd p.2)) :
    cs.flatten.IsChain g.Γ.Adj := by
  induction cs with
  | nil => simp
  | cons σ t ih =>
    rw [List.flatten_cons]
    have ht := ih (fun τ hτ => hne τ (by simp [hτ])) (fun τ hτ => hch τ (by simp [hτ]))
      (fun p hp => hj p (by cases t with
        | nil => simp at hp
        | cons τ t => simp only [lpairs_cons_cons]; exact List.mem_cons_of_mem _ hp))
    cases t with
    | nil => simpa using hch σ (by simp)
    | cons τ t =>
      have hσ := hne σ (by simp)
      have hτ := hne τ (by simp)
      have hτt : (τ :: t).flatten ≠ [] := by simp [hτ]
      refine List.IsChain.append (hch σ (by simp)) ht ?_
      intro x hx y hy
      rw [List.getLast?_eq_some_getLast hσ, Option.mem_def, Option.some.injEq] at hx
      have hy' : (τ :: t).flatten.head? = some (τ.head hτ) := by
        rw [List.flatten_cons, List.head?_append, List.head?_eq_some_head hτ]; rfl
      rw [hy', Option.mem_def, Option.some.injEq] at hy
      subst hx hy
      have := hj (σ, τ) (by simp)
      rwa [g.lt_eq_getLast hσ, g.hd_eq_head hτ] at this

lemma countPairs_flatten (r : V → V → Prop) {cs : List (List V)} (hne : ∀ σ ∈ cs, σ ≠ []) :
    countPairs r cs.flatten = (cs.map (countPairs r)).sum +
      ((lpairs cs).map (fun p => if r (g.lt p.1) (g.hd p.2) then 1 else 0)).sum := by
  induction cs with
  | nil => rfl
  | cons σ t ih =>
    have ih' := ih (fun τ hτ => hne τ (by simp [hτ]))
    cases t with
    | nil => simp
    | cons τ t =>
      have hσ := hne σ (by simp)
      have hτ := hne τ (by simp)
      have hτt : (τ :: t).flatten ≠ [] := by simp [hτ]
      rw [List.flatten_cons, countPairs_append r σ _ hσ hτt, ih']
      have hh : (τ :: t).flatten.head hτt = g.hd τ := by
        rw [g.hd_eq_head hτ]; simp [List.flatten_cons, List.head_append_of_ne_nil hτ]
      rw [hh, ← g.lt_eq_getLast hσ]
      simp only [List.map_cons, List.sum_cons, lpairs_cons_cons]
      ring

lemma cpairs_eq_lpairs_append (cs : List (List V)) (h : cs ≠ []) :
    cpairs cs = lpairs cs ++ [(cs.getLast h, cs.head h)] := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil h
  rw [cpairs_cons, lpairs_append_singleton _ _ (by simp)]; rfl

/-- A circuit without active vertices is a cycle of `Γ`; removing one edge gives a path. -/
lemma Circ.path {act : V → Prop} {cs : List (List V)} (h : g.Circ act cs)
    (hna : ∀ v ∈ cs.flatten, ¬ act v) :
    IsPathL g.Γ cs.flatten ∧ g.sz act cs ≤ countPairs g.Mp cs.flatten + 1 := by
  have hne : ∀ σ ∈ cs, σ ≠ [] := fun σ hσ => g.ne_nil_of_strand (h.strand σ hσ)
  have hjoin : ∀ p ∈ cpairs cs, g.Γ.Adj (g.lt p.1) (g.hd p.2) := by
    intro p hp
    rcases h.join p hp with ⟨h1, -⟩ | ⟨-, -, h3⟩
    · exact absurd h1 (hna _ (List.mem_flatten.2 ⟨_, mem_of_mem_cpairs_fst hp,
        g.lt_mem (hne _ (mem_of_mem_cpairs_fst hp))⟩))
    · exact h3
  have hcp := cpairs_eq_lpairs_append cs h.ne
  refine ⟨⟨g.chain_flatten hne (fun σ hσ => (h.strand σ hσ).chain) (fun p hp => hjoin p
    (by rw [hcp]; exact List.mem_append_left _ hp)), h.nodup⟩, ?_⟩
  rw [g.countPairs_flatten g.Mp hne]
  unfold sz
  rw [hcp, List.map_append, List.sum_append]
  have h1 : ((lpairs cs).map (fun p => g.joinVal act (g.lt p.1) (g.hd p.2))).sum ≤
      ((lpairs cs).map (fun p => if g.Mp (g.lt p.1) (g.hd p.2) then 1 else 0)).sum := by
    refine List.sum_le_sum fun p _ => ?_
    unfold joinVal; split_ifs with h1 h2 <;> simp_all
  have h2 : (([(cs.getLast h.ne, cs.head h.ne)] : List _).map
      (fun p => g.joinVal act (g.lt p.1) (g.hd p.2))).sum ≤ 1 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    unfold joinVal; split_ifs <;> simp
  omega

end Geo

end Lovasz
