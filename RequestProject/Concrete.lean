module
public import RequestProject.Core

/-!
# The concrete geometry of Theorem 1.2

The cycle `L` has vertices `0, …, 2n-1` and the matching `M` joins `i < n` with `n + f i`.
We cut each half into `Q = ⌊(n-2)/t⌋` intervals of `t` consecutive vertices; interval `k < Q`
starts at `1 + k t` and interval `Q + k` starts at `n + 1 + k t`.  The remaining vertices
(including `0`, `n - 1`, `n` and `2n - 1`) lie in no interval.
-/

@[expose] public section


open Classical

namespace Lovasz

namespace Conc

/-- The number of intervals in each half. -/
def nQ (n t : ℕ) : ℕ := (n - 2) / t

/-- The first vertex of interval `k`. -/
def st (n t k : ℕ) : ℕ := if k < nQ n t then 1 + k * t else n + 1 + (k - nQ n t) * t

variable {n t : ℕ}

lemma nQ_mul_le : nQ n t * t ≤ n - 2 := Nat.div_mul_le_self _ _

lemma one_le_st (k : ℕ) : 1 ≤ st n t k := by unfold st; split_ifs <;> omega

lemma t_pos_of {k : ℕ} (hk : k < nQ n t) : 0 < t :=
  Nat.pos_of_ne_zero (fun h => by simp [nQ, h] at hk)

lemma st_lt_half {k : ℕ} (hk : k < nQ n t) : st n t k + t ≤ n - 1 := by
  have h := @nQ_mul_le n t
  have ht := t_pos_of hk
  unfold st; rw [if_pos hk]
  have : k * t + t ≤ nQ n t * t := by nlinarith
  omega

lemma st_ge_half {k : ℕ} (hk : nQ n t ≤ k) : n + 1 ≤ st n t k := by
  unfold st; rw [if_neg (by omega)]; omega

lemma st_lt_top {k : ℕ} (hk : k < 2 * nQ n t) : st n t k + t ≤ 2 * n - 1 := by
  have h := @nQ_mul_le n t
  have ht : 0 < t := t_pos_of (n := n) (k := 0) (by omega)
  by_cases hk' : k < nQ n t
  · have := st_lt_half hk'; omega
  · unfold st; rw [if_neg hk']
    have : (k - nQ n t) * t + t ≤ nQ n t * t := by
      have : k - nQ n t + 1 ≤ nQ n t := by omega
      nlinarith
    omega

lemma st_mono {k k' : ℕ} (hkk : k < k') (hk' : k' < 2 * nQ n t) : st n t k + t ≤ st n t k' := by
  have ht : 0 < t := t_pos_of (n := n) (k := 0) (by omega)
  by_cases h1 : k' < nQ n t
  · unfold st; rw [if_pos h1, if_pos (by omega)]; nlinarith
  · by_cases h2 : k < nQ n t
    · have := st_lt_half (n := n) (t := t) h2; have := st_ge_half (n := n) (t := t) (not_lt.1 h1)
      omega
    · unfold st; rw [if_neg h1, if_neg h2]
      have : (k - nQ n t) + 1 ≤ k' - nQ n t := by omega
      nlinarith

/-- Two intervals containing a common vertex are equal. -/
lemma st_inj {k k' v : ℕ} (hk : k < 2 * nQ n t) (hk' : k' < 2 * nQ n t)
    (h1 : st n t k ≤ v) (h2 : v < st n t k + t) (h3 : st n t k' ≤ v) (h4 : v < st n t k' + t) :
    k = k' := by
  rcases lt_trichotomy k k' with h | h | h
  · have := st_mono h hk'; omega
  · exact h
  · have := st_mono h hk; omega

/-- A natural number as a vertex of the cycle. -/
def fv (n : ℕ) (hn : 0 < n) (i : ℕ) : Fin (2 * n) := ⟨i % (2 * n), Nat.mod_lt _ (by omega)⟩

lemma fv_val {hn : 0 < n} {i : ℕ} (hi : i < 2 * n) : (fv n hn i).val = i := Nat.mod_eq_of_lt hi

lemma fv_eq {hn : 0 < n} (v : Fin (2 * n)) : fv n hn v.val = v := Fin.ext (fv_val v.2)

/-- The vertices `a, a+1, …, b` of the cycle. -/
def rng (n : ℕ) (hn : 0 < n) (a b : ℕ) : List (Fin (2 * n)) :=
  (List.range' a (b + 1 - a)).map (fv n hn)

variable {hn : 0 < n}

lemma mem_rng {a b : ℕ} (hb : b < 2 * n) {x : Fin (2 * n)} :
    x ∈ rng n hn a b ↔ a ≤ x.val ∧ x.val ≤ b := by
  unfold rng
  simp only [List.mem_map, List.mem_range']
  constructor
  · rintro ⟨i, ⟨j, hj, rfl⟩, rfl⟩
    rw [fv_val (by omega)]; omega
  · rintro ⟨h1, h2⟩
    exact ⟨x.val, ⟨x.val - a, by omega, by omega⟩, fv_eq x⟩

lemma rng_nodup {a b : ℕ} (hb : b < 2 * n) : (rng n hn a b).Nodup := by
  unfold rng
  refine List.Nodup.map_on (fun i hi j hj e => ?_) List.nodup_range'
  rw [List.mem_range'] at hi hj
  have := congrArg Fin.val e
  rwa [fv_val (by omega), fv_val (by omega)] at this

lemma adj_succ (f : Fin n → Fin n) {a : ℕ} (ha : a + 1 < 2 * n) :
    (cycleMatchGraph n f).Adj (fv n hn a) (fv n hn (a + 1)) := by
  rw [cycleMatchGraph, SimpleGraph.fromRel_adj]
  refine ⟨fun e => ?_, Or.inl (Or.inl ?_)⟩
  · have := congrArg Fin.val e; rw [fv_val (by omega), fv_val (by omega)] at this; omega
  · unfold cycAdj; rw [fv_val (by omega), fv_val (by omega), Nat.mod_eq_of_lt ha]

lemma adj_wrap (f : Fin n → Fin n) :
    (cycleMatchGraph n f).Adj (fv n hn (2 * n - 1)) (fv n hn 0) := by
  rw [cycleMatchGraph, SimpleGraph.fromRel_adj]
  refine ⟨fun e => ?_, Or.inl (Or.inl ?_)⟩
  · have := congrArg Fin.val e; rw [fv_val (by omega), fv_val (by omega)] at this; omega
  · unfold cycAdj; rw [fv_val (by omega), fv_val (by omega), show 2 * n - 1 + 1 = 2 * n by omega,
      Nat.mod_self]

lemma rng_chain (f : Fin n → Fin n) {a b : ℕ} (hb : b < 2 * n) :
    (rng n hn a b).IsChain (cycleMatchGraph n f).Adj := by
  unfold rng
  suffices h : ∀ m a, a + m < 2 * n →
      ((List.range' a (m + 1)).map (fv n hn)).IsChain (cycleMatchGraph n f).Adj by
    rcases Nat.lt_or_ge b a with hab | hab
    · rw [show b + 1 - a = 0 by omega]; simp
    · rw [show b + 1 - a = (b - a) + 1 by omega]; exact h _ _ (by omega)
  intro m
  induction m with
  | zero => intro a _; simp
  | succ m ih =>
    intro a ha
    rw [List.range'_succ, List.map_cons]
    have h2 := ih (a + 1) (by omega)
    rw [List.range'_succ, List.map_cons] at h2 ⊢
    exact List.IsChain.cons_cons (adj_succ f (by omega)) h2


lemma rng_head {a b : ℕ} (hab : a ≤ b) : (rng n hn a b).head? = some (fv n hn a) := by
  unfold rng
  rw [show b + 1 - a = (b - a) + 1 by omega, List.range'_succ]; rfl

lemma rng_getLast {a b : ℕ} (hab : a ≤ b) : (rng n hn a b).getLast? = some (fv n hn b) := by
  unfold rng
  rw [show b + 1 - a = (b - a) + 1 by omega, List.range'_concat, List.map_append,
    List.getLast?_append]
  simp [show a + (b - a) = b by omega]

/-- The segment of `L` between two vertices. -/
def seg (n : ℕ) (hn : 0 < n) (u v : Fin (2 * n)) : List (Fin (2 * n)) :=
  if u.val ≤ v.val then rng n hn u.val v.val else (rng n hn v.val u.val).reverse

lemma mem_seg {u v x : Fin (2 * n)} :
    x ∈ seg n hn u v ↔ min u.val v.val ≤ x.val ∧ x.val ≤ max u.val v.val := by
  unfold seg
  split_ifs with h
  · rw [mem_rng v.2]; simp [min_eq_left h, max_eq_right h]
  · rw [List.mem_reverse, mem_rng u.2]; simp [min_eq_right (le_of_not_ge h),
      max_eq_left (le_of_not_ge h)]

lemma seg_head (u v : Fin (2 * n)) : (seg n hn u v).head? = some u := by
  unfold seg
  split_ifs with h
  · rw [rng_head h, fv_eq]
  · rw [List.head?_reverse, rng_getLast (by omega), fv_eq]

lemma seg_last (u v : Fin (2 * n)) : (seg n hn u v).getLast? = some v := by
  unfold seg
  split_ifs with h
  · rw [rng_getLast h, fv_eq]
  · rw [List.getLast?_reverse, rng_head (by omega), fv_eq]

lemma seg_nodup (u v : Fin (2 * n)) : (seg n hn u v).Nodup := by
  unfold seg
  split_ifs
  · exact rng_nodup v.2
  · exact List.nodup_reverse.2 (rng_nodup u.2)

lemma seg_chain (f : Fin n → Fin n) (u v : Fin (2 * n)) :
    (seg n hn u v).IsChain (cycleMatchGraph n f).Adj := by
  unfold seg
  split_ifs
  · exact rng_chain f v.2
  · rw [List.isChain_reverse]
    exact (rng_chain f u.2).imp fun a b h => (cycleMatchGraph n f).adj_symm h

variable (t)

/-- The interval containing a vertex. -/
noncomputable def ivOf (n : ℕ) (v : Fin (2 * n)) : Option (Fin (2 * nQ n t)) :=
  if h : ∃ k : Fin (2 * nQ n t), st n t k ≤ v.val ∧ v.val < st n t k + t then some h.choose
  else none

variable {t}

lemma ivOf_eq_some {v : Fin (2 * n)} {k : Fin (2 * nQ n t)} :
    ivOf t n v = some k ↔ st n t k ≤ v.val ∧ v.val < st n t k + t := by
  unfold ivOf
  constructor
  · intro h
    split_ifs at h with h'
    · rw [Option.some.injEq] at h; subst h; exact h'.choose_spec
  · intro h
    have h' : ∃ k : Fin (2 * nQ n t), st n t k ≤ v.val ∧ v.val < st n t k + t := ⟨k, h⟩
    rw [dif_pos h', Option.some.injEq]
    have := h'.choose_spec
    exact Fin.ext (st_inj h'.choose.2 k.2 this.1 this.2 h.1 h.2)

lemma ivOf_eq_none {v : Fin (2 * n)} :
    ivOf t n v = none ↔ ∀ k : Fin (2 * nQ n t), ¬ (st n t k ≤ v.val ∧ v.val < st n t k + t) := by
  unfold ivOf
  split_ifs with h
  · simp only [false_iff, not_forall, not_not]; exact h
  · push_neg at h; simpa using h

/-- The matching relation. -/
def Mrel (n : ℕ) (f : Fin n → Fin n) (u v : Fin (2 * n)) : Prop := matchAdj n f u v ∨ matchAdj n f v u

lemma Mrel_symm {f : Fin n → Fin n} {u v : Fin (2 * n)} (h : Mrel n f u v) : Mrel n f v u :=
  h.symm

lemma Mrel_adj {f : Fin n → Fin n} {u v : Fin (2 * n)} (h : Mrel n f u v) :
    (cycleMatchGraph n f).Adj u v := by
  rw [cycleMatchGraph, SimpleGraph.fromRel_adj]
  refine ⟨fun e => ?_, ?_⟩
  · subst e; rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · rcases h with h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inr h)

lemma Mrel_uniq {f : Fin n → Fin n} (hf : Function.Injective f) {u v w : Fin (2 * n)}
    (h1 : Mrel n f u v) (h2 : Mrel n f u w) : v = w := by
  rcases h1 with ⟨a1, b1⟩ | ⟨a1, b1⟩ <;> rcases h2 with ⟨a2, b2⟩ | ⟨a2, b2⟩
  · exact Fin.ext (by rw [b1, b2])
  · omega
  · omega
  · have : f ⟨v.val, a1⟩ = f ⟨w.val, a2⟩ := Fin.ext (by omega)
    have := congrArg Fin.val (hf this)
    exact Fin.ext this


lemma st_bound {k : Fin (2 * nQ n t)} : st n t k + t ≤ 2 * n - 1 := st_lt_top k.2

lemma lo_val (k : Fin (2 * nQ n t)) : (fv n hn (st n t k)).val = st n t k :=
  fv_val (by have := @st_bound n t k; omega)

lemma hi_val (k : Fin (2 * nQ n t)) :
    (fv n hn (st n t k + t - 1)).val = st n t k + t - 1 :=
  fv_val (by have := @st_bound n t k; omega)

end Conc

namespace Conc

/-- **The concrete geometry**: `L ∪ M` with intervals of length `t` and the block map `blk`. -/
noncomputable def cgeo (n t : ℕ) (hn : 0 < n) (ht : 2 ≤ t) (hQ : 0 < nQ n t) (f : Fin n → Fin n)
    (hf : Function.Injective f) {β : Type*} (blk : Fin (2 * nQ n t) → Option β) :
    Geo (Fin (2 * n)) (Fin (2 * nQ n t)) β where
  Γ := cycleMatchGraph n f
  Mp := Mrel n f
  ivOf := ivOf t n
  blk := blk
  lo k := fv n hn (st n t k)
  hi k := fv n hn (st n t k + t - 1)
  seg := seg n hn
  dflt := fv n hn 0
  dI := ⟨0, by omega⟩
  Mp_symm := Mrel_symm
  Mp_adj := Mrel_adj
  Mp_uniq := Mrel_uniq hf
  lo_ne_hi k := by
    intro e
    have := congrArg Fin.val e
    rw [lo_val, hi_val] at this
    omega
  iv_lo k := ivOf_eq_some.2 (by rw [lo_val]; omega)
  iv_hi k := ivOf_eq_some.2 (by rw [hi_val]; omega)
  seg_head := fun _ _ => seg_head _ _
  seg_last := fun _ _ => seg_last _ _
  seg_chain := fun _ _ => seg_chain f _ _
  seg_nodup := fun _ _ => seg_nodup _ _
  seg_iv := by
    intro J u v hu hv x hx
    rw [ivOf_eq_some] at hu hv ⊢
    rw [mem_seg] at hx
    constructor
    · exact le_trans (le_min hu.1 hv.1) hx.1
    · exact lt_of_le_of_lt hx.2 (max_lt hu.2 hv.2)
  seg_orient := by
    intro J w₁ w₂ h1 h2 hne
    rw [ivOf_eq_some] at h1 h2
    have hne' : w₁.val ≠ w₂.val := fun e => hne (Fin.ext e)
    rcases lt_or_gt_of_ne hne' with h | h
    · left
      intro x hx1 hx2
      rw [mem_seg, lo_val] at hx1
      rw [mem_seg, hi_val] at hx2
      have := hx1.2; have := hx2.1
      simp only [le_max_iff, min_le_iff] at *
      omega
    · right
      intro x hx1 hx2
      rw [mem_seg, hi_val] at hx1
      rw [mem_seg, lo_val] at hx2
      have := hx1.1; have := hx2.2
      simp only [le_max_iff, min_le_iff] at *
      omega

end Conc

end Lovasz
