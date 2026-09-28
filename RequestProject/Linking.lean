module
public import RequestProject.Expander

/-!
# The linking lemma (Lemma 2.6)

Arcs are vertex lists `P` of the expander (on its vertex type `ι`); `arcInner P` is the list of
internal vertices and `arcEdges P` the list of edges.  A *junction list* `Jn` is a cyclic list of
pairs `(x, y)`; the *demands* of `Jn` are the pairs `(y_i, x_{i+1})`.  Lemma 2.6 is proved in
the form of `LinkEvent`: every junction list whose entries lie in `V* ∪ Y` can be realised by
internally disjoint, edge-disjoint arcs avoiding `V* ∪ Y`, one of which is long.
-/

@[expose] public section


open scoped BigOperators
open Classical Filter

namespace Lovasz

noncomputable section

variable {ι : Type*}

/-- Internal vertices of an arc. -/
def arcInner (P : List ι) : List ι := P.tail.dropLast

/-- Edges of an arc. -/
def arcEdges (P : List ι) : List (Sym2 ι) := (P.zip P.tail).map (fun p => s(p.1, p.2))

/-- `P` is an arc from `d.1` to `d.2` in `H` whose internal vertices lie in `U \ B`. -/
def ArcOK (H : SimpleGraph ι) (U B : Finset ι) (d : ι × ι) (P : List ι) : Prop :=
  P.head? = some d.1 ∧ P.getLast? = some d.2 ∧ P.IsChain H.Adj ∧ 2 ≤ P.length ∧
    ∀ v ∈ arcInner P, v ∈ U ∧ v ∉ B

/-- The entries of a junction list (a junction `(x, x)` contributes one entry). -/
def jEntries (Jn : List (ι × ι)) : List ι :=
  Jn.flatMap (fun p => if p.1 = p.2 then [p.1] else [p.1, p.2])

/-- The demands `(y_i, x_{i+1})` of a cyclic junction list. -/
def demands (Jn : List (ι × ι)) : List (ι × ι) :=
  List.zipWith (fun p q => (p.2, q.1)) Jn (Jn.rotate 1)

/-- The conclusion of Lemma 2.6 for the expander `(H, U)`, the deterministic set `Vs` and the
random set `Y`. -/
def LinkEvent (H : SimpleGraph ι) (U Vs Y : Finset ι) (bound : ℝ) : Prop :=
  ∀ Jn : List (ι × ι), Jn ≠ [] → (jEntries Jn).Nodup →
    (∀ v ∈ jEntries Jn, v ∈ U ∧ (v ∈ Vs ∨ v ∈ Y)) →
    ∃ A : List (List ι), List.Forall₂ (ArcOK H U (Vs ∪ Y)) (demands Jn) A ∧
      (A.flatMap arcInner).Nodup ∧ (A.flatMap arcEdges).Nodup ∧
      ∃ P ∈ A, bound ≤ (P.length : ℝ) - 1

section lists

lemma mem_jEntries {Jn : List (ι × ι)} {v : ι} :
    v ∈ jEntries Jn ↔ ∃ p ∈ Jn, v = p.1 ∨ v = p.2 := by
  unfold jEntries
  simp only [List.mem_flatMap]
  refine exists_congr fun p => and_congr_right fun _ => ?_
  split_ifs with h
  · simp [← h]
  · simp

lemma jEntries_disjoint {Jn : List (ι × ι)} (h : (jEntries Jn).Nodup) {i j : ℕ}
    (hi : i < Jn.length) (hj : j < Jn.length) (hij : i ≠ j) {v : ι}
    (hv : v = Jn[i].1 ∨ v = Jn[i].2) (hw : v = Jn[j].1 ∨ v = Jn[j].2) : False := by
  unfold jEntries at h
  rw [List.nodup_flatMap] at h
  have hp := h.2
  rw [List.pairwise_iff_getElem] at hp
  have key : ∀ a b, a < b → (ha : a < Jn.length) → (hb : b < Jn.length) →
      (v = Jn[a].1 ∨ v = Jn[a].2) → (v = Jn[b].1 ∨ v = Jn[b].2) → False := by
    intro a b hab ha hb h1 h2
    have := hp a b ha hb hab
    have m1 : v ∈ (if Jn[a].1 = Jn[a].2 then [Jn[a].1] else [Jn[a].1, Jn[a].2]) := by
      split_ifs with h' <;> rcases h1 with h1 | h1 <;> simp [h1, h']
    have m2 : v ∈ (if Jn[b].1 = Jn[b].2 then [Jn[b].1] else [Jn[b].1, Jn[b].2]) := by
      split_ifs with h' <;> rcases h2 with h2 | h2 <;> simp [h2, h']
    exact this m1 m2
  rcases lt_or_gt_of_ne hij with h' | h'
  · exact key i j h' hi hj hv hw
  · exact key j i h' hj hi hw hv

lemma mem_iff_inner {l : List ι} {a b : ι} (ha : l.head? = some a) (hb : l.getLast? = some b)
    (hl : 2 ≤ l.length) {v : ι} : v ∈ l ↔ v = a ∨ v ∈ arcInner l ∨ v = b := by
  obtain ⟨c, l', rfl⟩ : ∃ c l', l = c :: l' := by
    cases l with
    | nil => simp at hl
    | cons c l' => exact ⟨c, l', rfl⟩
  simp only [List.head?_cons, Option.some.injEq] at ha
  subst ha
  have hl' : l' ≠ [] := by rintro rfl; simp at hl
  have hb' : l'.getLast hl' = b := by
    rw [List.getLast?_cons, List.getLast?_eq_some_getLast hl'] at hb; simpa using hb
  unfold arcInner
  simp only [List.tail_cons, List.mem_cons]
  conv_lhs => rw [← List.dropLast_append_getLast hl']
  rw [hb']
  simp only [List.mem_append, List.mem_singleton]

lemma notMem_inner_of_nodup {l : List ι} {a b : ι} (ha : l.head? = some a)
    (hb : l.getLast? = some b) (hl : l.Nodup) {v : ι} (hv : v ∈ arcInner l) : v ≠ a ∧ v ≠ b := by
  obtain ⟨c, l', rfl⟩ : ∃ c l', l = c :: l' := by
    cases l with
    | nil => simp at ha
    | cons c l' => exact ⟨c, l', rfl⟩
  simp only [List.head?_cons, Option.some.injEq] at ha
  subst ha
  unfold arcInner at hv
  simp only [List.tail_cons] at hv
  have hl' : l' ≠ [] := by rintro rfl; simp at hv
  have hb' : l'.getLast hl' = b := by
    rw [List.getLast?_cons, List.getLast?_eq_some_getLast hl'] at hb; simpa using hb
  have hvl' : v ∈ l' := List.dropLast_subset _ hv
  rw [List.nodup_cons] at hl
  refine ⟨fun h => hl.1 (h ▸ hvl'), fun h => ?_⟩
  have h2 := hl.2
  rw [← List.dropLast_append_getLast hl', hb'] at h2
  rw [List.nodup_append] at h2
  exact h2.2.2 v hv b (List.mem_singleton_self _) h

lemma inner_subset (l : List ι) : arcInner l ⊆ l := fun _ h =>
  List.tail_subset _ (List.dropLast_subset _ h)

lemma inner_nodup {l : List ι} (h : l.Nodup) : (arcInner l).Nodup :=
  (h.sublist (List.tail_sublist l)).sublist (List.dropLast_sublist _)

lemma mem_of_mem_arcEdges {l : List ι} {u w : ι} (h : s(u, w) ∈ arcEdges l) :
    u ∈ l ∧ w ∈ l := by
  unfold arcEdges at h
  obtain ⟨⟨p, q⟩, hpq, he⟩ := List.mem_map.1 h
  have hp := List.of_mem_zip hpq
  rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨hp.1, List.tail_subset _ hp.2⟩
  · exact ⟨List.tail_subset _ hp.2, hp.1⟩

lemma arcEdges_nodup {l : List ι} (h : l.Nodup) : (arcEdges l).Nodup := by
  induction l with
  | nil => simp [arcEdges]
  | cons a l ih =>
    cases l with
    | nil => simp [arcEdges]
    | cons b l =>
      rw [List.nodup_cons] at h
      have ih' := ih h.2
      have : arcEdges (a :: b :: l) = s(a, b) :: arcEdges (b :: l) := by
        simp [arcEdges]
      rw [this, List.nodup_cons]
      refine ⟨fun hm => ?_, ih'⟩
      have := (mem_of_mem_arcEdges hm)
      exact h.1 this.1

lemma arcEdges_adj {H : SimpleGraph ι} {l : List ι} (hc : l.IsChain H.Adj) {u w : ι}
    (h : s(u, w) ∈ arcEdges l) : H.Adj u w := by
  induction l with
  | nil => simp [arcEdges] at h
  | cons a l ih =>
    cases l with
    | nil => simp [arcEdges] at h
    | cons b l =>
      rw [List.isChain_cons_cons] at hc
      have : arcEdges (a :: b :: l) = s(a, b) :: arcEdges (b :: l) := by simp [arcEdges]
      rw [this, List.mem_cons] at h
      rcases h with h | h
      · rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hc.1
        · exact hc.1.symm
      · exact ih hc.2 h

lemma two_le_length_of_ne {l : List ι} {a b : ι} (ha : l.head? = some a)
    (hb : l.getLast? = some b) (hab : a ≠ b) : 2 ≤ l.length := by
  match l, ha, hb with
  | [c], ha, hb => simp at ha hb; exact absurd (ha.symm.trans hb) hab
  | _ :: _ :: _, _, _ => simp

end lists

section linkfun

variable {V : Type*}

lemma list_disjoint_of_pairwise {L : List (List V)} (h : List.Pairwise List.Disjoint L) {a b : ℕ}
    (ha : a < L.length) (hb : b < L.length) (hab : a ≠ b) : List.Disjoint L[a] L[b] := by
  rw [List.pairwise_iff_getElem] at h
  rcases lt_or_gt_of_ne hab with h' | h'
  · exact h a b ha hb h'
  · exact (h b a hb ha h').symm

/-- `LinkProp` in function form, for the pairs `Q i` with `i ∈ S`. -/
lemma linkProp_fun {G : SimpleGraph V} {U R : Finset V} {K : ℝ} (h : LinkProp G U R K) {m : ℕ}
    (S : Finset (Fin m)) (Q : Fin m → V × V)
    (hinj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (Q i).1 ≠ (Q j).1 ∧ (Q i).2 ≠ (Q j).2 ∧ (Q i).1 ≠ (Q j).2)
    (hne : ∀ i ∈ S, (Q i).1 ≠ (Q i).2)
    (hmem : ∀ i ∈ S, (Q i).1 ∈ U \ R ∧ (Q i).2 ∈ U \ R)
    (hexp : ∀ X : Finset V, (∀ x ∈ X, ∃ i ∈ S, x = (Q i).1 ∨ x = (Q i).2) →
      K * X.card ≤ (extNb G U X ∅).card) :
    ∃ P : Fin m → List V, (∀ i ∈ S, PathFrom G (Q i).1 (Q i).2 (P i) ∧
      ∀ v ∈ P i, v = (Q i).1 ∨ v = (Q i).2 ∨ v ∈ R) ∧
      ∀ i ∈ S, ∀ j ∈ S, i ≠ j → List.Disjoint (P i) (P j) := by
  set L := S.sort (· ≤ ·) with hL
  have hLnd : L.Nodup := Finset.sort_nodup _ _
  have hLmem : ∀ i, i ∈ L ↔ i ∈ S := fun i => Finset.mem_sort _
  have hnd : ((L.map Q).map Prod.fst ++ (L.map Q).map Prod.snd).Nodup := by
    rw [List.map_map, List.map_map, List.nodup_append]
    refine ⟨hLnd.map_on fun i hi j hj hij => ?_, hLnd.map_on fun i hi j hj hij => ?_, ?_⟩
    · by_contra hne'; exact (hinj i ((hLmem i).1 hi) j ((hLmem j).1 hj) hne').1 hij
    · by_contra hne'; exact (hinj i ((hLmem i).1 hi) j ((hLmem j).1 hj) hne').2.1 hij
    · intro a ha b hb hab
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hb
      by_cases hij : i = j
      · subst hij; exact hne i ((hLmem i).1 hi) hab
      · exact (hinj i ((hLmem i).1 hi) j ((hLmem j).1 hj) hij).2.2 hab
  have hends : ∀ p ∈ L.map Q, p.1 ∈ U \ R ∧ p.2 ∈ U \ R := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hp
    exact hmem i ((hLmem i).1 hi)
  have hX : ∀ X ⊆ ((L.map Q).map Prod.fst ++ (L.map Q).map Prod.snd).toFinset,
      K * X.card ≤ (extNb G U X ∅).card := by
    intro X hX
    refine hexp X fun x hx => ?_
    have := hX hx
    simp only [List.mem_toFinset, List.mem_append, List.map_map, List.mem_map,
      Function.comp] at this
    rcases this with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · exact ⟨i, (hLmem i).1 hi, Or.inl rfl⟩
    · exact ⟨i, (hLmem i).1 hi, Or.inr rfl⟩
  obtain ⟨Ps, hPsnd, hF⟩ := h (L.map Q) hnd hends hX
  have hlen : Ps.length = L.length := by rw [← hF.length_eq, List.length_map]
  rw [List.forall₂_iff_get] at hF
  refine ⟨fun i => Ps.getD (L.idxOf i) [], fun i hi => ?_, fun i hi j hj hij => ?_⟩
  · have hk : L.idxOf i < L.length := List.idxOf_lt_length_iff.2 ((hLmem i).2 hi)
    have hk' : L.idxOf i < Ps.length := hlen ▸ hk
    have := hF.2 (L.idxOf i) (by simpa using hk) hk'
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_idxOf] at this
    simp only [List.getD_eq_getElem _ _ hk']
    exact this
  · have hk : L.idxOf i < L.length := List.idxOf_lt_length_iff.2 ((hLmem i).2 hi)
    have hk2 : L.idxOf j < L.length := List.idxOf_lt_length_iff.2 ((hLmem j).2 hj)
    have hne' : L.idxOf i ≠ L.idxOf j := by
      intro he; apply hij
      rw [← List.getElem_idxOf hk, ← List.getElem_idxOf hk2]; simp [he]
    simp only [List.getD_eq_getElem _ _ (hlen ▸ hk), List.getD_eq_getElem _ _ (hlen ▸ hk2)]
    exact list_disjoint_of_pairwise (List.nodup_flatten.1 hPsnd).2 _ _ hne'

end linkfun

section junctions

lemma demands_length (Jn : List (ι × ι)) : (demands Jn).length = Jn.length := by
  simp [demands]

lemma demands_getElem (Jn : List (ι × ι)) (i : ℕ) (hi : i < (demands Jn).length) :
    (demands Jn)[i] = ((Jn[i]'(by simpa [demands_length] using hi)).2,
      (Jn[(i + 1) % Jn.length]'(Nat.mod_lt _ (by
        have := demands_length Jn; omega))).1) := by
  simp [demands, List.getElem_zipWith, List.getElem_rotate]

variable {Jn : List (ι × ι)}

lemma jn_snd_inj (h : (jEntries Jn).Nodup) {i j : ℕ} (hi : i < Jn.length) (hj : j < Jn.length)
    (he : Jn[i].2 = Jn[j].2) : i = j := by
  by_contra hij; exact jEntries_disjoint h hi hj hij (Or.inr rfl) (Or.inr he)

lemma jn_fst_inj (h : (jEntries Jn).Nodup) {i j : ℕ} (hi : i < Jn.length) (hj : j < Jn.length)
    (he : Jn[i].1 = Jn[j].1) : i = j := by
  by_contra hij; exact jEntries_disjoint h hi hj hij (Or.inl rfl) (Or.inl he)

lemma jn_snd_fst (h : (jEntries Jn).Nodup) {i j : ℕ} (hi : i < Jn.length) (hj : j < Jn.length)
    (he : Jn[i].2 = Jn[j].1) : i = j := by
  by_contra hij; exact jEntries_disjoint h hi hj hij (Or.inr rfl) (Or.inl he)

end junctions

/-- The colouring of the demands by three colours used in the proof of Lemma 2.6: cyclically
consecutive demands get different colours. -/
def dcol (m : ℕ) (i : ℕ) : ℕ := if i = m - 1 ∧ m % 3 = 1 then 1 else i % 3

lemma dcol_lt (m i : ℕ) : dcol m i < 3 := by
  unfold dcol; split_ifs <;> omega

lemma dcol_ne {m i j : ℕ} (hm : 3 ≤ m) (hi : i < m) (hj : j = (i + 1) % m) :
    dcol m i ≠ dcol m j := by
  unfold dcol
  have : (i + 1) % m = if i + 1 < m then i + 1 else 0 := by
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · have : i + 1 = m := by omega
      rw [this, Nat.mod_self]
  rw [this] at hj
  split_ifs at hj <;> subst hj <;> split_ifs <;> omega

section base

variable {H : SimpleGraph ι} {U : Finset ι} {K : ℝ}

lemma three_colour_paths {m : ℕ} (col : Fin m → Fin 3) (Q : Fin m → ι × ι)
    (Cc : Fin 3 → Finset ι) (hlink : ∀ c, LinkProp H U (Cc c) K)
    (hinj : ∀ i j, i ≠ j → col i = col j →
      (Q i).1 ≠ (Q j).1 ∧ (Q i).2 ≠ (Q j).2 ∧ (Q i).1 ≠ (Q j).2)
    (hne : ∀ i, (Q i).1 ≠ (Q i).2)
    (hmem : ∀ i, (Q i).1 ∈ U \ Cc (col i) ∧ (Q i).2 ∈ U \ Cc (col i))
    (hexp : ∀ X : Finset ι, (∀ x ∈ X, ∃ i, x = (Q i).1 ∨ x = (Q i).2) →
      K * X.card ≤ (extNb H U X ∅).card) :
    ∃ P : Fin m → List ι, (∀ i, PathFrom H (Q i).1 (Q i).2 (P i) ∧
      ∀ v ∈ P i, v = (Q i).1 ∨ v = (Q i).2 ∨ v ∈ Cc (col i)) ∧
      ∀ i j, i ≠ j → col i = col j → List.Disjoint (P i) (P j) := by
  have hc : ∀ c : Fin 3, ∃ P : Fin m → List ι,
      (∀ i ∈ Finset.univ.filter (fun i => col i = c), PathFrom H (Q i).1 (Q i).2 (P i) ∧
        ∀ v ∈ P i, v = (Q i).1 ∨ v = (Q i).2 ∨ v ∈ Cc c) ∧
      ∀ i ∈ Finset.univ.filter (fun i => col i = c), ∀ j ∈ Finset.univ.filter (fun i => col i = c),
        i ≠ j → List.Disjoint (P i) (P j) := by
    intro c
    refine linkProp_fun (hlink c) _ Q (fun i hi j hj hij => ?_) (fun i _ => hne i)
      (fun i hi => ?_) (fun X hX => hexp X fun x hx => ?_)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
      exact hinj i j hij (hi.trans hj.symm)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [← hi]; exact hmem i
    · obtain ⟨i, -, h⟩ := hX x hx; exact ⟨i, h⟩
  choose P hP hD using hc
  refine ⟨fun i => P (col i) i, fun i => ?_, fun i j hij hcol => ?_⟩
  · exact hP (col i) i (by simp)
  · dsimp only
    rw [hcol]
    exact hD (col j) i (by simp [hcol]) j (by simp) hij

end base

lemma succ_mod_eq {i m : ℕ} (hi : i < m) : (i + 1) % m = if i + 1 < m then i + 1 else 0 := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have : i + 1 = m := by omega
    rw [this, Nat.mod_self]

section base2

variable {H : SimpleGraph ι} {U : Finset ι} {K : ℝ}

lemma arc_head {pre suf P : List ι} {y y' : ι} (hP : P.head? = some y')
    (hpre : pre = [] ∧ y' = y ∨ pre = [y]) : (pre ++ P ++ suf).head? = some y := by
  rcases hpre with ⟨rfl, rfl⟩ | rfl
  · cases P with
    | nil => simp at hP
    | cons c P => simpa using hP
  · simp

lemma arc_last {pre suf P : List ι} {x x' : ι} (hP : P.getLast? = some x')
    (hsuf : suf = [] ∧ x' = x ∨ suf = [x]) : (pre ++ P ++ suf).getLast? = some x := by
  rcases hsuf with ⟨rfl, rfl⟩ | rfl
  · rw [List.append_nil, List.getLast?_append, hP]; rfl
  · simp

/-- The deterministic core of Lemma 2.6: with private neighbours for the vertices of `Vs` and
linking properties for three colour classes, every junction list of length at least three with
entries in `Vs ∪ T0` can be realised. -/
lemma base_arcs {Vs T0 C4 : Finset ι} (Cc : Fin 3 → Finset ι) {a b : ι → ι}
    (hT0 : T0 ⊆ U \ Vs) (hC4 : C4 ⊆ U \ Vs) (hCc : ∀ c, Cc c ⊆ U \ Vs)
    (hT0C4 : Disjoint T0 C4) (hT0Cc : ∀ c, Disjoint T0 (Cc c)) (hC4Cc : ∀ c, Disjoint C4 (Cc c))
    (hCcd : ∀ c c', c ≠ c' → Disjoint (Cc c) (Cc c'))
    (ha : ∀ v ∈ Vs, a v ∈ C4 ∧ H.Adj v (a v)) (hb : ∀ v ∈ Vs, b v ∈ C4 ∧ H.Adj v (b v))
    (hainj : ∀ v ∈ Vs, ∀ w ∈ Vs, a v = a w → v = w)
    (hbinj : ∀ v ∈ Vs, ∀ w ∈ Vs, b v = b w → v = w) (hab : ∀ v ∈ Vs, ∀ w ∈ Vs, a v ≠ b w)
    (hlink : ∀ c, LinkProp H (U \ Vs) (Cc c) K)
    (hexp : ∀ X ⊆ T0 ∪ C4, K * X.card ≤ (extNb H (U \ Vs) X ∅).card)
    (Jn : List (ι × ι)) (hlen : 3 ≤ Jn.length) (hnd : (jEntries Jn).Nodup)
    (hent : ∀ v ∈ jEntries Jn, v ∈ Vs ∨ v ∈ T0) :
    ∃ A : List (List ι), List.Forall₂ (ArcOK H U (Vs ∪ T0)) (demands Jn) A ∧
      (A.flatMap arcInner).Nodup ∧ (A.flatMap arcEdges).Nodup := by
  set m := Jn.length with hm
  have hm0 : 0 < m := by omega
  let yv : Fin m → ι := fun i => (Jn[i.val]'i.isLt).2
  let xv : Fin m → ι := fun i => (Jn[(i.val + 1) % m]'(Nat.mod_lt _ hm0)).1
  have hy_ent : ∀ i, yv i ∈ Vs ∨ yv i ∈ T0 := fun i =>
    hent _ (mem_jEntries.2 ⟨_, List.getElem_mem _, Or.inr rfl⟩)
  have hx_ent : ∀ i, xv i ∈ Vs ∨ xv i ∈ T0 := fun i =>
    hent _ (mem_jEntries.2 ⟨_, List.getElem_mem _, Or.inl rfl⟩)
  have hyinj : ∀ i j, yv i = yv j → i = j := fun i j h => Fin.ext (jn_snd_inj hnd _ _ h)
  have hxinj : ∀ i j, xv i = xv j → i = j := by
    intro i j h
    have := jn_fst_inj hnd _ _ h
    rw [succ_mod_eq i.isLt, succ_mod_eq j.isLt] at this
    ext; split_ifs at this <;> omega
  have hyx : ∀ i j, yv i = xv j → i.val = (j.val + 1) % m := fun i j h => jn_snd_fst hnd _ _ h
  have hyx' : ∀ i, yv i ≠ xv i := by
    intro i h
    have := hyx i i h
    rw [succ_mod_eq i.isLt] at this
    split_ifs at this <;> omega
  -- private neighbours
  let dep : ι → ι := fun v => if v ∈ Vs then b v else v
  let arr : ι → ι := fun v => if v ∈ Vs then a v else v
  have hVT : ∀ v, v ∈ T0 → v ∉ Vs := fun v hv => (Finset.mem_sdiff.1 (hT0 hv)).2
  have hVC4 : ∀ v, v ∈ C4 → v ∉ Vs := fun v hv => (Finset.mem_sdiff.1 (hC4 hv)).2
  have hdep_mem : ∀ v, v ∈ Vs ∨ v ∈ T0 → (v ∈ Vs ∧ dep v ∈ C4) ∨ (v ∉ Vs ∧ dep v = v ∧ v ∈ T0) := by
    intro v hv
    by_cases h : v ∈ Vs
    · left; exact ⟨h, by simp only [dep, if_pos h]; exact (hb v h).1⟩
    · right; refine ⟨h, by simp only [dep, if_neg h], hv.resolve_left h⟩
  have harr_mem : ∀ v, v ∈ Vs ∨ v ∈ T0 → (v ∈ Vs ∧ arr v ∈ C4) ∨ (v ∉ Vs ∧ arr v = v ∧ v ∈ T0) := by
    intro v hv
    by_cases h : v ∈ Vs
    · left; exact ⟨h, by simp only [arr, if_pos h]; exact (ha v h).1⟩
    · right; refine ⟨h, by simp only [arr, if_neg h], hv.resolve_left h⟩
  have hdd : ∀ v w, v ∈ Vs ∨ v ∈ T0 → w ∈ Vs ∨ w ∈ T0 → dep v = dep w → v = w := by
    intro v w hv hw h
    by_cases h1 : v ∈ Vs <;> by_cases h2 : w ∈ Vs <;>
      simp only [dep, if_pos, if_neg, h1, h2, not_false_eq_true] at h
    · exact hbinj v h1 w h2 h
    · exact absurd (h ▸ (hb v h1).1) (Finset.disjoint_left.1 hT0C4 (hw.resolve_left h2))
    · exact absurd (h.symm ▸ (hb w h2).1) (Finset.disjoint_left.1 hT0C4 (hv.resolve_left h1))
    · exact h
  have haa : ∀ v w, v ∈ Vs ∨ v ∈ T0 → w ∈ Vs ∨ w ∈ T0 → arr v = arr w → v = w := by
    intro v w hv hw h
    by_cases h1 : v ∈ Vs <;> by_cases h2 : w ∈ Vs <;>
      simp only [arr, if_pos, if_neg, h1, h2, not_false_eq_true] at h
    · exact hainj v h1 w h2 h
    · exact absurd (h ▸ (ha v h1).1) (Finset.disjoint_left.1 hT0C4 (hw.resolve_left h2))
    · exact absurd (h.symm ▸ (ha w h2).1) (Finset.disjoint_left.1 hT0C4 (hv.resolve_left h1))
    · exact h
  have hda : ∀ v w, v ∈ Vs ∨ v ∈ T0 → w ∈ Vs ∨ w ∈ T0 → dep v = arr w → v = w := by
    intro v w hv hw h
    by_cases h1 : v ∈ Vs <;> by_cases h2 : w ∈ Vs <;>
      simp only [dep, arr, if_pos, if_neg, h1, h2, not_false_eq_true] at h
    · exact absurd h.symm (hab w h2 v h1)
    · exact absurd (h ▸ (hb v h1).1) (Finset.disjoint_left.1 hT0C4 (hw.resolve_left h2))
    · exact absurd (h.symm ▸ (ha w h2).1) (Finset.disjoint_left.1 hT0C4 (hv.resolve_left h1))
    · exact h
  let Q : Fin m → ι × ι := fun i => (dep (yv i), arr (xv i))
  let col : Fin m → Fin 3 := fun i => ⟨dcol m i, dcol_lt m i⟩
  have hcolne : ∀ i j : Fin m, i.val = (j.val + 1) % m → col i ≠ col j := by
    intro i j h hc
    exact dcol_ne hlen j.isLt h (congrArg Fin.val hc).symm
  have hQmem : ∀ i, ((Q i).1 ∈ C4 ∨ (Q i).1 ∈ T0) ∧ ((Q i).2 ∈ C4 ∨ (Q i).2 ∈ T0) := by
    intro i
    refine ⟨?_, ?_⟩
    · rcases hdep_mem _ (hy_ent i) with ⟨-, h⟩ | ⟨-, h, h'⟩
      · exact Or.inl h
      · exact Or.inr (by simp only [Q]; rw [h]; exact h')
    · rcases harr_mem _ (hx_ent i) with ⟨-, h⟩ | ⟨-, h, h'⟩
      · exact Or.inl h
      · exact Or.inr (by simp only [Q]; rw [h]; exact h')
  have hmemCc : ∀ v c, v ∈ C4 ∨ v ∈ T0 → v ∈ U \ Vs ∧ v ∉ Cc c := by
    intro v c hv
    rcases hv with hv | hv
    · exact ⟨hC4 hv, Finset.disjoint_left.1 (hC4Cc c) hv⟩
    · exact ⟨hT0 hv, Finset.disjoint_left.1 (hT0Cc c) hv⟩
  obtain ⟨P, hP, hPd⟩ := three_colour_paths (H := H) (U := U \ Vs) (K := K) col Q Cc hlink
    (fun i j hij hc => ⟨fun h => hij (hyinj i j (hdd _ _ (hy_ent i) (hy_ent j) h)),
      fun h => hij (hxinj i j (haa _ _ (hx_ent i) (hx_ent j) h)),
      fun h => hcolne i j (hyx i j (hda _ _ (hy_ent i) (hx_ent j) h)) hc⟩)
    (fun i h => hyx' i (hda _ _ (hy_ent i) (hx_ent i) h))
    (fun i => ⟨Finset.mem_sdiff.2 ⟨(hmemCc _ (col i) (hQmem i).1).1, (hmemCc _ (col i) (hQmem i).1).2⟩,
      Finset.mem_sdiff.2 ⟨(hmemCc _ (col i) (hQmem i).2).1, (hmemCc _ (col i) (hQmem i).2).2⟩⟩)
    (fun X hX => hexp X fun x hx => by
      obtain ⟨i, h | h⟩ := hX x hx
      · rw [h, Finset.mem_union]; exact (hQmem i).1.symm
      · rw [h, Finset.mem_union]; exact (hQmem i).2.symm)
  let pre : Fin m → List ι := fun i => if yv i ∈ Vs then [yv i] else []
  let suf : Fin m → List ι := fun i => if xv i ∈ Vs then [xv i] else []
  let arc : Fin m → List ι := fun i => pre i ++ P i ++ suf i
  have hPmem : ∀ i v, v ∈ P i → v = dep (yv i) ∨ v = arr (xv i) ∨ v ∈ Cc (col i) :=
    fun i v hv => (hP i).2 v hv
  have hCcVs : ∀ c v, v ∈ Cc c → v ∉ Vs := fun c v hv => (Finset.mem_sdiff.1 (hCc c hv)).2
  have harc_mem : ∀ i v, v ∈ arc i →
      (yv i ∈ Vs ∧ v = yv i) ∨ v ∈ P i ∨ (xv i ∈ Vs ∧ v = xv i) := by
    intro i v hv
    simp only [arc, pre, suf, List.mem_append] at hv
    rcases hv with (hv | hv) | hv
    · split_ifs at hv with h
      · exact Or.inl ⟨h, List.mem_singleton.1 hv⟩
      · simp at hv
    · exact Or.inr (Or.inl hv)
    · split_ifs at hv with h
      · exact Or.inr (Or.inr ⟨h, List.mem_singleton.1 hv⟩)
      · simp at hv
  have hyP : ∀ i, yv i ∈ Vs → yv i ∉ P i := by
    intro i hy hv
    rcases hPmem i _ hv with h | h | h
    · simp only [dep, if_pos hy] at h
      exact hVC4 _ (h ▸ (hb _ hy).1) hy
    · by_cases hx : xv i ∈ Vs
      · simp only [arr, if_pos hx] at h
        exact hVC4 _ (h ▸ (ha _ hx).1) hy
      · simp only [arr, if_neg hx] at h
        exact hyx' i h
    · exact hCcVs _ _ h hy
  have hxP : ∀ i, xv i ∈ Vs → xv i ∉ P i := by
    intro i hx hv
    rcases hPmem i _ hv with h | h | h
    · by_cases hy : yv i ∈ Vs
      · simp only [dep, if_pos hy] at h
        exact hVC4 _ (h ▸ (hb _ hy).1) hx
      · simp only [dep, if_neg hy] at h
        exact hyx' i h.symm
    · simp only [arr, if_pos hx] at h
      exact hVC4 _ (h ▸ (ha _ hx).1) hx
    · exact hCcVs _ _ h hx
  have harc_nd : ∀ i, (arc i).Nodup := by
    intro i
    have hPnd := (hP i).1.2.2.2
    simp only [arc, pre, suf]
    rw [List.nodup_append, List.nodup_append]
    refine ⟨⟨by split_ifs <;> simp, hPnd, ?_⟩, by split_ifs <;> simp, ?_⟩
    · intro u hu w hw huw
      split_ifs at hu with h
      · rw [List.mem_singleton] at hu; subst hu; exact hyP i h (huw ▸ hw)
      · simp at hu
    · intro u hu w hw huw
      split_ifs at hw with h
      · rw [List.mem_singleton] at hw; subst hw
        rw [List.mem_append] at hu
        rcases hu with hu | hu
        · split_ifs at hu with h'
          · rw [List.mem_singleton] at hu; exact hyx' i (hu ▸ huw)
          · simp at hu
        · exact hxP i h (huw ▸ hu)
      · simp at hw
  have harc_head : ∀ i, (arc i).head? = some (yv i) := by
    intro i
    refine arc_head (hP i).1.1 ?_
    by_cases h : yv i ∈ Vs
    · right; simp only [pre, if_pos h]
    · left; simp only [pre, if_neg h, Q, dep, true_and]
  have harc_last : ∀ i, (arc i).getLast? = some (xv i) := by
    intro i
    refine arc_last (hP i).1.2.1 ?_
    by_cases h : xv i ∈ Vs
    · right; simp only [suf, if_pos h]
    · left; simp only [suf, if_neg h, Q, arr, true_and]
  have harc_chain : ∀ i, (arc i).IsChain H.Adj := by
    intro i
    have hPc := (hP i).1.2.2.1
    refine List.IsChain.append (List.IsChain.append ?_ hPc ?_) ?_ ?_
    · simp only [pre]; split_ifs <;> simp
    · intro x hx y hy
      simp only [pre] at hx
      split_ifs at hx with h
      · simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hx
        rw [(hP i).1.1, Option.mem_def, Option.some.injEq] at hy
        subst hx hy
        simp only [Q, dep, if_pos h]; exact (hb _ h).2
      · simp at hx
    · simp only [suf]; split_ifs <;> simp
    · intro x hx y hy
      simp only [suf] at hy
      split_ifs at hy with h
      · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
        rw [List.getLast?_append] at hx
        rw [(hP i).1.2.1] at hx
        simp only [Option.some_or, Option.mem_def, Option.some.injEq] at hx
        subst hx hy
        simp only [Q, arr, if_pos h]; exact (ha _ h).2.symm
      · simp at hy
  have harc_len : ∀ i, 2 ≤ (arc i).length :=
    fun i => two_le_length_of_ne (harc_head i) (harc_last i) (hyx' i)
  have hinner : ∀ i v, v ∈ arcInner (arc i) →
      (v ∈ C4 ∧ (v = dep (yv i) ∨ v = arr (xv i))) ∨ (v ∈ Cc (col i) ∧ v ∈ P i) := by
    intro i v hv
    obtain ⟨hvy, hvx⟩ := notMem_inner_of_nodup (harc_head i) (harc_last i) (harc_nd i) hv
    rcases harc_mem i v (inner_subset _ hv) with ⟨-, h⟩ | hvP | ⟨-, h⟩
    · exact absurd h hvy
    · rcases hPmem i v hvP with h | h | h
      · by_cases hy : yv i ∈ Vs
        · left; refine ⟨?_, Or.inl h⟩
          rw [h]; simp only [dep, if_pos hy]; exact (hb _ hy).1
        · simp only [dep, if_neg hy] at h; exact absurd h hvy
      · by_cases hx : xv i ∈ Vs
        · left; refine ⟨?_, Or.inr h⟩
          rw [h]; simp only [arr, if_pos hx]; exact (ha _ hx).1
        · simp only [arr, if_neg hx] at h; exact absurd h hvx
      · exact Or.inr ⟨h, hvP⟩
    · exact absurd h hvx
  have hinner_mem : ∀ i v, v ∈ arcInner (arc i) → v ∈ U ∧ v ∉ Vs ∪ T0 := by
    intro i v hv
    rcases hinner i v hv with ⟨h, -⟩ | ⟨h, -⟩
    · refine ⟨(Finset.mem_sdiff.1 (hC4 h)).1, ?_⟩
      rw [Finset.mem_union, not_or]
      exact ⟨hVC4 v h, fun h' => Finset.disjoint_left.1 hT0C4 h' h⟩
    · refine ⟨(Finset.mem_sdiff.1 (hCc _ h)).1, ?_⟩
      rw [Finset.mem_union, not_or]
      exact ⟨hCcVs _ v h, fun h' => Finset.disjoint_left.1 (hT0Cc _) h' h⟩
  have hdisj : ∀ i j, i ≠ j → List.Disjoint (arcInner (arc i)) (arcInner (arc j)) := by
    intro i j hij v hvi hvj
    rcases hinner i v hvi with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
      rcases hinner j v hvj with ⟨h2, h2'⟩ | ⟨h2, h2'⟩
    · have hyi := hy_ent i; have hyj := hy_ent j; have hxi := hx_ent i; have hxj := hx_ent j
      rcases h1' with h1' | h1' <;> rcases h2' with h2' | h2'
      · exact hij (hyinj i j (hdd _ _ hyi hyj (h1'.symm.trans h2')))
      · rcases hdep_mem _ hyi with ⟨hy, -⟩ | ⟨hy, hd, hT⟩
        · rcases harr_mem _ hxj with ⟨hx, -⟩ | ⟨hx, hd', hT'⟩
          · simp only [dep, arr, if_pos hy, if_pos hx] at h1' h2'
            exact hab _ hx _ hy (h2'.symm.trans h1')
          · rw [hd'] at h2'; exact Finset.disjoint_left.1 hT0C4 (h2' ▸ hT') h1
        · rw [hd] at h1'; exact Finset.disjoint_left.1 hT0C4 (h1' ▸ hT) h1
      · rcases hdep_mem _ hyj with ⟨hy, -⟩ | ⟨hy, hd, hT⟩
        · rcases harr_mem _ hxi with ⟨hx, -⟩ | ⟨hx, hd', hT'⟩
          · simp only [dep, arr, if_pos hy, if_pos hx] at h1' h2'
            exact hab _ hx _ hy (h1'.symm.trans h2')
          · rw [hd'] at h1'; exact Finset.disjoint_left.1 hT0C4 (h1' ▸ hT') h1
        · rw [hd] at h2'; exact Finset.disjoint_left.1 hT0C4 (h2' ▸ hT) h1
      · exact hij (hxinj i j (haa _ _ hxi hxj (h1'.symm.trans h2')))
    · exact Finset.disjoint_left.1 (hC4Cc _) h1 h2
    · exact Finset.disjoint_left.1 (hC4Cc _) h2 h1
    · have hc : col i = col j := by
        by_contra hc; exact Finset.disjoint_left.1 (hCcd _ _ hc) h1 h2
      exact hPd i j hij hc h1' h2'
  have hedge : ∀ i j, i ≠ j → List.Disjoint (arcEdges (arc i)) (arcEdges (arc j)) := by
    intro i j hij e hei hej
    induction e using Sym2.ind with
    | h u w =>
    have hadj := arcEdges_adj (harc_chain i) hei
    have hui := mem_of_mem_arcEdges hei
    have huj := mem_of_mem_arcEdges hej
    have hent_i : ∀ z, z ∈ arc i → z ∈ arc j → z = yv i ∨ z = xv i := by
      intro z hzi hzj
      rcases (mem_iff_inner (harc_head i) (harc_last i) (harc_len i)).1 hzi with h | h | h
      · exact Or.inl h
      · exfalso
        rcases (mem_iff_inner (harc_head j) (harc_last j) (harc_len j)).1 hzj with h' | h' | h'
        · exact (hinner_mem i z h).2 (Finset.mem_union.2 (h' ▸ hy_ent j))
        · exact hdisj i j hij h h'
        · exact (hinner_mem i z h).2 (Finset.mem_union.2 (h' ▸ hx_ent j))
      · exact Or.inr h
    have hent_j : ∀ z, z ∈ arc i → z ∈ arc j → z = yv j ∨ z = xv j := by
      intro z hzi hzj
      rcases (mem_iff_inner (harc_head j) (harc_last j) (harc_len j)).1 hzj with h | h | h
      · exact Or.inl h
      · exfalso
        rcases (mem_iff_inner (harc_head i) (harc_last i) (harc_len i)).1 hzi with h' | h' | h'
        · exact (hinner_mem j z h).2 (Finset.mem_union.2 (h' ▸ hy_ent i))
        · exact hdisj i j hij h' h
        · exact (hinner_mem j z h).2 (Finset.mem_union.2 (h' ▸ hx_ent i))
      · exact Or.inr h
    have hu1 := hent_i u hui.1 huj.1
    have hu2 := hent_j u hui.1 huj.1
    have hw1 := hent_i w hui.2 huj.2
    have hw2 := hent_j w hui.2 huj.2
    have huw : u ≠ w := hadj.ne
    have key : ∀ p q : Fin m, p.val = (q.val + 1) % m → q.val = (p.val + 1) % m → False := by
      intro p q h1 h2
      rw [succ_mod_eq q.isLt] at h1; rw [succ_mod_eq p.isLt] at h2
      split_ifs at h1 h2 <;> omega
    rcases hu1 with rfl | rfl <;> rcases hw1 with rfl | rfl
    · exact huw rfl
    · rcases hu2 with h | h
      · exact hij (hyinj _ _ h)
      · rcases hw2 with h' | h'
        · exact key i j (hyx _ _ h) (hyx _ _ h'.symm)
        · exact huw (h.trans h'.symm)
    · rcases hu2 with h | h
      · rcases hw2 with h' | h'
        · exact huw (h.trans h'.symm)
        · exact key j i (hyx _ _ h.symm) (hyx _ _ h')
      · exact hij (hxinj _ _ h)
    · exact huw rfl
  refine ⟨List.ofFn arc, ?_, ?_, ?_⟩
  · rw [List.forall₂_iff_get]
    refine ⟨by rw [demands_length, List.length_ofFn], fun k h1 h2 => ?_⟩
    have hk : k < m := by rwa [demands_length] at h1
    simp only [List.get_eq_getElem, List.getElem_ofFn]
    rw [demands_getElem]
    exact ⟨harc_head ⟨k, hk⟩, harc_last ⟨k, hk⟩, harc_chain _, harc_len _,
      fun v hv => hinner_mem _ v hv⟩
  · rw [List.nodup_flatMap]
    refine ⟨fun l hl => ?_, ?_⟩
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hl
      exact inner_nodup (harc_nd i)
    · rw [List.pairwise_ofFn]
      exact fun i j hij => hdisj i j hij.ne
  · rw [List.nodup_flatMap]
    refine ⟨fun l hl => ?_, ?_⟩
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hl
      exact arcEdges_nodup (harc_nd i)
    · rw [List.pairwise_ofFn]
      exact fun i j hij => hedge i j hij.ne

end base2

section glue

variable {H : SimpleGraph ι} {U B : Finset ι}

/-- Concatenation of arcs sharing endpoints. -/
def glueArcs : List (List ι) → List ι
  | [] => []
  | [P] => P
  | P :: Q :: Ps => P.dropLast ++ glueArcs (Q :: Ps)

lemma arcEdges_append_cons (l T : List ι) (z : ι) :
    arcEdges (l ++ z :: T) = arcEdges (l ++ [z]) ++ arcEdges (z :: T) := by
  induction l with
  | nil => simp [arcEdges]
  | cons a l ih =>
    cases l with
    | nil => simp [arcEdges]
    | cons b l =>
      have e1 : ∀ M : List ι, arcEdges (a :: b :: M) = s(a, b) :: arcEdges (b :: M) := by
        intro M; simp [arcEdges]
      simp only [List.cons_append] at ih ⊢
      rw [e1, e1, ih]; rfl

lemma glue_spec (zs : List ι) : ∀ (y x : ι) (As : List (List ι)),
    List.Forall₂ (ArcOK H U B) (List.zip (y :: zs) (zs ++ [x])) As →
    (glueArcs As).head? = some y ∧ (glueArcs As).getLast? = some x ∧
      (glueArcs As).IsChain H.Adj ∧ zs.length + 2 ≤ (glueArcs As).length ∧
      (arcInner (glueArcs As)).Perm (As.flatMap arcInner ++ zs) ∧
      arcEdges (glueArcs As) = As.flatMap arcEdges := by
  induction zs with
  | nil =>
    intro y x As hF
    simp only [List.nil_append, List.zip_cons_cons, List.zip_nil_left] at hF
    obtain ⟨P, rfl⟩ : ∃ P, As = [P] := by
      rcases hF with _ | ⟨h, hF'⟩; cases hF'; exact ⟨_, rfl⟩
    rcases hF with _ | ⟨⟨h1, h2, h3, h4, -⟩, -⟩
    refine ⟨h1, h2, h3, by simpa only [show glueArcs [P] = P from rfl,
      List.length_nil, zero_add] using h4, ?_, ?_⟩
    · rw [show glueArcs [P] = P from rfl]; simp
    · rw [show glueArcs [P] = P from rfl]; simp
  | cons z zs ih =>
    intro y x As hF
    simp only [List.cons_append, List.zip_cons_cons] at hF
    rcases hF with _ | ⟨hP, hF'⟩
    rename_i P As'
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := ih z x As' hF'
    obtain ⟨h1, h2, h3, h4, -⟩ := hP
    have hAs' : As' ≠ [] := by rintro rfl; simp [glueArcs] at g1
    have hglue : glueArcs (P :: As') = P.dropLast ++ glueArcs As' := by
      obtain ⟨Q, Qs, rfl⟩ := List.exists_cons_of_ne_nil hAs'
      rfl
    obtain ⟨P0, rfl⟩ := List.getLast?_eq_some_iff.1 h2
    obtain ⟨T, hT⟩ := List.head?_eq_some_iff.1 g1
    rw [hglue, List.dropLast_concat, hT]
    rw [hT] at g2 g3 g4 g5 g6
    have hP0 : P0 ≠ [] := by rintro rfl; simp at h4
    obtain ⟨y', P0', rfl⟩ := List.exists_cons_of_ne_nil hP0
    simp only [List.cons_append, List.head?_cons, Option.some.injEq] at h1
    subst h1
    have hT0 : T ≠ [] := by rintro rfl; simp at g4
    refine ⟨by simp, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.getLast?_append, g2]; rfl
    · rw [List.isChain_append]
      refine ⟨?_, g3, ?_⟩
      · exact (List.isChain_append.1 h3).1
      · intro a ha b hb
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
        subst hb
        exact (List.isChain_append.1 h3).2.2 a ha z (by simp)
    · simp only [List.length_append, List.length_cons] at g4 ⊢; omega
    · simp only [arcInner, List.cons_append, List.tail_cons] at g5 ⊢
      rw [List.dropLast_append_of_ne_nil (by simp), List.dropLast_cons_of_ne_nil hT0]
      simp only [List.flatMap_cons, arcInner, List.tail_cons,
        List.dropLast_concat, List.append_assoc]
      refine List.Perm.append_left _ ?_
      refine ((List.Perm.cons z g5).trans ?_)
      simp only [arcInner] at *
      exact List.perm_middle.symm
    · rw [List.flatMap_cons, ← g6]; exact arcEdges_append_cons (y' :: P0') T z

end glue

section subdiv

variable {H : SimpleGraph ι} {U B : Finset ι}

lemma demands_cons (a : ι × ι) (L : List (ι × ι)) :
    demands (a :: L) = List.zipWith (fun p q => (p.2, q.1)) (a :: L) (L ++ [a]) := by
  simp [demands]

lemma zipWith_dup (zs : List ι) : ∀ (a h : ι × ι),
    List.zipWith (fun p q => (p.2, q.1)) (a :: zs.map (fun z => (z, z)))
      (zs.map (fun z => (z, z)) ++ [h]) = List.zip (a.2 :: zs) (zs ++ [h.1]) := by
  induction zs with
  | nil => intro a h; simp
  | cons z zs ih =>
    intro a h
    simp only [List.map_cons, List.cons_append, List.zipWith_cons_cons, List.zip_cons_cons]
    rw [ih (z, z) h]

lemma demands_subdiv (j0 : ι × ι) (zs : List ι) (rest : List (ι × ι)) :
    demands (j0 :: (zs.map (fun z => (z, z)) ++ rest)) =
      List.zip (j0.2 :: zs) (zs ++ [((rest ++ [j0]).head (by simp)).1]) ++
        (demands (j0 :: rest)).tail ∧
    (demands (j0 :: rest)).head? = some (j0.2, ((rest ++ [j0]).head (by simp)).1) := by
  set h := (rest ++ [j0]).head (by simp)
  obtain ⟨t, ht⟩ : ∃ t, rest ++ [j0] = h :: t := ⟨(rest ++ [j0]).tail, by simp [h]⟩
  rw [demands_cons, demands_cons]
  constructor
  · rw [List.append_assoc, ht, show zs.map (fun z => (z, z)) ++ h :: t =
      (zs.map (fun z => (z, z)) ++ [h]) ++ t by simp, ← List.cons_append,
      List.zipWith_append (by simp), zipWith_dup]
    simp
  · rw [ht]; simp

lemma forall₂_mem_right {α β : Type*} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) {b : β} (hb : b ∈ l₂) : ∃ a ∈ l₁, R a b := by
  induction h with
  | nil => simp at hb
  | cons hab _ ih =>
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨_, List.mem_cons_self .., hab⟩
    · obtain ⟨a, ha, h⟩ := ih hb; exact ⟨a, List.mem_cons_of_mem _ ha, h⟩

lemma ArcOK.mono {d : ι × ι} {P : List ι} {B' : Finset ι} (h : ArcOK H U B d P) (hB : B' ⊆ B) :
    ArcOK H U B' d P :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun v hv => ⟨(h.2.2.2.2 v hv).1,
    fun h' => (h.2.2.2.2 v hv).2 (hB h')⟩⟩

/-- Subdividing the first demand through the vertices `zs` (Lemma 2.6, the colour-5 vertices):
gluing the corresponding arcs produces a long first arc. -/
lemma subdivide_arcs (zs : List ι) (hzs : zs.Nodup) (hzB : ∀ z ∈ zs, z ∈ B)
    (hzU : ∀ z ∈ zs, z ∈ U) (j0 : ι × ι) (rest : List (ι × ι)) (A' : List (List ι))
    (hF : List.Forall₂ (ArcOK H U B) (demands (j0 :: (zs.map (fun z => (z, z)) ++ rest))) A')
    (hin : (A'.flatMap arcInner).Nodup) (hed : (A'.flatMap arcEdges).Nodup) :
    ∃ A : List (List ι), List.Forall₂ (ArcOK H U (B \ zs.toFinset)) (demands (j0 :: rest)) A ∧
      (A.flatMap arcInner).Nodup ∧ (A.flatMap arcEdges).Nodup ∧
      ∃ P ∈ A, (zs.length : ℝ) + 1 ≤ (P.length : ℝ) - 1 := by
  obtain ⟨e1, e2⟩ := demands_subdiv j0 zs rest
  set x := ((rest ++ [j0]).head (by simp)).1
  rw [e1] at hF
  set k := zs.length + 1
  have hk : (List.zip (j0.2 :: zs) (zs ++ [x])).length = k := by simp [k]
  have hF1 := List.forall₂_take k hF
  have hF2 := List.forall₂_drop k hF
  rw [← hk, List.take_left] at hF1
  rw [← hk, List.drop_left] at hF2
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := glue_spec zs j0.2 x _ hF1
  set As := A'.take (List.zip (j0.2 :: zs) (zs ++ [x])).length
  set Ar := A'.drop (List.zip (j0.2 :: zs) (zs ++ [x])).length
  have hA' : A' = As ++ Ar := (List.take_append_drop _ _).symm
  have hinner_B : ∀ v ∈ A'.flatMap arcInner, v ∉ B := by
    intro v hv
    obtain ⟨P, hP, hvP⟩ := List.mem_flatMap.1 hv
    obtain ⟨d, -, hd⟩ := forall₂_mem_right hF hP
    exact (hd.2.2.2.2 v hvP).2
  refine ⟨glueArcs As :: Ar, ?_, ?_, ?_, ⟨_, List.mem_cons_self .., ?_⟩⟩
  · obtain ⟨d0, dt, hd⟩ : ∃ d0 dt, demands (j0 :: rest) = d0 :: dt := by
      rcases hdem : demands (j0 :: rest) with _ | ⟨d0, dt⟩
      · rw [hdem] at e2; simp at e2
      · exact ⟨d0, dt, rfl⟩
    rw [hd] at e2 hF2 ⊢
    simp only [List.head?_cons, Option.some.injEq] at e2
    simp only [List.tail_cons] at hF2
    refine List.Forall₂.cons ?_ (hF2.imp fun _ _ h => h.mono Finset.sdiff_subset)
    subst e2
    refine ⟨g1, g2, g3, by omega, fun v hv => ?_⟩
    have hv' := g5.subset hv
    rw [List.mem_append] at hv'
    rcases hv' with hv' | hv'
    · obtain ⟨P, hP, hvP⟩ := List.mem_flatMap.1 hv'
      obtain ⟨d, -, hd⟩ := forall₂_mem_right hF1 hP
      exact ⟨(hd.2.2.2.2 v hvP).1, fun h => (hd.2.2.2.2 v hvP).2 (Finset.mem_sdiff.1 h).1⟩
    · exact ⟨hzU v hv', fun h => (Finset.mem_sdiff.1 h).2 (List.mem_toFinset.2 hv')⟩
  · rw [List.flatMap_cons]
    have hp : (arcInner (glueArcs As) ++ Ar.flatMap arcInner).Perm
        (A'.flatMap arcInner ++ zs) := by
      rw [hA', List.flatMap_append]
      refine (List.Perm.append_right _ g5).trans ?_
      rw [List.append_assoc, List.append_assoc]
      exact List.Perm.append_left _ List.perm_append_comm
    rw [hp.nodup_iff, List.nodup_append]
    exact ⟨hin, hzs, fun a ha b hb hab => hinner_B a ha (hab ▸ hzB b hb)⟩
  · rw [List.flatMap_cons, g6, ← List.flatMap_append, ← hA']; exact hed
  · have : (zs.length + 2 : ℝ) ≤ (glueArcs As).length := by exact_mod_cast g4
    linarith

end subdiv

section event

variable {H : SimpleGraph ι} {U : Finset ι} {K : ℝ}

lemma ArcOK.mono' {d : ι × ι} {P : List ι} {B B' : Finset ι} (h : ArcOK H U B d P)
    (hB : ∀ v ∈ U, v ∈ B' → v ∈ B) : ArcOK H U B' d P :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun v hv => ⟨(h.2.2.2.2 v hv).1,
    fun h' => (h.2.2.2.2 v hv).2 (hB v (h.2.2.2.2 v hv).1 h')⟩⟩

lemma jEntries_dup (zs : List ι) : jEntries (zs.map (fun z => (z, z))) = zs := by
  induction zs with
  | nil => rfl
  | cons z zs ih => simp only [List.map_cons, jEntries, List.flatMap_cons, if_pos] at ih ⊢; rw [ih]; rfl

/-- The deterministic part of Lemma 2.6. -/
lemma linkEvent_of {Vs Y C4 C5 : Finset ι} (Cc : Fin 3 → Finset ι) {a b : ι → ι} {bound : ℝ}
    (hC5 : C5 ⊆ U \ Vs) (hC4 : C4 ⊆ U \ Vs) (hCc : ∀ c, Cc c ⊆ U \ Vs)
    (hC5Y : Disjoint C5 Y) (hC4Y : Disjoint C4 Y) (hCcY : ∀ c, Disjoint (Cc c) Y)
    (hC45 : Disjoint C5 C4) (hC5Cc : ∀ c, Disjoint C5 (Cc c)) (hC4Cc : ∀ c, Disjoint C4 (Cc c))
    (hCcd : ∀ c c', c ≠ c' → Disjoint (Cc c) (Cc c'))
    (ha : ∀ v ∈ Vs, a v ∈ C4 ∧ H.Adj v (a v)) (hb : ∀ v ∈ Vs, b v ∈ C4 ∧ H.Adj v (b v))
    (hainj : ∀ v ∈ Vs, ∀ w ∈ Vs, a v = a w → v = w)
    (hbinj : ∀ v ∈ Vs, ∀ w ∈ Vs, b v = b w → v = w) (hab : ∀ v ∈ Vs, ∀ w ∈ Vs, a v ≠ b w)
    (hlink : ∀ c, LinkProp H (U \ Vs) (Cc c) K)
    (hexp : ∀ X ⊆ ((Y ∩ U) \ Vs ∪ C5) ∪ C4, K * X.card ≤ (extNb H (U \ Vs) X ∅).card)
    (hC5card : 2 ≤ C5.card) (hbound : bound ≤ C5.card + 1) :
    LinkEvent H U Vs Y bound := by
  intro Jn hJn hnd hent
  obtain ⟨j0, rest, rfl⟩ := List.exists_cons_of_ne_nil hJn
  set T0 := (Y ∩ U) \ Vs ∪ C5 with hT0
  set zs := C5.toList
  have hzs : zs.Nodup := Finset.nodup_toList _
  have hzmem : ∀ z, z ∈ zs ↔ z ∈ C5 := fun z => Finset.mem_toList
  have hent' : ∀ v ∈ jEntries (j0 :: (zs.map (fun z => (z, z)) ++ rest)), v ∈ Vs ∨ v ∈ T0 := by
    intro v hv
    simp only [jEntries, List.flatMap_cons, List.flatMap_append, List.mem_append] at hv
    rw [← jEntries, jEntries_dup, ← jEntries] at hv
    have hv' : v ∈ jEntries (j0 :: rest) ∨ v ∈ zs := by
      simp only [jEntries, List.flatMap_cons, List.mem_append] at hv ⊢; tauto
    rcases hv' with hv' | hv'
    · obtain ⟨hvU, hv'⟩ := hent v hv'
      by_cases h : v ∈ Vs
      · exact Or.inl h
      · right; rw [hT0, Finset.mem_union]; left
        exact Finset.mem_sdiff.2 ⟨Finset.mem_inter.2 ⟨hv'.resolve_left h, hvU⟩, h⟩
    · exact Or.inr (Finset.mem_union_right _ ((hzmem v).1 hv'))
  have hnd' : (jEntries (j0 :: (zs.map (fun z => (z, z)) ++ rest))).Nodup := by
    have hp : (jEntries (j0 :: (zs.map (fun z => (z, z)) ++ rest))).Perm
        (jEntries (j0 :: rest) ++ zs) := by
      simp only [jEntries, List.flatMap_cons, List.flatMap_append]
      rw [← jEntries, jEntries_dup, ← jEntries, List.append_assoc]
      exact List.Perm.append_left _ List.perm_append_comm
    rw [hp.nodup_iff, List.nodup_append]
    refine ⟨hnd, hzs, fun u hu w hw huw => ?_⟩
    subst huw
    have hwC5 := (hzmem u).1 hw
    rcases (hent u hu).2 with h | h
    · exact (Finset.mem_sdiff.1 (hC5 hwC5)).2 h
    · exact Finset.disjoint_left.1 hC5Y hwC5 h
  have hlen : 3 ≤ (j0 :: (zs.map (fun z => (z, z)) ++ rest)).length := by
    simp only [List.length_cons, List.length_append, List.length_map, zs, Finset.length_toList]
    omega
  have hVY : ∀ v, v ∈ (Y ∩ U) \ Vs → v ∈ Y := fun v hv =>
    (Finset.mem_inter.1 (Finset.mem_sdiff.1 hv).1).1
  obtain ⟨A', hF, hin, hed⟩ := base_arcs (H := H) (U := U) (K := K) (Vs := Vs) (T0 := T0)
    (C4 := C4) Cc
    (Finset.union_subset (fun v hv => Finset.mem_sdiff.2
      ⟨(Finset.mem_inter.1 (Finset.mem_sdiff.1 hv).1).2, (Finset.mem_sdiff.1 hv).2⟩) hC5)
    hC4 hCc
    (Finset.disjoint_union_left.2 ⟨Finset.disjoint_left.2 fun v hv hv4 =>
      Finset.disjoint_left.1 hC4Y hv4 (hVY v hv), hC45⟩)
    (fun c => Finset.disjoint_union_left.2 ⟨Finset.disjoint_left.2 fun v hv hvc =>
      Finset.disjoint_left.1 (hCcY c) hvc (hVY v hv), hC5Cc c⟩)
    hC4Cc hCcd ha hb hainj hbinj hab hlink hexp _ hlen hnd' hent'
  obtain ⟨A, hA, hAin, hAed, P, hP, hPl⟩ := subdivide_arcs zs hzs
    (fun z hz => Finset.mem_union_right _ (Finset.mem_union_right _ ((hzmem z).1 hz)))
    (fun z hz => (Finset.mem_sdiff.1 (hC5 ((hzmem z).1 hz))).1) j0 rest A' hF hin hed
  refine ⟨A, hA.imp fun d P h => h.mono' fun v hvU hv => ?_, hAin, hAed, P, hP, ?_⟩
  · have : (zs.length : ℝ) = C5.card := by simp [zs]
    linarith
  · rw [Finset.mem_sdiff, Finset.mem_union]
    rcases Finset.mem_union.1 hv with hv | hv
    · exact ⟨Or.inl hv, fun h => (Finset.mem_sdiff.1 (hC5 ((hzmem v).1 (List.mem_toFinset.1 h)))).2 hv⟩
    · by_cases hVs : v ∈ Vs
      · exact ⟨Or.inl hVs, fun h => (Finset.mem_sdiff.1 (hC5 ((hzmem v).1 (List.mem_toFinset.1 h)))).2 hVs⟩
      · exact ⟨Or.inr (Finset.mem_union_left _ (Finset.mem_sdiff.2
          ⟨Finset.mem_inter.2 ⟨hv, hvU⟩, hVs⟩)),
          fun h => Finset.disjoint_left.1 hC5Y ((hzmem v).1 (List.mem_toFinset.1 h)) hv⟩

end event

section helpers

variable {H : SimpleGraph ι}

/-- Greedy choice of two private neighbours for every vertex of `Vs`. -/
lemma private_nbrs (Vs : Finset ι) (N : ι → Finset ι)
    (hN : ∀ v ∈ Vs, 2 * Vs.card ≤ (N v).card) :
    ∃ a b : ι → ι, (∀ v ∈ Vs, a v ∈ N v ∧ b v ∈ N v) ∧
      (∀ v ∈ Vs, ∀ w ∈ Vs, a v = a w → v = w) ∧ (∀ v ∈ Vs, ∀ w ∈ Vs, b v = b w → v = w) ∧
      (∀ v ∈ Vs, ∀ w ∈ Vs, a v ≠ b w) := by
  suffices h : ∀ S ⊆ Vs, ∃ a b : ι → ι, (∀ v ∈ S, a v ∈ N v ∧ b v ∈ N v) ∧
      (∀ v ∈ S, ∀ w ∈ S, a v = a w → v = w) ∧ (∀ v ∈ S, ∀ w ∈ S, b v = b w → v = w) ∧
      (∀ v ∈ S, ∀ w ∈ S, a v ≠ b w) from h Vs (Finset.Subset.refl _)
  intro S
  induction S using Finset.induction_on with
  | empty => intro _; exact ⟨id, id, by simp, by simp, by simp, by simp⟩
  | insert v S hv ih =>
    intro hS
    obtain ⟨a, b, h1, h2, h3, h4⟩ := ih ((Finset.subset_insert _ _).trans hS)
    have hvVs : v ∈ Vs := hS (Finset.mem_insert_self _ _)
    have hused : (S.image a ∪ S.image b).card ≤ 2 * S.card := by
      have := Finset.card_union_le (S.image a) (S.image b)
      have := Finset.card_image_le (s := S) (f := a)
      have := Finset.card_image_le (s := S) (f := b)
      omega
    have hSc : S.card + 1 ≤ Vs.card := by
      have := Finset.card_le_card hS; rw [Finset.card_insert_of_notMem hv] at this; exact this
    have hfree : 2 ≤ (N v \ (S.image a ∪ S.image b)).card := by
      have := Finset.le_card_sdiff (S.image a ∪ S.image b) (N v)
      have := hN v hvVs
      omega
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.1 (by omega : 1 < (N v \ (S.image a ∪ S.image b)).card)
    have hpu := (Finset.mem_sdiff.1 hp).2
    have hqu := (Finset.mem_sdiff.1 hq).2
    have hpa : ∀ w ∈ S, a w ≠ p := fun w hw h => hpu (Finset.mem_union_left _ (h ▸ Finset.mem_image_of_mem a hw))
    have hpb : ∀ w ∈ S, b w ≠ p := fun w hw h => hpu (Finset.mem_union_right _ (h ▸ Finset.mem_image_of_mem b hw))
    have hqa : ∀ w ∈ S, a w ≠ q := fun w hw h => hqu (Finset.mem_union_left _ (h ▸ Finset.mem_image_of_mem a hw))
    have hqb : ∀ w ∈ S, b w ≠ q := fun w hw h => hqu (Finset.mem_union_right _ (h ▸ Finset.mem_image_of_mem b hw))
    have hvS : ∀ w ∈ S, w ≠ v := fun w hw h => hv (h ▸ hw)
    refine ⟨Function.update a v p, Function.update b v q, ?_, ?_, ?_, ?_⟩
    · intro w hw
      rcases Finset.mem_insert.1 hw with rfl | hw
      · simp [(Finset.mem_sdiff.1 hp).1, (Finset.mem_sdiff.1 hq).1]
      · simp [hvS w hw, h1 w hw]
    · intro w hw w' hw' h
      rcases Finset.mem_insert.1 hw with hwv | hw <;> rcases Finset.mem_insert.1 hw' with hwv' | hw'
      · rw [hwv, hwv']
      · rw [hwv] at h; simp [hvS w' hw'] at h; exact absurd h.symm (hpa w' hw')
      · rw [hwv'] at h; simp [hvS w hw] at h; exact absurd h (hpa w hw)
      · simp [hvS w hw, hvS w' hw'] at h; exact h2 w hw w' hw' h
    · intro w hw w' hw' h
      rcases Finset.mem_insert.1 hw with hwv | hw <;> rcases Finset.mem_insert.1 hw' with hwv' | hw'
      · rw [hwv, hwv']
      · rw [hwv] at h; simp [hvS w' hw'] at h; exact absurd h.symm (hqb w' hw')
      · rw [hwv'] at h; simp [hvS w hw] at h; exact absurd h (hqb w hw)
      · simp [hvS w hw, hvS w' hw'] at h; exact h3 w hw w' hw' h
    · intro w hw w' hw'
      rcases Finset.mem_insert.1 hw with hwv | hw <;> rcases Finset.mem_insert.1 hw' with hwv' | hw'
      · rw [hwv, hwv']; simpa using hpq
      · rw [hwv]; simp [hvS w' hw']; exact fun h => hpb w' hw' h.symm
      · rw [hwv']; simp [hvS w hw]; exact hqa w hw
      · simp [hvS w hw, hvS w' hw']; exact h4 w hw w' hw'

/-- Expansion of sets of vertices that see few other such vertices. -/
lemma expansion_of_degrees {U T X : Finset ι} {D t : ℝ} (hXT : X ⊆ T) (hXU : X ⊆ U)
    (hdeg : ∀ x ∈ U, D ≤ degIn H U x) (ht : ∀ v ∈ U, (((U ∩ T).filter (H.Adj v)).card : ℝ) ≤ t)
    (ht0 : 0 < t) : (D - t) / t * X.card ≤ (extNb H U X ∅).card := by
  set N := (U \ T).filter (fun y => ∃ x ∈ X, H.Adj x y)
  have hN : N ⊆ extNb H U X ∅ := by
    intro y hy
    obtain ⟨hyUT, x, hx, hxy⟩ := Finset.mem_filter.1 hy
    obtain ⟨hyU, hyT⟩ := Finset.mem_sdiff.1 hyUT
    exact Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨hyU, fun h => hyT (hXT h)⟩, x, hx, hxy,
      Finset.notMem_empty _⟩
  have h1 : ∀ x ∈ X, D - t ≤ (((U \ T).filter (H.Adj x)).card : ℝ) := by
    intro x hx
    have hsplit : U.filter (H.Adj x) ⊆ (U ∩ T).filter (H.Adj x) ∪ (U \ T).filter (H.Adj x) := by
      intro y hy
      obtain ⟨hyU, hxy⟩ := Finset.mem_filter.1 hy
      by_cases hyT : y ∈ T
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_inter.2 ⟨hyU, hyT⟩, hxy⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨hyU, hyT⟩, hxy⟩)
    have := (Finset.card_le_card hsplit).trans (Finset.card_union_le _ _)
    have h' : (degIn H U x : ℝ) ≤ ((U ∩ T).filter (H.Adj x)).card +
        ((U \ T).filter (H.Adj x)).card := by unfold degIn; exact_mod_cast this
    have := hdeg x (hXU hx)
    have := ht x (hXU hx)
    linarith
  have h2 : ∑ x ∈ X, (((U \ T).filter (H.Adj x)).card : ℝ) =
      ∑ y ∈ U \ T, ((X.filter (fun x => H.Adj x y)).card : ℝ) := by
    exact_mod_cast Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (r := H.Adj)
  have h3 : ∀ y ∈ U \ T, ((X.filter (fun x => H.Adj x y)).card : ℝ) ≤
      if y ∈ N then t else 0 := by
    intro y hy
    split_ifs with hyN
    · have hyU := (Finset.mem_sdiff.1 hy).1
      refine le_trans ?_ (ht y hyU)
      exact_mod_cast Finset.card_le_card fun x hx => by
        obtain ⟨hxX, hxy⟩ := Finset.mem_filter.1 hx
        exact Finset.mem_filter.2 ⟨Finset.mem_inter.2 ⟨hXU hxX, hXT hxX⟩, hxy.symm⟩
    · have : X.filter (fun x => H.Adj x y) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro x hx hxy
        exact hyN (Finset.mem_filter.2 ⟨hy, x, hx, hxy⟩)
      simp [this]
  have h4 : ∑ y ∈ U \ T, (if y ∈ N then t else 0) = t * N.card := by
    rw [← Finset.sum_filter]
    have : (U \ T).filter (fun y => y ∈ N) = N := by
      ext y; constructor
      · intro h; exact (Finset.mem_filter.1 h).2
      · intro h; exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 h).1, h⟩
    rw [this, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hsum := Finset.sum_le_sum h1
  rw [Finset.sum_const, nsmul_eq_mul, h2] at hsum
  have hsum2 := hsum.trans ((Finset.sum_le_sum h3).trans h4.le)
  have hNc : (N.card : ℝ) ≤ (extNb H U X ∅).card := by exact_mod_cast Finset.card_le_card hN
  rw [div_mul_eq_mul_div, div_le_iff₀ ht0]
  nlinarith

end helpers

end

end Lovasz
