import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_925

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_append (gs rest : List Gate) (w : List Bool) :
    wiresFrom (gs ++ rest) w = wiresFrom rest (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

lemma prefix_val (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (wiresFrom C.gates (List.ofFn x)).getD i false

lemma val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    val C x i.val = x i := by
  rw [val, prefix_val _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

lemma val_beyond {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i : ℕ}
    (hi : n + C.gates.length ≤ i) : val C x i = false := by
  rw [val, List.getD_eq_default _ _ (by simpa [wiresFrom_length] using hi)]

def operand {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j i : ℕ) : Bool :=
  if i < j then val C x i else false

lemma val_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) {p : ℕ} {g : Gate}
    (hp : C.gates[p]? = some g) :
    val C x (n+p) = g.op.eval (g.inputs.map (operand C x (n+p))) := by
  obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.1 hp
  have hsplit : C.gates = (C.gates.take p ++ [g]) ++ C.gates.drop (p+1) := by
    conv_lhs => rw [← List.take_append_drop (p+1) C.gates]
    rw [List.take_succ_eq_append_getElem hb, heq]
  let w := wiresFrom (C.gates.take p) (List.ofFn x)
  have hw : w.length = n+p := by
    simp [w, wiresFrom_length, List.length_take, Nat.min_eq_left hb.le]
  have hread (i : ℕ) : w.getD i false = operand C x (n+p) i := by
    by_cases hi : i < n+p
    · have hv : val C x i = w.getD i false := by
        unfold val
        conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
        exact prefix_val _ w i (hw.symm ▸ hi)
      simp only [operand, ite_eq_left hi, hv]
    · rw [operand, ite_eq_right hi, List.getD_eq_default _ _ (by omega)]
  have he : (g.inputs.map fun i => w.getD i false) = g.inputs.map (operand C x (n+p)) :=
    List.map_congr_left fun i _ => hread i
  unfold val
  conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
  change (wiresFrom (C.gates.drop (p+1))
    (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD (n+p) false = _
  rw [prefix_val _ _ _ (by simp [hw]), ← hw, he]
  simp [hw]

def point {n : ℕ} (s : Finset (Fin n)) (i : Fin n) : Bool := decide (i ∈ s)

def On {n : ℕ} (C : Circuit) (s : Finset (Fin n)) (u : ℕ) : Prop :=
  val C (point s) u = true

def Admissible (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma expand {n : ℕ} {C : Circuit} (hg : Admissible C) {s : Finset (Fin n)} {u : ℕ}
    (hu : n ≤ u) (hon : On C s u) :
    ∃ D : Finset ℕ, D.card ≤ 2 ∧ (∀ a ∈ D, a < u ∧ On C s a) ∧
      ∀ X : Finset (Fin n), (∀ a ∈ D, On C X a) → On C X u := by
  have hb : u < n + C.gates.length := by
    by_contra! h
    exact Bool.noConfusion ((val_beyond C (point s) h).symm.trans hon)
  obtain ⟨p, hp, rfl⟩ : ∃ p, p < C.gates.length ∧ u = n + p := ⟨u-n, by omega, by omega⟩
  let g := C.gates[p]
  have hget : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp, rfl⟩
  obtain ⟨hop, hlen⟩ := hg g (List.mem_of_getElem? hget)
  have read (X : Finset (Fin n)) (a : ℕ) :
      operand C (point X) (n+p) a = true ↔ a < n+p ∧ On C X a := by
    by_cases h : a < n+p <;> simp [operand, h, On]
  rcases hop with hop | hop
  · have ev (X : Finset (Fin n)) : On C X (n+p) ↔
        ∀ a ∈ g.inputs, a < n+p ∧ On C X a := by
      simp only [On, val_gate C (point X) hget, hop, GateOp.eval, List.all_map,
        List.all_eq_true, Function.comp_apply, id, read]
    exact ⟨g.inputs.toFinset, (List.toFinset_card_le _).trans hlen,
      fun a ha => (ev s).1 hon a (List.mem_toFinset.1 ha), fun X hX =>
        (ev X).2 fun a ha => ⟨((ev s).1 hon a ha).1, hX a (List.mem_toFinset.2 ha)⟩⟩
  · have ev (X : Finset (Fin n)) : On C X (n+p) ↔
        ∃ a ∈ g.inputs, a < n+p ∧ On C X a := by
      simp only [On, val_gate C (point X) hget, hop, GateOp.eval, List.any_map,
        List.any_eq_true, Function.comp_apply, id, read]
    obtain ⟨a, ha, hlt, haon⟩ := (ev s).1 hon
    exact ⟨{a}, by simp, by simpa using And.intro hlt haon, fun X hX =>
      (ev X).2 ⟨a, ha, hlt, hX a (by simp)⟩⟩

lemma on_mono {n : ℕ} {C : Circuit} (hg : Admissible C) {s t : Finset (Fin n)}
    (hst : s ⊆ t) (u : ℕ) : On C s u → On C t u := by
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro hu
    by_cases h : u < n
    · let i : Fin n := ⟨u, h⟩
      have input (X : Finset (Fin n)) : On C X u ↔ i ∈ X := by
        change val C (point X) i.val = true ↔ _
        rw [val_input]
        simp [point]
      exact (input t).2 (hst ((input s).1 hu))
    · obtain ⟨D, _, hd, force⟩ := expand hg (Nat.le_of_not_gt h) hu
      exact force t fun a ha => ih a (hd a ha).1 (hd a ha).2

lemma frontier {n : ℕ} {C : Circuit} (hg : Admissible C) (s : Finset (Fin n))
    (A : Finset ℕ) (ha : ∀ u ∈ A, n ≤ u) (k : ℕ) (F : Finset ℕ)
    (hb : ∀ u ∈ F, u ∈ A → u < k) (ht : ∀ u ∈ F, On C s u) :
    ∃ L : Finset ℕ, (∀ u ∈ L, u ∉ A ∧ On C s u) ∧
      L.card ≤ F.card + (A ∩ Finset.range k).card ∧
      ∀ X : Finset (Fin n), (∀ u ∈ L, On C X u) → ∀ u ∈ F, On C X u := by
  classical
  induction k generalizing F with
  | zero =>
    exact ⟨F, fun u h => ⟨fun hA => Nat.not_lt_zero u (hb u h hA), ht u h⟩,
      by simp, fun _ h => h⟩
  | succ k ih =>
    have hsub : A ∩ Finset.range k ⊆ A ∩ Finset.range (k+1) :=
      fun _ h => Finset.mem_inter.2 ⟨(Finset.mem_inter.1 h).1,
        Finset.range_mono (Nat.le_succ k) (Finset.mem_inter.1 h).2⟩
    by_cases hk : k ∈ F ∧ k ∈ A
    · obtain ⟨D, hD, hchildren, force⟩ := expand hg (ha k hk.2) (ht k hk.1)
      let G := F.erase k ∪ D
      have child (u : ℕ) (hu : u ∈ G) : u ∈ F.erase k ∨ u ∈ D := Finset.mem_union.1 hu
      obtain ⟨L, hL, hsize, hforce⟩ := ih G (by
        intro u hu hA
        rcases child u hu with he | hd
        · obtain ⟨hne, hF⟩ := Finset.mem_erase.1 he
          have := hb u hF hA
          omega
        · exact (hchildren u hd).1) (by
        intro u hu
        rcases child u hu with he | hd
        · exact ht u (Finset.mem_of_mem_erase he)
        · exact (hchildren u hd).2)
      have hG : G.card ≤ (F.erase k).card + D.card := Finset.card_union_le _ _
      have herase := Finset.card_erase_add_one hk.1
      have hinc : (A ∩ Finset.range k).card < (A ∩ Finset.range (k+1)).card := by
        apply Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hsub, ?_⟩)
        intro e
        have hmem : k ∈ A ∩ Finset.range (k+1) := by simp [hk.2]
        rw [← e] at hmem
        simp at hmem
      refine ⟨L, hL, by omega, ?_⟩
      intro X hx u hu
      by_cases he : u = k
      · subst u
        exact force X fun a h => hforce X hx a (Finset.mem_union_right _ h)
      · exact hforce X hx u (Finset.mem_union_left _ (Finset.mem_erase.2 ⟨he, hu⟩))
    · obtain ⟨L, hL, hsize, hforce⟩ := ih F (by
        intro u hu hA
        have := hb u hu hA
        have hne : u ≠ k := fun e => hk (e ▸ And.intro hu hA)
        omega) ht
      exact ⟨L, hL, hsize.trans (Nat.add_le_add_left (Finset.card_le_card hsub) _), hforce⟩

lemma union_bound {n : ℕ} (L : Finset ℕ) (T : ℕ → Finset (Fin n)) (r : ℕ)
    (h : ∀ u ∈ L, (T u).card ≤ r) : (L.biUnion T).card ≤ L.card * r := by
  calc
    _ ≤ ∑ u ∈ L, (T u).card := Finset.card_biUnion_le
    _ ≤ ∑ _u ∈ L, r := Finset.sum_le_sum h
    _ = _ := by simp

def Piece {n m : ℕ} (S : Fin m → Finset (Fin n)) (w : Fin m) (t : Finset (Fin n)) : Prop :=
  t.card ≤ 1 ∨ ∃ v, v ≠ w ∧ t = S v

lemma piece_bounds {n m q : ℕ} {S : Fin m → Finset (Fin n)} {w : Fin m}
    (hq : 2 ≤ q) (hs : ∀ i, (S i).card = q+1)
    (hi : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (L : Finset ℕ) (T : ℕ → Finset (Fin n)) (ht : ∀ u ∈ L, Piece S w (T u)) :
    (L.biUnion T).card ≤ L.card * q + 1 ∧ ((L.biUnion T) ∩ S w).card ≤ L.card := by
  classical
  constructor
  · by_cases large : ∃ a ∈ L, ∃ v : Fin m, T a = S v
    · obtain ⟨a, ha, v, he⟩ := large
      let D := fun u => T u \ S v
      have hd : ∀ u ∈ L.erase a, (D u).card ≤ q := by
        intro u hu
        rcases ht u (Finset.mem_of_mem_erase hu) with h | ⟨j, _, hj⟩
        · exact (Finset.card_le_card Finset.sdiff_subset).trans (by omega)
        · by_cases e : v = j
          · simp [D, hj, e]
          · simp [D, hj, Finset.card_sdiff, hs, hi v j e]
      have cover : L.biUnion T ⊆ S v ∪ (L.erase a).biUnion D := by
        intro p hp
        obtain ⟨u, hu, hpu⟩ := Finset.mem_biUnion.1 hp
        by_cases h : p ∈ S v
        · exact Finset.mem_union_left _ h
        · have hne : u ≠ a := by
            rintro rfl
            exact h (he ▸ hpu)
          exact Finset.mem_union_right _ (Finset.mem_biUnion.2
            ⟨u, Finset.mem_erase.2 ⟨hne, hu⟩, Finset.mem_sdiff.2 ⟨hpu, h⟩⟩)
      have hcount := Finset.card_erase_add_one ha
      calc
        _ ≤ (S v ∪ (L.erase a).biUnion D).card := Finset.card_le_card cover
        _ ≤ (S v).card + ((L.erase a).biUnion D).card := Finset.card_union_le _ _
        _ ≤ (q+1) + (L.erase a).card * q := by rw [hs]; gcongr; exact union_bound _ _ _ hd
        _ = _ := by rw [← hcount, Nat.add_mul]; omega
    · apply Nat.le_trans (union_bound L T q ?_) (Nat.le_succ _)
      intro u hu
      rcases ht u hu with h | ⟨v, _, he⟩
      · omega
      · exact (large ⟨u, hu, v, he⟩).elim
  · rw [Finset.biUnion_inter]
    suffices h : ∀ u ∈ L, (T u ∩ S w).card ≤ 1 by
      simpa using union_bound L (fun u => T u ∩ S w) 1 h
    intro u hu
    rcases ht u hu with h | ⟨v, hv, he⟩
    · exact (Finset.card_le_card Finset.inter_subset_left).trans h
    · rw [he, hi v w hv]

noncomputable def specific {n m : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n))
    (w : Fin m) : Finset ℕ := by
  classical
  exact (Finset.Ico n (n+C.gates.length)).filter fun u =>
    On C (S w) u ∧ ∀ v, v ≠ w → ¬ On C (S v) u

lemma specific_count {n m q c K : ℕ} {C : Circuit} {S : Fin m → Finset (Fin n)}
    (hg : Admissible C) (hq : 2 ≤ q) (hs : ∀ i, (S i).card = q+1)
    (hi : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (hc : c ≤ q) (hK : c*q < K) (w : Fin m) (o : ℕ)
    (correct : ∀ X : Finset (Fin n), X.card ≤ K → (On C X o ↔ S w ⊆ X)) :
    c ≤ (specific C S w).card := by
  classical
  by_contra! hfew
  have hpos : 1 ≤ c := by omega
  have hqK : q+1 ≤ K := by
    have h := Nat.mul_le_mul_right q hpos
    simp only [Nat.one_mul] at h
    omega
  have hot := (correct (S w) (by rw [hs]; exact hqK)).2 (Finset.Subset.refl _)
  let A := specific C S w
  have hr {u : ℕ} (hu : u ∈ A) := Finset.mem_Ico.1 (Finset.mem_filter.1 hu).1
  obtain ⟨L, hL, hcard, hforce⟩ := frontier hg (S w) A (fun _ hu => (hr hu).1)
    (n+C.gates.length) {o} (fun _ _ hu => (hr hu).2) (by simpa using hot)
  have hLc : L.card ≤ c := by
    have h := Finset.card_le_card (Finset.inter_subset_left :
      A ∩ Finset.range (n+C.gates.length) ⊆ A)
    simp only [Finset.card_singleton] at hcard
    change A.card < c at hfew
    omega
  have cert (u : ℕ) : ∃ t : Finset (Fin n), u ∈ L →
      Piece S w t ∧ ∀ X : Finset (Fin n), t ⊆ X → On C X u := by
    by_cases hl : u ∈ L
    · obtain ⟨hna, hon⟩ := hL u hl
      by_cases hu : u < n
      · let i : Fin n := ⟨u, hu⟩
        refine ⟨{i}, fun _ => ⟨Or.inl (by simp), ?_⟩⟩
        intro X hx
        change val C (point X) i.val = true
        rw [val_input]
        exact decide_eq_true (hx (Finset.mem_singleton_self i))
      · have hb : u < n+C.gates.length := by
          by_contra! h
          exact Bool.noConfusion ((val_beyond C (point (S w)) h).symm.trans hon)
        have other : ∃ v, v ≠ w ∧ On C (S v) u := by
          by_contra! h
          exact hna (Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨by omega, hb⟩, hon, h⟩)
        obtain ⟨v, hv, hvon⟩ := other
        exact ⟨S v, fun _ => ⟨Or.inr ⟨v, hv, rfl⟩, fun _ hx => on_mono hg hx u hvon⟩⟩
    · exact ⟨∅, fun h => (hl h).elim⟩
  choose T hT using cert
  obtain ⟨hlit, hhits⟩ := piece_bounds hq hs hi L T (fun u hu => (hT u hu).1)
  have hweight : (L.biUnion T).card ≤ K := by
    have := Nat.mul_le_mul_right q hLc
    omega
  have hall : S w ⊆ L.biUnion T := (correct _ hweight).1 (hforce _ (fun u hu =>
    (hT u hu).2 _ (fun _ hp => Finset.mem_biUnion.2 ⟨u, hu, hp⟩)) o (by simp))
  rw [Finset.inter_eq_right.mpr hall, hs] at hhits
  omega

lemma total {n m q c K : ℕ} {C : Circuit} {S : Fin m → Finset (Fin n)}
    (hg : Admissible C) (hq : 2 ≤ q) (hs : ∀ i, (S i).card = q+1)
    (hi : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (hc : c ≤ q) (hK : c*q < K) (out : Fin m → ℕ)
    (correct : ∀ w (X : Finset (Fin n)), X.card ≤ K → (On C X (out w) ↔ S w ⊆ X)) :
    m*c ≤ C.gates.length := by
  classical
  let A := specific C S
  have hd : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint A := by
    intro w _ v _ hwv
    apply Finset.disjoint_left.2
    intro u huw huv
    exact (Finset.mem_filter.1 huw).2.2 v hwv.symm (Finset.mem_filter.1 huv).2.1
  have hsub : Finset.univ.biUnion A ⊆ Finset.Ico n (n+C.gates.length) := by
    intro u hu
    obtain ⟨w, _, hw⟩ := Finset.mem_biUnion.1 hu
    exact (Finset.mem_filter.1 hw).1
  calc
    _ = ∑ _w : Fin m, c := by simp
    _ ≤ ∑ w : Fin m, (A w).card := Finset.sum_le_sum fun w _ =>
      specific_count hg hq hs hi hc hK w (out w) (correct w)
    _ = (Finset.univ.biUnion A).card := (Finset.card_biUnion hd).symm
    _ ≤ (Finset.Ico n (n+C.gates.length)).card := Finset.card_le_card hsub
    _ = _ := by simp

end PEqualNP.Outside.L_meta_925

theorem PEqualNP.Outside.L_meta_925 : ∀ (q n m K : ℕ) (S : Fin m → Finset (Fin n)), 2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ K → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∀ v ∈ S w, x v = true)) → ∀ c : ℕ, c ≤ q → c * q < K → m * c ≤ gates.length := by
  classical
  intro q n m K S hq hs hi gates out hg he c hc hK
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gates, 0⟩
  apply PEqualNP.Outside.L_meta_925.total (C := C) hg hq hs hi hc hK out
  intro w X hX
  let x := PEqualNP.Outside.L_meta_925.point X
  have heq : Finset.univ.filter (fun i : Fin n => x i = true) = X := by
    ext i
    simp [x, PEqualNP.Outside.L_meta_925.point]
  have h := he w x (heq ▸ hX)
  change PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = true ↔ _
  rw [h, decide_eq_true_eq]
  simp only [x, PEqualNP.Outside.L_meta_925.point, decide_eq_true_eq]
  rfl
