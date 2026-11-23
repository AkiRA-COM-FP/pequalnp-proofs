import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_885

def bits {n : ℕ} (s : Finset (Fin n)) (p : Fin n) : Bool :=
  decide (p ∈ s)

lemma bits_mono {n : ℕ} {s t : Finset (Fin n)} (h : s ⊆ t) : bits s ≤ bits t := by
  intro p
  by_cases hp : p ∈ s
  · simp [bits, hp, h hp]
  · simp [bits, hp]

lemma window {n l : ℕ} (I : Finset (Fin l)) (k : ℕ)
    (f : Fin l → Finset (Fin n) → Bool) (hm : ∀ i ∈ I, Monotone (f i)) :
    ∃ (B : Finset (Fin n)) (d : ℕ), B.card ≤ d * k ∧ d ≤ I.card ∧
      ∀ E : Finset (Fin n), E.card ≤ k ∨ d = I.card →
        ∀ i ∈ I, f i (B ∪ E) = f i B := by
  classical
  let active (s : Finset (Fin n)) := I.filter fun i => f i s = true
  have monoActive {s t : Finset (Fin n)} (h : s ⊆ t) : active s ⊆ active t := by
    intro i hi
    obtain ⟨hi, hv⟩ := Finset.mem_filter.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨hi, ?_⟩
    have hle := hm i hi h
    exact Bool.eq_true_of_true_le (hv ▸ hle)
  let feasible := Finset.univ.filter fun s : Finset (Fin n) => s.card ≤ (active s).card * k
  have emp : ∅ ∈ feasible := by simp [feasible]
  obtain ⟨B, hB, hmax⟩ := feasible.exists_max_image (fun s => (active s).card) ⟨∅, emp⟩
  have budget := (Finset.mem_filter.mp hB).2
  have cap (s) : (active s).card ≤ I.card := Finset.card_le_card (Finset.filter_subset ..)
  refine ⟨B, (active B).card, budget, cap _, ?_⟩
  intro E hE i hi
  have hsub := monoActive (Finset.subset_union_left (s₂ := E) (s₁ := B))
  by_contra hne
  have hle := hm i hi (Finset.subset_union_left (s₂ := E) (s₁ := B))
  have hvals : f i B = false ∧ f i (B ∪ E) = true := by
    cases ha : f i B <;> cases hb : f i (B ∪ E) <;> simp_all
    exact absurd hle (by decide)
  have hstrict : (active B).card < (active (B ∪ E)).card := by
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
    intro he
    have hh : i ∈ active (B ∪ E) := Finset.mem_filter.mpr ⟨hi, hvals.2⟩
    rw [← he] at hh
    exact Bool.noConfusion (hvals.1.symm.trans (Finset.mem_filter.mp hh).2)
  rcases hE with hsmall | hfull
  · have next : B ∪ E ∈ feasible := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      calc
        (B ∪ E).card ≤ B.card + E.card := Finset.card_union_le ..
        _ ≤ (active B).card * k + k := Nat.add_le_add budget hsmall
        _ = ((active B).card + 1) * k := (Nat.succ_mul ..).symm
        _ ≤ (active (B ∪ E)).card * k := Nat.mul_le_mul_right _ hstrict
    exact (Nat.not_le_of_lt hstrict) (hmax _ next)
  · have := cap (B ∪ E)
    omega

lemma bad_bound {n m q : ℕ} (F : Fin m → Finset (Fin n))
    (pair : ∀ p p' : Fin n, p ≠ p' → ∃ i, p ∈ F i ∧ p' ∈ F i)
    (degree : ∀ p : Fin n, (Finset.univ.filter (fun i => p ∈ F i)).card = q + 1)
    (B : Finset (Fin n)) :
    (Finset.univ.filter (fun i => ¬ Disjoint B (F i))).card ≤ B.card * q + 1 := by
  classical
  let bad (s : Finset (Fin n)) := Finset.univ.filter fun i => ¬ Disjoint s (F i)
  change (bad B).card ≤ _
  induction B using Finset.induction_on with
  | empty => simp [bad]
  | @insert p s hp ih =>
    let star := Finset.univ.filter fun i => p ∈ F i
    have eqn : bad (insert p s) = star ∪ bad s := by
      ext i
      by_cases hi : p ∈ F i <;> simp [bad, star, Finset.disjoint_insert_left, hi]
    rw [eqn, Finset.card_insert_of_notMem hp, Nat.succ_mul]
    have ds : star.card = q + 1 := degree _
    rcases s.eq_empty_or_nonempty with hs | ⟨z, hz⟩
    · subst s
      simpa [bad] using ds.le
    · obtain ⟨i, hip, hiz⟩ := pair p z (by rintro rfl; exact hp hz)
      have hi : i ∈ star ∩ bad s := by
        simp only [star, bad, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hip, fun h => Finset.disjoint_left.mp h hz hiz⟩
      have pos := Finset.card_pos.mpr (show (star ∩ bad s).Nonempty from ⟨i, hi⟩)
      have sum := Finset.card_union_add_card_inter star (bad s)
      omega

def readWire {n : ℕ} (L : List Gate) (j : Fin L.length) (x : Fin n → Bool) : Bool :=
  ((L.get j).inputs.map fun p =>
    (Circuit.wires ⟨L.take j.val, 0⟩ (List.ofFn x)).getD p false).headD false

def freezeGate (g : Gate) (b : Bool) : Gate :=
  match g.op with
  | .not => if b then ⟨.or, []⟩ else ⟨.and, []⟩
  | _ => g

def frozen {n : ℕ} (L : List Gate) (y : Fin n → Bool) : List Gate :=
  List.ofFn fun j : Fin L.length => freezeGate (L.get j) (readWire L j y)

lemma frozen_length {n : ℕ} (L : List Gate) (y : Fin n → Bool) :
    (frozen L y).length = L.length := List.length_ofFn

lemma frozen_basis {n : ℕ} (L : List Gate) (y : Fin n → Bool)
    (h : ∀ g ∈ L, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ frozen L y, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hg
  obtain ⟨ho, hl⟩ := h (L.get j) (List.get_mem ..)
  rcases ho with ha | ha | ha
  · simp only [freezeGate, ha]
    simp [hl, -List.get_eq_getElem]
  · simp only [freezeGate, ha]
    simp [hl, -List.get_eq_getElem]
  · cases readWire L j y <;> simp only [freezeGate, ha] <;> simp

lemma frozen_wires {n : ℕ} (L : List Gate) (y x : Fin n → Bool)
    (stable : ∀ j : Fin L.length, (L.get j).op = .not → readWire L j x = readWire L j y) :
    Circuit.wires ⟨frozen L y, 0⟩ (List.ofFn x) = Circuit.wires ⟨L, 0⟩ (List.ofFn x) := by
  let w (A : List Gate) := Circuit.wires ⟨A, 0⟩ (List.ofFn x)
  have step (A : List Gate) (g : Gate) :
      w (A ++ [g]) = w A ++ [g.op.eval (g.inputs.map fun p => (w A).getD p false)] := by
    simp [w, Circuit.wires, List.foldl_append]
  have pre (s : ℕ) (hs : s ≤ L.length) :
      w ((frozen L y).take s) = w (L.take s) := by
    induction s with
    | zero => simp
    | succ j ih =>
      have hj : j < L.length := hs
      have hj' : j < (frozen L y).length := (frozen_length L y).symm ▸ hj
      rw [List.take_succ_eq_append_getElem hj', List.take_succ_eq_append_getElem hj,
        step, step, ih (Nat.le_of_lt hj)]
      have hget : (frozen L y)[j] = freezeGate (L.get ⟨j, hj⟩) (readWire L ⟨j, hj⟩ y) :=
        List.getElem_ofFn _
      rw [hget]
      let a : Fin L.length := ⟨j, hj⟩
      change _ ++ [(freezeGate (L.get a) (readWire L a y)).op.eval
        ((freezeGate (L.get a) (readWire L a y)).inputs.map _)] =
        _ ++ [(L.get a).op.eval ((L.get a).inputs.map _)]
      cases hop : (L.get a).op with
      | not =>
        have hv := stable a hop
        change (((L.get a).inputs.map fun p => (w (L.take j)).getD p false).headD false) = _ at hv
        cases hb : readWire L a y <;>
          simp only [freezeGate, hop, hb, Bool.false_eq_true, ite_false, ite_true, GateOp.eval, hv] <;> rfl
      | _ => simp only [freezeGate, hop]
  simpa [w, List.take_of_length_le (frozen_length L y).le] using pre L.length (Nat.le_refl _)

abbrev CountRow : Prop :=
  ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : Circuit) (o c : Fin m → ℕ),
    (∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) →
    (∀ i, 2 ≤ (S i).card) →
    (∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) →
    (∀ i p, (C.wires (List.ofFn (fun q => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) →
    (∀ i (x : Fin n → Bool), (Finset.univ.filter (fun q => x q = true)).card ≤ k →
      (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) →
    (∀ i, c i ≤ k) → (∀ i, c i + 1 ≤ (S i).card) → ∑ i, c i ≤ C.size

abbrev PropagationRow : Prop :=
  ∀ (n : ℕ) (A : List Gate) (T Z : Finset (Fin n)),
    (∀ g ∈ A, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) →
    ∃ (D : List Gate) (r : ℕ → ℕ),
      (∀ g ∈ D, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∧ D.length ≤ A.length ∧
      ∀ o, (∃ x y : Fin n → Bool,
        Circuit.eval ⟨A, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠
        Circuit.eval ⟨A, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) →
        ∀ x : Fin n → Bool, Circuit.eval ⟨D, r o⟩ (List.ofFn x) =
          Circuit.eval ⟨A, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i))

def support {n : ℕ} (x : Fin n → Bool) := Finset.univ.filter (fun p => x p = true)

lemma support_single {n : ℕ} (p : Fin n) :
    support (fun q => decide (q = p)) = {p} := by
  ext q
  simp [support]

def good {n m : ℕ} (F : Fin m → Finset (Fin n)) (B : Finset (Fin n)) :=
  Finset.univ.filter fun i => Disjoint B (F i)

lemma count_window (count : CountRow) (propagate : PropagationRow) {n m q k : ℕ}
    (hk : 1 ≤ k) (hq : 1 ≤ q) (F : Fin m → Finset (Fin n))
    (sz : ∀ i, (F i).card = q + 1)
    (inter : ∀ i j, i ≠ j → (F i ∩ F j).card ≤ 1)
    (A : List Gate) (o : Fin m → ℕ) (B : Finset (Fin n))
    (basis : ∀ g ∈ A, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (win : ∀ E : Finset (Fin n), E.card ≤ k → ∀ i,
      Circuit.eval ⟨A, o i⟩ (List.ofFn (bits (B ∪ E))) =
        decide (∃ p ∈ F i, bits (B ∪ E) p = true)) :
    min k q * (good F B).card ≤ A.length := by
  classical
  let pin (x : Fin n → Bool) (p : Fin n) :=
    if p ∈ B then true else if p ∈ (∅ : Finset (Fin n)) then false else x p
  have calcPin (i) (hi : i ∈ good F B) (x : Fin n → Bool) (hx : (support x).card ≤ k) :
      Circuit.eval ⟨A, o i⟩ (List.ofFn (pin x)) = decide (∃ p ∈ F i, x p = true) := by
    have dis := (Finset.mem_filter.mp hi).2
    have same : pin x = bits (B ∪ support x) := by
      funext p
      by_cases hp : p ∈ B <;> cases hb : x p <;> simp [pin, bits, support, hp, hb]
    rw [same, win _ hx]
    apply decide_eq_decide.mpr
    constructor
    · rintro ⟨p, hp, hv⟩
      have hB : p ∉ B := fun h => Finset.disjoint_left.mp dis h hp
      exact ⟨p, hp, by simpa [bits, support, hB] using hv⟩
    · rintro ⟨p, hp, hv⟩
      exact ⟨p, hp, by simp [bits, support, hv]⟩
  obtain ⟨D, r, hD, hlen, hprop⟩ := propagate n A B ∅ basis
  have compute (i) (hi : i ∈ good F B) (x : Fin n → Bool) (hx : (support x).card ≤ k) :
      Circuit.eval ⟨D, r (o i)⟩ (List.ofFn x) = decide (∃ p ∈ F i, x p = true) := by
    apply Eq.trans (hprop (o i) ?_ x) (calcPin i hi x hx)
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (show 0 < (F i).card by rw [sz]; omega)
    refine ⟨fun _ => false, fun a => decide (a = p), ?_⟩
    change Circuit.eval ⟨A, o i⟩ (List.ofFn (pin _)) ≠ Circuit.eval ⟨A, o i⟩ (List.ofFn (pin _))
    rw [calcPin i hi _ (by simp [support]), calcPin i hi _ (by simpa [support_single] using hk)]
    simp [hp]
  let G := good F B
  let e : Fin G.card ≃ G := (Fintype.equivFinOfCardEq (by simp)).symm
  let line (i : Fin G.card) : Fin m := (e i).val
  have inj : Function.Injective line := Subtype.val_injective.comp e.injective
  have hm (i) : line i ∈ good F B := (e i).property
  have answer := count n G.card k (fun i => F (line i)) ⟨D, 0⟩ (fun i => r (o (line i)))
    (fun _ => min k q) (fun i j h => inter _ _ (inj.ne h)) (fun i => by rw [sz]; omega) hD
    (by
      intro i p
      change Circuit.eval ⟨D, r (o (line i))⟩ _ = true ↔ _
      rw [compute _ (hm i) _ (by simpa [support_single] using hk)]
      simp)
    (by
      intro i x hx off
      change Circuit.eval ⟨D, r (o (line i))⟩ _ = false
      rw [compute _ (hm i) _ hx]
      simpa using fun p hp => off p hp)
    (fun _ => min_le_left ..) (fun i => by rw [sz]; omega)
  have hbound : G.card * min k q ≤ D.length := by simpa [Circuit.size] using answer
  simpa [G, Nat.mul_comm] using hbound.trans hlen

lemma recover {K a cutoff m kept lost credit : ℕ}
    (h : K + a * cutoff ≤ a * m + a * credit)
    (budget : lost + credit ≤ cutoff) (partition : kept + lost = m) :
    K ≤ a * kept := by
  have hscaled := Nat.mul_le_mul_left a budget
  rw [Nat.mul_add] at hscaled
  rw [← partition, Nat.mul_add] at h
  omega

end PEqualNP.Outside.L_meta_885

open PEqualNP.Outside.L_meta_885

theorem PEqualNP.Outside.L_meta_885 : (∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size) → (∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i))) → ∀ (nP mL qO : ℕ) (Fam : Fin mL → Finset (Fin nP)), (∀ i1 : Fin mL, (Fam i1).card = qO + 1) → (∀ i7 i8 : Fin mL, i7 ≠ i8 → (Fam i7 ∩ Fam i8).card ≤ 1) → (∀ p1 p2 : Fin nP, p1 ≠ p2 → ∃ i3 : Fin mL, p1 ∈ Fam i3 ∧ p2 ∈ Fam i3) → (∀ p3 : Fin nP, (Finset.univ.filter (fun i4 : Fin mL => p3 ∈ Fam i4)).card = qO + 1) → ∀ (tN kW : ℕ) (L : List PEqualNP.CircuitLowerBounds.Gate) (outW : Fin mL → ℕ), 1 ≤ tN → 1 ≤ kW → (∀ g1 ∈ L, (g1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g1.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g1.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g1.inputs.length ≤ 2) → Set.ncard {i5 : Fin L.length | (L.get i5).op = PEqualNP.CircuitLowerBounds.GateOp.not} ≤ tN → (∀ (j1 : ℕ) (g2 : PEqualNP.CircuitLowerBounds.Gate), L[j1]? = some g2 → g2.op = PEqualNP.CircuitLowerBounds.GateOp.not → Monotone (fun x1 : Fin nP → Bool => (g2.inputs.map (fun i6 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨L.take j1, 0⟩ (List.ofFn x1)).getD i6 false)).headD false)) → (∀ (w1 : Fin mL) (x2 : Fin nP → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨L, outW w1⟩ (List.ofFn x2) = decide (∃ v1 ∈ Fam w1, x2 v1 = true)) → ∀ Kb : ℕ, ((tN = 1 ∧ Kb ≤ kW * mL ∧ Kb ≤ qO * mL) ∨ (Kb + kW * (tN * kW * qO + 1) ≤ kW * mL + kW * kW * qO ∧ Kb + qO * (tN * kW * qO + 1) ≤ qO * mL + qO * kW * qO)) → Kb + qO * (tN * kW * qO + 1) ≤ qO * mL → Kb ≤ L.length := by
  classical
  intro count propagate n m q F sz inter pair degree t k L o _ht hk basis notCount mono computes K bounds last
  by_cases hzero : q = 0
  · subst q
    have hK : K = 0 := by simpa using last
    simp [hK]
  have hq : 1 ≤ q := Nat.pos_of_ne_zero hzero
  let I := Finset.univ.filter (fun j : Fin L.length => (L.get j).op = GateOp.not)
  have eqset : (I : Set (Fin L.length)) = {j | (L.get j).op = GateOp.not} := by
    ext j
    simp [I]
  have cap : I.card ≤ t := by
    rwa [← eqset, Set.ncard_coe_finset] at notCount
  let f (j : Fin L.length) (s : Finset (Fin n)) := readWire L j (bits s)
  have hf : ∀ j ∈ I, Monotone (f j) := by
    intro j hj s u hsu
    have hop := (Finset.mem_filter.mp hj).2
    have hget : L[j.val]? = some (L.get j) := by simp
    exact mono j.val (L.get j) hget hop (bits_mono hsu)
  obtain ⟨B, d, budget, hd, stable⟩ := window I k f hf
  let kept := (good F B).card
  let lost := (Finset.univ.filter (fun i => ¬ Disjoint B (F i))).card
  have partition : kept + lost = m := by
    simpa [kept, lost, good] using
      (Finset.univ.card_filter_add_card_filter_not (fun i : Fin m => Disjoint B (F i)))
  have bad : lost ≤ B.card * q + 1 := bad_bound F pair degree B
  have counted (u : ℕ) (hu : 1 ≤ u)
      (within : ∀ E : Finset (Fin n), E.card ≤ u → E.card ≤ k ∨ d = I.card) :
      min u q * kept ≤ L.length := by
    refine le_trans (count_window count propagate hu hq F sz inter
      (frozen L (bits B)) o B (frozen_basis L _ basis) ?_) (frozen_length L _).le
    intro E hE i
    have hw := frozen_wires L (bits B) (bits (B ∪ E)) (by
      intro j hj
      exact stable E (within E hE) j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩))
    exact (congrArg (fun w : List Bool => w.getD (o i) false) hw).trans (computes i _)
  by_cases full : d = I.card
  · have lower : q * kept ≤ L.length := by
      simpa using counted q hq (fun _ _ => Or.inr full)
    have loss : lost ≤ t * k * q + 1 := by
      calc
        lost ≤ B.card * q + 1 := bad
        _ ≤ d * k * q + 1 := by gcongr
        _ ≤ t * k * q + 1 := by gcongr; exact hd.trans cap
    apply le_trans _ lower
    apply recover (credit := 0) (cutoff := t * k * q + 1) (m := m) (lost := lost)
    · simpa using last
    · simpa using loss
    · exact partition
  have lower := counted k hk (fun _ h => Or.inl h)
  have dt : d + 1 ≤ t := by omega
  apply le_trans _ lower
  rcases bounds with ⟨one, smallK, smallQ⟩ | ⟨boundK, boundQ⟩
  · have dz : d = 0 := by omega
    have emp : B = ∅ := Finset.card_eq_zero.mp (by simpa [dz] using budget)
    have allKept : kept = m := by simp [kept, good, emp]
    rw [allKept]
    rcases le_total k q with h | h
    · simpa [min_eq_left h] using smallK
    · simpa [min_eq_right h] using smallQ
  · have loss : lost + k * q ≤ t * k * q + 1 := by
      calc
        lost + k * q ≤ (B.card * q + 1) + k * q := by omega
        _ ≤ (d * k * q + 1) + k * q := by gcongr
        _ = (d + 1) * k * q + 1 := by ring
        _ ≤ t * k * q + 1 := by gcongr
    rcases le_total k q with h | h
    · rw [min_eq_left h]
      exact recover (by simpa [Nat.mul_assoc] using boundK) loss partition
    · rw [min_eq_right h]
      exact recover (by simpa [Nat.mul_assoc] using boundQ) loss partition
