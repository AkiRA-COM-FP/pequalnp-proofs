import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_924

def bits {n : ℕ} (Z : Finset (Fin n)) (p : Fin n) : Bool :=
  decide (p ∉ Z)

def wire {n : ℕ} (L : List Gate) (Z : Finset (Fin n)) (a : ℕ) : Bool :=
  (Circuit.wires ⟨L, 0⟩ (List.ofFn (bits Z))).getD a false

def basis (L : List Gate) : Prop :=
  ∀ g ∈ L, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2

lemma prefix_basis {L : List Gate} {g : Gate} (h : basis (L ++ [g])) : basis L :=
  fun g' hg' => h g' (List.mem_append_left _ hg')

lemma last_basis {L : List Gate} {g : Gate} (h : basis (L ++ [g])) :
    (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 :=
  h _ (by simp)

lemma wires_length (L : List Gate) (x : List Bool) :
    (Circuit.wires ⟨L, 0⟩ x).length = x.length + L.length := by
  induction L using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton L g ih =>
    simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.length_append, List.length_cons, List.length_nil] at ih ⊢
    omega

lemma wire_append {n : ℕ} (L : List Gate) (g : Gate) (Z : Finset (Fin n)) (a : ℕ) :
    wire (L ++ [g]) Z a =
      if a = n + L.length then g.op.eval (g.inputs.map (wire L Z)) else wire L Z a := by
  let v := Circuit.wires ⟨L, 0⟩ (List.ofFn (bits Z))
  have hlen : v.length = n + L.length := by simp [v, wires_length]
  unfold wire Circuit.wires
  rw [List.foldl_append]
  change (v ++ [g.op.eval (g.inputs.map (wire L Z))]).getD a false =
    if a = n + L.length then g.op.eval (g.inputs.map (wire L Z)) else v.getD a false
  split_ifs with h
  · rw [List.getD_append_right _ _ _ _ (by omega), h, hlen, Nat.sub_self]
    rfl
  · by_cases ha : a < v.length
    · exact List.getD_append _ _ _ _ ha
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma wire_nil {n : ℕ} (Z : Finset (Fin n)) (a : ℕ) :
    wire [] Z a = if h : a < n then bits Z ⟨a, h⟩ else false := by
  change (List.ofFn (bits Z)).getD a false = _
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · exact List.getD_eq_default _ _ (by simp; omega)

lemma gate_false {g : Gate} (hg : g.op = .and ∨ g.op = .or)
    {u v : ℕ → Bool} (h : ∀ a ∈ g.inputs, u a = false → v a = false)
    (hu : g.op.eval (g.inputs.map u) = false) : g.op.eval (g.inputs.map v) = false := by
  rcases hg with ha | ha
  · simp [ha, GateOp.eval] at hu ⊢
    obtain ⟨a, ham, hau⟩ := hu
    exact ⟨a, ham, h _ ham hau⟩
  · simp [ha, GateOp.eval] at hu ⊢
    exact fun a ha => h _ ha (hu a ha)

lemma wire_false_of_subset {n : ℕ} {A B : Finset (Fin n)} (hab : A ⊆ B)
    (L : List Gate) (hl : basis L) (a : ℕ) (hf : wire L A a = false) :
    wire L B a = false := by
  induction L using List.reverseRecOn generalizing a with
  | nil =>
    rw [wire_nil] at hf ⊢
    split_ifs at hf ⊢ with h
    · simpa [bits] using hab (by simpa [bits] using hf)
    · rfl
  | append_singleton L g ih =>
    rw [wire_append] at hf ⊢
    split_ifs at hf ⊢ with h
    · exact gate_false (last_basis hl).1 (fun b _ hb => ih (prefix_basis hl) b hb) hf
    · exact ih (prefix_basis hl) a hf

def exclusive {n m : ℕ} (S : Fin m → Finset (Fin n)) (L : List Gate)
    (a : ℕ) (i : Fin m) : Prop :=
  wire L (S i) a = false ∧ ∀ j, j ≠ i → wire L (S j) a = true

noncomputable def count {n m : ℕ} (S : Fin m → Finset (Fin n)) (L : List Gate)
    (i : Fin m) : ℕ := by
  classical
  exact ((Finset.range L.length).filter fun t => exclusive S L (n + t) i).card

lemma count_append {n m : ℕ} (S : Fin m → Finset (Fin n)) (L : List Gate) (g : Gate)
    (i : Fin m) [Decidable (exclusive S (L ++ [g]) (n + L.length) i)] :
    count S (L ++ [g]) i = count S L i +
      if exclusive S (L ++ [g]) (n + L.length) i then 1 else 0 := by
  classical
  let p (t : ℕ) := exclusive S (L ++ [g]) (n + t) i
  have eqf : (Finset.range L.length).filter p =
      (Finset.range L.length).filter (fun t => exclusive S L (n + t) i) := by
    apply Finset.filter_congr
    intro t ht
    have hne : n + t ≠ n + L.length := by
      have := Finset.mem_range.mp ht
      omega
    simp only [p, exclusive, wire_append, ite_eq_right hne]
  change ((Finset.range (L ++ [g]).length).filter p).card = _
  simp only [List.length_append, List.length_singleton, Finset.range_add_one,
    Finset.filter_insert]
  by_cases h : p L.length
  · have hn : L.length ∉ (Finset.range L.length).filter p := by simp
    rw [ite_eq_left h, Finset.card_insert_of_notMem hn, eqf, ite_eq_left h]
    rfl
  · rw [ite_eq_right h, eqf, ite_eq_right h, Nat.add_zero]
    rfl

lemma total_count {n m : ℕ} (S : Fin m → Finset (Fin n)) (L : List Gate) :
    ∑ i : Fin m, count S L i ≤ L.length := by
  classical
  induction L using List.reverseRecOn with
  | nil => simp [count]
  | append_singleton L g ih =>
    let p (i : Fin m) := exclusive S (L ++ [g]) (n + L.length) i
    have hu : (Finset.univ.filter p).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro i hi j hj
      by_contra h
      have ha := ((Finset.mem_filter.mp hi).2 : p i)
      have hb := ((Finset.mem_filter.mp hj).2 : p j)
      exact Bool.noConfusion (hb.1.symm.trans (ha.2 j (Ne.symm h)))
    have hs : (∑ i : Fin m, if p i then 1 else 0) ≤ 1 := by
      simpa [Finset.sum_boole] using hu
    simp only [count_append, Finset.sum_add_distrib, List.length_append, List.length_singleton]
    exact Nat.add_le_add ih hs

lemma certificate {n m : ℕ} (S : Fin m → Finset (Fin n)) (i : Fin m)
    (L : List Gate) (hl : basis L) (D : Finset ℕ)
    (hd : ∀ a ∈ D, wire L (S i) a = false) :
    ∃ (J : Finset (Fin m)) (P : Finset (Fin n)), i ∉ J ∧
      J.card + P.card ≤ D.card + count S L i ∧
      ∀ Z : Finset (Fin n), P ⊆ Z → (∀ j ∈ J, S j ⊆ Z) →
        ∀ a ∈ D, wire L Z a = false := by
  classical
  induction L using List.reverseRecOn generalizing D with
  | nil =>
    let P := Finset.univ.filter (fun p : Fin n => p.val ∈ D)
    have hP : P.card ≤ D.card :=
      Finset.card_le_card_of_injOn Fin.val (fun _ hp => (Finset.mem_filter.mp hp).2)
        (fun _ _ _ _ h => Fin.ext h)
    refine ⟨∅, P, by simp, by simpa [count] using hP, ?_⟩
    intro Z hp _ a ha
    rw [wire_nil]
    split_ifs with h
    · have hm : (⟨a, h⟩ : Fin n) ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩
      simp [bits, hp hm]
    · rfl
  | append_singleton L g ih =>
    let u := n + L.length
    let E := D.erase u
    have hold (Z : Finset (Fin n)) {a : ℕ} (ha : a ≠ u) :
        wire (L ++ [g]) Z a = wire L Z a := by
      rw [wire_append, ite_eq_right ha]
    have prior : ∀ a ∈ E, wire L (S i) a = false := by
      intro a ha
      obtain ⟨hne, hm⟩ := Finset.mem_erase.mp ha
      rw [← hold _ hne]
      exact hd _ hm
    have restore (Z : Finset (Fin n)) (he : ∀ a ∈ E, wire L Z a = false)
        (hu : u ∈ D → wire (L ++ [g]) Z u = false) :
        ∀ a ∈ D, wire (L ++ [g]) Z a = false := by
      intro a ha
      by_cases h : a = u
      · exact h ▸ hu (h ▸ ha)
      · rw [hold _ h]
        exact he _ (Finset.mem_erase.mpr ⟨h, ha⟩)
    by_cases hu : u ∈ D
    · have hsize : E.card + 1 = D.card := Finset.card_erase_add_one hu
      have hfalse := hd u hu
      by_cases hx : exclusive S (L ++ [g]) u i
      · let F := g.inputs.toFinset.filter (fun a => wire L (S i) a = false)
        have hf : F.card ≤ 2 :=
          (Finset.card_filter_le ..).trans ((List.toFinset_card_le _).trans (last_basis hl).2)
        have hef : (E ∪ F).card ≤ E.card + F.card := Finset.card_union_le ..
        obtain ⟨J, P, hJ, hcost, hz⟩ := ih (prefix_basis hl) (E ∪ F) (by
          intro b hb
          rcases Finset.mem_union.mp hb with hb | hb
          · exact prior _ hb
          · exact (Finset.mem_filter.mp hb).2)
        refine ⟨J, P, hJ, ?_, ?_⟩
        · rw [count_append, ite_eq_left hx]
          omega
        · intro Z hp hj
          apply restore Z (fun a ha => hz Z hp hj a (Finset.mem_union_left _ ha))
          intro _
          rw [wire_append, ite_eq_left (show u = n + L.length from rfl)] at hfalse ⊢
          apply gate_false (last_basis hl).1 _ hfalse
          intro b hb hbval
          exact hz Z hp hj b (Finset.mem_union_right _ (Finset.mem_filter.mpr
            ⟨List.mem_toFinset.mpr hb, hbval⟩))
      · obtain ⟨j, hji, hval⟩ : ∃ j, j ≠ i ∧ wire (L ++ [g]) (S j) u = false := by
          by_contra! h
          exact hx ⟨hfalse, fun j hji => by simpa using h j hji⟩
        obtain ⟨J, P, hJ, hcost, hz⟩ := ih (prefix_basis hl) E prior
        refine ⟨insert j J, P, by simpa [hji.symm] using hJ, ?_, ?_⟩
        · have hcard := Finset.card_insert_le j J
          rw [count_append, ite_eq_right hx]
          omega
        · intro Z hp hj
          apply restore Z (hz Z hp (fun k hk => hj k (Finset.mem_insert_of_mem hk)))
          intro _
          exact wire_false_of_subset (hj j (Finset.mem_insert_self ..)) _ hl _ hval
    · obtain ⟨J, P, hJ, hcost, hz⟩ := ih (prefix_basis hl) E prior
      refine ⟨J, P, hJ, ?_, ?_⟩
      · have he : E.card ≤ D.card := Finset.card_le_card (Finset.erase_subset ..)
        rw [count_append]
        omega
      · intro Z hp hj
        exact restore Z (hz Z hp hj) (fun h => (hu h).elim)

lemma union_size {n m q : ℕ} (S : Fin m → Finset (Fin n))
    (hs : ∀ i, (S i).card = q + 1)
    (hi : ∀ i j, i ≠ j → (S i ∩ S j).card = 1) (J : Finset (Fin m)) :
    (J.biUnion S).card ≤ J.card * q + 1 := by
  classical
  induction J using Finset.induction_on with
  | empty => simp
  | @insert j J hj ih =>
    rw [Finset.biUnion_insert, Finset.card_insert_of_notMem hj, Nat.succ_mul]
    rcases J.eq_empty_or_nonempty with he | ⟨k, hk⟩
    · simp [he, hs]
    · have hjk : j ≠ k := by rintro rfl; exact hj hk
      obtain ⟨p, hp⟩ := Finset.card_pos.mp (show 0 < (S j ∩ S k).card by rw [hi j k hjk]; decide)
      obtain ⟨hpj, hpk⟩ := Finset.mem_inter.mp hp
      have hpos : 0 < (S j ∩ J.biUnion S).card := Finset.card_pos.mpr
        ⟨p, Finset.mem_inter.mpr ⟨hpj, Finset.mem_biUnion.mpr ⟨k, hk, hpk⟩⟩⟩
      have heq := Finset.card_union_add_card_inter (S j) (J.biUnion S)
      rw [hs] at heq
      omega

lemma union_hits {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hi : ∀ i j, i ≠ j → (S i ∩ S j).card = 1) (i : Fin m)
    (J : Finset (Fin m)) (hj : i ∉ J) :
    (J.biUnion S ∩ S i).card ≤ J.card := by
  classical
  rw [Finset.biUnion_inter]
  calc
    _ ≤ ∑ j ∈ J, (S j ∩ S i).card := Finset.card_biUnion_le
    _ = ∑ _j ∈ J, 1 := by
      apply Finset.sum_congr rfl
      intro j hm
      apply hi
      rintro rfl
      exact hj hm
    _ = J.card := by simp

lemma heavy {n K T : ℕ} (h : K + T = n) (Z : Finset (Fin n)) (hz : Z.card ≤ K) :
    T ≤ (Finset.univ.filter (fun i => bits Z i = true)).card := by
  classical
  have he : Finset.univ.filter (fun i => bits Z i = true) = Zᶜ := by
    ext i
    simp [bits]
  rw [he, Finset.card_compl, Fintype.card_fin]
  omega

end PEqualNP.Outside.L_meta_924

open PEqualNP.Outside.L_meta_924

theorem PEqualNP.Outside.L_meta_924 : ∀ (q n m K T : ℕ) (S : Fin m → Finset (Fin n)), 2 ≤ q → K + T = n → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), T ≤ (Finset.univ.filter (fun i : Fin n => x i = true)).card → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) → ∀ c : ℕ, c ≤ q → c * q < K → m * c ≤ gates.length := by
  classical
  intro q n m K T S hq hkt hs hi L out hl computes c hc hk
  by_cases hc0 : c = 0
  · simp [hc0]
  have hqK : q + 1 ≤ K := by
    have h := Nat.mul_le_mul_right q (show 1 ≤ c by omega)
    simp only [Nat.one_mul] at h
    omega
  have correct (i : Fin m) (Z : Finset (Fin n)) (hz : Z.card ≤ K) :
      wire L Z (out i) = decide (∃ v ∈ S i, v ∉ Z) := by
    change Circuit.eval ⟨L, out i⟩ (List.ofFn (bits Z)) = _
    rw [computes i _ (heavy hkt Z hz)]
    simp [bits]
  have lower (i : Fin m) : c ≤ count S L i := by
    by_contra! few
    have hf : wire L (S i) (out i) = false := by
      rw [correct i (S i) (by rw [hs]; exact hqK)]
      simp
    obtain ⟨J, P, hj, hbudget, force⟩ := certificate S i L hl {out i} (by simpa using hf)
    have hb : J.card + P.card ≤ c := by
      simp only [Finset.card_singleton] at hbudget
      omega
    let Z := J.biUnion S ∪ P
    have hz : Z.card ≤ K := by
      have hp : P.card ≤ P.card * q := by
        simpa using Nat.mul_le_mul_left P.card (show 1 ≤ q by omega)
      calc
        Z.card ≤ (J.biUnion S).card + P.card := Finset.card_union_le ..
        _ ≤ (J.card * q + 1) + P.card := Nat.add_le_add_right (union_size S hs hi J) _
        _ ≤ (J.card + P.card) * q + 1 := by rw [Nat.add_mul]; omega
        _ ≤ c * q + 1 := Nat.add_le_add_right (Nat.mul_le_mul_right q hb) _
        _ ≤ K := hk
    have hv : wire L Z (out i) = false :=
      force Z Finset.subset_union_right (fun j hm => (Finset.subset_biUnion_of_mem S hm).trans
        Finset.subset_union_left) _ (Finset.mem_singleton_self _)
    rw [correct i Z hz] at hv
    have hsub : S i ⊆ Z := by
      have hall : ∀ v ∈ S i, v ∈ Z := by simpa using hv
      intro v hm
      exact hall v hm
    have hhit : (Z ∩ S i).card ≤ J.card + P.card := by
      change ((J.biUnion S ∪ P) ∩ S i).card ≤ _
      rw [Finset.union_inter_distrib_right]
      exact (Finset.card_union_le ..).trans (Nat.add_le_add (union_hits S hi i J hj)
        (Finset.card_le_card Finset.inter_subset_left))
    rw [Finset.inter_eq_right.mpr hsub, hs] at hhit
    omega
  calc
    m * c = ∑ _i : Fin m, c := by simp
    _ ≤ ∑ i : Fin m, count S L i := Finset.sum_le_sum (fun i _ => lower i)
    _ ≤ L.length := total_count S L
