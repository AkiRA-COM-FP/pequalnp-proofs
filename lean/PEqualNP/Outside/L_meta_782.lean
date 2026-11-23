import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_782

open PEqualNP.CircuitLowerBounds

abbrev Wire (n : ℕ) := Finset (Fin n) →o Prop

def inputWire {n : ℕ} (a : Fin n) : Wire n :=
  ⟨fun X => a ∈ X, fun _ _ h ha => h ha⟩

def signal {n : ℕ} (w : List (Wire n)) (j : ℕ) : Wire n :=
  w.getD j ⊥

def combine {n : ℕ} (op : GateOp) (u v : Wire n) : Wire n :=
  match op with
  | .and => u ⊓ v
  | _ => u ⊔ v

def gateWire {n : ℕ} (w : List (Wire n)) (g : Gate) : Wire n :=
  combine g.op (signal w (g.inputs.getD 0 0)) (signal w (g.inputs.getD 1 0))

def extend {n : ℕ} (w : List (Wire n)) (g : Gate) : List (Wire n) :=
  w ++ [gateWire w g]

def binary (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

noncomputable def bit {n : ℕ} (X : Finset (Fin n)) (f : Wire n) : Bool := by
  classical
  exact decide (f X)

lemma bit_true {n : ℕ} (X : Finset (Fin n)) (f : Wire n) :
    bit X f = true ↔ f X := by
  classical
  simp [bit]

lemma bit_signal {n : ℕ} (X : Finset (Fin n)) (w : List (Wire n)) (j : ℕ) :
    bit X (signal w j) = (w.map (bit X)).getD j false := by
  have hb : bit X (⊥ : Wire n) = false := by
    apply Bool.eq_false_iff.mpr
    exact fun ht => (bit_true X _).1 ht
  rw [← hb, List.getD_map]
  rfl

lemma bit_gate {n : ℕ} (X : Finset (Fin n)) (w : List (Wire n)) (g : Gate)
    (hg : binary g) :
    bit X (gateWire w g) =
      g.op.eval (g.inputs.map fun j => (w.map (bit X)).getD j false) := by
  classical
  obtain ⟨hop, hlen⟩ := hg
  obtain ⟨a, b, hab⟩ : ∃ a b, g.inputs = [a, b] := by
    cases h : g.inputs with
    | nil => simp [h] at hlen
    | cons a t =>
      cases t with
      | nil => simp [h] at hlen
      | cons b t =>
        cases t with
        | nil => exact ⟨a, b, rfl⟩
        | cons d ds => simp [h] at hlen
  simp only [gateWire, hab, List.map_cons, List.map_nil, ← bit_signal]
  rcases hop with hop | hop <;> simp [hop, combine, GateOp.eval, bit]

lemma eval_fold {n : ℕ} (X : Finset (Fin n)) (gs : List Gate)
    (hg : ∀ g ∈ gs, binary g) (w : List (Wire n)) :
    ((gs.foldl extend w).map (bit X)) =
      gs.foldl (fun bs g => bs ++ [g.op.eval (g.inputs.map fun j => bs.getD j false)])
        (w.map (bit X)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (fun t ht => hg t (List.mem_cons_of_mem _ ht))]
    simp [extend, bit_gate X w g (hg g (by simp))]

def allWires (n : ℕ) (gs : List Gate) : List (Wire n) :=
  gs.foldl extend (List.ofFn inputWire)

lemma eval_output {n : ℕ} (C : Circuit) (hg : ∀ g ∈ C.gates, binary g)
    (j : ℕ) (X : Finset (Fin n)) :
    (signal (allWires n C.gates) j) X ↔
      (C.wires (List.ofFn fun a => decide (a ∈ X))).getD j false = true := by
  rw [← bit_true, bit_signal, allWires, eval_fold X _ hg, Circuit.wires]
  have h : (List.ofFn (@inputWire n)).map (bit X) =
      List.ofFn (fun a : Fin n => decide (a ∈ X)) := by
    rw [List.map_ofFn]
    congr 1
    funext a
    change bit X (inputWire a) = decide (a ∈ X)
    by_cases ha : a ∈ X
    · simpa [ha] using (bit_true X (inputWire a)).2 ha
    · have hb := Bool.eq_false_iff.mpr (fun ht => ha ((bit_true X (inputWire a)).1 ht))
      simpa [ha] using hb
  rw [h]

noncomputable def singles {n : ℕ} (f : Wire n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun a => f {a}

lemma mem_singles {n : ℕ} (f : Wire n) (a : Fin n) :
    a ∈ singles f ↔ f {a} := by
  classical
  simp [singles]

def Private {n : ℕ} (S : Finset (Fin n)) (f : Wire n) : Prop :=
  singles f ⊆ S ∧ 2 ≤ (singles f).card

lemma input_not_private {n : ℕ} (S : Finset (Fin n)) (a : Fin n) :
    ¬ Private S (inputWire a) := by
  have h : singles (inputWire a) = {a} := by
    ext b
    rw [mem_singles]
    change a ∈ ({b} : Finset _) ↔ b ∈ ({a} : Finset _)
    simp [eq_comm]
  simp [Private, h]

lemma bot_not_private {n : ℕ} (S : Finset (Fin n)) : ¬ Private S (⊥ : Wire n) := by
  have h : singles (⊥ : Wire n) = ∅ := by
    ext b
    rw [mem_singles]
    simp
  intro hp
  have hcard := hp.2
  rw [h] at hcard
  simp at hcard

lemma signal_mem {n : ℕ} {S : Finset (Fin n)} (w : List (Wire n)) (j : ℕ)
    (h : Private S (signal w j)) : signal w j ∈ w := by
  by_cases hj : j < w.length
  · simp only [signal, List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem ..
  · simp only [signal, List.getD_eq_default _ _ (Nat.le_of_not_lt hj)] at h
    exact (bot_not_private S h).elim

def Certificate {n : ℕ} (S : Finset (Fin n)) (D : Finset (Wire n)) (bound : ℕ) : Prop :=
  ∃ B X : Finset (Fin n), B.card ≤ bound ∧ X.card ≤ bound ∧
    (∀ q ∈ X, q ∉ S) ∧ ∀ a ∉ B, ∀ f ∈ D, f {a} → f X

lemma free_certificate {n : ℕ} (S : Finset (Fin n)) (D : Finset (Wire n))
    (hfree : ∀ f ∈ D, ¬ Private S f) : Certificate S D D.card := by
  classical
  induction D using Finset.induction_on with
  | empty => exact ⟨∅, ∅, by simp, by simp, by simp, by simp⟩
  | @insert f D hf ih =>
    obtain ⟨B, X, hB, hX, hout, hdom⟩ :=
      ih (fun t ht => hfree t (Finset.mem_insert_of_mem ht))
    rw [Finset.card_insert_of_notMem hf]
    by_cases hsub : singles f ⊆ S
    · have hsmall : (singles f).card ≤ 1 := by
        have hn := hfree f (Finset.mem_insert_self ..)
        by_contra! h
        exact hn ⟨hsub, h⟩
      refine ⟨B ∪ singles f, X, ?_, by omega, hout, ?_⟩
      · exact (Finset.card_union_le _ _).trans (Nat.add_le_add hB hsmall)
      · intro a ha t ht htval
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact (ha (Finset.mem_union_right _ ((mem_singles _ _).2 htval))).elim
        · exact hdom a (fun h => ha (Finset.mem_union_left _ h)) t ht htval
    · obtain ⟨q, hq, hqS⟩ := Finset.not_subset.mp hsub
      refine ⟨B, insert q X, by omega, (Finset.card_insert_le _ _).trans (by omega), ?_, ?_⟩
      · intro r hr
        rcases Finset.mem_insert.mp hr with rfl | hr
        · exact hqS
        · exact hout r hr
      · intro a ha t ht htval
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact t.monotone (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self ..))
            ((mem_singles _ _).1 hq)
        · exact t.monotone (Finset.subset_insert ..) (hdom a ha t ht htval)

def Budget {n : ℕ} (S : Finset (Fin n)) (w : List (Wire n)) (p : ℕ) : Prop :=
  ∀ D : Finset (Wire n), (∀ f ∈ D, Private S f → f ∈ w) →
    Certificate S D (D.card + p)

lemma initial_budget {n : ℕ} (S : Finset (Fin n)) :
    Budget S (List.ofFn inputWire) 0 := by
  intro D hD
  apply free_certificate
  intro f hf hp
  obtain ⟨a, ha⟩ := List.mem_ofFn.mp (hD f hf hp)
  subst f
  exact input_not_private S a hp

lemma combine_transfer {n : ℕ} (op : GateOp) (u v : Wire n) (A X : Finset (Fin n))
    (hu : u A → u X) (hv : v A → v X) :
    combine op u v A → combine op u v X := by
  cases op <;> first | exact And.imp hu hv | exact Or.imp hu hv

noncomputable def charge {n : ℕ} (S : Finset (Fin n)) (f : Wire n) : ℕ := by
  classical
  exact if Private S f then 1 else 0

lemma extend_budget {n : ℕ} {S : Finset (Fin n)} {w : List (Wire n)} {p : ℕ}
    (g : Gate) (hbudget : Budget S w p) :
    Budget S (extend w g) (p + charge S (gateWire w g)) := by
  classical
  intro D hD
  let f := gateWire w g
  let u := signal w (g.inputs.getD 0 0)
  let v := signal w (g.inputs.getD 1 0)
  have hprior (t : Wire n) (ht : t ∈ D) (hp : Private S t) : t ∈ w ∨ t = f := by
    simpa [extend, f] using hD t ht hp
  by_cases hexpand : f ∈ D ∧ Private S f
  · let rest := D.erase f
    let parents := insert u (insert v rest)
    have hmem (t : Wire n) (ht : t ∈ parents) (hp : Private S t) : t ∈ w := by
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact signal_mem _ _ hp
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact signal_mem _ _ hp
      obtain ⟨hne, hD'⟩ := Finset.mem_erase.mp ht
      exact (hprior t hD' hp).resolve_right hne
    obtain ⟨B, X, hB, hX, hout, hdom⟩ := hbudget parents hmem
    have hcard : parents.card ≤ D.card + 1 := by
      have h₁ := Finset.card_insert_le u (insert v rest)
      have h₂ := Finset.card_insert_le v rest
      have h₃ : rest.card = D.card - 1 := Finset.card_erase_of_mem hexpand.1
      have h₄ := Finset.card_pos.mpr ⟨f, hexpand.1⟩
      dsimp only [parents]
      omega
    have hb : parents.card + p ≤ D.card + (p + 1) := by omega
    have hc : charge S f = 1 := by simp [charge, hexpand.2]
    change Certificate S D (D.card + (p + charge S f))
    rw [hc]
    refine ⟨B, X, hB.trans hb, hX.trans hb, hout, ?_⟩
    intro a ha t ht
    by_cases heq : t = f
    · subst t
      exact combine_transfer g.op u v {a} X (hdom a ha u (by simp [parents]))
        (hdom a ha v (by simp [parents]))
    · exact hdom a ha t (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨heq, ht⟩)))
  · obtain ⟨B, X, hB, hX, hout, hdom⟩ := hbudget D (by
      intro t ht hp
      apply (hprior t ht hp).resolve_right
      rintro rfl
      exact hexpand ⟨ht, hp⟩)
    exact ⟨B, X, by omega, by omega, hout, hdom⟩

lemma total_charge {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) (f : Wire n) :
    (∑ i, charge (S i) f) ≤ 1 := by
  classical
  by_cases h : ∃ i, Private (S i) f
  · obtain ⟨j, hj⟩ := h
    have hle (i : Fin m) : charge (S i) f ≤ if i = j then 1 else 0 := by
      by_cases hij : i = j
      · subst i
        simp [charge, hj]
      · have hn : ¬ Private (S i) f := by
          intro hi
          have hsub : singles f ⊆ S i ∩ S j :=
            fun a ha => Finset.mem_inter.mpr ⟨hi.1 ha, hj.1 ha⟩
          have hc := (Finset.card_le_card hsub).trans (hinter i j hij)
          exact (by omega : ¬ 2 ≤ (singles f).card) hi.2
        simp [charge, hn, hij]
    calc
      _ ≤ ∑ i : Fin m, (if i = j then 1 else 0 : ℕ) :=
        Finset.sum_le_sum fun i _ => hle i
      _ ≤ 1 := by simp
  · have hn (i : Fin m) : ¬ Private (S i) f := fun hi => h ⟨i, hi⟩
    simp [charge, hn]

lemma all_budgets {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) (gs : List Gate) :
    ∃ p : Fin m → ℕ, (∑ i, p i) ≤ gs.length ∧
      ∀ i, Budget (S i) (allWires n gs) (p i) := by
  induction gs using List.reverseRecOn with
  | nil => exact ⟨fun _ => 0, by simp, fun i => initial_budget (S i)⟩
  | append_singleton gs g ih =>
    obtain ⟨p, hp, hbudget⟩ := ih
    let w := allWires n gs
    refine ⟨fun i => p i + charge (S i) (gateWire w g), ?_, ?_⟩
    · rw [Finset.sum_add_distrib, List.length_append]
      exact Nat.add_le_add hp (total_charge S hinter _)
    · intro i
      simpa only [w, allWires, List.foldl_append, List.foldl_cons, List.foldl_nil] using
        extend_budget g (hbudget i)

lemma output_bound {n p k c : ℕ} {S : Finset (Fin n)} {w : List (Wire n)}
    (j : ℕ) (hbudget : Budget S w p) (hck : c ≤ k)
    (hcard : c + 1 ≤ (singles (signal w j)).card)
    (hpromise : ∀ X : Finset (Fin n), X.card ≤ k → (∀ q ∈ X, q ∉ S) → ¬ signal w j X) :
    c ≤ p := by
  classical
  let f := signal w j
  obtain ⟨B, X, hB, hX, hout, hdom⟩ := hbudget {f} (by
    intro t ht hp
    rw [Finset.mem_singleton.mp ht] at hp ⊢
    exact signal_mem _ _ hp)
  simp only [Finset.card_singleton] at hB hX
  by_contra! h
  have hlt : B.card < (singles f).card := by
    change c + 1 ≤ (singles f).card at hcard
    omega
  obtain ⟨a, ha, haB⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  exact hpromise X (by omega) hout (hdom a haB f (by simp) ((mem_singles f a).1 ha))

end PEqualNP.Outside.L_meta_782

open PEqualNP.Outside.L_meta_782

theorem PEqualNP.Outside.L_meta_782 : ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true → p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → ∑ i : Fin m, c i ≤ C.size := by
  intro n m k S C o c hinter _ hg _ hpromise hck hcard
  obtain ⟨p, htotal, hbudget⟩ := all_budgets S hinter C.gates
  apply le_trans (Finset.sum_le_sum fun i _ => ?_) htotal
  apply output_bound (o i) (hbudget i) (hck i)
  · have heq : singles (signal (allWires n C.gates) (o i)) =
        Finset.univ.filter (fun a : Fin n =>
          (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true) := by
      ext a
      simpa only [mem_singles, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton] using
        (eval_output C hg (o i) ({a} : Finset (Fin n)))
    rw [heq]
    exact hcard i
  · intro X hX hout htrue
    have hfalse := hpromise i (fun a => decide (a ∈ X)) (by simpa using hX) (by
      intro q hq
      exact decide_eq_false (fun hx => hout q hx hq))
    exact Bool.noConfusion (((eval_output C hg (o i) X).1 htrue).symm.trans hfalse)
