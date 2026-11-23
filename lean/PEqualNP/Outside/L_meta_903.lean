import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_903

open PEqualNP.MetaComplexity SimpleGraph

abbrev Edges := List (Fin 8 × Fin 8)

def graph (es : Edges) : SimpleGraph (Fin 8) :=
  SimpleGraph.fromRel (fun i j => (i, j) ∈ es)

def evalEdges (es : Edges) (x : Fin 8 → Bool) (b : Bool) : Bool :=
  es.foldl (fun z e => z || (x e.1 && x e.2)) b

lemma evalEdges_true (es : Edges) (x : Fin 8 → Bool) (b : Bool) :
    evalEdges es x b = true ↔ b = true ∨ ∃ e ∈ es, x e.1 = true ∧ x e.2 = true := by
  induction es generalizing b with
  | nil => simp [evalEdges]
  | cons e es ih =>
    change evalEdges es x (b || (x e.1 && x e.2)) = true ↔ _
    simp only [ih, Bool.or_eq_true, Bool.and_eq_true, List.mem_cons]
    grind

abbrev Separated (e d : Fin 8 × Fin 8) : Prop :=
  e.1 ≠ d.1 ∧ e.1 ≠ d.2 ∧ e.2 ≠ d.1 ∧ e.2 ≠ d.2

lemma matching_bound (m : Edges) (hm : m.Pairwise Separated) (T : Finset (Fin 8))
    (hc : ∀ e ∈ m, e.1 ∈ T ∨ e.2 ∈ T) : m.length ≤ T.card := by
  let pick (e : Fin 8 × Fin 8) := if e.1 ∈ T then e.1 else e.2
  have hn : (m.map pick).Nodup := by
    apply List.pairwise_map.mpr
    apply hm.imp
    intro e d h
    dsimp [pick, Separated] at *
    split <;> split <;> tauto
  have hs : (m.map pick).toFinset ⊆ T := by
    intro v hv
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    change (if e.1 ∈ T then e.1 else e.2) ∈ T
    split <;> grind
  simpa [List.toFinset_card_of_nodup hn] using Finset.card_le_card hs

lemma connected_graph (es : Edges) (ho : ∀ e ∈ es, e.1 < e.2)
    (hp : ∀ j : Fin 8, j ≠ 0 → ∃ i, (i, j) ∈ es) : (graph es).Connected := by
  apply (graph es).connected_iff_exists_forall_reachable.mpr
  refine ⟨0, ?_⟩
  intro j
  induction j using WellFoundedLT.induction with
  | ind j ih =>
    by_cases h : j = 0
    · subst j
      exact Reachable.refl _
    obtain ⟨i, hi⟩ := hp j h
    have hlt := ho (i, j) hi
    have ha : (graph es).Adj i j := ⟨ne_of_lt hlt, Or.inl hi⟩
    exact (ih i hlt).trans ha.reachable

lemma card_edges_le (es : Edges) [DecidableRel (graph es).Adj] :
    (graph es).edgeFinset.card ≤ es.length := by
  let ends (e : Fin 8 × Fin 8) := s(e.1, e.2)
  have hsub : (graph es).edgeFinset ⊆ (es.map ends).toFinset := by
    intro e
    induction e using Sym2.ind with
    | _ i j =>
      intro he
      have ha : (graph es).Adj i j := by simpa using he
      rcases ha.2 with h | h
      · exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨(i, j), h, rfl⟩)
      · exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨(j, i), h, Sym2.eq_swap⟩)
  exact (Finset.card_le_card hsub).trans (by simpa using (es.map ends).toFinset_card_le)

lemma exact_size (es m : Edges) (T : Finset (Fin 8)) (k : ℕ)
    (hlen : es.length = 7) (ho : ∀ e ∈ es, e.1 < e.2)
    (hp : ∀ j : Fin 8, j ≠ 0 → ∃ i, (i, j) ∈ es)
    (hc : ∀ e ∈ es, e.1 ∈ T ∨ e.2 ∈ T)
    (hm : m ⊆ es) (hd : m.Pairwise Separated) (hcard : m.length = T.card)
    (hk : k = 7 + T.card - 1) :
    ∀ s : ℕ, HasCircuitSize 8 (fun x => evalEdges es x false) s ↔ k ≤ s := by
  let _ : DecidableRel (graph es).Adj := fun i j =>
    inferInstanceAs (Decidable (i ≠ j ∧ ((i, j) ∈ es ∨ (j, i) ∈ es)))
  have hconn := connected_graph es ho hp
  have hn := hconn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.card_eq_fintype_card,
    ← SimpleGraph.edgeFinset_card] at hn
  have hle := card_edges_le es
  have hnum : (graph es).edgeFinset.card = 7 := by omega
  have htree : (graph es).IsTree := by
    apply SimpleGraph.isTree_iff_connected_and_card.mpr
    refine ⟨hconn, ?_⟩
    rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, hnum,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have hedge : ∃ i j, (graph es).Adj i j := by
    obtain ⟨i, hi⟩ := hp 1 (by decide)
    exact ⟨i, 1, (ne_of_lt (ho (i, 1) hi)), Or.inl hi⟩
  have hfun : (fun x : Fin 8 → Bool => evalEdges es x false) =
      (fun x : Fin 8 → Bool => decide (∃ i j, (graph es).Adj i j ∧ x i = true ∧ x j = true)) := by
    funext x
    rw [Bool.eq_iff_iff, evalEdges_true, decide_eq_true_iff]
    simp only [Bool.false_eq_true, false_or]
    constructor
    · rintro ⟨⟨i, j⟩, h, hi, hj⟩
      exact ⟨i, j, ⟨ne_of_lt (ho (i, j) h), Or.inl h⟩, hi, hj⟩
    · rintro ⟨i, j, h, hi, hj⟩
      rcases h.2 with h | h
      · exact ⟨(i, j), h, hi, hj⟩
      · exact ⟨(j, i), h, hj, hi⟩
  rw [hfun]
  intro s
  constructor
  · intro h
    have lower := L104 8 m.length s (graph es) htree.isAcyclic hedge (fun U hU =>
      matching_bound m hd U (fun e he =>
        hU e.1 e.2 ⟨ne_of_lt (ho e (hm he)), Or.inl (hm he)⟩)) h
    omega
  · intro h
    have upper := L105 8 (graph es) T hedge (by
      intro i j ha
      rcases ha.2 with h | h
      · exact hc (i, j) h
      · exact (hc (j, i) h).symm)
    obtain ⟨C, hC, hsize, heval⟩ := upper
    exact ⟨C, hC, by omega, heval⟩

end PEqualNP.Outside.L_meta_903

open PEqualNP.Outside.L_meta_903


theorem PEqualNP.Outside.L_meta_903 : (∀ s1 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x1 : Fin 8 → Bool => (x1 0 && x1 1) || (x1 0 && x1 2) || (x1 0 && x1 3) || (x1 0 && x1 4) || (x1 0 && x1 5) || (x1 0 && x1 6) || (x1 0 && x1 7)) s1 ↔ 7 ≤ s1) ∧ (∀ s2 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x2 : Fin 8 → Bool => (x2 0 && x2 1) || (x2 0 && x2 2) || (x2 0 && x2 3) || (x2 0 && x2 4) || (x2 0 && x2 5) || (x2 0 && x2 6) || (x2 1 && x2 7)) s2 ↔ 8 ≤ s2) ∧ (∀ s3 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x3 : Fin 8 → Bool => (x3 0 && x3 1) || (x3 0 && x3 2) || (x3 1 && x3 3) || (x3 1 && x3 4) || (x3 1 && x3 5) || (x3 1 && x3 6) || (x3 2 && x3 7)) s3 ↔ 8 ≤ s3) ∧ (∀ s4 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x4 : Fin 8 → Bool => (x4 0 && x4 1) || (x4 0 && x4 2) || (x4 0 && x4 3) || (x4 0 && x4 4) || (x4 0 && x4 5) || (x4 1 && x4 6) || (x4 1 && x4 7)) s4 ↔ 8 ≤ s4) ∧ (∀ s5 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x5 : Fin 8 → Bool => (x5 0 && x5 1) || (x5 0 && x5 2) || (x5 0 && x5 3) || (x5 0 && x5 4) || (x5 0 && x5 5) || (x5 1 && x5 6) || (x5 2 && x5 7)) s5 ↔ 9 ≤ s5) ∧ (∀ s6 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x6 : Fin 8 → Bool => (x6 0 && x6 1) || (x6 0 && x6 2) || (x6 1 && x6 3) || (x6 1 && x6 4) || (x6 1 && x6 5) || (x6 2 && x6 6) || (x6 2 && x6 7)) s6 ↔ 8 ≤ s6) ∧ (∀ s7 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x7 : Fin 8 → Bool => (x7 0 && x7 1) || (x7 0 && x7 2) || (x7 0 && x7 3) || (x7 0 && x7 4) || (x7 1 && x7 5) || (x7 1 && x7 6) || (x7 1 && x7 7)) s7 ↔ 8 ≤ s7) ∧ (∀ s8 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x8 : Fin 8 → Bool => (x8 0 && x8 1) || (x8 0 && x8 2) || (x8 1 && x8 3) || (x8 1 && x8 4) || (x8 1 && x8 5) || (x8 2 && x8 6) || (x8 6 && x8 7)) s8 ↔ 9 ≤ s8) ∧ (∀ s9 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x9 : Fin 8 → Bool => (x9 0 && x9 1) || (x9 0 && x9 2) || (x9 0 && x9 3) || (x9 0 && x9 4) || (x9 1 && x9 5) || (x9 2 && x9 6) || (x9 5 && x9 7)) s9 ↔ 9 ≤ s9) ∧ (∀ s10 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x10 : Fin 8 → Bool => (x10 0 && x10 1) || (x10 0 && x10 2) || (x10 0 && x10 3) || (x10 1 && x10 4) || (x10 1 && x10 5) || (x10 1 && x10 6) || (x10 2 && x10 7)) s10 ↔ 9 ≤ s10) ∧ (∀ s11 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x11 : Fin 8 → Bool => (x11 0 && x11 1) || (x11 0 && x11 2) || (x11 0 && x11 3) || (x11 0 && x11 4) || (x11 1 && x11 5) || (x11 1 && x11 6) || (x11 2 && x11 7)) s11 ↔ 9 ≤ s11) ∧ (∀ s12 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x12 : Fin 8 → Bool => (x12 0 && x12 1) || (x12 0 && x12 2) || (x12 0 && x12 3) || (x12 0 && x12 4) || (x12 1 && x12 5) || (x12 2 && x12 6) || (x12 3 && x12 7)) s12 ↔ 10 ≤ s12) ∧ (∀ s13 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x13 : Fin 8 → Bool => (x13 0 && x13 1) || (x13 0 && x13 2) || (x13 0 && x13 3) || (x13 1 && x13 4) || (x13 1 && x13 5) || (x13 2 && x13 6) || (x13 6 && x13 7)) s13 ↔ 9 ≤ s13) ∧ (∀ s14 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x14 : Fin 8 → Bool => (x14 0 && x14 1) || (x14 0 && x14 2) || (x14 1 && x14 3) || (x14 2 && x14 4) || (x14 3 && x14 5) || (x14 3 && x14 6) || (x14 4 && x14 7)) s14 ↔ 9 ≤ s14) ∧ (∀ s15 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x15 : Fin 8 → Bool => (x15 0 && x15 1) || (x15 0 && x15 2) || (x15 1 && x15 3) || (x15 1 && x15 4) || (x15 2 && x15 5) || (x15 5 && x15 6) || (x15 5 && x15 7)) s15 ↔ 9 ≤ s15) ∧ (∀ s16 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x16 : Fin 8 → Bool => (x16 0 && x16 1) || (x16 0 && x16 2) || (x16 0 && x16 3) || (x16 1 && x16 4) || (x16 2 && x16 5) || (x16 4 && x16 6) || (x16 4 && x16 7)) s16 ↔ 9 ≤ s16) ∧ (∀ s17 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x17 : Fin 8 → Bool => (x17 0 && x17 1) || (x17 0 && x17 2) || (x17 0 && x17 3) || (x17 1 && x17 4) || (x17 2 && x17 5) || (x17 4 && x17 6) || (x17 5 && x17 7)) s17 ↔ 9 ≤ s17) ∧ (∀ s18 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x18 : Fin 8 → Bool => (x18 0 && x18 1) || (x18 0 && x18 2) || (x18 0 && x18 3) || (x18 1 && x18 4) || (x18 1 && x18 5) || (x18 2 && x18 6) || (x18 2 && x18 7)) s18 ↔ 9 ≤ s18) ∧ (∀ s19 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x19 : Fin 8 → Bool => (x19 0 && x19 1) || (x19 0 && x19 2) || (x19 0 && x19 3) || (x19 1 && x19 4) || (x19 1 && x19 5) || (x19 2 && x19 6) || (x19 3 && x19 7)) s19 ↔ 9 ≤ s19) ∧ (∀ s20 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x20 : Fin 8 → Bool => (x20 0 && x20 1) || (x20 0 && x20 2) || (x20 0 && x20 3) || (x20 1 && x20 4) || (x20 2 && x20 5) || (x20 3 && x20 6) || (x20 4 && x20 7)) s20 ↔ 10 ≤ s20) ∧ (∀ s21 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x21 : Fin 8 → Bool => (x21 0 && x21 1) || (x21 0 && x21 2) || (x21 1 && x21 3) || (x21 1 && x21 4) || (x21 2 && x21 5) || (x21 3 && x21 6) || (x21 5 && x21 7)) s21 ↔ 10 ≤ s21) ∧ (∀ s22 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x22 : Fin 8 → Bool => (x22 0 && x22 1) || (x22 0 && x22 2) || (x22 0 && x22 3) || (x22 1 && x22 4) || (x22 1 && x22 5) || (x22 2 && x22 6) || (x22 4 && x22 7)) s22 ↔ 10 ≤ s22) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply exact_size [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7)]
        [(0, 1)] {0} 7 <;> decide
  · apply exact_size [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 7)]
        [(0, 2), (1, 7)] {0, 1} 8 <;> decide
  · apply exact_size [(0, 1), (0, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 7)]
        [(0, 2), (1, 3)] {1, 2} 8 <;> decide
  · apply exact_size [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 6), (1, 7)]
        [(0, 2), (1, 6)] {0, 1} 8 <;> decide
  · apply exact_size [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 6), (2, 7)]
        [(0, 3), (1, 6), (2, 7)] {0, 1, 2} 9 <;> decide
  · apply exact_size [(0, 1), (0, 2), (1, 3), (1, 4), (1, 5), (2, 6), (2, 7)]
        [(0, 2), (1, 3)] {1, 2} 8 <;> decide
  · apply exact_size [(0, 1), (0, 2), (0, 3), (0, 4), (1, 5), (1, 6), (1, 7)]
        [(0, 2), (1, 5)] {0, 1} 8 <;> decide
  · apply exact_size [(0, 1), (0, 2), (1, 3), (1, 4), (1, 5), (2, 6), (6, 7)]
        [(0, 2), (1, 3), (6, 7)] {0, 1, 6} 9 <;> decide
  · apply exact_size [(0, 1), (0, 2), (0, 3), (0, 4), (1, 5), (2, 6), (5, 7)]
        [(0, 3), (1, 5), (2, 6)] {0, 2, 5} 9 <;> decide
  · apply exact_size [(0, 1), (0, 2), (0, 3), (1, 4), (1, 5), (1, 6), (2, 7)]
        [(0, 3), (1, 4), (2, 7)] {0, 1, 2} 9 <;> decide
  · apply exact_size [(0, 1), (0, 2), (0, 3), (0, 4), (1, 5), (1, 6), (2, 7)]
        [(0, 3), (1, 5), (2, 7)] {0, 1, 2} 9 <;> decide
  · apply exact_size [(0, 1), (0, 2), (0, 3), (0, 4), (1, 5), (2, 6), (3, 7)]
        [(0, 4), (1, 5), (2, 6), (3, 7)] {0, 1, 2, 3} 10 <;> decide
  · apply exact_size [(0, 1), (0, 2), (0, 3), (1, 4), (1, 5), (2, 6), (6, 7)]
        [(0, 3), (1, 4), (2, 6)] {0, 1, 6} 9 <;> decide
  · apply exact_size [(0, 1), (0, 2), (1, 3), (2, 4), (3, 5), (3, 6), (4, 7)]
        [(0, 1), (2, 4), (3, 5)] {0, 3, 4} 9 <;> decide
  · apply exact_size [(0, 1), (0, 2), (1, 3), (1, 4), (2, 5), (5, 6), (5, 7)]
        [(0, 2), (1, 3), (5, 6)] {0, 1, 5} 9 <;> decide
  · apply exact_size [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (4, 6), (4, 7)]
        [(0, 3), (1, 4), (2, 5)] {0, 2, 4} 9 <;> decide
  · apply exact_size [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (4, 6), (5, 7)]
        [(0, 3), (1, 4), (2, 5)] {0, 4, 5} 9 <;> decide
  · apply exact_size [(0, 1), (0, 2), (0, 3), (1, 4), (1, 5), (2, 6), (2, 7)]
        [(0, 3), (1, 4), (2, 6)] {0, 1, 2} 9 <;> decide
  · apply exact_size [(0, 1), (0, 2), (0, 3), (1, 4), (1, 5), (2, 6), (3, 7)]
        [(0, 3), (1, 4), (2, 6)] {1, 2, 3} 9 <;> decide
  · apply exact_size [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (3, 6), (4, 7)]
        [(0, 1), (2, 5), (3, 6), (4, 7)] {0, 2, 3, 4} 10 <;> decide
  · apply exact_size [(0, 1), (0, 2), (1, 3), (1, 4), (2, 5), (3, 6), (5, 7)]
        [(0, 2), (1, 4), (3, 6), (5, 7)] {0, 1, 3, 5} 10 <;> decide
  · apply exact_size [(0, 1), (0, 2), (0, 3), (1, 4), (1, 5), (2, 6), (4, 7)]
        [(0, 3), (1, 5), (2, 6), (4, 7)] {0, 1, 2, 4} 10 <;> decide
