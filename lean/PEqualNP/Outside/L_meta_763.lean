import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_763

open SimpleGraph PEqualNP.MetaComplexity

private abbrev graph : SimpleGraph (Fin 6) :=
  fromRel fun i j => (i, j) ∈ ([(0, 1), (0, 2), (1, 3), (4, 5)] : List (Fin 6 × Fin 6))

private lemma acyclic : graph.IsAcyclic := by
  let f : graph →g pathGraph 6 :=
    { toFun := ![1, 2, 0, 3, 4, 5]
      map_rel' := by decide }
  apply (isAcyclic_pathGraph 6).comap f
  change ∀ i j : Fin 6, (![1, 2, 0, 3, 4, 5] : Fin 6 → Fin 6) i =
    (![1, 2, 0, 3, 4, 5] : Fin 6 → Fin 6) j → i = j
  decide

private lemma edgeCount : graph.edgeFinset.card = 4 := by decide

private abbrev cover : Finset (Fin 6) := {0, 1, 4}

private lemma covers : ∀ i j : Fin 6, graph.Adj i j → i ∈ cover ∨ j ∈ cover := by
  decide

private lemma coverBound : ∀ T : Finset (Fin 6),
    (∀ i j : Fin 6, graph.Adj i j → i ∈ T ∨ j ∈ T) → 3 ≤ T.card := by
  decide

private lemma edgeValue : ∀ x : Fin 6 → Bool,
    decide (∃ i j : Fin 6, graph.Adj i j ∧ x i = true ∧ x j = true) =
      ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) := by
  decide

private lemma sizeBound (s : ℕ) : HasCircuitSize 6
    (fun x => decide (∃ i j : Fin 6, graph.Adj i j ∧ x i = true ∧ x j = true)) s ↔
    6 ≤ s := by
  have nonempty : ∃ i j : Fin 6, graph.Adj i j := ⟨0, 1, by decide⟩
  constructor
  · intro h
    have bound := L104 6 3 s graph acyclic nonempty coverBound h
    rw [edgeCount] at bound
    omega
  · intro hs
    have h := L105 6 graph cover nonempty covers
    rw [edgeCount, show cover.card = 3 by decide] at h
    obtain ⟨C, ok, size, eval⟩ := h
    exact ⟨C, ok, size.trans hs, eval⟩

end PEqualNP.Outside.L_meta_763

theorem PEqualNP.Outside.L_meta_763 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) s ↔ 6 ≤ s := by
  intro s
  simpa only [L_meta_763.edgeValue] using L_meta_763.sizeBound s
