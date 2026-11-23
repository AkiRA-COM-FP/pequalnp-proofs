import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_235

private def target (x : Fin 6 → Bool) : Bool :=
  ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) ||
    ((x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5))

private def pos (b : Bool) (i : Fin 3) : Fin 6 :=
  if b then Fin.natAdd 3 i else Fin.castAdd 3 i

private def row (b : Bool) (i : Fin 3) (p : Fin 6) : Bool :=
  decide (∃ j : Fin 3, j ≠ i ∧ p = pos b j)

private def col (b : Bool) (i : Fin 3) (p : Fin 6) : Bool :=
  decide (p = pos b i)

private lemma minor_bound {α : Type} [Fintype α] (M : Matrix α α ℚ)
    {d : ℕ} (r c : Fin d → α) (h : (M.submatrix r c).det ≠ 0) : d ≤ M.rank := by
  simpa only [Matrix.rank_of_det_ne_zero h, Fintype.card_fin] using M.rank_submatrix_le r c

private lemma three_ranks {α : Type} [Fintype α] (M : Fin 3 → Matrix α α ℚ)
    (r c : Fin 3 → α)
    (off : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → M i (r j) (c k) = 1)
    (unique : ∀ i j k, M i (r k) (c k) ≠ 0 → M j (r k) (c k) ≠ 0 → i = j) :
    5 ≤ ∑ i, (M i).rank := by
  have others : ∀ i : Fin 3, ∃ j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k := by decide
  have third : ∀ i j : Fin 3, ∃ k : Fin 3, i ≠ k ∧ j ≠ k := by decide
  have positive (i : Fin 3) : 1 ≤ (M i).rank := by
    obtain ⟨j, k, hij, hik, hjk⟩ := others i
    apply minor_bound (M i) (fun _ : Fin 1 => r j) (fun _ => c k)
    rw [Matrix.det_fin_one, Matrix.submatrix_apply, off i j k hij hik hjk]
    exact one_ne_zero
  have diagonal (i j : Fin 3) (hij : i ≠ j) (small : (M i).rank ≤ 1) :
      M i (r j) (c j) ≠ 0 := by
    intro hz
    obtain ⟨k, hik, hjk⟩ := third i j
    have two : 2 ≤ (M i).rank := by
      apply minor_bound (M i) ![r j, r k] ![c j, c k]
      rw [Matrix.det_fin_two]
      change M i (r j) (c j) * M i (r k) (c k) - M i (r j) (c k) * M i (r k) (c j) ≠ 0
      rw [hz, off i j k hij hik hjk, off i k j hik hij hjk.symm]
      norm_num
    omega
  have pair (i j : Fin 3) (hij : i ≠ j) : 3 ≤ (M i).rank + (M j).rank := by
    by_contra! h
    have hi := positive i
    have hj := positive j
    obtain ⟨k, hik, hjk⟩ := third i j
    exact hij (unique i j k (diagonal i k hik (by omega)) (diagonal j k hjk (by omega)))
  have h01 := pair 0 1 (by decide)
  have h02 := pair 0 2 (by decide)
  have h12 := pair 1 2 (by decide)
  rw [Fin.sum_univ_three]
  omega

private lemma block_bound (τ : (Fin 6 → Bool) → (Fin 6 → Bool) → ℕ)
    (hτ : IsTyping 6 target τ) (b : Bool) :
    5 ≤ ∑ i : Fin 3, (typedMatrix 6 target τ (pos b i) true).rank := by
  have inputs : ∀ a j, target (row a j) = true ∧ target (col a j) = false := by decide
  have diff : ∀ a i j k, i ≠ j → i ≠ k → j ≠ k → ∀ p, row a j p ≠ col a k p →
      p = pos a i ∧ row a j p = true := by decide
  apply three_ranks _ (row b) (col b)
  · intro i j k hij hik hjk
    obtain ⟨p, ht, hd⟩ := hτ _ _ (inputs b j).1 (inputs b k).2
    obtain ⟨rfl, hb⟩ := diff b i j k hij hik hjk p hd
    exact ite_eq_left ⟨(inputs b j).1, (inputs b k).2, ht, hb⟩
  · intro i j k hi hj
    have index (t : Fin 3) (h : typedMatrix 6 target τ (pos b t) true (row b k) (col b k) ≠ 0) :
        τ (row b k) (col b k) = (pos b t).val := by
      by_contra ht
      exact h (ite_eq_right (fun he => ht he.2.2.1))
    have inj : ∀ a i j, pos a i = pos a j → i = j := by decide
    exact inj b i j (Fin.ext ((index i hi).symm.trans (index j hj)))

end PEqualNP.Outside.L_meta_235

open PEqualNP.Outside.L_meta_235

theorem PEqualNP.Outside.L_meta_235 : ¬ PEqualNP.MetaComplexity.HasTypedRank 6 (fun x : Fin 6 → Bool => ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) ||
    ((x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5))) 9 := by
  rintro ⟨τ, hτ, hsum⟩
  let w (i : Fin 6) := (typedMatrix 6 target τ i true).rank
  have lower : 10 ≤ ∑ i, w i := by
    rw [Fin.sum_univ_add (a := 3) (b := 3)]
    exact add_le_add (block_bound τ hτ false) (block_bound τ hτ true)
  have upper : (∑ i, w i) ≤ 9 := by
    refine le_trans (Finset.sum_le_sum fun i _ => ?_) hsum
    exact Finset.single_le_sum (f := fun b => (typedMatrix 6 target τ i b).rank)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ true)
  omega
