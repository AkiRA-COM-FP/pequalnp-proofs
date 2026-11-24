import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1642

open PEqualNP.CircuitLowerBounds

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma fold_length (gs : List Gate) (x : List Bool) :
    (gs.foldl step x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [step]; omega

private lemma fold_read (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (gs.foldl step x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

variable {N : ℕ} {gs : List Gate} {ev : ℕ → (Fin N → Bool) → Bool}

private def Evaluates (gs : List Gate) (ev : ℕ → (Fin N → Bool) → Bool) : Prop :=
  ∀ w x, ev w x = Circuit.eval ⟨gs, w⟩ (List.ofFn x)

private def Earlier (N : ℕ) (gs : List Gate) : Prop :=
  ∀ (k : Fin gs.length), ∀ e ∈ (gs.get k).inputs, e < N + k.val

private lemma read_input (he : Evaluates gs ev) (p : Fin N) (x : Fin N → Bool) :
    ev p.val x = x p := by
  rw [he]
  change (gs.foldl step (List.ofFn x)).getD p.val false = _
  rw [fold_read _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, p.isLt]

private lemma read_absent (he : Evaluates gs ev) {w : ℕ} (h : N + gs.length ≤ w)
    (x : Fin N → Bool) : ev w x = false := by
  rw [he]
  change (gs.foldl step (List.ofFn x)).getD w false = _
  exact List.getD_eq_default _ _ (by simpa [fold_length] using h)

private lemma read_gate (he : Evaluates gs ev) (hw : Earlier N gs) (k : Fin gs.length)
    (x : Fin N → Bool) :
    ev (N + k.val) x = (gs.get k).op.eval ((gs.get k).inputs.map fun i => ev i x) := by
  let old := (gs.take k.val).foldl step (List.ofFn x)
  have hlen : old.length = N + k.val := by
    simp [old, fold_length]
  have splitG : gs = gs.take k.val ++ gs[k.val] :: gs.drop (k.val + 1) := by
    simp [List.take_append_drop]
  rw [he]
  change (gs.foldl step (List.ofFn x)).getD (N + k.val) false = _
  have foldSplit := congrArg (fun l : List Gate => l.foldl step (List.ofFn x)) splitG
  conv_lhs => rw [foldSplit, List.foldl_append, List.foldl_cons]
  change ((gs.drop (k.val + 1)).foldl step (step old (gs.get k))).getD (N + k.val) false = _
  rw [fold_read _ _ _ (by simp [step, hlen])]
  have hval : (step old (gs.get k)).getD (N + k.val) false =
      (gs.get k).op.eval ((gs.get k).inputs.map fun i => old.getD i false) := by
    simp [step, ← hlen, List.getD_eq_getElem?_getD]
  rw [hval]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [he]
  change old.getD i false = (gs.foldl step (List.ofFn x)).getD i false
  conv_rhs => rw [← List.take_append_drop k.val gs, List.foldl_append]
  exact (fold_read _ old i (hlen ▸ hw k i hi)).symm

private def AndRule (gs : List Gate) (ev : ℕ → (Fin N → Bool) → Bool) : Prop :=
  ∀ k : Fin gs.length, (gs.get k).op = .and → ∀ x, ev (N + k.val) x = true ↔
    ∀ e ∈ (gs.get k).inputs, ev e x = true

private def OrRule (gs : List Gate) (ev : ℕ → (Fin N → Bool) → Bool) : Prop :=
  ∀ k : Fin gs.length, (gs.get k).op = .or → ∀ x, ev (N + k.val) x = true ↔
    ∃ e ∈ (gs.get k).inputs, ev e x = true

private lemma rules (he : Evaluates gs ev) (hw : Earlier N gs) : AndRule gs ev ∧ OrRule gs ev := by
  constructor <;> intro k hop x <;> rw [read_gate he hw, hop] <;>
    simp [GateOp.eval, List.all_map, List.any_map]

private lemma mono_eval (he : Evaluates gs ev) (hw : Earlier N gs)
    (ops : ∀ k : Fin gs.length, (gs.get k).op = .and ∨ (gs.get k).op = .or)
    (ha : AndRule gs ev) (ho : OrRule gs ev) (x y : Fin N → Bool)
    (hxy : ∀ v, x v = true → y v = true) (w : ℕ) : ev w x = true → ev w y = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hx
    by_cases hi : w < N
    · let p : Fin N := ⟨w, hi⟩
      exact (read_input he p y).trans (hxy p ((read_input he p x).symm.trans hx))
    by_cases hout : N + gs.length ≤ w
    · simp [read_absent he hout] at hx
    let k : Fin gs.length := ⟨w - N, by omega⟩
    have hk : w = N + k.val := by dsimp [k]; omega
    rw [hk] at hx ⊢
    rcases ops k with hop | hop
    · apply (ha k hop y).mpr
      intro e hmem
      exact ih e (hk ▸ hw k e hmem) ((ha k hop x).mp hx e hmem)
    · obtain ⟨e, hmem, hex⟩ := (ho k hop x).mp hx
      exact (ho k hop y).mpr ⟨e, hmem, ih e (hk ▸ hw k e hmem) hex⟩

private def Good {α : Type*} [DecidableEq α] (T : ℕ → Finset α)
    (St : ℕ → α → Prop) (mark : α) (D : Finset α) (w : ℕ) : Prop :=
  (T w \ D).card ≤ 1 ∧ ∀ r ∈ T w \ D, r ≠ mark → St w r

private lemma good_mono {α : Type*} [DecidableEq α] {T : ℕ → Finset α}
    {St : ℕ → α → Prop} {mark : α} {D E : Finset α} {w : ℕ}
    (h : Good T St mark D w) (hDE : D ⊆ E) : Good T St mark E w := by
  have hsub : T w \ E ⊆ T w \ D := by
    intro r hr
    obtain ⟨ht, hn⟩ := Finset.mem_sdiff.mp hr
    exact Finset.mem_sdiff.mpr ⟨ht, fun hd => hn (hDE hd)⟩
  exact ⟨(Finset.card_le_card hsub).trans h.1, fun r hr => h.2 r (hsub hr)⟩

private lemma sweep {N m : ℕ} {T : ℕ → Finset (Fin N)} {St : ℕ → Fin N → Prop}
    {mark : Fin N} {low : ℕ → Prop} {B : Finset (Fin m)}
    (inp : ∀ w < N, low w → Good T St mark ∅ w)
    (advance : ∀ (k : Fin m) (D : Finset (Fin N)), mark ∉ D →
      (∀ e < N + k.val, low e → Good T St mark D e) → low (N + k.val) →
      Good T St mark D (N + k.val) ∨
        ∃ r ≠ mark, k ∈ B ∧ Good T St mark (insert r D) (N + k.val)) :
    ∃ D : Finset (Fin N), mark ∉ D ∧ D.card ≤ B.card ∧
      ∀ w < N + m, low w → Good T St mark D w := by
  classical
  let before (n : ℕ) := B.filter (fun k => k.val < n)
  have allStages (n : ℕ) (hn : n ≤ m) : ∃ D : Finset (Fin N), mark ∉ D ∧
      D.card ≤ (before n).card ∧ ∀ w < N + n, low w → Good T St mark D w := by
    induction n with
    | zero => exact ⟨∅, by simp, by simp, by simpa using inp⟩
    | succ n ih =>
      obtain ⟨D, hmark, hcard, hold⟩ := ih (by omega)
      let k : Fin m := ⟨n, by omega⟩
      have hsub : before n ⊆ before (n+1) := by
        intro i hi
        obtain ⟨hb, hi⟩ := Finset.mem_filter.mp hi
        exact Finset.mem_filter.mpr ⟨hb, by omega⟩
      have next : (low (N+n) → Good T St mark D (N+n)) ∨
          ∃ r ≠ mark, k ∈ B ∧ (low (N+n) → Good T St mark (insert r D) (N+n)) := by
        by_cases hz : low (N+n)
        · rcases advance k D hmark hold hz with hg | ⟨r, hr, hb, hg⟩
          · exact Or.inl fun _ => hg
          · exact Or.inr ⟨r, hr, hb, fun _ => hg⟩
        · exact Or.inl fun h => (hz h).elim
      rcases next with hnext | ⟨r, hr, hb, hnext⟩
      · refine ⟨D, hmark, hcard.trans (Finset.card_le_card hsub), ?_⟩
        intro w hw
        rcases Nat.lt_or_ge w (N+n) with h | h
        · exact hold w h
        · have : w = N+n := by omega
          exact this ▸ hnext
      · have hlt : (before n).card < (before (n+1)).card := by
          apply Finset.card_lt_card
          refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
          intro heq
          have hmem : k ∈ before (n+1) := Finset.mem_filter.mpr ⟨hb, Nat.lt_succ_self n⟩
          rw [← heq] at hmem
          exact (Nat.lt_irrefl n) (Finset.mem_filter.mp hmem).2
        refine ⟨insert r D, by simpa [hmark] using Ne.symm hr, ?_, ?_⟩
        · have := Finset.card_insert_le r D
          omega
        · intro w hw
          rcases Nat.lt_or_ge w (N+n) with h | h
          · intro hz
            exact good_mono (hold w h hz) (Finset.subset_insert _ _)
          · have : w = N+n := by omega
            exact this ▸ hnext
  obtain ⟨D, hd, hc, hg⟩ := allStages m le_rfl
  exact ⟨D, hd, hc.trans (Finset.card_le_card (Finset.filter_subset _ _)), hg⟩

private lemma pair_of_inputs {l : List ℕ} (h₁ : 1 ≤ l.length) (h₂ : l.length ≤ 2) :
    ∃ a ∈ l, ∃ b ∈ l, ∀ e ∈ l, e = a ∨ e = b := by
  rcases l with _ | ⟨a, _ | ⟨b, t⟩⟩
  · simp at h₁
  · exact ⟨a, by simp, a, by simp, by simp⟩
  · have : t = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at h₂; omega)
    subst t
    exact ⟨a, by simp, b, by simp, by simp⟩

private lemma or_step {N : ℕ} {T : ℕ → Finset (Fin N)} {St : ℕ → Fin N → Prop}
    {mark : Fin N} {D : Finset (Fin N)} {w : ℕ} {l : List ℕ} {charge : Prop}
    (hmark : mark ∉ D) (h₁ : 1 ≤ l.length) (h₂ : l.length ≤ 2)
    (hgood : ∀ e ∈ l, Good T St mark D e)
    (hT : ∀ p, p ∈ T w ↔ ∃ e ∈ l, p ∈ T e)
    (hSt : ∀ e ∈ l, ∀ r, St e r → St w r)
    (hcharge : ∀ r s, r ≠ mark → r ≠ s → r ∈ T w → s ∈ T w →
      St w r → (s ≠ mark → St w s) → (∃ e ∈ l, mark ∉ T e) → charge) :
    Good T St mark D w ∨ ∃ r ≠ mark, charge ∧ Good T St mark (insert r D) w := by
  classical
  have trace (p : Fin N) (hp : p ∈ T w \ D) (hne : p ≠ mark) : St w p := by
    obtain ⟨ht, hd⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨e, he, hp'⟩ := (hT p).mp ht
    exact hSt e he p ((hgood e he).2 p (Finset.mem_sdiff.mpr ⟨hp', hd⟩) hne)
  by_cases hcard : (T w \ D).card ≤ 1
  · exact Or.inl ⟨hcard, trace⟩
  obtain ⟨a, ha, b, hb, hab⟩ := pair_of_inputs h₁ h₂
  have hsub : T w \ D ⊆ (T a \ D) ∪ (T b \ D) := by
    intro p hp
    obtain ⟨ht, hd⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨e, he, hp'⟩ := (hT p).mp ht
    rcases hab e he with rfl | rfl
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hp', hd⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hp', hd⟩)
  have htwo : (T w \ D).card ≤ 2 := by
    have hu := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hca := (hgood a ha).1
    have hcb := (hgood b hb).1
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (Nat.lt_of_not_ge hcard)
  have pick : ∃ r ∈ T w \ D, ∃ s ∈ T w \ D, r ≠ mark ∧ r ≠ s := by
    by_cases hm : x = mark
    · exact ⟨y, hy, x, hx, hm ▸ hxy.symm, hxy.symm⟩
    · exact ⟨x, hx, y, hy, hm, hxy⟩
  obtain ⟨r, hr, s, hs, hrm, hrs⟩ := pick
  have ⟨hrt, hrd⟩ := Finset.mem_sdiff.mp hr
  obtain ⟨e, he, hret⟩ := (hT r).mp hrt
  have hmiss : mark ∉ T e := by
    intro hm
    exact hrm (Finset.card_le_one.mp (hgood e he).1 r (Finset.mem_sdiff.mpr ⟨hret, hrd⟩)
      mark (Finset.mem_sdiff.mpr ⟨hm, hmark⟩))
  have hc := hcharge r s hrm hrs hrt (Finset.mem_sdiff.mp hs).1 (trace r hr hrm)
    (trace s hs) ⟨e, he, hmiss⟩
  refine Or.inr ⟨r, hrm, hc, ?_, ?_⟩
  · rw [Finset.sdiff_insert, Finset.card_erase_of_mem hr]
    omega
  · intro p hp
    rw [Finset.sdiff_insert] at hp
    exact trace p (Finset.mem_of_mem_erase hp)

private lemma and_step {N : ℕ} {T : ℕ → Finset (Fin N)} {St : ℕ → Fin N → Prop}
    {mark : Fin N} {D : Finset (Fin N)} {w e : ℕ} {charge : Prop}
    (hchosen : ∀ r ∈ T w \ D, r ≠ mark →
      Good T St mark D e ∧ T w ⊆ T e ∧ (St e r → charge)) :
    Good T St mark D w ∨ ∃ r ≠ mark, charge ∧ Good T St mark (insert r D) w := by
  classical
  by_cases active : ∃ r ∈ T w \ D, r ≠ mark
  · obtain ⟨r, hr, hrm⟩ := active
    obtain ⟨hg, hsub, hc⟩ := hchosen r hr hrm
    have hsub' : T w \ D ⊆ T e \ D := by
      intro s hs
      obtain ⟨ht, hd⟩ := Finset.mem_sdiff.mp hs
      exact Finset.mem_sdiff.mpr ⟨hsub ht, hd⟩
    have hcard := (Finset.card_le_card hsub').trans hg.1
    have hempty : T w \ insert r D = ∅ := by
      rw [← Finset.card_eq_zero, Finset.sdiff_insert, Finset.card_erase_of_mem hr]
      omega
    exact Or.inr ⟨r, hrm, hc (hg.2 r (hsub' hr) hrm), by simp [Good, hempty]⟩
  · have eqmark (r : Fin N) (hr : r ∈ T w \ D) : r = mark := by
      by_contra hn
      exact active ⟨r, hr, hn⟩
    exact Or.inl ⟨Finset.card_le_one.mpr fun r hr s hs => (eqmark r hr).trans (eqmark s hs).symm,
      fun r hr hn => (hn (eqmark r hr)).elim⟩

private def off (S : Finset (Fin N)) (v : Fin N) : Bool := decide (v ∉ S)

private def single (p v : Fin N) : Bool := decide (v = p)

private def raised (S : Finset (Fin N)) (r v : Fin N) : Bool := decide (v ∉ S ∨ v = r)

private def Rest (S : Finset (Fin N)) (p₀ p₁ r : Fin N) : Prop :=
  r ∈ S ∧ r ≠ p₀ ∧ r ≠ p₁

private def Anchor (ev : ℕ → (Fin N → Bool) → Bool) (p₀ p₁ : Fin N) (w : ℕ) : Prop :=
  ev w (single p₀) = true ∨ ev w (single p₁) = true

private noncomputable def tokens (ev : ℕ → (Fin N → Bool) → Bool) (S : Finset (Fin N))
    (p₀ p₁ : Fin N) (w : ℕ) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter fun r => (r = p₀ ∧ Anchor ev p₀ p₁ w) ∨
    (Rest S p₀ p₁ r ∧ ev w (raised S r) = true)

private lemma mem_tokens {S : Finset (Fin N)} {p₀ p₁ r : Fin N} {w : ℕ} :
    r ∈ tokens ev S p₀ p₁ w ↔ (r = p₀ ∧ Anchor ev p₀ p₁ w) ∨
    (Rest S p₀ p₁ r ∧ ev w (raised S r) = true) := by
  classical
  simp [tokens]

private lemma mem_mark {S : Finset (Fin N)} {p₀ p₁ : Fin N} {w : ℕ} :
    p₀ ∈ tokens ev S p₀ p₁ w ↔ Anchor ev p₀ p₁ w := by simp [mem_tokens, Rest]

private lemma mem_real {S : Finset (Fin N)} {p₀ p₁ r : Fin N} {w : ℕ}
    (hm : r ≠ p₀) (hr : r ∈ tokens ev S p₀ p₁ w) : Rest S p₀ p₁ r ∧ ev w (raised S r) = true :=
  (mem_tokens.mp hr).resolve_left fun h => hm h.1

private lemma tokens_and (ha : AndRule gs ev) {S : Finset (Fin N)} {p₀ p₁ : Fin N}
    {k : Fin gs.length} (hop : (gs.get k).op = .and) {e : ℕ} (he : e ∈ (gs.get k).inputs) :
    tokens ev S p₀ p₁ (N+k.val) ⊆ tokens ev S p₀ p₁ e := by
  intro r hr
  apply mem_tokens.mpr
  rcases mem_tokens.mp hr with ⟨hm, h₀ | h₁⟩ | ⟨hr, hx⟩
  · exact Or.inl ⟨hm, Or.inl ((ha k hop _).mp h₀ e he)⟩
  · exact Or.inl ⟨hm, Or.inr ((ha k hop _).mp h₁ e he)⟩
  · exact Or.inr ⟨hr, (ha k hop _).mp hx e he⟩

private lemma tokens_or (ho : OrRule gs ev) {S : Finset (Fin N)} {p₀ p₁ : Fin N}
    {k : Fin gs.length} (hop : (gs.get k).op = .or) (r : Fin N) :
    r ∈ tokens ev S p₀ p₁ (N+k.val) ↔ ∃ e ∈ (gs.get k).inputs, r ∈ tokens ev S p₀ p₁ e := by
  constructor
  · intro h
    rcases mem_tokens.mp h with ⟨hm, h₀ | h₁⟩ | ⟨hr, hx⟩
    · obtain ⟨e, he, hx⟩ := (ho k hop _).mp h₀
      exact ⟨e, he, mem_tokens.mpr (Or.inl ⟨hm, Or.inl hx⟩)⟩
    · obtain ⟨e, he, hx⟩ := (ho k hop _).mp h₁
      exact ⟨e, he, mem_tokens.mpr (Or.inl ⟨hm, Or.inr hx⟩)⟩
    · obtain ⟨e, he, hx⟩ := (ho k hop _).mp hx
      exact ⟨e, he, mem_tokens.mpr (Or.inr ⟨hr, hx⟩)⟩
  · rintro ⟨e, he, h⟩
    apply mem_tokens.mpr
    rcases mem_tokens.mp h with ⟨hm, h₀ | h₁⟩ | ⟨hr, hx⟩
    · exact Or.inl ⟨hm, Or.inl ((ho k hop _).mpr ⟨e, he, h₀⟩)⟩
    · exact Or.inl ⟨hm, Or.inr ((ho k hop _).mpr ⟨e, he, h₁⟩)⟩
    · exact Or.inr ⟨hr, (ho k hop _).mpr ⟨e, he, hx⟩⟩

private def StarLaw (N : ℕ) (gs : List Gate) (St : ℕ → Fin N → Prop) : Prop :=
  ∀ w p, St w p ↔ ∀ Z : Set ℕ, w ∈ Z →
    (∀ k : Fin gs.length, N + k.val ∈ Z → (gs.get k).op = .or →
      ∀ e ∈ (gs.get k).inputs, e ∈ Z) → p.val ∈ Z

private lemma star_or {St : ℕ → Fin N → Prop} (hSt : StarLaw N gs St)
    {k : Fin gs.length} (hop : (gs.get k).op = .or) (e : ℕ) (he : e ∈ (gs.get k).inputs)
    (r : Fin N) (h : St e r) : St (N+k.val) r := by
  apply (hSt _ _).mpr
  intro Z hw hZ
  exact (hSt _ _).mp h Z (hZ k hw hop e he) hZ

private lemma star_true {St : ℕ → Fin N → Prop} (hSt : StarLaw N gs St) (he : Evaluates gs ev)
    (ho : OrRule gs ev) {w : ℕ} {r : Fin N} (h : St w r) : ev w (single r) = true := by
  by_contra hn
  let Z : Set ℕ := {i | ev i (single r) ≠ true}
  have hr := (hSt w r).mp h Z hn (by
    intro k hk hop e hmem htrue
    exact hk ((ho k hop _).mpr ⟨e, hmem, htrue⟩))
  exact hr ((read_input he r (single r)).trans (by simp [single]))

private lemma input_good {St : ℕ → Fin N → Prop} (hSt : StarLaw N gs St) (he : Evaluates gs ev)
    (S : Finset (Fin N)) (p₀ p₁ v : Fin N) (hz : ev v.val (off S) = false) :
    Good (tokens ev S p₀ p₁) St p₀ ∅ v.val := by
  classical
  have hv : v ∈ S := by simpa [read_input he, off] using hz
  have hreal (r : Fin N) (hr : r ∈ tokens ev S p₀ p₁ v.val) (hn : r ≠ p₀) :
      v = r ∧ r ≠ p₁ := by
    obtain ⟨hrest, hx⟩ := mem_real hn hr
    exact ⟨by simpa [read_input he, raised, hv] using hx, hrest.2.2⟩
  have hmarked (hm : p₀ ∈ tokens ev S p₀ p₁ v.val) : v = p₀ ∨ v = p₁ := by
    simpa [Anchor, read_input he, single] using mem_mark.mp hm
  refine ⟨?_, ?_⟩
  · simp only [Finset.sdiff_empty]
    apply Finset.card_le_one.mpr
    intro a ha b hb
    by_cases ham : a = p₀
    · subst a
      by_contra hne
      obtain ⟨hvb, hbp⟩ := hreal b hb (Ne.symm hne)
      rcases hmarked ha with h | h
      · exact hne (h.symm.trans hvb)
      · exact hbp (hvb.symm.trans h)
    · obtain ⟨hva, hap⟩ := hreal a ha ham
      by_cases hbm : b = p₀
      · subst b
        rcases hmarked hb with h | h
        · exact (ham (hva.symm.trans h)).elim
        · exact (hap (hva.symm.trans h)).elim
      · exact hva.symm.trans (hreal b hb hbm).1
  · intro r hr hn
    have hvr := (hreal r (Finset.mem_sdiff.mp hr).1 hn).1
    subst r
    exact (hSt _ _).mpr fun _ h _ => h

private lemma covers_lines (he : Evaluates gs ev) (hw : Earlier N gs)
    (ops : ∀ k : Fin gs.length, (gs.get k).op = .and ∨ (gs.get k).op = .or)
    (ha : AndRule gs ev) (ho : OrRule gs ev) (L : Fin N → Finset (Fin N))
    (hi : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    {i r s : Fin N} (hr : r ∈ L i) (hs : s ∈ L i) (hne : r ≠ s) {w : ℕ}
    (er : ev w (single r) = true) (es : ev w (single s) = true) (t : Fin N) (ht : t ≠ i) :
    ev w (off (L t)) = true := by
  have hit (p : Fin N) (hp : p ∉ L t) (ep : ev w (single p) = true) : ev w (off (L t)) = true := by
    apply mono_eval he hw ops ha ho (single p) _ _ w ep
    intro v hv
    have : v = p := by simpa [single] using hv
    simpa [off, this] using hp
  by_cases hr' : r ∈ L t
  · apply hit s _ es
    intro hs'
    exact hne (Finset.card_le_one.mp (hi t i ht).le r (Finset.mem_inter.mpr ⟨hr', hr⟩)
      s (Finset.mem_inter.mpr ⟨hs', hs⟩))
  · exact hit r hr' er

end PEqualNP.Outside.L_meta_1642

open PEqualNP.Outside.L_meta_1642

theorem PEqualNP.Outside.L_meta_1642 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ∀ o0 : ℕ, ev o0 (fun v : Fin N => decide (v ∉ L i0)) = false → ev o0 (fun v : Fin N => decide (v = p0)) = true → ev o0 (fun v : Fin N => decide (v = p1)) = true →
    (∀ r ∈ L i0, r ≠ p0 → r ≠ p1 → ev o0 (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true) →
    ∀ St : ℕ → Fin N → Prop,
    (∀ (w : ℕ) (p : Fin N), St w p ↔ ∀ Zs : Set ℕ, w ∈ Zs → (∀ k : Fin gates.length, N + (k : ℕ) ∈ Zs → (gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get k).inputs, e ∈ Zs) → (p : ℕ) ∈ Zs) →
    ∀ ch : Fin gates.length → ℕ, (∀ a : Fin gates.length, ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ev (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false ∧ ∃ r ∈ L i0, r ≠ p0 ∧ r ≠ p1 ∧ ev (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true) → ch a ∈ (gates.get a).inputs ∧ ev (ch a) (fun v : Fin N => decide (v ∉ L i0)) = false) →
    ∀ Au Xs : Finset (Fin gates.length), (∀ a : Fin gates.length, (((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ev (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false ∧ ∃ r ∈ L i0, r ≠ p0 ∧ r ≠ p1 ∧ ev (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true) ∧ ∃ r ∈ L i0, r ≠ p0 ∧ r ≠ p1 ∧ ev (N + (a : ℕ)) (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true ∧ St (ch a) r) → a ∈ Au) →
      (∀ g : Fin gates.length, ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ev (N + (g : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false ∧ (∀ t : Fin N, t ≠ i0 → ev (N + (g : ℕ)) (fun v : Fin N => decide (v ∉ L t)) = true) ∧
        ¬ ∀ e ∈ (gates.get g).inputs, (ev e (fun v : Fin N => decide (v = p0)) = true ∨ ev e (fun v : Fin N => decide (v = p1)) = true)) → g ∈ Xs) → q - 1 ≤ Au.card + Xs.card := by
  classical
  intro q N L i₀ p₀ p₁ _ _ hcard hi _ hne hp₀ hp₁ gs hgate hlen hw ev he
    o hz ho₀ _ hout St hSt ch hch Au Xs hAu hXs
  let S := L i₀
  let T := tokens ev S p₀ p₁
  have hEval : Evaluates gs ev := he
  have hEarly : Earlier N gs := hw
  have hStar : StarLaw N gs St := hSt
  obtain ⟨ha, ho⟩ := rules hEval hEarly
  have ops (k : Fin gs.length) := (hgate (gs.get k) (gs.get_mem k)).1
  have advance (k : Fin gs.length) (D : Finset (Fin N)) (hmark : p₀ ∉ D)
      (hold : ∀ e < N + k.val, ev e (off S) = false → Good T St p₀ D e)
      (hz' : ev (N+k.val) (off S) = false) :
      Good T St p₀ D (N+k.val) ∨
        ∃ r ≠ p₀, k ∈ Au ∪ Xs ∧ Good T St p₀ (insert r D) (N+k.val) := by
    rcases ops k with hop | hop
    · apply and_step (e := ch k)
      intro r hr hrm
      obtain ⟨hrest, hv⟩ := mem_real hrm (Finset.mem_sdiff.mp hr).1
      have hex : ∃ u ∈ S, u ≠ p₀ ∧ u ≠ p₁ ∧ ev (N+k.val) (raised S u) = true :=
        ⟨r, hrest.1, hrest.2.1, hrest.2.2, hv⟩
      obtain ⟨hmem, hlow⟩ := hch k ⟨hop, hz', hex⟩
      refine ⟨hold _ (hw k _ hmem) hlow, tokens_and ha hop hmem, ?_⟩
      intro hsr
      exact Finset.mem_union_left _ (hAu k ⟨⟨hop, hz', hex⟩,
        r, hrest.1, hrest.2.1, hrest.2.2, hv, hsr⟩)
    · apply or_step (l := (gs.get k).inputs) hmark (hlen k) (hgate _ (gs.get_mem k)).2
      · intro e hmem
        apply hold e (hw k e hmem)
        apply Bool.eq_false_iff.mpr
        intro htrue
        have ht := (ho k hop (off S)).mpr ⟨e, hmem, htrue⟩
        simp [hz'] at ht
      · exact tokens_or ho hop
      · exact star_or hStar hop
      · intro r s hrm hrs hrt hst hrstar hsstar hmiss
        obtain ⟨hrest, _⟩ := mem_real hrm hrt
        have er := star_true hStar hEval ho hrstar
        have existsPt : ∃ u ∈ S, r ≠ u ∧ ev (N+k.val) (single u) = true := by
          by_cases hsm : s = p₀
          · subst s
            rcases mem_mark.mp hst with h₀ | h₁
            · exact ⟨p₀, hp₀, hrm, h₀⟩
            · exact ⟨p₁, hp₁, hrest.2.2, h₁⟩
          · exact ⟨s, (mem_real hsm hst).1.1, hrs, star_true hStar hEval ho (hsstar hsm)⟩
        obtain ⟨u, hu, hru, eu⟩ := existsPt
        apply Finset.mem_union_right Au
        apply hXs k
        refine ⟨hop, hz', covers_lines hEval hEarly ops ha ho L hi hrest.1 hu hru er eu, ?_⟩
        obtain ⟨e, hmem, hm⟩ := hmiss
        exact fun hall => hm (mem_mark.mpr (hall e hmem))
  obtain ⟨D, hmark, hbudget, hall⟩ := sweep (N := N) (B := Au ∪ Xs)
    (low := fun w => ev w (off S) = false) (T := T) (St := St) (mark := p₀)
    (fun w hw' => input_good hStar hEval S p₀ p₁ ⟨w, hw'⟩) advance
  have hobound : o < N + gs.length := by
    by_contra! h
    have hf := read_absent hEval h (single p₀)
    exact Bool.noConfusion (hf.symm.trans ho₀)
  have hg := hall o hobound hz
  have htag : p₀ ∈ T o \ D := Finset.mem_sdiff.mpr ⟨mem_mark.mpr (Or.inl ho₀), hmark⟩
  have sub : (S.erase p₀).erase p₁ ⊆ D := by
    intro r hr
    obtain ⟨hne₁, hr'⟩ := Finset.mem_erase.mp hr
    obtain ⟨hne₀, hS⟩ := Finset.mem_erase.mp hr'
    by_contra hd
    have ht : r ∈ T o := mem_tokens.mpr
      (Or.inr ⟨⟨hS, hne₀, hne₁⟩, hout r hS hne₀ hne₁⟩)
    exact hne₀ (Finset.card_le_one.mp hg.1 r (Finset.mem_sdiff.mpr ⟨ht, hd⟩) p₀ htag)
  calc
    q - 1 = ((S.erase p₀).erase p₁).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hne.symm, hp₁⟩),
        Finset.card_erase_of_mem hp₀, hcard i₀]
      omega
    _ ≤ D.card := Finset.card_le_card sub
    _ ≤ (Au ∪ Xs).card := hbudget
    _ ≤ Au.card + Xs.card := Finset.card_union_le _ _
