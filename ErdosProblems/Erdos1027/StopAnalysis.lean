/-
JSP-000854 (Erdos Problem 1027) - L3: stop-condition analysis.

The stop conditions (conservative convention, threshold `2c`):
1) `totalWeight > 2c`;
2) some edge has weight at least `w/2`;
3) every vertex of `X = F.biUnion id` is colored.

Content (Koishi's observation ii): when stopping via 2) after coloring the
min-weight vertex `v`, every still-uncolored vertex of `X` lies in an edge of
weight at least `w/4`; there are at most `8c/w` such edges, and each such edge
has at most `log₂ (8/w)` uncolored vertices — so at most
`(8c/w) * log₂ (8/w)` vertices of `X` remain uncolored.
-/
import ErdosProblems.Erdos1027.Algorithm
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Erdos1027

open scoped Classical

variable {α : Type} [DecidableEq α]

/-! ### L3a: coloring one vertex at most doubles each edge weight -/

lemma edgeWeight_nonneg (C : PCol α) (A : Finset α) : 0 ≤ edgeWeight C A := by
  unfold edgeWeight
  split_ifs with h1 h2
  · exact le_of_lt (zpow_pos two_pos _)
  · exact le_refl _
  · exact le_of_lt (zpow_pos two_pos _)

lemma edgeWeight_colorVertex_le_two_mul (C : PCol α) (A : Finset α) (v : α) (b : Bool)
    (hv : C v = none) :
    edgeWeight (colorVertex C v b) A ≤ 2 * edgeWeight C A := by
  by_cases hAv : v ∈ A
  · by_cases hcol : ∃ x ∈ A, C x ≠ none
    · obtain ⟨x, hx, hxc⟩ := id hcol
      have hxv : x ≠ v := by
        intro hcon; subst hcon; exact hxc hv
      have hXexists : ∃ z ∈ A, colorVertex C v b z ≠ none :=
        ⟨x, hx, by simp only [colorVertex, ite_eq_right hxv]; exact hxc⟩
      by_cases hmono : Monochromatic C A
      · have fpos : 0 < uncoloredCount C A :=
          Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨hAv, hv⟩⟩
        by_cases hmono' : Monochromatic (colorVertex C v b) A
        · have hnew : edgeWeight (colorVertex C v b) A
              = (2:ℝ)^(-(((uncoloredCount C A - 1 : ℕ) : ℤ) + 1)) := by
            unfold edgeWeight
            rw [ite_eq_left hXexists, ite_eq_left hmono',
              uncoloredCount_colorVertex hv hAv b]
          have hold : edgeWeight C A = (2:ℝ)^(-((uncoloredCount C A : ℤ) + 1)) := by
            unfold edgeWeight
            rw [ite_eq_left hcol, ite_eq_left hmono]
          rw [hnew, hold]
          have e : ((uncoloredCount C A - 1 : ℕ) : ℤ) + 1 = (uncoloredCount C A : ℤ) := by
            have hzi : (0:ℤ) < (uncoloredCount C A : ℤ) := by exact_mod_cast fpos
            omega
          rw [e]
          have hadd : (-((uncoloredCount C A : ℤ) + 1) + 1 : ℤ)
              = -(uncoloredCount C A : ℤ) := by ring
          have hX : 0 < (2:ℝ)^(-((uncoloredCount C A : ℤ) + 1)) := zpow_pos two_pos _
          have hexp : (2:ℝ)^(-(uncoloredCount C A : ℤ))
              = 2 * (2:ℝ)^(-((uncoloredCount C A : ℤ) + 1)) := by
            rw [← hadd, zpow_add₀ (show (2:ℝ) ≠ 0 by norm_num), zpow_one, mul_comm]
          linarith
        · have hnew0 : edgeWeight (colorVertex C v b) A = 0 := by
            unfold edgeWeight
            rw [ite_eq_left hXexists, ite_eq_right hmono']
          rw [hnew0]
          have hle : 0 ≤ edgeWeight C A := edgeWeight_nonneg C A
          linarith
      · have hnew0 : edgeWeight (colorVertex C v b) A = 0 := by
          unfold edgeWeight
          rw [ite_eq_left hXexists,
            ite_eq_right (Monochromatic.colorVertex_persist hv hmono)]
        have hold0 : edgeWeight C A = 0 := by
          unfold edgeWeight
          rw [ite_eq_left hcol, ite_eq_right hmono]
        rw [hnew0, hold0]
        norm_num
    · have hnone : ∀ x ∈ A, C x = none := by
        intro x hx
        by_contra hxc
        exact hcol ⟨x, hx, hxc⟩
      have hcount : A.card = uncoloredCount C A := by
        rw [uncoloredCount, Finset.filter_eq_self.mpr (fun x hx => hnone x hx)]
      have hApos : 0 < A.card := Finset.card_pos.mpr ⟨v, hAv⟩
      have hmono' : Monochromatic (colorVertex C v b) A :=
        Monochromatic.colorVertex_of_all_uncolored (C := C) (A := A) (v := v) (b := b) hnone
      have hnew : edgeWeight (colorVertex C v b) A = (2:ℝ)^(-(A.card : ℤ)) := by
        unfold edgeWeight
        rw [ite_eq_left (⟨v, hAv, by simp [colorVertex]⟩ :
            ∃ z ∈ A, colorVertex C v b z ≠ none),
          ite_eq_left hmono', uncoloredCount_colorVertex hv hAv b]
        have e : ((uncoloredCount C A - 1 : ℕ) : ℤ) + 1 = (A.card : ℤ) := by
          have h1 : (0:ℤ) < (A.card : ℤ) := by exact_mod_cast hApos
          have h2 : (A.card : ℤ) = (uncoloredCount C A : ℤ) := by rw [hcount]
          omega
        rw [e]
      have hold : edgeWeight C A = (2:ℝ)^(-(A.card : ℤ)) := by
        unfold edgeWeight
        rw [ite_eq_right hcol]
      rw [hnew, hold]
      have hX : 0 < (2:ℝ)^(-(A.card : ℤ)) := zpow_pos two_pos _
      linarith
  · rw [edgeWeight_colorVertex_of_not_mem C A v b hAv]
    have hn := edgeWeight_nonneg C A
    linarith

/-! ### L3b: the last-step analysis (Koishi's ii) -/

/-- If coloring the uncolored vertex `v` pushes some edge of `F` to weight at
least `w/2` while no edge had weight ≥ `w/2` before, then `v` lies in some edge
whose weight was at least `w/4` before the step. -/
lemma exists_high_edge_of_push (C : PCol α) (F : Finset (Finset α)) (v : α) (b : Bool)
    (w : ℝ) (hv : C v = none)
    (hnot : ∀ A ∈ F, edgeWeight C A < w / 2)
    (hpush : ∃ A ∈ F, w / 2 ≤ edgeWeight (colorVertex C v b) A) :
    ∃ A ∈ F, v ∈ A ∧ w / 4 ≤ edgeWeight C A := by
  obtain ⟨A, hA, hp⟩ := hpush
  by_cases hvA : v ∈ A
  · refine ⟨A, hA, hvA, ?_⟩
    have h2 := edgeWeight_colorVertex_le_two_mul C A v b hv
    have h1 : w / 2 ≤ 2 * edgeWeight C A := hp.trans h2
    linarith
  · exfalso
    rw [edgeWeight_colorVertex_of_not_mem C A v b hvA] at hp
    exact absurd (hnot A hA) (not_lt.mpr hp)

/-! ### L3c: vertex weight extraction -/

lemma fold_max_ge {γ : Type} [DecidableEq γ] (s : Finset γ) (f : γ → ℝ) (i : γ)
    (hi : i ∈ s) : f i ≤ s.fold max 0 f := by
  classical
  induction s using Finset.induction_on with
  | empty => exact absurd hi (by simp)
  | insert a s has ih =>
    rw [Finset.fold_insert has]
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact le_max_left _ _
    · exact le_trans (ih hi) (le_max_right _ _)

lemma fold_max_eq_or_mem {γ : Type} [DecidableEq γ] (s : Finset γ) (f : γ → ℝ) :
    s.fold max 0 f = 0 ∨ ∃ i ∈ s, s.fold max 0 f = f i := by
  classical
  induction s using Finset.induction_on with
  | empty => left; simp
  | insert a s has ih =>
    rw [Finset.fold_insert has]
    rcases ih with h0 | ⟨i, hi, hfi⟩
    · by_cases hfa : f a ≤ 0
      · left
        rw [h0]
        exact max_eq_right hfa
      · right
        refine ⟨a, Finset.mem_insert_self a s, ?_⟩
        have hle : s.fold max 0 f ≤ f a := by rw [h0]; exact (not_le.mp hfa).le
        rw [max_eq_left hle]
    · by_cases hfa : f a ≤ f i
      · right
        refine ⟨i, Finset.mem_insert_of_mem hi, ?_⟩
        rw [hfi]
        exact max_eq_right hfa
      · right
        refine ⟨a, Finset.mem_insert_self a s, ?_⟩
        have hle : s.fold max 0 f ≤ f a := by rw [hfi]; exact le_of_lt (lt_of_not_ge hfa)
        rw [max_eq_left hle]

lemma vertexWeight_ge (C : PCol α) (F : Finset (Finset α)) (v : α) (A : Finset α)
    (hA : A ∈ F) (hvA : v ∈ A) : edgeWeight C A ≤ vertexWeight C F v := by
  unfold vertexWeight
  exact fold_max_ge _ _ A (Finset.mem_filter.mpr ⟨hA, hvA⟩)

lemma exists_high_edge_of_vertexWeight (C : PCol α) (F : Finset (Finset α)) (u : α)
    (hpos : 0 < vertexWeight C F u) :
    ∃ A ∈ F, u ∈ A ∧ vertexWeight C F u ≤ edgeWeight C A := by
  unfold vertexWeight at hpos ⊢
  rcases fold_max_eq_or_mem (F.filter fun A => u ∈ A) (edgeWeight C) with h0 | ⟨A, hA, heq⟩
  · exact absurd hpos (by rw [h0]; norm_num)
  · exact ⟨A, (Finset.mem_filter.mp hA).1, (Finset.mem_filter.mp hA).2, by rw [heq]⟩

/-! ### L3d: the uncolored count of a heavy edge -/

lemma uncoloredCount_le_log (C : PCol α) (A : Finset α) (w : ℝ) (hw : 0 < w)
    (hA : w / 8 ≤ edgeWeight C A) :
    (uncoloredCount C A : ℝ) ≤ Real.logb 2 (8 / w) := by
  by_cases hcol : ∃ x ∈ A, C x ≠ none
  · by_cases hmono : Monochromatic C A
    · have hw8 : edgeWeight C A = (2:ℝ)^(-((uncoloredCount C A : ℤ) + 1)) := by
        unfold edgeWeight
        rw [ite_eq_left hcol, ite_eq_left hmono]
      have hpos8 : 0 < (w / 8 : ℝ) := div_pos hw (by norm_num)
      have hA2 : w / 8 ≤ (2:ℝ)^(-((uncoloredCount C A : ℤ) + 1)) := by
        rw [← hw8]; exact hA
      have hpow : (2:ℝ)^(((uncoloredCount C A : ℕ) + 1 : ℕ) : ℝ) ≤ 8 / w := by
        have hinv : ((2:ℝ)^(-((uncoloredCount C A : ℤ) + 1)))⁻¹ ≤ (w / 8)⁻¹ :=
          inv_anti₀ hpos8 hA2
        rw [inv_div] at hinv
        have hYinv : ((2:ℝ)^(-((uncoloredCount C A : ℤ) + 1)))⁻¹
            = (2:ℝ)^(((uncoloredCount C A : ℕ) + 1 : ℕ) : ℝ) := by
          have hcast : ((uncoloredCount C A : ℤ) + 1)
              = (((uncoloredCount C A : ℕ) + 1 : ℕ) : ℤ) := by
            push_cast; ring
          rw [hcast, zpow_neg, inv_inv, zpow_natCast, Real.rpow_natCast]
        rw [hYinv] at hinv
        exact hinv
      have hlog : (((uncoloredCount C A : ℕ) + 1 : ℕ) : ℝ) ≤ Real.logb 2 (8 / w) := by
        rw [Real.le_logb_iff_rpow_le (by norm_num) (div_pos (by norm_num) hw)]
        exact hpow
      rw [Nat.cast_add] at hlog
      linarith
    · exfalso
      have h0 : edgeWeight C A = 0 := by
        unfold edgeWeight
        rw [ite_eq_left hcol, ite_eq_right hmono]
      rw [h0] at hA
      linarith
  · have hnone : ∀ x ∈ A, C x = none := by
      intro x hx
      by_contra hxc
      exact hcol ⟨x, hx, hxc⟩
    have hcount : A.card = uncoloredCount C A := by
      rw [uncoloredCount, Finset.filter_eq_self.mpr (fun x hx => hnone x hx)]
    have hw8 : edgeWeight C A = (2:ℝ)^(-(A.card : ℤ)) := by
      unfold edgeWeight
      rw [ite_eq_right hcol]
    have hpos8 : 0 < (w / 8 : ℝ) := div_pos hw (by norm_num)
    have hA2 : w / 8 ≤ (2:ℝ)^(-(A.card : ℤ)) := by
      rw [← hw8]; exact hA
    have hpow : (2:ℝ)^((A.card : ℕ) : ℝ) ≤ 8 / w := by
      have hinv : ((2:ℝ)^(-(A.card : ℤ)))⁻¹ ≤ (w / 8)⁻¹ := inv_anti₀ hpos8 hA2
      rw [inv_div] at hinv
      have hYinv : ((2:ℝ)^(-(A.card : ℤ)))⁻¹ = (2:ℝ)^((A.card : ℕ) : ℝ) := by
        rw [zpow_neg, inv_inv, zpow_natCast, Real.rpow_natCast]
      rw [hYinv] at hinv
      exact hinv
    have hlog : ((A.card : ℕ) : ℝ) ≤ Real.logb 2 (8 / w) := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) (div_pos (by norm_num) hw)]
      exact hpow
    rw [← hcount]
    exact hlog

/-! ### L3e: the uncolored count at a stop-② event -/

/-- **L3 (Koishi's observation ii)**: if a min-weight selector colors the
uncolored vertex `v` and the process stops via condition 2) right after, then
at most `(8c/w) * log₂ (8/w)` vertices of `X = F.biUnion id` remain uncolored. -/
lemma uncolored_card_le (C : PCol α) (F : Finset (Finset α)) (v : α) (b : Bool) (c w : ℝ)
    (hw : 0 < w) (hw1 : w ≤ 1)
    (hv : C v = none)
    (hmin : ∀ u, C u = none → u ∈ F.biUnion id →
      vertexWeight C F v ≤ vertexWeight C F u)
    (hnot2 : ∀ A ∈ F, edgeWeight C A < w / 2)
    (htot : totalWeight C F ≤ 2 * c)
    (hpush : ∃ A ∈ F, w / 2 ≤ edgeWeight (colorVertex C v b) A) :
    ((F.biUnion id).filter (fun u => C u = none)).card
      ≤ (8 * c / w) * Real.logb 2 (8 / w) := by
  classical
  obtain ⟨A0, hA0F, hvA0, hw4⟩ := exists_high_edge_of_push C F v b w hv hnot2 hpush
  have hvw : w / 4 ≤ vertexWeight C F v :=
    hw4.trans (vertexWeight_ge C F v A0 hA0F hvA0)
  set Heavy : Finset (Finset α) := F.filter fun A => w / 4 ≤ edgeWeight C A with hHeavy
  have cover : ∀ u ∈ (F.biUnion id).filter (fun u => C u = none),
      ∃ A ∈ Heavy, u ∈ A.filter (fun x => C x = none) := by
    intro u hu
    obtain ⟨huX, hu0⟩ := Finset.mem_filter.mp hu
    have hwu : w / 4 ≤ vertexWeight C F u := hvw.trans (hmin u hu0 huX)
    obtain ⟨A, hAF, huA, hle⟩ := exists_high_edge_of_vertexWeight C F u (by linarith)
    exact ⟨A, Finset.mem_filter.mpr ⟨hAF, hwu.trans hle⟩,
      Finset.mem_filter.mpr ⟨huA, hu0⟩⟩
  have hsub : (F.biUnion id).filter (fun u => C u = none) ⊆
      Heavy.biUnion (fun A => A.filter fun x => C x = none) := by
    intro u hu
    obtain ⟨A, hA, huA⟩ := cover u hu
    exact Finset.mem_biUnion.mpr ⟨A, hA, huA⟩
  have hcard1 : (((F.biUnion id).filter (fun u => C u = none)).card : ℝ)
      ≤ (Heavy.biUnion (fun A => A.filter fun x => C x = none)).card :=
    Nat.cast_le.mpr (Finset.card_le_card hsub)
  have hcard2 : (Heavy.biUnion (fun A => A.filter fun x => C x = none)).card
      ≤ ∑ A ∈ Heavy, uncoloredCount C A := by
    calc (Heavy.biUnion (fun A => A.filter fun x => C x = none)).card
        ≤ ∑ A ∈ Heavy, (A.filter fun x => C x = none).card := Finset.card_biUnion_le
      _ = ∑ A ∈ Heavy, uncoloredCount C A := by
          refine Finset.sum_congr rfl fun A _ => ?_
          rfl
  have hcard3 : (((F.biUnion id).filter (fun u => C u = none)).card : ℝ)
      ≤ ∑ A ∈ Heavy, (uncoloredCount C A : ℝ) := by
    have s1 : ((F.biUnion id).filter (fun u => C u = none)).card
        ≤ (Heavy.biUnion (fun A => A.filter fun x => C x = none)).card :=
      Finset.card_le_card hsub
    have s2 : (((F.biUnion id).filter (fun u => C u = none)).card : ℝ)
        ≤ ((∑ A ∈ Heavy, uncoloredCount C A : ℕ) : ℝ) :=
      Nat.cast_le.mpr (le_trans s1 hcard2)
    rw [Nat.cast_sum] at s2
    exact s2
  have hsum : (∑ A ∈ Heavy, (uncoloredCount C A : ℝ))
      ≤ (Heavy.card : ℝ) * Real.logb 2 (8 / w) := by
    calc ∑ A ∈ Heavy, (uncoloredCount C A : ℝ)
        ≤ ∑ _A ∈ Heavy, Real.logb 2 (8 / w) := by
          refine Finset.sum_le_sum fun A hA => ?_
          have h8 : (w / 8 : ℝ) ≤ w / 4 := by
            rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
            linarith
          exact uncoloredCount_le_log C A w hw
            (h8.trans (Finset.mem_filter.mp hA).2)
      _ = (Heavy.card : ℝ) * Real.logb 2 (8 / w) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hheavy : (Heavy.card : ℝ) * (w / 4) ≤ totalWeight C F := by
    have h1 : ∑ _A ∈ Heavy, (w / 4 : ℝ) ≤ ∑ A ∈ Heavy, edgeWeight C A :=
      Finset.sum_le_sum fun A hA => (Finset.mem_filter.mp hA).2
    have h2 : ∑ _A ∈ Heavy, (w / 4 : ℝ) = (Heavy.card : ℝ) * (w / 4) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    calc (Heavy.card : ℝ) * (w / 4) = ∑ _A ∈ Heavy, (w / 4 : ℝ) := h2.symm
      _ ≤ ∑ A ∈ Heavy, edgeWeight C A := h1
      _ ≤ totalWeight C F := by
          rw [totalWeight]
          exact Finset.sum_mono_set_of_nonneg (fun A => edgeWeight_nonneg C A)
            (Finset.filter_subset _ _)
  have hheavy' : (Heavy.card : ℝ) ≤ 8 * c / w := by
    rw [le_div_iff₀ hw]
    have hw4' : (4:ℝ) * (w / 4) = w := by field_simp
    calc (Heavy.card : ℝ) * w = (Heavy.card : ℝ) * ((4:ℝ) * (w / 4)) := by rw [hw4']
      _ = (4:ℝ) * ((Heavy.card : ℝ) * (w / 4)) := by ring
      _ ≤ (4:ℝ) * (2 * c) := by
          exact mul_le_mul_of_nonneg_left (le_trans hheavy htot) (by norm_num)
      _ = 8 * c := by ring
  have hlogpos : 0 ≤ Real.logb 2 (8 / w) := by
    refine Real.logb_nonneg (by norm_num) ?_
    rw [le_div_iff₀ hw]
    linarith
  calc ((F.biUnion id).filter (fun u => C u = none)).card
      ≤ ∑ A ∈ Heavy, (uncoloredCount C A : ℝ) := hcard3
    _ ≤ (Heavy.card : ℝ) * Real.logb 2 (8 / w) := hsum
    _ ≤ (8 * c / w) * Real.logb 2 (8 / w) :=
      mul_le_mul_of_nonneg_right hheavy' hlogpos

/-! ### L3f: the stop condition and the minimum-weight selector -/

/-- The three stop conditions (conservative threshold convention):
1) `totalWeight > 2c`; 2) some edge has weight ≥ `w/2`;
3) every vertex of `X = F.biUnion id` is colored. -/
def stopCond (F : Finset (Finset α)) (c w : ℝ) (C : PCol α) : Prop :=
  2 * c < totalWeight C F ∨ (∃ A ∈ F, w / 2 ≤ edgeWeight C A) ∨
    (∀ x ∈ F.biUnion id, C x ≠ none)

noncomputable instance (F : Finset (Finset α)) (c w : ℝ) :
    DecidablePred (stopCond F c w) :=
  Classical.decPred _

lemma exists_min_image_real {s : Finset α} (f : α → ℝ) (h : s.Nonempty) :
    ∃ v, v ∈ s ∧ ∀ u ∈ s, f v ≤ f u := by
  classical
  induction s using Finset.induction_on with
  | empty => obtain ⟨x, hx⟩ := h; exact absurd hx (by simp)
  | insert a s _ ih =>
    by_cases hs : s.Nonempty
    · obtain ⟨v, hv, hmin⟩ := ih hs
      by_cases hAv : f a ≤ f v
      · exact ⟨a, Finset.mem_insert_self a s, fun u hu => by
          rcases Finset.mem_insert.mp hu with rfl | hu
          · exact le_refl _
          · exact le_trans hAv (hmin u hu)⟩
      · exact ⟨v, Finset.mem_insert_of_mem hv, fun u hu => by
          rcases Finset.mem_insert.mp hu with rfl | hu
          · exact le_of_lt (lt_of_not_ge hAv)
          · exact hmin u hu⟩
    · have hse : s = ∅ := by
        by_contra hne
        exact hs (Finset.ne_empty_iff_nonempty.mp hne)
      refine ⟨a, Finset.mem_insert_self a s, fun u hu => ?_⟩
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact le_refl _
      · exact absurd hu (by rw [hse]; simp)

/-- If the stop condition does not hold, there is an uncolored vertex of `X`
with minimum vertex weight. -/
lemma exists_sel_min (F : Finset (Finset α)) (C : PCol α) (c w : ℝ) (h : ¬ stopCond F c w C) :
    ∃ v, v ∈ F.biUnion id ∧ C v = none ∧
      ∀ u, C u = none → u ∈ F.biUnion id → vertexWeight C F v ≤ vertexWeight C F u := by
  have hx : ∃ x ∈ F.biUnion id, C x = none := by
    by_contra hcon
    refine h (Or.inr (Or.inr ?_))
    intro x hxmem hxnone
    exact hcon ⟨x, hxmem, hxnone⟩
  obtain ⟨x, hxmem, hxcol⟩ := hx
  classical
  have hS : ((F.biUnion id).filter fun v => C v = none).Nonempty :=
    ⟨x, Finset.mem_filter.mpr ⟨hxmem, hxcol⟩⟩
  obtain ⟨v, hvS, hmin⟩ := exists_min_image_real (vertexWeight C F) hS
  obtain ⟨hvmem, hvcol⟩ := Finset.mem_filter.mp hvS
  exact ⟨v, hvmem, hvcol, fun u hu0 huX =>
    hmin u (Finset.mem_filter.mpr ⟨huX, hu0⟩)⟩

end Erdos1027
