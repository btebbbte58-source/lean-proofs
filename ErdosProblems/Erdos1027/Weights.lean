/-
JSP-000854 (Erdos Problem 1027) - L0: weight layer.

Reference: Koishi Chan's proof (comment #661) on erdosproblems.com forum thread 1027,
with Stijn Cambie's technical remark (#703) and the author's response (#704).
Construction follows the conservative convention agreed in the formalization plan:
Koishi's original edge-weight formula (2^(-(f+1)) for a monochromatic edge with f
uncolored vertices) with the enlarged stopping thresholds (4c instead of 2c), under
which the total weight process is a *supermartingale* (per-step expectation never
increases), so every downstream bound holds a fortiori.
-/
import Mathlib.Tactic

namespace Erdos1027

open scoped Classical

variable {α : Type} [DecidableEq α]

/-- A partial two-coloring: `some true` / `some false` for colored vertices,
`none` for uncolored ones. -/
abbrev PCol (α : Type) [DecidableEq α] : Type := α → Option Bool

/-- An edge is *monochromatic* under the partial coloring `C` if all of its
**colored** vertices share the same color (uncolored vertices are ignored). -/
def Monochromatic (C : PCol α) (A : Finset α) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, C x ≠ none → C y ≠ none → C x = C y

/-- Number of uncolored vertices of edge `A` under the partial coloring `C`. -/
def uncoloredCount (C : PCol α) (A : Finset α) : ℕ := (A.filter fun x => C x = none).card

/-- Koishi's edge weight (conservative 4c convention). For an edge `A`:
* `0` if `A` is not monochromatic;
* `2^(-(f+1))` if `A` is monochromatic, has at least one colored vertex and `f`
  uncolored vertices;
* `2^(-|A|)` if `A` is completely uncolored. -/
noncomputable def edgeWeight (C : PCol α) (A : Finset α) : ℝ :=
  if (∃ x ∈ A, C x ≠ none) then
    if Monochromatic C A then (2 : ℝ) ^ (-((uncoloredCount C A : ℤ) + 1))
    else 0
  else (2 : ℝ) ^ (-(A.card : ℤ))

/-- Total weight of the family `F` under the partial coloring `C`. -/
noncomputable def totalWeight (C : PCol α) (F : Finset (Finset α)) : ℝ :=
  ∑ A ∈ F, edgeWeight C A

/-- Vertex weight: the maximum edge weight among edges containing `v`
(`0` if no edge of `F` contains `v`). -/
noncomputable def vertexWeight (C : PCol α) (F : Finset (Finset α)) (v : α) : ℝ :=
  (F.filter fun A => v ∈ A).fold max 0 (edgeWeight C)

/-- Coloring an uncolored vertex `v`: the partial coloring updated by giving `v`
the color `b`. -/
def colorVertex (C : PCol α) (v : α) (b : Bool) : PCol α :=
  fun x => if x = v then some b else C x

/-! ### L1: coloring an uncolored vertex never increases the expected edge weight -/

/-- Coloring an uncolored vertex `v` with color `b` removes exactly `v` from the
uncolored part of `x`'s edge membership. -/
lemma colorVertex_eq_none_iff (C : PCol α) (v : α) (b : Bool) (x : α) :
    colorVertex C v b x = none ↔ (C x = none ∧ x ≠ v) := by
  unfold colorVertex
  split_ifs with h
  · simp [h]
  · simp [h]

/-- If an edge has a colored vertex and is monochromatic, all its colored vertices
share one common color `d`. -/
lemma exists_common_color {C : PCol α} {A : Finset α} (hcol : ∃ x ∈ A, C x ≠ none)
    (hmono : Monochromatic C A) : ∃ d : Bool, ∀ x ∈ A, C x ≠ none → C x = some d := by
  obtain ⟨x, hx, hxc⟩ := hcol
  obtain ⟨d, hd⟩ := Option.ne_none_iff_exists.mp hxc
  refine ⟨d, fun y hy hyc => ?_⟩
  exact (hmono y hy x hx hyc hxc).trans hd.symm

/-- Coloring an uncolored vertex `v ∈ A` decreases the uncolored count by one. -/
lemma uncoloredCount_colorVertex {C : PCol α} {A : Finset α} {v : α}
    (hv : C v = none) (hAv : v ∈ A) (b : Bool) :
    uncoloredCount (colorVertex C v b) A = uncoloredCount C A - 1 := by
  have key : A.filter (fun x => colorVertex C v b x = none)
      = (A.filter fun x => C x = none).erase v := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase, colorVertex_eq_none_iff]
    tauto
  simp only [uncoloredCount]
  rw [key]
  simp [Finset.card_erase_of_mem, Finset.mem_filter, hAv, hv]

/-- A disagreement between two colored vertices survives coloring an uncolored vertex. -/
lemma Monochromatic.colorVertex_persist {C : PCol α} {A : Finset α} {v : α} {b : Bool}
    (hv : C v = none) (h : ¬ Monochromatic C A) :
    ¬ Monochromatic (colorVertex C v b) A := by
  unfold Monochromatic at h ⊢
  push_neg at h
  obtain ⟨x, hx, y, hy, hxc, hyc, hne⟩ := h
  intro hmono'
  have hxv : x ≠ v := by
    intro hcon; subst hcon; exact hxc hv
  have hyv : y ≠ v := by
    intro hcon; subst hcon; exact hyc hv
  have hx' : colorVertex C v b x = C x := by simp only [colorVertex, if_neg hxv]
  have hy' : colorVertex C v b y = C y := by simp only [colorVertex, if_neg hyv]
  have h1 : colorVertex C v b x ≠ none := by rw [hx']; exact hxc
  have h2 : colorVertex C v b y ≠ none := by rw [hy']; exact hyc
  have hc' := hmono' x hx y hy h1 h2
  rw [hx', hy'] at hc'
  exact hne hc'

/-- If the old coloring of `A` is monochromatic with common color `d` and has at least
one colored vertex, then after coloring the uncolored vertex `v`, the edge stays
monochromatic iff the new color equals `d`. -/
lemma Monochromatic.colorVertex_iff {C : PCol α} {A : Finset α} {v : α} {b : Bool}
    (hv : C v = none) (hAv : v ∈ A) (hmono : Monochromatic C A)
    (hcol : ∃ x ∈ A, C x ≠ none) (d : Bool) (hd : ∀ x ∈ A, C x ≠ none → C x = some d) :
    Monochromatic (colorVertex C v b) A ↔ b = d := by
  constructor
  · intro hm'
    obtain ⟨x, hx, hxc⟩ := hcol
    have hxv : x ≠ v := by
      intro hcon; subst hcon; exact hxc hv
    have h1 : colorVertex C v b v ≠ none := by simp [colorVertex]
    have h2 : colorVertex C v b x ≠ none := by simp [colorVertex, hxv, hxc]
    have heq : colorVertex C v b v = colorVertex C v b x := hm' v hAv x hx h1 h2
    simpa [colorVertex, hxv, hd x hx hxc] using heq
  · intro hb
    unfold Monochromatic
    intro x hx y hy hxc hyc
    have get : ∀ z ∈ A, colorVertex C v b z ≠ none → z ≠ v → C z = some d := by
      intro z hz hne hzv
      refine hd z hz ?_
      by_contra hnone
      exact hne ((colorVertex_eq_none_iff C v b z).mpr ⟨hnone, hzv⟩)
    by_cases hxv : x = v
    · simp only [colorVertex, if_pos hxv]
      by_cases hyv : y = v
      · simp only [colorVertex, if_pos hyv]
      · simp only [colorVertex, if_neg hyv, get y hy hyc hyv, ← hb]
    · simp only [colorVertex, if_neg hxv, get x hx hxc hxv]
      by_cases hyv : y = v
      · simp only [colorVertex, if_pos hyv, ← hb]
      · simp only [colorVertex, if_neg hyv, get y hy hyc hyv]

/-- If all vertices of `A` are uncolored, coloring any one of them keeps `A`
monochromatic (it then has a single colored vertex). -/
lemma Monochromatic.colorVertex_of_all_uncolored {C : PCol α} {A : Finset α} {v : α}
    {b : Bool} (hnone : ∀ x ∈ A, C x = none) :
    Monochromatic (colorVertex C v b) A := by
  unfold Monochromatic
  intro x hx y hy hxc hyc
  have hxv : x = v := by
    by_contra hne
    exfalso
    simp only [colorVertex, if_neg hne, hnone x hx] at hxc
    exact hxc rfl
  have hyv : y = v := by
    by_contra hne
    exfalso
    simp only [colorVertex, if_neg hne, hnone y hy] at hyc
    exact hyc rfl
  subst hxv
  subst hyv
  simp [colorVertex]

/-- Sum over the two-element type `Bool`. -/
lemma sum_bool_eq (f : Bool → ℝ) : ∑ x : Bool, f x = f true + f false := by
  rw [Fintype.univ_bool, Finset.sum_insert (by simp), Finset.sum_singleton]

/-- **L1 (per-edge supermartingale step)**: coloring an uncolored vertex `v` of edge
`A` with a uniformly random color never increases the expected edge weight. -/
lemma edgeWeight_colorVertex_le (C : PCol α) (A : Finset α) (v : α)
    (hv : C v = none) (hAv : v ∈ A) :
    (∑ b : Bool, edgeWeight (colorVertex C v b) A) / 2 ≤ edgeWeight C A := by
  by_cases hcol : ∃ x ∈ A, C x ≠ none
  · by_cases hmono : Monochromatic C A
    · -- Case 1: monochromatic with a colored part — expectation exactly conserved
      obtain ⟨d, hd⟩ := exists_common_color hcol hmono
      have fpos : 0 < uncoloredCount C A :=
        Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨hAv, hv⟩⟩
      have hmb : ∀ b : Bool, Monochromatic (colorVertex C v b) A ↔ b = d :=
        fun b => Monochromatic.colorVertex_iff (b := b) hv hAv hmono hcol d hd
      have key : ∀ b : Bool, edgeWeight (colorVertex C v b) A =
          if b = d then (2 : ℝ) ^ (-(uncoloredCount C A : ℤ)) else 0 := by
        intro b
        obtain ⟨x, hx, hxc⟩ := hcol
        have hxv : x ≠ v := by
          intro hcon; subst hcon; exact hxc hv
        have hexists' : ∃ z ∈ A, colorVertex C v b z ≠ none :=
          ⟨x, hx, by simp only [colorVertex, if_neg hxv]; exact hxc⟩
        unfold edgeWeight
        rw [if_pos hexists']
        by_cases hb : b = d
        · rw [if_pos hb, if_pos ((hmb b).mpr hb), uncoloredCount_colorVertex hv hAv b]
          have e : ((uncoloredCount C A - 1 : ℕ) : ℤ) + 1 = (uncoloredCount C A : ℤ) := by
            have : (0 : ℤ) < (uncoloredCount C A : ℤ) := by exact_mod_cast fpos
            omega
          rw [e]
        · rw [if_neg hb, if_neg (fun hc => hb ((hmb b).mp hc))]
      have finish : (2:ℝ)^(-(uncoloredCount C A : ℤ)) / 2
          ≤ (2:ℝ)^(-((uncoloredCount C A : ℤ) + 1)) := by
        have e : (-((uncoloredCount C A : ℤ) + 1) + 1 : ℤ) = -(uncoloredCount C A : ℤ) := by ring
        have hexp : (2:ℝ)^(-(uncoloredCount C A : ℤ))
            = (2:ℝ)^(-((uncoloredCount C A : ℤ) + 1)) * 2 := by
          rw [← e, zpow_add₀ (by norm_num : (2:ℝ) ≠ 0), zpow_one]
        have hX : 0 < (2:ℝ)^(-((uncoloredCount C A : ℤ) + 1)) := zpow_pos two_pos _
        rw [hexp]
        field_simp
        linarith
      rw [sum_bool_eq]
      cases d with
      | false =>
        have h1 : edgeWeight (colorVertex C v true) A = 0 := by rw [key]; simp
        have h2 : edgeWeight (colorVertex C v false) A
            = (2:ℝ)^(-(uncoloredCount C A : ℤ)) := by rw [key]; simp
        simp only [h1, h2, zero_add]
        unfold edgeWeight
        rw [if_pos hcol, if_pos hmono]
        exact finish
      | true =>
        have h1 : edgeWeight (colorVertex C v false) A = 0 := by rw [key]; simp
        have h2 : edgeWeight (colorVertex C v true) A
            = (2:ℝ)^(-(uncoloredCount C A : ℤ)) := by rw [key]; simp
        simp only [h1, h2, add_zero]
        unfold edgeWeight
        rw [if_pos hcol, if_pos hmono]
        exact finish
    · -- Case 2: colored but not monochromatic — weight stays 0
      have hw : ∀ b : Bool, edgeWeight (colorVertex C v b) A = 0 := by
        intro b
        obtain ⟨x, hx, hxc⟩ := hcol
        have hxv : x ≠ v := by
          intro hcon; subst hcon; exact hxc hv
        have hexists' : ∃ z ∈ A, colorVertex C v b z ≠ none :=
          ⟨x, hx, by simp only [colorVertex, if_neg hxv]; exact hxc⟩
        unfold edgeWeight
        rw [if_pos hexists']
        exact if_neg (Monochromatic.colorVertex_persist hv hmono)
      rw [sum_bool_eq]
      simp only [hw]
      unfold edgeWeight
      rw [if_pos hcol, if_neg hmono]
      norm_num
  · -- Case 3: completely uncolored — expectation equals 2^(-|A|)
    have hnone : ∀ x ∈ A, C x = none := by
      intro x hx
      by_contra hxc
      exact hcol ⟨x, hx, hxc⟩
    have hcount : A.card = uncoloredCount C A := by
      rw [uncoloredCount, Finset.filter_eq_self.mpr (fun x hx => hnone x hx)]
    have hApos : 0 < A.card := Finset.card_pos.mpr ⟨v, hAv⟩
    have hw : ∀ b : Bool, edgeWeight (colorVertex C v b) A = (2:ℝ)^(-(A.card:ℤ)) := by
      intro b
      unfold edgeWeight
      rw [if_pos (⟨v, hAv, by simp only [colorVertex, if_pos rfl]; simp⟩ :
        ∃ z ∈ A, colorVertex C v b z ≠ none)]
      rw [if_pos (Monochromatic.colorVertex_of_all_uncolored
        (C := C) (A := A) (v := v) (b := b) hnone)]
      rw [uncoloredCount_colorVertex hv hAv b]
      have e : ((uncoloredCount C A - 1 : ℕ) : ℤ) + 1 = (A.card : ℤ) := by
        have h1 : (0:ℤ) < (A.card : ℤ) := by exact_mod_cast hApos
        have h2 : (A.card : ℤ) = (uncoloredCount C A : ℤ) := by rw [hcount]
        omega
      rw [e]
    have finish2 : ((2:ℝ)^(-(A.card:ℤ))) / 2 ≤ (2:ℝ)^(-(A.card:ℤ)) := by
      have hX : 0 < (2:ℝ)^(-(A.card:ℤ)) := zpow_pos two_pos _
      rw [div_le_iff₀ two_pos]
      linarith
    have hRHS : edgeWeight C A = (2:ℝ)^(-(A.card:ℤ)) := by
      unfold edgeWeight
      rw [if_neg hcol]
    rw [sum_bool_eq, hw true, hw false, hRHS]
    field_simp
    linarith

end Erdos1027
