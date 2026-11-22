/-
JSP-000854 (Erdos Problem 1027) - L5: completion of a stopped partial coloring
(Kooshi's observation iii).

The residual hypergraph consists of the uncolored parts of the monochromatic
edges.  Under Beck's theorem (taken here as a hypothesis; the exact statement is
Beck, "On 3-chromatic hypergraphs", Discrete Math. 24 (1978), Theorem 1.2, in
the non-uniform weighted form quoted by Koishi Chan), a partial coloring reached
by one more coloring step from a coloring in which every edge had weight
`< w₀/4`, and whose total weight is `≤ 2c`, can be completed to a proper total
coloring of `F`.

Constants note: our weight convention is the conservative one
(monochromatic edge with `f` uncolored vertices has weight `2^{-(f+1)}`, i.e.
half of Koishi's), so the `w₀/4` threshold here corresponds to Koishi's
`w(2c)/2`.  The residual weight of a monochromatic edge equals twice our edge
weight; the worst case (edge already monochromatic before the step) gives
`residual weight = 4 · (previous edge weight) < w₀`.
-/
import ErdosProblems.Erdos1027.StopAnalysis

namespace Erdos1027

open scoped Classical

variable {α : Type} [DecidableEq α]

/-! ### Helper: the sum over an image is at most the sum over the source -/

/-- For nonnegative `g`, summing over `s.image f` is at most summing `g (f ·)`
over `s` (each image element is hit at least once). -/
lemma sum_image_le {γ δ : Type} [DecidableEq γ] [DecidableEq δ]
    (s : Finset γ) (f : γ → δ) (g : δ → ℝ) (hg : ∀ d, 0 ≤ g d) :
    ∑ y ∈ s.image f, g y ≤ ∑ x ∈ s, g (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    rw [Finset.image_insert]
    by_cases hfa : f a ∈ s.image f
    · rw [Finset.insert_eq_of_mem hfa]
      have h2 : ∑ x ∈ insert a s, g (f x)
          = g (f a) + ∑ x ∈ s, g (f x) := Finset.sum_insert has
      linarith [ih, hg (f a)]
    · rw [Finset.sum_insert hfa, Finset.sum_insert has]
      linarith [ih, hg (f a)]

/-! ### The residual family -/

/-- Kooshi's residual hypergraph: the uncolored parts of the monochromatic
edges of `F` (fully uncolored monochromatic edges included). -/
noncomputable def residualEdges (C : PCol α) (F : Finset (Finset α)) :
    Finset (Finset α) :=
  (F.filter fun A => Monochromatic C A).image
    fun A => A.filter fun x => C x = none

lemma mem_residualEdges {C : PCol α} {F : Finset (Finset α)} {A' : Finset α} :
    A' ∈ residualEdges C F ↔
      ∃ A ∈ F, Monochromatic C A ∧ A' = A.filter (fun x => C x = none) := by
  constructor
  · intro h
    obtain ⟨A, hA, hA'⟩ := Finset.mem_image.mp h
    exact ⟨A, (Finset.mem_filter.mp hA).1, (Finset.mem_filter.mp hA).2, hA'.symm⟩
  · rintro ⟨A, hAF, hmono, hA'⟩
    exact Finset.mem_image.mpr ⟨A, Finset.mem_filter.mpr ⟨hAF, hmono⟩, hA'.symm⟩

/-! ### Disagreement extraction -/

/-- A non-monochromatic edge contains two colored vertices with different
colors. -/
lemma not_monochromatic_iff (C : PCol α) (A : Finset α) :
    ¬ Monochromatic C A ↔
      ∃ x ∈ A, ∃ y ∈ A, C x ≠ none ∧ C y ≠ none ∧ C x ≠ C y := by
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    exact h hcon
  · rintro ⟨x, hx, y, hy, hxc, hyc, hne⟩ hmono
    exact hne (hmono x hx y hy hxc hyc)

/-! ### Residual weights -/

/-- `2² = 4` in zpow form (norm_num cannot evaluate real zpow literals). -/
lemma real_two_zpow_two : ((2:ℝ) ^ ((2:ℤ))) = 4 := by
  rw [zpow_two]
  norm_num

/-- For a monochromatic edge, the residual weight `2^{-f}` (where `f` is the
number of uncolored vertices of `A`) is at most twice the edge weight. -/
lemma residual_pow_le (C : PCol α) (A : Finset α) (hmono : Monochromatic C A) :
    (2:ℝ)^(-((uncoloredCount C A : ℤ))) ≤ 2 * edgeWeight C A := by
  by_cases hcol : ∃ x ∈ A, C x ≠ none
  · -- monochromatic with a colored part: equality
    have hw : edgeWeight C A = (2:ℝ)^(-((uncoloredCount C A : ℤ) + 1)) := by
      unfold edgeWeight
      rw [ite_eq_left hcol, ite_eq_left hmono]
    have hEq : (2:ℝ)^(-((uncoloredCount C A : ℤ)))
        = 2 * (2:ℝ)^(-((uncoloredCount C A : ℤ) + 1)) := by
      have e : (-((uncoloredCount C A : ℤ)))
          = 1 + (-((uncoloredCount C A : ℤ) + 1)) := by ring
      rw [e, zpow_add₀ (by norm_num : (2:ℝ) ≠ 0), zpow_one]
    rw [hw, hEq]
  · -- completely uncolored: filter is all of `A`
    have hnone : ∀ x ∈ A, C x = none := fun x hx => by
      by_contra hxc; exact hcol ⟨x, hx, hxc⟩
    have hcard : A.filter (fun x => C x = none) = A :=
      Finset.filter_eq_self.mpr (fun x hx => hnone x hx)
    have hw : edgeWeight C A = (2:ℝ)^(-((A.card : ℕ) : ℤ)) := by
      unfold edgeWeight
      rw [ite_eq_right hcol]
    unfold uncoloredCount
    rw [hcard, hw]
    have hp : 0 < (2:ℝ)^(-((A.card : ℕ) : ℤ)) := zpow_pos two_pos _
    linarith

/-- **L5 core**: after coloring the uncolored vertex `v` (color `b`) starting
from a coloring in which every edge had weight `< w₀/4`, every monochromatic
edge has residual weight `2^{-f}` (f = number of still-uncolored vertices)
strictly below `w₀`. -/
lemma residual_weight_lt (C' : PCol α) (v : α) (b : Bool) (F : Finset (Finset α))
    (w₀ : ℝ) (hv : C' v = none) (hw₀ : 0 < w₀)
    (hnot2 : ∀ A ∈ F, edgeWeight C' A < w₀ / 4)
    {A : Finset α} (hAF : A ∈ F)
    (hmono : Monochromatic (colorVertex C' v b) A) :
    (2:ℝ)^(-((uncoloredCount (colorVertex C' v b) A : ℤ))) < w₀ := by
  classical
  by_cases hvA : v ∈ A
  · -- v belongs to the edge
    by_cases hmono' : Monochromatic C' A
    · by_cases hcol' : ∃ x ∈ A, C' x ≠ none
      · -- already monochromatic with a colored part
        have huc : uncoloredCount (colorVertex C' v b) A = uncoloredCount C' A - 1 :=
          uncoloredCount_colorVertex hv hvA b
        have huc1 : 0 < uncoloredCount C' A :=
          Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨hvA, hv⟩⟩
        have hucEq : uncoloredCount C' A
            = uncoloredCount (colorVertex C' v b) A + 1 := by omega
        have hw' : edgeWeight C' A = (2:ℝ)^(-((uncoloredCount C' A : ℤ) + 1)) := by
          unfold edgeWeight
          rw [ite_eq_left hcol', ite_eq_left hmono']
        have hstep := hnot2 A hAF
        rw [hw'] at hstep
        have h2 : (2:ℝ)^(-((uncoloredCount (colorVertex C' v b) A : ℤ)))
            = 4 * (2:ℝ)^(-((uncoloredCount C' A : ℤ) + 1)) := by
          rw [hucEq]
          push_cast
          have e : (-((uncoloredCount (colorVertex C' v b) A : ℤ)))
              = (2:ℤ) + (-(((uncoloredCount (colorVertex C' v b) A : ℤ) + 1) + 1)) := by
            ring
          rw [e, zpow_add₀ (by norm_num : (2:ℝ) ≠ 0), real_two_zpow_two]
        calc (2:ℝ)^(-((uncoloredCount (colorVertex C' v b) A : ℤ)))
            = 4 * (2:ℝ)^(-((uncoloredCount C' A : ℤ) + 1)) := h2
          _ < w₀ := by
              have h4 : (4:ℝ) * (w₀ / 4) = w₀ := by ring
              calc 4 * (2:ℝ)^(-((uncoloredCount C' A : ℤ) + 1))
                  < 4 * (w₀ / 4) := mul_lt_mul_of_pos_left hstep (by norm_num)
                _ = w₀ := h4
      · -- completely uncolored before the step
        have hnone' : ∀ x ∈ A, C' x = none := fun x hx => by
          by_contra hxc; exact hcol' ⟨x, hx, hxc⟩
        have hcardA : A.card = uncoloredCount C' A := by
          rw [uncoloredCount, Finset.filter_eq_self.mpr (fun x hx => hnone' x hx)]
        have huc : uncoloredCount (colorVertex C' v b) A = uncoloredCount C' A - 1 :=
          uncoloredCount_colorVertex hv hvA b
        have huc1 : 0 < uncoloredCount C' A :=
          Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨hvA, hv⟩⟩
        have hw' : edgeWeight C' A = (2:ℝ)^(-((A.card : ℕ) : ℤ)) := by
          unfold edgeWeight
          rw [ite_eq_right hcol']
        have hstep := hnot2 A hAF
        rw [hw'] at hstep
        have h2 : (2:ℝ)^(-((uncoloredCount (colorVertex C' v b) A : ℤ)))
            = 2 * (2:ℝ)^(-((A.card : ℕ) : ℤ)) := by
          have hcast : ((uncoloredCount (colorVertex C' v b) A : ℕ) : ℤ)
              = (A.card : ℤ) - 1 := by
            rw [huc, hcardA]
            omega
          rw [hcast]
          have e : (-((A.card : ℤ) - 1)) = (1:ℤ) + (-((A.card : ℤ))) := by ring
          rw [e, zpow_add₀ (by norm_num : (2:ℝ) ≠ 0), zpow_one]
        calc (2:ℝ)^(-((uncoloredCount (colorVertex C' v b) A : ℤ)))
            = 2 * (2:ℝ)^(-((A.card : ℕ) : ℤ)) := h2
          _ < w₀ := by
              have h4 : (2:ℝ) * (w₀ / 4) = w₀ / 2 := by ring
              have h5 : w₀ / 2 < w₀ := by linarith
              calc 2 * (2:ℝ)^(-((A.card : ℕ) : ℤ)) < 2 * (w₀ / 4) :=
                    mul_lt_mul_of_pos_left hstep two_pos
                _ = w₀ / 2 := h4
                _ < w₀ := h5
    · -- a disagreement at C' survives, contradicting monochromaticity at C
      exact absurd hmono (Monochromatic.colorVertex_persist hv hmono')
  · -- v outside the edge: weights agree
    have hsame : edgeWeight (colorVertex C' v b) A = edgeWeight C' A :=
      edgeWeight_colorVertex_of_not_mem C' A v b hvA
    have hle := residual_pow_le (colorVertex C' v b) A hmono
    calc (2:ℝ)^(-((uncoloredCount (colorVertex C' v b) A : ℤ)))
        ≤ 2 * edgeWeight (colorVertex C' v b) A := hle
      _ = 2 * edgeWeight C' A := by rw [hsame]
      _ < w₀ := by
          have h1 := hnot2 A hAF
          have h2 : (2:ℝ) * (w₀ / 4) < w₀ := by
            have : (2:ℝ) * (w₀ / 4) = w₀ / 2 := by ring
            rw [this]; linarith
          calc 2 * edgeWeight C' A < 2 * (w₀ / 4) :=
                mul_lt_mul_of_pos_left h1 two_pos
            _ < w₀ := h2

/-! ### The total residual weight -/

/-- The total weight of the residual family is at most twice the total weight:
each monochromatic edge contributes `2^{-f} ≤ 2 · edgeWeight`. -/
lemma residual_total_le (C : PCol α) (F : Finset (Finset α)) :
    ∑ A' ∈ residualEdges C F, (2:ℝ)^(-((A'.card : ℕ) : ℤ)) ≤ 2 * totalWeight C F := by
  classical
  calc ∑ A' ∈ residualEdges C F, (2:ℝ)^(-((A'.card : ℕ) : ℤ))
      = ∑ A' ∈ (F.filter (fun A => Monochromatic C A)).image
            (fun A => A.filter fun x => C x = none),
          (2:ℝ)^(-((A'.card : ℕ) : ℤ)) := rfl
    _ ≤ ∑ A ∈ F.filter (fun A => Monochromatic C A),
          (2:ℝ)^(-(((A.filter fun x => C x = none).card : ℕ) : ℤ)) :=
          sum_image_le _ _ _ (fun _d => by positivity)
    _ ≤ ∑ A ∈ F.filter (fun A => Monochromatic C A), 2 * edgeWeight C A :=
          Finset.sum_le_sum (fun A hA =>
            residual_pow_le C A (Finset.mem_filter.mp hA).2)
    _ ≤ 2 * ∑ A ∈ F.filter (fun A => Monochromatic C A), edgeWeight C A := by
          rw [Finset.mul_sum]
    _ ≤ 2 * ∑ A ∈ F, edgeWeight C A :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_mono_set_of_nonneg (fun A => edgeWeight_nonneg C A)
              (Finset.filter_subset _ _)) (by norm_num)
    _ = 2 * totalWeight C F := rfl

/-! ### L5: the completion theorem (Kooshi's iii) -/

/-- **L5 (Kooshi's observation iii)**: assume Beck's theorem in the non-uniform
weighted form (for total weight `≤ 4c` and all edge weights `≤ w₀` a proper
two-coloring exists; this is Beck 1978, Theorem 1.2, to be formalized in L4).
If `C = colorVertex C' v b` is obtained by coloring the uncolored vertex `v`,
every edge had weight `< w₀/4` at `C'`, and the total weight of `C` is `≤ 2c`,
then `C` can be extended to a **proper total coloring** of `F`: every edge
contains two vertices with different colors. -/
theorem exists_proper_extension (C' : PCol α) (v : α) (b : Bool)
    (F : Finset (Finset α)) (c w₀ : ℝ) (hc : 0 < c) (hw₀ : 0 < w₀)
    (hbeck : ∀ G : Finset (Finset α),
      (∑ A ∈ G, (2:ℝ)^(-((A.card : ℕ) : ℤ))) ≤ 4 * c →
      (∀ A ∈ G, (2:ℝ)^(-((A.card : ℕ) : ℤ)) ≤ w₀) →
      ∃ h : α → Bool, ∀ A ∈ G, ∃ x ∈ A, ∃ y ∈ A, h x ≠ h y)
    (hv : C' v = none)
    (hnot1 : totalWeight (colorVertex C' v b) F ≤ 2 * c)
    (hnot2 : ∀ A ∈ F, edgeWeight C' A < w₀ / 4) :
    ∃ H : α → Bool,
      (∀ x, ∀ d : Bool, colorVertex C' v b x = some d → H x = d) ∧
      ∀ A ∈ F, ∃ x ∈ A, ∃ y ∈ A, H x ≠ H y := by
  classical
  set C : PCol α := colorVertex C' v b with hC
  set G : Finset (Finset α) := residualEdges C F with hG
  -- Beck's hypotheses on the residual family
  have hGtotal : (∑ A ∈ G, (2:ℝ)^(-((A.card : ℕ) : ℤ))) ≤ 4 * c := by
    have h1 := residual_total_le C F
    have h2 : 2 * totalWeight C F ≤ 4 * c := by
      have : totalWeight C F ≤ 2 * c := hnot1
      linarith
    exact le_trans h1 h2
  have hGmax : ∀ A ∈ G, (2:ℝ)^(-((A.card : ℕ) : ℤ)) ≤ w₀ := by
    intro A hA
    obtain ⟨A₀, hA₀F, hmono, hAeq⟩ := mem_residualEdges.mp hA
    have hres := residual_weight_lt C' v b F w₀ hv hw₀ hnot2 hA₀F hmono
    rw [hAeq]
    exact le_of_lt hres
  obtain ⟨h, hhprop⟩ := hbeck G hGtotal hGmax
  refine ⟨fun x => match C x with | some d => d | none => h x, ?_, ?_⟩
  · intro x d hd
    show (match C x with | some d' => d' | none => h x) = d
    rw [hd]
  · intro A hAF
    by_cases hmono : Monochromatic C A
    · -- monochromatic: its uncolored part is a residual edge; Beck colors it
      have hGmem : A.filter (fun x => C x = none) ∈ G :=
        mem_residualEdges.mpr ⟨A, hAF, hmono, rfl⟩
      obtain ⟨x, hx, y, hy, hne⟩ := hhprop _ hGmem
      have hx0 : C x = none := (Finset.mem_filter.mp hx).2
      have hy0 : C y = none := (Finset.mem_filter.mp hy).2
      refine ⟨x, (Finset.mem_filter.mp hx).1, y, (Finset.mem_filter.mp hy).1, ?_⟩
      show (match C x with | some d' => d' | none => h x) ≠
          (match C y with | some d' => d' | none => h y)
      rw [hx0, hy0]
      exact hne
    · -- non-monochromatic: extract the existing disagreement
      obtain ⟨x, hx, y, hy, hxc, hyc, hne⟩ := (not_monochromatic_iff C A).mp hmono
      obtain ⟨dx, hdx⟩ := Option.ne_none_iff_exists.mp hxc
      obtain ⟨dy, hdy⟩ := Option.ne_none_iff_exists.mp hyc
      have hne' : dx ≠ dy := by
        intro hcon
        exact hne (by rw [← hdx, ← hdy, hcon])
      refine ⟨x, hx, y, hy, ?_⟩
      show (match C x with | some d' => d' | none => h x) ≠
          (match C y with | some d' => d' | none => h y)
      rw [← hdx, ← hdy]
      exact hne'

end Erdos1027
