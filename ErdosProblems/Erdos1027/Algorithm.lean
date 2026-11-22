/-
JSP-000854 (Erdos Problem 1027) - L2: the frozen coloring process, the
supermartingale induction, and the counting Markov bound.

The random experiment lives on `Fin m → Bool` (m independent coin flips). The
"frozen" process colors one uncolored vertex per step (chosen by an abstract
selector `sel`; in later layers this is the min-weight vertex) and freezes
forever once the abstract stopping condition holds or the m steps are used up.
The selection rule is irrelevant for the supermartingale property: L1 holds for
*any* uncolored vertex, so `E[W_{t+1}] ≤ W_t` under every selector.
-/
import ErdosProblems.Erdos1027.Weights

namespace Erdos1027

open scoped Classical

variable {α : Type} [DecidableEq α]

/-! ### Small helper lemmas -/

/-- Coloring `v` leaves the color of any other vertex unchanged. -/
lemma colorVertex_apply_of_ne (C : PCol α) (v : α) (b : Bool) {x : α} (h : x ≠ v) :
    colorVertex C v b x = C x := by
  simp only [colorVertex, ite_eq_right h]

/-- Total weight is nonnegative. -/
lemma totalWeight_nonneg (C : PCol α) (F : Finset (Finset α)) : 0 ≤ totalWeight C F := by
  refine Finset.sum_nonneg ?_
  intro A _
  unfold edgeWeight
  split_ifs with h1 h2
  · positivity
  · positivity
  · positivity

/-! ### L2a: coloring a vertex outside an edge does not change its weight -/

lemma edgeWeight_colorVertex_of_not_mem (C : PCol α) (A : Finset α) (v : α) (b : Bool)
    (hv : v ∉ A) : edgeWeight (colorVertex C v b) A = edgeWeight C A := by
  have hxv : ∀ x ∈ A, x ≠ v := by
    intro x hx hxe
    exact hv (hxe ▸ hx)
  have e1 : (∃ x ∈ A, colorVertex C v b x ≠ none) ↔ (∃ x ∈ A, C x ≠ none) := by
    constructor
    · rintro ⟨x, hx, hxc⟩
      exact ⟨x, hx, by rw [colorVertex_apply_of_ne C v b (hxv x hx)] at hxc; exact hxc⟩
    · rintro ⟨x, hx, hxc⟩
      exact ⟨x, hx, by rw [colorVertex_apply_of_ne C v b (hxv x hx)]; exact hxc⟩
  have e2 : Monochromatic (colorVertex C v b) A ↔ Monochromatic C A := by
    unfold Monochromatic
    constructor
    · intro h x hx y hy hxc hyc
      have p1 : colorVertex C v b x ≠ none := by
        rw [colorVertex_apply_of_ne C v b (hxv x hx)]
        exact hxc
      have p2 : colorVertex C v b y ≠ none := by
        rw [colorVertex_apply_of_ne C v b (hxv y hy)]
        exact hyc
      have heq := h x hx y hy p1 p2
      rw [colorVertex_apply_of_ne C v b (hxv x hx)] at heq
      rw [colorVertex_apply_of_ne C v b (hxv y hy)] at heq
      exact heq
    · intro h x hx y hy hxc hyc
      rw [colorVertex_apply_of_ne C v b (hxv x hx)] at hxc
      rw [colorVertex_apply_of_ne C v b (hxv y hy)] at hyc
      rw [colorVertex_apply_of_ne C v b (hxv x hx),
        colorVertex_apply_of_ne C v b (hxv y hy)]
      exact h x hx y hy hxc hyc
  have e3 : uncoloredCount (colorVertex C v b) A = uncoloredCount C A := by
    unfold uncoloredCount
    congr 1
    ext x
    simp only [Finset.mem_filter, colorVertex_eq_none_iff]
    tauto
  unfold edgeWeight
  simp only [e1, e2, e3]

/-! ### L2b: the supermartingale step for the total weight -/

/-- **L2 core step**: coloring any uncolored vertex `v` never increases the
*expected* total weight (expectation = average over the two colors). -/
lemma totalWeight_colorVertex_le (C : PCol α) (F : Finset (Finset α)) (v : α)
    (hv : C v = none) :
    (∑ b : Bool, totalWeight (colorVertex C v b) F) / 2 ≤ totalWeight C F := by
  have key : ∀ A ∈ F, (∑ b : Bool, edgeWeight (colorVertex C v b) A) ≤ 2 * edgeWeight C A := by
    intro A hA
    by_cases hvA : v ∈ A
    · have h := edgeWeight_colorVertex_le C A v hv hvA
      rw [div_le_iff₀ two_pos] at h
      linarith
    · simp only [sum_bool_eq,
        fun b => edgeWeight_colorVertex_of_not_mem C A v b hvA]
      linarith
  calc (∑ b : Bool, totalWeight (colorVertex C v b) F) / 2
      = (∑ A ∈ F, ∑ b : Bool, edgeWeight (colorVertex C v b) A) / 2 := by
        simp only [totalWeight]
        rw [Finset.sum_comm]
    _ ≤ ∑ A ∈ F, edgeWeight C A := by
        rw [div_le_iff₀ two_pos]
        have h1 : (∑ A ∈ F, ∑ b : Bool, edgeWeight (colorVertex C v b) A)
            ≤ ∑ A ∈ F, 2 * edgeWeight C A := Finset.sum_le_sum key
        have h2 : (∑ A ∈ F, 2 * edgeWeight C A)
            = 2 * ∑ A ∈ F, edgeWeight C A := by
          rw [Finset.mul_sum]
        linarith
    _ = totalWeight C F := rfl

/-! ### L2c: coordinate-splitting identity for sums over `Fin m → Bool` -/

/-- Averaging over the two possible values of coordinate `t`:
`∑_ω ∑_b f (update ω t b) = 2 * ∑_ω f ω`. -/
lemma sum_update_twice (m : ℕ) (t : Fin m) (f : (Fin m → Bool) → ℝ) :
    ∑ ω : Fin m → Bool, ∑ b : Bool, f (Function.update ω t b) = 2 * ∑ ω : Fin m → Bool, f ω := by
  have hp : ∀ ω : Fin m → Bool,
      ∑ b : Bool, f (Function.update ω t b) = f ω + f (Function.update ω t (!ω t)) := by
    intro ω
    rw [sum_bool_eq]
    cases hb : ω t with
    | false =>
      have e1 : Function.update ω t true = Function.update ω t (!ω t) := by rw [hb]; simp
      have e2 : Function.update ω t false = ω := by
        rw [← hb, Function.update_eq_self]
      rw [e2, ← hb, e1]
      ring
    | true =>
      have e1 : Function.update ω t false = Function.update ω t (!ω t) := by rw [hb]; simp
      have e2 : Function.update ω t true = ω := by
        rw [← hb, Function.update_eq_self]
      rw [e2, ← hb, e1]
  have hψ : Function.Involutive (fun ω : Fin m → Bool => Function.update ω t (!ω t)) := by
    intro ω
    dsimp only
    have hself : (Function.update ω t (!ω t)) t = !ω t := Function.update_self t (!ω t) ω
    have hne : (!ω t) ≠ ω t := by cases hb : ω t <;> simp
    rw [hself, Bool.not_not, Function.update_idem, Function.update_eq_self]
  rw [Finset.sum_congr rfl (fun ω _ => hp ω), Finset.sum_add_distrib]
  have hsum : ∑ ω : Fin m → Bool, f (Function.update ω t (!ω t))
      = ∑ ω : Fin m → Bool, f ω :=
    Equiv.sum_comp (Equiv.ofBijective _ hψ.bijective) f
  rw [hsum]
  ring

/-! ### L2d: the frozen process -/

/-- The `t`-th random bit (`false` past the end). -/
def bitAt (ω : Fin m → Bool) (t : ℕ) : Bool := if h : t < m then ω ⟨t, h⟩ else false

lemma bitAt_update_of_ne (ω : Fin m → Bool) (j : Fin m) (b : Bool) (k : ℕ)
    (hk : k ≠ (j : ℕ)) :
    bitAt (Function.update ω j b) k = bitAt ω k := by
  unfold bitAt
  by_cases hkm : k < m
  · rw [dite_eq_left hkm, dite_eq_left hkm]
    have hne : (⟨k, hkm⟩ : Fin m) ≠ j := by
      intro hc
      exact hk (by rw [← hc])
    exact Function.update_of_ne hne b ω
  · rw [dite_eq_right hkm, dite_eq_right hkm]

lemma bitAt_update_self (ω : Fin m → Bool) (j : Fin m) (b : Bool) :
    bitAt (Function.update ω j b) (j : ℕ) = b := by
  unfold bitAt
  rw [dite_eq_left j.isLt]
  exact Function.update_self j b ω

/-- The frozen coloring process: at step `t+1` (for `t < m`), unless the stopping
condition already holds, vertex `sel C` is given color `bitAt ω t`. Once stopped
(or past step `m`) the coloring stays frozen. -/
def frozen (sel : PCol α → α) (stop : PCol α → Prop) [DecidablePred stop]
    (C₀ : PCol α) (ω : Fin m → Bool) : ℕ → PCol α
  | 0 => C₀
  | t + 1 =>
    if _h : t ≥ m ∨ stop (frozen sel stop C₀ ω t) then frozen sel stop C₀ ω t
    else colorVertex (frozen sel stop C₀ ω t) (sel (frozen sel stop C₀ ω t)) (bitAt ω t)

lemma frozen_succ (sel : PCol α → α) (stop : PCol α → Prop) [DecidablePred stop]
    (C₀ : PCol α) (ω : Fin m → Bool) (t : ℕ) :
    frozen sel stop C₀ ω (t + 1) =
      if _h : t ≥ m ∨ stop (frozen sel stop C₀ ω t) then frozen sel stop C₀ ω t
      else colorVertex (frozen sel stop C₀ ω t) (sel (frozen sel stop C₀ ω t)) (bitAt ω t) :=
  rfl

lemma frozen_zero (sel : PCol α → α) (stop : PCol α → Prop) [DecidablePred stop]
    (C₀ : PCol α) (ω : Fin m → Bool) : frozen sel stop C₀ ω 0 = C₀ := rfl

lemma frozen_le_stopped (sel : PCol α → α) (stop : PCol α → Prop) [DecidablePred stop]
    (C₀ : PCol α) (ω : Fin m → Bool) (t : ℕ)
    (h : t ≥ m ∨ stop (frozen sel stop C₀ ω t)) :
    frozen sel stop C₀ ω (t + 1) = frozen sel stop C₀ ω t := by
  rw [frozen_succ]
  exact dite_eq_left h

lemma frozen_lt_color (sel : PCol α → α) (stop : PCol α → Prop) [DecidablePred stop]
    (C₀ : PCol α) (ω : Fin m → Bool) (t : ℕ) (htm : t < m)
    (h : ¬ stop (frozen sel stop C₀ ω t)) :
    frozen sel stop C₀ ω (t + 1) =
      colorVertex (frozen sel stop C₀ ω t) (sel (frozen sel stop C₀ ω t)) (bitAt ω t) := by
  rw [frozen_succ]
  exact dite_eq_right (by
    intro hc
    rcases hc with hx | hs
    · omega
    · exact h hs)

/-- The frozen process at time `k ≤ j` does not depend on bit `j`. -/
lemma frozen_update_of_le (sel : PCol α → α) (stop : PCol α → Prop) [DecidablePred stop]
    (C₀ : PCol α) (ω : Fin m → Bool) (j : Fin m) (b : Bool) (k : ℕ) (hk : k ≤ (j : ℕ)) :
    frozen sel stop C₀ (Function.update ω j b) k = frozen sel stop C₀ ω k := by
  have hjm : (j : ℕ) < m := j.isLt
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [frozen_succ, frozen_succ, ih (by omega),
      bitAt_update_of_ne ω j b k (by omega)]

/-! ### L2e: supermartingale induction -/

/-- One supermartingale step: the sum over all bit strings of the total weight of
the frozen process does not increase from `t` to `t+1`. -/
lemma frozen_sum_step_le (sel : PCol α → α) (stop : PCol α → Prop) [DecidablePred stop]
    (hsel : ∀ C, ¬ stop C → C (sel C) = none)
    (C₀ : PCol α) (F : Finset (Finset α)) (t : ℕ) (htm : t < m) :
    ∑ ω : Fin m → Bool, totalWeight (frozen sel stop C₀ ω (t + 1)) F
      ≤ ∑ ω : Fin m → Bool, totalWeight (frozen sel stop C₀ ω t) F := by
  have idd := sum_update_twice m (t := ⟨t, htm⟩)
    (fun ω => totalWeight (frozen sel stop C₀ ω (t + 1)) F)
  have pt : ∀ ω : Fin m → Bool,
      ∑ b : Bool, totalWeight
          (frozen sel stop C₀ (Function.update ω ⟨t, htm⟩ b) (t + 1)) F
        ≤ 2 * totalWeight (frozen sel stop C₀ ω t) F := by
    intro ω
    by_cases hstop : stop (frozen sel stop C₀ ω t)
    · -- stopped: frozen already, weight unchanged
      have heq : ∀ b : Bool,
          frozen sel stop C₀ (Function.update ω ⟨t, htm⟩ b) (t + 1)
            = frozen sel stop C₀ ω t := by
        intro b
        have h1 : stop (frozen sel stop C₀ (Function.update ω ⟨t, htm⟩ b) t) := by
          rw [frozen_update_of_le sel stop C₀ ω ⟨t, htm⟩ b t (le_refl t)]
          exact hstop
        rw [frozen_le_stopped sel stop C₀ _ t (Or.inr h1),
          frozen_update_of_le sel stop C₀ ω ⟨t, htm⟩ b t (le_refl t)]
      simp only [heq, sum_bool_eq]
      linarith
    · -- not stopped: each extension colors `sel (frozen ω t)` with bit `b`
      have hu : ∀ b : Bool,
          frozen sel stop C₀ (Function.update ω ⟨t, htm⟩ b) (t + 1)
            = colorVertex (frozen sel stop C₀ ω t) (sel (frozen sel stop C₀ ω t)) b := by
        intro b
        have hstop' : ¬ stop (frozen sel stop C₀ (Function.update ω ⟨t, htm⟩ b) t) := by
          rw [frozen_update_of_le sel stop C₀ ω ⟨t, htm⟩ b t (le_refl t)]
          exact hstop
        rw [frozen_lt_color sel stop C₀ (Function.update ω ⟨t, htm⟩ b) t htm hstop']
        rw [frozen_update_of_le sel stop C₀ ω ⟨t, htm⟩ b t (le_refl t)]
        rw [bitAt_update_self ω ⟨t, htm⟩ b]
      have hstep := totalWeight_colorVertex_le (frozen sel stop C₀ ω t) F
        (sel (frozen sel stop C₀ ω t)) (hsel _ hstop)
      rw [div_le_iff₀ two_pos] at hstep
      simp only [hu]
      linarith
  calc ∑ ω : Fin m → Bool, totalWeight (frozen sel stop C₀ ω (t + 1)) F
      = (∑ ω : Fin m → Bool, ∑ b : Bool, totalWeight
          (frozen sel stop C₀ (Function.update ω ⟨t, htm⟩ b) (t + 1)) F) / 2 := by
        rw [idd]; field_simp
    _ ≤ ∑ ω : Fin m → Bool, totalWeight (frozen sel stop C₀ ω t) F := by
        have h1 : (∑ ω : Fin m → Bool, ∑ b : Bool, totalWeight
            (frozen sel stop C₀ (Function.update ω ⟨t, htm⟩ b) (t + 1)) F)
            ≤ ∑ ω : Fin m → Bool, 2 * totalWeight (frozen sel stop C₀ ω t) F :=
          Finset.sum_le_sum (fun ω _ => pt ω)
        have h2 : (∑ ω : Fin m → Bool, 2 * totalWeight (frozen sel stop C₀ ω t) F)
            = 2 * ∑ ω : Fin m → Bool, totalWeight (frozen sel stop C₀ ω t) F := by
          rw [Finset.mul_sum]
        rw [div_le_iff₀ two_pos]
        linarith

/-- **L2 main bound**: the average total weight of the frozen process never
exceeds the initial total weight. -/
lemma frozen_sum_le (sel : PCol α → α) (stop : PCol α → Prop) [DecidablePred stop]
    (hsel : ∀ C, ¬ stop C → C (sel C) = none)
    (C₀ : PCol α) (F : Finset (Finset α)) (t : ℕ) :
    ∑ ω : Fin m → Bool, totalWeight (frozen sel stop C₀ ω t) F
      ≤ ((2 ^ m : ℕ) : ℝ) * totalWeight C₀ F := by
  induction t with
  | zero =>
    have h0 : ∀ ω : Fin m → Bool, frozen sel stop C₀ ω 0 = C₀ := fun ω => rfl
    simp only [h0]
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : (Finset.univ : Finset (Fin m → Bool)).card = 2 ^ m := by
      rw [Finset.card_univ, Fintype.card_pi]
      simp
    rw [hcard]
  | succ t ih =>
    by_cases htm : t < m
    · calc ∑ ω : Fin m → Bool, totalWeight (frozen sel stop C₀ ω (t + 1)) F
          ≤ ∑ ω : Fin m → Bool, totalWeight (frozen sel stop C₀ ω t) F :=
          frozen_sum_step_le sel stop hsel C₀ F t htm
        _ ≤ ((2 ^ m : ℕ) : ℝ) * totalWeight C₀ F := ih
    · have heq : ∀ ω : Fin m → Bool,
          frozen sel stop C₀ ω (t + 1) = frozen sel stop C₀ ω t :=
        fun ω => frozen_le_stopped sel stop C₀ ω t (Or.inl (by omega))
      simp only [heq]
      exact ih

/-! ### L2f: counting Markov bound -/

/-- Counting Markov: a nonnegative function on the finite space with sum `≤ B`
has `{f > K}` of cardinal at most `B / K`. -/
lemma count_le_of_sum_le (m : ℕ) (f : (Fin m → Bool) → ℝ) (hf : ∀ ω, 0 ≤ f ω)
    (K : ℝ) (_hK : 0 < K) (B : ℝ) (hB : (∑ ω : Fin m → Bool, f ω) ≤ B) :
    ((Finset.univ.filter (fun (ω : Fin m → Bool) => K < f ω)).card : ℝ) * K ≤ B := by
  have h1 : ((Finset.univ.filter (fun (ω : Fin m → Bool) => K < f ω)).card : ℝ) * K
      = ∑ ω ∈ Finset.univ.filter (fun (ω : Fin m → Bool) => K < f ω), K := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have h2 : ∑ ω ∈ Finset.univ.filter (fun (ω : Fin m → Bool) => K < f ω), K
      ≤ ∑ ω ∈ Finset.univ.filter (fun (ω : Fin m → Bool) => K < f ω), f ω := by
    refine Finset.sum_le_sum ?_
    intro ω hω
    exact le_of_lt (Finset.mem_filter.mp hω).2
  have h3 : ∑ ω ∈ Finset.univ.filter (fun (ω : Fin m → Bool) => K < f ω), f ω
      ≤ ∑ ω : Fin m → Bool, f ω :=
    Finset.sum_mono_set_of_nonneg hf (Finset.filter_subset _ _)
  linarith

/-- **L2 conclusion (Markov at threshold `K`)**: the number of bit strings on
which the frozen process exceeds weight `K` is at most `2^m · W₀ / K`. -/
lemma frozen_markov (sel : PCol α → α) (stop : PCol α → Prop) [DecidablePred stop]
    (hsel : ∀ C, ¬ stop C → C (sel C) = none)
    (C₀ : PCol α) (F : Finset (Finset α)) (t : ℕ) (K : ℝ) (hK : 0 < K) :
    ((Finset.univ.filter (fun (ω : Fin m → Bool) =>
        K < totalWeight (frozen sel stop C₀ ω t) F)).card : ℝ) * K
      ≤ ((2 ^ m : ℕ) : ℝ) * totalWeight C₀ F :=
  count_le_of_sum_le m
    (fun ω => totalWeight (frozen sel stop C₀ ω t) F)
    (fun _ω => totalWeight_nonneg _ F) K hK _
    (frozen_sum_le sel stop hsel C₀ F t)

/-! ### L2g: the initial total weight -/

/-- Every edge has initial weight `2^{-n}` under the empty coloring, when
`A.card = n`. -/
lemma edgeWeight_empty_le (A : Finset α) (n : ℕ) (hA : A.card = n) :
    edgeWeight (fun _ => (none : Option Bool)) A = (2 : ℝ) ^ (-(n : ℤ)) := by
  unfold edgeWeight
  rw [ite_eq_right (by rintro ⟨x, _, hx⟩; exact hx rfl), hA]

/-- The initial total weight of a family of at most `c·2ⁿ` many `n`-sets is at
most `c`. -/
lemma totalWeight_init_le (F : Finset (Finset α)) (n : ℕ) (c : ℝ)
    (hFn : ∀ A ∈ F, A.card = n) (hcard : (F.card : ℝ) ≤ c * ((2 ^ n : ℕ) : ℝ)) :
    totalWeight (fun _ => (none : Option Bool)) F ≤ c := by
  rw [totalWeight, Finset.sum_congr rfl (fun A hA => edgeWeight_empty_le A n (hFn A hA)),
    Finset.sum_const, nsmul_eq_mul]
  have hz : (2 : ℝ) ^ (-(n : ℤ)) = ((2 ^ n : ℕ) : ℝ)⁻¹ := by
    rw [zpow_neg, zpow_natCast, Nat.cast_pow]
    norm_num
  rw [hz]
  have hx0 : ((2 ^ n : ℕ) : ℝ) ≠ 0 := by positivity
  calc ((F.card : ℕ) : ℝ) * ((2 ^ n : ℕ) : ℝ)⁻¹
      ≤ c * ((2 ^ n : ℕ) : ℝ) * ((2 ^ n : ℕ) : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right hcard (inv_nonneg.mpr (by positivity))
    _ = c := by rw [mul_assoc, mul_inv_cancel₀ hx0, mul_one]

end Erdos1027
