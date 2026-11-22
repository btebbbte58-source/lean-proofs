/-
JSP-000854 (Erdos Problem 1027) - L6: the counting layer.

`goodCount C F` is the number of good sets `B ⊆ X = F.biUnion id` compatible
with the partial coloring `C` (i.e. proper total colorings of `X` extending
`C`, encoded by their blue set).  The step lemma `goodCount_split` says that
coloring one more uncolored vertex splits the count: `N(C) = N(C⁺) + N(C⁻)`.
This drives the martingale identity `∑_ω 2^{T(ω)} · N(C_{T(ω)}) = 2^m · N(C₀)`
(the counting form of the optional stopping theorem).
-/
import ErdosProblems.Erdos1027.Completion

namespace Erdos1027

open scoped Classical

variable {α : Type} [DecidableEq α]

/-! ### Good sets and the count -/

/-- A subset `B ⊆ X` is *compatible* with the partial coloring `C` if it
contains all `true`-colored vertices of `X` and none of the `false`-colored
ones (uncolored vertices are unconstrained). -/
def Compatible (C : PCol α) (X : Finset α) (B : Finset α) : Prop :=
  (∀ x ∈ X, C x = some true → x ∈ B) ∧ ∀ x ∈ X, C x = some false → x ∉ B

/-- `B` is a *good set* for `F`: it meets every edge of `F` and contains none
of them. -/
def GoodSet (F : Finset (Finset α)) (B : Finset α) : Prop :=
  ∀ A ∈ F, (A ∩ B).Nonempty ∧ ∃ x ∈ A, x ∉ B

/-- The counting predicate: `B` is a good set compatible with `C`. -/
def CountedPred (C : PCol α) (F : Finset (Finset α)) (B : Finset α) : Prop :=
  Compatible C (F.biUnion id) B ∧ GoodSet F B

noncomputable instance countedPredDecidable (C : PCol α) (F : Finset (Finset α)) :
    DecidablePred (CountedPred C F) := Classical.decPred _

/-- The count of good sets compatible with the partial coloring `C`. -/
noncomputable def goodCount (C : PCol α) (F : Finset (Finset α)) : ℕ :=
  ((F.biUnion id).powerset.filter (CountedPred C F)).card

/-! ### Membership rewrites after one coloring step -/

/-- Coloring `v` assigns it exactly color `b`. -/
lemma colorVertex_self (C : PCol α) (v : α) (b : Bool) :
    colorVertex C v b v = some b := by
  simp [colorVertex]

/-- A counted set for `C` that contains `v` is exactly a counted set for the
coloring that sets `v` to `true`. -/
lemma mem_filter_counted_true_iff (C : PCol α) (F : Finset (Finset α)) (v : α)
    (hv : C v = none) (hvx : v ∈ F.biUnion id) (B : Finset α) :
    B ∈ (F.biUnion id).powerset.filter (CountedPred (colorVertex C v true) F) ↔
      B ∈ (F.biUnion id).powerset.filter (CountedPred C F) ∧ v ∈ B := by
  classical
  constructor
  · intro hmem
    simp only [Finset.mem_filter, Finset.mem_powerset, CountedPred] at hmem
    obtain ⟨hBsub, hcomp, hgood⟩ := hmem
    obtain ⟨hcompT, hcompF⟩ := hcomp
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hBsub, ⟨⟨?_, ?_⟩, hgood⟩⟩,
      hcompT v hvx (colorVertex_self C v true)⟩
    · intro x hx hxc
      by_cases hxv : x = v
      · subst hxv
        simp [hv] at hxc
      · rw [← colorVertex_apply_of_ne C v true hxv] at hxc
        exact hcompT x hx hxc
    · intro x hx hxc
      by_cases hxv : x = v
      · subst hxv
        simp [hv] at hxc
      · rw [← colorVertex_apply_of_ne C v true hxv] at hxc
        exact hcompF x hx hxc
  · rintro ⟨hmem, hvB⟩
    simp only [Finset.mem_filter, Finset.mem_powerset, CountedPred] at hmem
    obtain ⟨hBsub, hcomp, hgood⟩ := hmem
    obtain ⟨hcompT, hcompF⟩ := hcomp
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hBsub,
      ⟨⟨?_, ?_⟩, hgood⟩⟩
    · intro x hx hxc
      by_cases hxv : x = v
      · subst hxv
        exact hvB
      · rw [colorVertex_apply_of_ne C v true hxv] at hxc
        exact hcompT x hx hxc
    · intro x hx hxc
      by_cases hxv : x = v
      · subst hxv
        rw [colorVertex_self] at hxc
        exact absurd hxc (by simp)
      · rw [colorVertex_apply_of_ne C v true hxv] at hxc
        exact hcompF x hx hxc

/-- A counted set for `C` that does not contain `v` is exactly a counted set
for the coloring that sets `v` to `false`. -/
lemma mem_filter_counted_false_iff (C : PCol α) (F : Finset (Finset α)) (v : α)
    (hv : C v = none) (hvx : v ∈ F.biUnion id) (B : Finset α) :
    B ∈ (F.biUnion id).powerset.filter (CountedPred (colorVertex C v false) F) ↔
      B ∈ (F.biUnion id).powerset.filter (CountedPred C F) ∧ v ∉ B := by
  classical
  constructor
  · intro hmem
    simp only [Finset.mem_filter, Finset.mem_powerset, CountedPred] at hmem
    obtain ⟨hBsub, hcomp, hgood⟩ := hmem
    obtain ⟨hcompT, hcompF⟩ := hcomp
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hBsub, ⟨⟨?_, ?_⟩, hgood⟩⟩,
      hcompF v hvx (colorVertex_self C v false)⟩
    · intro x hx hxc
      by_cases hxv : x = v
      · subst hxv
        simp [hv] at hxc
      · rw [← colorVertex_apply_of_ne C v false hxv] at hxc
        exact hcompT x hx hxc
    · intro x hx hxc
      by_cases hxv : x = v
      · subst hxv
        simp [hv] at hxc
      · rw [← colorVertex_apply_of_ne C v false hxv] at hxc
        exact hcompF x hx hxc
  · rintro ⟨hmem, hvB⟩
    simp only [Finset.mem_filter, Finset.mem_powerset, CountedPred] at hmem
    obtain ⟨hBsub, hcomp, hgood⟩ := hmem
    obtain ⟨hcompT, hcompF⟩ := hcomp
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hBsub,
      ⟨⟨?_, ?_⟩, hgood⟩⟩
    · intro x hx hxc
      by_cases hxv : x = v
      · subst hxv
        rw [colorVertex_self] at hxc
        exact absurd hxc (by simp)
      · rw [colorVertex_apply_of_ne C v false hxv] at hxc
        exact hcompT x hx hxc
    · intro x hx hxc
      by_cases hxv : x = v
      · subst hxv
        exact hvB
      · rw [colorVertex_apply_of_ne C v false hxv] at hxc
        exact hcompF x hx hxc

/-! ### The step splitting of the count -/

/-- **L6 step**: coloring one uncolored vertex `v` splits the count:
`N(C) = N(C⁺) + N(C⁻)` where `C⁺`/`C⁻` color `v` blue / red. -/
lemma goodCount_split (C : PCol α) (F : Finset (Finset α)) (v : α)
    (hv : C v = none) (hvx : v ∈ F.biUnion id) :
    goodCount C F = goodCount (colorVertex C v true) F
      + goodCount (colorVertex C v false) F := by
  classical
  unfold goodCount
  have hunion : (F.biUnion id).powerset.filter (CountedPred C F)
      = (F.biUnion id).powerset.filter (CountedPred (colorVertex C v true) F)
        ∪ (F.biUnion id).powerset.filter (CountedPred (colorVertex C v false) F) := by
    ext B
    constructor
    · intro hB
      by_cases hvB : v ∈ B
      · exact Finset.mem_union_left _
          ((mem_filter_counted_true_iff C F v hv hvx B).mpr ⟨hB, hvB⟩)
      · exact Finset.mem_union_right _
          ((mem_filter_counted_false_iff C F v hv hvx B).mpr ⟨hB, hvB⟩)
    · intro hB
      rcases Finset.mem_union.mp hB with hB | hB
      · exact (mem_filter_counted_true_iff C F v hv hvx B).mp hB |>.1
      · exact (mem_filter_counted_false_iff C F v hv hvx B).mp hB |>.1
  have hdisj : Disjoint
      ((F.biUnion id).powerset.filter (CountedPred (colorVertex C v true) F))
      ((F.biUnion id).powerset.filter (CountedPred (colorVertex C v false) F)) := by
    rw [Finset.disjoint_left]
    intro B hBp hBm
    obtain ⟨-, hvB⟩ := (mem_filter_counted_true_iff C F v hv hvx B).mp hBp
    obtain ⟨-, hvB'⟩ := (mem_filter_counted_false_iff C F v hv hvx B).mp hBm
    exact hvB' hvB
  rw [hunion, Finset.card_union_of_disjoint hdisj]

/-! ### The stopping time -/

/-- The stopping time of the frozen process: the first `t ≤ m` at which `stop`
holds (`m` if `stop` never holds up to time `m`). -/
noncomputable def stopTime (sel : PCol α → α) (stop : PCol α → Prop)
    [DecidablePred stop] (C₀ : PCol α) (ω : Fin m → Bool) : ℕ :=
  if h : ((Finset.range (m+1)).filter
      (fun t => stop (frozen sel stop C₀ ω t))).Nonempty
  then ((Finset.range (m+1)).filter
      (fun t => stop (frozen sel stop C₀ ω t))).min' h
  else m

/-- If `stop` holds at time `t ≤ m`, the stopping time is at most `t`. -/
lemma stopTime_le_of_stop (sel : PCol α → α) (stop : PCol α → Prop)
    [DecidablePred stop] (C₀ : PCol α) (ω : Fin m → Bool) (t : ℕ)
    (hstop : stop (frozen sel stop C₀ ω t)) (htm : t ≤ m) :
    stopTime sel stop C₀ ω ≤ t := by
  unfold stopTime
  split_ifs with h
  · have hmem : t ∈ (Finset.range (m+1)).filter
      (fun s => stop (frozen sel stop C₀ ω s)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le htm), hstop⟩
    exact Finset.min'_le _ t hmem
  · exact absurd (⟨t, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le htm), hstop⟩⟩ :
      ((Finset.range (m+1)).filter
        (fun s => stop (frozen sel stop C₀ ω s))).Nonempty) h

lemma stopTime_le (sel : PCol α → α) (stop : PCol α → Prop) [DecidablePred stop]
    (C₀ : PCol α) (ω : Fin m → Bool) : stopTime sel stop C₀ ω ≤ m := by
  unfold stopTime
  split_ifs with h
  · have hmin := Finset.min'_mem _ h
    rw [Finset.mem_filter, Finset.mem_range] at hmin
    exact Nat.lt_succ_iff.mp hmin.1
  · rfl


/-- At its stopping time the process has `stop` holding, or the time is `m`. -/
lemma stopTime_lt_or_stop (sel : PCol α → α) (stop : PCol α → Prop)
    [DecidablePred stop] (C₀ : PCol α) (ω : Fin m → Bool) :
    stopTime sel stop C₀ ω = m ∨
      stop (frozen sel stop C₀ ω (stopTime sel stop C₀ ω)) := by
  unfold stopTime
  split_ifs with h
  · right
    exact (Finset.mem_filter.mp (Finset.min'_mem _ h)).2
  · left; rfl

/-- Before the stopping time, `stop` does not hold. -/
lemma not_stop_of_lt_stopTime (sel : PCol α → α) (stop : PCol α → Prop)
    [DecidablePred stop] (C₀ : PCol α) (ω : Fin m → Bool) (t : ℕ)
    (ht : t < stopTime sel stop C₀ ω) :
    ¬ stop (frozen sel stop C₀ ω t) := by
  intro hstop
  have htm : t ≤ m :=
    le_trans (le_of_lt ht) (stopTime_le sel stop C₀ ω)
  have h1 := stopTime_le_of_stop sel stop C₀ ω t hstop htm
  omega

/-- The stopping time only depends on the process up to time `j`, provided it
stops at or before `j`. -/
lemma stopTime_prefix (sel : PCol α → α) (stop : PCol α → Prop)
    [DecidablePred stop] (C₀ : PCol α) {ω ω' : Fin m → Bool} (j : ℕ)
    (hprefix : ∀ k ≤ j, frozen sel stop C₀ ω k = frozen sel stop C₀ ω' k)
    (hTj : stopTime sel stop C₀ ω ≤ j) :
    stopTime sel stop C₀ ω' = stopTime sel stop C₀ ω := by
  have h1 : stopTime sel stop C₀ ω' ≤ stopTime sel stop C₀ ω := by
    rcases stopTime_lt_or_stop sel stop C₀ ω with hT | hstopT
    · rw [hT]
      exact stopTime_le sel stop C₀ ω'
    · have hstop' : stop (frozen sel stop C₀ ω' (stopTime sel stop C₀ ω)) := by
        rw [← hprefix _ hTj]
        exact hstopT
      exact stopTime_le_of_stop sel stop C₀ ω' _ hstop' (stopTime_le sel stop C₀ ω)
  have h2 : stopTime sel stop C₀ ω ≤ stopTime sel stop C₀ ω' := by
    rcases stopTime_lt_or_stop sel stop C₀ ω' with hT' | hstopT'
    · rw [hT']
      exact stopTime_le sel stop C₀ ω
    · have hT'j : stopTime sel stop C₀ ω' ≤ j := h1.trans hTj
      have hstop : stop (frozen sel stop C₀ ω (stopTime sel stop C₀ ω')) := by
        rw [hprefix _ hT'j]
        exact hstopT'
      exact stopTime_le_of_stop sel stop C₀ ω _ hstop (stopTime_le sel stop C₀ ω')
  omega

/-! ### Monotonicity of the stop condition along the process -/

/-- If `stop` persists under one more coloring, it persists along the whole
frozen process from the moment it first holds. -/
lemma stop_frozen_mono (sel : PCol α → α) (stop : PCol α → Prop)
    [DecidablePred stop]
    (hmono : ∀ (C : PCol α) (v : α) (b : Bool), stop C → stop (colorVertex C v b))
    (C₀ : PCol α) (ω : Fin m → Bool) (t : ℕ)
    (hstop : stop (frozen sel stop C₀ ω t)) (s : ℕ) (hs : t ≤ s) :
    stop (frozen sel stop C₀ ω s) := by
  have gen : ∀ s : ℕ, t ≤ s → stop (frozen sel stop C₀ ω s) := by
    intro s
    induction s with
    | zero =>
      intro h0
      have ht0 : t = 0 := by omega
      subst ht0
      exact hstop
    | succ s ih =>
      intro hs'
      by_cases hts : t = s + 1
      · subst hts
        exact hstop
      · have hle : t ≤ s := by omega
        have hstopS := ih hle
        by_cases hc : s ≥ m ∨ stop (frozen sel stop C₀ ω s)
        · rw [frozen_le_stopped sel stop C₀ ω s hc]
          exact hstopS
        · have hltm : s < m := by
            have h1 : ¬ (s ≥ m) := fun h1 => hc (Or.inl h1)
            omega
          have hnot' : ¬ stop (frozen sel stop C₀ ω s) := fun h2 =>
            hc (Or.inr h2)
          rw [frozen_lt_color sel stop C₀ ω s hltm hnot']
          exact hmono _ _ _ hstopS
  exact gen s hs

/-- If `stop` does not hold at time `t < m`, the stopping time is at least
`t+1`. -/
lemma stopTime_gt_of_not_stop (sel : PCol α → α) (stop : PCol α → Prop)
    [DecidablePred stop]
    (hmono : ∀ (C : PCol α) (v : α) (b : Bool), stop C → stop (colorVertex C v b))
    (C₀ : PCol α) (ω : Fin m → Bool) (t : ℕ) (htm : t < m)
    (hnot : ¬ stop (frozen sel stop C₀ ω t)) :
    t + 1 ≤ stopTime sel stop C₀ ω := by
  rcases stopTime_lt_or_stop sel stop C₀ ω with hT | hstopT
  · rw [hT]; omega
  · by_contra hcon
    have hTt : stopTime sel stop C₀ ω ≤ t := by omega
    exact hnot (stop_frozen_mono sel stop hmono C₀ ω _ hstopT t hTt)

/-! ### The counting martingale -/

/-- The counting martingale: `G_t(ω) = 2^{min(t,T)} · N(C_{min(t,T)})`, where
`N` is the good-set count of the frozen process. -/
noncomputable def cntG (sel : PCol α → α) (stop : PCol α → Prop)
    [DecidablePred stop] (C₀ : PCol α) (F : Finset (Finset α))
    (ω : Fin m → Bool) (t : ℕ) : ℝ :=
  ((2 : ℝ) ^ (min t (stopTime sel stop C₀ ω)))
    * goodCount (frozen sel stop C₀ ω (min t (stopTime sel stop C₀ ω))) F

/-- **Pairing step**: summing `G_{t+1}` over the two values of bit `t` gives
twice `G_t`. -/
lemma cntG_pairing (sel : PCol α → α) (stop : PCol α → Prop) [DecidablePred stop]
    (C₀ : PCol α) (F : Finset (Finset α))
    (hsel : ∀ C, ¬ stop C → C (sel C) = none)
    (hselX : ∀ C, ¬ stop C → sel C ∈ F.biUnion id)
    (hmono : ∀ (C : PCol α) (v : α) (b : Bool), stop C → stop (colorVertex C v b))
    (ω : Fin m → Bool) (t : ℕ) (htm : t < m) :
    ∑ b : Bool, cntG sel stop C₀ F (Function.update ω ⟨t, htm⟩ b) (t + 1)
      = 2 * cntG sel stop C₀ F ω t := by
  classical
  unfold cntG
  by_cases hTt : stopTime sel stop C₀ ω ≤ t
  · -- stopped at or before `t`: both extensions agree with `ω` from time `T` on
    have hTeq : ∀ b : Bool,
        stopTime sel stop C₀ (Function.update ω ⟨t, htm⟩ b)
          = stopTime sel stop C₀ ω := fun b =>
      stopTime_prefix sel stop C₀ (stopTime sel stop C₀ ω)
        (fun k hk => (frozen_update_of_le sel stop C₀ ω ⟨t, htm⟩ b k
          (le_trans hk hTt)).symm)
        (le_refl _)
    have hminT1 : min (t+1) (stopTime sel stop C₀ ω) = stopTime sel stop C₀ ω :=
      Nat.min_eq_right (by omega)
    have hminT0 : min t (stopTime sel stop C₀ ω) = stopTime sel stop C₀ ω :=
      Nat.min_eq_right hTt
    have hterm : ∀ b : Bool,
        ((2:ℝ) ^ (min (t+1) (stopTime sel stop C₀ (Function.update ω ⟨t, htm⟩ b))))
          * goodCount (frozen sel stop C₀ (Function.update ω ⟨t, htm⟩ b)
              (min (t+1) (stopTime sel stop C₀ (Function.update ω ⟨t, htm⟩ b)))) F
        = ((2:ℝ) ^ (stopTime sel stop C₀ ω))
          * goodCount (frozen sel stop C₀ ω (stopTime sel stop C₀ ω)) F := by
      intro b
      rw [hTeq b, hminT1,
        frozen_update_of_le sel stop C₀ ω ⟨t, htm⟩ b (stopTime sel stop C₀ ω) hTt]
    rw [Finset.sum_congr rfl (fun b _ => hterm b), sum_bool_eq, hminT0]
    ring
  · -- not stopped at `t`: the extensions split the count
    have hnot : ¬ stop (frozen sel stop C₀ ω t) :=
      not_stop_of_lt_stopTime sel stop C₀ ω t (by omega)
    have hv : frozen sel stop C₀ ω t (sel (frozen sel stop C₀ ω t)) = none :=
      hsel _ hnot
    have hvx : sel (frozen sel stop C₀ ω t) ∈ F.biUnion id := hselX _ hnot
    have hTgt : ∀ b : Bool,
        t + 1 ≤ stopTime sel stop C₀ (Function.update ω ⟨t, htm⟩ b) := by
      intro b
      refine stopTime_gt_of_not_stop sel stop hmono C₀
        (Function.update ω ⟨t, htm⟩ b) t htm ?_
      rw [frozen_update_of_le sel stop C₀ ω ⟨t, htm⟩ b t (le_refl t)]
      exact hnot
    have hterm : ∀ b : Bool,
        ((2:ℝ) ^ (min (t+1) (stopTime sel stop C₀ (Function.update ω ⟨t, htm⟩ b))))
          * goodCount (frozen sel stop C₀ (Function.update ω ⟨t, htm⟩ b)
              (min (t+1) (stopTime sel stop C₀ (Function.update ω ⟨t, htm⟩ b)))) F
        = ((2:ℝ) ^ (t+1))
          * goodCount (colorVertex (frozen sel stop C₀ ω t)
              (sel (frozen sel stop C₀ ω t)) b) F := by
      intro b
      have hnot' : ¬ stop (frozen sel stop C₀ (Function.update ω ⟨t, htm⟩ b) t) := by
        rw [frozen_update_of_le sel stop C₀ ω ⟨t, htm⟩ b t (le_refl t)]
        exact hnot
      rw [Nat.min_eq_left (hTgt b),
        frozen_lt_color sel stop C₀ (Function.update ω ⟨t, htm⟩ b) t htm hnot',
        frozen_update_of_le sel stop C₀ ω ⟨t, htm⟩ b t (le_refl t),
        bitAt_update_self ω ⟨t, htm⟩ b]
    have hsplit := goodCount_split (frozen sel stop C₀ ω t) F
      (sel (frozen sel stop C₀ ω t)) hv hvx
    rw [Finset.sum_congr rfl (fun b _ => hterm b), ← Finset.mul_sum, sum_bool_eq,
      Nat.min_eq_left (show t ≤ stopTime sel stop C₀ ω by omega), hsplit,
      Nat.cast_add]
    ring

/-- Summing the martingale over all bit strings does not change from `t` to
`t+1` (for `t < m`). -/
lemma cntG_sum_step (sel : PCol α → α) (stop : PCol α → Prop) [DecidablePred stop]
    (C₀ : PCol α) (F : Finset (Finset α))
    (hsel : ∀ C, ¬ stop C → C (sel C) = none)
    (hselX : ∀ C, ¬ stop C → sel C ∈ F.biUnion id)
    (hmono : ∀ (C : PCol α) (v : α) (b : Bool), stop C → stop (colorVertex C v b))
    (t : ℕ) (htm : t < m) :
    ∑ ω : Fin m → Bool, cntG sel stop C₀ F ω (t + 1)
      = ∑ ω : Fin m → Bool, cntG sel stop C₀ F ω t := by
  have idd := sum_update_twice m (t := ⟨t, htm⟩)
    (fun ω => cntG sel stop C₀ F ω (t + 1))
  have hpair : ∀ ω : Fin m → Bool,
      ∑ b : Bool, cntG sel stop C₀ F (Function.update ω ⟨t, htm⟩ b) (t + 1)
        = 2 * cntG sel stop C₀ F ω t := fun ω =>
    cntG_pairing sel stop C₀ F hsel hselX hmono ω t htm
  calc ∑ ω : Fin m → Bool, cntG sel stop C₀ F ω (t + 1)
      = (∑ ω : Fin m → Bool, ∑ b : Bool,
          cntG sel stop C₀ F (Function.update ω ⟨t, htm⟩ b) (t + 1)) / 2 := by
        rw [idd]; field_simp
    _ = ∑ ω : Fin m → Bool, cntG sel stop C₀ F ω t := by
        have h1 : (∑ ω : Fin m → Bool, ∑ b : Bool,
            cntG sel stop C₀ F (Function.update ω ⟨t, htm⟩ b) (t + 1))
            = ∑ ω : Fin m → Bool, (2 * cntG sel stop C₀ F ω t) :=
          Finset.sum_congr rfl (fun ω _ => hpair ω)
        rw [h1, ← Finset.mul_sum]
        field_simp

/-- The sum of the counting martingale over all bit strings is constant in
`t` and equals `2^m · N(C₀)`. -/
lemma cntG_sum_const (sel : PCol α → α) (stop : PCol α → Prop) [DecidablePred stop]
    (C₀ : PCol α) (F : Finset (Finset α))
    (hsel : ∀ C, ¬ stop C → C (sel C) = none)
    (hselX : ∀ C, ¬ stop C → sel C ∈ F.biUnion id)
    (hmono : ∀ (C : PCol α) (v : α) (b : Bool), stop C → stop (colorVertex C v b))
    (t : ℕ) :
    ∑ ω : Fin m → Bool, cntG sel stop C₀ F ω t
      = ((2 ^ m : ℕ) : ℝ) * goodCount C₀ F := by
  induction t with
  | zero =>
    have h0 : ∀ ω : Fin m → Bool, cntG sel stop C₀ F ω 0 = goodCount C₀ F := by
      intro ω
      unfold cntG
      rw [Nat.min_eq_left (Nat.zero_le _)]
      simp [frozen_zero]
    simp only [h0]
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : (Finset.univ : Finset (Fin m → Bool)).card = 2 ^ m := by
      rw [Finset.card_univ, Fintype.card_pi]
      simp
    rw [hcard]
  | succ t ih =>
    by_cases htm : t < m
    · rw [cntG_sum_step sel stop C₀ F hsel hselX hmono t htm]
      exact ih
    · have hTt : ∀ ω : Fin m → Bool, stopTime sel stop C₀ ω ≤ t := by
        intro ω
        have hTm := stopTime_le sel stop C₀ ω
        omega
      have hmin : ∀ ω : Fin m → Bool,
          cntG sel stop C₀ F ω (t + 1) = cntG sel stop C₀ F ω t := by
        intro ω
        have hTw := hTt ω
        unfold cntG
        rw [Nat.min_eq_right (by omega), Nat.min_eq_right hTw]
      simp only [hmin]
      exact ih

/-- **L6 main theorem** (the counting form of the optional stopping theorem):
`∑_ω 2^{T(ω)} · N(C_{T(ω)}) = 2^m · N(C₀)`. -/
theorem martingale_count (sel : PCol α → α) (stop : PCol α → Prop)
    [DecidablePred stop] (C₀ : PCol α) (F : Finset (Finset α))
    (hsel : ∀ C, ¬ stop C → C (sel C) = none)
    (hselX : ∀ C, ¬ stop C → sel C ∈ F.biUnion id)
    (hmono : ∀ (C : PCol α) (v : α) (b : Bool), stop C → stop (colorVertex C v b)) :
    ∑ ω : Fin m → Bool,
      ((2 : ℝ) ^ (stopTime sel stop C₀ ω))
        * goodCount (frozen sel stop C₀ ω (stopTime sel stop C₀ ω)) F
      = ((2 ^ m : ℕ) : ℝ) * goodCount C₀ F := by
  have h1 : ∑ ω : Fin m → Bool, cntG sel stop C₀ F ω m
      = ((2 ^ m : ℕ) : ℝ) * goodCount C₀ F :=
    cntG_sum_const sel stop C₀ F hsel hselX hmono m
  have hmin : ∀ ω : Fin m → Bool,
      cntG sel stop C₀ F ω m
        = ((2 : ℝ) ^ (stopTime sel stop C₀ ω))
          * goodCount (frozen sel stop C₀ ω (stopTime sel stop C₀ ω)) F := by
    intro ω
    unfold cntG
    rw [Nat.min_eq_right (stopTime_le sel stop C₀ ω)]
  rw [Finset.sum_congr rfl (fun ω _ => (hmin ω).symm)]
  exact h1

end Erdos1027
