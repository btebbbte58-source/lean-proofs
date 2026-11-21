/-
JSP-000854 (Erdos Problem 1027) — target statement aligned 1:1 with
google-deepmind/formal-conjectures `FormalConjectures/ErdosProblems/1027.lean`
(fetched 2026-11-21). Math solution: Koishi Chan's proof comment on
https://www.erdosproblems.com/1027 (archived: JustinSunPrize-awards/_koishi_proof_1027.md).
Formalization: clean-room proof code in this repo, owner btebbbte58-source.
-/

import Mathlib.Tactic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union

/-!
# Erdős Problem 1027 (JSP-000854)

*References:*
- [erdosproblems.com/1027](https://www.erdosproblems.com/1027)
- [Er64e] Erdős, P., *On a combinatorial problem. II*. Acta Math. Acad. Sci. Hungar. (1964),
  445-447.
-/

open Filter

namespace Erdos1027

variable {α : Type*} [DecidableEq α]

/-- The ground set $X=\bigcup_{A\in\mathcal{F}}A$ of a finite family of finite sets. -/
def groundSet (F : Finset (Finset α)) : Finset α := F.biUnion id

/-- The sets $B\subseteq X$ which intersect every set in $\mathcal{F}$, yet contain none of them. -/
def goodSets (F : Finset (Finset α)) : Finset (Finset α) :=
  (groundSet F).powerset.filter fun B ↦ ∀ A ∈ F, (A ∩ B).Nonempty ∧ ¬ A ⊆ B

/--
Let $c>0$, and let $n$ be sufficiently large depending on $c$. Suppose that $\mathcal{F}$ is a
family of at most $c2^n$ many finite sets of size $n$. Let $X=\cup_{A\in \mathcal{F}}A$.

Must there exist $\gg_c 2^{\lvert X\rvert}$ many sets $B\subset X$ which intersect every set in
$\mathcal{F}$, yet contain none of them?

This is true, and a proof was given in the comment section by Koishi Chan.
-/
theorem erdos_1027 : ∀ c : ℝ, 0 < c → ∃ δ : ℝ, 0 < δ ∧
    ∀ᶠ n : ℕ in atTop, ∀ (α : Type) [DecidableEq α] (F : Finset (Finset α)),
      (∀ A ∈ F, A.card = n) → (F.card : ℝ) ≤ c * 2 ^ n →
        δ * 2 ^ (groundSet F).card ≤ (goodSets F).card := by
  sorry

end Erdos1027
