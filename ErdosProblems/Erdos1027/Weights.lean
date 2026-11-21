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

end Erdos1027
