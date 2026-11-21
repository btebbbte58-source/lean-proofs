import Lake
open Lake DSL

package «leanproofs» where
  -- The Justin Sun Prize (JSP) Lean formalization proofs
  -- Official process: proofs live in THIS repo; PRs to TheJustinSunPrize/awards
  -- only edit catalog entry fields (no proof code in PRs).

require mathlib from
  git "https://github.com/leanprover-community/mathlib4.git" @ "master"

@[default_target]
lean_lib «LeanProofs» where
  -- one module per problem, e.g. LeanProofs.JSP000748
