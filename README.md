# LeanProofs — The Justin Sun Prize formalizations

Lean 4 / Mathlib proofs for The Justin Sun Prize (https://www.hejustinsun.com/prize).

## Layout
- One module per problem: `LeanProofs/JSP<NNNNNN>.lean`
- Each module exposes a fully-qualified theorem matching the original problem statement 1:1
  (no modified statements, no `axiom`, no `sorry`/`admit`)

## Build
```
lake exe cache get   # fetch prebuilt mathlib olean cache (~1-2 GB, once)
lake build
```

## Verification (per proof module)
```
lake env lean LeanProofs/JSP<NNNNNN>.lean
```
Then in the file (temporarily) `#print axioms <theorem>` — only
`propext`, `Classical.choice`, `Quot.sound` are acceptable. Remove the check before commit.

## Submission (official rules)
- Proofs live here; PRs go to `TheJustinSunPrize/awards` and only edit the
  catalog entry's 4 fields (Current status / Lean proof / Attribution basis /
  Publication details). No proof code in PRs.
- Priority = commit timestamp in this repo (must have verifiable public history).
