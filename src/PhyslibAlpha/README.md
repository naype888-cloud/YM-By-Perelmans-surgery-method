# PhyslibAlpha (vendored copy)

Files copied **verbatim** from PhyslibAlpha at commit `b0ba04c3`
(`feat-algstate-bridge`, branch of `naype888-cloud/physlib`), with their original
headers. They are copied only so that this repository builds from
**Mathlib v4.35.0 alone**; they use nothing but Mathlib (and the four Physlib files
in `../Physlib`). The tight-binding chain, the uncertainty relations on
C*-algebra states and the cube (`TightBindingChain`, `StarAlgebra`,
`CStarAlgebra`, `HilbertSpaces.FiniteTarget`) are plain algebra over Mathlib.

Bridge, for orientation: the same statements live in PhyslibAlpha, which is the
version under review there (stated in Physlib's own API). This copy is the
Mathlib-only form of the same content; the reviewed PhyslibAlpha version is the
reference if anything differs.
