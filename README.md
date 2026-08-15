# galois — Galois groups of the n-bonacci polynomials, in Lean 4

Formalizing the Galois theory of the n-bonacci family in Lean 4 with Mathlib.

**Status: one lemma closed, the main theorem open with a named obstruction.**
Nothing in this repository should be described as proved except what the list
below marks `[VERIFIED]`. See *Standard of claim* at the end.

---

## The object

For `n ≥ 2` the n-bonacci polynomial is

```
p_n(X) = X^n − (X^(n-1) + X^(n-2) + ⋯ + X + 1)
       = X^n − Σ_{i<n} X^i
```

Its dominant real root is the n-bonacci constant ρ_n: the golden ratio
φ ≈ 1.6180 at n = 2, the tribonacci constant η ≈ 1.8393 at n = 3, tetranacci
at n = 4, and so on, increasing to the embodiment threshold τ = 2 as n → ∞.
That ladder is the algebraic spine of the *Principia Orthogona* series, and η
in particular is the constant the DNLS research program is built on.

A fact that matters for the method: multiplying by (X − 1) gives a **trinomial**,

```
(X − 1) · p_n(X) = X^(n+1) − 2·X^n + 1
```

so results about Galois groups of trinomials apply to this family, and that is
where the literature route runs.

---

## What is asked

For which `n` is the action of `Gal(K_n/ℚ)` on the roots of `p_n` the *full*
symmetric group — that is, when is

```
Gal(K_n/ℚ) ≅ S_n ,     K_n = splitting field of p_n over ℚ
```

realized by the natural root-action map being **bijective**?

---

## Status

| Result | Tag | Evidence |
|---|---|---|
| `nBonacci_action_injective` | `[VERIFIED]` | Mathlib `Polynomial.Gal.galActionHom_injective`, applied directly. No `sorry`. |
| `nBonacci_action_bijective` | `[OPEN]` | `sorry`. Surjectivity. See the obstruction below. |
| `Theorem_Galois` | `[OPEN]` | Compiles, but derives from the line above and therefore **inherits its `sorry`**. |
| Irreducibility of `p_n` | `[ASSUMED]` | Carried as the hypothesis `hirr`, not discharged here. See task 1. |

Injectivity is the easy half and Mathlib gives it outright. Everything
interesting is in surjectivity.

---

## The obstruction

For **prime** degree `p` there is a classical shortcut: a transitive subgroup of
`S_p` containing a transposition is all of `S_p`. Establish transitivity from
irreducibility, produce one transposition from complex conjugation when the
polynomial has exactly two non-real roots, and surjectivity closes immediately.

**`n` odd and composite defeats that route.** The shortcut is false at composite
degree — transitive plus a transposition is not enough. The correct chain is

```
irreducible  ⟹  transitive
transitive + primitive + one transposition  ⟹  S_n      (Jordan)
```

so **primitivity** becomes the load-bearing step, and it is not free. For the
trinomial family `X^(n+1) − 2X^n + 1` the relevant primitivity results are due to
Movahhedi and Salinier. **They are not in Mathlib.** Formalizing them is the
prerequisite; no amount of tactic search closes this `sorry` without them.

That is why the theorem is restricted to odd composite `n`: the prime case has a
known route, and the odd composite case is the residual hard one.

`[CITE NEEDED]` — pin the exact Movahhedi–Salinier reference (title, journal,
year) before it appears in any deposit. It is named here from working knowledge
and has not been checked against the literature in this repository.

---

## Work plan

Each task states what *done* means. A task is not done because it looks done.

**1. Discharge irreducibility.** `hirr` is currently a hypothesis. The n-bonacci
constant is a Pisot number and `p_n` is understood to be its minimal polynomial,
which would give irreducibility for all `n ≥ 2` — but that is not proved here and
the supporting reference is not yet pinned. *Done when:* `Irreducible
(nBonacciPolynomialQ n)` is a theorem in this repo with no `sorry`, or the
hypothesis is documented as deliberate with the reason.

**2. Transitivity.** Follows from irreducibility; Mathlib has the machinery.
*Done when:* the transitive action is a theorem here, no `sorry`.

**3. Count real roots.** Surjectivity arguments of this shape need exactly two
non-real roots, giving complex conjugation as a transposition. Establish the
signature of `p_n` for odd composite `n`. *Done when:* the real-root count is a
theorem, not a computation reported in prose.

**4. Primitivity — the actual work.** Formalize enough Movahhedi–Salinier to get
primitivity for this family. This is a Mathlib-scale contribution, not a lemma.
*Done when:* primitivity of the Galois action is a theorem here with no `sorry`.

**5. Jordan.** Primitive + a transposition ⟹ `S_n`. Check whether Mathlib has
this; if not it is its own task. *Done when:* available and applied.

**6. Close `nBonacci_action_bijective`.** Only after 1–5. *Done when:*
`#print axioms Theorem_Galois` returns `[propext, Classical.choice, Quot.sound]`
and nothing else — in particular no `sorryAx`.

---

## How to verify

```bash
lake exe cache get
lake build
```

Then, in the Lean file or a scratch file:

```lean
#print axioms Theorem_Galois
```

A result counts as proved here only when that command returns
`[propext, Classical.choice, Quot.sound]`. If `sorryAx` appears, the theorem is
open regardless of what any README, repo description, badge, chapter or deposit
says about it.

---

## Standard of claim

This repository follows the house rule from `geometry/CLAUDE.md`:

> **Kernel-check before writing "proved."** No claim moves to VERIFIED without
> either green CI or a paste into a real Lean kernel that you watched come back
> clean. Fluent prose is not evidence.

And its corollary, which is the one that actually gets violated:

> **A caveat may only be removed by the same edit that verifies the thing it
> hedges — never as tidying.**

Self-reported metadata does not count. A repository description, a README claim,
a CI badge and a chapter's prose are all assertions *about* the artifact; only
the kernel is evidence. This repository previously described itself as having
proved that the action map is a bijective isomorphism for all odd composite `n`,
while the file carried `sorry`. That is corrected here, and the correction is
recorded rather than quietly applied.

---

## Licence

Lean source under MIT. Prose under CC BY-NC-ND 4.0, per the series split.

Pablo Nogueira Grossi · G6 LLC · Newark NJ · ORCID 0009-0000-6496-2186
[Principia Orthogona](https://zenodo.org/communities/principia-orthogona)
