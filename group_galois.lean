import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic

open Polynomial
open scoped BigOperators

-- ============================================================================
-- Phase 1: Polynomial Definitions & Splitting Field
-- ============================================================================

/-- Define the n-bonacci polynomial dynamically in ℤ[X]. -/
noncomputable def nBonacciPolynomial (n : ℕ) : ℤ[X] :=
  X^n - ∑ i ∈ Finset.range n, X^i

/-- Cast the integer polynomial to ℚ[X] so it lives over a Field. -/
noncomputable def nBonacciPolynomialQ (n : ℕ) : ℚ[X] :=
  (nBonacciPolynomial n).map (Int.castRingHom ℚ)

/-- Transparent definition for SplittingField. -/
noncomputable abbrev NBonacciSplittingField (n : ℕ) : Type _ :=
  (nBonacciPolynomialQ n).SplittingField

/-- Galois Group defined directly via Mathlib's native `Polynomial.Gal`. -/
abbrev nBonacciGaloisGroup (n : ℕ) : Type _ :=
  (nBonacciPolynomialQ n).Gal

-- ============================================================================
-- Phase 3: The action map
-- ============================================================================

noncomputable def nBonacciActionHom (n : ℕ) :
    nBonacciGaloisGroup n →* Equiv.Perm ((nBonacciPolynomialQ n).rootSet (NBonacciSplittingField n)) :=
  Polynomial.Gal.galActionHom (nBonacciPolynomialQ n)

/-- FIX: `galActionHom_injective` needs the polynomial to be separable —
without it, distinct field automorphisms can act identically on a repeated
root, so injectivity genuinely fails to follow from nothing. The previous
version of this theorem took no hypotheses at all, which cannot supply that.
Since ℚ has characteristic zero, irreducibility implies separability, so we
add `hirr` here — matching the hypothesis already present (for a different,
harder reason) on `nBonacci_action_bijective` and `Theorem_Galois` below.

UNVERIFIED: I do not have a Lean kernel to check this against. The step
`hirr.separable` assumes Mathlib exposes `Irreducible.separable` for a
`CharZero` field with that exact name; if the real build error names a
different lemma (e.g. `Polynomial.separable_of_irreducible`, or something
requiring the hypothesis spelled out via `Polynomial.Separable` and
`Polynomial.derivative_ne_zero`-style reasoning instead of a one-line dot
call), that is the next thing to fix, and I'd want the actual error text
to get it right rather than guess twice. -/
theorem nBonacci_action_injective (n : ℕ) (hirr : Irreducible (nBonacciPolynomialQ n)) :
    Function.Injective (nBonacciActionHom n) :=
  Polynomial.Gal.galActionHom_injective (nBonacciPolynomialQ n) hirr.separable

-- ============================================================================
-- Phase 4: Surjectivity and the main theorem
-- ============================================================================

/-- NOT ATTEMPTED. This is not a routine `sorry` — it is asking for a
Selmer/Nart–Vila/Osada-style theorem that the Galois group of this
polynomial family is the full symmetric group Sₙ. The standard proof
technique for this kind of claim (see K. Conrad's writeup for xⁿ − x − 1)
needs three separate, hard ingredients none of which are supplied by
automation:
  1. Transitivity, from irreducibility (`hirr`).
  2. A transposition in the Galois group, obtained by showing the polynomial
     has *exactly one* complex-conjugate pair of non-real roots — a real
     analytic argument (e.g. via Descartes' rule of signs or calculus on the
     real-valued polynomial function), not a tactic.
  3. Primitivity of the Galois action on the roots. The classical
     "transitive + contains a transposition ⟹ Sₙ" criterion only closes
     cleanly when n is *prime*. This theorem explicitly assumes `hn_comp :
     ¬ n.Prime` — the harder composite-degree case, which needs a genuine
     primitivity argument in the style of Movahhedi–Salinier's 1996 paper
     on trinomial Galois groups, not the classical shortcut.
I have found nothing suggesting this primitivity machinery already exists
in Mathlib. Left as `sorry`, honestly, rather than faked. -/
theorem nBonacci_action_bijective (n : ℕ) (hn_odd : Odd n) (hn_comp : ¬ n.Prime) (hn2 : 2 ≤ n)
    (hirr : Irreducible (nBonacciPolynomialQ n)) :
    Function.Bijective (nBonacciActionHom n) := by
  sorry

theorem Theorem_Galois (n : ℕ) (hn_odd : Odd n) (hn_comp : ¬ n.Prime) (hn2 : 2 ≤ n)
    (hirr : Irreducible (nBonacciPolynomialQ n)) :
    Nonempty (nBonacciGaloisGroup n ≃* Equiv.Perm ((nBonacciPolynomialQ n).rootSet (NBonacciSplittingField n))) :=
  ⟨MulEquiv.ofBijective (nBonacciActionHom n) (nBonacci_action_bijective n hn_odd hn_comp hn2 hirr)⟩
