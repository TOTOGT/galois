import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic

open Polynomial
open scoped BigOperators

-- ============================================================================
-- Phase 1: Polynomial Definitions & Splitting Field
-- ============================================================================

/-- Define the n-bonacci polynomial dynamically in ℤ[X]. -/
def nBonacciPolynomial (n : ℕ) : ℤ[X] :=
  X^n - ∑ i ∈ Finset.range n, X^i

/-- Cast the integer polynomial to ℚ[X] so it lives over a Field. -/
def nBonacciPolynomialQ (n : ℕ) : ℚ[X] :=
  (nBonacciPolynomial n).map (Int.castRingHom ℚ)

/-- The Splitting Field defined natively over ℚ[X]. -/
def NBonacciSplittingField (n : ℕ) :=
  (nBonacciPolynomialQ n).SplittingField

/-- Galois Group using Mathlib's native Gal(L/K) notation. -/
abbrev nBonacciGaloisGroup (n : ℕ) : Type _ :=
  Gal(NBonacciSplittingField n / ℚ)

-- ============================================================================
-- Phase 2: Structural Lemmas & Filters
-- ============================================================================

/-- In characteristic 0, the splitting field of any polynomial is automatically Galois. -/
instance nBonacci_isGalois (n : ℕ) : IsGalois ℚ (NBonacciSplittingField n) :=
  inferInstance
