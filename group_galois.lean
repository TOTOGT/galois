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
-- Phase 2: Structural Lemmas
-- ============================================================================

/-- In characteristic 0, the splitting field of any polynomial is automatically Galois. -/
instance nBonacci_isGalois (n : ℕ) : IsGalois ℚ (NBonacciSplittingField n) :=
  Polynomial.SplittingField.isGalois (nBonacciPolynomialQ n)

-- ============================================================================
-- Phase 3: The action map
-- ============================================================================

noncomputable def nBonacciActionHom (n : ℕ) :
    nBonacciGaloisGroup n →* Equiv.Perm ((nBonacciPolynomialQ n).rootSet (NBonacciSplittingField n)) :=
  Polynomial.Gal.galActionHom (nBonacciPolynomialQ n)

theorem nBonacci_action_injective (n : ℕ) :
    Function.Injective (nBonacciActionHom n) :=
  Polynomial.Gal.galActionHom_injective (nBonacciPolynomialQ n)

-- ============================================================================
-- Phase 4: Surjectivity and the main theorem
-- ============================================================================

theorem nBonacci_action_bijective (n : ℕ) (hn_odd : Odd n) (hn_comp : ¬ n.Prime) (hn2 : 2 ≤ n)
    (hirr : Irreducible (nBonacciPolynomialQ n)) :
    Function.Bijective (nBonacciActionHom n) := by
  sorry

theorem Theorem_Galois (n : ℕ) (hn_odd : Odd n) (hn_comp : ¬ n.Prime) (hn2 : 2 ≤ n)
    (hirr : Irreducible (nBonacciPolynomialQ n)) :
    Nonempty (nBonacciGaloisGroup n ≃* Equiv.Perm ((nBonacciPolynomialQ n).rootSet (NBonacciSplittingField n))) :=
  ⟨MulEquiv.ofBijective (nBonacciActionHom n) (nBonacci_action_bijective n hn_odd hn_comp hn2 hirr)⟩
