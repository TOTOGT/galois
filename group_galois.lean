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

/-- The Splitting Field defined natively over ℚ[X]. -/
noncomputable def NBonacciSplittingField (n : ℕ) :=
  (nBonacciPolynomialQ n).SplittingField

/-- Galois Group using Mathlib's native Gal(L/K) notation. -/
abbrev nBonacciGaloisGroup (n : ℕ) : Type _ :=
  Gal(NBonacciSplittingField n / ℚ)

-- ============================================================================
-- Phase 2: Structural Lemmas
-- ============================================================================

/-- In characteristic 0, the splitting field of any polynomial is automatically Galois. -/
instance nBonacci_isGalois (n : ℕ) : IsGalois ℚ (NBonacciSplittingField n) :=
  inferInstance

-- ============================================================================
-- Phase 3: The action map
-- ============================================================================

noncomputable def nBonacciActionHom (n : ℕ) :
    nBonacciGaloisGroup n →* Equiv.Perm ((nBonacciPolynomialQ n).rootSet (NBonacciSplittingField n)) :=
  Polynomial.Gal.galActionHom (nBonacciPolynomialQ n)

theorem nBonacci_action_injective (n : ℕ) (hsep : (nBonacciPolynomialQ n).Separable) :
    Function.Injective (nBonacciActionHom n) :=
  Polynomial.Gal.galActionHom_injective (nBonacciPolynomialQ n) hsep

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
