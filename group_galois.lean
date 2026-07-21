import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Discriminant
import Mathlib.Algebra.Polynomial.SplittingField.Construction
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic

open Polynomial BigOperators

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
instance nBonacci_isGalois (n : ℕ) : 
    IsGalois ℚ (NBonacciSplittingField n) := 
  IsSplittingField.isGalois (nBonacciPolynomialQ n)

/-- Filter for unramified primes: p does not divide the discriminant of P_n(X). -/
def IsUnramifiedPrime (n p : ℕ) [Fact (Nat.Prime p)] : Prop :=
  ¬ ((p : ℤ) ∣ Polynomial.discriminant (nBonacciPolynomial n))

-- ============================================================================
-- Phase 3: Root Bijection & Permutation Isomorphism Bridge
-- ============================================================================

/-- Subtype representing roots of P_n(X) inside its splitting field. -/
def nBonacciRoots (n : ℕ) := 
  (nBonacciPolynomialQ n).rootSet (NBonacciSplittingField n)

/-- Equivalence between the root set and `Fin n` when n roots are distinct. -/
noncomputable def rootsEquivFin (n : ℕ) 
    (h_card : Fintype.card (nBonacciRoots n) = n) :
    nBonacciRoots n ≃ Fin n :=
  Fintype.equivFinOfCardEq h_card

/-- Group homomorphism mapping Gal(L/K) into Equiv.Perm (Fin n) via Gal.galActionHom. -/
noncomputable def galActionToPerm (n : ℕ)
    (h_card : Fintype.card (nBonacciRoots n) = n) :
    nBonacciGaloisGroup n →* Equiv.Perm (Fin n) :=
  let rootPerm := Gal.galActionHom ℚ (NBonacciSplittingField n) (nBonacciPolynomialQ n)
  -- Equiv.Perm.congr transports the action from Perm(rootSet) to Perm(Fin n)
  MonoidHom.comp (Equiv.Perm.congr (rootsEquivFin n h_card)) rootPerm
