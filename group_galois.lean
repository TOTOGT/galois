import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic

open Polynomial
open scoped BigOperators

-- ============================================================================
-- Phase 1: Polynomial Definitions & Splitting Field
-- (unchanged — already CI-verified in run #69)
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
-- Phase 2: Structural Lemmas
-- (unchanged — already CI-verified in run #69)
-- ============================================================================

/-- In characteristic 0, the splitting field of any polynomial is automatically Galois. -/
instance nBonacci_isGalois (n : ℕ) : IsGalois ℚ (NBonacciSplittingField n) :=
  inferInstance

-- ============================================================================
-- Phase 3: The action map — NEW. Real content, unverified by a compiler here.
-- ============================================================================

/-- The Galois group acts on the roots of the polynomial inside its splitting
field. Mathlib already builds this permutation representation for any
polynomial via `Polynomial.Gal.galActionHom`; here we just specialize it to
the n-bonacci polynomial. This line does the actual mathematical work of
"the native Galois group action map" that the README refers to — everything
before this point was setup, not the map itself. -/
noncomputable def nBonacciActionHom (n : ℕ) :
    nBonacciGaloisGroup n →*
      Equiv.Perm ((nBonacciPolynomialQ n).rootSet (NBonacciSplittingField n)) :=
  Polynomial.Gal.galActionHom (nBonacciPolynomialQ n)
  -- NOTE: this relies on `nBonacciGaloisGroup n` being defeq to
  -- `(nBonacciPolynomialQ n).Gal`, which it should be since
  -- `NBonacciSplittingField n` is literally `(nBonacciPolynomialQ n).SplittingField`.
  -- If Mathlib's exact name/signature for `galActionHom` has drifted, this is
  -- the line to fix first.

/-- INJECTIVITY — the "easy half" of "bijective isomorphism", genuinely provable
in general, *conditional on separability* (distinct roots). Separability is
NOT proven here for the n-bonacci family — it's taken as a hypothesis. Proving
it for real would mean showing `nBonacciPolynomialQ n` and its derivative are
coprime, e.g. via `Polynomial.separable_iff_derivative_ne_zero` plus an
explicit gcd computation, or by proving irreducibility first (irreducible ⇒
separable in characteristic 0). Neither is attempted here. -/
theorem nBonacci_action_injective (n : ℕ)
    (hsep : (nBonacciPolynomialQ n).Separable) :
    Function.Injective (nBonacciActionHom n) :=
  Polynomial.Gal.galActionHom_injective (nBonacciPolynomialQ n) hsep
  -- Again, exact Mathlib lemma name/signature may need adjustment.

-- ============================================================================
-- Phase 4: Surjectivity and the main theorem — NOT DONE. Genuinely hard.
-- ============================================================================

/-
This is where the real mathematics lives, and it is not a formalization gap
so much as an open mathematical question for this specific family. To prove

    Gal(NBonacciSplittingField n / ℚ) ≃* Equiv.Perm (roots)

for odd composite n, the standard route (Conrad, "Galois Groups as Permutation
Groups") needs ALL of:

1. IRREDIBILITY of `nBonacciPolynomialQ n` over ℚ.
   Not proven. Would need e.g. a reduction-mod-p irreducibility argument
   (`Polynomial.Monic.irreducible_of_irreducible_map` style), or a direct
   argument specific to this polynomial family. I am not aware of a citable
   theorem establishing this for X^n - Σ_{i<n} X^i restricted to odd
   composite n — I could not find this exact family in the literature when
   I searched, which means this may not even be TRUE as stated. Before
   writing more Lean, this should be checked numerically (e.g. in Sage,
   PARI/GP, or Magma) for the first several odd composite n (9, 15, 21, 25,
   27, ...) to confirm the Galois group actually comes out as the full
   symmetric group in each case.

2. SEPARABILITY. See the note above — follows from irreducibility in
   characteristic 0, but that route is also unproven.

3. A GENERATION ARGUMENT placing the (transitive, by step 1) image inside
   Equiv.Perm in all of S_n. The classical tool is:

      "A transitive subgroup of S_n containing a transposition and an
       (n-1)-cycle is all of S_n."

   Getting a transposition and an (n-1)-cycle is usually done via Dedekind's
   theorem: factor `nBonacciPolynomial n` mod various primes p not dividing
   the discriminant, and read off cycle types from the degrees of the
   irreducible factors mod p. This requires exhibiting SPECIFIC primes
   (possibly depending on n, possibly requiring a case split on n mod
   something) with the right factorization shape. Nothing like this is
   attempted here, and it is very unlikely to go through as one clean
   induction over "n odd composite" — this is normally proven prime-by-prime
   or via a computational verification for small n plus a separate argument
   (or conjecture) for the general pattern.

4. Only after 1–3 would `Function.Bijective (nBonacciActionHom n)` — and
   hence a genuine isomorphism `Gal(... / ℚ) ≃* Equiv.Perm (roots)` — be
   provable.

The theorem statement below is therefore a TARGET, not a result. The `sorry`
is not a missing tactic call; it stands in for genuine unproven (and,
pending numerical checking, possibly unproven-because-unclear-if-true)
mathematics.
-/

theorem nBonacci_action_bijective (n : ℕ) (hn_odd : Odd n) (hn_comp : ¬ n.Prime)
    (hn2 : 2 ≤ n)
    (hirr : Irreducible (nBonacciPolynomialQ n)) :
    Function.Bijective (nBonacciActionHom n) := by
  sorry
  -- Missing: injectivity from `nBonacci_action_injective` once separability
  -- is derived from `hirr` (char 0: irreducible ⇒ separable), PLUS
  -- surjectivity from the Dedekind/generation argument in item 3 above.

/-- The isomorphism your README actually claims. Depends entirely on the
`sorry` above and is therefore itself unproven. -/
theorem Theorem_Galois (n : ℕ) (hn_odd : Odd n) (hn_comp : ¬ n.Prime) (hn2 : 2 ≤ n)
    (hirr : Irreducible (nBonacciPolynomialQ n)) :
    Nonempty (nBonacciGaloisGroup n ≃*
      Equiv.Perm ((nBonacciPolynomialQ n).rootSet (NBonacciSplittingField n))) :=
  ⟨MulEquiv.ofBijective (nBonacciActionHom n)
    (nBonacci_action_bijective n hn_odd hn_comp hn2 hirr)⟩
