import «SquareDeterminantGaussIntegration»

/-!
# The determinant-square theorem on the square simplex

The homogeneous representative has a global determinant-square factor.  The
compiled simplex-kernel reconstruction then returns to the original
polynomial, adding exactly a multiple of the total-mass equation.
-/

noncomputable section

namespace SquarePolynomial

theorem square_simplex_det_sq
    {n : ℕ} (hn : 2 ≤ n)
    (P : Poly n) (hDPI : PolynomialDPI P)
    (hRKO : PolynomialRKO P) :
    ∃ Q K : Poly n,
      P = detPoly n ^ 2 * Q +
        (tauPoly (R := ℝ) (simplexStar hn) - 1) * K := by
  obtain ⟨Q, hfactor⟩ := det_sq_dvd_tauHom hn P hDPI hRKO
  obtain ⟨K, hidentity⟩ := square_identity_of_tauHomogenize_factor
    (simplexStar hn) P (detPoly n) Q hfactor
  exact ⟨Q, K, hidentity⟩

end SquarePolynomial

#print axioms SquarePolynomial.square_simplex_det_sq
