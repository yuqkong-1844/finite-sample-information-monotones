import «GenericDeterminantIrreducible»

/-!
# Gauss descent for the square of the generic determinant

This file isolates the descent from a fraction-field divisibility statement in
one pivot variable to divisibility in the original multivariate polynomial
ring.
-/

noncomputable section

namespace SquarePolynomial

/-- Clear the denominator in the value of `p` at the affine root `-b/a`,
using any exponent which bounds the degree of `p`. -/
def clearLinearRoot {A : Type*} [CommRing A]
    (N : ℕ) (p : Polynomial A) (a b : A) : A :=
  ∑ i ∈ Finset.range (N + 1),
    p.coeff i * (-b) ^ i * a ^ (N - i)

lemma map_clearLinearRoot_eq_pow_mul_eval
    {A K : Type*} [CommRing A] [Field K]
    (f : A →+* K) (N : ℕ) (p : Polynomial A) (a b : A)
    (hdeg : p.natDegree ≤ N) (ha : f a ≠ 0) :
    f (clearLinearRoot N p a b) =
      f a ^ N * Polynomial.eval (-f b / f a) (p.map f) := by
  rw [clearLinearRoot, map_sum]
  simp only [map_mul, map_pow, map_neg]
  rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range'
    f (Nat.lt_succ_of_le hdeg)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hiN : i ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rw [div_pow]
  field_simp
  rw [mul_assoc, mul_assoc, pow_sub_mul_pow _ hiN]
  ring

/-- A primitive divisor over a GCD domain descends from its fraction field. -/
theorem primitive_dvd_of_fraction_dvd
    {A L : Type*} [CommRing A] [IsDomain A] [IsGCDMonoid A]
    [Field L] [Algebra A L] [IsFractionRing A L]
    {d h : Polynomial A} (hd : d.IsPrimitive)
    (hfrac : d.map (algebraMap A L) ∣ h.map (algebraMap A L)) :
    d ∣ h := by
  exact hd.dvd_of_fraction_map_dvd_fraction_map hfrac

/-- Specialization of Gauss descent to the square of the generic determinant
in pivot coordinates. -/
theorem genericDetPoly_sq_dvd_of_pivot_fraction_dvd
    {n : ℕ} (hn : 0 < n)
    (H : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℝ)
    (hfrac :
      ((toNested (R := ℝ) (pivotZero n)
          (genericDetPoly ℝ (n + 1)) ^ 2).map
          (algebraMap (MvPolynomial (DetCoeffVar n) ℝ)
            (FractionRing (MvPolynomial (DetCoeffVar n) ℝ)))) ∣
        (toNested (R := ℝ) (pivotZero n) H).map
          (algebraMap (MvPolynomial (DetCoeffVar n) ℝ)
            (FractionRing (MvPolynomial (DetCoeffVar n) ℝ)))) :
    genericDetPoly ℝ (n + 1) ^ 2 ∣ H := by
  let A := MvPolynomial (DetCoeffVar n) ℝ
  let L := FractionRing A
  have hnested :
      toNested (R := ℝ) (pivotZero n)
          (genericDetPoly ℝ (n + 1)) ^ 2 ∣
        toNested (R := ℝ) (pivotZero n) H := by
    apply primitive_dvd_of_fraction_dvd
      (L := L) (genericDetPoly_pivot_sq_isPrimitive (K := ℝ) hn)
    exact hfrac
  obtain ⟨q, hq⟩ := hnested
  refine ⟨(toNested (R := ℝ) (pivotZero n)).symm q, ?_⟩
  apply (toNested (R := ℝ) (pivotZero n)).injective
  simpa using hq

end SquarePolynomial

#print axioms SquarePolynomial.primitive_dvd_of_fraction_dvd
#print axioms SquarePolynomial.genericDetPoly_sq_dvd_of_pivot_fraction_dvd
