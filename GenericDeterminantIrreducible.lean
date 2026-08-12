import «SquareDeterminantDoubleContact»

/-!
# Generic determinant irreducibility

The determinant is written as a primitive linear polynomial in a pivot
variable.  Induction on the matrix size and a sparse permutation-matrix
specialization exclude divisibility of the constant term by the leading
minor.
-/

noncomputable section

namespace SquarePolynomial

theorem detPoly_one_eq :
    detPoly 1 = MvPolynomial.X ((0 : Fin 1), (0 : Fin 1)) := by
  rw [detPoly, Matrix.det_fin_one]
  rfl

theorem detPoly_one_irreducible : Irreducible (detPoly 1) := by
  rw [detPoly_one_eq]
  exact MvPolynomial.X_prime.irreducible

abbrev pivot2 : Var 2 := ((1 : Fin 2), (1 : Fin 2))
abbrev Other2 := Free pivot2

def other2_00 : Other2 := ⟨((0 : Fin 2), (0 : Fin 2)), by decide⟩
def other2_01 : Other2 := ⟨((0 : Fin 2), (1 : Fin 2)), by decide⟩
def other2_10 : Other2 := ⟨((1 : Fin 2), (0 : Fin 2)), by decide⟩

lemma detPoly_two_nested :
    toNested (R := ℝ) pivot2 (detPoly 2) =
      Polynomial.C (MvPolynomial.X other2_00) * Polynomial.X +
        Polynomial.C (-(MvPolynomial.X other2_01 *
          MvPolynomial.X other2_10)) := by
  rw [detPoly, Matrix.det_fin_two]
  simp [pivot2, other2_00, other2_01, other2_10]
  ring

theorem detPoly_two_irreducible : Irreducible (detPoly 2) := by
  have hnotdiv : ¬(MvPolynomial.X other2_00 : MvPolynomial Other2 ℝ) ∣
      -(MvPolynomial.X other2_01 * MvPolynomial.X other2_10) := by
    simp only [dvd_neg, MvPolynomial.X_dvd_mul_iff, MvPolynomial.X_dvd_X]
    decide
  have hrel : IsRelPrime
      (MvPolynomial.X other2_00 : MvPolynomial Other2 ℝ)
      (-(MvPolynomial.X other2_01 * MvPolynomial.X other2_10)) :=
    MvPolynomial.X_prime.irreducible.isRelPrime_iff_not_dvd.mpr hnotdiv
  have hnested : Irreducible (toNested (R := ℝ) pivot2 (detPoly 2)) := by
    rw [detPoly_two_nested]
    exact Polynomial.irreducible_C_mul_X_add_C
      (MvPolynomial.X_ne_zero other2_00) hrel
  exact (MulEquiv.irreducible_iff
    (toNested (R := ℝ) pivot2).toMulEquiv).mp hnested

section GenericInduction

variable {K : Type*} [Field K]

/-- The generic determinant over an arbitrary field. -/
def genericDetPoly (K : Type*) [Field K] (n : ℕ) :
    MvPolynomial (Fin n × Fin n) K :=
  Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) K)

@[simp] lemma genericDetPoly_real (n : ℕ) :
    genericDetPoly ℝ n = detPoly n := rfl

abbrev pivotZero (n : ℕ) : Fin (n + 1) × Fin (n + 1) :=
  ((0 : Fin (n + 1)), (0 : Fin (n + 1)))

abbrev DetCoeffVar (n : ℕ) := Free (pivotZero n)

def lowerVarEmbedding (n : ℕ) :
    (Fin n × Fin n) ↪ DetCoeffVar n where
  toFun ij := ⟨(ij.1.succ, ij.2.succ), by
    intro h
    have hfst := congrArg Prod.fst h
    simp at hfst⟩
  inj' := by
    intro x y h
    apply Prod.ext
    · apply Fin.ext
      simpa using congrArg (fun z : DetCoeffVar n => z.1.1.val) h
    · apply Fin.ext
      simpa using congrArg (fun z : DetCoeffVar n => z.1.2.val) h

def lowerDet (K : Type*) [Field K] (n : ℕ) :
    MvPolynomial (DetCoeffVar n) K :=
  MvPolynomial.rename (lowerVarEmbedding n) (genericDetPoly K n)

def pivotBaseMatrix (K : Type*) [Field K] (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1))
      (MvPolynomial (DetCoeffVar n) K) :=
  fun i j => if h : (i, j) = pivotZero n then 0 else MvPolynomial.X ⟨(i, j), h⟩

def pivotDirection (K : Type*) [Field K] (n : ℕ) :
    Fin (n + 1) → MvPolynomial (DetCoeffVar n) K :=
  fun i => if i = 0 then 1 else 0

def detPivotLeading (K : Type*) [Field K] (n : ℕ) :
    MvPolynomial (DetCoeffVar n) K :=
  Matrix.det ((pivotBaseMatrix K n).updateCol 0 (pivotDirection K n))

def detPivotRemainder (K : Type*) [Field K] (n : ℕ) :
    MvPolynomial (DetCoeffVar n) K :=
  Matrix.det (pivotBaseMatrix K n)

lemma genericDetPoly_pivot_nested (n : ℕ) :
    toNested (R := K) (pivotZero n) (genericDetPoly K (n + 1)) =
      Polynomial.C (detPivotLeading K n) * Polynomial.X +
        Polynomial.C (detPivotRemainder K n) := by
  classical
  let M := pivotBaseMatrix K n
  let u : Fin (n + 1) → MvPolynomial (DetCoeffVar n) K := fun i => M i 0
  let v := pivotDirection K n
  have hmatrix :
      (toNested (R := K) (pivotZero n)).toRingHom.mapMatrix
          (Matrix.mvPolynomialX (Fin (n + 1)) (Fin (n + 1)) K) =
        (M.map Polynomial.C).updateCol 0 (affineColumn u v) := by
    apply Matrix.ext
    intro i j
    simp only [RingHom.mapMatrix_apply]
    by_cases hj : j = 0
    · subst j
      by_cases hi : i = 0
      · subst i
        simp [M, u, v, pivotBaseMatrix, pivotDirection, affineColumn]
      · have hne : (i, (0 : Fin (n + 1))) ≠ pivotZero n := by
          intro h
          exact hi (congrArg Prod.fst h)
        simp [M, u, v, pivotBaseMatrix, pivotDirection, affineColumn, hi, hne]
    · have hne : (i, j) ≠ pivotZero n := by
        intro h
        exact hj (congrArg Prod.snd h)
      simp [M, u, v, pivotBaseMatrix, hj, hne]
  calc
    toNested (R := K) (pivotZero n) (genericDetPoly K (n + 1)) =
        Matrix.det
          ((toNested (R := K) (pivotZero n)).toRingHom.mapMatrix
            (Matrix.mvPolynomialX (Fin (n + 1)) (Fin (n + 1)) K)) :=
      (toNested (R := K) (pivotZero n)).toRingHom.map_det _
    _ = Matrix.det ((M.map Polynomial.C).updateCol 0 (affineColumn u v)) := by
      rw [hmatrix]
    _ = Polynomial.C (Matrix.det (M.updateCol 0 u)) +
        Polynomial.C (Matrix.det (M.updateCol 0 v)) * Polynomial.X :=
      det_updateCol_affine M 0 u v
    _ = Polynomial.C (detPivotLeading K n) * Polynomial.X +
        Polynomial.C (detPivotRemainder K n) := by
      have hu : M.updateCol 0 u = M := by
        ext i j
        by_cases hj : j = 0 <;> simp [hj, u]
      simp [detPivotLeading, detPivotRemainder, M, v, hu, add_comm]

lemma detPivotLeading_eq_lowerDet (n : ℕ) :
    detPivotLeading K n = lowerDet K n := by
  classical
  rw [detPivotLeading, Matrix.det_succ_column_zero]
  rw [Fin.sum_univ_succ]
  simp [pivotDirection]
  have hmatrix :
      ((pivotBaseMatrix K n).updateCol 0 (pivotDirection K n)).submatrix
          Fin.succ Fin.succ =
        (MvPolynomial.rename (lowerVarEmbedding n)).mapMatrix
          (Matrix.mvPolynomialX (Fin n) (Fin n) K) := by
    apply Matrix.ext
    intro i j
    simp [pivotBaseMatrix, lowerVarEmbedding]
  rw [hmatrix]
  simp only [lowerDet, genericDetPoly]
  exact (MvPolynomial.rename (R := K) (lowerVarEmbedding n)).map_det _ |>.symm

lemma lowerDet_prime (n : ℕ) (hprime : Prime (genericDetPoly K n)) :
    Prime (lowerDet K n) := by
  classical
  let s : Set (DetCoeffVar n) := Set.range (lowerVarEmbedding n)
  let e : (Fin n × Fin n) ≃ s := Equiv.ofInjective (lowerVarEmbedding n)
    (lowerVarEmbedding n).injective
  have he : Prime
      (MvPolynomial.rename e (genericDetPoly K n) : MvPolynomial s K) :=
    (MulEquiv.prime_iff (MvPolynomial.renameEquiv K e).toMulEquiv).mpr hprime
  have hs : Prime
      (MvPolynomial.rename ((↑) : s → DetCoeffVar n)
        (MvPolynomial.rename e (genericDetPoly K n))) :=
    (MvPolynomial.prime_rename_iff (R := K) s).mpr he
  rw [lowerDet]
  convert hs using 1
  rw [MvPolynomial.rename_rename]
  apply congrArg (fun f => MvPolynomial.rename f (genericDetPoly K n))
  funext ij
  rfl

def swapZeroOne {n : ℕ} (hn : 0 < n) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.swap (0 : Fin (n + 1)) ⟨1, by omega⟩

def swapCoeffAssignment {n : ℕ} (hn : 0 < n) : DetCoeffVar n → K :=
  fun q => (swapZeroOne hn).permMatrix K q.1.1 q.1.2

lemma eval_lowerDet_swap_eq_zero {n : ℕ} (hn : 0 < n) :
    MvPolynomial.eval (swapCoeffAssignment (K := K) hn) (lowerDet K n) = 0 := by
  rw [lowerDet, MvPolynomial.eval_rename]
  rw [genericDetPoly, Matrix.eval_det_mvPolynomialX (Fin n) K]
  let i0 : Fin n := ⟨0, hn⟩
  apply Matrix.det_eq_zero_of_row_eq_zero i0
  intro j
  simp [swapCoeffAssignment, swapZeroOne, lowerVarEmbedding,
    Equiv.Perm.permMatrix, Equiv.toPEquiv_apply, i0]
  exact (Fin.succ_ne_zero j).symm

lemma eval_detPivotRemainder_swap_eq_neg_one {n : ℕ} (hn : 0 < n) :
    MvPolynomial.eval (swapCoeffAssignment (K := K) hn)
      (detPivotRemainder K n) = -1 := by
  let y := swapCoeffAssignment (K := K) hn
  have hcoeff :
      (toNested (R := K) (pivotZero n) (genericDetPoly K (n + 1))).coeff 0 =
        detPivotRemainder K n := by
    rw [genericDetPoly_pivot_nested]
    simp
  have heval := toNested_map_eval (R := K) (pivotZero n)
    (genericDetPoly K (n + 1)) 0 y
  rw [← Polynomial.coeff_zero_eq_eval_zero] at heval
  rw [Polynomial.coeff_map, hcoeff] at heval
  have hinsert : insertDistinguished (pivotZero n) 0 y =
      fun ij => (swapZeroOne hn).permMatrix K ij.1 ij.2 := by
    funext ij
    by_cases h : ij = pivotZero n
    · subst ij
      simp [insertDistinguished, swapZeroOne, Equiv.Perm.permMatrix,
        Equiv.toPEquiv_apply]
    · simp [insertDistinguished, y, swapCoeffAssignment, h]
  rw [hinsert, genericDetPoly, Matrix.eval_det_mvPolynomialX (Fin (n + 1)) K] at heval
  change (MvPolynomial.eval y) (detPivotRemainder K n) =
    Matrix.det ((swapZeroOne hn).permMatrix K) at heval
  rw [Matrix.det_permutation] at heval
  dsimp [swapZeroOne] at heval
  rw [Equiv.Perm.sign_swap] at heval
  · simpa [y] using heval
  · intro h
    have hv := congrArg Fin.val h
    simp at hv

lemma detPivotLeading_not_dvd_remainder {n : ℕ} (hn : 0 < n) :
    ¬detPivotLeading K n ∣ detPivotRemainder K n := by
  intro hdvd
  have hmap := map_dvd (MvPolynomial.eval (swapCoeffAssignment (K := K) hn)) hdvd
  rw [detPivotLeading_eq_lowerDet, eval_lowerDet_swap_eq_zero hn,
    eval_detPivotRemainder_swap_eq_neg_one hn] at hmap
  simpa using hmap

/-- The generic determinant is irreducible over every field. -/
theorem genericDetPoly_irreducible (n : ℕ) (hn : 0 < n) :
    Irreducible (genericDetPoly K n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      by_cases hm : m = 0
      · subst m
        rw [genericDetPoly, Matrix.det_fin_one]
        exact MvPolynomial.X_prime.irreducible
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
        have hsmallIrr : Irreducible (genericDetPoly K m) := ih m (by omega) hmpos
        have hsmallPrime : Prime (genericDetPoly K m) :=
          UniqueFactorizationMonoid.irreducible_iff_prime.mp hsmallIrr
        have hleadPrime : Prime (detPivotLeading K m) := by
          rw [detPivotLeading_eq_lowerDet]
          exact lowerDet_prime m hsmallPrime
        have hrel : IsRelPrime (detPivotLeading K m) (detPivotRemainder K m) :=
          hleadPrime.irreducible.isRelPrime_iff_not_dvd.mpr
            (detPivotLeading_not_dvd_remainder hmpos)
        have hnested : Irreducible
            (toNested (R := K) (pivotZero m) (genericDetPoly K (m + 1))) := by
          rw [genericDetPoly_pivot_nested]
          exact Polynomial.irreducible_C_mul_X_add_C hleadPrime.ne_zero hrel
        exact (MulEquiv.irreducible_iff
          (toNested (R := K) (pivotZero m)).toMulEquiv).mp hnested

theorem detPoly_irreducible {n : ℕ} (hn : 0 < n) :
    Irreducible (detPoly n) := by
  exact genericDetPoly_irreducible (K := ℝ) n hn

/-- In pivot coordinates, the generic determinant is primitive over the ring
of the remaining variables. -/
theorem genericDetPoly_pivot_isPrimitive {n : ℕ} (hn : 0 < n) :
    (toNested (R := K) (pivotZero n)
      (genericDetPoly K (n + 1))).IsPrimitive := by
  have hsmallIrr : Irreducible (genericDetPoly K n) :=
    genericDetPoly_irreducible (K := K) n hn
  have hsmallPrime : Prime (genericDetPoly K n) :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hsmallIrr
  have hleadPrime : Prime (detPivotLeading K n) := by
    rw [detPivotLeading_eq_lowerDet]
    exact lowerDet_prime n hsmallPrime
  have hirrFull : Irreducible (genericDetPoly K (n + 1)) :=
    genericDetPoly_irreducible (K := K) (n + 1) (by omega)
  have hirrNested : Irreducible
      (toNested (R := K) (pivotZero n) (genericDetPoly K (n + 1))) :=
    (MulEquiv.irreducible_iff
      (toNested (R := K) (pivotZero n)).toMulEquiv).mpr hirrFull
  apply hirrNested.isPrimitive
  rw [genericDetPoly_pivot_nested,
    Polynomial.natDegree_linear hleadPrime.ne_zero]
  norm_num

/-- The square of the pivot-coordinate determinant is primitive as well. -/
theorem genericDetPoly_pivot_sq_isPrimitive {n : ℕ} (hn : 0 < n) :
    (toNested (R := K) (pivotZero n)
      (genericDetPoly K (n + 1)) ^ 2).IsPrimitive := by
  letI : NormalizedGCDMonoid (MvPolynomial (DetCoeffVar n) K) :=
    Nonempty.some inferInstance
  have hp := genericDetPoly_pivot_isPrimitive (K := K) hn
  simpa [pow_two] using hp.mul hp

end GenericInduction

end SquarePolynomial

#print axioms SquarePolynomial.detPoly_one_irreducible
#print axioms SquarePolynomial.detPoly_two_irreducible
#print axioms SquarePolynomial.detPoly_irreducible
#print axioms SquarePolynomial.genericDetPoly_pivot_sq_isPrimitive
