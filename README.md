# Finite-Sample Unbiasedly Estimable Information Monotones

This repository contains the Lean 4 formalization accompanying the paper
[*Finite-Sample Unbiasedly Estimable Information Monotones*](https://arxiv.org/abs/2606.14225).

The machine-checked entry point is [`PaperProofs.lean`](PaperProofs.lean).

The formalization verifies the paper's principal rigidity and classification
results in all three dimension regimes. It also develops a reusable body of
determinantal algebra, including a Lean formalization of the classical theorem
that every positive power of the generic maximal-minor ideal over an arbitrary
integral domain is primary.

## Motivation

Let $U=(u_{i\alpha})$ be the joint probability matrix of two finite random
variables. A functional of $U$ that is a polynomial of degree at most $d$
admits an unbiased estimator from $d$ independent samples. This motivates the
study of polynomial measures of dependence satisfying two information-theoretic
requirements:

1. **rank-one vanishing:** the functional vanishes on product distributions;
2. **data processing:** randomized post-processing cannot increase the
   functional.

The results formalized here show that these requirements impose strong
algebraic rigidity. In the taller case $n>m$, they force vanishing on the
simplex; in the square case $n=m$, they force a determinant-square factor
modulo the simplex equation; and in the wide case $n<m$, they force membership
in the square of the maximal-minor ideal modulo the simplex equation.

The development also verifies a Frobenius dependence functional under a
restricted class of stochastic channels and formalizes the semantic reduction
from copositivity to DPI recognition.

## Setup and notation

For integers $n,m\ge 1$, define the probability simplex

$$
\Delta_{n,m}
=\{U\in\mathbb R^{n\times m} :
u_{i\alpha}\ge 0,\ 
\sum_{i,\alpha}u_{i\alpha}=1\}.
$$

For an $n\times n$ column-stochastic matrix $T$, the formalized left-sided
data-processing inequality (DPI) is $F(TU)\le F(U)$ for
$U\in\Delta_{n,m}$.

Rank-one vanishing means that $F(U)=0$ whenever
$U\in\Delta_{n,m}$ and $\mathrm{rank}(U)\le 1$.

For a polynomial $P\in\mathbb R[u_{i\alpha}]$, write
$\tau=\sum_{i,\alpha}u_{i\alpha}$. Thus the affine probability simplex lies in
the hyperplane $\tau=1$.

In Lean, rectangular matrices are represented by the definitionally equal
iterated function type

```lean
Fin n → Fin m → ℝ
```

and `Matrix.of` is used when matrix rank is needed.

## Main results verified by Lean

Every theorem in this section is imported and checked by
[`PaperProofs.lean`](PaperProofs.lean).

### Rank-one vanishing bridge

The internal development initially uses an outer-product formulation of
rank-one vanishing. Lean proves that, on the probability simplex, this is
equivalent to the rank-at-most-one formulation used in the paper.

**Theorem (outer-product vanishing iff rank-one vanishing).**
For a functional $F:\mathbb R^{n\times m}\to\mathbb R$, the two formulations
of rank-one vanishing are equivalent on $\Delta_{n,m}$:

$$
\bigl(\forall x,y,\ F(xy^{\mathsf T})=0\bigr)
\quad\Longleftrightarrow\quad
\bigl(\forall U,\ \mathrm{rank}(U)\le 1\Rightarrow F(U)=0\bigr),
$$

where the quantifiers are restricted to points satisfying the relevant simplex
conditions.

```lean
GeneralAsymmetricC1.rko_iff_rankOneVanishing
```

The supporting development also proves that every outer product has rank at
most one and that every real matrix of rank at most one admits an outer-product
representation.

### Taller processed alphabet: $n>m\ge 2$

The first rigidity theorem concerns the regime in which the processed alphabet
is strictly larger than the reported alphabet.

**Theorem (tall-case $C^1$ rigidity).**
Let $n>m\ge 2$, let $\Omega\subseteq\mathbb R^{n\times m}$ be open with
$\Delta_{n,m}\subseteq\Omega$, and let
$F:\mathbb R^{n\times m}\to\mathbb R$. Assume that:

1. $F$ is $C^1$ on $\Omega$;
2. $F$ satisfies left-sided DPI on $\Delta_{n,m}$;
3. $F(U)=0$ for every $U\in\Delta_{n,m}$ with
   $\mathrm{rank}(U)\le 1$.

Then

$$
F(U)=0
\qquad\text{for every }U\in\Delta_{n,m}.
$$

The Lean theorem assumes `ContDiffOn ℝ 1 F Ω`, so it requires only $C^1$
regularity on an open neighborhood of the simplex, not global $C^1$
regularity.

```lean
GeneralAsymmetricC1.general_asymmetric_simplex_C1_openNeighborhood
```

**Corollary (tall-case polynomial factorization).**
Let $P\in\mathbb R[u_{i\alpha}]$ satisfy the polynomial tall-case hypotheses.
Then there exists a polynomial $Q$ such that $P=(\tau-1)Q$. Equivalently,
$P\in\langle\tau-1\rangle$.

Thus every such polynomial vanishes identically on the affine simplex
hyperplane.

```lean
AsymmetricPolynomial.asymmetric_polynomial_mem_simplex_ideal
```

### Equal alphabet sizes: $n=m\ge 2$

In the square case, the determinant gives the fundamental algebraic
obstruction.

**Theorem (square-case determinant-square classification).**
Let $n\ge 2$, and let $P\in\mathbb R[u_{i\alpha}]$ satisfy left-sided DPI and
rank-one vanishing on $\Delta_{n,n}$. Then there exist polynomials $Q$ and $K$
such that

$$
P=(\det U)^2Q+(\tau-1)K.
$$

Equivalently,
$P\in\langle(\det U)^2\rangle+\langle\tau-1\rangle$.
Hence, modulo the affine simplex equation $\tau=1$, every such polynomial is
divisible by $(\det U)^2$.

```lean
SquarePolynomial.square_simplex_det_sq
```

**Corollary (square-case degree lower bound).**
Under the hypotheses above, if $P$ is nonzero at some point of
$\Delta_{n,n}$, then
$2n\le\mathrm{totalDegree}(P)$.

```lean
SquarePolynomial.square_simplex_totalDegree_lower_bound
```

The formalization also proves a converse-type construction by constant
compensation.

**Theorem (constant compensation).**
Let $n\ge 2$, and let $P$ be a polynomial that is row-symmetric on
$\Delta_{n,n}$. Then there exists $M\ge 0$ such that

$$
U\longmapsto(\det U)^2\bigl(P(U)+M\bigr)
$$

satisfies left-sided DPI on $\Delta_{n,n}$.

More precisely, the Lean development defines the normalized-defect supremum 
$M_{\*}(P)$, proves that it is finite, and proves that every
$M\ge\max\lbrace 0,M_*(P)\rbrace$ is a valid compensation constant.

```lean
SquarePolynomial.compensationRatioSet_bddAbove
SquarePolynomial.compensatedEval_dpi_of_compensationSup_le
SquarePolynomial.exists_constantCompensation_dpi
```

### Wider reported alphabet: $2\le n<m$

Let $R=\mathbb R[u_{i\alpha}]$ be the polynomial ring of the generic
$n\times m$ matrix, and let $I_n\subseteq R$ be the ideal generated by its
maximal $n\times n$ minors.

**Theorem (wide-case maximal-minor-square classification).**
Let $2\le n<m$, and let $P\in R$ satisfy left-sided DPI and rank-one vanishing
on $\Delta_{n,m}$. Then 

$$P\in I_n^2+\langle\tau-1\rangle.$$

Equivalently, there exist $Q\in I_n^2$ and $K\in R$ such that
$P=Q+(\tau-1)K$.

Thus, modulo the affine simplex equation, $P$ belongs to the square of the
maximal-minor ideal.

```lean
WidePolynomial.wide_simplex_maximalMinor_sq
```

**Corollary (wide-case degree lower bound).**
Under the hypotheses above, if $P$ is nonzero at some point of
$\Delta_{n,m}$, then
$2n\le\mathrm{totalDegree}(P)$.

```lean
WidePolynomial.wide_simplex_totalDegree_lower_bound
```

### Frobenius Dependence Index

For $U=(u_{i\alpha})\in\Delta_{n,m}$, define the row and column marginals by
$r_i=\sum_\alpha u_{i\alpha}$ and
$c_\alpha=\sum_i u_{i\alpha}$.

The squared Frobenius Dependence Index is

$$
F_{\mathrm{FDI}}(U)
=\sum_{i,\alpha}
\bigl(u_{i\alpha}-r_ic_\alpha\bigr)^2.
$$

**Theorem (zero set of the Frobenius Dependence Index).**
For every $U\in\Delta_{n,m}$,

$$
F_{\mathrm{FDI}}(U)=0
\quad\Longleftrightarrow\quad
\mathrm{rank}(U)=1.
$$

Thus the Frobenius Dependence Index vanishes exactly on product
distributions.

```lean
FrobeniusDependence.fdi_eq_zero_iff_rank_eq_one
```

**Theorem (restricted-channel DPI for the Frobenius Dependence Index).**
The functional $F_{\mathrm{FDI}}$ satisfies two-sided DPI for every channel in
the convex hull of the doubly-stochastic channels and the rank-one erasure
channels.

The Lean development also proves the corresponding characterization of this
restricted channel class.

```lean
FrobeniusDependence.restrictedChannel_iff_mem_convexHull
FrobeniusDependence.fdi_convexHull_dpi
```

The restriction is essential.

**Theorem (failure of unrestricted stochastic DPI).**
There exists an exact rational $4\times3$ counterexample for which
$F_{\mathrm{FDI}}$ violates unrestricted stochastic DPI.

```lean
FrobeniusDependence.fdi_not_full_dpi
```

### Semantic reduction from copositivity to DPI recognition

For a matrix $A$, the formalization constructs an explicit polynomial
functional of the form

$$
F_A(U)
=(\det U)^2 c(U)^{\mathsf T}A c(U),
$$

where $c(U)$ is the vector appearing in the formalized construction.

**Theorem (copositivity-DPI equivalence).**
For $n\ge 2$, the constructed polynomial functional satisfies

$$
F_A\text{ satisfies DPI}
\quad\Longleftrightarrow\quad
A\text{ is copositive}.
$$

The equivalence is also exported for rational input matrices.

```lean
CopositiveDPIRecognition.rationalRecognitionPoly_dpi_iff_copositive
```

The constructed family is also proved to be row-symmetric on the simplex and
rank-one vanishing.

```lean
CopositiveDPIRecognition.recognitionPoly_rowSymmetricOnSimplex
CopositiveDPIRecognition.recognitionPoly_rankOneVanishing
CopositiveDPIRecognition.copositive_semantically_reduces_to_dpi
```

Lean verifies the complete mathematical and semantic reduction. The final
complexity-theoretic conclusion additionally uses the external theorem that
strong rational copositivity recognition is coNP-complete.

The repository does **not** claim to formalize that external complexity theorem
or a complete theory of polynomial-time many-one reductions for rational
arithmetic circuits.

## Reusable determinantal algebra

The wide-case proof formalizes in Lean a classical theorem in determinantal
algebra that is useful independently of probability simplices and information
theory.

For the classical result, see Bruns and Vetter,
[*Determinantal Rings*](https://doi.org/10.1007/BFb0080378),
Corollary 7.10(a); see also the more general Corollary 9.18.

### Generic maximal-minor ideals

**Theorem (generic maximal-minor ideal).**
Let $D$ be an arbitrary integral domain, let
$R=D[x_{ij}\mid 1\le i\le p,\ 1\le j\le m]$, and let
$X=(x_{ij})$ be the generic $p\times m$ matrix with $p\le m$.
Let $I_p(X)\subseteq R$ be the ideal generated by the maximal
$p\times p$ minors of $X$.

Then $I_p(X)$ is prime, and for every integer $r\ge 1$,

$$
I_p(X)^r\text{ is }I_p(X)\text{-primary}.
$$

In particular, $I_p(X)^2$ is $I_p(X)$-primary.

The corresponding coefficient-polymorphic Lean declarations are

```lean
GenericMaximalMinor.maximalMinorIdealOver_isPrime
GenericMaximalMinor.maximalMinorIdealOver_pow_isPrimary
GenericMaximalMinor.maximalMinorIdealOver_sq_isPrimary
```

### Strong cancellation

The Lean development also proves the following strong cancellation form.

**Theorem (cancellation modulo powers of the maximal-minor ideal).**
Under the hypotheses above, let $r\ge 1$ and $a,b\in R$. If
$a\notin I_p(X)$ and $ab\in I_p(X)^r$, then

$$
b\in I_p(X)^r.
$$

Equivalently,

$$
a\notin I_p(X),\qquad
ab\in I_p(X)^r
\quad\Longrightarrow\quad
b\in I_p(X)^r.
$$

```lean
GenericMaximalMinor.mem_maximalMinorIdealOver_pow_of_mul_mem_of_not_mem
```

The specialization to the real wide-polynomial API, together with the
fixed-pivot saturation consequence, is exported through

```lean
WidePolynomial.maximalMinorIdeal_isPrime
WidePolynomial.maximalMinorIdeal_sq_isPrimary
WidePolynomial.mem_maximalMinorIdeal_sq_of_pivot_pow_mul_mem
```

### Straightening and standard-minor basis

The proof of primaryness is supported by a reusable straightening and basis
theory for generic minors.

**Theorem (two-minor straightening).**
Over an arbitrary commutative ring, the product of two minors admits the
formalized straightening expansion into standard minor products.

```lean
GenericMaximalMinor.two_minor_straightening
```

**Theorem (linear independence of standard minor products).**
The standard products of nonempty minors are linearly independent.

```lean
GenericMaximalMinor.standardMinorProducts_linearIndependent
```

**Theorem (spanning by standard minor products).**
The standard products of nonempty minors span the generic polynomial ring.

```lean
GenericMaximalMinor.standardMinorProducts_span_eq_top
```

Consequently, the formalization constructs a basis of the generic polynomial
ring by standard minor products.

```lean
GenericMaximalMinor.standardMinorProductBasis
```

### Characterization of powers of the maximal-minor ideal

The development also proves an exact filtration criterion for membership in
powers of the maximal-minor ideal.

**Theorem (trailing-degree characterization).**
For every positive power of the generic maximal-minor ideal, membership is
characterized exactly by the formalized weight/trailing-degree condition.

```lean
GenericMaximalMinor.mem_maximalMinorIdealOver_pow_iff_trailingDegree
```

Thus the primaryness theorem is not introduced as an external algebraic
assumption: the straightening theory, basis construction, filtration
description, cancellation theorem, primality theorem, and primaryness theorem
are all proved within the Lean development.

## Paper-to-Lean correspondence

| Mathematical result | Lean declaration | Source file |
|---|---|---|
| Outer-product RKO iff rank $\le 1$ vanishing | `GeneralAsymmetricC1.rko_iff_rankOneVanishing` | [`GeneralAsymmetricC1.lean`](GeneralAsymmetricC1.lean) |
| $n>m$ open-neighborhood $C^1$ rigidity | `GeneralAsymmetricC1.general_asymmetric_simplex_C1_openNeighborhood` | [`GeneralAsymmetricC1.lean`](GeneralAsymmetricC1.lean) |
| $n>m$ polynomial factorization | `AsymmetricPolynomial.asymmetric_polynomial_mem_simplex_ideal` | [`AsymmetricPolynomialCorollary.lean`](AsymmetricPolynomialCorollary.lean) |
| Square determinant-square classification | `SquarePolynomial.square_simplex_det_sq` | [`SquareSimplexTheorem.lean`](SquareSimplexTheorem.lean) |
| Square degree lower bound | `SquarePolynomial.square_simplex_totalDegree_lower_bound` | [`SquareDegreeBound.lean`](SquareDegreeBound.lean) |
| Constant compensation | `SquarePolynomial.exists_constantCompensation_dpi` | [`ConstantCompensation.lean`](ConstantCompensation.lean) |
| Wide maximal-minor-square classification | `WidePolynomial.wide_simplex_maximalMinor_sq` | [`WideSimplexTheorem.lean`](WideSimplexTheorem.lean) |
| Wide degree lower bound | `WidePolynomial.wide_simplex_totalDegree_lower_bound` | [`WideSimplexTheorem.lean`](WideSimplexTheorem.lean) |
| Generic maximal-minor ideal is prime | `GenericMaximalMinor.maximalMinorIdealOver_isPrime` | [`MaximalMinorWeight.lean`](MaximalMinorWeight.lean) |
| Every positive maximal-minor-ideal power is primary | `GenericMaximalMinor.maximalMinorIdealOver_pow_isPrimary` | [`MaximalMinorWeight.lean`](MaximalMinorWeight.lean) |
| Strong cancellation for maximal-minor-ideal powers | `GenericMaximalMinor.mem_maximalMinorIdealOver_pow_of_mul_mem_of_not_mem` | [`MaximalMinorWeight.lean`](MaximalMinorWeight.lean) |
| FDI vanishes exactly at rank one | `FrobeniusDependence.fdi_eq_zero_iff_rank_eq_one` | [`FrobeniusDependence.lean`](FrobeniusDependence.lean) |
| FDI convex-hull DPI | `FrobeniusDependence.fdi_convexHull_dpi` | [`FrobeniusDependence.lean`](FrobeniusDependence.lean) |
| Rational copositivity/DPI equivalence | `CopositiveDPIRecognition.rationalRecognitionPoly_dpi_iff_copositive` | [`CopositiveDPIRecognition.lean`](CopositiveDPIRecognition.lean) |

## Reproducing the verification

The project is pinned to Lean `v4.32.0` and mathlib `v4.32.0`.

Install Lean through [`elan`](https://lean-lang.org/install/), then run:

```bash
git clone https://github.com/yuqkong-1844/finite-sample-information-monotones.git
cd finite-sample-information-monotones
lake update
lake exe cache get
lake build
lake env lean PaperProofs.lean
```

The first two Lake commands obtain the pinned dependencies and the precompiled
mathlib cache. A successful verification ends with exit code `0`. The theorem
types and axiom reports printed by `PaperProofs.lean` are informational.

To inspect the proofs interactively, open the repository folder in VS Code with
the official **Lean 4** extension (`leanprover.lean4`), open
[`PaperProofs.lean`](PaperProofs.lean), and Cmd-click a declaration to jump to
its proof. Placing the cursor inside a tactic block displays the current goal
in the Lean Infoview.

## Completeness and axiom audit

The Lean source contains no `sorry`, `admit`, user-declared `axiom`, or
`unsafe` shortcut. This can be checked with

```bash
rg -n '\b(sorry|admit|axiom|unsafe)\b' --glob '*.lean' .
```

The command should print nothing.

The final `#print axioms` commands report only

```text
propext
Classical.choice
Quot.sound
```

which are standard Lean foundations used by mathlib.

## Citation

For the mathematical results, please cite:

> *Finite-Sample Unbiasedly Estimable Information Monotones*,  
> [arXiv:2606.14225](https://arxiv.org/abs/2606.14225).

For the classical determinantal-algebra theorem on generic maximal-minor ideals
and their powers, see:

> Winfried Bruns and Udo Vetter,  
> [*Determinantal Rings*](https://doi.org/10.1007/BFb0080378),  
> Corollary 7.10(a); see also Corollary 9.18.

When reusing the Lean code or the general determinantal-algebra development,
please also cite this repository and identify the release or commit used.

## License

This formalization is released under the
[Apache License 2.0](LICENSE).
