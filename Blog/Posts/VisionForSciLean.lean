import VersoBlog
import Blog.Categories
import Blog.Meta
import Blog.Lean

import NumLean
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Constructions.HaarToSphere

open Verso Genre Blog NumLean

set_option linter.unusedVariables false
set_option checkBinderAnnotations false

macro "ℝ^" noWs n:term : term => `(EuclideanSpace ℝ (Fin $n))

-- #check  (mfderiv 𝓘(ℝ, ℝ^2) 𝓘(ℝ, ℝ) f x)

private axiom omitted {α} : α

variable {nθ nφ : ℕ} {R : Type} {Rs : ℕ → Type} [RealModelOps R Rs] [LawfulRealModel R]



-- variable (f : Metric.sphere (0 : ℝ^3) 1 → ℝ) (x : Metric.sphere (0 : ℝ^3) 1)

/-- Interpolate data on grid `(0, 0)...(nθ, nφ)` for `x ∈ [0, π) × [0, 2*π)`. -/
private noncomputable
def interpolate (data : R^[nθ,nφ]) (x : R×R) : R := omitted

/-- Convert point on a sphere `x : sphere (0 : ℝ^3) 1)` to its spherical coordinates `(θ, φ)`. -/
private noncomputable
def toSphericalCoord (x : Metric.sphere (0 : ℝ^3) 1) : ℝ×ℝ := omitted

open NumLean

private noncomputable
instance : RealModelOps ℝ (Vector ℝ) where
  tensorSum := omitted
  tensorAxpy := omitted
  tensorAxpySelf := omitted
  tensorScal := omitted
  tensorDot := omitted
  tensorMul := omitted
  tensorGemv := omitted
  tensorGer := omitted
  tensorGemm := omitted

open Classical in
private noncomputable
instance : LawfulDataRealModelOps ℝ where
  completeSpace := inferInstance
  decEq := inferInstance
  reHom x := x
  imHom x := 0

private noncomputable
instance : LawfulRealModelOps ℝ := omitted

private noncomputable
instance : LawfulRealModel ℝ where

private noncomputable
def basis (dims : ℕ×ℕ) (ij : Fin dims.1 × Fin dims.2) : Tensor ℝ (Fin dims.1 × Fin dims.2) := omitted

/-- Sphere in `ℝ³` -/
local macro "S²" : term => `(Metric.sphere (0 : ℝ^3) 1)

/-- Surface mearue of a sphere `S²` -/
local macro "μS" : term => `((omitted : MeasureTheory.Measure (S²)))

private noncomputable
instance : MeasurableSpace S² := omitted

open Matrix
local macro "⟪" x:term ", " y:term "⟫" : term => `(Inner.inner ℝ $x $y)

noncomputable section

private structure LogMsg (R : Type) where
  step : ℕ
  absError : R

private abbrev LogM (R : Type) := StateM (Array (LogMsg R))

private def log (msg : LogMsg R) : LogM R Unit :=
  modify (fun msgs => msgs.push msg)

private structure CGConfig (R : Type) where
  maxSteps : ℕ
  absTol : R


#doc (Post) "A Vision for Scientific Computing Library in Lean" =>

%%%
authors := ["Tomáš Skřivan"]
date := {year := 2026, month := 2, day := 22}
categories := []
%%%

```lean' -show
open NumLean
set_option checkBinderAnnotations false
```

This post follows the announcement of NumLean, a Lean library for multidimensional arrays. Here I want to sketch the larger goal: SciLean, a library for scientific computing built on top of NumLean.

At a first approximation, NumLean and SciLean are Lean's versions of NumPy and SciPy, but verified. That is true enough as a slogan, but it misses the part I find most exciting. Lean can let us write scientific software by stating the mathematical meaning first, and then deriving or justifying efficient implementations from that meaning.

I want to motivate SciLean in two steps. First, I will describe the verified-SciPy layer: the basic numerical tools that should form the foundation of the library. Second, I will use a small PCA example to show why a library like SciLean should do more than expose verified implementations of standard algorithms. It should help users formulate the right mathematical problem.

This also matters for teaching. Too often we teach computational and statistical methods as recipes: if you want this, call that function in some package. I would rather teach scientists to state precisely what they want to know and why. Once the intent is explicit, software should help choose and justify the computational method.

# Where To Start

With NumLean in place, we can start serious work on SciLean. As a practical roadmap, it makes sense to follow the broad structure of the [SciPy manual](https://docs.scipy.org/doc/scipy/tutorial/index.html) and focus first on a few central areas:

1. integration,
2. interpolation,
3. linear algebra,
4. optimization.

*Integration and interpolation.* The first layer should contain the standard definitions and theorems from introductory numerical analysis: Lagrange interpolation, Gaussian quadrature, piecewise-polynomial interpolation, cubic splines, and similar tools.

I would like this API to have two layers. The core layer should handle canonical domains: unit intervals, half-infinite intervals, boxes, and data indexed by integer coordinates. A second layer should explain how to transport those constructions to other domains using maps such as linear, affine, or monotone piecewise-linear transformations. This is how a uniform reference grid becomes a nonuniform physical grid.

*Linear algebra and optimization.* This layer should include the standard decompositions, direct solvers, iterative solvers, and basic optimization methods.

For iterative solvers, it is useful to separate the mathematical specification from the executable implementation. The implementation needs engineering features: logging, early stopping, residual tracking, absolute and relative error estimates, flexible matrix representations, and so on. Those details are essential for real use, but they can obscure the core proof. A good design lets us prove the mathematical properties against a clean specification, and then prove one theorem connecting the practical implementation to that specification.

# Beyond Verified Numerical Methods

So far I have described the _SciPy, but verified_ side of SciLean. That is useful, but by itself it is not enough. I do not have serious trust issues with SciPy; its authors have done excellent work, and the code has been tested by a huge user base. The more interesting question is what we can do once these numerical tools live in a language where their mathematical meaning is explicit.

Let me give an example: PCA applied to functions on a sphere. The point is not that PCA is complicated. The point is that applying a familiar method to the wrong mathematical object can quietly answer the wrong question. If we focus on the specification first, the mistake becomes visible.

Suppose we are working with functions defined on a sphere. These appear in directional data, radiance fields, spherical harmonics, geophysics, computer graphics, and many other applications. Here is an AI-generated illustration of a few such functions:

:::lightboxImage "static/imgs/spherical_functions.png" "Examples of spherical functions" "420px"
:::

A common representation is to sample the function on a grid in spherical coordinates. If we use `nθ` samples in the polar direction and `nφ` samples in the azimuthal direction, then the data has shape {lean'}`R^[nθ, nφ]`.

The problem with naive PCA in spatial settings is well known. For example, [Geographically weighted principal components analysis](https://www.tandfonline.com/doi/full/10.1080/13658816.2011.554838) begins its abstract with:

> Principal components analysis (PCA) is a widely used technique in the social and physical sciences. However in spatial applications, standard PCA is frequently applied without any adaptation that accounts for important spatial effects. Such a naive application can be problematic as such effects often provide a more complete understanding of a given process.

For spherical data, a naive grid in spherical coordinates overrepresents points near the poles. If we treat all samples equally, those regions contribute too much.

:::lightboxImage "static/imgs/discrete_spherical_functions.png" "Discretized spherical functions" "420px"
:::

What is PCA doing? It finds the directions in which the data varies the most. Those directions are usually the first ones we study when trying to understand a data set.

The dominant direction is the direction of maximal variance:

$$`
\varphi^* = \arg\max_{\langle \varphi,\varphi\rangle = 1} \mathrm{Var}\big(\langle f, \varphi\rangle\big)
`
where `f` is the random function on the sphere, and our data are samples of this random variable.

The crucial point is that $`\langle f, \varphi\rangle` is the inner product of two functions on the sphere:

$$`
\langle f, g\rangle = \int_{S^2} f(x) g(x) \, dS(x)
                    = \int_0^{\pi} \int_{0}^{2\pi} f(\theta, \phi) g(\theta, \phi) \text{sin}(\theta) \, d\phi \, d\theta
`

```lean' -show
variable {R : Type} {Rs : ℕ → Type} [RealModelOps R Rs] [LawfulRealModel R]
variable  {nθ nφ : Nat} (xs ys : R^[nθ, nφ])
open Metric
```

This is not correctly approximated by the naive dot product {lean'}`xs.dot ys = ∑ (i : Fin nθ) (j : Fin nφ), xs[i.1,j.1] * ys[i.1,j.1]`, which is what standard off-the-shelf PCA effectively uses.

We need to go back to the basics. PCA studies the eigenvectors and eigenvalues of the covariance operator:

$$`
\langle \varphi, C\psi\rangle = \mathrm{Cov}\big(\langle f,\varphi\rangle, \langle f,\psi\rangle\big)
`

Skipping some details, when `C` is represented by a matrix in a non-orthonormal discretized basis, the problem becomes a generalized eigenvalue problem:

$$`
C v = \lambda M v
`

Here `M` is the matrix representing the inner product of functions on the sphere. We represent a function by samples {lean'}`(xs : R^[nθ, nφ])`, and interpret those samples as an actual function using interpolation. Assume we have an interpolation function and a function converting a point on the sphere to spherical coordinates:
```lean'
#check (interpolate : R^[nθ, nφ] → (R×R) → R)
#check (toSphericalCoord : sphere (0 : ℝ^3) 1 → ℝ×ℝ)
```

```lean' -show
variable (xs ys : Tensor ℝ (Fin nθ × Fin nφ))
noncomputable section
```

With these functions, the continuous inner product can be expanded in the interpolation basis:
```lean'
theorem inner_in_basis :
  (∫ x, interpolate xs (toSphericalCoord x) *
        interpolate ys (toSphericalCoord x) ∂μS)
  =
  (∑ (i : Fin nθ) (i' : Fin nθ) (j : Fin nφ) (j' : Fin nφ),
    xs[i.1,j.1] * ys[i'.1,j'.1] *
    (∫ x, interpolate (basis (nθ,nφ) (i, j)) (toSphericalCoord x) *
          interpolate (basis (nθ,nφ) (i', j')) (toSphericalCoord x) ∂μS))
  := omitted
```

```lean' -show
section
variable (M  : ℝ ^[[nθ, nφ], [nθ, nφ]])
```
The correct discrete inner product is therefore {lean'}`xs.dot (M *ᵥ ys)`, where the matrix {lean'}`M` is defined by:
```lean' -show
end
```
```lean'
def M : ℝ ^[[nθ, nφ], [nθ, nφ]] := ⊞ ((i,j),(i',j')) =>
    (∫ x, interpolate (basis (nθ,nφ) (i, j)) (toSphericalCoord x) *
          interpolate (basis (nθ,nφ) (i', j')) (toSphericalCoord x) ∂μS)
```
After substituting spherical coordinates into the integral, we get an expression of the form $`\int \int P(θ, φ) \text{sin}(\theta) \, dθ \, dφ`, where $`P` is a polynomial of degree at most two and such integral can be computed exactly.

```lean' -show
section
variable (M  : ℝ ^[[nθ, nφ], [nθ, nφ]])
```
Turning a mathematical expression such as $`\int_{S^2} f(x) g(x) \, dS(x)` into a computable expression such as {lean'}`xs.dot (M *ᵥ ys)` is at the heart of many specialized numerical packages. This particular case is the core of finite-element method: symbolic expressions such as the dot product or $`\int_{S^2} \nabla f(x) \cdot \nabla g(x) \, dS(x)` become operations on concrete matrices.
```lean' -show
end
```

This is why merely creating _SciPy but verified_  is not enough. It is useful to prove that an interpolation scheme converges to the function it interpolates, but SciLean should capture much more: how interpolation interacts with integration, differentiation, inner products, changes of variables, and linear algebra.

Once these facts are available as theorems, we can write deterministic tactics that transform well-known classes of mathematical problems into tractable computational problems. But the real game-changer here is the use of AI, which will allow us to state problems in potentially less standard forms and work on non-standard problems. We should train an AI system capable of transforming even such problems into tractable computational tasks, while ensuring that they still correspond to the original problem as stated.

I believe that such a library can have a broader impact on how scientists analyze data and reason about computation. With such a library, we can also shift the focus in teaching, away from memorizing computational recipes and more toward stating clearly what we want to know. We should remain responsible for what and why we compute, but we can let the software worry about the concrete methods.

If that prospect sounds exciting, please express your interest on [Lean Zulip](https://leanprover.zulipchat.com/), join the effort and start building.
