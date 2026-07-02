import VersoBlog
import Blog.Categories
import Blog.Meta
import Blog.Lean

import NumLean
import NumLean.Experimental.Data.DyadicInterval.Basic
import NumLean.Experimental.Data.DyadicInterval.Isolate
import NumLean.Experimental.Interfaces.Interval.Lawful

open NumLean

open Verso Genre Blog


private axiom omitted {α} : α

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


set_option linter.unusedVariables false
set_option backward.do.legacy false

#doc (Post) "Introducing NumLean! A stepping stone towards verified numerics in Lean." =>

%%%
authors := ["Tomáš Skřivan"]
date := {year := 2026, month := 2, day := 22}
categories := []
%%%


Since around 2018, I have been wondering whether there is a better way to write numerical software and physics simulations. This kind of code is deeply mathematical. It is often easy to say what the code should do, such as "solve this differential equation", but much harder to implement it correctly and make it fast. Existing libraries help a lot, but they usually cover a fairly narrow class of problems. Once you step outside that class, you often have to reimplement a large part of the machinery yourself.

A key moment was when I saw Kevin Buzzard's 2019 talk, [The Future of Mathematics?](https://www.youtube.com/watch?v=Dp-mQ3HxgDE) That was when I learned about the community around Lean and mathlib: people trying to formalize large parts of mathematics in a single language. It made me ask a very tempting question. If Lean can express the mathematics I care about, could I write the thing I want to compute in Lean and then somehow turn that specification into runnable code?

That question led me to SciLean, a Lean library for scientific computing. My goal was to write high-level mathematical specifications and gradually transform them into executable programs. I worked on SciLean intensely for about four or five years, and then, about a year ago, I more or less gave up.

The problem was that SciLean sat in an awkward place. Formalization was not the main goal, so many proofs were left as future work. That made it hard for people interested in formal methods to understand what the library was for. At the same time, people doing computational mathematics had little reason to use SciLean, because it provided only a small fraction of the functionality available in mature ecosystems such as NumPy, Julia, MATLAB, and others. SciLean never caught on. I burned out and stopped working on it.

A few weeks ago, [Lauri Oksanen](https://www.mv.helsinki.fi/home/lsoksane/) asked me about the state of SciLean and said that he would be interested in formalizing some numerical mathematics. Sadly, I had to tell him that the project was more or less dead and, in its current state, not very usable.

But the underlying dream is still alive for me: a library where I can write a mathematical specification and turn it into runnable code. That dream may be too ambitious in its purest form. A more realistic version is a library where I can write code in the most direct mathematical style, and then optimize it aggressively because the library understands the mathematics well enough to preserve the intended semantics.

So I decided to start again with a narrower target: NumLean, a library focused on multidimensional arrays. I hope NumLean can become the foundation for a future SciLean. As the names suggest, NumLean and SciLean are meant to play roles in the Lean ecosystem roughly analogous to NumPy and SciPy in the Python ecosystem.

My design principles are roughly as follows:

1. Fully verified. NumLean should be held to the same standard as mathlib: no sorries, no axioms, and no `native_decide`.
2. Performant. NumLean should provide good performance out of the box, mainly through FFI bindings to established libraries such as BLAS. It should also provide a specialized, verifiable compiler for turning a useful subset of Lean into fast kernels for multidimensional arrays.
3. Extensible. NumLean should aim for mathlib-level generality in how it represents multidimensional arrays. Users should be able to index tensors not only by natural numbers, but also by colors, finite-element nodes, mesh elements, and other meaningful finite types. Arrays should be able to live on the CPU or GPU.

There are two main workflows I want NumLean to support.

*Verified Numerics*: It should be possible to write a numerical program once and reason about it at multiple levels. We should be able to talk about its ideal real-number semantics, and also about what happens when it is executed with finite arithmetic such as floating-point numbers. The goal is not to pretend that machines compute with real numbers. The goal is to relate the finite computation to the real-valued meaning we intended.

*Fearless Optimization*: The second workflow is writing a program in the most straightforward mathematical way and then optimizing it aggressively while preserving its real-number semantics. Matrix multiplication is the simplest example. The direct implementation is easy to write, but serious performance requires a lot of work. NumLean should make it possible to justify transformations from clear code to fast code using theorems, not just trust that the optimized version still means the same thing.

# A Brief Introduction to NumLean

```lean' -show
open NumLean
set_option checkBinderAnnotations false
```
NumLean is about working with multidimansional arrays which are represented as the type {lean'}`Tensor`, with conforortable notation such as `Float^[256,256,3]` for a tensor of floats with dimensions `256×256×3`. We can write a literal tensor with
```lean'
#check ⊞[1.0, 2.0, 3.0]
#check ⊞[[1.0, 2.0, 3.0], [4.0, 5.0, 6.0]]
#check ⊞[[[1.0, 2], [3,4]], [[5,6],[7,8]]]
#check ⊞ (i j : Fin 10) =>
  ⊞ (k l : Fin 5) => if i = j ∧ k = l then 1.0 else 0
```
Access its elements
```lean'
#check ⊞[1.0, 2.0, 3.0][1]
#check ⊞[[1.0, 2.0, 3.0], [4.0, 5.0, 6.0]][0,2]
#check ⊞[[[1.0, 2], [3,4]], [[5,6],[7,8]]][0,1,1]
```
Take its slices
```lean'
#check ⊞[1.0, 2.0, 3.0][1:2]&
#check ⊞[[1.0, 2.0, 3.0], [4.0, 5.0, 6.0]][:,:-1]&
```
Reshape them
```lean'
#check ⊞[1.0, 2, 3, 4].reshape h(2,2)
```
Multiply them
```lean'
#check ⊞[[1.0, 2], [3, 4]] *ᵥ ⊞[10.0, 100.0]
```
And other operations one would expectec from a library with multidimensional arrays. I wrote a [Quickstart for NumPy users](https://lecopivo.github.io/NumLeanManual/Quickstart-for-NumPy-Users/#quickstart) to give you a quick glimpse into the computational part of the library.

## Reasoning About Arrays

The core novelty of the library is that array representation is efficient *and* allows formal reasoning at the same time. For numerical software we really need to reason about the programs in its real-value semantics and in tis finite arithmetics semantics as well. For this purpose we need to write programs parametrize by the type `R` for the real numbers. Therefore we usually start by introducing this type with

```lean'
variable {R : Type} {Rs : Nat -> Type} [RealModelOps R Rs]
```
```lean' -show
variable {m n : Nat}
```

Where the class {lean'}`RealModelOps` says that {lean'}`R` provides the operations we expect from a model of the real numbers, and that {lean'}`Rs n` behaves like an array of {lean'}`n` values of type {lean'}`R`. We parameterize over the array type as well because Lean's standard containers, such as {lean'}`List`, {lean'}`Array`, and {lean'}`Vector`, are not enough for high-performance numerical computing.

In executable code, one might instantiate {lean'}`R = Float64` and {lean'}`Rs = Float64Vector`. In proofs, one might instantiate {lean'}`R = ℝ` and {lean'}`Rs n = EuclideanSpace ℝ (Fin n)`. The same program can therefore have both an executable interpretation and a mathematical interpretation.

Parameterizing over the array type also leaves room for GPU-backed implementations. There are already experimental implementations for `OpenCLFloat` and `OpenCLFloatVector`.

```lean' -show
variable {x normal : R^[n]}
```

For example, we can write a simple program that reflects the vector {lean'}`x` around the given normal vector {lean'}`normal`.
```lean'
def reflect (normal x : R^[n]) : R^[n] :=
    x - (2 * (normal.dot x)) • normal
```

Now when we want to prove program real-value properties about `reflect` we need to assume {lean'}`LawfulRealModel` which is effectivelly {lean'}`Prop` valued class stating that all the operations behave as for real numberes:

```lean'
theorem cont (normal : ℝ^[n]) :
    Continuous (fun (x : ℝ^[n]) => reflect normal x) := by
  unfold reflect
  sorry -- fun_prop
```

Or we can introduce instance of {lean'}`LawfulRealModel` is effectivelly a {lean'}`Prop` valued class containing all the laws of all the operations.
```lean'
theorem lin [LawfulRealModel R] (normal : R^[n]) :
    IsLinearMap R (fun (x : R^[n]) => reflect normal x) :=by
  sorry
```

To convince you even more I should show that
```lean'
variable [LawfulRealModel R]

def euclideanEquiv :
  R^[n] ≃ₗᵢ[R] EuclideanSpace R (Fin n) := sorry

def matrixEquiv :
  R^[m,n] ≃ₗ[R] Matrix (Fin m) (Fin n) R := sorry

-- -- todo: maybe shift this to ℝ
theorem euclidean_equiv
    (A : R^[m,n]) (x : R^[n]) (y : R^[m]) :
    euclideanEquiv (y + A *ᵥ x)
    =
    euclideanEquiv y
    +
    (matrixEquiv A).mulVec (euclideanEquiv x) := sorry
```

```lean' -show
variable {X I} {Ks K nX nI} [VectorType Ks K] [HasDefaultFlatRepr X Ks nX] [IndexType I nI]
```

To summarize, the main contribution of NumLean is that it offers you the type {lean'}`Tensor X I` with efficient vector, matrix and tensor operations and provable equivalence to `EuclidenSpace X I` which is linear isomorphism for `X` inner product space and `I` finite type.

Regarding reasoning in finite arithmetics, there is not much yet. There is a definition if {lean'}`DyadicInterval` using Lean's new {lean'}`Dyadic` numbers and instance of `Interval.LawfulRingOps` which is saying that the ring operations, {lean'}`RingOps DyadicInterval`, are lawful with respect to the ring operations on reals, {lean'}`Ring ℝ`. However, I'm not sure if this is a worthwhile direction as there are other Lean project doing interval arithmetics and it would be best to make sure that both libraries can easily cooperate.

# Moving forward

What is next for NumLean. There are still many things missing. Many natural theorems are missing. There needs to lots of work done on performance. Support for Float32, Complex32, Complex64 scalar types. Provide fast implementation using BLAS and continue working on [OpenCL backend](https://github.com/lecopivo/NumLeanOpenCL). Improved reasoning about ranges/for loops such as splitting, reordering. Improve slices workflow, add misssing many theorems about them.

With introduction of NumLean, I would like to also reastart effort on building SciLean from ground up. I have renamed my wild experiment to SciLeanLegacy and would like to start a clean version, fully verified and as a community effort. At the first order of approximation NumLean and SciLean are just ports of NumPy and SciPy to Lean but verified. But this is really reductive view and would not be overly interesting thing to do in my opinion. I believe, It can be much more and change a way how we write numerical software. I have written as second accompaniong blog post where I sketch out my vision for SciLean and why I'm excited about it. So if you are interested give it a read and if you find it compeling then join the effort!
