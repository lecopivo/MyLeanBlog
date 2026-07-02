import VersoBlog
import Blog.Categories
import Blog.Meta

open Verso Genre Blog

set_option linter.unusedVariables false

#doc (Post) "A few thoughts on verified numerical software and finite arithmetic" =>

%%%
authors := ["Tomáš Skřivan"]
date := {year := 2026, month := 2, day := 22}
categories := []
%%%

NumLean aims to be a formally verified version of NumPy. That sounds straightforward, but the phrase "formally verified numerical software" hides an important question: verified against which semantics?

For exact mathematics, the answer is often clear. A function that sums an array should compute the mathematical sum of its entries. But numerical software is usually executed with finite arithmetic, especially floating-point arithmetic, and there the situation becomes much more subtle.

There are two messages I want to convey in this post. First, real-number reasoning is not a luxury or a mathematical indulgence. It is often the clearest way to say what a numerical program is supposed to mean. Second, reasoning about finite arithmetic is not one problem with one standard solution. It probably requires several different techniques, depending on the question we want to answer.

This is also an invitation. I want NumLean to support serious reasoning about finite arithmetic, but I am not an expert in floating-point verification, interval methods, or numerical error analysis. If you are, I would very much like your help.

# What Does It Mean To Verify `sum`?

Consider a function such as `Tensor.sum`. What should its specification be?

The first answer one wants to write is the mathematical one:

```
Tensor.sum xs = ∑ i, xs[i]
```

This is the right specification when the element type is a commutative monoid, ring, field, or some other algebraic structure where finite sums behave as expected. It is also the kind of statement mathlib is designed to support.

But `Float` does not behave like a commutative monoid under addition. Floating-point addition is rounded. It is not associative, and once special values such as `NaN` enter the picture, even more familiar algebraic laws fail. So if `Tensor.sum` is instantiated with `Float`, what exactly should it be verified to compute?

One possible answer is to specify the exact evaluation order:


```
def sum (xs : Fin n -> R) : R := Id.run do
  let mut s := 0
  for i in 0...n do
    s := s + xs[i]
  return s
```

Then we can require that `Tensor.sum` on `Float` performs exactly this loop. That is a valid specification, but it is probably not the one we want most of the time. It rules out many perfectly reasonable implementations: pairwise summation, vectorized reductions, parallel reductions, BLAS calls, GPU kernels, and other reorderings that may be faster or even more accurate.

At the other extreme, we might require the best representable floating-point answer to the real-valued sum. That sounds attractive, but it is usually too expensive to compute and too strong to be a useful specification for a general-purpose array library.

So there is a tension. If the specification is too operational, it prevents optimization. If it is too mathematical, it no longer says what actually happens on finite machines.

# The Polymorphic Specification

My current view is that the core specification of a function such as `Tensor.sum` should be polymorphic and algebraic.

`Tensor.sum` is a function that uses zero and addition on the element type. Under the assumption that the element type satisfies the laws of a commutative monoid, it should agree with the mathematical finite sum. Without those laws, the generic theorem simply does not apply.

This is not a failure. It is a useful separation of concerns.

For real numbers, rationals, integers, or any lawful algebraic model, `Tensor.sum` has the expected mathematical meaning. For floats, `Tensor.sum` is still executable, but the algebraic theorem is not available unless we provide a separate model explaining how floating-point execution relates to the real-number semantics.

# Real Semantics And Finite Execution

This distinction matters beyond `sum`. In numerical programming, the code we write often expresses an ideal real-valued computation. The machine program is an approximation strategy for that computation.

This is why I think real-number semantics should be central to NumLean. Without it, we risk verifying only accidental implementation details: a particular loop order, a particular reduction tree, a particular kernel. Those details matter, but they are rarely the reason the program was written. The reason is usually a real-valued mathematical object: an integral, an optimization problem, a differential equation, a least-squares fit, a linear solve.

In NumLean-style code, the hope is to write programs polymorphically over a model of real-number operations:

```
def f {R} {Rs} [RealModelOps R Rs] (x : R) : R :=
  ...
```

The same definition can then be instantiated in different ways. With `R = Real`, it gives the mathematical interpretation. With `R = Float`, it gives executable code. With `R = Interval`, it gives an enclosure. Each instantiation answers a different question.

The real-valued interpretation tells us what the program is supposed to mean. The finite-arithmetic interpretation tells us what the machine does. Verification has to relate the two.

# Interval Arithmetic

The most common way to reason about finite arithmetic is interval arithmetic. Instead of evaluating a function at one real number, we evaluate it on an interval that is known to contain the real input. The result is another interval that is guaranteed to contain the real output.

Informally, the theorem has the shape:

```
x ∈ I → f x ∈ f I
```

Here `x` is an exact real input, while `I` is a finite object such as an interval with rational or dyadic endpoints. The expression `f x` may not be executable, but `f I` is. If the interval result is small enough, we get a useful certified statement about the real computation.

This is a powerful technique, and it is often the right one. But it is not the whole story.

One limitation is that the estimate is usually a posteriori. We run the interval computation and only then learn how sharp the resulting enclosure is. Sometimes that is enough. Sometimes we want an a priori estimate: given a target precision, how accurately do we need to represent the input, how many subdivisions do we need, or which numerical method should we choose?

Those questions are not answered by interval arithmetic alone. They require additional mathematical analysis of the algorithm.

There are also other kinds of questions one may want to ask. Does a floating-point implementation follow the IEEE semantics of a particular expression? How large can the rounding error be? Is a rearranged computation more stable than the original one? Can a compensated summation algorithm be justified? Does a solver converge despite rounding? Can a mixed-precision implementation be certified? I do not expect one technique to answer all of these.

# Different Questions Need Different Proofs

This is the main point I want to emphasize: there is no single meaning of "verified numerical software" that covers every useful question.

Sometimes we want to prove that a program computes a mathematical function over `Real`.

Sometimes we want to prove that a floating-point implementation follows a particular operational semantics.

Sometimes we want a certified error bound between the floating-point result and the real-valued result.

Sometimes we want an algorithm-level theorem saying that a method converges at a known rate, independently of a particular run.

These are related, but they are not the same theorem.

For NumLean, I think the right foundation is to make the real-valued semantics primary, while still allowing finite-arithmetic models to be instantiated and reasoned about explicitly. Most of the time, when we write numerical software, the intended specification is not the exact sequence of floating-point operations we happened to write. The intended specification is a real-valued computation, together with a claim that our finite machine approximates it well enough for the problem at hand.

That separation is what makes optimization possible. It lets us rewrite, reorder, vectorize, parallelize, or replace code with specialized kernels, as long as we can justify that the optimized finite computation still approximates the same real-valued meaning.

I would like NumLean to become a place where these different styles of reasoning can coexist. Some parts may use interval arithmetic. Some may use explicit floating-point semantics. Some may use forward or backward error analysis. Some may use condition numbers, stability theorems, convergence proofs, or problem-specific estimates. I do not yet know what the right architecture for all of this should be.

So if you work on floating-point verification, interval arithmetic, constructive real analysis, numerical analysis, or any adjacent topic, please consider this an invitation. NumLean needs real expertise here. I can build some of the infrastructure, but the finite-arithmetic story should be shaped by people who understand the field much better than I do.
