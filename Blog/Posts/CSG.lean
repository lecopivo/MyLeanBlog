import VersoBlog
import Blog.Categories
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
open Verso Genre Blog

#doc (Post) "Vibe coding with .lean instead of .md files" =>

%%%
authors := ["Tomas Skrivan"]
date := {year := 2026, month := 2, day := 20}
categories := []
%%%


I'm a computer graphics programmer specializing in physics simulation and computational geometry. As a trained mathematician, I love thinking about the math, but I have always seen the coding part as a necessary evil of the job. Roughly five years ago, I discovered interactive proof assistants and realized they could revolutionize how I write code. I could start from a precise mathematical formulation of a problem and interactively transform it into executable code. So I started working on the Lean 4 library SciLean, hoping to bring this idea to life. After four years, I would say the project is effectively dead: it did not gain meaningful traction, and I ran out of energy. It did not address the problems current Lean users have, and the likely target audience had little motivation to switch to Lean from far more mature ecosystems like C++, Python, or Julia.

I still believe the core idea of writing mathematical specifications and transforming them into executable code is sound. However, SciLean's approach was fundamentally flawed because it tried to provide a fixed set of transformation rules. The design space for these rules is too large, and implementing a practically useful subset is effectively impossible.

The rise of LLMs calls for rethinking the approach behind SciLean. AI has become capable enough that I think the workflow should look like this:
1. Hand-write a precise mathematical specification of your problem in Lean.
2. Transform that Lean specification into a more detailed Lean specification/code, tied back to the original spec with proofs.
3. Generate code in your target language from the detailed Lean specification.

At step one, I specify what I actually want to implement, but the result is still too coarse for AI to directly generate good code. So we need a more detailed specification. This is where you inject engineering knowledge and real-world constraints. For example, the optimal implementation should differ substantially depending on whether you target CPU, GPU, or distributed systems. You can think of this detailed specification as what you would otherwise write manually in `.md` files to give AI a real chance of generating the code you want. Using Lean keeps a tight connection between the top-level and detailed specifications.

The main motivation for working this way is that I can modify or extend the top-level specification and get deterministic feedback about whether those changes break core ideas in my code. Without Lean, I would have to manually review all `.md` files and check whether a change in what I'm building affects engineering decisions.

Recently at work, I had to write a set of tools for signed distance functions. Their mathematical description is simple, so this felt like a good test of the workflow. This post documents that experiment.

# Case Study: Constructive Solid Geometry

```leanInit post
```
```leanInit post'
```

```lean post
open EuclideanSpace Topology Metric NNReal
notation "ℝ^" n => EuclideanSpace ℝ (Fin n)
notation "ℝ≥0^" n => EuclideanSpace (ℝ≥0) (Fin n)
noncomputable section
open Classical
variable {n : ℕ}
```

Let's start with a bit of background on signed distance functions and constructive solid geometry.

Signed distance functions are a very useful tool for representing solid objects. For an object $`\Omega` we define the signed distance function $`\phi` as
$$`
\phi(x) = \begin{cases}
  -d(x, \partial \Omega) & \text{if } x \in \Omega \\
   d(x, \partial \Omega) & \text{if }\, x \notin \Omega\\
   0 & \text{if }\, x \in \partial \Omega.
\end{cases}
`
Many operations become easy with signed distance functions, such as collision detection. To determine whether a point is inside an object, we just check $`\phi(x) < 0`, and projecting the point to the surface is simply $`x^* := x - \phi(x) \cdot \nabla \phi(x)`.

To make this concrete, the following figure visualizes the signed distance function of a ball. Negative values are blue and positive values are orange, with black isolines every 0.2.

![polygon_vs_sdf](static/imgs/polygon_vs_sdf.png)

The figure contrasts the SDF representation with a polygonal representation of a ball (on the left), where exact collision detection is much harder and more computationally expensive. Also, a sphere can only be approximated by polygons. In the SDF representation, a ball is simply $`\phi(x) = \|x - c\| - r`, where $`c` is the center and $`r` is the radius.

There are many basic shapes for which we can write exact signed distance functions. I highly recommend [Inigo Quilez's article](https://iquilezles.org/articles/distfunctions/) on 3D SDFs. More complicated objects can be assembled from these primitives. For example, in games, complex polygonal models (like the one on the left) are often approximated for collision detection by a handful of simple shapes (on the right), with the resulting SDF visualized as above.

![compound_shape](static/imgs/polygon_vs_sdf.compound_shape.0001.png)


Creating more complex shapes out of simple ones is called [*Constructive Solid Geometry*](https://en.wikipedia.org/wiki/Constructive_solid_geometry) (CSG). Mathematically, it is just performing set operations such as union, intersection, or complement, which translates to $`\min`, $`\max`, and negation on SDFs.

$$`
\begin{align*}
A \cup B &= \{ x | \min(\phi_A(x), \phi_B(x)) \le 0 \} \\
A \cap B &= \{ x | \max(\phi_A(x), \phi_B(x)) \le 0 \} \\
A^c &= \{ x | - \phi_A(x) ≤ 0 \}
\end{align*}
`

At work, I had to write tools for these shapes. This roughly included:
- around 15 basic shapes
- CSG operations
- fast evaluation at many locations
- computing bounds on SDFs in a region
- pruning CSG expressions
- conversion to voxel representation
- computing derivatives in space and with respect to parameters

It is worth mentioning that lots of inspiration for this work on SDFs came from reading [Matt Keeter's articles](https://www.mattkeeter.com/).

All of these SDF operations have simple mathematical specifications, but implementation can get tedious. As a mathematician at heart, I enjoy the math and algorithms, while coding often feels like necessary overhead. That raised a question: can I write the specification in Lean and let AI generate the necessary C code?

The purpose of this post is to document that experiment. To capture both what went well and what failed, I wrote most of it as I progressed.


# Vibe coding based on Lean specification

The goal of this experiment is to vibe-code a C library that performs basic constructive solid geometry operations. The process is to first write the pure mathematical specification in Lean, then refine it until it can be translated to C by AI with minimal room for misinterpretation.

My experience with vibe coding is that writing clean, precise specifications in English is hard. Most of my work is in computational physics and computer graphics, where concise mathematical specifications are often possible, so I would rather write those than English prose.


The first step is to write down the formal definition of the signed distance function:
```lean post
def sdf (s : Set (ℝ^n)) (x : ℝ^n) : ℝ :=
  let dist := infDist x (frontier s)
  if x ∈ s then - dist else dist
```

Here, `infDist` is the distance between a point and a set, and `frontier` is the boundary of a set.

Keep in mind that this function is just a specification. Neither real numbers `ℝ` nor the generic set `Set (ℝ^n)` have direct executable representations. Functions like `infDist`, `frontier`, and `∈` are also pure specifications, not executable code.

When turning this into actual C code, we will replace `ℝ` with floating-point numbers, but what do we do with generic sets `Set (ℝ^n)`? We only have explicit exact SDF formulas for a handful of basic shapes.

For simplicity in this experiment, let's just work with balls and boxes. Let's define a type representing a basic shape:
```lean post
inductive BasicShape (n : ℕ) where
  | ball (center : ℝ^n) (radius : ℝ)
  | box (center : ℝ^n) (size : ℝ^n)
```
At the C level, we want to represent this as a tagged union, with these values at the leaves of the CSG tree.

What we need next is an interpretation of `BasicShape` as `Set (ℝ^n)` and explicit SDF formulas for them.

Because I already wrote too much code, let's ask AI to do that for us:

```
❯ Please define BasicShape.toSet turning basic shape to Set (ℝ^n) and
  BasicShape.sdf which provides an explicit formula for signed distance function.
```

Which generated:
```lean post
protected def BasicShape.toSet : BasicShape n → Set (ℝ^n)
  | .ball center radius =>
      Metric.closedBall center radius
  | .box center size    =>
      {x | ∀ i : Fin n, |x i - center i| ≤ size i / 2}

protected def BasicShape.sdf (x : ℝ^n) : BasicShape n → ℝ
  | .ball center radius => ‖x - center‖ - radius
  | .box center size =>
    let q : Fin n → ℝ :=
      fun i => |x i - center i| - size i / 2
    let outerDist :=
      Real.sqrt (∑ i : Fin n, (max (q i) 0) ^ 2)
    let maxQ : ℝ :=
      if h : (Finset.univ : Finset (Fin n)).Nonempty
      then Finset.sup' Finset.univ h q
      else 0
    outerDist + min maxQ 0
```

`BasicShape.toSet` looks good, but `BasicShape.sdf` is already getting complicated. We need a guarantee that `BasicShape.sdf` is actually equal to `sdf`.

Let's ask AI to do that:
```
❯ Can you please state that `sdf` is equal to `BasicShape.sdf` and try to prove it.
```

My hope was to get this theorem and its proof:
```lean post
theorem BasicShape.sdf_eq (s : BasicShape n) (x : ℝ^n) :
    sdf s.toSet x = s.sdf x := sorry
```
but it didn't. Instead, the AI burned through ~60k tokens and still did not produce reasonable working code. On the other hand, it pointed out that the theorem is not true for negative ball radii or negative box sizes. This is actually a common source of bugs. There are three possible interpretations of a ball with negative radius: an empty set, a ball using the absolute value of the radius, or the complement of a ball with positive radius.

We have two options: either litter `BasicShape.toSet` and `BasicShape.sdf` with absolute values, or forbid negative radii and sizes. Let's try the second approach:

```lean post
inductive BasicShape' (n : ℕ) where
  | ball (center : ℝ^n) (radius : ℝ≥0)
  | box (center : ℝ^n) (size : ℝ≥0^n)
```
Creating a ball with a negative radius will now fail:
-- ```lean post (name:=negball)
-- #check BasicShape'.ball !₂[0,0] (-1)
-- ```
-- ```leanOutput negball
-- BasicShape.ball !₂[0, 0] (-1) : BasicShape 2
-- ```

Rather than burning more tokens on a general coding model to prove `sdf s.toSet x = s.sdf x`, I tried [Harmonic's Aristotele](https://aristotle.harmonic.fun/). Sure enough, it is true. You can see the proof [here][proof1], except for the case `n = 0`, which we do not care about.

We are now done with basic shapes for now. Let's turn our attention to the CSG operations. For simplicity, let's consider only union, intersection, and rigid transformation. This can be represented with this inductive type:
```lean post
inductive CompoundShape (n : ℕ) where
  | basic     (s : BasicShape n)
  | transform (s : CompoundShape n)
              (A : Matrix.orthogonalGroup (Fin n) ℝ) (t : ℝ^n)
  | union     (a b : CompoundShape n)
  | intersect (a b : CompoundShape n)
```

Similar to `BasicShape`, we want to have `toSet` and `sdf` functions. The only caveat is that `min/max` do not precisely conserve SDFs, so we rather call it `csgSdf`.

```
❯ Please define `CompoundShape.toSet` and `CompoundShape.csgSdf` analogous to `BasicShape` functions. The `CompoundShape.csgSdf` is not a true SDF, it should turn union into `min` and intersection to `max` operation.
```


```lean post
def CompoundShape.toSet : CompoundShape n → Set (ℝ^n)
  | .basic s         => s.toSet
  | .transform s A t =>
    {y | WithLp.toLp 2 (A.val.transpose.mulVec (WithLp.ofLp (y - t))) ∈ s.toSet}
  | .union a b       => a.toSet ∪ b.toSet
  | .intersect a b   => a.toSet ∩ b.toSet

def CompoundShape.csgSdf (x : ℝ^n) : CompoundShape n → ℝ
  | .basic s         => s.sdf x
  | .transform s A t =>
    s.csgSdf (WithLp.toLp 2 (A.val.transpose.mulVec (WithLp.ofLp (x - t))))
  | .union a b       => min (a.csgSdf x) (b.csgSdf x)
  | .intersect a b   => max (a.csgSdf x) (b.csgSdf x)
```
This looks good, except for `WithLp.toLp 2`, which is an annoying quirk of mathlib's API around matrices and `ℝ^n`.


Now we can relate `sdf` and `csgSdf`. The CSG SDF underestimates the true SDF in absolute value.
```
theorem CompoundShape.abs_csgSdf_le_sdf (s : CompoundShape n) (x : ℝ^n) :
    |s.csgSdf x| ≤ |sdf s.toSet x| := sorry
```
Let's ask Aristotele... [oops, not true][proof2]. It is trivially false when `n = 0`, but more importantly it is false when `s` is empty. The counterexample was the intersection of two spheres centered at `2` and `-2` with radius `1`. In that case, `csgSdf` is nonzero, but the intersection is empty, and `infDist` has the quirk of returning zero for empty sets.

Maybe using `infDist` was not the best idea, since `infEDist` can return infinity while `infDist` cannot. I expected working with `ℝ∞` to add more hassle than value, so I left that for later. For now, we can add the condition `s.toSet ≠ ∅`. Then it should be correct, right Aristotele?



## Generating C Code

At this point, I thought I had enough to generate the first version of the C code. So I prompted:
```
❯ Can you please generate equivalent C program in a new `c` directory that is equivalent to the Lean code with n=3. The `BasicShape` should be a C tagged union and `CompoundShape` should be represented as a flat array in reverse Polish notation. Ignore functions manipulating `Set (ℝ^n)` as we have no runtime representation for `Set (ℝ^n)`.
```

My reasoning behind "flat array in reverse Polish notation" was that I did not want a heap-allocated tree structure. I wanted a flat representation that can also be ported to a GPU.

The AI generated working and readable C code, [csg.h][csgh] and [csg.c][csgc], but it was a bit more complicated than expected. Part of the response was
```
  Encoding of CompoundShape.transform: since transforms change the evaluation context (not just a value), they don't
  fit pure postfix on a single value stack. The encoding is:
  OP_PUSH_TRANSFORM(A,t)   ← pushes A^T·(cur−t) onto the point stack
    [sub-expression...]    ← evaluated with the new point on top
  OP_POP_TRANSFORM         ← restores the previous point
  This mirrors the Lean semantics s.csgSdf(Aᵀ·(x−t)) exactly.
```
I did not realize that transforms would prevent a pure postfix encoding. So I wanted to verify this encoding. Time for more Lean.


Prompt
```
❯ In LeanCSG/StackEval.lean, can you please define a flat representation of `CompoundShape n` that can be easily evaluated using a
  stack machine. Please provide:
  - flat representation of CompoundShape that can be evaluated using stack machine
  - equivalent of `CompoundShape.csgSdf` and all the constructors
  - equivalence between the flat representation and CompoundShape
  - state theorems that this equivalence preserves all the operations
```

... and after waiting a bit, I got really cool code. In just 154 lines, we get this flat representation:
```lean post
inductive Instr (n : ℕ) where
  | basic         (s : BasicShape n)
  | pushTransform (A : Matrix.orthogonalGroup (Fin n) ℝ) (t : ℝ^n)
  | popTransform
  | union
  | intersect

abbrev FlatShape (n : ℕ) := List (Instr n)
```
and the translation from `CompoundShape` to `FlatShape`:
```lean post
def CompoundShape.toFlat : CompoundShape n → FlatShape n
  | .basic s         => [.basic s]
  | .transform s A t => [.pushTransform A t] ++ s.toFlat ++ [.popTransform]
  | .union a b       => a.toFlat ++ b.toFlat ++ [.union]
  | .intersect a b   => a.toFlat ++ b.toFlat ++ [.intersect]
```
It even included the key theorem, fully proven, that flattening then evaluating a compound shape is equivalent to evaluating `csgSdf` directly:
```
theorem FlatShape.eval_toFlat (cs : CompoundShape n) (x : ℝ^n) :
    cs.toFlat.eval x = some (cs.csgSdf x) := ...
```
you can see the full code [here][proof3].

At this point, `FlatShape n` was much closer to the C data structure I wanted. So I asked:
```
❯ Can you please update the C code to mirror the Lean code in LeanCSG/StackEval.lean very closely. The Lean FlatShape should be the C CompoundShape.
```
It produced very nice C code that closely mirrors the Lean version: updated [csg.h][csgh2] and [csg.c][csgc2].

The main caveat is memory management. Lean does not express it directly, so the AI has no precise source to mirror. Right now, the generated code allocates sufficiently large buffers on the stack, which is good enough for my application.


That was enough for now. Next I validated that the program behaves as expected:
```
❯ Can you please write a simple program that will generate a simple picture visualizing the computed SDF? Visualize negative numbers in a blue gradient (blue at zero -> light blue as values decrease) and orange for positive numbers (red at zero -> orange as values increase). Then create a simple test shape doing a couple of transforms, unions and intersections. The picture should be a slice through the XY plane.
```
Here is the generated image, and it matches the instructions:
![generated_sdf](static/imgs/sdf.png)


# Summary

I want to summarize whether this workflow is actually feasible. I have to say I am surprised by how smooth it was overall. Early on, I was disappointed when AI failed to prove
```
theorem BasicShape.sdf_eq [Nontrivial (ℝ^n)] (s : BasicShape n) (x : ℝ^n) :
    _root_.sdf s.toSet x = s.sdf x := sorry
```
and
```
theorem CompoundShape.abs_csgSdf_le_sdf (s : CompoundShape n) (x : ℝ^n) :
    |s.csgSdf x| ≤ |sdf s.toSet x| := sorry
```
Harmonic's Aristotele is still running, but the progress bar appears stuck, so the statement may simply be wrong due to an edge case I missed.

After that, it was smooth sailing. The AI generated C code on the first try, but it was more complicated than I wanted to validate manually. So I asked it to first mirror the desired stack-based implementation in Lean and prove it equivalent to the straightforward recursive version. Done in one shot. Updating the C code was another one-shot task, and with Lean as a precise template, there was very little room for the AI to drift.

The main thing to watch is memory management, because it is not explicit in Lean. The current C implementation effectively fixes the maximum number of nodes in the CSG tree, so everything is stack-allocated and there is no heap allocation. This works for my use case but may not work in general. More experiments are needed to see whether this becomes a problem.

Overall, I am very happy with this experiment. There are many more SDF tasks I want to explore with the same workflow.
