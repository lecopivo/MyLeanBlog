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

```leanInit post
```
```leanInit post'
```

```lean post
open EuclideanSpace Topology Metric NNReal
notation "ℝ^" n => EuclideanSpace ℝ (Fin n)
notation "ℝ≥0^" n => EuclideanSpace (ℝ≥0) (Fin n)
notation "ℝ∞" => EReal
instance : Coe (Set (ℝ^1)) (Set ℝ) := ⟨fun s x => s (.single 0 x)⟩
noncomputable section
open Classical
variable {n : ℕ}
```


I'm a computer graphics programmer specializing in physics simulation and computational geometry. As a trained mathematician, I love the math, but I've always seen the coding part as a necessary evil. About five years ago, I discovered interactive proof assistants and realized they could transform how I write code: start from a precise mathematical formulation and interactively refine it into something executable. That idea became SciLean, a Lean 4 library I spent four years building. Unfortunatelly, the project is effectively dead now. It never gained meaningful traction, and I ran out of steam. It didn't address the problems Lean users actually had, and the likely target audience had little motivation to leave mature ecosystems like C++, Python, or Julia.

The core idea, writing mathematical specification and deriving code from it, still strikes me as sound and worth pursuing. What was fundamentally flawed was SciLean's approach of providing a fixed set of transformation rules. The design space is too large, and implementing a practically useful subset is nearly impossible.

LLMs change the calculus here. The workflow I now have in mind looks like this:

1. Hand-write a precise mathematical specification in Lean.
2. Transform that specification into a more detailed Lean spec or implementation, tied back to the original with proofs.
3. Generate target-language code from the detailed specification.

Step one captures what you actually want to implement, but at too coarse a level for AI to generate good code directly. Step two is where you inject engineering knowledge and real-world constraints. For examples, optimal implementation differ substantially between CPU, GPU, and distributed targets. You can think of the detailed specification as what you'd otherwise write in `.md` files to give AI a real chance of producing the code you want, but keeping it in Lean maintains a tight, verifiable connection to the top-level specification. The key payoff: when you modify or extend the top-level specification, Lean gives you deterministic feedback about whether those changes break anything downstream. Without it, you'd have to manually audit all your prose documentation.

Recently at work I had to write a set of tools for signed distance functions. Their mathematics is clean and well-understood, which made this a natural first test of the workflow. This post documents that experiment.

# Case Study: Constructive Solid Geometry

A signed distance function (SDF) represents a solid object $`\Omega` by encoding both membership and distance to the boundary in a single scalar field:

$$`
\phi(x) = \begin{cases}
  -d(x, \partial \Omega) & \text{if } x \in \Omega \\
   d(x, \partial \Omega) & \text{if }\, x \notin \Omega\\
   0 & \text{if }\, x \in \partial \Omega.
\end{cases}
`

This makes many operations elegant. Checking whether a point is inside an object reduces to $`\phi(x) < 0`, and projecting to the surface is $`x^* := x - \phi(x) \cdot \nabla \phi(x)`.

The figure below visualizes the SDF of a ball, negative values in blue, positive in orange, with black isolines every 0.2. Contrast it with the polygonal representation on the left, where exact collision detection is far harder and more expensive. The SDF for a sphere is simply $`\phi(x) = \|x - c\| - r`.

![polygon_vs_sdf](static/imgs/polygon_vs_sdf.png)

I highly recommend [Inigo Quilez's article](https://iquilezles.org/articles/distfunctions/) for a catalogue of exact SDFs for common 3D shapes. More complex objects are assembled from these primitives. In games, a detailed polygonal model is often approximated for collision detection by a handful of simple shapes.

![compound_shape](static/imgs/polygon_vs_sdf.compound_shape.0001.png)

Combining shapes through set operations is called [*Constructive Solid Geometry*](https://en.wikipedia.org/wiki/Constructive_solid_geometry) (CSG). It translates cleanly to arithmetic on SDFs:

$$`
\begin{align*}
A \cup B &= \{ x \mid \min(\phi_A(x), \phi_B(x)) \le 0 \} \\
A \cap B &= \{ x \mid \max(\phi_A(x), \phi_B(x)) \le 0 \} \\
A^c &= \{ x \mid -\phi_A(x) \le 0 \}
\end{align*}
`

The tools I has to implement at work were roughly:
  * around 15 basic shapes
  * CSG operations
  * fast evaluation at many locations
  * bounds on SDFs over a region
  * pruning of CSG expressions
  * conversion to voxel representation
  * derivatives with respect to space and shape parameters

The math and algorithms are enjoyable; the implementation is the grind. That raised the question: can I write the specification in Lean and let AI generate the C code?


# Vibe coding based on a Lean specification

The goal is to vibe-code a C library for basic CSG operations. The process: write the pure mathematical specification in Lean, refine it until it can be translated to C by AI with minimal ambiguity.

The formal definition of the SDF is a direct transcription of the mathematical one:

```lean post
def sdf (s : Set (ℝ^n)) (x : ℝ^n) : ℝ :=
  let dist := infDist x (frontier s)
  if x ∈ s then - dist else dist
```

Here `infDist` is the distance from a point to a set and `frontier` is the boundary. Keep in mind that this function is pure specification - `ℝ`, `Set (ℝ^n)`, `infDist`, and `frontier` have no executable representations.

When generating C, `ℝ` naturally becomes a float; what do we do with generic sets? For this experiment, we restrict to balls and boxes:

```lean post
inductive BasicShape (n : ℕ) where
  | ball (center : ℝ^n) (radius : ℝ)
  | box (center : ℝ^n) (size : ℝ^n)
```

At the C level this becomes a tagged union. We need an interpretation of `BasicShape` as `Set (ℝ^n)` and explicit SDF formulas. I asked AI to provide both:

```
❯ Please define BasicShape.toSet turning basic shape to Set (ℝ^n) and
  BasicShape.sdf which provides an explicit formula for signed distance function.
```

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

`BasicShape.toSet` looks right. `BasicShape.sdf` is already non-trivial, so we need a proof it agrees with `sdf`. I asked AI:

```
❯ Can you please state that `sdf` is equal to `BasicShape.sdf` and try to prove it.
```

```lean post
theorem BasicShape.sdf_eq (s : BasicShape n) (x : ℝ^n) :
    sdf s.toSet x = s.sdf x := sorry
```

The AI burned through roughly 60k tokens without a result, but it did flag something useful: the theorem is false for negative radii or box sizes, which is a genuine source of bugs. A ball with negative radius is ambiguous: is it empty, a ball of absolute radius, or the complement? Rather than cluttering the definitions with absolute values, let's forbid the invalid inputs:

```lean post
inductive BasicShape' (n : ℕ) where
  | ball (center : ℝ^n) (radius : ℝ≥0)
  | box (center : ℝ^n) (size : ℝ≥0^n)
```

With that fixed, I tried [Harmonic's Aristotele](https://aristotle.harmonic.fun/), which confirmed the theorem holds. You can see the proof [here][proof1], modulo the degenerate `n = 0` case we don't care about.

Now for CSG. We model union, intersection, and rigid transformation:

```lean post
inductive CompoundShape (n : ℕ) where
  | basic     (s : BasicShape n)
  | transform (s : CompoundShape n)
              (A : Matrix.orthogonalGroup (Fin n) ℝ) (t : ℝ^n)
  | union     (a b : CompoundShape n)
  | intersect (a b : CompoundShape n)
```

Because `min`/`max` don't exactly preserve distance, the CSG version of the SDF gets its own name, `csgSdf`:

```
❯ Please define `CompoundShape.toSet` and `CompoundShape.csgSdf` analogous to `BasicShape` functions. The `CompoundShape.csgSdf` is not a true SDF — it should turn union into `min` and intersection into `max`.
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

The `WithLp.toLp 2` noise is an unfortunate artifact of how Mathlib wraps `ℝ^n`. The semantics are correct.

The key property we want is that `csgSdf` underestimates the true signed distance:

```lean post
theorem CompoundShape.abs_csgSdf_le_sdf
    (s : CompoundShape n) (x : ℝ^n) :
    |s.csgSdf x| ≤ |sdf s.toSet x| := sorry
```

Aristotele found a [counterexample][proof2]: the intersection of two non-overlapping spheres centered at `2` and `-2` with radius `1`. The intersection is empty, so `sdf` returns zero (since `infDist` returns zero for empty sets), but `csgSdf` is nonzero. Adding `s.toSet ≠ ∅` as a hypothesis should fix it. Unfortunatelly, Aristotele ran out of context on this one. Likely because it had to reprove `BasicShape.sdf_eq`. I will leave the proof of this theorem for another day.


## Generating C Code

With the specification in reasonable shape, I asked for C code:

```
❯ Can you please generate equivalent C code in a new `c` directory for n=3. `BasicShape` should be a C tagged union and `CompoundShape` should be represented as a flat array in reverse Polish notation. Ignore functions manipulating `Set (ℝ^n)`.
```

I wanted a flat array rather than a heap-allocated tree so the representation could port cleanly to a GPU. The AI produced working, readable C ([csg.h][csgh], [csg.c][csgc]), but noted a subtlety I'd missed:

```
  Encoding of CompoundShape.transform: since transforms change the evaluation context
  (not just a value), they don't fit pure postfix on a single value stack. The encoding is:
  OP_PUSH_TRANSFORM(A,t)   ← pushes A^T·(cur−t) onto the point stack
    [sub-expression...]    ← evaluated with the new point on top
  OP_POP_TRANSFORM         ← restores the previous point
  This mirrors the Lean semantics s.csgSdf(Aᵀ·(x−t)) exactly.
```

Transforms require a separate point stack, postfix isn't quite sufficient. Before trusting the C code, I wanted this encoding verified in Lean itself:

```
❯ In LeanCSG/StackEval.lean, please define a flat representation of `CompoundShape n` evaluable by a stack machine, along with the equivalent of `CompoundShape.csgSdf`, all the constructors, and a proof that flattening then evaluating is equivalent to direct recursive evaluation.
```

The AI returned the key encoding of `CompoundShape` as `FlatShape`:

```lean post
inductive Instr (n : ℕ) where
  | basic         (s : BasicShape n)
  | pushTransform (A : Matrix.orthogonalGroup (Fin n) ℝ) (t : ℝ^n)
  | popTransform
  | union
  | intersect

abbrev FlatShape (n : ℕ) := List (Instr n)
```

With the function converting one to the other:

```lean post
def CompoundShape.toFlat : CompoundShape n → FlatShape n
  | .basic s         => [.basic s]
  | .transform s A t => [.pushTransform A t] ++ s.toFlat ++ [.popTransform]
  | .union a b       => a.toFlat ++ b.toFlat ++ [.union]
  | .intersect a b   => a.toFlat ++ b.toFlat ++ [.intersect]
```

And the key theorem, fully proven:

```
theorem FlatShape.eval_toFlat (cs : CompoundShape n) (x : ℝ^n) :
    cs.toFlat.eval x = some (cs.csgSdf x) := ...
```

All in just [~200 lines of code][proof3] on the first try. With `FlatShape` as a precise template, updating the C code was a one-shot task, producing [csg.h][csgh2] and [csg.c][csgc2] that mirror the Lean version closely.

The one important gap is memory management, Lean doesn't express it, so the AI had no template to follow. The current implementation pre-allocates fixed-size stack buffers, which works for my use case but may not generalize.

I asked for a quick visual validation:

```
❯ Please write a simple program that visualizes the computed SDF as a slice through the XY plane. Negative values in blue (blue at zero, lighter as values decrease), positive in orange (red at zero, lighter as values increase). Use a test shape with a few transforms, unions, and intersections.
```

![generated_sdf](static/imgs/sdf.png)

Looks right, I'm happy!


# Summary

This workflow is more feasible than I expected. The early stumble, AI failing to prove `BasicShape.sdf_eq`, turned out to be useful, since it surfaced a real correctness issue with negative dimensions. Aristotele handled that theorem where the general model couldn't.

After that it was smooth sailing. AI generated the initial C code in one shot, but the transform encoding was complex enough that I wanted independent verification before trusting it. Asking for a Lean formalization of the stack machine first, then updating the C to mirror it, gave me exactly that, with very little room for the AI to drift, because the template was precise and machine-checked.

# What's Next

I defenitelly want to continue this experiment as it was a success in my view. Here is a rough plan for follow up blog posts.

## Fast batch evaluation

When evaluating `ComboundShape.csgSdf` for many points at a time we can propagate the loop over all points to the inner most part of the code. This corresponds to this Lean code:

```lean post
def BasicShape.sdfBatch (xs : List (ℝ^n)) : BasicShape n → List ℝ
  | .ball c r => xs.map (ball c r).sdf
  | .box c s => xs.map (box c s).sdf

def CompoundShape.csgSdfBatch (xs : List (ℝ^n)) : CompoundShape n → List ℝ
  | .basic s         => s.sdfBatch xs
  | .transform s A t => xs.map (transform s A t).csgSdf
  | .union a b       => xs.map (fun x => min (a.csgSdf x) (b.csgSdf x))
  | .intersect a b   => xs.map (fun x => max (a.csgSdf x) (b.csgSdf x))
```

When done correctly, the C compiler can vectorize the loop over the points achievnig 4~8x speedups. Conceptually, this is a very simple code transformation but very annoying to write as you have to write down most of your code in slightly different form.

## Bounding SDF

Collision detection can be stated as a bounding problem. Given a shape `s` does it colide with a region `r`? If we know a bound `b` on the values `sdf` attains over the region `r`, i.e. `s.sdf(r) ⊆ b`, we know that collision definitely happened when `b ≤ 0` and definitelly did not happend when `b ≥ 0`.

Mathematically, we are looking for the function:
```lean post
def CompoundShape.outputBound
    (s : CompoundShape n) (inputBound : BasicShape n) :
    BasicShape 1 := sorry
```

That satisfies:
```lean post
theorem CompoundShape.set_image_csgSdf_subset_outputBound
     (s : CompoundShape n) (inputBound : BasicShape n) :
     Set.image s.csgSdf inputBound.toSet
     ⊆
     (s.outputBound inputBound).toSet := sorry
```

## Pruning CSG tree

When doing hierarchical spatial search it is very usefull to progressivelly simplify the CSG tree.

Mathematically, we look for the function:
```lean post
def CompoundShape.pruneIn
    (s : CompoundShape n) (region : BasicShape n) :
    CompoundShape n := sorry
```

That satisfies:
```lean post
theorem CompoundShape.pruneIn_eq
    (s : CompoundShape n) (region : BasicShape n) :
    ∀ x ∈ region.toSet,
      (s.pruneIn r).csgSdf x = s.csgSdf x:= sorry
```





[proof1]: https://live.lean-lang.org/#project=mathlib-v4.24.0&codez=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

[proof2]: https://live.lean-lang.org/#project=mathlib-v4.24.0&codez=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


[csgh]: https://github.com/lecopivo/LeanCSG/blob/97660e7ab097d6d4a6d2371fbe441fb7e77f9e5c/c/csg.h
[csgc]: https://github.com/lecopivo/LeanCSG/blob/97660e7ab097d6d4a6d2371fbe441fb7e77f9e5c/c/csg.c
[proof3]: https://github.com/lecopivo/LeanCSG/blob/7055f3f43e07eabebb9331cdaa0b4d16828cad28/LeanCSG/StackEval.lean#L165
[csgh2]: https://github.com/lecopivo/LeanCSG/blob/677d17747706caf308ca3fcb9055b12b22bd6602/c/csg.h
[csgc2]: https://github.com/lecopivo/LeanCSG/blob/677d17747706caf308ca3fcb9055b12b22bd6602/c/csg.c
