# Collision Entropy of a Boolean Function

This note summarises the definition of **collision entropy** for a
single Boolean function and shows how it is formalised in Lean.  The
implementation can be found in `pnp/Pnp/Collentropy.lean`.

## Definition

Given `f : Point n → Bool`, write `p` for the probability that `f` is
`true` under the uniform distribution on `Point n`.  The *collision
probability* is
```
collProbFun f = p * p + (1 - p) * (1 - p).
```
The *collision entropy* is measured in bits via
```
H₂Fun f = -log₂ (collProbFun f).
```
Constant functions have collision probability `1`, hence zero collision
entropy.

## Lean formalisation

The file defines these notions using the existing `prob` function from
`BoolFunc.lean`:

```lean
@[simp] def collProbFun (f : BFunc n) : ℝ :=
  let p := prob f
  p * p + (1 - p) * (1 - p)

@[simp] def H₂Fun (f : BFunc n) : ℝ :=
  -Real.logb 2 (collProbFun f)
```

Simple lemmas establish that constant functions have zero collision
entropy:
```lean
lemma H₂Fun_const_false :
    H₂Fun (fun _ => false : BFunc n) = 0 := by
  simp
```

Additional lemmas bound the range of `collProbFun` and `H₂Fun`:
```lean
lemma prob_nonneg (f : BFunc n) : 0 ≤ prob f
lemma prob_le_one (f : BFunc n) : prob f ≤ 1
lemma collProbFun_ge_half (f : BFunc n) :
  (1 / 2 : ℝ) ≤ collProbFun f
lemma collProbFun_le_one (f : BFunc n) :
  collProbFun f ≤ 1
lemma H₂Fun_nonneg (f : BFunc n) : 0 ≤ H₂Fun f
lemma H₂Fun_le_one (f : BFunc n) : H₂Fun f ≤ 1
```
In particular, a function with output probability `1/2` has maximal
collision entropy `1`:
```lean
lemma H₂Fun_prob_half (f : BFunc n) (h : prob f = 1 / 2) :
  H₂Fun f = 1
```

These facts provide the basic groundwork for further entropy arguments.

## Building

To compile the `collentropy` module run:
```bash
lake exe cache get
lake build Pnp.Collentropy
```
The first command downloads pre-built Mathlib binaries. If the download fails or is skipped, the build step may take a long time as it compiles Mathlib from source.

After downloading the cache, running `lake build` should complete without errors, though the compilation can be slow on first run.
