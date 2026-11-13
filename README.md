# Grothendieck–Riemann–Roch

Let $`k`$ be a field and $`f\colon X \to Y`$ a projective morphism of smooth quasi-projective varieties over $`k`$. For every $`\alpha \in K_0(X)`$, in $`A^*(Y)_{\mathbb Q}`$:

```math
\mathrm{ch}(f_!\,\alpha)\cdot\mathrm{td}(T_Y) \;=\; f_*\big(\mathrm{ch}(\alpha)\cdot\mathrm{td}(T_X)\big).
```

**How it is read in Lean.** $`X`$ and $`Y`$ are smooth, separated schemes of finite type over $`k`$ (every smooth quasi-projective variety is one; integrality and quasi-projectivity are not used). $`f`$ is projective in the sense that it factors as a closed immersion $`X \to \mathbb P^n_Y`$ followed by the projection $`\mathbb P^n_Y \to Y`$. $`K_0(X)`$ is the Grothendieck group of coherent sheaves and $`f_![\mathcal F]=\sum_i(-1)^i[R^if_*\mathcal F]`$. Both sides are capped with the fundamental class $`[Y]`$, which identifies $`A^*(Y)_{\mathbb Q}`$ with $`CH_*(Y)_{\mathbb Q}`$ for smooth $`Y`$, and $`f_*`$ is proper pushforward of cycles. So the statement is

```math
f_*\big((\mathrm{ch}(\alpha)\cdot\mathrm{td}(T_X))\cap[X]\big) \;=\; (\mathrm{ch}(f_!\,\alpha)\cdot\mathrm{td}(T_Y))\cap[Y]\quad\text{in } CH_*(Y)_{\mathbb Q},
```

that is, $`f_*\,\tau_X(\alpha)=\tau_Y(f_!\,\alpha)`$ for the Riemann–Roch map $`\tau_X(\alpha)=(\mathrm{ch}(\alpha)\cdot\mathrm{td}(T_X))\cap[X]`$.

Under the hypotheses:
- $`k`$ is a field.
- $`X`$ and $`Y`$ are smooth, separated and of finite type over $`k`$ (in particular: smooth quasi-projective varieties).
- $`f`$ factors as a closed immersion $`X \to \mathbb P^n_Y`$ followed by the projection to $`Y`$.

**Status: proved in Lean**, with no `sorry` and no axioms beyond Lean's standard three. Hirzebruch–Riemann–Roch, the case $`Y=\mathrm{Spec}\,k`$, is proved as `GRR.hirzebruch_riemann_roch`, with the same three axioms.

## What Lean checked

```lean
theorem GRR.grothendieck_riemann_roch :
    ∀ (k : Type u_1) [inst : Field k] {X Y : AlgebraicGeometry.Scheme}
      (sX : X ⟶ AlgebraicGeometry.Spec ↧k) (sY : Y ⟶ AlgebraicGeometry.Spec ↧k) [inst_1 : GRR.IsSmoothFT k sX]
      [inst_2 : GRR.IsSmoothFT k sY] (f : X ⟶ Y) (hf : CategoryTheory.CategoryStruct.comp f sY = sX)
      (hproj : AlgebraicGeometry.IsProjectiveMorphism f) (α : AlgebraicGeometry.CoherentKZero X),
      (Stacks.Chow.rationalProperChowPushforward (Stacks.Chow.fieldChowSituation k) sX sY hf) ((GRR.tau k sX) α) =
        (GRR.tau k sY) ((GRR.pushforwardK f) α)
```

Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Check it yourself

```sh
./verify
```

It needs Lean (elan) and python3, downloads Mathlib's cache (about 7 GB) and builds the project. It also builds from source the part of Stacks this proof imports, about 17,500 modules, which takes hours. It prints a verdict with the theorem's axioms and writes `verification.json`: every declaration behind a Formal card, with its axioms and signature.

Memory: with Lake's default parallelism that build ran a 24 GB Mac out of memory. `verify` therefore runs each Lean process on 3 threads; if you have more memory, run `LEAN_NUM_THREADS=8 ./verify`.

## How it was made

| | |
|---|---|
| Made on | [grothendieck](https://grothendieck.io) |
| Platform version | 0.2.32 |
| Lean | leanprover/lean4:v4.35.0, Mathlib `56a005855ea1` |
| Model | Fable 5.2, claude, effort max |
| Helpers | 34 on Opus 5.5, at most four at once |
| Working time | 6 h 23 min |
| Independent checks | 106 statements read against Lean by a separate agent; 80 steps attacked by one |

`map.json` holds the whole map: every statement, written proof, reading and attack.

## What it rests on

- **Stacks**, at commit [`c496df0`](https://github.com/AxiomMath/Stacks/tree/c496df0d9beea9deaeabcea8492605f9a0a2313b): Chow groups, Chern classes, the Chern character, Gysin maps, deformation to the normal cone. Sixteen of its results are cited on the map (the cards of type `cited` in `map.json`) and taken as Stacks proves them.
- Two of those results are restated here, because the Stacks modules that prove them were not compiled for this run: Stacks 0FF4, the Gysin map of a flat morphism is flat pullback, in `GRR/ProjectionGen.lean` (from `WeilCohomology/Concrete/ProjectiveBundleRationalChow`), and flat pullback of the fundamental class of a smooth scheme, in `GRR/ProjectionTau.lean` (from `WeilCohomology/Concrete/ProjectiveBundleDiagonal`). Both are marked in the source.
- No result of Stacks' own Riemann–Roch modules is used: a dependency walk from the two theorems reaches none of `Variety/Curve/RiemannRoch`, `RiemannRochZeroScheme` or `NumericalIntersections/AsymptoticRiemannRoch`.
- The route is Fulton, *Intersection Theory*, chapter 15.

## Licence

Apache-2.0, as Mathlib and Stacks are; see `LICENSE` and `NOTICE`.
