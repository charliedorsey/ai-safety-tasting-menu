# Jacobi — actual programming with Lean

This is the **centerpiece** of the AI Safety Tasting Menu. The Lean 4 files here implement a real rational spectral-distance producer, an independently usable certificate checker and formal soundness claims. This is an executable program, not a proposal to someday write one.

## Follow the executable pieces

1. [AsterPublicProducer.lean](LEAN_PROJECT/AsterPublicProducer.lean) defines `produceNearest?`, which takes rational matrix coefficients, dimension, target and tolerance. Its `produceNearest?_complete` and `produceNearest?_sound` theorems characterize valid production under precise input contracts.
2. [AsterTotalRadialProducer.lean](LEAN_PROJECT/AsterTotalRadialProducer.lean) carries out rational singularity detection, finds a spectral bracket and refines a witness. It contains a termination argument, while explicitly noting that the outer search does not have a uniform numeric bound on total candidate iterations.
3. [AsterAccuracyCheckR0001.lean](LEAN_PROJECT/AsterAccuracyCheckR0001.lean) defines `checkAccurate`. Its theorem `accurate_implies_spectral_bounds` links checker acceptance to the stated real spectral bounds and tolerance.
4. [AsterFastProducerR0001.lean](LEAN_PROJECT/AsterFastProducerR0001.lean) connects rational refinement fuel and checked witness production. A fuel bound is not, by itself, a measured whole-program runtime bound.
5. [AsterEmitted3x3R0001.lean](LEAN_PROJECT/AsterEmitted3x3R0001.lean) evaluates the actual producer on a concrete three-site example: diagonal [0,0,0], physical hops [1,1], target 7/5 and tolerance 1/32.
6. [AsterLiteralIndependentCheckR0001.lean](LEAN_PROJECT/AsterLiteralIndependentCheckR0001.lean) **imports the checker, not the producer**. It checks the literal emitted witness using Lean and proves `emitted_literal_accepted` and `emitted_literal_spectral_bounds`, with explicit spectral-distance bounds 7/3520 and 1179/56320.

This demonstrates a valuable asymmetry: complex certificate search can be separated from comparatively narrow, source-independent checking of a **given** certificate. It is an implemented Lean example, not an assertion that every downstream runtime is formally secure.

**Exact seam:** the producer represents two physical off-diagonal hops with zero padding beyond the matrix; the literal checker uses a constant-one extension. Both denote the same physical three-site matrix. A general finite-array API should standardize padding or prove extension invariance before claiming unrestricted interoperation. This does not negate the verified literal example.

Read the [R0005 manuscript](MANUSCRIPT_AND_REFERENCE/ASTER_JACOBI_WORKING_MANUSCRIPT_R0005.pdf) and [complete flagship source](README.md). No claim is made that every manuscript section is independently Lean-verified or that a new dependency-clean cold replay occurred during this tasting-menu build.
