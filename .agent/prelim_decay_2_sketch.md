# Proof Sketch for `prelim_decay_2`

## Current Structure

The proof now uses a clean `calc` chain that mirrors the mathematical steps from CONTRIBUTING.md:

```lean
calc ‖𝓕 ψ u‖ * (2 * π * ‖u‖)
    = ‖2 * π * (u : ℂ) * I * 𝓕 ψ u‖     -- Step 1: Norm algebra
    = <Stieltjes integral>              -- Step 2: Integration by parts
    ≤ <variation bound>                 -- Step 3: Triangle inequality
    = (eVariationOn ψ Set.univ).toReal  -- Step 4: Unit modulus
```

## What Each `sorry` Represents

### Step 1 (Line 334): Norm Algebra
**Current goal:** Show `‖𝓕 ψ u‖ * (2 * π * ‖u‖) = ‖2 * π * (u : ℂ) * I * 𝓕 ψ u‖`

**What's needed:**
- Use `norm_mul` repeatedly to decompose the RHS
- Show `‖(2 : ℂ)‖ = 2`, `‖(π : ℂ)‖ = π`, `‖(u : ℂ)‖ = ‖u‖`, `‖I‖ = 1`
- Rearrange using commutativity and the fact that `|I| = 1`

**Lemmas to find:**
- `Complex.norm_ofReal` or `Complex.abs_ofReal`
- `Complex.norm_I` or `Complex.abs_I`
- Norm preservation under real→complex coercion

---

### Step 2 (Line 339): Integration by Parts
**Current goal:** Show `‖2 * π * (u : ℂ) * I * 𝓕 ψ u‖ = <some integral expression>`

**What's needed:**
This is the core lemma. The mathematical identity is:
$$2\pi i u \cdot \hat{\psi}(u) = \int_\mathbb{R} e(-tu) \, d\psi(t)$$

In Lean, the RHS should be something like:
```lean
∫ t, fourierChar[ℝ] (-(t * u)) • <Stieltjes_differential> ∂<signed_measure_from_ψ>
```

**Challenges:**
1. Need to construct a signed measure from `BoundedVariationOn ψ`
2. Need an integration by parts formula for Fourier transforms
3. Mathlib may not have this exact lemma - might need to prove it

**Possible approaches:**
- Look for `stieltjesFunction` or similar in mathlib
- Check if there's a signed measure construction from functions of bounded variation
- May need to prove this as a separate helper lemma first

---

### Step 3 (Line 346): Triangle Inequality for Stieltjes Integrals
**Current goal:** Show the Stieltjes integral `≤ <some expression>`

**What's needed:**
$$\left|\int_\mathbb{R} e(-tu) \, d\psi(t)\right| \leq \int_\mathbb{R} |e(-tu)| \, d|\psi|(t)$$

This is the triangle inequality for integrals with respect to signed measures.

**Lemmas to find:**
- Triangle inequality for integrals over signed measures
- Likely in `MeasureTheory.Integral` or related to `VectorMeasure`

---

### Step 4 (Line 351): Unit Modulus Evaluation
**Current goal:** Show `∫ |e(-tu)| d|ψ|(t) = (eVariationOn ψ Set.univ).toReal`

**What's needed:**
Since `|e(-tu)| = 1` for all `t`, we have:
$$\int_\mathbb{R} 1 \, d|\psi|(t) = V(\psi)$$

This connects the integral over the variation measure to `eVariationOn`.

**Lemmas to find:**
- Relationship between variation measure and `eVariationOn`
- Integral of constant 1 over variation measure equals total variation
- Likely in `Mathlib.Topology.EMetricSpace.BoundedVariation`

---

## Summary

The proof skeleton now compiles with 4 `sorry`s, each representing a concrete mathematical step. The main challenge is **Step 2** (integration by parts), which may require constructing infrastructure that doesn't exist in mathlib yet.

The other steps are more straightforward applications of existing norm and measure theory lemmas.
