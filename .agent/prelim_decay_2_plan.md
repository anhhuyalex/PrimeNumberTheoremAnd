# Implementation Plan for `prelim_decay_2`

## Goal
Prove that for $\psi:\mathbb{R}\to\mathbb{C}$ that is integrable and of bounded variation:
$$\|\hat{\psi}(u)\| \leq \frac{V(\psi)}{2\pi|u|}$$
where $V(\psi) = (\text{eVariationOn } \psi \text{ Set.univ}).toReal$

## Mathematical Outline (from CONTRIBUTING.md)

The proof follows these steps:

1. **Start from Fourier transform definition**: $\hat{\psi}(u) = \int_\mathbb{R} \psi(t) e(-tu) dt$

2. **Differentiate the exponential**: $e(-tu) = \frac{1}{-2\pi i u} \frac{d}{dt}e(-tu)$

3. **Apply Lebesgue-Stieltjes integration by parts**:
   $$2\pi i u \hat{\psi}(u) = \int_\mathbb{R} e(-tu) d\psi(t)$$

4. **Take norms**: $2\pi|u| |\hat{\psi}(u)| = |\int_\mathbb{R} e(-tu) d\psi(t)|$

5. **Triangle inequality**: $|\int_\mathbb{R} e(-tu) d\psi(t)| \leq \int_\mathbb{R} |d\psi(t)| = V(\psi)$

6. **Final rearrangement**: Divide by $2\pi|u|$

## Lean Proof Structure

```lean
theorem prelim_decay_2 (ψ : ℝ → ℂ) (hψ : Integrable ψ) (hvar : BoundedVariationOn ψ Set.univ)
    (u : ℝ) (hu : u ≠ 0) :
    ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ (eVariationOn ψ Set.univ).toReal / (2 * π * ‖u‖) := by
  -- Step 1: Express the goal after dividing by 2π|u|
  rw [le_div_iff₀]

  -- Step 2: Show that 2π|u| * ‖𝓕 ψ u‖ = ‖2π * u * I * 𝓕 ψ u‖
  have key_identity : 2 * π * ‖u‖ * ‖𝓕 ψ u‖ = ‖2 * π * u * I * 𝓕 ψ u‖ := by
    sorry -- norm algebra
  rw [key_identity]

  -- Step 3: Apply integration by parts lemma to get
  -- 2π i u 𝓕 ψ u = ∫ e(-tu) d ψ(t)
  have ibp : 2 * π * u * I * 𝓕 ψ u =
      sorry -- integral with respect to Stieltjes measure dψ
    := by
    sorry -- This is the core Lebesgue-Stieltjes integration by parts

  rw [ibp]

  -- Step 4: Use triangle inequality for Stieltjes integrals
  have triangle : ‖sorry‖ ≤ sorry := by
    sorry -- Apply bound |∫ e(-tu) dψ| ≤ ∫ |dψ| = eVariationOn

  exact triangle

  -- Positivity for division
  · positivity
```

## Required Lemmas to Find or Prove

1. **Integration by parts for Fourier transform with bounded variation**
   - Need: Something like `fourierIntegral_eq_stieltjes_integral`
   - This should express $2\pi i u \hat{\psi}(u)$ as a Stieltjes integral against $d\psi$

2. **Norm of complex scalar multiplication**
   - Need: Conversion between $2\pi|u| \cdot |\hat{\psi}(u)|$ and $|2\pi u i \hat{\psi}(u)|$
   - Should be in `Complex.norm_*` lemmas

3. **Triangle inequality for Stieltjes integrals**
   - Need: Bound for integrals with respect to variation measure
   - Likely in `Mathlib.Topology.EMetricSpace.BoundedVariation`
   - Connection between eVariationOn and integral bounds

4. **Unit modulus of exponential**
   - Already available: Complex exponentials on unit circle have norm 1
   - Used to show $|e(-tu)| = 1$

## Search Strategy

1. Search for existing Fourier integration by parts lemmas
2. Search for Stieltjes integration and bounded variation in mathlib
3. Look for lemmas connecting `eVariationOn` to integral bounds
4. Check if there's a Fourier transform derivative formula we can use

## Notes

- The key challenge is Step 3: expressing the Fourier transform via Lebesgue-Stieltjes integration
- We might need to first prove a helper lemma about the derivative of the Fourier transform
- Alternative: Use weak derivatives and duality
- The bounded variation hypothesis `BoundedVariationOn ψ Set.univ` means `eVariationOn ψ Set.univ ≠ ∞`, which allows us to treat ψ as defining a finite signed measure
