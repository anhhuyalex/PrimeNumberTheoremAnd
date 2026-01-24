# Contributing to the PNT+ Project

Thank you for your interest in contributing to the PNT+ Project!
This guide provides detailed instructions on how to effectively and efficiently contribute to the project.

## Project Coordination

The project is managed using a [GitHub project dashboard](https://github.com/users/AlexKontorovich/projects/1), which tracks tasks through various stages, from assignment to completion.

## How to Contribute

Contributions to the project are made through GitHub pull requests (PRs) from forks. PRs correspond to specific tasks outlined in the project's issues. The following instructions detail the process for claiming and completing tasks.

### 1. Task Identification

- Tasks are posted as GitHub issues and can be found in the `Unclaimed` column of the project dashboard.
- Each issue represents a specific task to be completed. The issue title and description contain relevant details and requirements.

### 2. Claiming a Task

- To claim a task, comment the single word `claim` on the relevant GitHub issue.
- If no other user is assigned, you will automatically be assigned to the task, and the issue will move to the `Claimed` column.
- If you decide not to work on a task after claiming it, comment the single word `disclaim` on the issue. This will unassign you and return the issue to the `Unclaimed` column, making it available for others to claim.

### 3. Working on the Task

Once you are assigned to an issue, begin working on the corresponding task. You should fork the project and also create a new branch from the `main` branch to develop your solution. Please try and avoid making PRs from `main` as for technical reasons this makes them slightly harder to review.

### 4. Submitting a Pull Request

- When you are ready to submit your solution, create a PR from the working branch of your fork to the project’s `main` branch.
- After submitting the PR, comment `propose #PR_NUMBER` on the original issue. This links your PR to the task, and the task will move to the `In Progress` column on the dashboard.
- A task can only move to `In Progress` if it has been claimed by the user proposing the PR.

### 5. Withdrawing or Updating a PR

- If you need to withdraw your PR, comment the single phrase `withdraw #PR_NUMBER` on the issue. The task will return to the `Claimed` column, but you will remain assigned to the issue.
- To submit an updated PR after withdrawal, comment `propose #NEW_PR_NUMBER` following the same process outlined in step 4.

### 6. Review Process

- After finishing the task and ensuring your PR is ready for review, comment `awaiting-review` on the PR. This will add the `awaiting-review` label to your PR and move the task from `In Progress` to the `In Review` column of the dashboard.
 The project maintainers will review the PR. They may request changes, approve the PR, or provide feedback. If they comment `awaiting-author`, this will add the `awaiting-author` label to your PR.
 When you've responded, comment `awaiting-review` again to remove it and add the `awaiting-review` tag again.

### 7. Task Completion

- Once the PR is approved and merged, the task will automatically move to the `Completed` column.
- If further adjustments are needed after merging, a new issue will be created to track additional work.

### Additional Guidelines and Notes

1. Please adhere to the issue claiming process. If an issue is already assigned to another contributor, refrain from working on it without prior communication with the current claimant. This ensures a collaborative and respectful workflow that values each contributor’s efforts.
2. Be aware that this contribution process is still in an experimental phase. As a result, occasional issues and inefficiencies may arise. We are committed to continuously refining the process, and your constructive feedback is highly appreciated. You can share your thoughts and suggestions on the [Lean Zulip chat channel](https://leanprover.zulipchat.com/#narrow/channel/423402-PrimeNumberTheorem.2B).
3. Until the integration of sufficient CI automation, the management of the project dashboard is handled manually by the maintainers. We ask for your patience and understanding as we work to keep the process running smoothly.

# Preliminary decay bound II
* **Statement of the theorem (Preliminary decay bound II / `prelim_decay_2`)**

  * Let $\psi:\mathbb R\to\mathbb C$ satisfy:

    * Absolute integrability: $\int_\mathbb R |\psi(t)|,dt<\infty$.
    * Bounded variation on $\mathbb R$: $\mathrm{eVariationOn},\psi,\mathrm{Set.univ}<\infty$.
  * Let $u\in\mathbb R$ with $u\neq 0$.
  * Then the Fourier transform satisfies
    $$|\hat\psi(u)|\le \frac{|\psi|*{TV}}{2\pi|u|},$$
    where $|\psi|*{TV}=(\mathrm{eVariationOn},\psi,\mathrm{Set.univ}).\mathrm{toReal}$.

* **Relation to the Lean statement**

  * `Integrable ψ` encodes absolute integrability with respect to Lebesgue measure in the variable $t$.
  * `BoundedVariationOn ψ Set.univ` encodes finiteness of total variation on all of $\mathbb R$.
  * `𝓕 (ψ : ℝ → ℂ) u` is Lean’s Fourier transform, defined using the kernel $e(-tu)=e^{-2\pi iut}$.
  * `‖u‖` is the real absolute value $|u|$.

* **Conceptual meaning**

  * This theorem is a *regularity-to-decay* result.
  * Compared to the $L^1$ bound $|\hat\psi(u)|\le |\psi|_1$, bounded variation gives an *extra factor* of $1/|u|$.
  * Intuitively, bounded variation limits oscillation of $\psi$, forcing faster decay of its Fourier transform at high frequencies.

* **Key analytic ingredient: Lebesgue–Stieltjes integration by parts**

  * A function of bounded variation defines a finite complex measure $d\psi(t)$.
  * For sufficiently nice $g(t)$, integration by parts gives
    $$\int g(t),d\psi(t)=g(t)\psi(t)\Big|_{-\infty}^{\infty}-\int \psi(t),dg(t).$$
  * This allows us to move derivatives from the oscillatory exponential to $\psi$.

* **Step 1: Start from the Fourier transform definition**

  * By definition (with respect to the variable $t\in\mathbb R$),
    $$\hat\psi(u)=\int_\mathbb R \psi(t),e(-tu),dt,$$
    where $e(-tu)=e^{-2\pi iut}$.

* **Step 2: Differentiate the exponential factor**

  * The exponential satisfies
    $$\frac{d}{dt}e(-tu)=-2\pi i u,e(-tu).$$
  * Equivalently,
    $$e(-tu)=\frac{1}{-2\pi i u},\frac{d}{dt}e(-tu).$$
  * This identity explains why a factor of $2\pi u$ will appear in the final bound.

* **Step 3: Apply Lebesgue–Stieltjes integration by parts**

  * Using bounded variation of $\psi$, integration by parts yields
    $$2\pi i u,\hat\psi(u)=\int_\mathbb R e(-tu),d\psi(t).$$
  * This identity is the core formal step in the Lean proof.

* **Step 4: Take norms of both sides**

  * Taking absolute values gives
    $$2\pi|u|,|\hat\psi(u)|=\left|\int_\mathbb R e(-tu),d\psi(t)\right|.$$

* **Step 5: Use the triangle inequality for Stieltjes integrals**

  * The complex exponential has unit modulus: $|e(-tu)|=1$ for all $t,u$.
  * Therefore,
    $$\left|\int_\mathbb R e(-tu),d\psi(t)\right|\le \int_\mathbb R |d\psi(t)|.$$
  * The right-hand side is exactly the total variation $V(\psi)$.

* **Step 6: Express the bound using total variation**

  * Substituting the total variation bound gives
    $$2\pi|u|,|\hat\psi(u)|\le V(\psi).$$

* **Final rearrangement**

  * Since $u\neq 0$, divide both sides by $2\pi|u|$ to obtain
    $$|\hat\psi(u)|\le \frac{V(\psi)}{2\pi|u|}.$$
  * In Lean notation, this corresponds to
    $$|\mathcal F(\psi)u|\le \frac{(\mathrm{eVariationOn},\psi,\mathrm{Set.univ}).\mathrm{toReal}}{2\cdot\pi\cdot|u|}.$$

* **Summary and takeaway**

  * Absolute integrability ensures $\hat\psi(u)$ is well-defined.
  * Bounded variation allows integration by parts and introduces a factor of $u$ in the denominator.
  * The oscillatory nature of the exponential, combined with bounded variation, forces $O(1/|u|)$ decay of the Fourier transform.

# Autocheby

**Theorem**: Automatic Chebyshev Bound
**Location**: `Wiener.lean` (Lines 3746-3764)
**Name**: `auto_cheby`

### Statement Overview

This theorem asserts that for a non-negative arithmetic function $f(n)$, if its associated Dirichlet series behaves like a simple pole at $s=1$, then the partial sums of $f(n)$ grow at most linearly.

*   **Formal Claim**: $\displaystyle \sum_{n \leq x} f(n) = O(x)$ for all $x \geq 1$.
*   **Goal**: To establish the "Chebyshev bound" (i.e., that the sum is $O(x)$) purely from the analytic properties of the generating function, without assuming it beforehand.

### Assumptions

The theorem relies on four key hypotheses regarding the function $f: \mathbb{N} \to \mathbb{R}$ and its Dirichlet series $L(s) = \sum_{n=1}^\infty f(n)n^{-s}$.

*   **Non-negativity (`hpos`)**
    *   $f(n) \geq 0$ for all $n$.
    *   **Significance**: This allows the use of Tauberian arguments where cancellations usually complicate matters, and ensures monotonic growth of partial sums is only constrained by the magnitude of $f$.
*   **Convergence for $\text{Re}(s) > 1$ (`hf`)**
    *   The series $\sum f(n)n^{-s}$ is summable for all $\sigma' > 1$.
    *   **Significance**: Ensures the L-series is well-defined and analytic in the half-plane to the right of the critical line $\text{Re}(s) = 1$.
*   **Anticipated Pole and Residue (`hG`, `hG'`)**
    *   The code defines a function $G(s)$ representing the analytic part of the L-series near $s=1$.
    *   Specifically, $L(s) - \frac{A}{s-1} = G(s)$ for $\text{Re}(s) > 1$.
    *   **Regularity condition (`hG`)**: $G(s)$ can be analytically continued (or just continuously extended) to the closed half-plane $\text{Re}(s) \geq 1$.
    *   **Interpretation**: The L-series has a simple pole at $s=1$ with residue $A$ and is otherwise regular on the line $\text{Re}(s)=1$.

### Proof Strategy

The proof relies on a bootstrapping argument that converts a "crude" smoothed bound into a sharp asymptotic bound using induction.

#### **Step 1: The Crude Upper Bound**
*   One constructs a smooth, compactly supported test function $\psi$ (a "kernel") whose Fourier transform $\hat{\psi}$ is non-negative.
*   By applying a variant of the limiting Fourier identity (Corollary `crude-upper-bound`), one relates the weighted sum of $f(n)$ to the integral of the L-series.
*   Because the L-series has a simple pole at $s=1$, the contour integral yields a finite value plus terms bounded by the residue $A$.
*   This establishes that a specific weighted average of $f(n)$ is bounded:
    $$ \left| \sum_{n=1}^\infty \frac{f(n)}{n} \hat{\psi}\left( \frac{1}{2\pi} \log \frac{n}{x} \right) \right| \leq B $$

#### **Step 2: Localizing the Bound (Short Intervals)**
*   By choosing $\psi$ effectively, the weight function $\hat{\psi}\left( \frac{1}{2\pi} \log \frac{n}{x} \right)$ can be made to concentrate support on a localized range, such as $n \in ((1-\varepsilon)x, x]$.
*   Since $f(n) \geq 0$, one can drop non-negative terms from the sum or use the positivity to bound the "short interval" sum:
    $$ \sum_{(1-\varepsilon)x < n \leq x} f(n) = O(x) $$
*   Here, the $O(x)$ comes from the scale of the residue and the properties of the kernel $\psi$.

#### **Step 3: Strong Induction (The "Bootstrapping" Argument)**
*   To extend the short interval bound to the full sum $S(x) = \sum_{n \leq x} f(n)$, use strong induction on $x$.
*   **Base Assumption**: Assume the bound holds for all $y < x$.
*   **Inductive Step**: Decompose the sum at $x$:
    $$ S(x) = S((1-\varepsilon)x) + \sum_{(1-\varepsilon)x < n \leq x} f(n) $$
*   By the short interval bound from Step 2, the second term is $\leq C_1 x$.
*   If, inductively, $S((1-\varepsilon)x) \leq C (1-\varepsilon)x$, then:
    $$ S(x) \leq C(1-\varepsilon)x + C_1 x = x (C(1-\varepsilon) + C_1) $$
*   For the bound to hold ($S(x) \leq C x$), we need $C(1-\varepsilon) + C_1 \leq C$, which simplifies to $C \varepsilon \geq C_1$, or $C \geq C_1 / \varepsilon$.
*   Since this holds for a sufficiently large constant $C$, the linear bound $O(x)$ is established for all $x$.

### `h_decomp`
* The hypothesis `h_decomp` plays a critical role in the divide-and-conquer strategy of the proof by strong induction.
    * Decomposition: It splits the total cumulative sum $S(n)$ into two parts:
        * Prefix Sum ($S(m)$): The sum of terms up to $m$. Since $m < n$ (proven in hm_lt), we can control this part using the inductive hypothesis (h_ih).
        * Tail Sum ($\sum f(k)$): The sum of the remaining terms in the interval $(m, n]$. This corresponds to the "short interval" $((1-\epsilon)x, x]$ established in Step 2.
    * Strategy: By splitting the sum, you can prove the bound for $S(n)$ by combining:
        * The bound for $S(m)$ (from induction).
        * The bound for the tail sum (from the h_bound / h_short_interval derived earlier using Fourier analysis).
    * The bound for the tail sum (from the h_bound / h_short_interval derived earlier using Fourier analysis).
Note on Syntax and Indices:

Syntax Error: The error unexpected token 'in' occurs because the correct syntax for sums in Lean usually requires the ∈ symbol (typed with \in) instead of the word in. You should use:
lean
∑ k ∈ Finset.Ico ...
Indices: There might be an off-by-one mismatch in your indices.
S n is defined as cumsum ... n, which typically sums over 0, ..., n-1 (i.e., Finset.range n).
S m sums over 0, ..., m-1.
The difference S n - S m should be the sum over m, ..., n-1, which corresponds to Finset.Ico m n.
Your code uses Finset.Ico (m + 1) (n + 1), which sums m+1, ..., n. You should verify if this shift is intended (e.g., if you are working with 1-based indexing for the number theoretic function). Common usage with range n suggests using Finset.Ico m n.
$$\begin{align*}
\sum_{k=m}^{n-1} f(k)
&= \sum_{k=m}^{n-1} f(k) \cdot \mathbb{1}_{((1-\varepsilon)x, x]}(k) \quad \text{(since } m > (1-\varepsilon)x \text{ and } n-1 \le x \text{)} \\
&\le \sum_{k=0}^{\infty} f(k) \cdot \mathbb{1}_{((1-\varepsilon)x, x]}(k) \quad \text{(extending sum over non-negative terms)} \\
&\le C_{\text{short}} x \quad \text{(by hypothesis } h_{\text{bound}} \text{)}
\end{align*}
$$

To solve the inequality $\sum_{n=0}^\infty \frac{f(n)}{n} \text{Re}\left(\hat{\psi}\left(\frac{1}{2\pi} \log(n/x)\right)\right) \le B$, we can use the following steps.

### Plan to prove `Real.fourierIntegral_convolution`

- **Goal (expanded)**: for `f g : ℝ → ℂ` with `hf : Integrable f volume` and `hg : Integrable g volume`, show

```lean
𝓕 (MeasureTheory.convolution f g (ContinuousLinearMap.mul ℂ ℂ) volume) = 𝓕 f * 𝓕 g
```

- **Normalization note**: adjust signs/normalization if your `𝓕` definition uses a different kernel constant. Below I assume a kernel equivalent to `fun x y => exp (-2 * π * I * x * y)`.

Below is a detailed step–by–step roadmap you can follow when writing the Lean proof. I give the mathematical steps, the analytic justification needed (Tonelli/Fubini, translation invariance), and suggested mathlib lemmas/tactic hints where appropriate.

---

#### 0. Unfold definitions / set up

1. `dsimp` / `rw` to expand the definitions of:

   - `Real.fourierIntegral` / `𝓕` at the point `y` into the integral `∫ x, f x * exp kernel x y` (use whatever exact name your file uses),
   - `MeasureTheory.convolution f g (ContinuousLinearMap.mul ℂ ℂ) volume` into its integral form

     $$
     (f * g)(x) = \int_{t \in \mathbb{R}} f(t)\, g(x-t)\, dt.
     $$
2. Your goal becomes a pointwise equality of integrals for fixed `y`. Start the proof with `ext y` (you already have that).

**Tactic hint:** `dsimp [Real.fourierIntegral, MeasureTheory.convolution]` or `rw [fourierIntegral, convolution]` (names will depend on your file).

---

#### 1. Write the left-hand side as a double integral

After unfolding you will have something like

$$
\int_{x \in \mathbb{R}} \Big(\int_{t \in \mathbb{R}} f(t)\, g(x-t)\, dt\Big)\, e^{-2\pi i x y}\, dx.
$$

Rewrite that as the iterated integral

$$
\int_{x} \int_{t} f(t)\, g(x-t)\, e^{-2\pi i x y}\, dt\, dx.
$$

This is just algebraic rewriting after unfolding.

---

#### 2. Justify swapping integrals (Tonelli / Fubini)

You need to apply Fubini/Tonelli to swap the order of integration. For that you must check absolute integrability of the function
$$
(x,t) \mapsto |f(t), g(x-t), e^{-2\pi i x y}|
= |f(t)|,|g(x-t)|.
$$

Compute the double integral of the absolute value:
$$
\iint |f(t)|,|g(x-t)|, dx, dt
= \int_t |f(t)| \Big(\int_x |g(x-t)|,dx\Big) dt.
$$
Use translation invariance of Lebesgue measure to see, for each fixed `t`,
$$
\int_x |g(x-t)|,dx = \int_u |g(u)|,du = ‖g‖_{L¹} < ∞.
$$
Hence the double integral equals `‖g‖_{L¹} ∫ |f(t)| dt = ‖f‖_{L¹} ‖g‖_{L¹} < ∞`. So the integrand is absolutely integrable and you may apply Fubini/Tonelli.

**Mathlib ingredients / lemma names to look for**

* translation invariance of `volume` for measurable sets / integrals (something like `measure_theory.measure_preserving_add_left` / `measure_preserving_add_right` or `measure_theory.integral_comp_add_right` / `integral_comp_add_left`).
* `MeasureTheory.integrable_of_integrable_norm` or direct `integrable` facts: you already have `hf` and `hg` (integrability of `f` and `g`), i.e. `∫ |f| < ∞` and `∫ |g| < ∞`.
* `MeasureTheory.integral_snd` / Tonelli/Fubini lemma: `MeasureTheory.integral_prod` or `measure_theory.lintegral_prod` / `integral_integral_swap` — look for `integral_congr_ae` and `measure_theory.fubini` / `measure_theory.lintegral` family.

**Tactic hint:** show absolute integrability by

```lean
have h_abs : ∫∫ |f t| * |g (x - t)| ∂x ∂t = ‖f‖_1 * ‖g‖_1 := ...
```

then apply `fubini`/`measure_theory.integral_swap` / `MeasureTheory.iterateIntegral_eq_integral`, e.g.

```lean
have h_swap := (measure_theory.integral_swap ... h_abs).symm
rw [h_swap] at *
```

Exact lemma names may vary; the pattern is: prove `AEMeasurable` and `Integrable` hypotheses, then use `measure_theory.integral_swap` or `measure_theory.lintegral_prod` to swap.

---

#### 3. Swap integrals

Conclude
$$
\int_x \int_t f(t) g(x-t) e^{-2\pi i x y} ,dt,dx
= \int_t f(t) \int_x g(x-t) e^{-2\pi i x y}, dx , dt.
$$

(You have just applied Fubini/Tonelli and moved `f(t)` outside the inner integral because it depends only on `t`.)

**Tactic hint:** `rw [integral_swap ...]` or `have : _ = _ := (integral_swap ...).symm` then `simp` to simplify.

---

#### 4. Change variables in inner integral: $u = x - t$

For each fixed `t`, perform the substitution `u = x - t` on the inner integral:
$$
\int_x g(x-t) e^{-2\pi i x y}, dx
= \int_u g(u) e^{-2\pi i (u+t) y}, du.
$$
Now factor the exponential:
$$
e^{-2\pi i (u+t) y} = e^{-2\pi i u y}, e^{-2\pi i t y}.
$$
So the inner integral equals
$$
e^{-2\pi i t y} \int_u g(u) e^{-2\pi i u y}, du = e^{-2\pi i t y} \cdot 𝓕 g; y.
$$

**Justifications / lemmas**

* Use `measure_theory.integral_comp_add_right` (or equivalent) to change variables for translation: `∫ φ (x - t) dx = ∫ φ x dx` or the more general `integral_comp_map` with `measure_preserving` of `add_left`/`add_right`.
* Use measurability/integrability to justify the substitution; the translation map is measure-preserving and continuous so it preserves integrability.

**Tactic hint:**

```lean
have h_trans : ∫ x, g (x - t) * expKernel x y = exp (-2π I * t * y) * ∫ u, g u * expKernel u y := by
  -- use integral_comp_add_right + simple algebra on the exponential
```

---

#### 5. Plug back into outer integral and factor constants

You now have:
$$
\int_t f(t) \big(e^{-2\pi i t y} \cdot 𝓕 g; y\big), dt
= 𝓕 g; y \cdot \int_t f(t) e^{-2\pi i t y}, dt.
$$
But the remaining integral is exactly `𝓕 f y`, so you obtain
$$
(𝓕 f * 𝓕 g)(y) = 𝓕 f; y \cdot 𝓕 g; y.
$$

Conclude the pointwise equality at `y`. Since `y` was arbitrary and `ext y` was used at the start, finish the proof.

**Tactic hint:** use `simp`/`ring` to move the scalar `𝓕 g y` out of the integral, e.g.

```lean
rw [mul_comm, ← mul_assoc]; simp [← mul_comm]
```

or use `is_scalar_tower`/`algebra` lemmas if needed. Then `simp [Real.fourierIntegral]`.

---

#### 6. Additional housekeeping / edge cases

* **Normalization / kernel sign:** if your Fourier definition uses slightly different constants (e.g. `2*π` vs `-2*π`, or `exp (2π I ...)`), adjust the sign when factoring the exponential in step 4. The algebra is the same.
* **Measurability:** ensure `f`, `g`, and the kernel `x ↦ exp (-2π I x y)` are measurable — the kernel is continuous, so fine.
* **Integrability of the convolution function:** you may also want to show `Integrable (convolution f g …)` (this follows from the L¹ convolution bound `‖f*g‖₁ ≤ ‖f‖₁ ‖g‖₁`, which you essentially used inside the Tonelli argument). It’s convenient to produce this as an auxiliary `have` because `Real.fourierIntegral` might require integrability of its argument.
* **Uniform usage of `volume`:** pass `μ := volume` explicitly to lemmas about convolution/integral swap if Lean has trouble inferring the measure.

**Useful lemmas to search for in mathlib:**

* `MeasureTheory.integral_swap` / `measure_theory.fubini` / `MeasureTheory.integral_iterate` (swap order of integration).
* `MeasureTheory.integral_comp_add_right` / `integral_comp_add_left` / lemmas about translation invariance of `volume`.
* `MeasureTheory.AE.measurable` / `continuous.measurable` (for kernel).
* `MeasureTheory.integrable_of_norm` / `Integrable.ofReal` style lemmas.
* `MeasureTheory.convolution` definition and its measurability facts.
* `Complex.exp_add` / `Complex.mul_comm` / `Complex.mul_assoc` for the exponential algebra.

---

#### Example tactic skeleton (pseudo-Lean)

```lean
theorem Real.fourierIntegral_convolution {f g : ℝ → ℂ} (hf : Integrable f volume)
  (hg : Integrable g volume) :
  𝓕 (MeasureTheory.convolution f g (ContinuousLinearMap.mul ℂ ℂ) volume) = 𝓕 f * 𝓕 g := by
  ext y
  dsimp [Real.fourierIntegral, MeasureTheory.convolution, FourierKernel]  -- names vary
  -- show absolute integrability of (x,t) ↦ |f t| * |g (x-t)| and apply Fubini
  have h_abs : integrable (fun p : ℝ×ℝ => abs (f p.snd) * abs (g (p.fst - p.snd))) volume := ...
  have h_swap := (measure_theory.integral_swap (… ) h_abs) -- exact arguments may vary
  rw [h_swap]
  -- change variables in inner integral
  have h_trans := (integral_comp_add_right ... ) -- move x ↦ x - t
  simp [Complex.exp_add, mul_comm, mul_assoc] at h_trans
  -- factor constants and finish
  simp [Real.fourierIntegral]
```

---

#### Final remarks / priority checklist while implementing in Lean

1. **Find the exact names** of Fubini/Tonelli and translation lemmas in your mathlib version and import the corresponding files.
2. **Prove the absolute integrability** calculation cleanly (this is the crucial analytic input).
3. **Be explicit with `μ := volume`** where Lean has trouble inferring measures.
4. **Track measurability** of all intermediate functions (product measurability is usually automatic from measurability of factors).
5. **Test the proof on a minimal example** (e.g. compactly supported continuous `f`, `g`) first if you run into integrability difficulties, then generalize to arbitrary `L¹` integrable functions.

---

If you want, I can now:

* draft a concrete Lean proof using the exact current mathlib4 lemma names (I can search up the exact lemma names and produce a `proof`), or
* produce the detailed `h_abs` proof (the Young / Tonelli part) in Lean step-by-step. Which would you prefer?


### `psi`
At `Wiener.lean:3820-3822` the hidden fact is:

$$
\operatorname{re}(𝓕\psi(0)) > 0.
$$

### Why this is true (math)

- **You built $\psi$ as an autocorrelation kernel.**
  Earlier in `auto_cheby` you defined:
  - $\varphi : \mathbb{R} \to \mathbb{C}$ from a real bump $\varphi_{\mathrm{real}}$,
  - $\varphi_{\mathrm{rev}}(x) := \overline{\varphi(-x)}$,
  - $\psi := \varphi * \varphi_{\mathrm{rev}}$ (convolution).

- **Fourier transform turns that convolution into a modulus square.**
  Using the convolution theorem and the conjugate/negation Fourier identity (this is exactly the computation used to prove `hψpos` earlier), you get:

  $$
  𝓕\psi(y) = 𝓕\varphi(y)\cdot \overline{𝓕\varphi(y)} = |𝓕\varphi(y)|^2.
  $$

  Hence $𝓕\psi(y)$ is **real and nonnegative** for every $y$. In particular:

  $$
  \operatorname{re}(𝓕\psi(0)) = |𝓕\varphi(0)|^2.
  $$

- **So strict positivity at $0$ reduces to $𝓕\varphi(0)\neq 0$.**
  At frequency $0$, the Fourier integral is just the integral of the function (because the character is $1$):

  $$
  𝓕\varphi(0) = \int_{\mathbb{R}} \varphi(t)\,dt.
  $$

  Your $\varphi_{\mathrm{real}}$ comes from a smooth Urysohn lemma (`smooth_urysohn_support_Ioo ...`), so it is a **nonnegative bump that is not identically zero** (it equals $1$ on some nontrivial region / at least takes a positive value on an open set). Therefore:

  $$
  \int \varphi_{\mathrm{real}}(t)\,dt > 0
  \;\Rightarrow\;
  \int \varphi(t)\,dt > 0
  \;\Rightarrow\;
  |𝓕\varphi(0)|^2 > 0.
  $$

  Thus $\operatorname{re}(𝓕\psi(0)) > 0$.

In short: **$\psi$ is a convolution of $\varphi$ with its conjugate-reversal, so $𝓕\psi = |𝓕\varphi|^2$; at $0$ this is strictly positive because $\varphi$ is chosen nonnegative and nonzero, hence has positive integral.**

### Proving `h_psi_zero_pos` in Lean

You can prove `h_psi_zero_pos` by reducing it to: a nonnegative, nonzero bump has **positive integral**, together with the Fourier identity

$$
\widehat{\psi}(0)=|\widehat{\varphi}(0)|^2.
$$

The two key implementation points are:

- **Don’t throw away** the extra data from `smooth_urysohn_support_Ioo` (you’ll need the support equality / indicator bounds).
- **Reuse** the same Mathlib lemma you already used elsewhere in `Wiener.lean`: `setIntegral_pos_iff_support_of_nonneg_ae`.

Below is a workable skeleton (you may need to tweak a couple `simp` lemmas depending on imports, but the structure is right).

```lean
-- When you define φ_real, keep the bounds/support:
obtain ⟨φ_real, hφSmooth, hφCompact, hφIcc, hφIoo, hφsupp⟩ :=
  smooth_urysohn_support_Ioo (a := (1/2:ℝ)) (b := (1:ℝ)) (c := (1:ℝ)) (d := (2:ℝ))
    (by norm_num) (by norm_num)

let φ : ℝ → ℂ := Complex.ofReal ∘ φ_real
let φ_rev : ℝ → ℂ := fun x ↦ conj (φ (-x))
let ψ_fun : ℝ → ℂ := MeasureTheory.convolution φ φ_rev (ContinuousLinearMap.mul ℂ ℂ) volume
-- ... define ψ : CS 2 ℂ as you already do ...

-- 1) show φ_real is pointwise nonnegative (indicator ≤ φ_real)
have hφ_nonneg : ∀ x, 0 ≤ φ_real x := by
  intro x
  have hx := hφIcc x
  by_cases hmem : x ∈ Set.Icc (1:ℝ) (1:ℝ)
  · -- then indicator = 1, so 1 ≤ φ_real x
    simpa [Set.indicator_of_mem hmem] using (zero_le_one.trans hx)
  · -- then indicator = 0, so 0 ≤ φ_real x
    simpa [Set.indicator_of_not_mem hmem] using hx

-- 2) show the support has positive measure (support = Ioo 1/2 2 contains Ico 1 2)
have hsupp_Ico : Set.Ico (1:ℝ) 2 ⊆ Function.support φ_real := by
  intro x hx
  -- hx : 1 ≤ x ∧ x < 2  ⇒  x ∈ Ioo (1/2) 2
  have hxIoo : x ∈ Set.Ioo ((1/2:ℝ)) 2 := by
    refine ⟨?_, hx.2⟩
    have : (1/2:ℝ) < 1 := by norm_num
    exact this.trans_le hx.1
  -- use support equality
  simpa [hφsupp] using hxIoo

have hvol_supp : (1 : ℝ≥0∞) ≤ volume (Function.support φ_real) := by
  -- volume.mono : A ⊆ B → volume A ≤ volume B
  have := (volume.mono hsupp_Ico)
  -- volume (Ico 1 2) = 1
  simpa using (show (volume (Set.Ico (1:ℝ) 2) : ℝ≥0∞) ≤ volume (Function.support φ_real) from this)

-- 3) conclude ∫ φ_real > 0 using setIntegral_pos_iff_support_of_nonneg_ae on s = univ
have hφint_pos : 0 < ∫ x, φ_real x := by
  have r1 : 0 ≤ᵐ[volume] φ_real := Eventually.of_forall hφ_nonneg
  have r2 : Integrable φ_real := hφSmooth.continuous.integrable_of_hasCompactSupport hφCompact
  -- lemma gives: 0 < ∫ φ_real  ↔ 0 < volume (support φ_real)
  have : 0 < volume (Function.support φ_real) :=
    (zero_lt_one.trans_le hvol_supp)
  -- turn it into the desired integral positivity
  simpa [setIntegral_univ] using
    (setIntegral_pos_iff_support_of_nonneg_ae
        (μ := volume) (s := (Set.univ : Set ℝ)) (f := φ_real)
        (Eventually.of_forall hφ_nonneg) (r2.integrableOn)).2 (by simpa)

-- 4) show 𝓕 φ 0 ≠ 0 (because it’s the integral of φ and has positive real part)
have hFφ0_ne : (𝓕 (φ : ℝ → ℂ) 0) ≠ 0 := by
  -- At frequency 0, Fourier integral is just the integral (character = 1).
  -- And Re(∫ φ) = ∫ φ_real > 0, so the complex number can’t be 0.
  -- (Depending on simp lemmas available, you may do this via `re`.)
  have hre : 0 < (𝓕 (φ : ℝ → ℂ) 0).re := by
    -- simp should reduce 𝓕 φ 0 to ∫ φ, then commute re/integral, then use hφint_pos
    -- Typical shape:
    --   simp [Real.fourier_eq, φ, hφint_pos]   -- may need `Complex.re_integral` lemma
    sorry
  exact fun h => (lt_irrefl (0:ℝ)) (by simpa [h] using hre)

-- 5) now 𝓕 ψ 0 = normSq (𝓕 φ 0), hence real part > 0
have h_psi_zero_pos : 0 < (𝓕 (ψ : ℝ → ℂ) 0).re := by
  -- reuse the same computation pattern as `hψpos` but at y=0
  -- to rewrite (𝓕 ψ 0).re = Complex.normSq (𝓕 φ 0)
  have : (𝓕 (ψ : ℝ → ℂ) 0).re = Complex.normSq (𝓕 (φ : ℝ → ℂ) 0) := by
    -- simp [ψ, ψ_fun, φ_rev, φ, Real.fourierIntegral_convolution, Real.fourierIntegral_conj_neg]
    -- then take real part
    sorry
  -- normSq is strictly positive when the complex number is nonzero
  simpa [this] using (Complex.normSq_pos.2 hFφ0_ne)
```

### What usually needs a tiny bit of “glue”

The only genuinely fiddly substep is **commuting `re` with the integral** in step (4). In Mathlib it’s usually a lemma like `Complex.re_integral` / `Complex.re_integral_eq_integral_re` (name varies). If you can’t find it, you can avoid it by proving directly that `∫ φ ≠ 0` using a norm bound (e.g. `‖∫ φ‖ ≥ ∫ ‖φ‖`), but commuting `re` is the cleanest.

### Role of `ε` in `auto_cheby` (around `Wiener.lean:3831-3832`)

`ε` is the **bridge between a small-neighborhood statement in Fourier space** (the `δ` from continuity of `Re(𝓕 ψ)` near 0) and a **short multiplicative interval in the integers** (the range `((1-ε)x, x]`).

Concretely:

- From continuity you get `∃ δ > 0, ∃ c > 0, ∀ y, |y| < δ → c ≤ (𝓕 ψ y).re`.
- The weighted sum uses the Fourier argument $y = \frac{1}{2\pi}\log(\frac{n}{x})$.
- You **choose**:

$$
ε := 1 - e^{-2\pi δ}
\quad\text{so that}\quad
1-ε = e^{-2\pi δ}.
$$

- Then for any $n \in ((1-ε)x, x]$, you have:

$$
e^{-2\pi δ} < \frac{n}{x} \le 1
\;\Rightarrow\;
-2\pi δ < \log\Big(\frac{n}{x}\Big) \le 0
\;\Rightarrow\;
\Big|\frac{1}{2\pi}\log\Big(\frac{n}{x}\Big)\Big| < δ.
$$

  This is exactly what lets the proof invoke `h_psi_ge_c` on that interval.

So `ε` is chosen **so the indicator interval** `Ioc ((1-ε)*x) x` lands inside the region where the Fourier weight is **uniformly ≥ c**, which is the key Step 2 in the `CONTRIBUTING.md` plan: turning the crude bound on the *smoothed* sum into a bound on the *short-interval* sum, which then bootstraps via strong induction to the full Chebyshev bound.

## Refining (what the `sorry`s mean)

### What the `sorry` at `Wiener.lean:3839` is

At that point you’re inside `h_short_interval : ∃ ε C, ε>0 ∧ ε<1 ∧ C>0 ∧ ∀ x≥1, ...`, and you’ve already chosen

- `ε := 1 - exp(-2πδ)` and proved `hε : 0 < ε ∧ ε < 1`
- `C := B / c + 1`

So the code is building the final pair `⟨C > 0, ∀ x ≥ 1, ...⟩`:

```lean
refine ⟨by
  -- goal: B / c + 1 > 0
  ...
, fun x hx ↦ ?_⟩
```

is constructing the final pair `⟨C>0, ∀ x≥1, ...⟩`. Therefore, **the first `sorry` is exactly the proof obligation**

$$
(B / c + 1) > 0.
$$

How you prove it in Lean (typical approach):

- From `hB`, since norms are nonnegative, you can show `0 ≤ B` (pick any `x>0`, e.g. `x=1`, use `0 ≤ ‖…‖ ≤ B`).
- With `hcpos : c > 0`, you get `0 ≤ B / c`.
- Hence `0 < B / c + 1`.

So the `sorry` is hiding that small lemma: **“the crude-upper-bound constant `B` is ≥ 0, so `B/c + 1` is positive.”**

### What the `sorry` at `Wiener.lean:3840` is

The next `sorry` is unrelated to `C>0`. It’s the proof of

$$
\texttt{Summable}\Big(n \mapsto \frac{f(n)}{n}\, \mathcal{F}\psi(\frac{1}{2\pi}\log(\frac{n}{x}))\Big).
$$

This summability is needed immediately afterward for steps like:

- `Complex.re_tsum h_summable` (commuting `Re` with `tsum`)
- `Summable.tsum_le_tsum ...` (termwise comparison of `tsum`s)

In practice, you usually discharge it by bounding the summand by a known summable series (often using `hf` for some `σ' > 1`, plus boundedness/decay of `𝓕 ψ` coming from smoothness + compact support of `ψ`).
## Proving `c`
### What `c` is

In `auto_cheby`, `c` comes from the “ψ̂ bounded away from 0 near 0” step:

- First you prove $((𝓕 ψ 0).re > 0)$.
- By **continuity** of $y \mapsto (𝓕 ψ y).re$, you get **∃ δ > 0, ∃ c > 0** such that whenever $|y| < δ$, then

$$
c \le (𝓕 ψ\, y).re.
$$

That’s exactly your hypothesis `h_psi_ge_c : ∀ y, |y| < δ → c ≤ (𝓕 ψ y).re` (see `Wiener.lean` around where `c` is obtained).

### Why `c` shows up in the goal as `c / x`

- **Goal (termwise inequality)**:

$$
\frac{c}{x} f(n)\;\le\; \frac{f(n)}{n}\cdot (𝓕 ψ(\tfrac{1}{2\pi}\log(\tfrac{n}{x}))).re.
$$

- **Why this is the right shape**: it’s the inequality you need *term-by-term* to lower-bound the **smoothed/weighted** Dirichlet-series sum by a constant multiple of the **plain** short-interval sum.

- **On the short interval** $n \in ((1-\varepsilon)x, x]$, define the Fourier argument

$$
y := \frac{1}{2\pi}\log\!\Big(\frac{n}{x}\Big).
$$

  `h_arg_small` proves $|y| < \delta$, so `h_psi_ge_c` yields

$$
(𝓕 ψ\, y).re \ge c.
$$

- **Also on that interval** you have $n \le x$, hence $\frac{1}{x} \le \frac{1}{n}$, and therefore

$$
\frac{c}{x} \le \frac{c}{n} \le \frac{(𝓕 ψ\, y).re}{n}.
$$

- **Finally**, since `hpos` gives $f(n)\ge 0$, you can multiply by $f(n)$ without flipping the inequality, producing exactly the goal.

### What’s the mathematical argument behind `h_sum_lower` (3849–3850)

That inequality is proved by a **term-by-term comparison** between two nonnegative series, then summing.

Write the Fourier argument:

$$
y_n := \frac{1}{2\pi}\log\!\Big(\frac{n}{x}\Big).
$$

#### 1) On the short interval, the Fourier weight is uniformly bounded below
If $n \in ((1-\varepsilon)x, x]$, then:
- Since $n \le x$, we have $\log(n/x) \le 0$.
- Since $n > (1-\varepsilon)x$, we have $n/x > 1-\varepsilon$. By the special choice $\varepsilon = 1 - e^{-2\pi\delta}$, this means $n/x > e^{-2\pi\delta}$, so $\log(n/x) > -2\pi\delta$.

So $-2\pi\delta < \log(n/x) \le 0$, hence $|y_n| < \delta$. Then the continuity-based hypothesis gives

$$
(𝓕\psi(y_n)).\mathrm{re} \ge c.
$$

#### 2) Also on the short interval, $\frac1x \le \frac1n$
From $n \le x$ and $n>0$, we get $x^{-1} \le n^{-1}$.

Combining with the previous step:

$$
c\,x^{-1} \;\le\; c\,n^{-1} \;\le\; (𝓕\psi(y_n)).\mathrm{re}\,n^{-1}.
$$

#### 3) Multiply by $f(n)\ge 0$
Since `hpos` says $f(n)\ge 0$, multiplying preserves inequalities:

$$
\frac{c}{x} f(n)\;\le\; \frac{f(n)}{n}\,(𝓕\psi(y_n)).\mathrm{re}.
$$

This is exactly the “member case” goal inside the proof.

#### 4) Off the interval, the left term is 0 and the right term is ≥ 0
If $n\notin ((1-\varepsilon)x,x]$, then the indicator is 0, so the left summand is $0$.
The right summand is $\ge 0$ because $f(n)\ge 0$ and `hψpos` gives $((𝓕\psi(\cdot)).\mathrm{re}\ge 0)$.

#### 5) Sum over all $n$
With the pointwise inequality for every $n$, you can apply `tsum_le_tsum`/monotonicity of infinite sums to conclude:

$$
\frac{c}{x}\sum_n f(n)\mathbf{1}_{((1-\varepsilon)x,x]}(n)\;\le\;\sum_n \frac{f(n)}{n}(𝓕\psi(y_n)).\mathrm{re},
$$

which is `h_sum_lower` at lines 3849–3850.
### Big-picture role in `auto_cheby`

`c` is the **positivity constant** that lets you say: “on the short interval, the Fourier weight is at least `c`”, so the *bounded weighted average* (`hB`) forces a bound on the *unweighted short-interval mass* $\sum_{(1-\varepsilon)x<n\le x} f(n)$. This is the key bridge from Step 1 (“crude upper bound”) to Step 2 (“short interval bound”) in `CONTRIBUTING.md`’s explanation.

Commute Sum and Real Part: Recall that for a convergent series of complex numbers $\sum z_n$, the real part of the sum is the sum of the real parts: $$ \text{Re}\left(\sum_{n} z_n\right) = \sum_{n} \text{Re}(z_n) $$ This allows us to rewritten the LHS as: $$ LHS = \text{Re}\left( \sum_{n=0}^\infty \frac{f(n)}{n} \hat{\psi}\left(\frac{1}{2\pi} \log(n/x)\right) \right) $$
bound Real Part by Norm: For any complex number $Z$, we know that $\text{Re}(Z) \le |Z|$. Applying this to our sum $Z = \sum_{n} \dots$: $$ \text{Re}\left(\sum_{n} \dots\right) \le \left| \sum_{n} \frac{f(n)}{n} \hat{\psi}\left(\frac{1}{2\pi} \log(n/x)\right) \right| $$
Apply Hypothesis hB: The hypothesis hB explicitly bounds exactly this norm: $$ \left| \sum_{n=0}^\infty \frac{f(n)}{n} \hat{\psi}\left(\frac{1}{2\pi} \log(n/x)\right) \right| \le B $$ (provided $x > 0$, which we have from $x \ge 1$).
### Significance in Mathematical Context

*   **The Problem with Circularity**: The standard Wiener-Ikehara theorem proves $S(x) \sim Ax$. However, many classical proofs assume $S(x) = O(x)$ (the "Chebyshev bound") as a precondition to justify the Tauberian limiting process.
*   **The Resolution**: This lemma breaks the circularity. It shows that the analytic continuation of $L(s)$ to $\text{Re}(s)=1$ is actually sufficient on its own (assuming non-negativity) to deduce the $O(x)$ bound.
*   **Result**: This allows the final version of the Wiener-Ikehara theorem to be stated with minimal assumptions: "If $L(s)$ has a pole at $s=1$ and non-negative coefficients, then $S(x) \sim Ax$."


# Crude Upper Bound

**Location**: `PrimeNumberTheoremAnd/Wiener.lean` (Lines 3601-3619)
**Theorem Name**: `crude_upper_bound`

### Overview
This theorem establishes a uniform upper bound on a specific weighted average of a non-negative arithmetic function $f(n)$. It serves as a critical intermediate step in proving the Wiener-Ikehara theorem without assuming a priori Chebyshev bounds (i.e., that $\sum_{n \le x} f(n) = O(x)$).

### Hypotheses
The theorem relies on assumptions about the arithmetic function $f$, its Dirichlet series, and a test function $\psi$:

*   **Arithmetic Function $f$**
    *   **Non-negativity (`hpos`)**: $f(n) \ge 0$ for all $n$.
    *   **Convergence (`hf`)**: The Dirichlet series $L(s) = \sum \frac{f(n)}{n^s}$ converges for $\text{Re}(s) > 1$.
*   **Analytic Behavior near $s=1$**
    *   **Pole Structure (`hG'`)**: The L-series has a simple pole at $s=1$ with residue $A$.
        $$ G(s) = L(s) - \frac{A}{s-1} \quad \text{for } \text{Re}(s) > 1 $$
    *   **Regularity (`hG`)**: The function $G(s)$ can be extended continuously to the closed half-plane $\text{Re}(s) \ge 1$. This implies $L(s)$ has no singularities on the line $\text{Re}(s)=1$ other than the pole at $s=1$.
*   **Test Function $\psi$**
    *   **Regularity**: $\psi: \mathbb{R} \to \mathbb{C}$ is a $C^2$ function with compact support.
    *   **Fourier Transform Condition (`hψpos`)**: The Fourier transform $\hat{\psi}(y)$ is real and non-negative for all $y$.

### Statement
Under the above hypotheses, there exists a constant $B \in \mathbb{R}$ such that for all $x > 0$:

$$ \left| \sum_{n=1}^\infty \frac{f(n)}{n} \hat{\psi}\left( \frac{1}{2\pi} \log \frac{n}{x} \right) \right| \le B $$

*   **Interpretation**: The sum is a weighted average of $f(n)$ around $x$. The weight function depends on $\log(n/x)$, effectively localizing the sum to integers $n$ comparable to $x$.
*   **Significance**: This "crude" bound shows that the average size of $f(n)$ does not explode, solely based on the analytic properties of its generating function.

### Proof Strategy
The proof utilizes a Fourier inversion identity derived in the preceding lemma (`limiting_fourier_variant`) and bounds the resulting terms.

**Step 1: Limiting Fourier Identity**
*   The `limiting_fourier_variant` lemma provides the relation:
    $$ \sum_{n=1}^\infty \frac{f(n)}{n} \hat{\psi}\left( \frac{1}{2\pi} \log \frac{n}{x} \right) - A \int_{-\log x}^\infty \hat{\psi}\left(\frac{u}{2\pi}\right) du = \int_{-\infty}^\infty G(1+it) \psi(t) x^{it} dt $$
*   This equation relates the arithmetic sum (LHS) to an integral involving the analytic part $G(s)$ (RHS) and a boundary term from the pole.

**Step 2: Bounding the Analytic Integral (RHS)**
*   The term to bound is $\int_{\mathbb{R}} G(1+it) \psi(t) x^{it} dt$.
*   Since $\psi$ has compact support, let $S = \text{supp}(\psi)$.
*   $G(1+it)$ is continuous on $S$, which is compact, so $|G(1+it)|$ is bounded by some constant $K$.
*   The term $|x^{it}| = 1$ for real $t$.
*   Therefore, the integral is bounded by $K \int | \psi(t) | dt$, which is independent of $x$.

**Step 3: Bounding the Pole Term**
*   The term to bound is $A \int_{-\log x}^\infty \hat{\psi}\left(\frac{u}{2\pi}\right) du$.
*   Since $\psi$ is $C^2$ and compactly supported, its Fourier transform $\hat{\psi}$ decays rapidly (specifically, it is integrable).
*   The integral over a sub-interval ($[-\log x, \infty)$) is bounded by the integral over the entire real line:
    $$ \left| \int_{-\log x}^\infty \hat{\psi}(u) du \right| \le \int_{-\infty}^\infty |\hat{\psi}(u)| du < \infty $$
*   Thus, this term is also bounded by a constant independent of $x$.

**Step 4: Conclusion via Triangle Inequality**
*   Rearranging the identity from Step 1:
    $$ \text{Sum} = \text{RHS Integral} + \text{Pole Term} $$
*   By the triangle inequality:
    $$ |\text{Sum}| \le |\text{RHS Integral}| + |\text{Pole Term}| $$
*   Since both terms on the right are bounded by constants independent of $x$, the sum is uniformly bounded by some $B$.
