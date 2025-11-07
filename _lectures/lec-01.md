---
layout: lecture
title: "Lecture 1: Introduction to the Course"
date: 2025-01-23
slides_url: /slides/slides-01.html
---

* TOC
{:toc}

## Notes

Notes for the first lecture will be added here...

## LaTeX support

The notes support inline math like $e^{i \pi} + 1 = 0$, or centered math
like

$$
    \int_{-\infty}^{\infty} e^{-x^2/2} dx = \sqrt{2 \pi}
$$

## Sample Code Block

Below we are testing how a code block would get rendered.

```lean
lemma implication_1 : A → (B → A) := by
  intro h_A
  intro _
  exact h_A

lemma implication_2 : A → (A → B) → B := by
  intro h_A h_A_to_B -- Same as `intro h_A` then `intro h_A_to_B`
  exact h_A_to_B h_A

lemma implication_3 : (A → (B → C)) → ((A → B) → (A → C)) := by
  intro h₁ h₂ h_a
  apply h₁ h_a
  apply h₂
  exact h_a
```