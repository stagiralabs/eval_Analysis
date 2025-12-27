import VerifiedAgora.tagger
/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.MeasureTheory.Integral.SetIntegral

/-!
# Integrals and the continuous functional calculus

This file gives results about integrals of the form `∫ x, cfc (f x) a`. Most notably, we show
that the integral commutes with the continuous functional calculus under appropriate conditions.

## Main declarations

+ `cfc_integral`: given a function `f : X → 𝕜 → 𝕜`, we have that
  `cfc (fun r => ∫ x, f x r ∂μ) a = ∫ x, cfc (f x) a ∂μ`
  under appropriate conditions
+ `cfcₙ_integral`: given a function `f : X → 𝕜 → 𝕜`, we have that
  `cfcₙ (fun r => ∫ x, f x r ∂μ) a = ∫ x, cfcₙ (f x) a ∂μ`
  under appropriate conditions

## TODO

+ Lift this to the case where the CFC is over `ℝ≥0`
+ Use this to prove operator monotonicity and concavity/convexity of `rpow` and `log`
-/

open MeasureTheory Topology
open scoped ContinuousMapZero

section unital

variable {X : Type*} {𝕜 : Type*} {A : Type*} {p : A → Prop} [RCLike 𝕜]
  [MeasurableSpace X] {μ : Measure X}
  [NormedRing A] [StarRing A] [NormedAlgebra 𝕜 A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [ContinuousFunctionalCalculus 𝕜 p]

lemma cfcL_integral (a : A) (f : X → C(spectrum 𝕜 a, 𝕜)) (hf₁ : Integrable f μ)
    (ha : p a := by cfc_tac) :
    ∫ x, cfcL (a := a) ha (f x) ∂μ = cfcL (a := a) ha (∫ x, f x ∂μ) := by
  rw [ContinuousLinearMap.integral_comp_comm _ hf₁]

lemma cfcHom_integral (a : A) (f : X → C(spectrum 𝕜 a, 𝕜)) (hf₁ : Integrable f μ)
    (ha : p a := by cfc_tac) :
    ∫ x, cfcHom (a := a) ha (f x) ∂μ = cfcHom (a := a) ha (∫ x, f x ∂μ) :=
  cfcL_integral a f hf₁ ha

open ContinuousMap in
/-- The continuous functional calculus commutes with integration. -/
lemma cfc_integral [TopologicalSpace X] [OpensMeasurableSpace X] (f : X → 𝕜 → 𝕜)
    (bound : X → ℝ) (a : A) [SecondCountableTopologyEither X C(spectrum 𝕜 a, 𝕜)]
    (hf₁ : ∀ x, ContinuousOn (f x) (spectrum 𝕜 a))
    (hf₂ : Continuous (fun x ↦ (⟨_, hf₁ x |>.restrict⟩ : C(spectrum 𝕜 a, 𝕜))))
    (hbound : ∀ x, ∀ z ∈ spectrum 𝕜 a, ‖f x z‖ ≤ ‖bound x‖)
    (hbound_finite_integral : HasFiniteIntegral bound μ) (ha : p a := by cfc_tac) :
    cfc (fun r => ∫ x, f x r ∂μ) a = ∫ x, cfc (f x) a ∂μ := by
  let fc : X → C(spectrum 𝕜 a, 𝕜) := fun x => ⟨_, (hf₁ x).restrict⟩
  have fc_integrable : Integrable fc μ := by
    refine ⟨hf₂.aestronglyMeasurable, ?_⟩
    refine hbound_finite_integral.mono <| .of_forall fun x ↦ ?_
    rw [norm_le _ (norm_nonneg (bound x))]
    exact fun z ↦ hbound x z.1 z.2
  have h_int_fc : (spectrum 𝕜 a).restrict (∫ x, f x · ∂μ) = ∫ x, fc x ∂μ := by
    ext; simp [integral_apply fc_integrable, fc]
  have hcont₂ : ContinuousOn (fun r => ∫ x, f x r ∂μ) (spectrum 𝕜 a) := by
    rw [continuousOn_iff_continuous_restrict]
    convert map_continuous (∫ x, fc x ∂μ)
  rw [integral_congr_ae (.of_forall fun _ ↦ cfc_apply ..), cfc_apply ..,
    cfcHom_integral _ _ fc_integrable]
  congr

/-- The continuous functional calculus commutes with integration. -/
lemma cfc_integral' [TopologicalSpace X] [OpensMeasurableSpace X] (f : X → 𝕜 → 𝕜)
    (bound : X → ℝ) (a : A) [SecondCountableTopologyEither X C(spectrum 𝕜 a, 𝕜)]
    (hf : Continuous (fun x => (spectrum 𝕜 a).restrict (f x)).uncurry)
    (hbound : ∀ x, ∀ z ∈ spectrum 𝕜 a, ‖f x z‖ ≤ ‖bound x‖)
    (hbound_finite_integral : HasFiniteIntegral bound μ) (ha : p a := by cfc_tac) :
    cfc (fun r => ∫ x, f x r ∂μ) a = ∫ x, cfc (f x) a ∂μ := by
  refine cfc_integral f bound a ?_ ?_ hbound hbound_finite_integral
  · exact (continuousOn_iff_continuous_restrict.mpr <| hf.uncurry_left ·)
  · exact ContinuousMap.curry ⟨_, hf⟩ |>.continuous

end unital

section nonunital

variable {X : Type*} {𝕜 : Type*} {A : Type*} {p : A → Prop} [RCLike 𝕜]
  [MeasurableSpace X] {μ : Measure X} [NonUnitalNormedRing A] [StarRing A] [CompleteSpace A]
  [NormedSpace 𝕜 A] [NormedSpace ℝ A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
  [NonUnitalContinuousFunctionalCalculus 𝕜 p]

lemma cfcₙL_integral (a : A) (f : X → C(quasispectrum 𝕜 a, 𝕜)₀) (hf₁ : Integrable f μ)
    (ha : p a := by cfc_tac) :
    ∫ x, cfcₙL (a := a) ha (f x) ∂μ = cfcₙL (a := a) ha (∫ x, f x ∂μ) := by
  rw [ContinuousLinearMap.integral_comp_comm _ hf₁]

lemma cfcₙHom_integral (a : A) (f : X → C(quasispectrum 𝕜 a, 𝕜)₀) (hf₁ : Integrable f μ)
    (ha : p a := by cfc_tac) :
    ∫ x, cfcₙHom (a := a) ha (f x) ∂μ = cfcₙHom (a := a) ha (∫ x, f x ∂μ) :=
  cfcₙL_integral a f hf₁ ha

open ContinuousMapZero in
/-- The non-unital continuous functional calculus commutes with integration. -/
lemma cfcₙ_integral [TopologicalSpace X] [OpensMeasurableSpace X] (f : X → 𝕜 → 𝕜)
    (bound : X → ℝ) (a : A) [SecondCountableTopologyEither X C(quasispectrum 𝕜 a, 𝕜)₀]
    (hf₁ : ∀ x, ContinuousOn (f x) (quasispectrum 𝕜 a))
    (hf₂ : ∀ x, f x 0 = 0)
    (hf₃ : Continuous (fun x ↦ (⟨⟨_, hf₁ x |>.restrict⟩, hf₂ x⟩ : C(quasispectrum 𝕜 a, 𝕜)₀)))
    (hbound : ∀ x, ∀ z ∈ quasispectrum 𝕜 a, ‖f x z‖ ≤ ‖bound x‖)
    (hbound_finite_integral : HasFiniteIntegral bound μ) (ha : p a := by cfc_tac) :
    cfcₙ (fun r => ∫ x, f x r ∂μ) a = ∫ x, cfcₙ (f x) a ∂μ := by
  let fc : X → C(quasispectrum 𝕜 a, 𝕜)₀ := fun x => ⟨⟨_, (hf₁ x).restrict⟩, hf₂ x⟩
  have fc_integrable : Integrable fc μ := by
    refine ⟨hf₃.aestronglyMeasurable, ?_⟩
    refine hbound_finite_integral.mono <| .of_forall fun x ↦ ?_
    change ‖(fc x : C(quasispectrum  𝕜 a, 𝕜))‖ ≤ ‖bound x‖
    rw [ContinuousMap.norm_le _ (norm_nonneg (bound x))]
    exact fun z ↦ hbound x z.1 z.2
  have h_int_fc : (quasispectrum 𝕜 a).restrict (∫ x, f x · ∂μ) = ∫ x, fc x ∂μ := by
    ext; simp [integral_apply fc_integrable, fc]
  have hcont₂ : ContinuousOn (fun r => ∫ x, f x r ∂μ) (quasispectrum 𝕜 a) := by
    rw [continuousOn_iff_continuous_restrict]
    convert map_continuous (∫ x, fc x ∂μ)
  rw [integral_congr_ae (.of_forall fun _ ↦ cfcₙ_apply ..), cfcₙ_apply ..,
    cfcₙHom_integral _ _ fc_integrable]
  congr

/-- The non-unital continuous functional calculus commutes with integration. -/
lemma cfcₙ_integral' [TopologicalSpace X] [OpensMeasurableSpace X] (f : X → 𝕜 → 𝕜)
    (bound : X → ℝ) (a : A) [SecondCountableTopologyEither X C(quasispectrum 𝕜 a, 𝕜)₀]
    (hf : Continuous (fun x => (quasispectrum 𝕜 a).restrict (f x)).uncurry)
    (hf₂ : ∀ x, f x 0 = 0)
    (hbound : ∀ x, ∀ z ∈ quasispectrum 𝕜 a, ‖f x z‖ ≤ ‖bound x‖)
    (hbound_finite_integral : HasFiniteIntegral bound μ) (ha : p a := by cfc_tac) :
    cfcₙ (fun r => ∫ x, f x r ∂μ) a = ∫ x, cfcₙ (f x) a ∂μ := by
  refine cfcₙ_integral f bound a ?_ hf₂ ?_ hbound hbound_finite_integral
  · exact (continuousOn_iff_continuous_restrict.mpr <| hf.uncurry_left ·)
  · let g := ((↑) : C(quasispectrum 𝕜 a, 𝕜)₀ → C(quasispectrum 𝕜 a, 𝕜))
    refine ((isInducing_iff g).mpr rfl).continuous_iff.mpr ?_
    exact ContinuousMap.curry ⟨_, hf⟩ |>.continuous

end nonunital
