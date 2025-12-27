import VerifiedAgora.tagger
/-
Copyright (c) 2023 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, Patrick Massot
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.RCLike.Basic

/-!
# A collection of specific limit computations for `RCLike`

-/

open Set Algebra Filter
open scoped Topology

variable (𝕜 : Type*) [RCLike 𝕜]

theorem RCLike.tendsto_inverse_atTop_nhds_zero_nat :
    Tendsto (fun n : ℕ => (n : 𝕜)⁻¹) atTop (𝓝 0) := by
  convert tendsto_algebraMap_inverse_atTop_nhds_zero_nat 𝕜
  simp

variable {𝕜}

theorem RCLike.tendsto_add_mul_div_add_mul_atTop_nhds (a b c : 𝕜) {d : 𝕜} (hd : d ≠ 0) :
    Tendsto (fun k : ℕ ↦ (a + c * k) / (b + d * k)) atTop (𝓝 (c / d)) := by
  apply Filter.Tendsto.congr'
  case f₁ => exact fun k ↦ (a * (↑k)⁻¹ + c) / (b * (↑k)⁻¹ + d)
  · refine (eventually_ne_atTop 0).mp (Eventually.of_forall ?_)
    intro h hx
    field_simp [hx]
  · apply Filter.Tendsto.div _ _ hd
    all_goals
      apply zero_add (_ : 𝕜) ▸ Filter.Tendsto.add_const _ _
      apply mul_zero (_ : 𝕜) ▸ Filter.Tendsto.const_mul _ _
      exact RCLike.tendsto_inverse_atTop_nhds_zero_nat 𝕜
