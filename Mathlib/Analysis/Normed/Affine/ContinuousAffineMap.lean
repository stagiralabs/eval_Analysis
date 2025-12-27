import VerifiedAgora.tagger
/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Topology.Algebra.ContinuousAffineMap
import Mathlib.Analysis.NormedSpace.OperatorNorm.NormedSpace

/-!
# Continuous affine maps between normed spaces.

This file develops the theory of continuous affine maps between affine spaces modelled on normed
spaces.

In the particular case that the affine spaces are just normed vector spaces `V`, `W`, we define a
norm on the space of continuous affine maps by defining the norm of `f : V →ᴬ[𝕜] W` to be
`‖f‖ = max ‖f 0‖ ‖f.cont_linear‖`. This is chosen so that we have a linear isometry:
`(V →ᴬ[𝕜] W) ≃ₗᵢ[𝕜] W × (V →L[𝕜] W)`.

The abstract picture is that for an affine space `P` modelled on a vector space `V`, together with
a vector space `W`, there is an exact sequence of `𝕜`-modules: `0 → C → A → L → 0` where `C`, `A`
are the spaces of constant and affine maps `P → W` and `L` is the space of linear maps `V → W`.

Any choice of a base point in `P` corresponds to a splitting of this sequence so in particular if we
take `P = V`, using `0 : V` as the base point provides a splitting, and we prove this is an
isometric decomposition.

On the other hand, choosing a base point breaks the affine invariance so the norm fails to be
submultiplicative: for a composition of maps, we have only `‖f.comp g‖ ≤ ‖f‖ * ‖g‖ + ‖f 0‖`.

## Main definitions:

 * `ContinuousAffineMap.contLinear`
 * `ContinuousAffineMap.hasNorm`
 * `ContinuousAffineMap.norm_comp_le`
 * `ContinuousAffineMap.toConstProdContinuousLinearMap`

-/


namespace ContinuousAffineMap

variable {𝕜 R V W W₂ P Q Q₂ : Type*}
variable [NormedAddCommGroup V] [MetricSpace P] [NormedAddTorsor V P]
variable [NormedAddCommGroup W] [MetricSpace Q] [NormedAddTorsor W Q]
variable [NormedAddCommGroup W₂] [MetricSpace Q₂] [NormedAddTorsor W₂ Q₂]
variable [NormedField R] [NormedSpace R V] [NormedSpace R W] [NormedSpace R W₂]
variable [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 V] [NormedSpace 𝕜 W] [NormedSpace 𝕜 W₂]

/-- The linear map underlying a continuous affine map is continuous. -/
def contLinear (f : P →ᴬ[R] Q) : V →L[R] W :=
  { f.linear with
    toFun := f.linear
    cont := by rw [AffineMap.continuous_linear_iff]; exact f.cont }

@[simp]
theorem coe_contLinear (f : P →ᴬ[R] Q) : (f.contLinear : V → W) = f.linear :=
  rfl

@[simp]
theorem coe_contLinear_eq_linear (f : P →ᴬ[R] Q) :
    (f.contLinear : V →ₗ[R] W) = (f : P →ᵃ[R] Q).linear := by ext; rfl

@[target] theorem coe_mk_const_linear_eq_linear (f : P →ᵃ[R] Q) (h) :
    ((⟨f, h⟩ : P →ᴬ[R] Q).contLinear : V → W) = f.linear := by sorry


@[target] theorem coe_linear_eq_coe_contLinear (f : P →ᴬ[R] Q) :
    ((f : P →ᵃ[R] Q).linear : V → W) = (⇑f.contLinear : V → W) := by sorry


@[simp]
theorem comp_contLinear (f : P →ᴬ[R] Q) (g : Q →ᴬ[R] Q₂) :
    (g.comp f).contLinear = g.contLinear.comp f.contLinear :=
  rfl

@[target] theorem map_vadd (f : P →ᴬ[R] Q) (p : P) (v : V) : f (v +ᵥ p) = f.contLinear v +ᵥ f p := by sorry


@[target] theorem contLinear_map_vsub (f : P →ᴬ[R] Q) (p₁ p₂ : P) : f.contLinear (p₁ -ᵥ p₂) = f p₁ -ᵥ f p₂ := by sorry


@[simp]
theorem const_contLinear (q : Q) : (const R P q).contLinear = 0 :=
  rfl

@[target] theorem contLinear_eq_zero_iff_exists_const (f : P →ᴬ[R] Q) :
    f.contLinear = 0 ↔ ∃ q, f = const R P q := by
  sorry


@[target] theorem to_affine_map_contLinear (f : V →L[R] W) : f.toContinuousAffineMap.contLinear = f := by
  sorry


@[target] theorem zero_contLinear : (0 : P →ᴬ[R] W).contLinear = 0 := by sorry


@[target] theorem add_contLinear (f g : P →ᴬ[R] W) : (f + g).contLinear = f.contLinear + g.contLinear := by sorry


@[target] theorem sub_contLinear (f g : P →ᴬ[R] W) : (f - g).contLinear = f.contLinear - g.contLinear := by sorry


@[simp]
theorem neg_contLinear (f : P →ᴬ[R] W) : (-f).contLinear = -f.contLinear :=
  rfl

@[target] theorem smul_contLinear (t : R) (f : P →ᴬ[R] W) : (t • f).contLinear = t • f.contLinear := by sorry


@[target] theorem decomp (f : V →ᴬ[R] W) : (f : V → W) = f.contLinear + Function.const V (f 0) := by
  sorry


section NormedSpaceStructure

variable (f : V →ᴬ[𝕜] W)

/-- Note that unlike the operator norm for linear maps, this norm is _not_ submultiplicative:
we do _not_ necessarily have `‖f.comp g‖ ≤ ‖f‖ * ‖g‖`. See `norm_comp_le` for what we can say. -/
noncomputable instance hasNorm : Norm (V →ᴬ[𝕜] W) :=
  ⟨fun f => max ‖f 0‖ ‖f.contLinear‖⟩

theorem norm_def : ‖f‖ = max ‖f 0‖ ‖f.contLinear‖ :=
  rfl

theorem norm_contLinear_le : ‖f.contLinear‖ ≤ ‖f‖ :=
  le_max_right _ _

@[target] theorem norm_image_zero_le : ‖f 0‖ ≤ ‖f‖ := by sorry


@[target] theorem norm_eq (h : f 0 = 0) : ‖f‖ = ‖f.contLinear‖ :=
  calc
    ‖f‖ = max ‖f 0‖ ‖f.contLinear‖ := by sorry


noncomputable instance : NormedAddCommGroup (V →ᴬ[𝕜] W) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := fun f => max ‖f 0‖ ‖f.contLinear‖
      map_zero' := by simp [(ContinuousAffineMap.zero_apply)]
      neg' := fun f => by
        simp [(ContinuousAffineMap.neg_apply)]
      add_le' := fun f g => by
        simp only [coe_add, max_le_iff, Pi.add_apply, add_contLinear]
        exact
          ⟨(norm_add_le _ _).trans (add_le_add (le_max_left _ _) (le_max_left _ _)),
            (norm_add_le _ _).trans (add_le_add (le_max_right _ _) (le_max_right _ _))⟩
      eq_zero_of_map_eq_zero' := fun f h₀ => by
        rcases max_eq_iff.mp h₀ with (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) <;> rw [h₁] at h₂
        · rw [norm_le_zero_iff, contLinear_eq_zero_iff_exists_const] at h₂
          obtain ⟨q, rfl⟩ := h₂
          simp only [norm_eq_zero, coe_const, Function.const_apply] at h₁
          rw [h₁]
          rfl
        · rw [norm_eq_zero, contLinear_eq_zero_iff_exists_const] at h₁
          obtain ⟨q, rfl⟩ := h₁
          simp only [norm_le_zero_iff, coe_const, Function.const_apply] at h₂
          rw [h₂]
          rfl }

instance : NormedSpace 𝕜 (V →ᴬ[𝕜] W) where
  norm_smul_le t f := by
    simp only [norm_def, coe_smul, Pi.smul_apply, norm_smul, smul_contLinear,
      ← mul_max_of_nonneg _ _ (norm_nonneg t), le_refl]

@[target] theorem norm_comp_le (g : W₂ →ᴬ[𝕜] V) : ‖f.comp g‖ ≤ ‖f‖ * ‖g‖ + ‖f 0‖ := by
  sorry


variable (𝕜 V W)

/-- The space of affine maps between two normed spaces is linearly isometric to the product of the
codomain with the space of linear maps, by taking the value of the affine map at `(0 : V)` and the
linear part. -/
def toConstProdContinuousLinearMap : (V →ᴬ[𝕜] W) ≃ₗᵢ[𝕜] W × (V →L[𝕜] W) where
  toFun f := ⟨f 0, f.contLinear⟩
  invFun p := p.2.toContinuousAffineMap + const 𝕜 V p.1
  left_inv f := by
    ext
    rw [f.decomp]
    simp only [coe_add, ContinuousLinearMap.coe_toContinuousAffineMap, Pi.add_apply, coe_const]
  right_inv := by rintro ⟨v, f⟩; ext <;> simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

@[target] theorem toConstProdContinuousLinearMap_fst (f : V →ᴬ[𝕜] W) :
    (toConstProdContinuousLinearMap 𝕜 V W f).fst = f 0 := by sorry


@[target] theorem toConstProdContinuousLinearMap_snd (f : V →ᴬ[𝕜] W) :
    (toConstProdContinuousLinearMap 𝕜 V W f).snd = f.contLinear := by sorry


end NormedSpaceStructure

end ContinuousAffineMap
