/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.FixedCubeApplicationCharacter

set_option autoImplicit false
namespace QRH.Cycle092.SignedCenter
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily EisensteinSchwartzPoisson CenteredMomentLattice
local notation "O" => HeckeFamily.O

/-- The original fixed-row source before removing the two independent outside
norm phases. Its arithmetic coefficient and exceptional masks are unchanged. -/
def fixedCubeRawSource (D₁ D₂ : FixedCubeDatum) (P₁ P₂ : OrdinaryProfile)
    (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (x y : ℝ) : ℂ :=
  ∑' p : Ideal O×Ideal O,
    (if PairAllowed bad allowed p.1 p.2 then
      D₁.actualCoefficient p.1*D₂.actualCoefficient p.2 else 0)*
      (Ideal.absNorm p.1 : ℂ)^(Complex.I*P₁.t)*(Ideal.absNorm p.2 : ℂ)^(Complex.I*P₂.t)*
      P₁.W ((Ideal.absNorm p.1 : ℝ)/x)*P₂.W ((Ideal.absNorm p.2 : ℝ)/y)

def fixedCubeOutsidePhase (P₁ P₂ : OrdinaryProfile) (x y : ℝ) : ℂ :=
  (x : ℂ)^(Complex.I*P₁.t)*(y : ℂ)^(Complex.I*P₂.t)

lemma fixedCubeOutsidePhase_ne_zero (P₁ P₂ : OrdinaryProfile) (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y) : fixedCubeOutsidePhase P₁ P₂ x y ≠ 0 :=
  mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne')))
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne')))

/-- The actual two raw pitches are normalized separately. Even the signed
reference arm has its own outside phase before applying equal-product H8. -/
theorem fixedCubeRawSource_scale (D₁ D₂ : FixedCubeDatum) (P₁ P₂ : OrdinaryProfile)
    (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y) :
    fixedCubeRawSource D₁ D₂ P₁ P₂ bad allowed x y=
      fixedCubeOutsidePhase P₁ P₂ x y*fixedCubePhysicalSource D₁ D₂ P₁ P₂ bad allowed x y := by
  unfold fixedCubeRawSource fixedCubePhysicalSource
  rw [←tsum_mul_left]
  apply tsum_congr
  intro p
  have hphase (N : ℕ) (X t : ℝ) (hX : 0 < X) :
      (N : ℂ)^(Complex.I*t)=(X : ℂ)^(Complex.I*t)*(((N : ℝ)/X : ℝ) : ℂ)^(Complex.I*t) := by
    have h := Complex.mul_cpow_ofReal_nonneg hX.le
      (div_nonneg (Nat.cast_nonneg N) hX.le) (Complex.I*t)
    have he : X*((N : ℝ)/X)=(N : ℝ) := by field_simp
    rw [←Complex.ofReal_mul,he,Complex.ofReal_natCast] at h
    exact h
  dsimp only [OrdinaryProfile.normalized]
  rw [normPowerProfile_apply,normPowerProfile_apply,hphase _ x P₁.t hx,hphase _ y P₂.t hy]
  unfold fixedCubeOutsidePhase
  ring

/-- H8's physical source is exactly the original source with its actual
independent outside phases removed, with no altered ray or mask. -/
theorem fixedCubeRawSource_normalized (D₁ D₂ : FixedCubeDatum) (P₁ P₂ : OrdinaryProfile)
    (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y) :
    (fixedCubeOutsidePhase P₁ P₂ x y)⁻¹*fixedCubeRawSource D₁ D₂ P₁ P₂ bad allowed x y=
      fixedCubePhysicalSource D₁ D₂ P₁ P₂ bad allowed x y := by
  rw [fixedCubeRawSource_scale D₁ D₂ P₁ P₂ bad allowed x y hx hy]
  exact inv_mul_cancel_left₀ (fixedCubeOutsidePhase_ne_zero P₁ P₂ x y hx hy) _

/-- The original signed rectangles are normalized before installing their
reference; heights need not agree and no raw phase is silently shared. -/
theorem fixedCubeRawSource_signed_normalized (D₁ D₂ : FixedCubeDatum) (P₁ P₂ : OrdinaryProfile)
    (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ))
    (X₁ X₂ Y₁ Y₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    (fixedCubeOutsidePhase P₁ P₂ X₁ X₂)⁻¹*fixedCubeRawSource D₁ D₂ P₁ P₂ bad allowed X₁ X₂-
      (fixedCubeOutsidePhase P₁ P₂ Y₁ Y₂)⁻¹*fixedCubeRawSource D₁ D₂ P₁ P₂ bad allowed Y₁ Y₂=
    fixedCubePhysicalSource D₁ D₂ P₁ P₂ bad allowed X₁ X₂-
      fixedCubePhysicalSource D₁ D₂ P₁ P₂ bad allowed Y₁ Y₂ := by
  rw [fixedCubeRawSource_normalized D₁ D₂ P₁ P₂ bad allowed X₁ X₂ hX₁ hX₂,
    fixedCubeRawSource_normalized D₁ D₂ P₁ P₂ bad allowed Y₁ Y₂ hY₁ hY₂]

#print axioms fixedCubeRawSource_scale
#print axioms fixedCubeRawSource_signed_normalized
end
end QRH.Cycle092.SignedCenter
