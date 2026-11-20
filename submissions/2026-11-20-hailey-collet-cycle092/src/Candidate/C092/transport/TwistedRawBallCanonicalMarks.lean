/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Direct original canonical marked data, independent of old StepData/globalFace. -/
import Candidate.C092.transport.TwistedRawBallCanonicalProducer
set_option autoImplicit false
namespace QRH.Cycle092.TwistedRawBallRootProducer
noncomputable section
open scoped Classical SchwartzMap
open Set OAI OAI.SevenEighths HeckeFamily
open CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentUncenteredTerminal
open QRH.Record1252270103KernelMass QRH.Record1252270103TwoIdeal
open QRH.SilDensitySplit.CubeFree.FP MixedCanonicalSource
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι]

/-- Unit auxiliary lengths instantiate the native marked-data record only.
    canonicalPairSource installs the four true lengths and true volume. -/
def originalCanonicalMarks (M : Id) [NeZero M] (Hr : Subgroup (O⧸M)ˣ)
    (Z Lcap : ℝ) (hZ : 1<Z) (hLcap : 8 ≤ Lcap)
    (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W ⊆ Icc (1:ℝ) 2)
    (base first : Character) (θ : ι→RayQuotient.Characters M Hr) (w freq : ι→ℝ)
    (hw : ∀i,0 ≤ w i) (hwcap : ∀i,w i ≤ 1/6)
    (R₀ : ι→Finset Id) (t : ℝ) (p : Profiles (1/4) (9/4)) : RestoredRootSource.Data M Hr ι where
  Z:=Z
  hZ:=hZ
  Lcap:=Lcap
  hLcap:=hLcap
  W:=W
  hW:=hW
  hWs:=hWs
  η₀:=base.product first.inverse
  θ:=θ
  w:=w
  freq:=freq
  hw:=hw
  hwcap:=hwcap
  R₀:=R₀
  t:=t
  p:=p
  X₁:=1
  X₂:=1
  hx₁:=by norm_num [comparisonScale]
  hx₂:=by norm_num [comparisonScale]
  hcap₁:=hZ.le
  hcap₂:=hZ.le

theorem originalCanonicalMarks_reanchor
    (M : Id) [NeZero M] (Hr : Subgroup (O⧸M)ˣ)
    (hHr : RayOrthogonality.globalUnits M ≤ Hr)
    (Z Lcap : ℝ) (hZ : 1<Z) (hLcap : 8 ≤ Lcap)
    (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W ⊆ Icc (1:ℝ) 2)
    (base first : Character) (θ : ι→RayQuotient.Characters M Hr) (w freq : ι→ℝ)
    (hw : ∀i,0 ≤ w i) (hwcap : ∀i,w i ≤ 1/6)
    (R₀ : ι→Finset Id) (t : ℝ) (p : Profiles (1/4) (9/4)) (i : ι) (I : Id) :
    let r := originalCanonicalMarks M Hr Z Lcap hZ hLcap W hW hWs base first θ w freq hw hwcap R₀ t p
    slotCoefficient (r.characters hHr) R₀ t i I =
      idealCoeff first I*slotCoefficient (fun j=>relativeCharacter M Hr hHr base (θ j)) R₀ t i I := by
  exact slotCoefficient_reanchor M Hr hHr base first θ R₀ t i I

#print axioms originalCanonicalMarks_reanchor
end
end QRH.Cycle092.TwistedRawBallRootProducer
