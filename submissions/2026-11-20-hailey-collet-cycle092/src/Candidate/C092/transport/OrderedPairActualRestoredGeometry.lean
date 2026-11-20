/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
All intake proofs for the actual four inverse-divided lengths are derived
from the original positive common rectangle and equal product. -/
import Candidate.C092.transport.OrderedPairActualRestoredLeaf
set_option autoImplicit false
namespace QRH.Cycle092.OrderedPairActualRestored
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily
open QRH.Record1252270103KernelMass
open QRH.SilDensitySplit.CubeFree.FP KernelRowPools
open QRH.Cycle092.TwistedRawBallRootProducer QRH.Cycle092.FixedFramePacking
local notation "O"=>HeckeFamily.O
local notation "Id"=>Ideal O
local notation "Prime"=>QRH.Record1252270103KernelMass.PrimeIdeal

structure DividedLengths (Z X₁ X₂ Y₁ Y₂:ℝ) (d:IdealPair) : Prop where
  x₁ : 0<X₁/d.1.absNorm
  x₂ : 0<X₂/d.2.absNorm
  y₁ : 0<Y₁/d.1.absNorm
  y₂ : 0<Y₂/d.2.absNorm
  product : (X₁/d.1.absNorm)*(X₂/d.2.absNorm)=(Y₁/d.1.absNorm)*(Y₂/d.2.absNorm)
  capx₁ : X₁/d.1.absNorm ≤ Z
  capx₂ : X₂/d.2.absNorm ≤ Z
  capy₁ : Y₁/d.1.absNorm ≤ Z
  capy₂ : Y₂/d.2.absNorm ≤ Z

theorem divided_lengths (Z X₁ X₂ Y₁ Y₂ M₁ M₂:ℝ) (S:Finset Prime) (d:IdealPair)
    (hX₁:0<X₁)(hX₂:0<X₂)(hY₁:0<Y₁)(hY₂:0<Y₂)
    (hprod:X₁*X₂=Y₁*Y₂)
    (hxM₁:X₁ ≤ M₁)(hyM₁:Y₁ ≤ M₁)(hxM₂:X₂ ≤ M₂)(hyM₂:Y₂ ≤ M₂)
    (hM₁:M₁ ≤ Z)(hM₂:M₂ ≤ Z)
    (hd:d∈divisorPool (supportedRectangle S (9/4) M₁ M₂)) :
    DividedLengths Z X₁ X₂ Y₁ Y₂ d := by
  have hc:=root_divisor_caps S (9/4) M₁ M₂ hd
  have hp:0<(d.1.absNorm:ℝ):=zero_lt_one.trans_le hc.1
  have hq:0<(d.2.absNorm:ℝ):=zero_lt_one.trans_le hc.2.1
  refine ⟨div_pos hX₁ hp,div_pos hX₂ hq,div_pos hY₁ hp,div_pos hY₂ hq,?_,
    (div_le_self hX₁.le hc.1).trans (hxM₁.trans hM₁),
    (div_le_self hX₂.le hc.2.1).trans (hxM₂.trans hM₂),
    (div_le_self hY₁.le hc.1).trans (hyM₁.trans hM₁),
    (div_le_self hY₂.le hc.2.1).trans (hyM₂.trans hM₂)⟩
  rw [div_mul_div_comm,div_mul_div_comm,hprod]

variable {ι:Type} [Fintype ι]
def dividedCanonicalSource (M:Id)[NeZero M](Hr:Subgroup (O⧸M)ˣ)
    (hHr:RayOrthogonality.globalUnits M ≤ Hr)(r:RestoredRootSource.Data M Hr ι)
    (X₁ X₂ Y₁ Y₂ t₁ t₂:ℝ)(d:IdealPair)
    (h:DividedLengths r.Z X₁ X₂ Y₁ Y₂ d) : MixedPrincipalPair.Source ι (1/4) (9/4) :=
  canonicalPairSource M Hr hHr r (X₁/d.1.absNorm) (X₂/d.2.absNorm)
    (Y₁/d.1.absNorm) (Y₂/d.2.absNorm) t₁ t₂
    h.x₁ h.x₂ h.y₁ h.y₂ h.product h.capx₁ h.capx₂ h.capy₁ h.capy₂

#print axioms divided_lengths
end
end QRH.Cycle092.OrderedPairActualRestored
