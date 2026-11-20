/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Native canonical mark data with all four actual positive residual lengths.
   No ordering of the reference coordinates or lower comparison threshold is imposed. -/
import Candidate.C092.transport.TwistedRawBallCanonicalProducer
import Candidate.C092.transport.TwistedRawBallRootEnclosure
import Candidate.C092.transport.TwistedRawBallRootFinite
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.TwistedRawBallRootProducer
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103KernelMass
open QRH.SilDensitySplit.CubeFree.FP
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations MixedFirstActualNonexceptional
open MixedInnerExceptionalBlock MixedCanonicalSource MixedLiveNormalization
open ReferencePrimeEnclosure RestoredInitialSource
open CenteredMomentLattice CenteredMomentTwist
open KernelRowPools
open QRH.Cycle092.TwistedRawSource
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι]
variable (M : Id) [NeZero M] (Hr : Subgroup (O⧸M)ˣ)
variable (hHr : RayOrthogonality.globalUnits M ≤ Hr)
variable (r : RestoredRootSource.Data M Hr ι)
variable (X₁ X₂ Y₁ Y₂ t₁ t₂ : ℝ)
variable (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
variable (hprod : X₁*X₂=Y₁*Y₂)
variable (hcapX₁ : X₁ ≤ r.Z) (hcapX₂ : X₂ ≤ r.Z) (hcapY₁ : Y₁ ≤ r.Z) (hcapY₂ : Y₂ ≤ r.Z)

local notation "src" => canonicalPairSource M Hr hHr r X₁ X₂ Y₁ Y₂ t₁ t₂
  hX₁ hX₂ hY₁ hY₂ hprod hcapX₁ hcapX₂ hcapY₁ hcapY₂

/-- Exact canonical signed leaf on the ORIGINAL supplying-prime enclosure.
    No absolute values, phases, marked holes or independent colors are dropped. -/
theorem canonicalPairSource_original_signed (χ : Character) (ω₁ ω₂ : Id→*₀ℂ)
    (hoff : ∀I,¬Supported I→idealCoeff χ I=0) :
    let β := fun i I=>slotCoefficient (r.characters hHr) r.R₀ r.t i I*
      slotProfile r.W (33/50) (r.freq i) (I.absNorm/(r.Z^(r.w i)))
    let V₁ := normPowerProfile (r.p.profile 0) (1/4) (9/4) (by norm_num)
      (r.p.support 0) ((r.p.profile 0).smooth ⊤) t₁
    let V₂ := normPowerProfile (r.p.profile 1) (1/4) (9/4) (by norm_num)
      (r.p.support 1) ((r.p.profile 1).smooth ⊤) t₂
    coloredWeightedRow src (by norm_num) ω₁ ω₂ χ =
      restoredRow χ ω₁ ω₂ (primeEnclosure r.Z) r.pool β (fun i=>r.Z^(r.w i)) V₁ V₂ (9/4) X₁ X₂-
        restoredRow χ ω₁ ω₂ (primeEnclosure r.Z) r.pool β (fun i=>r.Z^(r.w i)) V₁ V₂ (9/4) Y₁ Y₂ := by
  dsimp only
  let β := fun i I=>slotCoefficient (r.characters hHr) r.R₀ r.t i I*
    slotProfile r.W (33/50) (r.freq i) (I.absNorm/(r.Z^(r.w i)))
  let V₁ := normPowerProfile (r.p.profile 0) (1/4) (9/4) (by norm_num)
    (r.p.support 0) ((r.p.profile 0).smooth ⊤) t₁
  let V₂ := normPowerProfile (r.p.profile 1) (1/4) (9/4) (by norm_num)
    (r.p.support 1) ((r.p.profile 1).smooth ⊤) t₂
  have hβpool : ∀i,r.pool i ⊆ primeValues (primeEnclosure r.Z) := fun i=>r.pool_original_enclosed i
  have hss : primeEnclosure r.Z ⊆ enclosure (16*r.Z^r.Lcap) :=
    RestoredRootSource.original_enclosure_subset r.Z r.Lcap r.hZ r.hLcap
  have h₁ : Function.support (V₁:ℝ→ℂ) ⊆ Set.Iic (9/4) :=
    (normPowerProfile_support _ _ _ _ _ _ _).trans (fun x hx=>(r.p.support 0 hx).2)
  have h₂ : Function.support (V₂:ℝ→ℂ) ⊆ Set.Iic (9/4) :=
    (normPowerProfile_support _ _ _ _ _ _ _).trans (fun x hx=>(r.p.support 1 hx).2)
  have hS (A B : ℝ) (hA : A ≤ r.Z) (hB : B ≤ r.Z) :
      ∀I,Supported I→((I.absNorm:ℝ) ≤ (9/4)*A ∨ (I.absNorm:ℝ) ≤ (9/4)*B)→
      primeSupport I ⊆ primeValues (primeEnclosure r.Z) := by
    intro I hI hlen
    apply support_enclosed _ I hI
    have hpow : r.Z ≤ r.Z^(2:ℝ) := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le r.hZ.le (show (1:ℝ) ≤ 2 by norm_num)
    rcases hlen with hlen|hlen
    · nlinarith [hA.trans hpow]
    · nlinarith [hB.trans hpow]
  have hx := colored_row_enclosure (primeEnclosure r.Z) (enclosure (16*r.Z^r.Lcap)) hss
    χ ω₁ ω₂ r.pool β (fun i=>r.Z^(r.w i)) hβpool V₁ V₂ (9/4) X₁ X₂ hX₁ hX₂
    h₁ h₂ hoff (hS X₁ X₂ hcapX₁ hcapX₂)
  have hy := colored_row_enclosure (primeEnclosure r.Z) (enclosure (16*r.Z^r.Lcap)) hss
    χ ω₁ ω₂ r.pool β (fun i=>r.Z^(r.w i)) hβpool V₁ V₂ (9/4) Y₁ Y₂ hY₁ hY₂
    h₁ h₂ hoff (hS Y₁ Y₂ hcapY₁ hcapY₂)
  have he := sourceSignedRow_eq_weighted src (by norm_num) (by norm_num)
    (canonicalPairSource_original_enclosure M Hr hHr r X₁ X₂ Y₁ Y₂ t₁ t₂
      hX₁ hX₂ hY₁ hY₂ hprod hcapX₁ hcapX₂ hcapY₁ hcapY₂)
    rfl rfl rfl χ ω₁ ω₂ hoff
  change (restoredRow χ ω₁ ω₂ (enclosure (16*r.Z^r.Lcap)) r.pool β
      (fun i=>r.Z^(r.w i)) V₁ V₂ (9/4) X₁ X₂-
      restoredRow χ ω₁ ω₂ (enclosure (16*r.Z^r.Lcap)) r.pool β
      (fun i=>r.Z^(r.w i)) V₁ V₂ (9/4) Y₁ Y₂)=_ at he
  rw [←hx,←hy] at he
  exact he.symm

#print axioms canonicalPairSource_original_signed
end
end QRH.Cycle092.TwistedRawBallRootProducer
