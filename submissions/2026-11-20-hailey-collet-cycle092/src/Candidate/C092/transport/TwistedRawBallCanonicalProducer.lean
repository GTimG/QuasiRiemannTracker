/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Native canonical mark data with all four actual positive residual lengths.
   No ordering of the reference coordinates or lower comparison threshold is imposed. -/
import Candidate.C092.transport.TwistedRawBallRootProducer
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
open ReferencePrimeEnclosure
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

/-- The original canonical mark datum is retained verbatim. The finite source
    uses the actual two residual rectangles and their actual common volume. -/
def canonicalPairSource : Source ι (1/4) (9/4) :=
  {r.source hHr with
    X₁:=X₁
    X₂:=X₂
    Y₁:=Y₁
    Y₂:=Y₂
    T:=X₁*X₂
    t₁:=t₁
    t₂:=t₂
    L:=min (min X₁ X₂) (min Y₁ Y₂)
    U₁:=max X₁ Y₁
    U₂:=max X₂ Y₂
    hL:=lt_min (lt_min hX₁ hX₂) (lt_min hY₁ hY₂)
    hX₁:=(min_le_left _ _).trans (min_le_left _ _)
    hX₂:=(min_le_left _ _).trans (min_le_right _ _)
    hY₁:=(min_le_right _ _).trans (min_le_left _ _)
    hY₂:=(min_le_right _ _).trans (min_le_right _ _)
    hXU₁:=le_max_left _ _
    hXU₂:=le_max_left _ _
    hYU₁:=le_max_right _ _
    hYU₂:=le_max_right _ _
    hpX:=rfl
    hpY:=hprod.symm
    henclose:=by
      intro I hI hlen
      simp only [RestoredRootSource.Data.source,one_mul,map_one,Nat.cast_one,div_one] at hlen
      have hZL : r.Z ≤ r.Z^r.Lcap := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le r.hZ.le (show (1:ℝ) ≤ r.Lcap by linarith [r.hLcap])
      apply support_enclosed _ I hI
      rcases hlen with hlen|hlen
      · have hm : max X₁ Y₁ ≤ r.Z := max_le hcapX₁ hcapY₁
        nlinarith [hm.trans hZL]
      · have hm : max X₂ Y₂ ≤ r.Z := max_le hcapX₂ hcapY₂
        nlinarith [hm.trans hZL]}

local notation "src" => canonicalPairSource M Hr hHr r X₁ X₂ Y₁ Y₂ t₁ t₂
  hX₁ hX₂ hY₁ hY₂ hprod hcapX₁ hcapX₂ hcapY₁ hcapY₂

theorem canonicalPairSource_canonical :
    Canonical M Hr hHr r.W 16 r.Lcap r.Z r.η₀ r.θ r.w
      (fun _=>33/50) r.freq r.t r.R₀ src := by
  exact r.source_canonical hHr

theorem canonicalPairSource_original_enclosure : OriginalEnclosure src := by
  intro I hI hlen
  simpa only [canonicalPairSource,RestoredRootSource.Data.source,one_mul,map_one,Nat.cast_one,div_one] using
    (src).henclose I hI (by
      simpa only [canonicalPairSource,RestoredRootSource.Data.source,one_mul,map_one,Nat.cast_one,div_one] using hlen)

theorem canonicalPairSource_masks : (src).H=∅ ∧ (src).R=1 ∧ (src).d=(1,1) := ⟨rfl,rfl,rfl⟩

theorem canonicalPairSource_volume : sourceVolume src=X₁*X₂*∏i,r.Z^(r.w i) := rfl

theorem canonicalPairSource_lengths_lower (L : ℝ) (hL₁ : L ≤ X₁) (hL₂ : L ≤ X₂)
    (hL₃ : L ≤ Y₁) (hL₄ : L ≤ Y₂) : L ≤ (src).L := le_min (le_min hL₁ hL₂) (le_min hL₃ hL₄)

#print axioms canonicalPairSource_canonical
#print axioms canonicalPairSource_original_enclosure
#print axioms canonicalPairSource_masks
#print axioms canonicalPairSource_volume
#print axioms canonicalPairSource_lengths_lower
end
end QRH.Cycle092.TwistedRawBallRootProducer
