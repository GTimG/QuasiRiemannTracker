/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual native collision/inverse leaves, with compensated original mark base,
identified with their direct canonical sources at all four residual lengths. -/
import Candidate.C092.transport.OrderedPairActualRestoredProfiles
import Candidate.C092.transport.TwistedRawBallCanonicalRows
import Candidate.C092.transport.TwistedRawBallRootReindex
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.OrderedPairActualRestored
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFiniteProfileExceptional
open CenteredMomentLattice CenteredMomentCommonMaskEnergy CenteredMomentNaturalFixedRaySource
open QRH.Record1252270103KernelMass QRH.Record1252270103TwoIdeal
open QRH.SilDensitySplit.CubeFree.FP
open NativeMaskedEnergy
open MixedCanonicalSource RestoredRootDictionary RestoredInitialSource
open Candidate.FourthPower.KernelCollisionEnergy
open QRH.SilDensitySplit.CubeFree.FP.RestorationFamily
open QRH.SilDensitySplit.CubeFree.FP.RestorationCollisionEnergy
open Candidate.FourthPower.NativeFiniteHoles
open QRH.Cycle092.TwistedRawBallRootProducer
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {α:Type} [Fintype α]
variable (M:Id) [NeZero M] (Hr:Subgroup (O⧸M)ˣ)
variable (hHr:RayOrthogonality.globalUnits M ≤ Hr)
variable (Z:ℝ) (hZ:1<Z) (W:ℝ→ℂ) (hW:Continuous W)
variable (hWs:Function.support W ⊆ Set.Icc (1:ℝ) 2)
variable (base first:Character) (θ:α→RayQuotient.Characters M Hr) (w freq:α→ℝ)
variable (hw:∀i,0 ≤ w i) (hwcap:∀i,w i ≤ 1/6)
variable (t:ℝ) (p:Profiles (1/4) (9/4))
variable (r:Setoid α) (tc:{q // ¬singletonBlock r q}→primeEnclosure Z)
variable (A:Finset {q // singletonBlock r q}) (ti:A→primeEnclosure Z)

def restoredMarksData : RestoredRootSource.Data M Hr (remainingSet r A) :=
  originalCanonicalMarks M Hr Z 8 hZ le_rfl W hW hWs base first
    (fun i=>θ i.val) (fun i=>w i.val) (fun i=>freq i.val)
    (fun i=>hw i.val) (fun i=>hwcap i.val)
    (fun _=>restorationHoles r (primeEnclosure Z) tc A ti) t p

def actualRestoredRow (χ:Character) (ω₁ ω₂:Id→*₀ℂ) (V₁ V₂:ℝ→ℂ) (X₁ X₂:ℝ) : ℂ :=
  restoredRow χ ω₁ ω₂ (primeEnclosure Z)
    (fun q:Remaining r A=>initialPool M Hr w Z (singletonRepresentative r q.val))
    (crossBeta A (primeEnclosure Z) ti
      (collisionBeta r (primeEnclosure Z) tc
        (initialCoefficient M Hr hHr (base.product first.inverse) θ W w
          (fun _=>(33/50:ℝ)) freq Z t)))
    (fun q=>Z^(w (singletonRepresentative r q.val))) V₁ V₂ (9/4) X₁ X₂

theorem actual_restored_row_canonical (χ:Character) (ω₁ ω₂:Id→*₀ℂ)
    (V₁ V₂:ℝ→ℂ) (X₁ X₂:ℝ) :
    let d:=restoredMarksData M Hr Z hZ W hW hWs base first θ w freq hw hwcap t p r tc A ti
    actualRestoredRow M Hr hHr Z W base first θ w freq t r tc A ti χ ω₁ ω₂ V₁ V₂ X₁ X₂ =
      restoredRow χ ω₁ ω₂ (primeEnclosure Z) d.pool
        (fun i I=>slotCoefficient (d.characters hHr) d.R₀ d.t i I*
          slotProfile d.W (33/50) (d.freq i) (I.absNorm/(d.Z^(d.w i))))
        (fun i=>d.Z^(d.w i)) V₁ V₂ (9/4) X₁ X₂ := by
  dsimp only
  have he:=colored_restored_on_original_subset r (primeEnclosure Z) tc A ti χ ω₁ ω₂
    (initialPool M Hr w Z)
    (fun i=>relativeCharacter M Hr hHr (base.product first.inverse) (θ i)) W
    (fun i=>Z^(w i)) (fun _=>(33/50:ℝ)) freq t
    (KernelRowPools.supportedRectangle (primeEnclosure Z) (9/4) X₁ X₂) V₁ V₂ X₁ X₂
  unfold actualRestoredRow restoredRow
  convert he using 1 <;> rfl

theorem actual_restored_signed_source (χ:Character) (ω₁ ω₂:Id→*₀ℂ)
    (hoff:∀I,¬Supported I→idealCoeff χ I=0)
    (X₁ X₂ Y₁ Y₂ t₁ t₂:ℝ)
    (hX₁:0<X₁) (hX₂:0<X₂) (hY₁:0<Y₁) (hY₂:0<Y₂)
    (hprod:X₁*X₂=Y₁*Y₂)
    (hx₁:X₁ ≤ Z) (hx₂:X₂ ≤ Z) (hy₁:Y₁ ≤ Z) (hy₂:Y₂ ≤ Z) :
    let d:=restoredMarksData M Hr Z hZ W hW hWs base first θ w freq hw hwcap t p r tc A ti
    let V₁:=normPowerProfile (p.profile 0) (1/4) (9/4) (by norm_num)
      (p.support 0) ((p.profile 0).smooth ⊤) t₁
    let V₂:=normPowerProfile (p.profile 1) (1/4) (9/4) (by norm_num)
      (p.support 1) ((p.profile 1).smooth ⊤) t₂
    actualRestoredRow M Hr hHr Z W base first θ w freq t r tc A ti χ ω₁ ω₂ V₁ V₂ X₁ X₂-
      actualRestoredRow M Hr hHr Z W base first θ w freq t r tc A ti χ ω₁ ω₂ V₁ V₂ Y₁ Y₂ =
      sourceSignedRow (canonicalPairSource M Hr hHr d X₁ X₂ Y₁ Y₂ t₁ t₂
        hX₁ hX₂ hY₁ hY₂ hprod hx₁ hx₂ hy₁ hy₂) (by norm_num) χ ω₁ ω₂ := by
  dsimp only
  rw [actual_restored_row_canonical M Hr hHr Z hZ W hW hWs base first θ w freq hw hwcap t p r tc A ti,
    actual_restored_row_canonical M Hr hHr Z hZ W hW hWs base first θ w freq hw hwcap t p r tc A ti]
  let d:=restoredMarksData M Hr Z hZ W hW hWs base first θ w freq hw hwcap t p r tc A ti
  have hsource:=sourceSignedRow_eq_weighted
    (canonicalPairSource M Hr hHr d X₁ X₂ Y₁ Y₂ t₁ t₂
      hX₁ hX₂ hY₁ hY₂ hprod hx₁ hx₂ hy₁ hy₂) (by norm_num) (by norm_num)
    (canonicalPairSource_original_enclosure M Hr hHr d X₁ X₂ Y₁ Y₂ t₁ t₂
      hX₁ hX₂ hY₁ hY₂ hprod hx₁ hx₂ hy₁ hy₂) rfl rfl rfl χ ω₁ ω₂ hoff
  rw [hsource]
  exact (canonicalPairSource_original_signed M Hr hHr d X₁ X₂ Y₁ Y₂ t₁ t₂
    hX₁ hX₂ hY₁ hY₂ hprod hx₁ hx₂ hy₁ hy₂ χ ω₁ ω₂ hoff).symm

#print axioms actual_restored_row_canonical
#print axioms actual_restored_signed_source
end
end QRH.Cycle092.OrderedPairActualRestored
