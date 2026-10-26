/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Canonical initial data discharge every first MAIN radius and projector cap.
The threshold precedes all moving columns, profiles and user heights. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.ExceptionalInitialGeometryBounds

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.ExceptionalPrice
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstAnnularMajorant CenteredMomentLogDyadic
open CenteredMomentAmplificationChildInput CenteredMomentSourceMass Cycle61InitialMass
open QRH.Record1252270103Low High.CoupledFirst Admission.FirstFamily InitialTruncated
local notation "O"=>HeckeFamily.O
local notation "source"=>High.CoupledFirst.geometryFirstSource
local instance initialGeometryUniformDecidable {α:Type*}:DecidableEq α:=Classical.decEq _

theorem eventually_initial_first_geometry (N:ℕ)(B lam cap ξ amp reserve:ℝ)
    (hB:B≤1)(hL:1≤lam)(hcap:cap≤1)(hξ:0<ξ)(hξ1:ξ≤1)
    (ha:0≤amp)(ha1:amp≤1)(hr:0≤reserve)(hr1:reserve≤1):
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀hZ:1<Z,
    ∀{α:Type}[Fintype α](rayM:Ideal O)[NeZero rayM]
      (H:Subgroup (O⧸rayM)ˣ)(hH:RayOrthogonality.globalUnits rayM≤H)
      (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(hsW:Function.support W⊆Set.Icc (1:ℝ) 2)
      (η η₀:Character)(R₀:Ideal O)(θ:α→RayQuotient.Characters rayM H)(w v:α→ℝ)(t:ℝ)
      (p:Profiles (1/4) (9/4))(X₁ X₂ Y₁ Y₂:ℝ)
      (hX₁:0<X₁)(hX₂:0<X₂)(hY₁:0<Y₁)(hY₂:0<Y₂)(hprod:Y₁*Y₂=X₁*X₂),
      Fintype.card α≤N→(∀i,0≤w i)→
      (globalFace B lam cap).Admissible (length Z X₁) (length Z X₂) (∑i,w i) 1→
      1≤Y₂→Y₂≤X₁→Y₂≤X₂→
    let s:=initialInput rayM H hH W hW hsW Z (zero_lt_one.trans hZ) η η₀ R₀ θ w v t
      p (by norm_num) X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
    ∀(modifier:Tuple α→ℂ)(reflected:Bool)(bin:ℤ×(Fin 5→ℤ))
      (j:FirstColumnIndex (source s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin)),
    let l:=firstLabel s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin j
    let radius:=literalFirstRadius reflected Z (volume s) Z ξ reserve l
    0<(source s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin j.1).H0 ∧
      0≤radius+6*amp ∧ radius+6*amp≤32 ∧
      (∀n∈bands (source s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin j.1).H0,
        dyadicScale n≤Z^radius) ∧
      j.2.1.val≠0 ∧ (j.2.1.val.absNorm:ℝ)≤Z^(4:ℝ) ∧
      Z^(radius+6*amp)=firstMainRadius reflected Z (volume s) Z ξ (3*amp) reserve l := by
  have hcaps:=eventually_initial_caps N B lam cap hB hL hcap
  have hfreq:=eventually_frequency_loss 32 ξ (by norm_num) hξ
  refine (hcaps.and hfreq).mono ?_
  rintro Z ⟨hc,hf⟩
  refine ⟨hc.1,?_⟩
  intro hZ α inst rayM instRay H hH W hW hsW η η₀ R₀ θ w v t p X₁ X₂ Y₁ Y₂
    hX₁ hX₂ hY₁ hY₂ hprod hN hw hadm hy₂ hl₁ hl₂ s modifier reflected bin j l radius
  have hd:=hc.2 hZ rayM H hH W hW hsW η η₀ R₀ θ w v t p X₁ X₂ Y₁ Y₂
    hX₁ hX₂ hY₁ hY₂ hprod hN hw hadm hy₂ hl₁ hl₂
  have hz₁:s.W₁ 0=0:=initial_plain_zero p (by norm_num) 0
  have hz₂:s.W₂ 0=0:=initial_plain_zero p (by norm_num) 1
  have hp:∀I∈finiteColumns (Fintype.piFinset s.pools),(I.absNorm:ℝ)≤Z^(4:ℝ):=by
    intro I hI
    apply hd.2.2.2.2 I
    simpa only [finiteColumns,Fintype.mem_piFinset,Finset.mem_image] using hI
  have hb:=actual_first_radius_envelope s modifier R₀ 1 Z Z ξ reserve
    (zero_lt_one.trans hZ) hZ hr reflected bin j
  have hu:=actual_first_radius_upper s modifier R₀ 1 Z ξ amp reserve hZ (by simp) hz₁ hz₂
    hd.2.1 hd.2.2.2.1 ha1 hr1 (hf.2.2.le.trans hξ1) reflected bin j
  have hproj:=actual_first_projector_cap s modifier R₀ 1 Z Z ξ (Z^(4:ℝ))
    (zero_lt_one.trans hZ) hp bin j
  have hh:=actual_first_H0_and_frequency s modifier R₀ 1 Z Z ξ (zero_lt_one.trans hZ) bin j
  exact ⟨zero_lt_one.trans hh.1,add_nonneg hb.1 (mul_nonneg (by norm_num) ha),
    hu,hb.2,hproj.1,hproj.2,literal_first_main_radius reflected Z (volume s) Z ξ amp reserve l⟩

end
end QRH.Record1252270103Source.ExceptionalPrice
#print axioms QRH.Record1252270103Source.ExceptionalPrice.eventually_initial_first_geometry
