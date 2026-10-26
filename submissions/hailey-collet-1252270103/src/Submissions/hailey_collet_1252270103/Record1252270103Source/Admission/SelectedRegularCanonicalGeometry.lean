/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Canonical initial global-face geometry discharges actual Newton corner and
fixed collected-mask gates before all moving profiles and selected rows. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.SelectedRegularCanonicalGeometryData
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedRegularCanonicalGeometry
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators ContDiff
open Filter HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentAmplificationChildInput CenteredMomentAddedZeroUniform CenteredMomentCanonicalFirst
open Cycle61Moment Cycle61InitialMass CenteredMomentSecondHeightFamily
open OAI.SevenEighths.Record1252270103Source QRH.Record1252270103Low
open Record12518109Raw
open SelectedHighCofactorFamily
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq ι:=Classical.decEq _
local instance (rayM:Ideal O)[NeZero rayM]:Finite (O⧸rayM):=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

section Initial
variable {ι:Type}[Fintype ι]
variable (rayM:Ideal O)[NeZero rayM](H:Subgroup (O⧸rayM)ˣ)(hH:RayOrthogonality.globalUnits rayM≤H)
variable (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(hsW:Function.support W⊆Set.Icc (1:ℝ) 2)
variable (Z:ℝ)(hZ:1<Z)(η η₀:Character)(R₀:Ideal O)
variable (θ:ι→RayQuotient.Characters rayM H)(w v:ι→ℝ)(t:ℝ)(p:Profiles (1/4) (9/4))
variable (X₁ X₂ Y₁ Y₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hY₁:0<Y₁)(hY₂:0<Y₂)(hprod:Y₁*Y₂=X₁*X₂)
local notation "s"=>initialInput rayM H hH W hW hsW Z (zero_lt_one.trans hZ) η η₀ R₀ θ w v t
  p (by norm_num) X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod

include rayM H hH W hW hsW hZ η η₀ R₀ θ v t p hX₁ hX₂ hY₁ hY₂ hprod
theorem initial_long_corners (B lam cap r:ℝ)(hB:B≤1)(hlam:1≤lam)(hw:∀i,0≤w i)
    (hadm:(globalFace B lam cap).Admissible (length Z X₁) (length Z X₂) (∑i,w i) 1)
    (hr:0≤r)(hl1:Z^r≤X₁)(hl2:Z^r≤X₂)(href:Y₂=Z^r):
    X₁≤Z ∧ X₂≤Z ∧ Y₁≤Z ∧ Y₂≤Z ∧ X₁*X₂≤Z := by
  have hv:=InitialPhysical.initial_volume_cap rayM H hH W hW hsW Z (zero_lt_one.trans hZ) η η₀ R₀
    θ w v t p X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod B lam cap hZ hB hlam hw hadm
  have hp:1≤∏i,Z^(w i):=Finset.one_le_prod₀ (fun i _=>Real.one_le_rpow hZ.le (hw i))
  have hraw:X₁*X₂≤volume s:=le_mul_of_one_le_right (mul_pos hX₁ hX₂).le hp
  have hcap:X₁*X₂≤Z:=hraw.trans hv
  have hc:=RegularResidualGeometry.long_corner_caps Z X₁ X₂ r hZ.le hX₁ hX₂ hr hl1 hl2 hcap
  have he:Y₁=X₁*X₂/Z^r:=(eq_div_iff (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) r).ne').mpr
    (by simpa only [←href] using hprod)
  exact ⟨hc.2.2.2.1,hc.2.2.2.2.1,he.symm ▸ hc.2.2.2.2.2.1,href.symm ▸ hc.2.2.2.2.2.2,hcap⟩
end Initial

theorem eventually_canonical_selected_geometry (ηanchor:Character)(R₀:Ideal O)(hR₀:R₀≠0):
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀{ι:Type}[Fintype ι]
      (rayM:Ideal O)[NeZero rayM](H:Subgroup (O⧸rayM)ˣ)(hH:RayOrthogonality.globalUnits rayM≤H)
      (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(hsW:Function.support W⊆Set.Icc (1:ℝ) 2)
      (η₀:Character)(θ:ι→RayQuotient.Characters rayM H)(w v:ι→ℝ)(t:ℝ)(p:Profiles (1/4) (9/4))
      (X₁ X₂ Y₁ Y₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hY₁:0<Y₁)(hY₂:0<Y₂)(hprod:Y₁*Y₂=X₁*X₂)
      (B lam cap r:ℝ),B≤1→1≤lam→(∀i,0≤w i)→
      (globalFace B lam cap).Admissible (length Z X₁) (length Z X₂) (∑i,w i) 1→
      0≤r→Z^r≤X₁→Z^r≤X₂→Y₂=Z^r→
      ∀(hZ:1<Z),
      let s:=initialInput rayM H hH W hW hsW Z (zero_lt_one.trans hZ) ηanchor η₀ R₀ θ w v t
        p (by norm_num) X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
      ∀(reflected second:Bool)(l:FirstSourceLabel)(C₂ D₂ R:Ideal O)
        (sel:Selection s reflected second l C₂ D₂ R)
        (L:Ideal O),L≠0→(L.absNorm:ℝ)≤Z^(4:ℝ)→
      ∀(P S A:Finset (Ideal O))(depth:ℕ)(amp:ℝ),S⊆P→A⊆S→S.card≤depth→
        0≤amp→(depth:ℝ)*amp<5→(∀q∈P,q≠0)→(∀q∈P,(q.absNorm:ℝ)≤Z^amp)→
      CornerBounds sel.finalInput S A Z ∧
      corner₁ sel.finalInput S A true*corner₂ sel.finalInput S A true=
        corner₁ sel.finalInput S A false*corner₂ sel.finalInput S A false ∧
      (geometryRawFixedMask s R₀*L)*((newtonDivisorPair S A).1*(newtonDivisorPair S A).2)≠0 ∧
      (((geometryRawFixedMask s R₀*L)*((newtonDivisorPair S A).1*(newtonDivisorPair S A).2)).absNorm:ℝ)≤Z^(10:ℝ):=by
  filter_upwards [eventually_mask_ten ηanchor R₀ hR₀,eventually_ge_atTop ((9/4:ℝ)^2)] with Z hm hlarge
  refine ⟨hm.1,?_⟩
  intro ι inst rayM instM H hH W hW hsW η₀ θ w v t p X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
    B lam cap r hB hlam hw hadm hr hl1 hl2 href hZ s reflected second l C₂ D₂ R sel L hL hLcap
    P S A depth amp hS hA hdepth hamp hcost hp hpool
  have hc:=initial_long_corners rayM H hH W hW hsW Z hZ ηanchor η₀ R₀ θ w v t p
    X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod B lam cap r hB hlam hw hadm hr hl1 hl2 href
  have hs:=selected_newton_corners s reflected second l C₂ D₂ R sel Z hZ hlarge
    hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2 P S A hS hA hp
  have hmask:=hm.2 ι s rfl L hL hLcap P S A depth amp hS hA hdepth hamp hcost hp hpool
  exact ⟨hs.1,hs.2,hmask.1,hmask.2⟩
end
end QRH.Record1252270103Source.Admission.SelectedRegularCanonicalGeometry
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularCanonicalGeometry.initial_long_corners
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularCanonicalGeometry.eventually_canonical_selected_geometry
