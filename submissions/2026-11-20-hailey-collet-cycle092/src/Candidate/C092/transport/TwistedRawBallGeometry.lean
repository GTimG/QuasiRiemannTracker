/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Original geometric first-band bounds on true colored active labels. -/
import Candidate.C092.transport.TwistedRawBallRetained
import Submissions.sil_density_split_20261026.CubeFree.FP.MixedFirstActualBandGeometry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.TwistedRawBall
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSourceRow CenteredMomentActiveSource CenteredMomentSupportedCorrelation
open CenteredMomentCanonicalFirst CenteredMomentFirstPhysicalSource CenteredMomentFirstScale
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentFirstSectorTransform
open CenteredMomentFirstDiscardedEnergy
open CenteredMomentSecondBlockAggregate CenteredMomentLogDyadic
open CenteredMomentFirstSectors
open CenteredMomentWholeDivisorShell CenteredMomentSectorLocalization CenteredMomentMobiusRegroup
open QRH.SilDensitySplit.CubeFree.FP
open QRH.Cycle092.TwistedRawSource
open MixedPrincipalPair MixedPrincipalWindow MixedOriginalNormCap MixedOriginalTail
open MixedOriginalTailCaps MixedPrincipalPoolCaps MixedInnerExceptionalBlock
open MixedFirstCommonSum MixedFirstPhysicalApplication MixedFirstRetainedFixed
open MixedFirstPaidRetained MixedFirstCutoffs MixedFirstGeometricCaps
open MixedFirstExceptionalWindow MixedFirstExceptionalNormalization
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type u} [Fintype ι] {a b : ℝ}

open MixedFirstActualBandGeometry

structure BandGeometry (s : Source ι a b) (ha : 0<a) (ω₁ ω₂ : Id→ℂ) (seed : Id)
    (K Z ξ κ W Tsecond H Btail Bfrequency : ℝ) : Prop where
  radius : ∀p : Labels s ha ω₁ ω₂ seed,∀E : Finset (CommonIndex p.val.1 p.val.2),
    firstRadius s p.val.1 p.val.2 E K Z ξ ≤ Z^Bfrequency
  artificial : ∀p : Labels s ha ω₁ ω₂ seed,
    ∀Dart∈artificialDivisors s p.val.1 p.val.2
      (commonLabels_supported (activeSource (sourceColumns s) (sourceColumn s ha ω₁ ω₂ seed)) p).2.1,
      (UniqueFactorizationMonoid.moebius Dart:ℂ)≠0→(Dart.absNorm:ℝ) ≤ Z^Btail
  children : ∀p : Labels s ha ω₁ ω₂ seed,∀E∈inactiveSubsets p.val.1 p.val.2,
    ∀n : Blocks (effectiveScale p.val.1 p.val.2 E K)
      (firstRadius s p.val.1 p.val.2 E K Z ξ) (H/p.val.1.absNorm) (H/p.val.2.absNorm),
    1/2 ≤ dyadicScale (n 1)→
    let Kc:=MixedFirstExceptionalWindow.childScale Z κ (n 1)
    Kc ≤ Z^Btail ∧ sharpSupport s^2/(16*Kc*W^4) ≤ Tsecond ∧
    ∀z∈fixedRows (firstRadius s p.val.1 p.val.2 E K Z ξ) (fun i=>(n i:ℤ)),
      (Ideal.absNorm (Ideal.span {z}):ℝ) ≤ Kc


/-- Original scale cap B produces a full common/pool cap 3B+1.
The already checked cutoff theorem is therefore used at 3B+1, rather
than incorrectly feeding a 3B+1 common norm into its B input. -/
theorem uniform_actual_band_geometry (N : ℕ) (b B ξfirst ξsecond κ : ℝ)
    (hb : 0<b) (hB : 1 ≤ B) (hξfirst : 0 ≤ ξfirst) (hξsecond : 0<ξsecond) (hκ : 0<κ) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(ι : Type u) [Fintype ι],∀a : ℝ,∀s : Source ι a b,∀ha : 0<a, ∀ω₁ ω₂ : Id→ℂ,
      Fintype.card ι ≤ N→Z^(-B) ≤ s.L→
      s.X₁ ≤ Z^B→s.X₂ ≤ Z^B→s.Y₁ ≤ Z^B→s.Y₂ ≤ Z^B→(∏i,s.P i) ≤ Z^B→
    ∀K W : ℝ,0<K→0<W→K ≤ Z^B→K⁻¹ ≤ Z^B→W ≤ Z^B→W⁻¹ ≤ Z^B→
    poolCap s ≤ Z^(sourceExponent B) ∧
    sourceNormCap s.P b s.T s.d ≤ Z^(sourceExponent B) ∧
    ∀seed : Id,∀H : ℝ,
      BandGeometry s ha ω₁ ω₂ seed K Z ξfirst κ W (secondCutoff (sourceExponent B) Z) H
        (tailExponent (sourceExponent B) ξfirst κ)
        (tailExponent (sourceExponent B) ξfirst κ+ξfirst/2) := by
  have hB0 : 1 ≤ sourceExponent B := by unfold sourceExponent;linarith
  have hBB0 : B ≤ sourceExponent B := by unfold sourceExponent;linarith
  have htail : sourceExponent B ≤ tailExponent (sourceExponent B) ξfirst κ := by
    unfold tailExponent secondExponent childExponent sourceExponent
    linarith
  filter_upwards [eventually_source_caps N b B B 1 (by norm_num),
    uniform_actual_cutoffs N b (sourceExponent B) ξfirst ξsecond κ hb hB0 hξfirst hξsecond hκ,
    eventually_padding κ hκ]
      with Z hcaps hcut hpad
  refine ⟨hcaps.1,?_⟩
  intro ι instι a s ha ω₁ ω₂ hcard hmin hX₁ hX₂ hY₁ hY₂ hP K W hK hW hKcap hKinv hWcap hWinv
  have hZ := hcaps.1
  have hZ0 := zero_lt_one.trans hZ
  have hscale : Z^B ≤ Z^(sourceExponent B) :=
    Real.rpow_le_rpow_of_exponent_le hZ.le hBB0
  have hmin0 : Z^(-sourceExponent B) ≤ s.L :=
    (Real.rpow_le_rpow_of_exponent_le hZ.le (neg_le_neg hBB0)).trans hmin
  have hc := hcaps.2 ι a s hcard hX₁ hX₂ hY₁ hY₂ hP
  have hpool : poolCap s ≤ Z^(sourceExponent B) := by
    simpa only [sourceExponent,show 2*B+B+1=3*B+1 by ring] using hc.1
  have hsource : sourceNormCap s.P b s.T s.d ≤ Z^(sourceExponent B) := by
    simpa only [sourceExponent,show 2*B+B+1=3*B+1 by ring] using hc.2
  refine ⟨hpool,hsource,?_⟩
  intro seed H
  have hdata (p : Labels s ha ω₁ ω₂ seed) :
      (p.val.1.absNorm:ℝ) ≤ Z^(sourceExponent B) ∧ (p.val.2.absNorm:ℝ) ≤ Z^(sourceExponent B) :=
    commonLabel_norm_bounds (sourceColumns s) (sourceColumn s ha ω₁ ω₂ seed) _
      (fun I _ hI=>(sourceColumn_cap s ha ω₁ ω₂ seed I hI).2.trans hsource)
      p.val.1 p.val.2 p.property
  have hactual (p : Labels s ha ω₁ ω₂ seed) (E : Finset (CommonIndex p.val.1 p.val.2)) :=
    hcut.2 ι a s hcard hmin0 (hX₁.trans hscale) (hX₂.trans hscale)
      (hY₁.trans hscale) (hY₂.trans hscale) (hP.trans hscale) K W hK hW
      (hKcap.trans hscale) (hKinv.trans hscale) (hWcap.trans hscale) (hWinv.trans hscale)
      p.val.1 p.val.2 1
      (commonLabels_supported (activeSource (sourceColumns s) (sourceColumn s ha ω₁ ω₂ seed)) p).1
      (commonLabels_supported (activeSource (sourceColumns s) (sourceColumn s ha ω₁ ω₂ seed)) p).2
      (commonLabels_data _ _ p.val.1 p.val.2 p.property).2.2
      (hdata p).1 (hdata p).2
      (by simpa only [map_one,Nat.cast_one] using Real.one_le_rpow hZ.le (zero_le_one.trans hB0)) E
  constructor
  · intro p E
    obtain ⟨_,_,_,_,_,_,htcap,_,_,_,_,_,_,_⟩ := hactual p E
    rw [actual_radius_eq,frequencyRadius]
    apply (mul_le_mul_of_nonneg_right htcap (Real.rpow_nonneg hZ0.le _)).trans_eq
    exact (Real.rpow_add hZ0 _ _).symm
  · intro p Dart hDart hμ
    exact ((artificial_norm s hb.le p.val.1 p.val.2
      (commonLabels_supported (activeSource (sourceColumns s) (sourceColumn s ha ω₁ ω₂ seed)) p).2.1
      Dart hDart).2.trans hpool).trans (Real.rpow_le_rpow_of_exponent_le hZ.le htail)
  · intro p E hE n hdy
    obtain ⟨_,_,_,hxcap,_,_,_,_,_,_,_,_,_,hchildren⟩ := hactual p E
    have hn := block_retained (effectiveScale p.val.1 p.val.2 E K)
      (firstRadius s p.val.1 p.val.2 E K Z ξfirst)
      (H/p.val.1.absNorm) (H/p.val.2.absNorm) n
    have hn' : Retained
        (frequencyRadius (firstCutoff p.val.1 p.val.2 E K (sourceVolume s)) Z ξfirst)
        (n 1 : ℤ) :=
      (congrArg (fun r : ℝ => Retained r (n 1 : ℤ))
        (actual_radius_eq s p.val.1 p.val.2 E K Z ξfirst)).mp hn
    obtain ⟨_,_,hKL,_,_,_,_,_,_⟩ := hchildren (n 1) hn'
    have hlive := childScale_live Z κ hZ hpad (n 1) hdy
    have hK0 : 0<childScale Z κ (n 1) := zero_lt_one.trans_le hlive.1
    have h7 : (childScale Z κ (n 1))⁻¹ ≤ Z^(7*sourceExponent B) :=
      (inv_le_one_of_one_le₀ hlive.1).trans
        (Real.one_le_rpow hZ.le (by linarith))
    refine ⟨(childScale_le_nominal _ _ E K (sourceVolume s) Z κ hZ (n 1)).trans hKL,
      fourth_cutoff_cap Z (sourceExponent B) _ _ W hZ (sharp_support_pos s hb).le hK0 hW
        hxcap h7 (hWinv.trans hscale),?_⟩
    intro z hz
    have hza : z∈annularRows (n 1 : ℤ) :=
      fixedRows_annular (firstRadius s p.val.1 p.val.2 E K Z ξfirst)
        (fun i => (n i : ℤ)) hz
    exact hlive.2 z hza

#print axioms uniform_actual_band_geometry
end
end QRH.Cycle092.TwistedRawBall
