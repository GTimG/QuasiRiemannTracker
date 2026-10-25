/- Copyright (c) 2026 Sil. Apache-2.0.
Construct the literal retained-band geometry from original scalar caps.
No common-label, artificial-divisor, row, or child-energy cap is assumed.
Full ideal norms, both child scales and the exact first radius survive.
-/
import Candidate.SilPrior.FourthPower.MixedFirstPaidRetained
import Candidate.SilPrior.FourthPower.MixedFirstCutoffs
import Candidate.SilPrior.FourthPower.MixedPrincipalPoolCaps

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.MixedFirstActualBandGeometry
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSourceRow CenteredMomentActiveSource CenteredMomentSupportedCorrelation
open CenteredMomentCanonicalFirst CenteredMomentFirstPhysicalSource CenteredMomentFirstScale
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentFirstSectorTransform
open CenteredMomentFirstSectors
open CenteredMomentWholeDivisorShell CenteredMomentSectorLocalization CenteredMomentMobiusRegroup
open MixedPrincipalPair MixedPrincipalWindow MixedOriginalNormCap MixedOriginalTail
open MixedOriginalTailCaps MixedPrincipalPoolCaps MixedInnerExceptionalBlock
open MixedFirstCommonSum MixedFirstPhysicalApplication MixedFirstRetainedFixed
open MixedFirstPaidRetained MixedFirstCutoffs MixedFirstGeometricCaps
open MixedFirstExceptionalWindow MixedFirstExceptionalNormalization
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- The actual first artificial divisor pool uses ALL original columns,
including columns whose coefficient happens to vanish. Its full norm is
bounded by the full pool cap, without replacement by a radical. -/
theorem artificial_norm (s : Source ι a b) (hb : 0≤b) (C D : Id) (hD : D≠0)
    (Dart : Id) (hDart : Dart∈artificialDivisors s C D hD) :
    Dart≠0 ∧ (Dart.absNorm:ℝ)≤poolCap s := by
  apply divisorPool_nonzero_norm
    (Finset.univ : Finset (columns C D hD (sourceColumns s)))
    (fun J=>Ideal.span {element C D hD (sourceColumns s) J})
    (fun J _=>(element_supported C D hD (sourceColumns s) J).1)
    (poolCap s) ?_ Dart hDart
  intro J hJ
  rw [element_span]
  have hj : D*J.val∈supportedColumns (sourceColumns s) :=
    (mem_residualPool D hD (supportedColumns (sourceColumns s)) J.val).mp
      (Finset.mem_filter.mp J.property).1
  exact (CenteredExceptionalCount.norm_le_of_dvd (Finset.mem_filter.mp hj).2.1
    (dvd_mul_left J.val D)).trans
      (source_column_pool_norm s hb (D*J.val) (Finset.mem_filter.mp hj).1)

theorem actual_radius_eq (s : Source ι a b) (C D : Id)
    (E : Finset (CommonIndex C D)) (K Z ξ : ℝ) :
    firstRadius s C D E K Z ξ=
      frequencyRadius (firstCutoff C D E K (sourceVolume s)) Z ξ := by
  simp only [firstRadius,firstCutoff,primeSubsetGenerator,span_idealGenerator]

/-- Original scale cap B produces a full common/pool cap 3B+1.
The already checked cutoff theorem is therefore used at 3B+1, rather
than incorrectly feeding a 3B+1 common norm into its B input. -/
theorem uniform_actual_band_geometry (N : ℕ) (b B ξfirst ξsecond κ : ℝ)
    (hb : 0<b) (hB : 1≤B) (hξfirst : 0≤ξfirst) (hξsecond : 0<ξsecond) (hκ : 0<κ) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(ι : Type u) [Fintype ι],∀a : ℝ,∀s : Source ι a b,∀ha : 0<a,
      Fintype.card ι≤N→Z^(-B)≤s.L→
      s.X₁≤Z^B→s.X₂≤Z^B→s.Y₁≤Z^B→s.Y₂≤Z^B→(∏i,s.P i)≤Z^B→
    ∀K W : ℝ,0<K→0<W→K≤Z^B→K⁻¹≤Z^B→W≤Z^B→W⁻¹≤Z^B→
    poolCap s≤Z^(sourceExponent B) ∧
    sourceNormCap s.P b s.T s.d≤Z^(sourceExponent B) ∧
    ∀seed : Id,∀H : ℝ,
      BandGeometry s ha seed K Z ξfirst κ W (secondCutoff (sourceExponent B) Z) H
        (tailExponent (sourceExponent B) ξfirst κ)
        (tailExponent (sourceExponent B) ξfirst κ+ξfirst/2) := by
  have hB0 : 1≤sourceExponent B := by unfold sourceExponent;linarith
  have hBB0 : B≤sourceExponent B := by unfold sourceExponent;linarith
  have htail : sourceExponent B≤tailExponent (sourceExponent B) ξfirst κ := by
    unfold tailExponent secondExponent childExponent sourceExponent
    linarith
  filter_upwards [eventually_source_caps N b B B 1 (by norm_num),
    uniform_actual_cutoffs N b (sourceExponent B) ξfirst ξsecond κ hb hB0 hξfirst hξsecond hκ]
      with Z hcaps hcut
  refine ⟨hcaps.1,?_⟩
  intro ι instι a s ha hcard hmin hX₁ hX₂ hY₁ hY₂ hP K W hK hW hKcap hKinv hWcap hWinv
  have hZ := hcaps.1
  have hZ0 := zero_lt_one.trans hZ
  have hscale : Z^B≤Z^(sourceExponent B) :=
    Real.rpow_le_rpow_of_exponent_le hZ.le hBB0
  have hmin0 : Z^(-sourceExponent B)≤s.L :=
    (Real.rpow_le_rpow_of_exponent_le hZ.le (neg_le_neg hBB0)).trans hmin
  have hc := hcaps.2 ι a s hcard hX₁ hX₂ hY₁ hY₂ hP
  have hpool : poolCap s≤Z^(sourceExponent B) := by
    simpa only [sourceExponent,show 2*B+B+1=3*B+1 by ring] using hc.1
  have hsource : sourceNormCap s.P b s.T s.d≤Z^(sourceExponent B) := by
    simpa only [sourceExponent,show 2*B+B+1=3*B+1 by ring] using hc.2
  refine ⟨hpool,hsource,?_⟩
  intro seed H
  have hdata (p : Labels s ha seed) :
      (p.val.1.absNorm:ℝ)≤Z^(sourceExponent B) ∧ (p.val.2.absNorm:ℝ)≤Z^(sourceExponent B) :=
    commonLabel_norm_bounds (sourceColumns s) (sourceCoefficient s ha seed) _
      (fun I _ hI=>(original_coefficient_cap s ha seed I hI).2.trans hsource)
      p.val.1 p.val.2 p.property
  have hactual (p : Labels s ha seed) (E : Finset (CommonIndex p.val.1 p.val.2)) :=
    hcut.2 ι a s hcard hmin0 (hX₁.trans hscale) (hX₂.trans hscale)
      (hY₁.trans hscale) (hY₂.trans hscale) (hP.trans hscale) K W hK hW
      (hKcap.trans hscale) (hKinv.trans hscale) (hWcap.trans hscale) (hWinv.trans hscale)
      p.val.1 p.val.2 1
      (commonLabels_supported (activeSource (sourceColumns s) (sourceCoefficient s ha seed)) p).1
      (commonLabels_supported (activeSource (sourceColumns s) (sourceCoefficient s ha seed)) p).2
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
      (commonLabels_supported (activeSource (sourceColumns s) (sourceCoefficient s ha seed)) p).2.1
      Dart hDart).2.trans hpool).trans (Real.rpow_le_rpow_of_exponent_le hZ.le htail)
  · intro p E hE n
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,hchildren⟩ := hactual p E
    have hn := block_retained (effectiveScale p.val.1 p.val.2 E K)
      (firstRadius s p.val.1 p.val.2 E K Z ξfirst)
      (H/p.val.1.absNorm) (H/p.val.2.absNorm) n
    have hn' : Retained
        (frequencyRadius (firstCutoff p.val.1 p.val.2 E K (sourceVolume s)) Z ξfirst)
        (n 1 : ℤ) :=
      (congrArg (fun r : ℝ => Retained r (n 1 : ℤ))
        (actual_radius_eq s p.val.1 p.val.2 E K Z ξfirst)).mp hn
    obtain ⟨_,_,hKL,hKR,_,_,hTL,hTR,hrows⟩ := hchildren (n 1) hn'
    refine ⟨hKL,hKR,hTL,hTR,?_⟩
    intro z hz
    have hza : z∈annularRows (n 1 : ℤ) :=
      fixedRows_annular (firstRadius s p.val.1 p.val.2 E K Z ξfirst)
        (fun i => (n i : ℤ)) hz
    exact (hrows z hza).2

end
end Candidate.SilPrior.FourthPower.MixedFirstActualBandGeometry
