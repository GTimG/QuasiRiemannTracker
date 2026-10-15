/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B005
import Submissions.affine_local_20261013.Bundles.B026
import Submissions.affine_local_20261013.Bundles.B031
import Submissions.affine_local_20261013.Bundles.B047
import Submissions.affine_local_20261013.Bundles.B053
import Submissions.affine_local_20261013.Bundles.B062
import Submissions.affine_local_20261013.Bundles.B070
import Submissions.affine_local_20261013.Bundles.B072
import Submissions.affine_local_20261013.Bundles.B073
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.CanonicalLiveCapacity
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainRelativeClass
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedFourCoefficients
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.NonfloorDyadic

/- BEGIN ORIGINAL MODULE Global.Transport.HighAssembly ; sha256 084a5ab7fd8f2b0cf8c0fc8c94ce2acf8ca7f86a1df462c1c61ec3d75f1e97cc -/
section
/- Adapted from weighted upstream PR6; no full-W analytic bound is assumed except the explicit cell premise. -/



open OAI OAI.SevenEighths

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace Submission20261012.Global.FinalAssembly
open ProbeFinalAssembly Submission20261012.Global.HighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

theorem actual_high_probe_from_moments_and_fullW (N : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0 < e) (he1 : e<1/1000) (heps : 0 < eps) (hc : 0 < c) (hcb : c ≤ b) (hA : 0 ≤ A)
    (hR : 0 ≤ R) (hdmin : 0 < dmin) (hdmax : 0 ≤ dmax) (hdRange : dmin ≤ dmax) (hrmin : 0 < rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0 ≤ cost) (hmesh : 0 < mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε < rmin*mesh) (hmargin : 0 < margin)
    (hheight : 2*τ < dmin*cost) (hloss : τ*(2+4*eps) < loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin ≤ ell j) (hellhi : ∀j,ell j ≤ dmin*R)
    (W : Fin N→ℝ→ℝ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,0 ≤ W j t ∧ W j t ≤ A)
    (hcompact : ∀j,HasCompactSupport (W j)) (hne : ∀j,W j≠0)
    (hellsum : ∑j,ell j=Submission20261012.Global.ell)
    (hdtop : dmax≤37/42) (hε1 : ε≤1/1000) (hκ1 : κ≤1)
    (hτzero : τ < dmin/2) (hτheight : 4*τ < dmin*cost)
    (hwbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ε/2)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y ≤ B₀)
    (εm ν logCost heightCost momentCost : ℝ)
    (hεm : 0<εm) (hν : 0<ν)
    (hlog : 0 < logCost) (hMomentHeight : τ < heightCost)
    (ζ μ : ℝ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1/48)
    (hweightedTop : Submission20261012.Global.h+ζ+2*margin ≤ Submission20261012.Global.h+Submission20261012.Global.rowExtension)
    (hfinal : (159*ε+εm+R+7*ν)+(12*e+eps*(N+8))+
      (logCost+heightCost+momentCost+loss+mesh*Submission20261012.Global.ell+(16-6*Submission20261012.Global.ly)*e)+μ ≤ 1/4000)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (target nu : ℝ) (htarget : Submission20261012.Global.signal Submission20261012.Global.theta≤ target) (hnu : 0 < nu)
    (dyadCost : ℝ) (hdyadCost : 0 < dyadCost)
    (hdmin1 : dmin<1/100) (hconductor : Submission20261012.Global.h+ζ+2*margin ≤ dmax)
    (hmuMargin : 2*margin≤μ)
    (hβlo : Submission20261012.Global.theta ≤ HeckeZeroSupremum.beta)
    (hβ : HeckeZeroSupremum.beta ≤ (7/8:ℝ))
    (sigma : ℝ) (hsigma : 0 < sigma)
    (hgeometric : sigma+8*e+nu≤1/20) (hprincipal : sigma+nu≤1/4000)
    (hwindow : sigma+e ≤ Submission20261012.Global.theta*(dmax*rmin))
    (hfloorbudget : 26*e+(N+8)*eps+loss+mesh*Submission20261012.Global.ell+nu+sigma≤1/100)
    (hcentral : sigma+nu+dyadCost≤ HeckeZeroSupremum.beta-(4+Submission20261012.Global.b)/6-target) (counts : CountParameters M H εm) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃n : ℕ,0 < n ∧ ∃C : ℝ,
      0 < C ∧
    ∀η : Character,∃Ct : ℝ,0 < Ct ∧ ∀ᶠZ : ℝ in atTop,
      let Yp := fun j=> Z^(ell j)
      let T := fun j=> pool (RayQuotient.identityClass M H) S c b (Yp j)
      let _hT := nonfloorPoolOutside M H S N c b Yp
      let WC : Fin N→ℝ→ℂ := fun j y=>(W j y:ℂ)
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (Submission20261012.Global.ell) (slotMass T (residueWeights W Yp)) : ℂ)
      normer≠0 ∧ ∃idx grid : FreeRow→ℕ,
      (∀u,1 ≤ idx u ∧ idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/e⌋₊ ∧
        ((3*idx u+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*idx u+2:ℕ)*Z^τ) ∧
      (∀u, let a : ℝ := 51/100+e*grid u
        (51/100:ℝ) ≤ a ∧ a≤7/8 ∧
        a ≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ) ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ) < a+e ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(idx u+1:ℕ)*Z^τ) < a+2*e ∧
        (51/100 < a → ∃j s,LFunction (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) s=0 ∧
          ¬((sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j).residue=1 ∧ s=1) ∧
          a ≤ s.re ∧ s.re < a+e ∧ |s.im|≤3*idx u*Z^τ)) ∧
      (∀u∈rowBand (Z^(1/100:ℝ)) (Z^((Submission20261012.Global.h:ℝ)+ζ)),
        (calibrationForSet S hmax).residueMonoid u.val≠0 →
        (∀θ,(rayCubeFamily M H hH u θ).residue≠1) ∧
        (∀θ,(rayCubeFamily M H hH u θ).modulus.absNorm≤
          conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm) ∧
        ∀hnp : ∀θ,(rayCubeFamily M H hH u θ).residue≠1,
        HeckeDetectorZeros.zeroMaximum (rayCubeFamily M H hH u) hnp
          (3*(idx u+1:ℕ)*Z^τ)<(51/100:ℝ)+e*grid u+2*e) ∧
      let rows := supportedNonfloorRows S hmax (rowBand (Z^(1/100:ℝ)) (Z^((Submission20261012.Global.h:ℝ)+ζ))) grid
      ∀C0 : ℝ,1 ≤ C0 → ∀weightedC : ℝ,0 ≤ weightedC →
      (∀k∈smallDyadicIndices (Z^(Submission20261012.Global.h+ζ)),∀i∈Finset.range (n+1),∀j∈Finset.range (⌊(49/100:ℝ)/e⌋₊+1),
        let rows' := cubeBinRows (rows∩dyadicRows 1 k) idx grid i j
        rows'.Nonempty → ∀t : HeightSpace,
        ((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
        SourceMomentsAt M H hH S hS.prime η rows' ell WC Z
          (sourceDyadConductor Z margin k) (51/100+e*j) ε τ dmax b R mesh i
          ((17/50:ℂ)+t.1.2*Complex.I) 0
          (if 2*(51/100+e*j)-1≤5/6 then counts.cB else counts.cH)
          (if 2*(51/100+e*j)-1≤5/6 then counts.kB else counts.kH)
          (C0*Z^momentCost) (Z^heightCost) εm) →
      (∀k∈smallDyadicIndices (Z^(Submission20261012.Global.h+ζ)),∀i∈Finset.range (n+1),∀j∈Finset.range (⌊(49/100:ℝ)/e⌋₊+1),
        let rows' := cubeBinRows (rows∩dyadicRows 1 k) idx grid i j
        let Y : Fin N→ℝ := fun j=> Z^(ell j)
        let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
        let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
          (Probe.principalScalar Finset.univ Z (Submission20261012.Global.ell)
            (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Y)) : ℂ)
        rows'.Nonempty →
        (1/2:ℝ) < sourceDyadConductor Z margin k →
        (1/3:ℝ) < 2*(51/100+e*j)-1 →
        sourceDyadConductor Z margin k ≤ Submission20261012.Global.h+ζ+2*margin →
        ‖Cycle25.Weighted.FullWContour.finiteCentralFullWRows S hS hmax η rows' T (nonfloorPoolOutside M H S N c b Y)
          (fun j y=>(W j y:ℂ)) Y W0 W1 (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z e
          (fun _=>51/100+e*j) (fun _=>(3*i+1:ℕ)*Z^τ)/normer‖ ≤
          weightedC*C0*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(target+nu)) →
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun j=> canonicalSlotSupport (T j)) WC Yp (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-(4+Submission20261012.Global.b)/6) Z‖≤
        (Ct+C*(2+weightedC)*C0*(η.modulus.absNorm:ℝ)^(2*eps))*Z^(HeckeZeroSupremum.beta-(4+Submission20261012.Global.b)/6-sigma) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have hmin : 0 < dmax*rmin := mul_pos (hdmin.trans_le hdRange) hrmin
  obtain ⟨n,hn,htransport⟩ := actual_nonfloor_probe_transport M H hH N e (1/4) c b A ζ 1 τ (dmax*rmin) nu
    he he1 (by norm_num) (by norm_num) hζ hζ1 hτ hc hcb hA hmin hnu hβlo hβ S hS hmax hfirst
    ell hello hell hellsum W hW hcompact hWs hWB hne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    hr0 hr1 hp0 hp1 hn0 hn1 sigma hsigma hgeometric hprincipal hwindow (by rw [Submission20261012.Global.signal_low]; linarith [Submission20261012.Global.ell_pos,Submission20261012.Global.x_rescaled_pos,Submission20261012.Global.b_pos])
    eps R dmin dmax rmin ε κ cost mesh margin loss heps hR hdmin hdmax hdRange hrmin hε hκ hcost hmesh hmargin
    hbudget hgap hheight hloss (by linarith) hello hellhi (by change Submission20261012.Global.h+ζ+2*margin ≤ Submission20261012.Global.h+Submission20261012.Global.rowExtension at hweightedTop; linarith) hfloorbudget
  obtain ⟨C,hC,hbound⟩ :=
    actual_mixed_fullW_nonfloor_rows_saving M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss
      he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
      hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hcompact hne hellsum
      hdtop hε1 hκ1 hτzero hτheight hwbudget
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
      εm ν logCost heightCost momentCost hεm hν hlog hMomentHeight
      μ (Submission20261012.Global.h+ζ) (by linarith) hfinal W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      hr0 hr1 hp0 hp1 hn0 hn1 target nu htarget hnu ⌊(49/100:ℝ)/e⌋₊ dyadCost hdyadCost hdmin1 hconductor hweightedTop hmuMargin counts
  refine ⟨n,hn,C,hC,?_⟩
  intro η
  obtain ⟨Ct,hCt,htransport⟩ := htransport η
  refine ⟨Ct,hCt,?_⟩
  filter_upwards [htransport,hbound η,eventually_ge_atTop (1:ℝ)] with Z ht hb hZ
  dsimp only at ht ⊢
  obtain ⟨hnorm,idx,grid,hlabels,hbins,hray,herror⟩ := ht
  refine ⟨hnorm,idx,grid,hlabels,hbins,hray,?_⟩
  intro C0 hC0 weightedC hweightedC hmom hweighted
  let rows := supportedNonfloorRows S hmax (rowBand (Z^(1/100:ℝ)) (Z^((Submission20261012.Global.h:ℝ)+ζ))) grid
  have hrows : ∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ) ≤ rowNorm u ∧
      (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u ≤ Z^(Submission20261012.Global.h+ζ) := by
    intro u hu
    rcases (mem_supportedNonfloorRows S hmax _ grid u).mp hu with ⟨hur,hcal,hg⟩
    have hh := mem_rowBand.mp hur
    exact ⟨hh.1,hh.2.1,hcal,hh.2.2.le⟩
  have hlabel : ∀u∈rows,idx u ≤ n ∧ grid u≤⌊(49/100:ℝ)/e⌋₊ ∧ grid u≠0 ∧ 51/100+e*grid u≤7/8 := by
    intro u hu
    exact ⟨(hlabels u).2.1,(hlabels u).2.2.1,
      ((mem_supportedNonfloorRows S hmax _ grid u).mp hu).2.2,(hbins u).2.1⟩
  have hnext : ∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
      (3*(idx u+1:ℕ)*Z^τ)<51/100+e*grid u+2*e := fun u _=>(hbins u).2.2.2.2.1
  have hcurrent : ∀u∈rows,51/100+e*grid u ≤ detectorMaximum
      (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) ((3*idx u:ℕ)*Z^τ) := by
    intro u hu
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using (hbins u).2.2.1
  have hglobal := (hb C0 hC0 weightedC hweightedC rows hrows idx grid hlabel hnext hcurrent hweighted hmom).2
  have hexp : Z^(target+nu+dyadCost)≤
      Z^(HeckeZeroSupremum.beta-(4+Submission20261012.Global.b)/6-sigma) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith only [hcentral])
  have hcentral' := hglobal.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
  have hsum := (norm_add_le _ _).trans (add_le_add herror hcentral')
  simpa only [rows,sub_add_cancel,add_mul] using hsum

end Submission20261012.Global.FinalAssembly

end



#print axioms Submission20261012.Global.FinalAssembly.actual_high_probe_from_moments_and_fullW
end
/- END ORIGINAL MODULE Global.Transport.HighAssembly -/

/- BEGIN ORIGINAL MODULE Analytic.ActualErrorPowerFull ; sha256 b9f65e03ce3a71b95a0c32fa46b30f5b376402f3122f98c0b627d0b534e7e803 -/
section

/-! Actual extracted Gaussian errors, uniformly over original source subsets.
The genuine incumbent endpoints are consumed internally. The first Gaussian
power retains sigma + removal - moving and therefore the local reserve. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.Local44.Analytic
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=> HeckeFamily.O
local instance actualErrorPowerInstance1Full {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalLiveBound CenteredMomentEnergyCanonicalLiveCapacity
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid CenteredMomentEnergyBandSubtypeTransport
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization
variable (M:Ideal O)[NeZero M]
local instance actualErrorPowerInstance2Full : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

open CenteredMomentEnergyCanonicalUniformReference CenteredMomentEnergyAmplifiedRayDictionary
open CenteredMomentFirstAmplifiedPaidAdmission CenteredMomentFirstAmplifiedCapacityCommon
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss
open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)
open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization
open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource
open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource
open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization
open CenteredMomentFirstNestedSeededGaussianPower CenteredMomentFirstSecondInputGates

theorem actual_original_subsets_error_power_full
    (Wslot:ℝ→ℂ)(aslot bslot Mcap εremove lo hi εchild:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤ Mslot)(hεmask:0<εmask)(haPlain:0< a)(haUpper:a≤1/4)(hbPlain:1≤ b)
    (L:ℝ)(hL:0≤ L)
    (ha:0< aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hbslot:0≤ bslot)(hMcap:0< Mcap)
    (hεchild:0<εchild)(hε:0<εremove)
    (hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)(hbetaTop:HeckeZeroSupremum.beta≤7/8)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0< lower)(hupper:1≤ upper)
    (ha0:0< a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤ highs i)
    (εsrc δsrc θsrc Bcap Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hBcap:0≤ Bcap)(hξ:0<ξ)
    (sigma cost:ℝ)(hsigma:0< sigma)(hξsmall:ξ≤ sigma/4)(hcost:1≤ cost):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤ M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃Cbound:ℝ,0< Cbound ∧ ∀ᶠ Z : ℝ in atTop, 1< Z ∧
    ∀θ:α→RayQuotient.Characters M H,
    ∀(w σ freq:α→ℝ)(height mesh:ℝ),0≤ mesh → (∀i,0≤ w i) → (∀i,w i≤ mesh) →
    (∀i,w i≤(Cycle25.Energy.commonMesh Mcap 0 L εchild)) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) → 0≤ height → (∀i,|freq i|≤ height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤ bslot) → (∀i,src.M i≤ Mslot) →
    (∀i,src.lo i=lows i) → (∀i,src.hi i=highs i) →
    Fintype.card α≤ N → lower≤ src.lower → src.upper≤ upper →
    0≤ src.b₁ → 0≤ src.b₂ → src.b₁≤ max 1 b → src.b₂≤ max 1 b →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D} →
    ∀K delta reserve asource:ℝ,0< K → 0< asource →
    0≤ delta → 0≤ reserve → a0≤ asource →
    ∀(prime:O),prime≠0 → ∀k:ℕ,(k=0 ∨ k=5 ∨ k=6) →
    sigma/6≤ Real.logb Z (normValue prime) →
    (∀i,∀I∈(activeInput (child src C R0 B τ t)).slots i,IsCoprime (Ideal.span {prime}) I) →
    ∀Bp:actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime})^(k+1)),
    ∀(υ:Character)(χerr:RayCharacter)(v0:ℝ),
    υ.modulus.absNorm≤ CenteredMomentAmplificationRadicalFamily.radicalBound
      (CenteredMomentChildRows.childCharacter τ χerr) fixedBadMask prime
      (CenteredMomentAmplificationActiveFactor.errorMovingExponent k) →
    (υ.modulus.absNorm:ℝ)≤ cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z (k+1)) →
    ∀input:Input (CenteredMomentCommonProfile.liveIndices Bp.val),
    input=errorInput src C R0 B τ t (Ideal.span {prime}) (k+1) Bp υ v0 →
    let Kerror:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime (k+1)
    Ready input ((R0*C)*(Ideal.span {prime})^(k+1)) Kerror Z ξ Bcap →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤ Z^Bseed →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤ Z^L → src.X₂≤ Z^L → src.Y₁≤ Z^L → src.Y₂≤ Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*(3/4)*(∑i,w i)≤ Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤ Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤ Mwidth →
    Mwidth-sigma/2≤ Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    asource≤ CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    ∀r:ℝ,Z^r≤ input.X₁ → Z^r≤ input.X₂ → Z^r≤ input.Y₁ → Z^r≤ input.Y₂ →
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+(3/4)*mesh;
    normalizedGaussSource input ((R0*C)*(Ideal.span {prime})^(k+1)) seed
      CenteredMomentFirstAmplificationChoice.ballProfile Kerror≤
      (∑j,(Cbound*(p.control Uprofile)^2*(1+|v0|+height)^Jheight*
        Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm:ℝ))*
        CenteredMomentFirstAmplifiedFourCoefficients.errorPowers prime (k+1)
        (τ.modulus.absNorm:ℝ) Z Kerror
        (refinedErrorDeficit prime Z (k+1) sigma (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)))) paid saving r j*
        (volume input)^(powers εsrc j))*mass input^2 := by
  have hmax : 0 < max 1 b := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have ha' : 0 < a/max 1 b := div_pos haPlain hmax
  have haUpper' : a/max 1 b ≤ 1/4 := by
    apply (div_le_iff₀ hmax).mpr
    nlinarith [le_max_left (1 : ℝ) b]
  obtain ⟨degree,S,hinc⟩ := actual_incumbent_pair (α := α) M H hH Wslot aslot bslot
    (a/max 1 b) b 2 0 L lo hi Mcap εchild ha hWs hW hbslot ha' haUpper' hbPlain
    (by norm_num) (by norm_num) hMcap hεchild hbeta hbetaTop
  have hmesh := Cycle25.Energy.commonMesh_pos Mcap 0 L εchild hMcap.le (by norm_num) hεchild
  obtain ⟨Uprofile,Jheight,hmain⟩ := refined_error_homogeneous (α := α) M H hH
    Wslot aslot bslot Mcap (Cycle25.Energy.commonMesh Mcap 0 L εchild) εremove lo hi (3/4)
    a b Mslot εmask hMslot hεmask haPlain (zero_le_one.trans hbPlain)
    L hL degree S ha hWs hW hMcap.le hmesh.le hε (by norm_num) hbeta (by linarith)
    N lower upper a0 θsource hlower hupper ha0 hθsource lows highs hhighs
    εsrc δsrc θsrc Bcap Bseed ξ saving hεsrc hδsrc hθsrc hBcap hξ sigma cost hsigma hξsmall hcost
  refine ⟨Uprofile,Jheight,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,Z₀,hZ₀,hconsume⟩ := hmain η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C₀,C₁,hC₀,hC₁,hincZ⟩ := hinc η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cbound*(C₀+C₁+1),mul_pos hCbound (by positivity),?_⟩
  filter_upwards [hincZ,eventually_ge_atTop Z₀] with Z hZ hZ₀Z
  refine ⟨hZ.1,?_⟩
  intro θ
  exact hconsume θ Z hZ₀Z εchild C₀ C₁ hC₀.le hC₁.le hZ.2.1 hZ.2.2

#print axioms actual_original_subsets_error_power_full
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.ActualErrorPowerFull -/

/- BEGIN ORIGINAL MODULE Analytic.JointAmplificationErrors ; sha256 3462f74ea248b4e59460716b11e3106543ec4fb55fd8ee2bae4980f2786b26d2 -/
section




/-! The actual global removal estimate on the three extracted errors.
The error scalar and the shortened prime-power volume are retained literally.
All original-slot subsets share the same constant, degree and profile control.
The remaining hypothesis is a length/width inequality, not an analytic estimate. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Set Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CenteredMomentEnergyBands CenteredMomentEnergyState
open CenteredMomentEnergyPaidRemoval CenteredMomentNaturalFixedRaySource
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentPrimeSlot QuadraticInitialBound
open CenteredMomentPrimeElements CenteredMomentPrimePool CanonicalQuadraticSieve
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplificationErrorEnergy
open CenteredMomentFirstMixedNormalization CenteredMomentFirstAmplifiedFourCoefficients
open ConcreteTraceCRT RayFourExpansion CenteredMomentGaussNormalization CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O

/-- The positive-part excess retains the strict local error reserve.
The value `37/10000` is the genuine parent cost-`22/5` excess cap. -/
lemma amplification_error_positive_excess (p : O) (Z x : ℝ) (k : ℕ)
    (hk : k=1 ∨ k=6 ∨ k=7)
    (hlog : 9/2000 ≤ Real.logb Z (normValue p))
    (hx : x ≤ 37/10000+9/500+errorRemoval p Z k-errorMoving p Z k) :
    max x 0/6-errorRemoval p Z k ≤ -(53/60000) := by
  have hr := local_amplification_error_reserves (37/10000) (Real.logb Z (normValue p))
    le_rfl hlog
  have hlog0 : 0 ≤ Real.logb Z (normValue p) := by linarith
  rcases hk with rfl | rfl | rfl
  · simp only [errorRemoval,errorMoving,show ¬(1 : ℕ)=6 by decide,ite_false,
      Nat.cast_one,one_mul] at hx ⊢
    have hm : max x 0 ≤ (37/10000 : ℝ)+9/500 := max_le (by linarith) (by norm_num)
    linarith [hr.1]
  · norm_num only [errorRemoval,errorMoving,ite_true,Nat.cast_ofNat] at hx ⊢
    have hm : max x 0 ≤ (37/10000 : ℝ)+9/500+6*Real.logb Z (normValue p) :=
      max_le (by linarith) (by linarith)
    linarith [hr.2.1]
  · norm_num only [errorRemoval,errorMoving,ite_false,Nat.cast_ofNat] at hx ⊢
    have hm : max x 0 ≤ (37/10000 : ℝ)+9/500+6*Real.logb Z (normValue p) :=
      max_le (by linarith) (by linarith)
    linarith [hr.2.2]

/-- The actual local Gauss error scalar cancels the moving conductor.
The extraction divisor is exactly the norm of the actual prime to `k`. -/
lemma amplification_error_energy_contraction (p : O) (hp : p ≠ 0)
    (Z width paid x E A : ℝ) (hZ : 1 < Z) (hA : 0 ≤ A) (k : ℕ)
    (hk : k=1 ∨ k=6 ∨ k=7)
    (hlog : 9/2000 ≤ Real.logb Z (normValue p))
    (hx : x ≤ 37/10000+9/500+errorRemoval p Z k-errorMoving p Z k)
    (hE : E ≤ A*Z^(width+paid+max x 0/6)) :
    (localErrorCost p (k-1)*Z^(errorMoving p Z k))*E /
      (Z^width*(normValue p)^k) ≤ A*Z^(paid-53/60000) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hc : 0 ≤ localErrorCost p (k-1)*Z^(errorMoving p Z k) :=
    mul_nonneg (localErrorCost_nonneg _ _) (Real.rpow_nonneg hz.le _)
  have hw := mul_le_mul_of_nonneg_right (actual_error_weight p hp Z hZ k hk)
    (Real.rpow_nonneg hz.le (errorMoving p Z k))
  rw [← Real.rpow_add hz, neg_add_cancel, Real.rpow_zero] at hw
  have hbound : (localErrorCost p (k-1)*Z^(errorMoving p Z k))*E ≤
      A*Z^(width+paid+max x 0/6) :=
    (mul_le_mul_of_nonneg_left hE hc).trans
      ((mul_le_mul_of_nonneg_right hw (mul_nonneg hA (Real.rpow_nonneg hz.le _))).trans_eq
        (one_mul _))
  have hd : 0 < Z^width*(normValue p)^k :=
    mul_pos (Real.rpow_pos_of_pos hz _) (pow_pos (normValue_pos p hp) _)
  calc
    _ ≤ (A*Z^(width+paid+max x 0/6))/(Z^width*(normValue p)^k) :=
      div_le_div_of_nonneg_right hbound hd.le
    _ = A*Z^(paid+max x 0/6-errorRemoval p Z k) := by
      rw [← errorRemoval_power p hp Z hZ k, ← Real.rpow_add hz,
        mul_div_assoc, ← Real.rpow_sub hz]
      congr 2
      ring
    _ ≤ A*Z^(paid-53/60000) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.le
        (by linarith [amplification_error_positive_excess p Z x k hk hlog hx])) hA

/-- Support and clipping perturbations cost exactly one sixth of their
nonnegative affine error; they do not replace the strict reserve. -/
lemma amplification_error_energy_contraction_with_loss (p : O) (hp : p ≠ 0)
    (Z width paid x E A loss : ℝ) (hZ : 1 < Z) (hA : 0 ≤ A) (hloss : 0 ≤ loss)
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7)
    (hlog : 9/2000 ≤ Real.logb Z (normValue p))
    (hx : x ≤ 37/10000+9/500+errorRemoval p Z k-errorMoving p Z k+loss)
    (hE : E ≤ A*Z^(width+paid+max x 0/6)) :
    (localErrorCost p (k-1)*Z^(errorMoving p Z k))*E /
      (Z^width*(normValue p)^k) ≤ A*Z^(paid+loss/6-53/60000) := by
  have hm : max x 0 ≤ max (x-loss) 0+loss :=
    max_le (by linarith [le_max_left (x-loss) (0 : ℝ)])
      (by linarith [le_max_right (x-loss) (0 : ℝ)])
  apply amplification_error_energy_contraction p hp Z width (paid+loss/6)
    (x-loss) E A hZ hA k hk hlog (by linarith)
  exact hE.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)) hA)

/-- A smaller actual dyadic width pays its own larger affine defect. Only
an upper bound by the nominal width is needed. -/
lemma error_nominal_width (actual nominal total pad : ℝ)
    (hpad : 0 ≤ pad) (hactual : actual ≤ nominal+pad) :
    actual+max (total-actual) 0/6 ≤ nominal+pad+max (total-nominal) 0/6 := by
  have hm₀ := le_max_right (total-nominal) (0 : ℝ)
  have hm₁ := le_max_left (total-nominal) (0 : ℝ)
  by_cases h : total ≤ actual
  · rw [max_eq_right (sub_nonpos.mpr h)]
    linarith
  · rw [max_eq_left (sub_nonneg.mpr (le_of_not_ge h))]
    linarith

/-- The literal error normalization at the nominal width works for every
smaller actual row width. The harmless upper-width pad stays explicit. -/
lemma amplification_error_nominal_contraction (p : O) (hp : p ≠ 0)
    (Z actual nominal total pad paid E A loss : ℝ)
    (hZ : 1 < Z) (hA : 0 ≤ A) (hpad : 0 ≤ pad) (hloss : 0 ≤ loss)
    (hwidth : actual ≤ nominal+pad) (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7)
    (hlog : 9/2000 ≤ Real.logb Z (normValue p))
    (hexcess : total-nominal ≤ 37/10000+9/500+errorRemoval p Z k-errorMoving p Z k+loss)
    (hE : E ≤ A*Z^(actual+paid+max (total-actual) 0/6)) :
    (localErrorCost p (k-1)*Z^(errorMoving p Z k))*E /
      (Z^nominal*(normValue p)^k) ≤ A*Z^(paid+pad+loss/6-53/60000) := by
  apply amplification_error_energy_contraction_with_loss p hp Z nominal (paid+pad)
    (total-nominal) E A loss hZ hA hloss k hk hlog hexcess
  exact hE.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.le
    (by linarith [error_nominal_width actual nominal total pad hpad hwidth])) hA)

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Genuine global removal at every original-slot subset and every actual
amplifying prime. No local moment or whole-error bound is a premise. The
remaining excess inequality concerns only the actual scales and row width. -/
theorem actual_global_amplification_errors
    (W : ℝ → ℂ) (aslot bslot a b radial Bmask L lo hi Mcap εchild εremove : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0 ≤ bslot)
    (ha : 0 < a) (haUpper : a ≤ 1/4) (hb : 1 ≤ b) (hrad : 0 < radial)
    (hmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hεchild : 0 < εchild) (hεremove : 0 < εremove)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) (hbetaTop : HeckeZeroSupremum.beta ≤ 7/8)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes ⊆ Sbad) :
    ∃ degree : ℕ, ∃ S : Finset (ℕ × ℕ), ∀ η₀ : Character,
      ∀ Q : Ideal O, Q ≤ M → internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
        ∀ p : O, p ∈ elementPool (primePool M H Sbad (1/2) 1 (Z^((9/500 : ℝ)/3))) →
        ∀ k : ℕ, (k=1 ∨ k=6 ∨ k=7) →
        ∀ (J : Finset α) (θ : α → RayQuotient.Characters M H)
          (w σ v : α → ℝ) (t height mesh : ℝ),
        0 ≤ mesh → mesh ≤ Cycle25.Energy.commonMesh Mcap Bmask L εchild →
        (∀ i, 0 ≤ w i) → (∀ i, w i ≤ mesh) →
        (∀ i, lo ≤ σ i) → (∀ i, σ i ≤ hi) → 0 ≤ height → (∀ i, |v i| ≤ height) →
        ∀ s : NaturalState Z Bmask radial, s.puncture = 1 →
          s.fixedModulus = internalQ Q η₀ → s.width ≤ Mcap →
        ∀ (profile : Profiles a b) (X₁ X₂ loss : ℝ), 0 ≤ loss →
        0 < X₁ → 0 < X₂ → X₁ ≤ Z^L → X₂ ≤ Z^L →
        length Z X₁+length Z X₂+(9/2)*(∑ i ∈ J, w i)-s.width ≤
          37/10000+9/500+errorRemoval p Z k-errorMoving p Z k+loss →
        (localErrorCost p (k-1)*Z^(errorMoving p Z k))*
          energy s.character s.mask 1 t (profile.profile 0) (profile.profile 1)
            (fun i : J => primePool M H bslot (Z^(w i)))
            (fun (i : J) I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
              HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
            (fun i : J => Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale /
              (Z^s.width*(normValue p)^k) ≤
          C*diagonalControl s.radial.profile*(profile.control S)^2*(1+|t|+height)^degree*
            Z^(εchild+εremove+(3/4)*mesh+loss/6-53/60000) := by
  obtain ⟨degree,S,hglobal⟩ := actual_global_removal (α := α) M H hH W
    aslot bslot a b radial Bmask L lo hi Mcap εchild εremove haslot hWs hW hbslot
    ha haUpper hb hrad hmask hMcap hεchild hεremove hbeta hbetaTop
  refine ⟨degree,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,hglobalZ⟩ := hglobal η₀ Q hQM hQ0 hQt hQ72
  refine ⟨C,hC,?_⟩
  filter_upwards [hglobalZ,
    eventually_pool_prime_quarter_lower M H Sbad hbad (9/500) (by norm_num)] with Z hZ hpZ
  refine ⟨hZ.1,?_⟩
  intro p hp k hk J θ w σ v t height mesh hmesh0 hmeshCap hw hwm hσlo hσhi hheight hv
    s hunit hQ hs profile X₁ X₂ loss hloss hX₁ hX₂ hLX₁ hLX₂ hexcess
  have hpdata := elementPool_data _
    (fun Q hQ => (primePool_data M H Sbad hbad (1/2) 1
      (Z^((9/500 : ℝ)/3)) Q hQ).1)
    (fun Q hQ => (primePool_data M H Sbad hbad (1/2) 1
      (Z^((9/500 : ℝ)/3)) Q hQ).2) p hp
  have henergy := hZ.2 J θ w σ v t height mesh hmesh0 hmeshCap hw hwm hσlo hσhi hheight hv
    s hunit hQ hs profile X₁ X₂ hX₁ hX₂ hLX₁ hLX₂
  refine amplification_error_energy_contraction_with_loss p hpdata.1.ne_zero Z s.width
    (εchild+εremove+(3/4)*mesh)
    (length Z X₁+length Z X₂+(9/2)*(∑ i ∈ J, w i)-s.width)
    _ _ loss hZ.1 (by have hd := diagonalControl_nonneg s.radial.profile; positivity) hloss
    k hk (by linarith [(hpZ.2 p hp).1]) hexcess ?_
  convert henergy using 1
  congr 1
  congr 1
  ring

/-- The source-facing version uses a nominal width upper cap. It makes no
lower-width hypothesis on the actual canonical dyadic state. -/
theorem actual_global_nominal_amplification_errors
    (W : ℝ → ℂ) (aslot bslot a b radial Bmask L lo hi Mcap εchild εremove : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0 ≤ bslot)
    (ha : 0 < a) (haUpper : a ≤ 1/4) (hb : 1 ≤ b) (hrad : 0 < radial)
    (hmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hεchild : 0 < εchild) (hεremove : 0 < εremove)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) (hbetaTop : HeckeZeroSupremum.beta ≤ 7/8)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes ⊆ Sbad) :
    ∃ degree : ℕ, ∃ S : Finset (ℕ × ℕ), ∀ η₀ : Character,
      ∀ Q : Ideal O, Q ≤ M → internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
        ∀ p : O, p ∈ elementPool (primePool M H Sbad (1/2) 1 (Z^((9/500 : ℝ)/3))) →
        ∀ k : ℕ, (k=1 ∨ k=6 ∨ k=7) →
        ∀ (J : Finset α) (θ : α → RayQuotient.Characters M H)
          (w σ v : α → ℝ) (t height mesh : ℝ),
        0 ≤ mesh → mesh ≤ Cycle25.Energy.commonMesh Mcap Bmask L εchild →
        (∀ i, 0 ≤ w i) → (∀ i, w i ≤ mesh) →
        (∀ i, lo ≤ σ i) → (∀ i, σ i ≤ hi) → 0 ≤ height → (∀ i, |v i| ≤ height) →
        ∀ s : NaturalState Z Bmask radial, s.puncture = 1 →
          s.fixedModulus = internalQ Q η₀ → s.width ≤ Mcap →
        ∀ (profile : Profiles a b) (X₁ X₂ nominal pad loss : ℝ), 0 ≤ pad → 0 ≤ loss →
        0 < X₁ → 0 < X₂ → X₁ ≤ Z^L → X₂ ≤ Z^L → s.width ≤ nominal+pad →
        length Z X₁+length Z X₂+(9/2)*(∑ i ∈ J, w i)-nominal ≤
          37/10000+9/500+errorRemoval p Z k-errorMoving p Z k+loss →
        (localErrorCost p (k-1)*Z^(errorMoving p Z k))*
          energy s.character s.mask 1 t (profile.profile 0) (profile.profile 1)
            (fun i : J => primePool M H bslot (Z^(w i)))
            (fun (i : J) I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
              HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
            (fun i : J => Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale /
              (Z^nominal*(normValue p)^k) ≤
          C*diagonalControl s.radial.profile*(profile.control S)^2*(1+|t|+height)^degree*
            Z^(εchild+εremove+(3/4)*mesh+pad+loss/6-53/60000) := by
  obtain ⟨degree,S,hglobal⟩ := actual_global_removal (α := α) M H hH W
    aslot bslot a b radial Bmask L lo hi Mcap εchild εremove haslot hWs hW hbslot
    ha haUpper hb hrad hmask hMcap hεchild hεremove hbeta hbetaTop
  refine ⟨degree,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,hglobalZ⟩ := hglobal η₀ Q hQM hQ0 hQt hQ72
  refine ⟨C,hC,?_⟩
  filter_upwards [hglobalZ,
    eventually_pool_prime_quarter_lower M H Sbad hbad (9/500) (by norm_num)] with Z hZ hpZ
  refine ⟨hZ.1,?_⟩
  intro p hp k hk J θ w σ v t height mesh hmesh0 hmeshCap hw hwm hσlo hσhi hheight hv
    s hunit hQ hs profile X₁ X₂ nominal pad loss hpad hloss hX₁ hX₂ hLX₁ hLX₂ hwidth hexcess
  have hpdata := elementPool_data _
    (fun Q hQ => (primePool_data M H Sbad hbad (1/2) 1
      (Z^((9/500 : ℝ)/3)) Q hQ).1)
    (fun Q hQ => (primePool_data M H Sbad hbad (1/2) 1
      (Z^((9/500 : ℝ)/3)) Q hQ).2) p hp
  have henergy := hZ.2 J θ w σ v t height mesh hmesh0 hmeshCap hw hwm hσlo hσhi hheight hv
    s hunit hQ hs profile X₁ X₂ hX₁ hX₂ hLX₁ hLX₂
  refine amplification_error_nominal_contraction p hpdata.1.ne_zero Z s.width nominal
    (length Z X₁+length Z X₂+(9/2)*(∑ i ∈ J, w i)) pad
    (εchild+εremove+(3/4)*mesh) _ _ loss hZ.1
    (by have hd := diagonalControl_nonneg s.radial.profile; positivity) hpad hloss hwidth k hk (by linarith [(hpZ.2 p hp).1]) hexcess ?_
  convert henergy using 1
  congr 1
  congr 1
  ring

/-- The prime average cancels its own cardinality while all first labels
remain under the same finite sum. Only the three fixed valuations and ray
characters contribute a constant. -/
theorem joint_amplification_error_average {Λ : Type*}
    (labels : Finset Λ) (weight E : Λ → ℝ)
    (P : Finset (Ideal O)) (hne : P.Nonempty)
    (hp : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P, Q ∉ fixedBadPrimes)
    (f : elementPool P → Λ → Fin 3 → RayCharacter → ℝ)
    (hw : ∀ l ∈ labels, 0 ≤ weight l)
    (hE : ∀ l ∈ labels, 0 ≤ E l)
    (hf : ∀ p l, l ∈ labels → ∀ i χ, f p l i χ ≤ E l) :
    (56/(P.card : ℝ))*(∑ p : elementPool P, ∑ l ∈ labels, weight l*
      ∑ i : Fin 3, 16*(errorIndex i+2 : ℝ)^2*∑ χ : RayCharacter, f p l i χ) ≤
      (56*1872*(Fintype.card RayCharacter : ℝ))*(∑ l ∈ labels, weight l*E l) := by
  have hpoint (l : Λ) (hl : l ∈ labels) := actual_error_average P hne hp hbad
    (fun p i χ => f p l i χ) (E l) (hE l hl) (fun p i χ => hf p l hl i χ)
  calc
    _ = 56*∑ l ∈ labels, weight l*((1/(P.card : ℝ))*
        ∑ p : elementPool P, ∑ i : Fin 3,
          16*(errorIndex i+2 : ℝ)^2*∑ χ : RayCharacter, f p l i χ) := by
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro χ hχ
      ring
    _ ≤ 56*∑ l ∈ labels, weight l*(1872*(Fintype.card RayCharacter : ℝ)*E l) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum (fun l hl => mul_le_mul_of_nonneg_left (hpoint l hl) (hw l hl))
    _ = _ := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      ring

#print axioms actual_global_amplification_errors
#print axioms actual_global_nominal_amplification_errors
#print axioms joint_amplification_error_average
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointAmplificationErrors -/

/- BEGIN ORIGINAL MODULE Analytic.JointLowComplete ; sha256 8159904d73e306ce3d91dacff33a673238f4e99a3e8b30e5c1ed5b2ebc84eb63 -/
section







/-! The low-bin mean value for every original prime scale, including
bounded scales. The bin restriction stays in place during bounded-slot
removal, and only a fixed profile constant is paid. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open Set Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeDyadic HeckeDetectorZeros HeckePrimeRay HeckePrimeAnnular
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentPrimeSlot ConcretePrimeRowBridge LocalMoment LocalMomentSourceAudit
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyPaidBands
open CenteredMomentRetainedEnergy CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open QuadraticInitialBound
open CenteredMomentEnergyCapacityRemoval
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)


variable {α : Type*} [Fintype α] [DecidableEq α]

theorem actual_joint_low_full_moment
    (W : ℝ → ℂ) (aslot bslot a b radial Bmask L lo hi Mcap εmoment : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0 ≤ bslot)
    (ha : 0 < a) (haUpper : a ≤ 1/4) (hb : 1 ≤ b) (hrad : 0 < radial)
    (hmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hεmoment : 0 < εmoment)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) (hbetaTop : HeckeZeroSupremum.beta ≤ 7/8)
    (Rwidth d τ εslot e κ ηheight loss : ℝ)
    (hRw : 0 < Rwidth) (hd : 0 < d) (hτ : 0 < τ) (hεslot : 0 < εslot)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ ηheight)
    (hbudget : 8*e*Rwidth+κ ≤ εslot)
    (mesh : ℝ) (hmesh : 0 < mesh)
    (hmeshInc : mesh ≤ Cycle25.Energy.commonMesh Mcap Bmask L εmoment)
    (hmeshWidth : mesh ≤ d*Rwidth)
    (hmeshLoss : εmoment+(67/100)*mesh+2*d*εslot*(Fintype.card α) ≤ loss) :
    ∃ (degree : ℕ) (S : Finset (ℕ × ℕ)),
      ∀ (η₀ : Character) (Q : Ideal O) (hQM : Q ≤ M), internalQ Q η₀ ≠ 0 →
      internalQ Q η₀ ≠ ⊤ → internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (J : Finset α) (θ : α → RayQuotient.Characters M H) (w σ v : α → ℝ)
        (t height : ℝ),
      (∀ i, 0 ≤ w i) → (∀ i, w i ≤ mesh) →
      (∀ i, lo ≤ σ i) → (∀ i, σ i ≤ hi) → 0 ≤ height → (∀ i, |v i| ≤ height) →
      ∀ (s : NaturalState Z Bmask radial) (hQ : s.fixedModulus = internalQ Q η₀),
      s.width ≤ Mcap → ∀ (low : O → Prop) (abin : ℝ) (k : ℕ),
      51/100 ≤ abin → abin ≤ 167/200 → 2 ≤ Z^d → 2 < Z^τ →
      (∀ z, ∀ hz : s.radial.keep z, low z → NaturalLowGate M H hH s η₀ Q hQM hQ d τ e abin k z hz) →
      (∀ i ∈ J, |t+v i|+Z^τ/2 ≤ (3*k+2 : ℕ)*Z^τ) →
      (3+(3*k+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^ηheight →
      ∀ (p : Profiles a b) (X₁ X₂ : ℝ), 0 < X₁ → 0 < X₂ → X₁ ≤ Z^L → X₂ ≤ Z^L →
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i : J => primePool M H bslot (Z^(w i)))
        (fun (i : J) I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
          annularWeight W (Z^(w i)) (σ i) (v i) I)
        (fun i : J => Z^(w i)) X₁ X₂ (fun z => s.radial.keep z ∧ low z)
        s.radial.profile s.radial.scale ≤
      C*diagonalControl s.radial.profile*(p.control S)^2*(1+|t|+height)^degree *
        Z^(s.width+(67/450)*max (length Z X₁+length Z X₂+(9/2)*(∑ i ∈ J, w i)-s.width) 0+loss) := by
  obtain ⟨degree,S,hmain⟩ := actual_joint_low_moment (α := α) M H hH W
    aslot bslot a b radial Bmask L lo hi Mcap εmoment haslot hWs hW hbslot
    ha haUpper hb hrad hmask hMcap hεmoment hbeta hbetaTop
    Rwidth d τ εslot e κ ηheight loss hRw hd hτ hεslot he he' hκ hη hbudget
    mesh hmesh hmeshInc hmeshWidth hmeshLoss
  obtain ⟨Cs,hCs,hsmall⟩ := restricted_energy_remove_small_slots (Slot := α) M H
    (fun _ => W) (fun _ => aslot) (fun _ => bslot) lo hi (fun _ => haslot)
    (fun _ => hWs) (fun _ => hW.continuous)
  refine ⟨degree,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,hmain⟩ := hmain η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cs*C,mul_pos (zero_lt_one.trans_le hCs) hC,?_⟩
  filter_upwards [hmain] with Z hmain
  refine ⟨hmain.1,?_⟩
  intro J θ w σ v t height hw hwmesh hσlo hσhi hheight hv s hQ hs low abin k
    habin habinTop hbase hT hlow hfreq hheightSource p X₁ X₂ hX₁ hX₂ hc₁ hc₂
  let Jbig := J ∩ largePrimeSlots (fun _ : α => aslot) (fun _ => bslot) (fun i => Z^(w i))
  have hsub : Jbig ⊆ J := Finset.inter_subset_left
  have hbound := hmain.2 Jbig θ w σ v t height hw hwmesh hσlo hσhi hheight hv
    s hQ hs low abin k habin habinTop hbase hT hlow
    (fun i hi => largePrimeSlots_log_scale _ _ _ i (Finset.mem_inter.mp hi).2)
    (fun i hi => hfreq i (hsub hi)) hheightSource p X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hremove := hsmall s low J (fun i => relativeCharacter M H hH η₀ (θ i))
    (fun i => Z^(w i)) σ v t (p.profile 0) (p.profile 1) X₁ X₂
    (fun i _ => Real.one_le_rpow hmain.1.le (hw i))
    (fun i _ => ⟨hσlo i,hσhi i⟩) hX₁ hX₂
  dsimp only at hremove
  apply hremove.trans
  apply (mul_le_mul_of_nonneg_left hbound (zero_le_one.trans hCs)).trans
  have hsum : (∑ i ∈ Jbig, w i) ≤ ∑ i ∈ J, w i :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hw i)
  have hdef : max (length Z X₁+length Z X₂+(9/2)*(∑ i ∈ Jbig, w i)-s.width) 0 ≤
      max (length Z X₁+length Z X₂+(9/2)*(∑ i ∈ J, w i)-s.width) 0 :=
    max_le_max (by linarith) le_rfl
  have hdiag := diagonalControl_nonneg s.radial.profile
  calc
    _ = (Cs*C)*diagonalControl s.radial.profile*(p.control S)^2*(1+|t|+height)^degree *
        Z^(s.width+(67/450)*max (length Z X₁+length Z X₂+(9/2)*(∑ i ∈ Jbig, w i)-s.width) 0+loss) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hmain.1.le (by linarith)) (by positivity)

/-- The complete literal low mean lies below its child allowance by half
the strict local reserve, once the explicit support and mesh losses fit. -/
theorem actual_joint_low_contribution
    (W : ℝ → ℂ) (aslot bslot a b radial Bmask L lo hi Mcap εmoment : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0 ≤ bslot)
    (ha : 0 < a) (haUpper : a ≤ 1/4) (hb : 1 ≤ b) (hrad : 0 < radial)
    (hmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hεmoment : 0 < εmoment)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) (hbetaTop : HeckeZeroSupremum.beta ≤ 7/8)
    (Rwidth d τ εslot e κ ηheight loss : ℝ)
    (hRw : 0 < Rwidth) (hd : 0 < d) (hτ : 0 < τ) (hεslot : 0 < εslot)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ ηheight)
    (hbudget : 8*e*Rwidth+κ ≤ εslot)
    (mesh : ℝ) (hmesh : 0 < mesh)
    (hmeshInc : mesh ≤ Cycle25.Energy.commonMesh Mcap Bmask L εmoment)
    (hmeshWidth : mesh ≤ d*Rwidth)
    (hmeshLoss : εmoment+(67/100)*mesh+2*d*εslot*(Fintype.card α) ≤ loss) :
    ∃ (degree : ℕ) (S : Finset (ℕ × ℕ)),
      ∀ (η₀ : Character) (Q : Ideal O) (hQM : Q ≤ M), internalQ Q η₀ ≠ 0 →
      internalQ Q η₀ ≠ ⊤ → internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (J : Finset α) (θ : α → RayQuotient.Characters M H) (w σ v : α → ℝ)
        (t height : ℝ),
      (∀ i, 0 ≤ w i) → (∀ i, w i ≤ mesh) →
      (∀ i, lo ≤ σ i) → (∀ i, σ i ≤ hi) → 0 ≤ height → (∀ i, |v i| ≤ height) →
      ∀ (s : NaturalState Z Bmask radial) (hQ : s.fixedModulus = internalQ Q η₀),
      s.width ≤ Mcap → ∀ (low : O → Prop) (abin : ℝ) (k : ℕ),
      51/100 ≤ abin → abin ≤ 167/200 → 2 ≤ Z^d → 2 < Z^τ →
      (∀ z, ∀ hz : s.radial.keep z, low z → NaturalLowGate M H hH s η₀ Q hQM hQ d τ e abin k z hz) →
      (∀ i ∈ J, |t+v i|+Z^τ/2 ≤ (3*k+2 : ℕ)*Z^τ) →
      (3+(3*k+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^ηheight →
      ∀ (p : Profiles a b) (X₁ X₂ : ℝ), 0 < X₁ → 0 < X₂ → X₁ ≤ Z^L → X₂ ≤ Z^L →
      ∀ nominal pad g allowance ledgerLoss : ℝ,
      0 ≤ pad → s.width ≤ nominal+pad → 0 ≤ g → g ≤ 37/10000 →
      3/500 ≤ allowance → 0 ≤ ledgerLoss →
      length Z X₁+length Z X₂+(9/2)*(∑ i ∈ J, w i)-nominal ≤ g+6*(3/500)+ledgerLoss →
      pad+loss+(67/450)*ledgerLoss ≤ 401/9000000 →
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i : J => primePool M H bslot (Z^(w i)))
        (fun (i : J) I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
          annularWeight W (Z^(w i)) (σ i) (v i) I)
        (fun i : J => Z^(w i)) X₁ X₂ (fun z => s.radial.keep z ∧ low z)
        s.radial.profile s.radial.scale ≤
      C*diagonalControl s.radial.profile*(p.control S)^2*(1+|t|+height)^degree *
        Z^(nominal+allowance-401/9000000) := by
  obtain ⟨degree,S,hmain⟩ := actual_joint_low_full_moment (α := α) M H hH W
    aslot bslot a b radial Bmask L lo hi Mcap εmoment haslot hWs hW hbslot
    ha haUpper hb hrad hmask hMcap hεmoment hbeta hbetaTop
    Rwidth d τ εslot e κ ηheight loss hRw hd hτ hεslot he he' hκ hη hbudget
    mesh hmesh hmeshInc hmeshWidth hmeshLoss
  refine ⟨degree,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,hmain⟩ := hmain η₀ Q hQM hQ0 hQt hQ72
  refine ⟨C,hC,?_⟩
  filter_upwards [hmain] with Z hmain
  refine ⟨hmain.1,?_⟩
  intro J θ w σ v t height hw hwmesh hσlo hσhi hheight hv s hQ hs low abin k
    habin habinTop hbase hT hlow hfreq hheightSource p X₁ X₂ hX₁ hX₂ hc₁ hc₂
    nominal pad g allowance ledgerLoss hpad hwidth hg hgcap hallowance hledgerLoss hdefect hbudgetLoss
  have hb := hmain.2 J θ w σ v t height hw hwmesh hσlo hσhi hheight hv s hQ hs
    low abin k habin habinTop hbase hT hlow hfreq hheightSource p X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hwidth := low_nominal_width s.width nominal
    (length Z X₁+length Z X₂+(9/2)*(∑ i ∈ J, w i)) pad hpad hwidth
  have hmax : max (length Z X₁+length Z X₂+(9/2)*(∑ i ∈ J, w i)-nominal) 0 ≤
      g+6*(3/500)+ledgerLoss := max_le hdefect (by linarith)
  have hreserve := local_low_reserve g hgcap
  have hdiag := diagonalControl_nonneg s.radial.profile
  exact hb.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hmain.1.le (by linarith)) (by positivity))

#print axioms actual_joint_low_full_moment
#print axioms actual_joint_low_contribution
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowComplete -/

/- BEGIN ORIGINAL MODULE Analytic.JointLowGate ; sha256 229a156b903ce07186557b0319a02ed9e0a3b64245a80105684da54ec846580d -/
section



/-! The common fixed dictionary upper bin implies the literal low gate
of a source row after exact coefficient transport and finite deletions. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeDetectorZeros HeckeFiniteDeletion
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyState CenteredExceptionalProfile
open HeckeInverseAmplification ConcretePrimeRowBridge LocalMoment
open CenteredMomentSecondHeightFamily ProbeHighRowFamily HeckePrimeRay
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance lowGateFiniteQuotient : Finite (O ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

theorem naturalLowGate_of_joint_maximum {Z Bmask radial : ℝ}
    (s : NaturalState Z Bmask radial) (η η₀ : Character)
    (Q : Ideal O) (hQM : Q ≤ M) (hQ : s.fixedModulus = internalQ Q η₀)
    (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72 : O)})
    (w : NonzeroElement) (hex : ¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 w.val)
    (parent : JointParentLabel η) (N : NaturalRow parent.val w.val)
    (R : Ideal O) (hR : R ≠ 0)
    (z : O) (hz : s.radial.keep z)
    (hcoeff : ∀ I : Ideal O,
      idealCoeff (excluded (naturalRow s.character z (s.row_ne_zero z hz)).character s.puncture) I =
        idealCoeff (excluded N.character R) I)
    (d τ e a : ℝ) (k : ℕ)
    (hupper : zeroMaximum
      (fun label => (momentData (jointRelativeParent η
        (relativeSlotTranslate M H hH (fun _ : Unit => η₀)) label)).character w)
      (jointRelativeMoment_nonprincipal η (relativeSlotTranslate M H hH (fun _ : Unit => η₀))
        (internalQ Q η₀) hQ72
        (relativeSlotTranslate_fixedQ M H hH (fun _ : Unit => η₀) (internalQ Q η₀)
          (inf_le_left.trans hQM) (fun _ => inf_le_right)) w hex)
      (3*(k+1 : ℕ)*Z^τ) < a+2*e)
    (hconductor : ∀ θ : RayQuotient.Characters M H,
      (twistedFamily M H hH ((excluded
        (naturalRow s.character z (s.row_ne_zero z hz)).character s.puncture).product η₀.inverse) θ).modulus.absNorm ≤ Z^d) :
    NaturalLowGate M H hH s η₀ Q hQM hQ d τ e a k z hz := by
  refine ⟨?_,hconductor⟩
  have hnp := jointRelative_ray_nonprincipal M H hH η (fun _ : Unit => η₀)
    (internalQ Q η₀) hQ72 (inf_le_left.trans hQM) (fun _ => inf_le_right)
    w hex parent N () R hR
  have hcompare := jointRelative_ray_zeroMaximum_le M H hH η (fun _ : Unit => η₀)
    (internalQ Q η₀) hQ72 (inf_le_left.trans hQM) (fun _ => inf_le_right)
    w hex parent N () R hR (3*(k+1 : ℕ)*Z^τ)
  have htransfer : zeroMaximum (twistedFamily M H hH ((excluded
      (naturalRow s.character z (s.row_ne_zero z hz)).character s.puncture).product η₀.inverse))
      (naturalState_relative_nonprincipal M H hH s η₀ Q hQM hQ z hz)
      (3*(k+1 : ℕ)*Z^τ) ≤
    zeroMaximum (twistedFamily M H hH ((excluded N.character R).product η₀.inverse))
      hnp (3*(k+1 : ℕ)*Z^τ) := by
    apply zeroMaximum_le_of_zero_inclusion
    intro θ
    refine ⟨θ,?_⟩
    intro q hq hzero
    have he : ∀ I : Ideal O,
        idealCoeff (twistedFamily M H hH ((excluded
          (naturalRow s.character z (s.row_ne_zero z hz)).character s.puncture).product η₀.inverse) θ) I =
        idealCoeff (twistedFamily M H hH ((excluded N.character R).product η₀.inverse) θ) I := by
      intro I
      simp only [twistedFamily,idealCoeff_product,hcoeff I]
    exact (coefficient_equality_positive_zeros _ _ he (hnp θ) hq).mp hzero
  exact (htransfer.trans hcompare).trans_lt hupper

/-- A single threshold absorbs the fixed ray and natural-presentation
constants. The parent itself may vary with the source labels, provided its
literal modulus and the row and puncture satisfy the displayed norm bounds. -/
theorem eventually_natural_relative_conductor
    (η₀ : Character) (ξ : ℝ) (hξ : 0 < ξ) :
    ∀ᶠ Z : ℝ in Filter.atTop, 1 < Z ∧
      ∀ (A W B d : ℝ), A+W+B+ξ ≤ d →
      ∀ (η : Character) (z : O) (N : NaturalRow η z) (R : Ideal O), R ≠ 0 →
      (η.modulus.absNorm : ℝ) ≤ Z^A → ((Ideal.span {z}).absNorm : ℝ) ≤ Z^W →
      (R.radical.absNorm : ℝ) ≤ Z^B →
      ∀ θ : RayQuotient.Characters M H,
        ((twistedFamily M H hH ((excluded N.character R).product η₀.inverse) θ).modulus.absNorm : ℝ) ≤ Z^d := by
  let C : ℕ := fixedConductorFactor*(1+η₀.modulus.absNorm)*M.absNorm
  have hM : 1 ≤ M.absNorm := Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (NeZero.ne M))
  filter_upwards [(tendsto_rpow_atTop hξ).eventually (Filter.eventually_ge_atTop (C : ℝ)),
    Filter.eventually_gt_atTop (1 : ℝ)] with Z hCZ hZ
  refine ⟨hZ,?_⟩
  intro A W B d hd η z N R hR hη hz hRnorm θ
  have hnat := buffered_family_modulus_norm M H hH (fun _ : Unit => η₀)
    N.character R hR (1+η₀.modulus.absNorm) (by omega) (fun _ => by omega) hM
    (some ((),θ))
  have hn := N.natural_modulus_bound
  have hnat' := hnat.trans (Nat.mul_le_mul_right M.absNorm
    (Nat.mul_le_mul_right (1+η₀.modulus.absNorm) (Nat.mul_le_mul_right R.radical.absNorm hn)))
  have hnreal : ((twistedFamily M H hH ((excluded N.character R).product η₀.inverse) θ).modulus.absNorm : ℝ) ≤
      (C : ℝ)*(η.modulus.absNorm : ℝ)*((Ideal.span {z}).absNorm : ℝ)*(R.radical.absNorm : ℝ) := by
    have halg : η.modulus.absNorm*fixedConductorFactor*(Ideal.span {z}).absNorm*
        R.radical.absNorm*(1+η₀.modulus.absNorm)*M.absNorm =
        C*η.modulus.absNorm*(Ideal.span {z}).absNorm*R.radical.absNorm := by dsimp [C];ring
    rw [halg] at hnat'
    exact_mod_cast hnat'
  calc
    _ ≤ (C : ℝ)*(η.modulus.absNorm : ℝ)*((Ideal.span {z}).absNorm : ℝ)*(R.radical.absNorm : ℝ) := hnreal
    _ ≤ Z^ξ*Z^A*Z^W*Z^B := by
      apply mul_le_mul _ hRnorm (Nat.cast_nonneg _) (by positivity)
      apply mul_le_mul _ hz (Nat.cast_nonneg _) (by positivity)
      exact mul_le_mul hCZ hη (Nat.cast_nonneg _) (by positivity)
    _ = Z^(A+W+B+ξ) := by
      rw [←Real.rpow_add (zero_lt_one.trans hZ),←Real.rpow_add (zero_lt_one.trans hZ),
        ←Real.rpow_add (zero_lt_one.trans hZ)]
      congr 1
      ring
    _ ≤ Z^d := Real.rpow_le_rpow_of_exponent_le hZ.le hd

#print axioms eventually_natural_relative_conductor
#print axioms naturalLowGate_of_joint_maximum
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowGate -/

/- BEGIN ORIGINAL MODULE Analytic.JointLowGeometry ; sha256 2ccb223512d91edee9b606f5abf31740d1ae30ada28cb18715c0ad3dc82d452e -/
section




/-! The low-bin exponent is paid from the actual live allocated child's
parent capacity and source volume shift. No lower bound on actual child
width is used. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily CenteredMomentEnergyCanonicalLiveBound
open CenteredMomentEnergyCanonicalLiveCapacity CenteredMomentEnergyDeletedChildCapacity
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedRayDictionary
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedNaturalRadial CenteredMomentRetainedProfile
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyBands CenteredMomentRadialEligibleEnergy
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem live_source_low_nominal_cost (src : Input α) (C R : Ideal O)
    (B : actualAllocations src.pools C) (D : Ideal O)
    (alloc : Allocation D (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val))
    (τ : Character) (rad : Radial) (V₁ V₂ : Plain)
    (v Z X₁ X₂ A M Mnom Mactual pad g geometryLoss clip : ℝ) (w : α → ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (F₁ F₂ : Finset (Ideal O))
    (hZ : 1 < Z) (hw : ∀ i,0 ≤ w i) (hscale : ∀ i,src.P i = Z^(w i))
    (hF₁ : ∀ I ∈ F₁,I ≠ 0) (hF₂ : ∀ I ∈ F₂,I ≠ 0)
    (hparent : A+(7/2)*(∑ i : CenteredMomentCommonProfile.liveIndices B.val,w i.val) ≤ M)
    (hshift : Real.logb Z (X₁*X₂*∏ i : CenteredMomentCommonProfile.liveIndices B.val,src.P i.val)-Mnom ≤
      A-M+6*(3/500)+g+geometryLoss)
    (hwidth : Mactual ≤ Mnom+pad) (hpad : 0 ≤ pad) (hg : 0 ≤ g)
    (hgeometry : 0 ≤ geometryLoss) (hclip : 0 ≤ clip)
    (hclipCost : Real.logb Z (max 1 V₁.b*max 1 V₂.b) ≤ 2*clip)
    (hlive : LiveChild τ rad D alloc V₁ V₂
      (commonData (withHeight src τ v) C R B).slots
      (commonData (withHeight src τ v) C R B).coefficient
      (commonData (withHeight src τ v) C R B).P v X₁ X₂ hX₁ hX₂ F₁ F₂ J) :
    Mactual+(67/450)*max (length Z (scale D alloc X₁ 0 F₁)+
      length Z (scale D alloc X₂ 1 F₂)+(9/2)*(∑ i ∈ originalImage src C B D alloc J,w i)-Mactual) 0 ≤
      Mnom+pad+(67/450)*(6*(3/500)+g+geometryLoss+2*clip) := by
  obtain ⟨z,hz,hφ,hchild⟩ := hlive
  let data := commonData (withHeight src τ v) C R B
  have hP : ∀ i,1 ≤ data.P i := by
    intro i
    change 1 ≤ src.P i.val
    rw [hscale]
    exact Real.one_le_rpow hZ.le (hw i.val)
  have hp : A+(6*(3/4)-1)*(∑ i,Real.logb Z (data.P i)) ≤ M := by
    simp only [data,commonData,withHeight,hscale,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
    norm_num
    exact hparent
  have he := child_excess_from_parent (naturalCharacter τ z) D alloc V₁ V₂
    data.slots data.coefficient data.P v Z X₁ X₂ (3/4) A M Mnom Mnom
    (3/500) 0 (g+geometryLoss) clip hX₁ hX₂ F₁ F₂ J hZ (by norm_num) hP hF₁ hF₂
    hchild hp (by change Real.logb Z (X₁*X₂*∏ i : CenteredMomentCommonProfile.liveIndices B.val,src.P i.val)-Mnom ≤ _; linarith) hclipCost
  rw [original_deleted_excess src C R B D alloc J τ v Z X₁ X₂ (3/4) Mnom w hZ hscale F₁ F₂] at he
  unfold CenteredMomentLiveCapacity.excess at he
  have hnonneg : 0 ≤ 6*(3/500)+g+geometryLoss+2*clip := by linarith
  have he' : max (length Z (scale D alloc X₁ 0 F₁)+length Z (scale D alloc X₂ 1 F₂)+
      (9/2)*(∑ i ∈ originalImage src C B D alloc J,w i)-Mnom) 0 ≤
      6*(3/500)+g+geometryLoss+2*clip := by
    norm_num only at he
    rw [show 9/250+(g+geometryLoss)+2*clip+Mnom-Mnom =
      6*(3/500)+g+geometryLoss+2*clip by ring,max_eq_left hnonneg] at he
    exact he
  have hwidthCost := low_nominal_width Mactual Mnom
    (length Z (scale D alloc X₁ 0 F₁)+length Z (scale D alloc X₂ 1 F₂)+
      (9/2)*(∑ i ∈ originalImage src C B D alloc J,w i)) pad hpad hwidth
  linarith

theorem live_source_low_reserve (nominal pad g geometryLoss clip loss allowance : ℝ)
    (hg : g ≤ 37/10000) (hallowance : 3/500 ≤ allowance)
    (hbudget : pad+loss+(67/450)*(geometryLoss+2*clip) ≤ 401/9000000) :
    nominal+pad+(67/450)*(6*(3/500)+g+geometryLoss+2*clip)+loss ≤
      nominal+allowance-401/9000000 := by
  have h := local_low_reserve g hg
  linarith

#print axioms live_source_low_nominal_cost
#print axioms live_source_low_reserve
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowGeometry -/
