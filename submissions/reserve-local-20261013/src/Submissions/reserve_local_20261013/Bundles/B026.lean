/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.reserve_local_20261013.Bundles.B011
import Submissions.reserve_local_20261013.Bundles.B023
import Submissions.reserve_local_20261013.Bundles.B024
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.DetectorInverseFields
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.DetectorInverseMarkedField
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.DetectorInverseRawField
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.CanonicalErrorSubsets

/- BEGIN ORIGINAL MODULE OAI.NumberTheory.DirichletL.Detector.FinalAssemblyHigh ; sha256 51fff0db37a0e2cab919256b87ac4456ca601991e02fbf8543e2d4e1573cb5e4 -/
section



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeFinalAssembly
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

theorem actual_high_probe_from_raw_moments (N : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0< e) (he1 : e<1/1000) (heps : 0< eps) (hc : 0< c) (hcb : c≤ b) (hA : 0≤ A)
    (hR : 0≤ R) (hdmin : 0< dmin) (hdmax : 0≤ dmax) (hdRange : dmin≤ dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0< mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) (hmargin : 0< margin)
    (hheight : 2*τ< dmin*cost) (hloss : τ*(2+4*eps)< loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ ell j) (hellhi : ∀j,ell j≤ dmin*R)
    (W : Fin N→ℝ→ℝ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,0≤ W j t ∧ W j t≤ A)
    (hcompact : ∀j,HasCompactSupport (W j)) (hne : ∀j,W j≠0)
    (hellsum : ∑j,ell j=1/6)
    (hdtop : dmax≤37/42) (hε1 : ε≤1/1000) (hκ1 : κ≤1)
    (hτzero : τ< dmin/2) (hτheight : 4*τ< dmin*cost)
    (hwbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ε/2)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤ B₀)
    (εm ν logCost heightCost momentCost : ℝ)
    (hεm : 0<εm) (hν : 0<ν)
    (hlog : 0< logCost) (hMomentHeight : τ< heightCost)
    (ζ μ saving : ℝ) (hζ : 0<ζ) (hζ1 : ζ≤1/48) (hμ : 0≤μ)
    (hcount : 159*ε+εm+R+7*ν≤1/32)
    (hfinal : (13/16)*(159*ε+εm+R+7*ν)+2*ζ+(3/2)*μ+
      (26*e+(N+8)*eps+loss+mesh/6)+(logCost+heightCost+momentCost)+saving≤49/440640)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0< nu)
    (dyadCost : ℝ) (hdyadCost : 0< dyadCost)
    (hdmin1 : dmin<1/100) (hconductor : 13/16+ζ+2*margin≤ dmax)
    (hmuMargin : 2*margin≤μ)
    (hβ : (7/8:ℝ)≤ HeckeZeroSupremum.beta)
    (sigma : ℝ) (hsigma : 0< sigma)
    (hgeometric : sigma+8*e+nu≤63/800) (hprincipal : sigma+nu≤17/48000)
    (hwindow : sigma+e≤(7/8)*(dmax*rmin))
    (hfloorbudget : 2*ζ+26*e+(N+8)*eps+loss+mesh/6+nu+sigma≤7/1200)
    (hcentral : sigma+nu+dyadCost≤ saving) (counts : CountParameters M H εm) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃n : ℕ,0< n ∧ ∃C : ℝ,
      0< C ∧
    ∀η : Character,∃Ct : ℝ,0< Ct ∧ ∀ᶠZ : ℝ in atTop,
      let Yp := fun j=> Z^(ell j)
      let T := fun j=> pool (RayQuotient.identityClass M H) S c b (Yp j)
      let _hT := nonfloorPoolOutside M H S N c b Yp
      let WC : Fin N→ℝ→ℂ := fun j y=>(W j y:ℂ)
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (1/6) (slotMass T (residueWeights W Yp)) : ℂ)
      normer≠0 ∧ ∃idx grid : FreeRow→ℕ,
      (∀u,1 ≤ idx u ∧ idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/e⌋₊ ∧
        ((3*idx u+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*idx u+2:ℕ)*Z^τ) ∧
      (∀u, let a : ℝ := 51/100+e*grid u
        (51/100:ℝ)≤ a ∧ a≤1 ∧
        a≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ) ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ)< a+e ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(idx u+1:ℕ)*Z^τ)< a+2*e ∧
        (51/100< a → ∃j s,LFunction (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) s=0 ∧
          ¬((sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j).residue=1 ∧ s=1) ∧
          a≤ s.re ∧ s.re< a+e ∧ |s.im|≤3*idx u*Z^τ)) ∧
      (∀u∈rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ)),
        (calibrationForSet S hmax).residueMonoid u.val≠0 →
        (∀θ,(rayCubeFamily M H hH u θ).residue≠1) ∧
        (∀θ,(rayCubeFamily M H hH u θ).modulus.absNorm≤
          conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm) ∧
        ∀hnp : ∀θ,(rayCubeFamily M H hH u θ).residue≠1,
        HeckeDetectorZeros.zeroMaximum (rayCubeFamily M H hH u) hnp
          (3*(idx u+1:ℕ)*Z^τ)<(51/100:ℝ)+e*grid u+2*e) ∧
      let rows := supportedNonfloorRows S hmax (rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ))) grid
      ∀C0 : ℝ,0≤ C0 →
      (∀k∈smallDyadicIndices (Z^(13/16+ζ)),∀i∈Finset.range (n+1),∀j∈Finset.range (⌊(49/100:ℝ)/e⌋₊+1),
        let rows' := cubeBinRows (rows∩dyadicRows 1 k) idx grid i j
        rows'.Nonempty → ∀t : HeightSpace,
        ((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
        SourceMomentsAt M H hH S hS.prime η rows' ell WC Z
          (sourceDyadConductor Z margin k) (51/100+e*j) ε τ dmax b R mesh i
          ((17/50:ℂ)+t.1.2*Complex.I) (HeckeZeroSupremum.beta-7/8)
          (if 2*(51/100+e*j)-1≤5/6 then counts.cB else counts.cH)
          (if 2*(51/100+e*j)-1≤5/6 then counts.kB else counts.kH)
          (C0*Z^momentCost) (Z^heightCost) εm) →
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun j=> canonicalSlotSupport (T j)) WC Yp (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-11/16) Z‖≤
        (Ct+C*C0*(η.modulus.absNorm:ℝ)^(2*eps))*Z^(HeckeZeroSupremum.beta-11/16-sigma) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have hmin : 0< dmax*rmin := mul_pos (hdmin.trans_le hdRange) hrmin
  obtain ⟨n,hn,htransport⟩ := actual_nonfloor_probe_transport M H hH N e (1/4) c b A ζ 1 τ (dmax*rmin) nu
    he he1 (by norm_num) (by norm_num) hζ hζ1 hτ hc hcb hA hmin hnu hβ S hS hmax hfirst
    ell hello hell hellsum W hW hcompact hWs hWB hne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    hr0 hr1 hp0 hp1 hn0 hn1 sigma hsigma hgeometric hprincipal hwindow (by linarith)
    eps R dmin dmax rmin ε κ cost mesh margin loss heps hR hdmin hdmax hdRange hrmin hε hκ hcost hmesh hmargin
    hbudget hgap hheight hloss (by linarith) hello hellhi hfloorbudget
  have hΔ : 0≤ HeckeZeroSupremum.beta-7/8 := by linarith
  have hΔ1 : HeckeZeroSupremum.beta-7/8≤1/8 := by linarith [HeckeZeroSupremum.beta_le_one]
  obtain ⟨C,hC,hbound⟩ :=
    actual_nonfloor_rows_saving M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss
      he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
      hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hcompact hne hellsum
      hdtop hε1 hκ1 hτzero hτheight hwbudget
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
      εm (HeckeZeroSupremum.beta-7/8) ν logCost heightCost momentCost hεm hΔ hΔ1 hν hlog hMomentHeight
      ζ μ saving hζ.le (by linarith) hμ hcount hfinal W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      hr0 hr1 hp0 hp1 hn0 hn1 nu hnu ⌊(49/100:ℝ)/e⌋₊ dyadCost hdyadCost hdmin1 hconductor hmuMargin counts
  refine ⟨n,hn,C,hC,?_⟩
  intro η
  obtain ⟨Ct,hCt,htransport⟩ := htransport η
  refine ⟨Ct,hCt,?_⟩
  filter_upwards [htransport,hbound η,eventually_ge_atTop (1:ℝ)] with Z ht hb hZ
  dsimp only at ht ⊢
  obtain ⟨hnorm,idx,grid,hlabels,hbins,hray,herror⟩ := ht
  refine ⟨hnorm,idx,grid,hlabels,hbins,hray,?_⟩
  intro C0 hC0 hmom
  let rows := supportedNonfloorRows S hmax (rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ))) grid
  have hrows : ∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧
      (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(13/16+ζ) := by
    intro u hu
    rcases (mem_supportedNonfloorRows S hmax _ grid u).mp hu with ⟨hur,hcal,hg⟩
    have hh := mem_rowBand.mp hur
    exact ⟨hh.1,hh.2.1,hcal,hh.2.2.le⟩
  have hlabel : ∀u∈rows,idx u≤ n ∧ grid u≤⌊(49/100:ℝ)/e⌋₊ ∧ grid u≠0 ∧ 51/100+e*grid u≤1 := by
    intro u hu
    exact ⟨(hlabels u).2.1,(hlabels u).2.2.1,
      ((mem_supportedNonfloorRows S hmax _ grid u).mp hu).2.2,(hbins u).2.1⟩
  have hnext : ∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
      (3*(idx u+1:ℕ)*Z^τ)<51/100+e*grid u+2*e := fun u _=>(hbins u).2.2.2.2.1
  have hcurrent : ∀u∈rows,51/100+e*grid u≤ detectorMaximum
      (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) ((3*idx u:ℕ)*Z^τ) := by
    intro u hu
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using (hbins u).2.2.1
  have hglobal := (hb C0 hC0 rows hrows idx grid hlabel hnext hcurrent hmom).2
  have hexp : Z^(3/16+(HeckeZeroSupremum.beta-7/8)-saving+nu+dyadCost)≤
      Z^(HeckeZeroSupremum.beta-11/16-sigma) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hcentral' := hglobal.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
  have hsum := (norm_add_le _ _).trans (add_le_add herror hcentral')
  simpa only [rows,sub_add_cancel,add_mul] using hsum

end SevenEighths.ProbeFinalAssembly

end

end OAI
end
/- END ORIGINAL MODULE OAI.NumberTheory.DirichletL.Detector.FinalAssemblyHigh -/

/- BEGIN ORIGINAL MODULE Analytic.ActualBinnedUniform ; sha256 4dc26d676c53adce301476dcc04e63785ca09cfb1b9cfa470d35b5fb11f58a56 -/
section



/-!
Actual buffered-row counting, with witness construction and both moment
inputs discharged. The remaining hypotheses are literal arithmetic
coefficient identities, nonprincipality, conductor bounds and buffered
zero maxima for the finite row set being counted.
-/

set_option autoImplicit false

namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate
open Set Filter

namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeDyadic HeckeInverseAmplification
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows
open HeckeDetectorCoefficientTransfer HeckeDetectorDyadicProfiles
open HeckeDetectorRawFiber HeckeDetectorInverseFiberCount
open HeckeDetectorProfiles HeckeDetectorRowwisePolynomial
open ProbeHighRowFamily LocalMoment HeckeDetectorZeros

local notation "O" => HeckeFamily.O

/-- A literal buffered-zero row set obeys the balanced density exponent.

Unlike a conditional moment interface, this theorem takes neither a
moment estimate nor a detector witness as input. Both are constructed
from the existing source theorems. The height is quantified after the
eventual row threshold.
-/
theorem actual_binned_row_count_uniform_geometry {Label : Type*} [Fintype Label]
    (η : Label → Character) (Q : Ideal O) [NeZero Q]
    (hQtop : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (hQη : ∀ label, Q ≤ (η label).modulus)
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (S : Finset (Ideal O))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (εm : ℝ) (hεm : 0 < εm) :
    ∃ (J : ℕ) (C K₀ : ℝ), 0 < C ∧ 0 ≤ K₀ ∧
      ∀ (τ ε e κaux ηaux : ℝ) (I : ℕ)
        (hτ : 0 < τ) (hτzero : τ < 1/2)
    (hτheight : 4*τ < ηaux) (hε : 0 < ε) (hεsmall : ε ≤ 1/1000)
    (he : 0 < e) (hesmall : e < 1/1000)
    (hκ : 0 < κaux) (hκone : κaux ≤ 1) (hη : 0 ≤ ηaux)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κaux+2*ηaux ≤ ε/2)
    (hβupper : HeckeZeroSupremum.beta ≤ 7/8) (hI : 0 < I)
    (hwidth : (49/100 : ℝ) ≤ (I : ℝ)*e),
      ∀ᶠ U : ℝ in atTop, 1 < U ∧
      ∀ (rows : Finset FreeRow) (χ : FreeRow → Label → Character)
        (reverse : Label → Bool) (hχ : ∀ u j, (χ u j).residue ≠ 1),
      (∀ u ∈ rows, ((Ideal.span {u.val}).absNorm : ℝ) ≤ U) →
      (∀ u ∈ rows, ∀ j I,
        idealCoeff (χ u j) I =
          if reverse j then starRingEnd ℂ (idealCoeff ((momentData (η j)).character ⟨u.val, u.property.1⟩) I)
          else idealCoeff ((momentData (η j)).character ⟨u.val, u.property.1⟩) I) →
      (∀ u ∈ rows, ∀ j, ((χ u j).modulus.absNorm : ℝ) ≤ U) →
      ∀ (a height : ℝ), 167/200 ≤ a → a ≤ 7/8 →
      (∀ u ∈ rows, a ≤ zeroMaximum (χ u) (hχ u) (U^τ)) →
      2 < U^τ → 0 ≤ height →
      2*Real.pi*U^(τ/2)+((3*I : ℕ) : ℝ)*U^τ ≤ height →
      (rows.card : ℝ) ≤ ((I : ℝ)+1)^2 *
        (((Fintype.card Label : ℝ)*(dyadicLength U : ℝ)^2 *
          fiberConstant (C*(1+height)^J) height K₀) *
          U^(unmarkedDensity (2*a-1)+156*ε+εm+3*e)) := by
  obtain ⟨J, C, K₀, hC, hK₀, hactualBase⟩ := actual_buffered_row_count_uniform_geometry
    η Q hQtop hQ72 hQη hβ M H hH S φ hφ hφc hφp hφ0 hφne
    a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨J, C, K₀, hC, hK₀, ?_⟩
  intro τ ε e κaux ηaux I hτ hτzero hτheight hε hεsmall he hesmall hκ hκone hη hbudget
    hβupper hI hwidth
  have hactual := hactualBase τ ε e κaux ηaux I
    hτ hτzero hτheight hε hεsmall he hesmall hκ hκone hη hbudget
  filter_upwards [hactual] with U hU
  refine ⟨hU.1, ?_⟩
  intro rows χ reverse hχ hrow hcoeff hconductor a height ha haupper hinitial hT hh hheight
  let K : ℝ := (Fintype.card Label : ℝ)*(dyadicLength U : ℝ)^2 *
    fiberConstant (C*(1+height)^J) height K₀
  have hK : 0 ≤ K := by
    dsimp [K, fiberConstant]
    positivity
  have hresult := buffered_count_of_bin_counts χ hχ rows U (U^τ) e K
    (156*ε+εm) a I hU.1 hT he hesmall hI hwidth hK hβupper ha haupper hinitial
    (by
      intro s hs b i hi hb hbupper hnext hcurrent
      have hTpos : 0 < U^τ := Real.rpow_pos_of_pos (by linarith [hU.1]) _
      have hiR : (i : ℝ) ≤ I := by exact_mod_cast hi
      have hheighti : 2*Real.pi*U^(τ/2)+((3*i : ℕ) : ℝ)*U^τ ≤ height := by
        simp only [Nat.cast_mul, Nat.cast_ofNat] at hheight ⊢
        nlinarith
      have hbcount := hU.2 s (fun u => χ u.val) reverse (fun u j => hχ u.val j)
        (by intro u hu; exact hrow u (hs hu))
        (by intro u j L; exact hcoeff u.val (hs u.property) j L)
        b height i hi hb hbupper
        (by intro u; simpa [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using hnext u.val u.property)
        (by intro u; simpa [Nat.cast_mul, Nat.cast_ofNat] using hcurrent u.val u.property)
        (by intro u j; exact hconductor u.val (hs u.property) j)
        hh hheighti
      simpa only [K, add_assoc] using hbcount)
  simpa only [K, add_assoc] using hresult

#print axioms actual_binned_row_count_uniform_geometry
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.ActualBinnedUniform -/

/- BEGIN ORIGINAL MODULE Analytic.ActualNaturalRows ; sha256 8c7059ea6dcd2855e01059986170d53408d9dd5d46fcdb5ff701a5526ee7366c -/
section


/-! Exact natural characters for the joint first-column / second-frequency
rows. All conductor information is supplied by the existing NaturalRow
construction. The Euler puncture is retained literally. -/

set_option autoImplicit false

namespace OAI
noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.Local44.Analytic
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CenteredMomentCanonicalFirst CenteredMomentActive
open HeckeFamily CenteredMomentSecondHeightFamily CenteredMomentSourceRow
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow
open CenteredMomentNaturalRowSource CenteredMomentFirstPhysicalSource
open CenteredMomentSupportedCorrelation RayFourExpansion

local notation "O" => ActualEisensteinCubic.O

theorem active_product_pow_ne_zero (C D : Ideal O) (hC : Supported C)
    (k : ActiveIndex C D → ℕ) : (∏ i, activePrimary C D i ^ k i) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact pow_ne_zero _ (supported_element_ne_zero _ (activePrimary_supported C D hC i))

/-- The actual source pair is represented by existing natural row characters
over a fixed parent dictionary, followed by explicit finite Euler deletion.
There is no new analytic hypothesis in this coefficient theorem. -/
theorem actual_source_natural_rows (η : Character) (C D : Ideal O)
    (hC : Supported C) (E : Finset (CommonIndex C D)) (ξ₁ ξ₂ : RayCharacter)
    (F : FixedPair η C D hC E ξ₁ ξ₂) :
    ∃ u : Oˣ, ∃ τL ∈ fixedParentDictionary η, ∃ τR ∈ fixedParentDictionary η,
      activeConductor C D = (u : O) * ∏ i, activePrimary C D i ∧
      ∀ j : O, j ≠ 0 →
        let wL := primeSubsetGenerator (fun P : CommonIndex C D => P.val) E *
          (u : O) * leftEffectiveFactor C D * j
        let wR := primeSubsetGenerator (fun P : CommonIndex C D => P.val) E *
          (u : O) * rightEffectiveFactor C D * j
        ∃ NL : NaturalRow τL wL, ∃ NR : NaturalRow τR wR,
          ∀ t : ℝ, ∀ I : Ideal O,
            (rowWeight F.left fixedBadMask 1 j t I =
              heightCoeff (excluded NL.character (canceledIdeal C D 5)) t I) ∧
            (rowWeight F.right fixedBadMask 1 j t I =
              heightCoeff (excluded NR.character (canceledIdeal C D 1)) t I) := by
  obtain ⟨u, τL, hτL, τR, hτR, hu, hrows⟩ :=
    actual_source_rows_fixed_parent η C D hC E ξ₁ ξ₂ F
  refine ⟨u, τL, hτL, τR, hτR, hu, ?_⟩
  intro j hj
  dsimp only
  have he := primeSubsetGenerator_ne_zero (fun P : CommonIndex C D => P.val) E
  have hL : leftEffectiveFactor C D ≠ 0 := active_product_pow_ne_zero C D hC _
  have hR : rightEffectiveFactor C D ≠ 0 := active_product_pow_ne_zero C D hC _
  let NL := naturalRow τL
    (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E *
      (u : O) * leftEffectiveFactor C D * j)
    (mul_ne_zero (mul_ne_zero (mul_ne_zero he u.ne_zero) hL) hj)
  let NR := naturalRow τR
    (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E *
      (u : O) * rightEffectiveFactor C D * j)
    (mul_ne_zero (mul_ne_zero (mul_ne_zero he u.ne_zero) hR) hj)
  refine ⟨NL, NR, ?_⟩
  intro t I
  constructor
  · exact (hrows j t I).1.trans (naturalRow_canceled_height NL C D hC 5 t I).symm
  · exact (hrows j t I).2.trans (naturalRow_canceled_height NR C D hC 1 t I).symm

#print axioms actual_source_natural_rows

end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.ActualNaturalRows -/

/- BEGIN ORIGINAL MODULE Analytic.JointErrorSubsets ; sha256 b3ea82b0afd5bef5adb88f62d4a18f159560574f5634f5e6c7cd420b1bb4805e -/
section



/-! Refined powers for the actual extracted Gaussian source. -/
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
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
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
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
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

theorem refined_original_subsets_error_power
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤ Mslot)(hεmask:0<εmask)(haPlain:0< a)(hbPlain:0≤ b)
    (L:ℝ)(hL:0≤ L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0< aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤ Mcap)(hLs:0≤ Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)(hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκ:2*HeckeZeroSupremum.beta-1≤κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0< lower)(hupper:1≤ upper)
    (ha0:0< a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤ highs i)
    (εsrc δsrc θsrc Bcap Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hBcap:0≤ Bcap)(hξ:0<ξ)
    (sigma cost:ℝ)(hsigma:0< sigma)(hξsmall:ξ≤ sigma/4)(hcost:1≤ cost):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤ M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃Cbound:ℝ,0< Cbound ∧ ∃Z₀:ℝ,1< Z₀ ∧
    ∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤ Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤ C₀ → 0≤ C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤ mesh → (∀i,0≤ w i) → (∀i,w i≤ mesh) →
    (∀i,w i≤ Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) → 0≤ height → (∀i,|freq i|≤ height) →
    ∀src:Input Aorig,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤ bslot) → (∀i,src.M i≤ Mslot) →
    (∀i,src.lo i=lows i.val) → (∀i,src.hi i=highs i.val) →
    Fintype.card Aorig≤ N → lower≤ src.lower → src.upper≤ upper →
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
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤ Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤ Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤ Mwidth →
    Mwidth-sigma/2≤ Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    asource≤ CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    ∀r:ℝ,Z^r≤ input.X₁ → Z^r≤ input.X₂ → Z^r≤ input.Y₁ → Z^r≤ input.Y₂ →
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    normalizedGaussSource input ((R0*C)*(Ideal.span {prime})^(k+1)) seed
      CenteredMomentFirstAmplificationChoice.ballProfile Kerror≤
      (∑j,(Cbound*(C₀+C₁+1)*(p.control Uprofile)^2*(1+|v0|+height)^Jheight*
        Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm:ℝ))*
        CenteredMomentFirstAmplifiedFourCoefficients.errorPowers prime (k+1)
        (τ.modulus.absNorm:ℝ) Z Kerror
        (refinedErrorDeficit prime Z (k+1) sigma (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)))) paid saving r j*
        (volume input)^(powers εsrc j))*mass input^2 :=by
  have hmain (Aorig:Finset α):=
    refined_error_homogeneous (α:=Aorig) M H hH
      Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
      L hL degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ N lower upper a0 θsource
      hlower hupper ha0 hθsource (fun i=> lows i.val) (fun i=> highs i.val)
      (fun i=> hhighs i.val) εsrc δsrc θsrc Bcap Bseed ξ saving
      hεsrc hδsrc hθsrc hBcap hξ sigma cost hsigma hξsmall hcost
  choose Uj Jj hj using hmain
  let Uprofile:Finset (ℕ×ℕ):=Finset.univ.biUnion Uj
  let Jheight:ℕ:=∑Aorig:Finset α,Jj Aorig
  refine ⟨Uprofile,Jheight,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  choose Cj hCj Zj hZj hconsume using fun Aorig=> hj Aorig η₀ Q hQM hQ0 hQt hQ72
  let Cbound:ℝ:=1+∑Aorig:Finset α,Cj Aorig
  let Z₀:ℝ:=2+∑Aorig:Finset α,|Zj Aorig|
  have hCbound:0< Cbound:=by
    have hh:=Finset.sum_nonneg (fun Aorig (_:Aorig∈(Finset.univ:Finset (Finset α)))=>(hCj Aorig).le)
    dsimp [Cbound];linarith
  have hZ₀:1< Z₀:=by
    have hh:=Finset.sum_nonneg (fun Aorig (_:Aorig∈(Finset.univ:Finset (Finset α)))=> abs_nonneg (Zj Aorig))
    dsimp [Z₀];linarith
  have hCC (Aorig:Finset α):Cj Aorig≤ Cbound:=by
    have hh:=Finset.single_le_sum (fun A (_:A∈(Finset.univ:Finset (Finset α)))=>(hCj A).le)
      (Finset.mem_univ Aorig)
    dsimp [Cbound];linarith
  have hZZ (Aorig:Finset α):Zj Aorig≤ Z₀:=by
    have hh:=Finset.single_le_sum (fun A (_:A∈(Finset.univ:Finset (Finset α)))=> abs_nonneg (Zj A))
      (Finset.mem_univ Aorig)
    dsimp [Z₀];linarith [le_abs_self (Zj Aorig)]
  refine ⟨Cbound,hCbound,Z₀,hZ₀,?_⟩
  intro Aorig θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve asource hK hasource hdelta hreserve haSource
    prime hprime k hk hprimeScale hslot Bp υ χerr v0 hN hυ input hinput
  dsimp only
  intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower r hr1 hr2 hr3 hr4
  have hposA:=positiveAt_subtype M H hH Aorig Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
    Mcap εchild κ Z η₀ Q degree S C₁ hpos
  have hg:=hconsume Aorig θ Z ((hZZ Aorig).trans hZ) εchild C₀ C₁ hC₀ hC₁ hzero hposA
    w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve asource hK hasource hdelta hreserve haSource
    prime hprime k hk hprimeScale hslot Bp υ χerr v0 hN hυ input hinput
    hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower r hr1 hr2 hr3 hr4
  dsimp only at hg ⊢
  have hsub:Uj Aorig⊆Uprofile:=by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨Aorig,Finset.mem_univ _,hx⟩
  have hp:p.control (Uj Aorig)≤ p.control Uprofile:=by
    unfold Profiles.control
    exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono hsub) (p.profile 0))
      (Seminorm.le_def.mp (Finset.sup_mono hsub) (p.profile 1))
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hJ:Jj Aorig≤ Jheight:=Finset.single_le_sum (fun _ _=> Nat.zero_le _) (Finset.mem_univ Aorig)
  have hz:0< Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  have hp0:=p.control_nonneg (Uj Aorig)
  have hp1:=p.control_nonneg Uprofile
  have hh:(1+|v0|+height)^(Jj Aorig)≤(1+|v0|+height)^Jheight:=
    pow_le_pow_right₀ (by linarith [abs_nonneg v0]) hJ
  have hfront:Cj Aorig*(C₀+C₁+1)*(p.control (Uj Aorig))^2*(1+|v0|+height)^(Jj Aorig)≤
      Cbound*(C₀+C₁+1)*(p.control Uprofile)^2*(1+|v0|+height)^Jheight:=by
    have hc:=hCC Aorig
    have hc0:0≤ Cj Aorig:=(hCj Aorig).le
    gcongr
  apply hg.trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (volume_pos _).le _)
  apply mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hfront (Real.rpow_nonneg hz.le _)) (Nat.cast_nonneg _))
  fin_cases j <;> simp only [CenteredMomentFirstAmplifiedFourCoefficients.errorPowers,Matrix.cons_val,Fin.reduceFinMk] <;>
    try unfold errorCommonRadius
  all_goals positivity

#print axioms refined_original_subsets_error_power
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointErrorSubsets -/

/- BEGIN ORIGINAL MODULE Analytic.LocalReserve ; sha256 5b4e84e590b19bca5a36dd17b164ca8173a462bf297bf843bd22a0f07a8d2d19 -/
section


/-! Exact rational reserves for the local cost-22/5 ledger. These are
arithmetic consequences, not an assertion of the analytic moment. -/
set_option autoImplicit false
namespace OAI
noncomputable section
namespace SevenEighths.Local44.Analytic
open LocalMoment

theorem local_density_bounds (δ : ℝ) (hδ : 67/100 ≤ δ) (hδ' : δ ≤ 3/4) :
    2/7 ≤ unmarkedDensity δ ∧ unmarkedDensity δ ≤ 214/549 ∧
    1 < unmarkedDensity δ+δ ∧ 1 < 5*unmarkedDensity δ ∧
    0 ≤ 4*unmarkedDensity δ-1 := by
  have hden : 0 < 3*(5-2*δ) := by linarith
  have hlo := unmarkedDensity_ge_two_sevenths hδ'
  have hu : unmarkedDensity δ ≤ 214/549 := by
    have hq : (335/549 : ℝ) ≤ 10*δ/(3*(5-2*δ)) :=
      (le_div_iff₀ hden).mpr (by linarith)
    unfold unmarkedDensity
    linarith
  have hs : 1 < unmarkedDensity δ+δ := by
    have hp : 0 < δ*(5-6*δ) := mul_pos (by linarith) (by linarith)
    have hq : 10*δ/(3*(5-2*δ)) < δ :=
      (div_lt_iff₀ hden).mpr (by nlinarith)
    unfold unmarkedDensity
    linarith
  exact ⟨hlo, hu, hs, by linarith, by linarith⟩

theorem local_label_coefficient (δ : ℝ) (hδ : 67/100 ≤ δ) (hδ' : δ ≤ 3/4) :
    4*unmarkedDensity δ-1-δ ≤ -6083/54900 := by
  have h := (local_density_bounds δ hδ hδ').2.1
  linarith

def localHighReserve (δ : ℝ) : ℝ :=
  unmarkedDensity δ-1+(883/1000)*δ+(3/500)*(5-6*unmarkedDensity δ)

theorem local_high_reserve (δ : ℝ) (hδ : 67/100 ≤ δ) (hδ' : δ ≤ 3/4) :
    localHighReserve δ ≤ -144011/54900000 := by
  have hden : 0 < 3*(5-2*δ) := by linarith
  have hid : (localHighReserve δ+144011/54900000)*(3*(5-2*δ)) =
      -(2649/500)*(δ-67/100)^2-(31787639/9150000)*(δ-67/100) := by
    unfold localHighReserve unmarkedDensity
    field_simp [show 5-2*δ ≠ 0 by linarith, show 5-δ*2 ≠ 0 by linarith]
    <;> ring
  have hp : (localHighReserve δ+144011/54900000)*(3*(5-2*δ)) ≤ 0 := by
    rw [hid]
    nlinarith [sq_nonneg (δ-67/100)]
  by_contra hn
  have hh : 0 < (localHighReserve δ+144011/54900000)*(3*(5-2*δ)) :=
    mul_pos (by linarith) hden
  linarith

/-- Here m=min(c,d), t=(c-d)₊ and c=m+t. The discarded labels have
nonnegative widths, and the effective factor loses canceled primes. -/
theorem local_joint_label_reserve (δ m t p R R₀ E B L : ℝ)
    (hδ : 67/100 ≤ δ) (hδ' : δ ≤ 3/4)
    (ht : 0 ≤ t) (hp : 0 ≤ p) (hmp : p ≤ m) (hRp : R ≤ p)
    (hR₀ : 0 ≤ R₀) (hE : 0 ≤ E) (hB : 0 ≤ B)
    (hL : L ≤ 5*(R-R₀)) :
    (1-unmarkedDensity δ)*t-δ*(m+t)-(1+unmarkedDensity δ)*R-E-B+
        unmarkedDensity δ*L+R₀ ≤ 0 := by
  let ρ := unmarkedDensity δ
  obtain ⟨hρlow, hρup, hρδ, h5ρ, h4ρ⟩ := local_density_bounds δ hδ hδ'
  change 2/7 ≤ ρ at hρlow
  change 1 < ρ+δ at hρδ
  change 1 < 5*ρ at h5ρ
  change 0 ≤ 4*ρ-1 at h4ρ
  have hL' : ρ*L ≤ ρ*(5*(R-R₀)) :=
    mul_le_mul_of_nonneg_left hL (by linarith)
  have hm' : -δ*m ≤ -δ*p := mul_le_mul_of_nonpos_left hmp (by linarith)
  have hR' : (4*ρ-1)*R ≤ (4*ρ-1)*p :=
    mul_le_mul_of_nonneg_left hRp h4ρ
  have ht' : (1-ρ-δ)*t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) ht
  have hR₀' : (1-5*ρ)*R₀ ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hR₀
  have hc := local_label_coefficient δ hδ hδ'
  change 4*ρ-1-δ ≤ _ at hc
  have hp' : (4*ρ-1-δ)*p ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hp
  change (1-ρ)*t-δ*(m+t)-(1+ρ)*R-E-B+ρ*L+R₀ ≤ 0
  nlinarith

theorem local_second_label_reserve (δ b g t : ℝ)
    (hδ : 0 ≤ δ) (hb : 0 ≤ b) (hg : g ≤ b) (ht : 0 ≤ t) :
    g-t-(1+δ)*b ≤ 0 := by
  nlinarith [mul_nonneg hδ hb]

theorem local_high_ledger_reserve (δ A m t p R R₀ E B L b₂ g₂ t₂ : ℝ)
    (hδ : 67/100 ≤ δ) (hδ' : δ ≤ 3/4) (hA : A ≤ 883/1000)
    (ht : 0 ≤ t) (hp : 0 ≤ p) (hmp : p ≤ m) (hRp : R ≤ p)
    (hR₀ : 0 ≤ R₀) (hE : 0 ≤ E) (hB : 0 ≤ B)
    (hL : L ≤ 5*(R-R₀)) (hb₂ : 0 ≤ b₂) (hg₂ : g₂ ≤ b₂) (ht₂ : 0 ≤ t₂) :
    unmarkedDensity δ-1+δ*A+(3/500)*(5-6*unmarkedDensity δ)+
      ((1-unmarkedDensity δ)*t-δ*(m+t)-(1+unmarkedDensity δ)*R-E-B+
        unmarkedDensity δ*L+R₀)+g₂-t₂-(1+δ)*b₂ ≤ -144011/54900000 := by
  have hfirst := local_high_reserve δ hδ hδ'
  have hlabels := local_joint_label_reserve δ m t p R R₀ E B L
    hδ hδ' ht hp hmp hRp hR₀ hE hB hL
  have hsecond := local_second_label_reserve δ b₂ g₂ t₂ (by linarith) hb₂ hg₂ ht₂
  have hA' := mul_le_mul_of_nonneg_left hA (show 0 ≤ δ by linarith)
  unfold localHighReserve at hfirst
  linarith

theorem local_low_reserve (g : ℝ) (hg : g ≤ 1/250) :
    1/22500 ≤ 3/500-(67/450)*(g+6*(3/500)) := by linarith

theorem local_amplification_error_reserves (g lam : ℝ)
    (hg : g ≤ 1/250) (hlam : 9/2000 ≤ lam) :
    1/1200 ≤ lam-(g+9/500+lam-lam)/6 ∧
    1/1200 ≤ 6*lam-(g+9/500+6*lam)/6 ∧
    1/1200 ≤ 7*lam-(g+9/500+7*lam-lam)/6 := by
  constructor <;> [linarith; constructor <;> linarith]

theorem local_exceptional_reserves (A : ℝ) (hA : A ≤ 883/1000) :
    A-1+5*(3/500) ≤ -87/1000 ∧
    A-1+4*(3/500) ≤ -93/1000 ∧
    A-1+3*(9/500) ≤ -63/1000 := by
  constructor <;> [linarith; constructor <;> linarith]

#print axioms local_high_ledger_reserve
#print axioms local_amplification_error_reserves
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.LocalReserve -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.MomentDetectorInverseFields ; sha256 a7b29f838c1b7b5d282ffad34827643eae7e73a0fe9dd466d9019135d528f9ac -/
section





namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
namespace SevenEighths.Cycle25ProbeDetectorInverseFields
open ProbeDetectorInverseFields Cycle25ProbeFinalAssembly
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseMoment
open HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorCoefficientTransfer
open ProbeHighRowFamily ProbeFinalAssembly Filter
local notation "O"=> HeckeFamily.O
variable (M:Ideal O)[NeZero M]
local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M ≤ H)
local instance:Fintype (Sum Bool (RayQuotient.Characters M H)):=Fintype.ofFinite _

private lemma raw_mono (data:RowData)(W:ℝ→ℂ)(c κ A B:ℝ)
    (hAB:A ≤ B)(h:RawMoment data W c κ A):RawMoment data W c κ B:=by
  intro X D hX hD hcap rows hrows
  apply (h X D hX hD hcap rows hrows).trans
  gcongr

theorem weighted_source_batch_inverse_fields {D:Cycle25.Weighted.MomentData}
    (S:WeightedSourceData D)(counts:Cycle25ProbeHighRowFamily.CountParameters M H D.t):
    ∃J:ℕ,∀η:Character,∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,
    1< Z ∧ ∀d:ℝ,(1/200:ℝ) ≤ d →
    ∀(a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin D.N)
        (Z^d) a ε tstar T allowance i),
      B.data=sourceMomentData M H hH S.S S.exclusions.prime η →
      B.profile=(fun _ x=>(S.w x:ℂ)) → B.upper=(fun _=>2) →
      B.widths=(fun s=> D.ell s/d) → (∀s,(B.external s).re=17/50) →
    ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
    ∀height:ℝ,0 ≤ height →
    let F:=B.fiber bin label left right hne;
    (∀n:ℕ,n ≤ 2 → ∀s∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
      let W:=twistProfile (logTest (orientedProfile F.reverse F.inverseProfile) n) s t;
      RawMoment F.rowData W counts.c
        counts.k (C*(1+height)^J) ∧
      RawMoment F.rowData (scaleProfile W) counts.c
        counts.k (C*(1+height)^J)) ∧
    (∀selected:Finset (Fin D.N),selected⊆F.slots →
      F.r+2*(∑s∈selected,F.widths s)<1 → 2*F.r+8*(∑s∈selected,F.widths s)<3 →
      ∀n:ℕ,n ≤ 2 → ∀s∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
        (∑u∈F.rows,‖polynomial (F.family u F.label) true
          ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile)
          ((Z^d)^F.r) s t*F.physicalProduct selected u‖^2) ≤
          (C*(1+height)^J)*(Z^d)^(1+D.t)) := by
  obtain ⟨Jr,hr⟩ := Cycle25ProbeDetectorInverseRawField.source_batch_inverse_raw
    M H hH S.S S.exclusions.prime D.t counts
  obtain ⟨Jm,hm⟩ := Cycle25ProbeDetectorInverseMarkedField.weighted_source_batch_inverse_marked M H hH S
  refine ⟨Jr+Jm,?_⟩
  intro η
  obtain ⟨Cr,hCr,hr⟩ := hr η
  obtain ⟨Cm,hCm,hm⟩ := hm η
  refine ⟨Cr+Cm,add_pos hCr hCm,?_⟩
  filter_upwards [hm] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro d hd a ε tstar T allowance i B hdata hprofile hupper hwidths hex
    bin label left right hne height hheight F
  have hU:0< Z^d := Real.rpow_pos_of_pos (zero_lt_one.trans hZ.1) _
  have hscale:1 ≤ 1+height := by linarith
  have hraw:Cr*(1+height)^Jr ≤ (Cr+Cm)*(1+height)^(Jr+Jm) := by
    apply mul_le_mul
    · linarith
    · exact pow_le_pow_right₀ hscale (Nat.le_add_right _ _)
    · positivity
    · positivity
  have hmarked:Cm*(1+height)^Jm ≤ (Cr+Cm)*(1+height)^(Jr+Jm) := by
    apply mul_le_mul
    · linarith
    · exact pow_le_pow_right₀ hscale (Nat.le_add_left _ _)
    · positivity
    · positivity
  constructor
  · intro n hn s hs t ht
    have hh:=hr hU B hdata bin label left right hne height hheight n hn s hs t ht
    exact ⟨raw_mono _ _ _ _ _ _ hraw hh.1,raw_mono _ _ _ _ _ _ hraw hh.2⟩
  · intro selected hselected hfirst hsecond n hn s hs t ht
    have hh:=hZ.2 d hd a ε tstar T allowance i B hdata hprofile hupper hwidths hex
      bin label left right hne height hheight selected hselected hfirst hsecond n hn s hs t ht
    exact hh.trans (mul_le_mul_of_nonneg_right hmarked (Real.rpow_nonneg hU.le _))

end SevenEighths.Cycle25ProbeDetectorInverseFields

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.MomentDetectorInverseFields -/
