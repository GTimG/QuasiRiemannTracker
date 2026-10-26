/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B000
import Candidate.Bundles.B025
import Candidate.Bundles.B032
import Candidate.Bundles.B042

/- BEGIN ORIGINAL Cycle61.Assembly.Transport.HighApproximation; sha256 15f12659163d4f0484f7f2f6479a5cbff6ec35af489bb73800bfb8c5e772e42e -/
section
                                                

set_option autoImplicit false

namespace OAI
noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set Asymptotics
namespace SevenEighths.Cycle61HighTransport
open ProbeHighRowFamily HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
open ProbeRaySlots PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O

private theorem numeratorPoolOutside {K : ℕ} (M : Ideal O) (H : Subgroup (O ⧸ M)ˣ)
    (S : Finset (Ideal O)) (a b : ℝ) (Y : Fin K→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S a b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S a b (Y j) P).mp hP |>.2.2.2

theorem selected_row_within_density_cutoff {Z ζ : ℝ} {u : FreeRow}
    (hZ : 1≤Z) (hζ : ζ≤1/10000000000)
    (hu : u∈rowBand (Z^(1/100:ℝ)) (Z^(Cycle61.Arithmetic.h+ζ))) :
    rowNorm u ≤ Z^Cycle61.Arithmetic.dPlus := by
  exact (mem_rowBand.mp hu).2.2.le.trans
    (Real.rpow_le_rpow_of_exponent_le hZ (Cycle61.Transport.extended_row_cutoff hζ))

/-- The literal finite numerator left after the proved floor and tail transport. -/
def finiteNonfloorNumerator {K : ℕ} (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (slotEll : Fin K→ℝ) (a b ζ e τ : ℝ)
    (W : Fin K→ℝ→ℝ) (W0 W1 : SchwartzMap ℝ ℂ) (η : Character) (Z : ℝ)
    (idx grid : FreeRow→ℕ) : ℂ :=
  let Yp := fun j=>Z^(slotEll j)
  let T := fun j=>pool (RayQuotient.identityClass M H) S a b (Yp j)
  let hT := numeratorPoolOutside M H S a b Yp
  let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
  finiteCentralCubeRows S hS hmax η
    (supportedNonfloorRows S hmax (rowBand (Z^(1/100:ℝ)) (Z^(Cycle61.Arithmetic.h+ζ))) grid)
    T hT WC Yp W0 W1 (Z^Cycle61.Arithmetic.x) (Z^Cycle61.Arithmetic.y) Z e
    (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)

def actualNormalizer {K : ℕ} (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (S : Finset (Ideal O)) [NeZero (∏P∈S,P)]
    (slotEll : Fin K→ℝ) (a b : ℝ) (W : Fin K→ℝ→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (Z : ℝ) : ℂ :=
  let Yp := fun j=>Z^(slotEll j)
  let T := fun j=>pool (RayQuotient.identityClass M H) S a b (Yp j)
  sourceResidueConstant W0 W1 (∏P∈S,P)*
    (Probe.principalScalar Finset.univ Z Cycle61.Arithmetic.ell
      (slotMass T (residueWeights W Yp)) : ℂ)

/-- Selection and zero facts are conclusions of actual transport, not analytic inputs. -/
def ActualBufferedSelection (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (ζ e τ : ℝ) (n : ℕ) (Z : ℝ) (idx grid : FreeRow→ℕ) : Prop :=
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
      (∀u∈rowBand (Z^(1/100:ℝ)) (Z^((Cycle61.Arithmetic.h:ℝ)+ζ)),
        (calibrationForSet S hmax).residueMonoid u.val≠0 →
        (∀θ,(rayCubeFamily M H hH u θ).residue≠1) ∧
        (∀θ,(rayCubeFamily M H hH u θ).modulus.absNorm≤
          conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm) ∧
        ∀hnp : ∀θ,(rayCubeFamily M H hH u θ).residue≠1,
        HeckeDetectorZeros.zeroMaximum (rayCubeFamily M H hH u) hnp
          (3*(idx u+1:ℕ)*Z^τ)<(51/100:ℝ)+e*grid u+2*e)

/-- Remaining analytic integration obligation: the literal finite full-W numerator,
uniform before the actual buffered choices. No probe or signal bound is assumed. -/
def FiniteNonfloorNumeratorBound {K : ℕ} (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (slotEll : Fin K→ℝ) (a b ζ e τ sigma : ℝ) (W : Fin K→ℝ→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (n : ℕ) (η : Character) : Prop :=
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,∀idx grid : FreeRow→ℕ,
    ActualBufferedSelection M H hH S hS hmax η ζ e τ n Z idx grid →
    ‖finiteNonfloorNumerator M H S hS hmax slotEll a b ζ e τ W W0 W1 η Z idx grid‖ ≤
      C*‖actualNormalizer M H S slotEll a b W W0 W1 Z‖*
        Z^(HeckeZeroSupremum.beta+Cycle61.Assembly.signalShift-sigma)

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

theorem normalizedProbe_high_of_finite_nonfloor_numerator (K : ℕ) (e δ a b B ζ saving τ ellMin nu : ℝ)
    (he : 0 < e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (hζ' : ζ≤1/10000000000) (hτ : 0<τ)
    (ha : 0 < a) (hab : a ≤ b) (hB : 0 ≤ B) (hmin : 0 < ellMin) (hnu : 0 < nu)
    (hβlo : Cycle61.Arithmetic.theta ≤ HeckeZeroSupremum.beta)
    (hβ : HeckeZeroSupremum.beta ≤ (7/8:ℝ))
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (ell : Fin K→ℝ) (hell : ∀j,ellMin ≤ ell j) (hellinj : Function.Injective ell) (hellsum : ∑j,ell j=Cycle61.Arithmetic.ell)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Ioo a b) (hWB : ∀j y,0 ≤ W j y ∧ W j y ≤ B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (sigma : ℝ) (hsigma : 0 < sigma)
    (hgeometric : sigma+8*e+nu≤1/20) (hprincipal : sigma+nu≤1/4000)
    (hwindow : sigma+e ≤ Cycle61.Arithmetic.theta*ellMin) (hlarge : sigma+nu ≤ saving+Cycle61.Assembly.signal Cycle61.Arithmetic.theta)
    (eps R dmin dmax rmin ε κ cost mesh margin loss : ℝ)
    (heps : 0 < eps) (hR : 0 ≤ R) (hdmin : 0 < dmin) (hdmax : 0 ≤ dmax) (hdRange : dmin ≤ dmax)
    (hrmin : 0 < rmin) (hε : 0<ε) (hκ : 0<κ) (hcost : 0 ≤ cost) (hmesh : 0 < mesh) (hmargin : 0 < margin)
    (hphasebudget : 8*e*R+κ≤ε) (hphasegap : ε < rmin*mesh)
    (hheight : 2*τ < dmin*cost) (hloss : τ*(2+4*eps) < loss)
    (hcap : Cycle61.Arithmetic.h+ζ ≤ dmax-margin)
    (helllo : ∀j,dmax*rmin ≤ ell j) (hellhi : ∀j,ell j ≤ dmin*R)
    (hζcap : ζ ≤ Cycle61.Transport.rowExtension)
    (hfloorbudget : 26*e+(K+8)*eps+loss+mesh*Cycle61.Arithmetic.ell+nu+sigma≤1/100)
    (hfinite : ∀n : ℕ,0<n → ∀η : Character,
      FiniteNonfloorNumeratorBound M H hH S hS hmax ell a b ζ e τ sigma W W0 W1 n η) :
    let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∀η : Character,
      (fun Z : ℝ=>Cycle61Low.normalizedProbe M H S hmax ell a b W W0 W1 η Z-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S)
          Cycle61.Assembly.signalShift Z) =O[atTop]
        (fun Z : ℝ=>Z^(HeckeZeroSupremum.beta+Cycle61.Assembly.signalShift-sigma)) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨n,hn,ht⟩ := actual_shared_nonfloor_probe_transport M H hH K e δ a b B ζ saving τ ellMin nu
    he he' hδ hδ' hζ hζ' hτ ha hab hB hmin hnu hβlo hβ S hS hmax hfirst
    ell hell hellinj hellsum W hW hcompact hsupp hWB hne
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    sigma hsigma hgeometric hprincipal hwindow hlarge
    eps R dmin dmax rmin ε κ cost mesh margin loss
    heps hR hdmin hdmax hdRange hrmin hε hκ hcost hmesh hmargin
    hphasebudget hphasegap hheight hloss hcap helllo hellhi hζcap hfloorbudget
  dsimp only
  intro η
  obtain ⟨Ct,hCt,ht⟩ := ht η
  obtain ⟨Cf,hCf,hf⟩ := hfinite n hn η
  apply Cycle61Low.isBigO_rpow_of_eventual_norm_bound
  refine ⟨Ct+Cf,by positivity,?_⟩
  filter_upwards [ht,hf,eventually_gt_atTop (0:ℝ)] with Z ht hf hZ
  dsimp only at ht
  obtain ⟨hnorm,idx,grid,hlabels,hbins,hray,herror⟩ := ht
  have hnum := hf idx grid ⟨hlabels,hbins,hray⟩
  let N := actualNormalizer M H S ell a b W W0 W1 Z
  let F := finiteNonfloorNumerator M H S hS hmax ell a b ζ e τ W W0 W1 η Z idx grid
  let A := Cycle61Low.normalizedProbe M H S hmax ell a b W W0 W1 η Z-
    HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S)
      Cycle61.Assembly.signalShift Z
  let E := Z^(HeckeZeroSupremum.beta+Cycle61.Assembly.signalShift-sigma)
  have hN : N≠0 := hnorm
  have hexp : HeckeZeroSupremum.beta-(4+Cycle61.Transport.b)/6-sigma =
      HeckeZeroSupremum.beta+Cycle61.Assembly.signalShift-sigma := by
    rw [←Cycle61.Transport.signalShift_eq]
    ring
  rw [hexp] at herror
  have he : ‖A-F/N‖≤Ct*E := herror
  have hf' : ‖F/N‖≤Cf*E := by
    rw [norm_div]
    apply (div_le_iff₀ (norm_pos_iff.mpr hN)).mpr
    simpa only [N,F,E,mul_assoc,mul_comm,mul_left_comm] using hnum
  calc
    ‖A‖ = ‖(A-F/N)+F/N‖ := by rw [sub_add_cancel]
    _ ≤ ‖A-F/N‖+‖F/N‖ := norm_add_le _ _
    _ ≤ Ct*E+Cf*E := add_le_add he hf'
    _ = (Ct+Cf)*E := by ring

/-- The same probe bound for one character, from its own numerator bound. -/
theorem normalizedProbe_high_of_finite_nonfloor_numerator_at (K : ℕ) (e δ a b B ζ saving τ ellMin nu : ℝ)
    (he : 0 < e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (hζ' : ζ≤1/10000000000) (hτ : 0<τ)
    (ha : 0 < a) (hab : a ≤ b) (hB : 0 ≤ B) (hmin : 0 < ellMin) (hnu : 0 < nu)
    (hβlo : Cycle61.Arithmetic.theta ≤ HeckeZeroSupremum.beta)
    (hβ : HeckeZeroSupremum.beta ≤ (7/8:ℝ))
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (ell : Fin K→ℝ) (hell : ∀j,ellMin ≤ ell j) (hellinj : Function.Injective ell) (hellsum : ∑j,ell j=Cycle61.Arithmetic.ell)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Ioo a b) (hWB : ∀j y,0 ≤ W j y ∧ W j y ≤ B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (sigma : ℝ) (hsigma : 0 < sigma)
    (hgeometric : sigma+8*e+nu≤1/20) (hprincipal : sigma+nu≤1/4000)
    (hwindow : sigma+e ≤ Cycle61.Arithmetic.theta*ellMin) (hlarge : sigma+nu ≤ saving+Cycle61.Assembly.signal Cycle61.Arithmetic.theta)
    (eps R dmin dmax rmin ε κ cost mesh margin loss : ℝ)
    (heps : 0 < eps) (hR : 0 ≤ R) (hdmin : 0 < dmin) (hdmax : 0 ≤ dmax) (hdRange : dmin ≤ dmax)
    (hrmin : 0 < rmin) (hε : 0<ε) (hκ : 0<κ) (hcost : 0 ≤ cost) (hmesh : 0 < mesh) (hmargin : 0 < margin)
    (hphasebudget : 8*e*R+κ≤ε) (hphasegap : ε < rmin*mesh)
    (hheight : 2*τ < dmin*cost) (hloss : τ*(2+4*eps) < loss)
    (hcap : Cycle61.Arithmetic.h+ζ ≤ dmax-margin)
    (helllo : ∀j,dmax*rmin ≤ ell j) (hellhi : ∀j,ell j ≤ dmin*R)
    (hζcap : ζ ≤ Cycle61.Transport.rowExtension)
    (hfloorbudget : 26*e+(K+8)*eps+loss+mesh*Cycle61.Arithmetic.ell+nu+sigma≤1/100)
    (η : Character)
    (hfinite : ∀n : ℕ,0<n →
      FiniteNonfloorNumeratorBound M H hH S hS hmax ell a b ζ e τ sigma W W0 W1 n η) :
    let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩;
      (fun Z : ℝ=>Cycle61Low.normalizedProbe M H S hmax ell a b W W0 W1 η Z-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S)
          Cycle61.Assembly.signalShift Z) =O[atTop]
        (fun Z : ℝ=>Z^(HeckeZeroSupremum.beta+Cycle61.Assembly.signalShift-sigma)) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨n,hn,ht⟩ := actual_shared_nonfloor_probe_transport M H hH K e δ a b B ζ saving τ ellMin nu
    he he' hδ hδ' hζ hζ' hτ ha hab hB hmin hnu hβlo hβ S hS hmax hfirst
    ell hell hellinj hellsum W hW hcompact hsupp hWB hne
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    sigma hsigma hgeometric hprincipal hwindow hlarge
    eps R dmin dmax rmin ε κ cost mesh margin loss
    heps hR hdmin hdmax hdRange hrmin hε hκ hcost hmesh hmargin
    hphasebudget hphasegap hheight hloss hcap helllo hellhi hζcap hfloorbudget
  dsimp only
  obtain ⟨Ct,hCt,ht⟩ := ht η
  obtain ⟨Cf,hCf,hf⟩ := hfinite n hn
  apply Cycle61Low.isBigO_rpow_of_eventual_norm_bound
  refine ⟨Ct+Cf,by positivity,?_⟩
  filter_upwards [ht,hf,eventually_gt_atTop (0:ℝ)] with Z ht hf hZ
  dsimp only at ht
  obtain ⟨hnorm,idx,grid,hlabels,hbins,hray,herror⟩ := ht
  have hnum := hf idx grid ⟨hlabels,hbins,hray⟩
  let N := actualNormalizer M H S ell a b W W0 W1 Z
  let F := finiteNonfloorNumerator M H S hS hmax ell a b ζ e τ W W0 W1 η Z idx grid
  let A := Cycle61Low.normalizedProbe M H S hmax ell a b W W0 W1 η Z-
    HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S)
      Cycle61.Assembly.signalShift Z
  let E := Z^(HeckeZeroSupremum.beta+Cycle61.Assembly.signalShift-sigma)
  have hN : N≠0 := hnorm
  have hexp : HeckeZeroSupremum.beta-(4+Cycle61.Transport.b)/6-sigma =
      HeckeZeroSupremum.beta+Cycle61.Assembly.signalShift-sigma := by
    rw [←Cycle61.Transport.signalShift_eq]
    ring
  rw [hexp] at herror
  have he : ‖A-F/N‖≤Ct*E := herror
  have hf' : ‖F/N‖≤Cf*E := by
    rw [norm_div]
    apply (div_le_iff₀ (norm_pos_iff.mpr hN)).mpr
    simpa only [N,F,E,mul_assoc,mul_comm,mul_left_comm] using hnum
  calc
    ‖A‖ = ‖(A-F/N)+F/N‖ := by rw [sub_add_cancel]
    _ ≤ ‖A-F/N‖+‖F/N‖ := norm_add_le _ _
    _ ≤ Ct*E+Cf*E := add_le_add he hf'
    _ = (Ct+Cf)*E := by ring

#print axioms normalizedProbe_high_of_finite_nonfloor_numerator
end SevenEighths.Cycle61HighTransport
end
end OAI

end
/- END ORIGINAL Cycle61.Assembly.Transport.HighApproximation -/

/- BEGIN ORIGINAL Cycle61.Assembly.Final.FixedHigh; sha256 a50d47ee44043379c2eabf0cd8bb20a0b4ff0341925c798b8b31a7648a745e4d -/
section
                                         
                                    
                                      
                                                   

set_option autoImplicit false
namespace Cycle61.FinalAssembly
noncomputable section
open scoped Classical BigOperators
open Filter Asymptotics OAI.SevenEighths
open HeckeFamily ProbePhysical Cycle61DetectorCount PrincipalSignalComparison Cycle61HighTransport

/-- The finite numerator remains the honest analytic integration prerequisite. -/
def FixedFiniteNumeratorInput (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (τ : ℝ) : Prop :=
  ∀n : ℕ,0<n → ∀η : Character,
    FiniteNonfloorNumeratorBound F.modulus ⊤ le_top F.S F.exclusions F.maximal
      D.length 1 2 rowPadding D.e τ P.sigma (fun _=>F.w) F.W F.W n η

/-- The finite numerator bound for one character. -/
def FixedFiniteNumeratorInputAt (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (τ : ℝ) (η : Character) : Prop :=
  ∀n : ℕ,0<n →
    FiniteNonfloorNumeratorBound F.modulus ⊤ le_top F.S F.exclusions F.maximal
      D.length 1 2 rowPadding D.e τ P.sigma (fun _=>F.w) F.W F.W n η

theorem sourceProbe_high_of_finite_numerator (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (J τ : ℝ) (hheight : HeightAdmissible D P J τ)
    (hβ : Arithmetic.theta≤HeckeZeroSupremum.beta)
    (hfinite : FixedFiniteNumeratorInput D F P τ) :
    ∀η : Character,
      (fun Z=>sourceProbe D F η Z-HeckeSignal.signal
        (η.excludePrimes F.S F.exclusions.prime) (sourceCorrection η F.S) Assembly.signalShift Z)
        =O[atTop](fun Z : ℝ=>Z^(HeckeZeroSupremum.beta+Assembly.signalShift-P.sigma)) := by
  rcases hheight with ⟨hτ,hτd,hτcost,hτt,hτeps,hτJ⟩
  have hlarge : P.sigma+P.nu≤1+Assembly.signal Arithmetic.theta := by
    have hn:=P.nu_eq
    have hs:=P.sigma_small
    have ht:=D.t_small
    have hsig : (1/10:ℝ)<Assembly.signal Arithmetic.theta := by
      norm_num [Assembly.signal,Assembly.signalShift,Arithmetic.theta,Arithmetic.x,Arithmetic.ell]
    linarith
  have hcap : Arithmetic.h+rowPadding≤(7/8:ℝ)-1/100 := by
    norm_num [Arithmetic.h,rowPadding]
  have hh := normalizedProbe_high_of_finite_nonfloor_numerator F.modulus ⊤ le_top
    D.N D.e (1/100) 1 2 1 rowPadding 1 τ P.ellMin P.nu
    D.e_pos D.e_small (by norm_num) (by norm_num)
    (by norm_num [rowPadding]) (by norm_num [rowPadding])
    hτ (by norm_num) (by norm_num) (by norm_num) P.ellMin_pos P.nu_pos
    hβ baseline_beta F.S F.exclusions F.maximal F.first
    D.length P.slots_min D.slots_injective D.slots_sum
    (fun _=>F.w) (fun _=>F.smooth) (fun _=>F.compact) (fun _=>F.support)
    (fun _=>F.bounded) (fun _=>F.nonzero)
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num)
    F.complex_support F.complex_support F.real F.real F.nonnegative F.nonnegative
    F.complex_nonzero F.complex_nonzero P.sigma P.sigma_pos
    P.geometric_budget P.principal_budget P.window_budget hlarge
    P.eps D.t (1/200) (7/8) P.rmin P.phaseEpsilon P.phaseKappa
    D.cost P.mesh (1/100) D.t
    P.eps_pos D.t_pos.le (by norm_num) (by norm_num) (by norm_num)
    P.rmin_pos P.phaseEpsilon_pos P.phaseKappa_pos D.cost_pos.le P.mesh_pos (by norm_num)
    P.phase_budget P.phase_gap (by linarith) hτeps hcap
    P.slots_lower D.slots_small (by norm_num [rowPadding,Transport.rowExtension]) P.floor_budget hfinite
  simpa only [sourceProbe] using hh
theorem sourceProbe_high_of_finite_numerator_at (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (J τ : ℝ) (hheight : HeightAdmissible D P J τ)
    (hβ : Arithmetic.theta≤HeckeZeroSupremum.beta)
    (η : Character) (hfinite : FixedFiniteNumeratorInputAt D F P τ η) :
      (fun Z=>sourceProbe D F η Z-HeckeSignal.signal
        (η.excludePrimes F.S F.exclusions.prime) (sourceCorrection η F.S) Assembly.signalShift Z)
        =O[atTop](fun Z : ℝ=>Z^(HeckeZeroSupremum.beta+Assembly.signalShift-P.sigma)) := by
  rcases hheight with ⟨hτ,hτd,hτcost,hτt,hτeps,hτJ⟩
  have hlarge : P.sigma+P.nu≤1+Assembly.signal Arithmetic.theta := by
    have hn:=P.nu_eq
    have hs:=P.sigma_small
    have ht:=D.t_small
    have hsig : (1/10:ℝ)<Assembly.signal Arithmetic.theta := by
      norm_num [Assembly.signal,Assembly.signalShift,Arithmetic.theta,Arithmetic.x,Arithmetic.ell]
    linarith
  have hcap : Arithmetic.h+rowPadding≤(7/8:ℝ)-1/100 := by
    norm_num [Arithmetic.h,rowPadding]
  have hh := normalizedProbe_high_of_finite_nonfloor_numerator_at F.modulus ⊤ le_top
    D.N D.e (1/100) 1 2 1 rowPadding 1 τ P.ellMin P.nu
    D.e_pos D.e_small (by norm_num) (by norm_num)
    (by norm_num [rowPadding]) (by norm_num [rowPadding])
    hτ (by norm_num) (by norm_num) (by norm_num) P.ellMin_pos P.nu_pos
    hβ baseline_beta F.S F.exclusions F.maximal F.first
    D.length P.slots_min D.slots_injective D.slots_sum
    (fun _=>F.w) (fun _=>F.smooth) (fun _=>F.compact) (fun _=>F.support)
    (fun _=>F.bounded) (fun _=>F.nonzero)
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num)
    F.complex_support F.complex_support F.real F.real F.nonnegative F.nonnegative
    F.complex_nonzero F.complex_nonzero P.sigma P.sigma_pos
    P.geometric_budget P.principal_budget P.window_budget hlarge
    P.eps D.t (1/200) (7/8) P.rmin P.phaseEpsilon P.phaseKappa
    D.cost P.mesh (1/100) D.t
    P.eps_pos D.t_pos.le (by norm_num) (by norm_num) (by norm_num)
    P.rmin_pos P.phaseEpsilon_pos P.phaseKappa_pos D.cost_pos.le P.mesh_pos (by norm_num)
    P.phase_budget P.phase_gap (by linarith) hτeps hcap
    P.slots_lower D.slots_small (by norm_num [rowPadding,Transport.rowExtension]) P.floor_budget η hfinite
  simpa only [sourceProbe] using hh
end
end Cycle61.FinalAssembly

end
/- END ORIGINAL Cycle61.Assembly.Final.FixedHigh -/

/- BEGIN ORIGINAL Cycle61.Assembly.Final.CommonProbe; sha256 a4185121dc6dd2f047391e46e4999448ab106c8a9a1d3f85e2268c41981ac292 -/
section
                                       

set_option autoImplicit false
namespace Cycle61.FinalAssembly
noncomputable section
open scoped Classical
open Filter Asymptotics OAI.SevenEighths
open HeckeFamily Cycle61DetectorCount

structure ChosenData where
  D : BaselineData
  kappa_exact : D.momentKappa=2*HeckeZeroSupremum.beta-1
  count_budget : 159*D.ε+609*D.t≤(HeckeZeroSupremum.beta-Arithmetic.theta)/10000
  fine : ∀j,D.length j≤Cycle25.sourceMesh D.t/200
  detector_fine : ∀j,D.length j≤DetectorAffine.detectorMesh D.t/200
  P : TransportParameters D
  F : BaselineSourceData D
  counts : Cycle25ProbeHighRowFamily.CountParameters (baselineSource D F).modulus ⊤ D.t

theorem exists_chosen_data (hβ : Arithmetic.theta<HeckeZeroSupremum.beta) : Nonempty ChosenData := by
  obtain ⟨hk,hk1,hbeta⟩ := moment_parameter_gates hβ
  obtain ⟨D,hκ,hbudget,hfine,hcommon,⟨P⟩⟩ := exists_compatible_data hk hk1
    (show 0<(HeckeZeroSupremum.beta-Arithmetic.theta)/10000 by positivity)
  obtain ⟨F⟩ := exists_baseline_source D
  obtain ⟨counts⟩ := fresh_count_parameters D.toData (baselineSource D F)
  have hdet : ∀j,D.length j≤DetectorAffine.detectorMesh D.t/200 := fun j=>
    (hcommon j).trans (div_le_div_of_nonneg_right commonMesh_le_detector (by norm_num))
  exact ⟨⟨D,hκ,hbudget,hfine,hdet,P,F,counts⟩⟩

/-- Honest intermediate source obligation. Fixed data and polynomial degree precede
height; actual baseline source moments at that height are supplied by the assembly. -/
def FiniteNumeratorAssemblyInput : Prop :=
  Arithmetic.theta<HeckeZeroSupremum.beta →
  ∀A : ChosenData,∃J : ℝ,0≤J ∧ ∀τ : ℝ,HeightAdmissible A.D A.P J τ →
    ∀η : Character,(∃C : ℝ,1≤C ∧ ∀ᶠZ : ℝ in atTop,
      SourceMomentBound A.D.toData (baselineSource A.D A.F) A.counts η Z τ
        (C*Z^A.D.t) (Z^(2*τ))) →
    FixedFiniteNumeratorInputAt A.D A.F A.P τ η

theorem common_probe_of_finite_numerator
    (hdet : Cycle25ProbeFinalAssemblyCertifiedBands.DetectorAffineInput)
    (hinput : FiniteNumeratorAssemblyInput) :
    Cycle25.UniformCommonProbe Arithmetic.theta Assembly.signalShift := by
  intro hβ
  obtain ⟨A⟩ := exists_chosen_data hβ
  obtain ⟨J,hJ,hfinite⟩ := hinput hβ A
  have hβ51 := (moment_parameter_gates hβ).2.2
  have hβhi : HeckeZeroSupremum.beta≤7/8 := by linarith [(moment_parameter_gates hβ).2.1]
  have hkβ : 2*HeckeZeroSupremum.beta-1≤A.D.momentKappa := A.kappa_exact.ge
  have hjoint := actual_joint_height A.D A.F A.P A.counts hβ51 hkβ A.fine
    hdet hβhi A.detector_fine J hJ

  let loss := (HeckeZeroSupremum.beta-Arithmetic.theta)/2
  have hloss : 0<loss := by dsimp [loss];linarith
  have hgap : loss<HeckeZeroSupremum.beta-Arithmetic.theta := by dsimp [loss];linarith
  exact ⟨loss,A.P.sigma,hloss,hgap,A.P.sigma_pos,
    fixed_source_contract A.D A.F loss A.P.sigma hloss (fun η=>by
      obtain ⟨τ,hheight,hcount⟩ := hjoint η
      exact sourceProbe_high_of_finite_numerator_at A.D A.F A.P J τ hheight hβ.le η
        (hfinite τ hheight η hcount))⟩
end
end Cycle61.FinalAssembly

end
/- END ORIGINAL Cycle61.Assembly.Final.CommonProbe -/

/- BEGIN ORIGINAL Cycle61.Assembly.MeshChoice; sha256 fdf43808b0a2a363d4cf4a6564c2723da9720bcfe3476e214084810db8da2e6e -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                         

set_option autoImplicit false
namespace Cycle61.FinalAssembly
noncomputable section
open scoped Classical
open Filter OAI.SevenEighths HeckeFamily Cycle61DetectorCount

/-- Choose the slot data after a positive analytic mesh cap has been fixed.
The cap precedes the slot count, source profiles, exclusions and ray modulus. -/
theorem exists_chosen_data_with_mesh
    (hβ : Arithmetic.theta<HeckeZeroSupremum.beta)
    {meshCap : ℝ} (hmesh : 0<meshCap) :
    ∃ A : ChosenData, A.P.mesh≤meshCap := by
  obtain ⟨hk,hk1,hbeta⟩ := moment_parameter_gates hβ
  have hbudget : 0<min ((HeckeZeroSupremum.beta-Arithmetic.theta)/10000) meshCap :=
    lt_min (by positivity) hmesh
  obtain ⟨D,hκ,hbound,hfine,hcommon,⟨P⟩⟩ := exists_compatible_data hk hk1 hbudget
  obtain ⟨F⟩ := exists_baseline_source D
  obtain ⟨counts⟩ := fresh_count_parameters D.toData (baselineSource D F)
  have hdet : ∀j,D.length j≤DetectorAffine.detectorMesh D.t/200 := fun j=>
    (hcommon j).trans (div_le_div_of_nonneg_right commonMesh_le_detector (by norm_num))
  have hcount := hbound.trans (min_le_left _ _)
  have ht : D.t≤meshCap := by
    have hsmall := hbound.trans (min_le_right _ _)
    have he := D.epsilon_pos
    have ht := D.t_pos
    linarith
  exact ⟨⟨D,hκ,hcount,hfine,hdet,P,F,counts⟩,P.mesh_small.trans ht⟩

/-- The actual numerator is needed for one suitably chosen set of data.
This avoids requiring a moment theorem for every otherwise admissible mesh. -/
def ChosenFiniteNumeratorInput : Prop :=
  Arithmetic.theta<HeckeZeroSupremum.beta →
  ∃ A : ChosenData, ∃ J : ℝ, 0≤J ∧
    ∀ τ : ℝ, HeightAdmissible A.D A.P J τ →
    ∀η : Character,(∃C : ℝ,1≤C ∧ ∀ᶠZ : ℝ in atTop,
      SourceMomentBound A.D.toData (baselineSource A.D A.F) A.counts η Z τ
        (C*Z^A.D.t) (Z^(2*τ))) →
    FixedFiniteNumeratorInputAt A.D A.F A.P τ η

theorem common_probe_of_chosen_finite_numerator
    (hdet : Cycle25ProbeFinalAssemblyCertifiedBands.DetectorAffineInput)
    (hinput : ChosenFiniteNumeratorInput) :
    Cycle25.UniformCommonProbe Arithmetic.theta Assembly.signalShift := by
  intro hβ
  obtain ⟨A,J,hJ,hfinite⟩ := hinput hβ
  have hβ51 := (moment_parameter_gates hβ).2.2
  have hβhi : HeckeZeroSupremum.beta≤7/8 := by linarith [(moment_parameter_gates hβ).2.1]
  have hkβ : 2*HeckeZeroSupremum.beta-1≤A.D.momentKappa := A.kappa_exact.ge
  have hjoint := actual_joint_height A.D A.F A.P A.counts hβ51 hkβ A.fine
    hdet hβhi A.detector_fine J hJ

  let loss := (HeckeZeroSupremum.beta-Arithmetic.theta)/2
  have hloss : 0<loss := by dsimp [loss];linarith
  have hgap : loss<HeckeZeroSupremum.beta-Arithmetic.theta := by dsimp [loss];linarith
  exact ⟨loss,A.P.sigma,hloss,hgap,A.P.sigma_pos,
    fixed_source_contract A.D A.F loss A.P.sigma hloss (fun η=>by
      obtain ⟨τ,hheight,hcount⟩ := hjoint η
      exact sourceProbe_high_of_finite_numerator_at A.D A.F A.P J τ hheight hβ.le η
        (hfinite τ hheight η hcount))⟩
end
end Cycle61.FinalAssembly

#print axioms Cycle61.FinalAssembly.exists_chosen_data_with_mesh
#print axioms Cycle61.FinalAssembly.common_probe_of_chosen_finite_numerator

end
/- END ORIGINAL Cycle61.Assembly.MeshChoice -/
