import Candidate.Target830.Physical.Transport.ProbeDefinition
import Candidate.Target830.Physical.Transport.PrincipalRemainderNormalized
import Candidate.Target830.Physical.Transport.TailScales
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CanonicalReduction
import Candidate.Target830.Physical.Transport.NonfloorTransport
import Candidate.Target830.Physical.Normalizer

/- Original module: Candidate.Target830.Physical.Transport.CommonProbe. -/
section

set_option autoImplicit false

namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Target830PhysicalHighTransport
open HeckeFamily ProbePhysical ProbeHighRowFamily ProbeRaySlots CompletedGauss CanonicalQuadraticSieve
open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O

theorem principal_shift_is_common :
    Target830Physical.Transport.PrincipalSignal.signalShift = Target830Physical.Assembly.signalShift :=
  Target830Physical.Transport.signalShift_eq

/-- The exact principal, finite central, and tail partition of the shared
normalized probe at the new physical lengths. -/
theorem normalizedProbe_partition {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    [NeZero (∏P∈S,P)] (slotEll : Fin K→ℝ) (a b ζ Z : ℝ)
    (hζ : 0 ≤ ζ) (hZ : 1 ≤ Z) (W : Fin K→ℝ→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (η : Character) :
    let Yp := fun j=> Z^(slotEll j)
    let T := fun j=> pool (RayQuotient.identityClass M H) S a b (Yp j)
    let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
    let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
      (Probe.principalScalar Finset.univ Z Target830Physical.Arithmetic.ell
        (slotMass T (residueWeights W Yp)) : ℂ)
    Target830PhysicalLow.normalizedProbe M H S hmax slotEll a b W W0 W1 η Z =
      principalPhysicalPool η S T WC Yp W0 W1
        (Z^Target830Physical.Arithmetic.x) (Z^Target830Physical.Arithmetic.y) Z/normer +
      ((∑n∈smallDyadicIndices (Z^(1/100:ℝ)),
          finitePhysicalRows S hmax η (smallDyadicRows (Z^(1/100:ℝ)) n) T WC Yp W0 W1
            (Z^Target830Physical.Arithmetic.x) (Z^Target830Physical.Arithmetic.y) Z)+
        finitePhysicalRows S hmax η (rowBand (Z^(1/100:ℝ)) (Z^(Target830Physical.Arithmetic.h+ζ)))
          T WC Yp W0 W1 (Z^Target830Physical.Arithmetic.x) (Z^Target830Physical.Arithmetic.y) Z+
        (∑'n : ℕ, finitePhysicalRows S hmax η (dyadicRows (Z^(Target830Physical.Arithmetic.h+ζ)) n)
          T WC Yp W0 W1 (Z^Target830Physical.Arithmetic.x) (Z^Target830Physical.Arithmetic.y) Z))/normer := by
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  let Yp := fun j=> Z^(slotEll j)
  let T := fun j=> pool (RayQuotient.identityClass M H) S a b (Yp j)
  let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
  have hT : ∀i P,P∈T i → Supported P.val := by
    intro i P hP
    exact outside_prime_supported S hS.bad P ((mem_pool _ S a b (Yp i) P).mp hP).2.2.2
  have hp := canonical_physical_probe_partition S hS hmax η T hT WC Yp
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (Z^Target830Physical.Arithmetic.x) (Z^Target830Physical.Arithmetic.y) Z
    (Z^(1/100:ℝ)) (Z^(Target830Physical.Arithmetic.h+ζ))
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0
    (Real.one_le_rpow hZ (by norm_num))
    (Real.rpow_le_rpow_of_exponent_le hZ (by linarith [Target830Physical.Transport.h_interval.1]))
  dsimp only
  change _ = principalPhysicalPool η S T WC Yp W0 W1 _ _ _ / _ + _
  unfold Target830PhysicalLow.normalizedProbe
  dsimp only
  rw [hp]
  exact add_div _ _ _

#print axioms normalizedProbe_partition
end SevenEighths.Target830PhysicalHighTransport
end
end OAI

#print axioms OAI.SevenEighths.Target830PhysicalHighTransport.principal_shift_is_common
#print axioms OAI.SevenEighths.Target830PhysicalHighTransport.normalizedProbe_partition
end

/- Original module: Candidate.Target830.Physical.Transport.SharedNonfloor. -/
section

namespace OAI
noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.Target830PhysicalHighTransport
open ProbeHighRowFamily HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
open ProbeRaySlots PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

omit [NeZero M] in
private theorem sharedNonfloorPoolOutside (S : Finset (Ideal O)) (K : ℕ) (a b : ℝ) (Y : Fin K→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S a b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S a b (Y j) P).mp hP |>.2.2.2

theorem actual_shared_nonfloor_probe_transport (K : ℕ) (e δ a b B ζ saving τ ellMin nu : ℝ)
    (he : 0 < e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (hζ' : ζ≤1/10000000000) (hτ : 0<τ)
    (ha : 0 < a) (hab : a ≤ b) (hB : 0 ≤ B) (hmin : 0 < ellMin) (hnu : 0 < nu)
    (hβlo : Target830Physical.Arithmetic.theta ≤ HeckeZeroSupremum.beta)
    (hβ : HeckeZeroSupremum.beta ≤ (7/8:ℝ))
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (ell : Fin K→ℝ) (hell : ∀j,ellMin ≤ ell j) (hellinj : Function.Injective ell) (hellsum : ∑j,ell j=Target830Physical.Arithmetic.ell)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Ioo a b) (hWB : ∀j y,0 ≤ W j y ∧ W j y ≤ B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (sigma : ℝ) (hsigma : 0 < sigma)
    (hgeometric : sigma+8*e+nu≤1/20) (hprincipal : sigma+nu≤1/4000)
    (hwindow : sigma+e ≤ Target830Physical.Arithmetic.theta*ellMin) (hlarge : sigma+nu ≤ saving+Target830Physical.Assembly.signal Target830Physical.Arithmetic.theta)
    (eps R dmin dmax rmin ε κ cost mesh margin loss : ℝ)
    (heps : 0 < eps) (hR : 0 ≤ R) (hdmin : 0 < dmin) (hdmax : 0 ≤ dmax) (hdRange : dmin ≤ dmax)
    (hrmin : 0 < rmin) (hε : 0<ε) (hκ : 0<κ) (hcost : 0 ≤ cost) (hmesh : 0 < mesh) (hmargin : 0 < margin)
    (hphasebudget : 8*e*R+κ≤ε) (hphasegap : ε < rmin*mesh)
    (hheight : 2*τ < dmin*cost) (hloss : τ*(2+4*eps) < loss)
    (hcap : Target830Physical.Arithmetic.h+ζ ≤ dmax-margin)
    (helllo : ∀j,dmax*rmin ≤ ell j) (hellhi : ∀j,ell j ≤ dmin*R)
    (hζcap : ζ ≤ Target830Physical.Transport.rowExtension)
    (hfloorbudget : 26*e+(K+8)*eps+loss+mesh*Target830Physical.Arithmetic.ell+nu+sigma≤1/100) :
    let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃n : ℕ,0 < n ∧ ∀η : Character,∃C : ℝ,0 < C ∧ ∀ᶠ Z : ℝ in atTop,
      let Yp := fun j=> Z^(ell j)
      let T := fun j=> pool (RayQuotient.identityClass M H) S a b (Yp j)
      let hT := sharedNonfloorPoolOutside M H S K a b Yp
      let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (Target830Physical.Arithmetic.ell) (slotMass T (residueWeights W Yp)) : ℂ)
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
      (∀u∈rowBand (Z^(1/100:ℝ)) (Z^((Target830Physical.Arithmetic.h:ℝ)+ζ)),
        (calibrationForSet S hmax).residueMonoid u.val≠0 →
        (∀θ,(rayCubeFamily M H hH u θ).residue≠1) ∧
        (∀θ,(rayCubeFamily M H hH u θ).modulus.absNorm≤
          conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm) ∧
        ∀hnp : ∀θ,(rayCubeFamily M H hH u θ).residue≠1,
        HeckeDetectorZeros.zeroMaximum (rayCubeFamily M H hH u) hnp
          (3*(idx u+1:ℕ)*Z^τ)<(51/100:ℝ)+e*grid u+2*e) ∧
      let alpha : FreeRow→ℝ := fun u=>51/100+e*grid u
      let height : FreeRow→ℝ := fun u=>(3*idx u+1:ℕ)*Z^τ
      ‖Target830PhysicalLow.normalizedProbe M H S hmax ell a b W W0 W1 η Z-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) Target830Physical.Assembly.signalShift Z-
        finiteCentralCubeRows S hS hmax η
          (supportedNonfloorRows S hmax (rowBand (Z^(1/100:ℝ)) (Z^((Target830Physical.Arithmetic.h:ℝ)+ζ))) grid) T hT WC Yp
          W0 W1 (Z^(Target830Physical.Arithmetic.x:ℝ)) (Z^(Target830Physical.Arithmetic.y:ℝ)) Z e alpha height/normer‖≤
        C*Z^(HeckeZeroSupremum.beta-(4+Target830Physical.Transport.b)/6-sigma) := by
  simpa only [Target830PhysicalLow.normalizedProbe, Target830Physical.Transport.signalShift_eq] using
    Target830PhysicalHighRowFamily.actual_nonfloor_probe_transport M H hH K e δ a b B ζ saving τ ellMin nu
      he he' hδ hδ' hζ hζ' hτ ha hab hB hmin hnu hβlo hβ S hS hmax hfirst
      ell hell hellinj hellsum W hW hcompact hsupp hWB hne
      W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
      sigma hsigma hgeometric hprincipal hwindow hlarge
      eps R dmin dmax rmin ε κ cost mesh margin loss
      heps hR hdmin hdmax hdRange hrmin hε hκ hcost hmesh hmargin
      hphasebudget hphasegap hheight hloss hcap helllo hellhi hζcap hfloorbudget

#print axioms actual_shared_nonfloor_probe_transport
end SevenEighths.Target830PhysicalHighTransport
end
end OAI

#print axioms OAI.SevenEighths.Target830PhysicalHighTransport.actual_shared_nonfloor_probe_transport
end

/- Original module: Candidate.Target830.Physical.Transport.HighApproximation. -/
section
/- Source integration: PR50 8cb265dc base; PR56 67edfb7a detector affine interfaces.
   Original Hailey Collet, OpenAI and predecessor notices are retained.
   Detector affine contribution: DaysSky, with Claude assistance; Apache-2.0. -/

                                                

set_option autoImplicit false

namespace OAI
noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set Asymptotics
namespace SevenEighths.Target830PhysicalHighTransport
open ProbeHighRowFamily HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
open ProbeRaySlots PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O

private theorem numeratorPoolOutside {K : ℕ} (M : Ideal O) (H : Subgroup (O ⧸ M)ˣ)
    (S : Finset (Ideal O)) (a b : ℝ) (Y : Fin K→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S a b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S a b (Y j) P).mp hP |>.2.2.2

theorem selected_row_within_density_cutoff {Z ζ : ℝ} {u : FreeRow}
    (hZ : 1≤ Z) (hζ : ζ≤1/10000000000)
    (hu : u∈rowBand (Z^(1/100:ℝ)) (Z^(Target830Physical.Arithmetic.h+ζ))) :
    rowNorm u ≤ Z^Target830Physical.Arithmetic.dPlus := by
  exact (mem_rowBand.mp hu).2.2.le.trans
    (Real.rpow_le_rpow_of_exponent_le hZ (Target830Physical.Transport.extended_row_cutoff hζ))

/-- The literal finite numerator left after the proved floor and tail transport. -/
def finiteNonfloorNumerator {K : ℕ} (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (slotEll : Fin K→ℝ) (a b ζ e τ : ℝ)
    (W : Fin K→ℝ→ℝ) (W0 W1 : SchwartzMap ℝ ℂ) (η : Character) (Z : ℝ)
    (idx grid : FreeRow→ℕ) : ℂ :=
  let Yp := fun j=> Z^(slotEll j)
  let T := fun j=> pool (RayQuotient.identityClass M H) S a b (Yp j)
  let hT := numeratorPoolOutside M H S a b Yp
  let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
  finiteCentralCubeRows S hS hmax η
    (supportedNonfloorRows S hmax (rowBand (Z^(1/100:ℝ)) (Z^(Target830Physical.Arithmetic.h+ζ))) grid)
    T hT WC Yp W0 W1 (Z^Target830Physical.Arithmetic.x) (Z^Target830Physical.Arithmetic.y) Z e
    (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)

/-- Selection and zero facts are conclusions of actual transport, not analytic inputs. -/
def ActualBufferedSelection (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
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
      (∀u∈rowBand (Z^(1/100:ℝ)) (Z^((Target830Physical.Arithmetic.h:ℝ)+ζ)),
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
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (slotEll : Fin K→ℝ) (a b ζ e τ sigma : ℝ) (W : Fin K→ℝ→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (n : ℕ) (η : Character) : Prop :=
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in atTop,∀idx grid : FreeRow→ℕ,
    ActualBufferedSelection M H hH S hS hmax η ζ e τ n Z idx grid →
    ‖finiteNonfloorNumerator M H S hS hmax slotEll a b ζ e τ W W0 W1 η Z idx grid‖ ≤
      C*‖actualNormalizer M H S slotEll a b W W0 W1 Z‖*
        Z^(HeckeZeroSupremum.beta+Target830Physical.Assembly.signalShift-sigma)

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

theorem normalizedProbe_high_of_finite_nonfloor_numerator (K : ℕ) (e δ a b B ζ saving τ ellMin nu : ℝ)
    (he : 0 < e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (hζ' : ζ≤1/10000000000) (hτ : 0<τ)
    (ha : 0 < a) (hab : a ≤ b) (hB : 0 ≤ B) (hmin : 0 < ellMin) (hnu : 0 < nu)
    (hβlo : Target830Physical.Arithmetic.theta ≤ HeckeZeroSupremum.beta)
    (hβ : HeckeZeroSupremum.beta ≤ (7/8:ℝ))
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (ell : Fin K→ℝ) (hell : ∀j,ellMin ≤ ell j) (hellinj : Function.Injective ell) (hellsum : ∑j,ell j=Target830Physical.Arithmetic.ell)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Ioo a b) (hWB : ∀j y,0 ≤ W j y ∧ W j y ≤ B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (sigma : ℝ) (hsigma : 0 < sigma)
    (hgeometric : sigma+8*e+nu≤1/20) (hprincipal : sigma+nu≤1/4000)
    (hwindow : sigma+e ≤ Target830Physical.Arithmetic.theta*ellMin) (hlarge : sigma+nu ≤ saving+Target830Physical.Assembly.signal Target830Physical.Arithmetic.theta)
    (eps R dmin dmax rmin ε κ cost mesh margin loss : ℝ)
    (heps : 0 < eps) (hR : 0 ≤ R) (hdmin : 0 < dmin) (hdmax : 0 ≤ dmax) (hdRange : dmin ≤ dmax)
    (hrmin : 0 < rmin) (hε : 0<ε) (hκ : 0<κ) (hcost : 0 ≤ cost) (hmesh : 0 < mesh) (hmargin : 0 < margin)
    (hphasebudget : 8*e*R+κ≤ε) (hphasegap : ε < rmin*mesh)
    (hheight : 2*τ < dmin*cost) (hloss : τ*(2+4*eps) < loss)
    (hcap : Target830Physical.Arithmetic.h+ζ ≤ dmax-margin)
    (helllo : ∀j,dmax*rmin ≤ ell j) (hellhi : ∀j,ell j ≤ dmin*R)
    (hζcap : ζ ≤ Target830Physical.Transport.rowExtension)
    (hfloorbudget : 26*e+(K+8)*eps+loss+mesh*Target830Physical.Arithmetic.ell+nu+sigma≤1/100)
    (hfinite : ∀n : ℕ,0< n → ∀η : Character,
      FiniteNonfloorNumeratorBound M H hH S hS hmax ell a b ζ e τ sigma W W0 W1 n η) :
    let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∀η : Character,
      (fun Z : ℝ=> Target830PhysicalLow.normalizedProbe M H S hmax ell a b W W0 W1 η Z-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S)
          Target830Physical.Assembly.signalShift Z) =O[atTop]
        (fun Z : ℝ=> Z^(HeckeZeroSupremum.beta+Target830Physical.Assembly.signalShift-sigma)) := by
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
  apply Target830PhysicalLow.isBigO_rpow_of_eventual_norm_bound
  refine ⟨Ct+Cf,by positivity,?_⟩
  filter_upwards [ht,hf,eventually_gt_atTop (0:ℝ)] with Z ht hf hZ
  dsimp only at ht
  obtain ⟨hnorm,idx,grid,hlabels,hbins,hray,herror⟩ := ht
  have hnum := hf idx grid ⟨hlabels,hbins,hray⟩
  let N := actualNormalizer M H S ell a b W W0 W1 Z
  let F := finiteNonfloorNumerator M H S hS hmax ell a b ζ e τ W W0 W1 η Z idx grid
  let A := Target830PhysicalLow.normalizedProbe M H S hmax ell a b W W0 W1 η Z-
    HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S)
      Target830Physical.Assembly.signalShift Z
  let E := Z^(HeckeZeroSupremum.beta+Target830Physical.Assembly.signalShift-sigma)
  have hN : N≠0 := hnorm
  have hexp : HeckeZeroSupremum.beta-(4+Target830Physical.Transport.b)/6-sigma =
      HeckeZeroSupremum.beta+Target830Physical.Assembly.signalShift-sigma := by
    rw [←Target830Physical.Transport.signalShift_eq]
    ring
  rw [hexp] at herror
  have he : ‖A-F/N‖≤ Ct*E := herror
  have hf' : ‖F/N‖≤ Cf*E := by
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
    (hβlo : Target830Physical.Arithmetic.theta ≤ HeckeZeroSupremum.beta)
    (hβ : HeckeZeroSupremum.beta ≤ (7/8:ℝ))
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (ell : Fin K→ℝ) (hell : ∀j,ellMin ≤ ell j) (hellinj : Function.Injective ell) (hellsum : ∑j,ell j=Target830Physical.Arithmetic.ell)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Ioo a b) (hWB : ∀j y,0 ≤ W j y ∧ W j y ≤ B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (sigma : ℝ) (hsigma : 0 < sigma)
    (hgeometric : sigma+8*e+nu≤1/20) (hprincipal : sigma+nu≤1/4000)
    (hwindow : sigma+e ≤ Target830Physical.Arithmetic.theta*ellMin) (hlarge : sigma+nu ≤ saving+Target830Physical.Assembly.signal Target830Physical.Arithmetic.theta)
    (eps R dmin dmax rmin ε κ cost mesh margin loss : ℝ)
    (heps : 0 < eps) (hR : 0 ≤ R) (hdmin : 0 < dmin) (hdmax : 0 ≤ dmax) (hdRange : dmin ≤ dmax)
    (hrmin : 0 < rmin) (hε : 0<ε) (hκ : 0<κ) (hcost : 0 ≤ cost) (hmesh : 0 < mesh) (hmargin : 0 < margin)
    (hphasebudget : 8*e*R+κ≤ε) (hphasegap : ε < rmin*mesh)
    (hheight : 2*τ < dmin*cost) (hloss : τ*(2+4*eps) < loss)
    (hcap : Target830Physical.Arithmetic.h+ζ ≤ dmax-margin)
    (helllo : ∀j,dmax*rmin ≤ ell j) (hellhi : ∀j,ell j ≤ dmin*R)
    (hζcap : ζ ≤ Target830Physical.Transport.rowExtension)
    (hfloorbudget : 26*e+(K+8)*eps+loss+mesh*Target830Physical.Arithmetic.ell+nu+sigma≤1/100)
    (η : Character)
    (hfinite : ∀n : ℕ,0< n →
      FiniteNonfloorNumeratorBound M H hH S hS hmax ell a b ζ e τ sigma W W0 W1 n η) :
    let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩;
      (fun Z : ℝ=> Target830PhysicalLow.normalizedProbe M H S hmax ell a b W W0 W1 η Z-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S)
          Target830Physical.Assembly.signalShift Z) =O[atTop]
        (fun Z : ℝ=> Z^(HeckeZeroSupremum.beta+Target830Physical.Assembly.signalShift-sigma)) := by
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
  apply Target830PhysicalLow.isBigO_rpow_of_eventual_norm_bound
  refine ⟨Ct+Cf,by positivity,?_⟩
  filter_upwards [ht,hf,eventually_gt_atTop (0:ℝ)] with Z ht hf hZ
  dsimp only at ht
  obtain ⟨hnorm,idx,grid,hlabels,hbins,hray,herror⟩ := ht
  have hnum := hf idx grid ⟨hlabels,hbins,hray⟩
  let N := actualNormalizer M H S ell a b W W0 W1 Z
  let F := finiteNonfloorNumerator M H S hS hmax ell a b ζ e τ W W0 W1 η Z idx grid
  let A := Target830PhysicalLow.normalizedProbe M H S hmax ell a b W W0 W1 η Z-
    HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S)
      Target830Physical.Assembly.signalShift Z
  let E := Z^(HeckeZeroSupremum.beta+Target830Physical.Assembly.signalShift-sigma)
  have hN : N≠0 := hnorm
  have hexp : HeckeZeroSupremum.beta-(4+Target830Physical.Transport.b)/6-sigma =
      HeckeZeroSupremum.beta+Target830Physical.Assembly.signalShift-sigma := by
    rw [←Target830Physical.Transport.signalShift_eq]
    ring
  rw [hexp] at herror
  have he : ‖A-F/N‖≤ Ct*E := herror
  have hf' : ‖F/N‖≤ Cf*E := by
    rw [norm_div]
    apply (div_le_iff₀ (norm_pos_iff.mpr hN)).mpr
    simpa only [N,F,E,mul_assoc,mul_comm,mul_left_comm] using hnum
  calc
    ‖A‖ = ‖(A-F/N)+F/N‖ := by rw [sub_add_cancel]
    _ ≤ ‖A-F/N‖+‖F/N‖ := norm_add_le _ _
    _ ≤ Ct*E+Cf*E := add_le_add he hf'
    _ = (Ct+Cf)*E := by ring

#print axioms normalizedProbe_high_of_finite_nonfloor_numerator
end SevenEighths.Target830PhysicalHighTransport
end
end OAI


#print axioms OAI.SevenEighths.Target830PhysicalHighTransport.selected_row_within_density_cutoff
#print axioms OAI.SevenEighths.Target830PhysicalHighTransport.normalizedProbe_high_of_finite_nonfloor_numerator
#print axioms OAI.SevenEighths.Target830PhysicalHighTransport.normalizedProbe_high_of_finite_nonfloor_numerator_at
end
