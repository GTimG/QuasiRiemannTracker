/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Fixed positive row fee and conductor extension 1/10^22.
The support padding is half the extension; the later budget is reduced accordingly.
Inherited notices and source attribution follow unchanged. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Fixed HIGH row fee 1/10^12, source reserve half that fee.
Contour extension 1/10^10 and support padding 5/10^11 are unchanged.
Inherited notices and preceding adapter attribution follow unchanged. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Restart return: h < .813, y < .473, ell < .173, row fee 1e-22.
All numerical proof obligations are re-elaborated; inherited notices follow. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Adapted for the fine-chain return: h < .810, floor reserve 1/10000.
All inherited notices follow unchanged; upstream source files are unmodified. -/
/- Repeated marks: fork of Collet's generic return module Transport.Transport.SharedNonfloor (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Modified by Sil (2026-10-26): forked into QRH.SilDensitySplit.Return (namespaces and imports renamed);
re-elaborated against the widened coarse box `BoundsN` (873/1000<θ, h<806/1000, ell<171/1000) and,
where used, the physical slot cap as the `PhysicalSchedule` field `cap`. -/
import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.Transport.Transport.CommonProbe
import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.Transport.Transport.NonfloorTransport
set_option autoImplicit false

namespace OAI
noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN]
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.BoundaryDensitySplitReturn.TransportHighTransport
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
    (he : 0 < e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (hζ' : ζ≤1/10000000000000000000000) (hτ : 0<τ)
    (ha : 0 < a) (hab : a ≤ b) (hB : 0 ≤ B) (hmin : 0 < ellMin) (hnu : 0 < nu)
    (hβlo : Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.theta ≤ HeckeZeroSupremum.beta)
    (hβ : HeckeZeroSupremum.beta ≤ (7/8:ℝ))
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (ell : Fin K→ℝ) (hell : ∀j,ellMin ≤ ell j) (hellinj : Function.Injective ell) (hellsum : ∑j,ell j=Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.ell)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Ioo a b) (hWB : ∀j y,0 ≤ W j y ∧ W j y ≤ B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (sigma : ℝ) (hsigma : 0 < sigma)
    (hgeometric : sigma+8*e+nu≤1/20) (hprincipal : sigma+nu≤1/4000)
    (hwindow : sigma+e ≤ Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.theta*ellMin) (hlarge : sigma+nu ≤ saving+Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Assembly.signal Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.theta)
    (eps R dmin dmax rmin ε κ cost mesh margin loss : ℝ)
    (heps : 0 < eps) (hR : 0 ≤ R) (hdmin : 0 < dmin) (hdmax : 0 ≤ dmax) (hdRange : dmin ≤ dmax)
    (hrmin : 0 < rmin) (hε : 0<ε) (hκ : 0<κ) (hcost : 0 ≤ cost) (hmesh : 0 < mesh) (hmargin : 0 < margin)
    (hphasebudget : 8*e*R+κ≤ε) (hphasegap : ε < rmin*mesh)
    (hheight : 2*τ < dmin*cost) (hloss : τ*(2+4*eps) < loss)
    (hcap : Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.h+ζ ≤ dmax-margin)
    (helllo : ∀j,dmax*rmin ≤ ell j) (hellhi : ∀j,ell j ≤ dmin*R)
    (hζcap : ζ ≤ Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Transport.rowExtension)
    (hfloorbudget : 26*e+(K+8)*eps+loss+mesh*Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.ell+nu+sigma≤1/10000) :
    let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃n : ℕ,0 < n ∧ ∀η : Character,∃C : ℝ,0 < C ∧ ∀ᶠ Z : ℝ in atTop,
      let Yp := fun j=>Z^(ell j)
      let T := fun j=>pool (RayQuotient.identityClass M H) S a b (Yp j)
      let hT := sharedNonfloorPoolOutside M H S K a b Yp
      let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.ell) (slotMass T (residueWeights W Yp)) : ℂ)
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
      (∀u∈rowBand (Z^(1/100:ℝ)) (Z^((Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.h:ℝ)+ζ)),
        (calibrationForSet S hmax).residueMonoid u.val≠0 →
        (∀θ,(rayCubeFamily M H hH u θ).residue≠1) ∧
        (∀θ,(rayCubeFamily M H hH u θ).modulus.absNorm≤
          conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm) ∧
        ∀hnp : ∀θ,(rayCubeFamily M H hH u θ).residue≠1,
        HeckeDetectorZeros.zeroMaximum (rayCubeFamily M H hH u) hnp
          (3*(idx u+1:ℕ)*Z^τ)<(51/100:ℝ)+e*grid u+2*e) ∧
      let alpha : FreeRow→ℝ := fun u=>51/100+e*grid u
      let height : FreeRow→ℝ := fun u=>(3*idx u+1:ℕ)*Z^τ
      ‖BoundaryDensitySplitTransportLow.normalizedProbe M H S hmax ell a b W W0 W1 η Z-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Assembly.signalShift Z-
        finiteCentralCubeRows S hS hmax η
          (supportedNonfloorRows S hmax (rowBand (Z^(1/100:ℝ)) (Z^((Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.h:ℝ)+ζ))) grid) T hT WC Yp
          W0 W1 (Z^(Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.x:ℝ)) (Z^(Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Arithmetic.y:ℝ)) Z e alpha height/normer‖≤
        C*Z^(HeckeZeroSupremum.beta-(4+Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Transport.b)/6-sigma) := by
  simpa only [BoundaryDensitySplitTransportLow.normalizedProbe, Qrh.JointDetector.BoundaryPhysical.TransportKernel.Transport.Transport.signalShift_eq] using
    BoundaryDensitySplitReturn.TransportHighRowFamily.actual_nonfloor_probe_transport M H hH K e δ a b B ζ saving τ ellMin nu
      he he' hδ hδ' hζ hζ' hτ ha hab hB hmin hnu hβlo hβ S hS hmax hfirst
      ell hell hellinj hellsum W hW hcompact hsupp hWB hne
      W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
      sigma hsigma hgeometric hprincipal hwindow hlarge
      eps R dmin dmax rmin ε κ cost mesh margin loss
      heps hR hdmin hdmax hdRange hrmin hε hκ hcost hmesh hmargin
      hphasebudget hphasegap hheight hloss hcap helllo hellhi hζcap hfloorbudget

end SevenEighths.BoundaryDensitySplitReturn.TransportHighTransport
end
end OAI
