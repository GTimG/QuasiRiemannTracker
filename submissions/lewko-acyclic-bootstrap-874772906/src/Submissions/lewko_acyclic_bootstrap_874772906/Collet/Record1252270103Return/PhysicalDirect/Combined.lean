/- Actual old-band physical reconstruction on new geometry, adapted Gao/Hailey Collet/OpenAI; Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Return.Schedule
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Return.PhysicalDirect.Collect
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Return.PhysicalDirect.OldCollect
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle25.Numerator.FiniteHeight
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
open scoped Classical BigOperators ContDiff
open Filter
namespace QRH.Record1252270103Return.GenericPhysical.PhysicalDirect.Source
variable [Geometry.Parameters] [Geometry.Bounds] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
open QRH.Record1252270103Return.GenericArithmetic OAI OAI.SevenEighths
open QRH.Record1252270103Return.GenericArithmetic
open QRH.Record1252270103Return.GenericArithmetic QRH.Record12518109Count QRH.Record1252270103Return.GenericPhysical.PhysicalDirect
open QRH.Record1252270103Return.GenericPhysical.Scalar QRH.Record1252270103Return.GenericPhysical
open Cycle25.Weighted.Numerator Cycle25.Numerator
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open QRH.Record12518109Count
open QRH.Record1252270103Return.GenericPhysical.PhysicalDirect Cycle25DetectorRowCount HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

theorem source_integrated_all_bands (D : BaselineData)
    (hgap : theta < HeckeZeroSupremum.beta)
    (hbetatop : HeckeZeroSupremum.beta ≤ 7/8)
    (hkap : D.momentKappa=2*HeckeZeroSupremum.beta-1)
    (F : BaselineSourceData D) (hbeta : (51/100:ℝ)  ≤  HeckeZeroSupremum.beta)
    (bPhi mesh affineError : ℝ) (haff : 0< affineError)
    (hsPhi : Function.support (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ → ℂ) ⊆ Set.Iic bPhi)
    (di : ℕ) (control : Finset (ℕ×ℕ)) (Ci : ℝ) (hCi : 0< Ci)
    (hinput : ∀ᶠU:ℝ in atTop,AffineAt F bPhi mesh affineError U di control Ci)
    (hfineAffine : ∀j,D.length j ≤  mesh/200)
    (eps sigma : ℝ) (heps : 0< eps) (hsigma : 0 ≤ sigma)
    (hbudget : 16*D.e+2*eps+3*sigma/4+affineError/4+8*D.t ≤ (HeckeZeroSupremum.beta-theta)/4)
    (hfine : ∀j,D.length j  ≤  Cycle25.sourceMesh D.t/200) :
    ∃Jw : ℝ,0  ≤  Jw ∧ ∃C : ℝ,0 < C ∧ ∀ᶠU : ℝ in atTop,
      1 < U ∧ ∀(Z d : ℝ),1 < Z  →  d0  ≤  d  →  d  ≤  dp  →  U=Z^d  → 
      ∀(η : Character) (x z : ℂ) (a height : ℝ),(51/100:ℝ)  ≤  a  →  a  ≤  7/8  → 
      x.re=a+16*D.e  →  z.re=17/50  →  0  ≤  height  →  |z.im|  ≤  height  → 
      ∀rows : Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ)  ≤  rowNorm u ∧ rowNorm u  ≤  U)  → 
      (∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue≠1)  → 
      (∀J : Finset (Fin D.N),∀P : ∀i:J,sourcePrimePool F Z i.val,
        Function.Injective (fun i=>(P i).val))  → 
      (∀P : ∀i,sourcePrimePool F Z i,Function.Injective (fun i=>(P i).val))  → 
      (∀i P,P∈sourcePrimePool F Z i  →  IsCoprime P.val η.modulus)  → 
      (∀i P,P∈sourcePrimePool F Z i  →  (4:ℝ)  ≤  P.val.absNorm)  → 
      (∀i,∀P∈F.S,(P.absNorm:ℝ)  ≤  Z^(D.length i))  → 
      (∀i,sourcePrimePool F Z i)  → 
      ∀Cs K C0 : ℝ,0  ≤  Cs  →  1  ≤  K  →  1  ≤  C0  → 
      let Q := fun (u : FreeRow) s=>HeckePrimeRow.canonicalPrimeAmplitude
        F.modulus ⊤ u.val F.W 2 (Z^(D.length s)) z
      (∀J : Finset (Fin D.N),∀bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t,
        let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=>D.length s/d) Q bin
        let q := weightedMean Finset.univ (fun s=>D.length s/d)
          (maskedGain (Finset.univ\J) (binValue Finset.univ ((2*a-1)/2) D.t bin))
        rows'.Nonempty  →  (rows'.card:ℝ)  ≤  K*C0*Z^(3*D.t)*
          U^(QRH.Record1252270103Return.GenericCount.envelope D.momentKappa (2*a-1) (q/(2*a-1))+sigma))  → 
      (∀u∈rows,‖frequencyWeight z ⟨u.val,u.property.1⟩*
        numeratorFreeRowScalar F.S F.exclusions F.maximal η u x z‖  ≤ 
        Cs*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^(2*eps)*
          U^(2*eps)*U^(-(17/50:ℝ))*Z^((17/25)*D.t))  → 
      (∀u∈rows,∀s,‖Q u s‖  ≤  (Z^(D.length s))^
        (HeckePrimeAmplitudeBins.amplitude (Z^(D.length s)) ((2*a-1)/2) D.t (Q u s)+D.t))  → 
      ‖Cycle25.Weighted.FullWContour.integratedDyadValue F.S F.exclusions F.maximal η rows (sourcePrimePool F Z)
        (fun s=>source_prime_pool_outside F Z s) (fun _=>F.W) (fun s=>Z^(D.length s)) F.W (Z^GenericArithmetic.y) x z‖  ≤ 
        (C*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^Jw*
          Z^(Assembly.signal HeckeZeroSupremum.beta-sourceReserve-(HeckeZeroSupremum.beta-theta)/2-D.t-kernelExponent a D.e) := by
  obtain ⟨Jn,hJn,Cn,hCn,hn⟩ := source_integrated_amplitude_classes D hgap hbetatop hkap F hbeta
    bPhi mesh affineError haff hsPhi di control Ci hCi hinput hfineAffine eps sigma heps hsigma hbudget hfine
  obtain ⟨Jo,hJo,Co,hCo,ho⟩ := old_source_integrated_amplitude_classes D hgap hbetatop hkap F hbeta
    eps sigma heps hsigma (by linarith [haff]) hfine
  refine ⟨Jn+Jo,add_nonneg hJn hJo,Cn+Co,add_pos hCn hCo,?_⟩
  filter_upwards [hn,ho] with U hn ho
  refine ⟨hn.1,?_⟩
  intro Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hH him rows hrows hrow
    hdis hdisAll hη hQ hS Pbase Cs K C0 hCs hK hC0
  dsimp only
  intro hcount hscalar hupper
  by_cases hdn : dm≤ d
  · have hh := hn.2 Z d hZ hdn hdmax hUZ η x z a height ha hatop hx hz hH him rows
      hrows hrow hdis hdisAll hη hQ hS Pbase Cs K C0 hCs hK hC0 hcount hscalar hupper
    apply hh.trans
    gcongr <;> linarith
  · have hh := ho.2 Z d hZ hd (le_of_not_ge hdn) hUZ η x z a height ha hatop hx hz hH him rows
      hrows hrow hdis hdisAll hη hQ hS Pbase Cs K C0 hCs hK hC0 hcount hscalar hupper
    apply hh.trans
    gcongr <;> linarith
end QRH.Record1252270103Return.GenericPhysical.PhysicalDirect.Source

#print axioms QRH.Record1252270103Return.GenericPhysical.PhysicalDirect.Source.source_integrated_all_bands
