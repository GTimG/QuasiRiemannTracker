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
/- Repeated marks: fork of Collet's generic return module PhysicalDirect.Collect (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Actual new-face source mask/class reconstruction, adapted Gao/Hailey Collet/OpenAI; Apache-2.0. -/
/- Modified by Sil (2026-10-26): forked into QRH.SilDensitySplit.Return (namespaces and imports renamed);
re-elaborated against the widened coarse box `BoundsN` (873/1000<θ, h<806/1000, ell<171/1000) and,
where used, the physical slot cap as the `PhysicalSchedule` field `cap`. -/
import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.Schedule
import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.PhysicalDirect.Mask
import Submissions.hailey_collet_1252270103.Cycle25.Numerator.FiniteHeight
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
open scoped Classical BigOperators ContDiff
open Filter
namespace Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect.Source
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
variable [Geometry.Parameters] [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
open Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic QRH.Record12518109Count Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Scalar QRH.Record1252270103Return.GenericPhysical
open Cycle25.Weighted.Numerator Cycle25.Numerator
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open QRH.Record12518109Count
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect Cycle25DetectorRowCount HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

theorem source_integrated_amplitude_classes (D : BaselineData)
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
      1 < U ∧ ∀(Z d : ℝ),1 < Z  →  dm  ≤  d  →  d  ≤  dp  →  U=Z^d  →
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
  choose degree Cmask hCmask hmask using (fun J : Finset (Fin D.N)=>source_mask_amplitude_class D hgap hbetatop hkap F hbeta bPhi mesh affineError haff hsPhi di control Ci hCi hinput hfineAffine eps sigma heps hsigma hbudget hfine J)
  obtain ⟨Jw,hJw,Ctot,hCtot,hcoeff,hheight⟩ := finite_height_envelope degree Cmask hCmask
  let classFactor : ℝ := (HeckeDetectorClassBudget.alphabetBound D.t:ℝ)^D.N
  let maskFactor : ℝ := (2:ℝ)^D.N
  have hcf : 0 < classFactor := by
    unfold classFactor HeckeDetectorClassBudget.alphabetBound
    positivity
  have hmf : 0 < maskFactor := by dsimp only [maskFactor];positivity
  refine ⟨Jw+2*eps,by linarith [heps],(2*Real.pi)*classFactor*maskFactor*Ctot,
    by positivity,?_⟩
  filter_upwards [Filter.eventually_all.mpr hmask] with U hall
  refine ⟨(hall ∅).1,?_⟩
  intro Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hH him rows hrows hrow
    hdis hdisAll hη hQ hS Pbase Cs K C0 hCs hK hC0
  dsimp only
  let Q := fun (u : FreeRow) s=>HeckePrimeRow.canonicalPrimeAmplitude
    F.modulus ⊤ u.val F.W 2 (Z^(D.length s)) z
  let classRows := fun bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t=>
    amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=>D.length s/d) Q bin
  intro hcount hscalar hupper
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  let common : ℝ := Cs*K*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
    Z^(Assembly.signal HeckeZeroSupremum.beta-sourceReserve-(HeckeZeroSupremum.beta-theta)/2-D.t-kernelExponent a D.e)
  let A : ℝ := common*Ctot*(3+height)^(Jw+2*eps)
  have hcommon : 0  ≤  common := by dsimp only [common];positivity
  have hA : 0  ≤  A := by dsimp only [A];positivity
  have hmaskBound (bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t)
      (hne : (classRows bin).Nonempty) (J : Finset (Fin D.N)) :
      ‖sourceMaskContribution F η (classRows bin) J Z x z (Z^GenericArithmetic.y)‖  ≤  A := by
    have hsub : classRows bin  ⊆  rows := Finset.filter_subset _ _
    have hh := (hall J).2 Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hH him
      rows hrows hrow (hdis J) hη hQ hS (fun j:J=>Pbase j.val) bin hne Cs K C0 hCs hK hC0
      (hcount J bin hne) (fun u hu=>hscalar u (hsub hu)) (fun u hu=>hupper u (hsub hu))
    have he := (hheight height eps hH heps.le).1 J
    calc
      _  ≤  (Cmask J*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
          (3+height)^((degree J:ℝ)+2*eps)*
          Z^(Assembly.signal HeckeZeroSupremum.beta-sourceReserve-(HeckeZeroSupremum.beta-theta)/2-D.t-kernelExponent a D.e) := hh
      _ = common*(Cmask J*(3+height)^((degree J:ℝ)+2*eps)) := by dsimp only [common];ring
      _  ≤  common*(Ctot*(3+height)^(Jw+2*eps)) := mul_le_mul_of_nonneg_left he hcommon
      _ = A := by dsimp only [A];ring
  have hclass (bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t)
      (hne : (classRows bin).Nonempty) :
      ‖reconstructedDyadValue F.S F.exclusions F.maximal η (classRows bin) (sourcePrimePool F Z)
        (fun s=>source_prime_pool_outside F Z s) (fun _=>F.W) (fun s=>Z^(D.length s)) x z F.W (Z^GenericArithmetic.y)‖  ≤  maskFactor*A := by
    calc
      _ = ‖∑J∈Finset.univ.powerset,sourceMaskContribution F η (classRows bin) J Z x z (Z^GenericArithmetic.y)‖ :=
        congrArg norm (source_reconstructed_sum_masks F η (classRows bin) Z x z (Z^GenericArithmetic.y))
      _  ≤  ∑J∈Finset.univ.powerset,A := by
        apply (norm_sum_le _ _).trans
        exact Finset.sum_le_sum (fun J _=>hmaskBound bin hne J)
      _ = maskFactor*A := by
        simp only [Finset.sum_const,Finset.card_powerset,Finset.card_univ,Fintype.card_fin,
          nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
        rfl
  have hr := reconstructedDyadValue_class_uniform F.S F.exclusions F.maximal η rows
    (sourcePrimePool F Z) (fun s=>source_prime_pool_outside F Z s) (fun _=>F.W) (fun s=>Z^(D.length s))
    x z F.W (Z^GenericArithmetic.y) Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (by linarith)
    (fun s=>D.length s/d) Q (maskFactor*A) (mul_nonneg hmf.le hA) hclass
  have heq := integratedDyadValue_reconstruction F.S F.exclusions F.maximal (4*D.e) F.first η rows hrow
    (sourcePrimePool F Z) (fun s=>source_prime_pool_outside F Z s) hdis hdisAll hη hQ
    (fun _=>F.W) (fun s=>Z^(D.length s)) x z (by rw [hx];linarith [D.e_pos]) hz.ge
    (by rw [hx];linarith [D.e_pos]) F.W 1 2 (by norm_num) F.complex_support (Z^GenericArithmetic.y)
    (Real.rpow_pos_of_pos hZ0 _)
  rw [heq,norm_mul]
  have hpi : ‖(2*Real.pi:ℂ)‖=2*Real.pi := by
    rw [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  rw [hpi]
  apply (mul_le_mul_of_nonneg_left hr (by positivity : 0  ≤  2*Real.pi)).trans_eq
  simp only [Finset.card_univ,Fintype.card_fin]
  dsimp only [classFactor,maskFactor,A,common]
  ring


end Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect.Source
