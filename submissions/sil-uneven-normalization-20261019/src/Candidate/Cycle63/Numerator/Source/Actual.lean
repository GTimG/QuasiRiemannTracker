import Candidate.Cycle63.Numerator.Source.OldClass
import Candidate.Cycle25.Numerator.FiniteHeight
import Candidate.Cycle63.Numerator.Source.Ledger
import Candidate.Cycle25.Numerator.PhysicalCollect
import Candidate.Cycle25.Numerator.SourceScalar
import Candidate.Cycle63.Numerator.Source.Collect
import Candidate.Cycle63.Numerator.Source.Helpers
import Candidate.Cycle63.Assembly.Final.CommonProbe

/- Original module: Candidate.Cycle63.Numerator.Source.OldCollect. -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

noncomputable section
set_option maxHeartbeats 2800000
open scoped Classical BigOperators ContDiff
open Filter
namespace Cycle63.Numerator.Source
open Cycle63.Arithmetic Cycle63.Arithmetic.Bernstein Cycle63.Numerator.OldFourth
open Cycle63.Numerator.Scalar
open Cycle25.Weighted.Numerator Cycle25.Numerator
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open Cycle63DetectorCount Cycle25DetectorRowCount HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

/-- A literal physical error-mask sum has the uniform pre-height certificate
exponent, with only the original full-class count and actual scalar as inputs. -/
theorem old_source_mask_amplitude_class (D:BaselineData)
    (hgap:theta < HeckeZeroSupremum.beta)
    (hbetatop : HeckeZeroSupremum.beta ≤ 7/8)
    (hkap : D.momentKappa=2*HeckeZeroSupremum.beta-1)
    (F:BaselineSourceData D) (hbeta:(51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (eps sigma : ℝ) (heps : 0<eps) (hsigma : 0 ≤ sigma)
    (hbudget : 16*D.e+2*eps+3*sigma/4+8*D.t ≤ (HeckeZeroSupremum.beta-theta)/4)
    (hfine:∀j,D.length j ≤  Cycle25.sourceMesh D.t/200) (J:Finset (Fin D.N)) :
    ∃degree:ℕ,∃C:ℝ,0 < C ∧ ∀ᶠU:ℝ in atTop,
      1 < U ∧ ∀(Z d:ℝ),1 < Z  →  d0 ≤ d  →  d ≤ dMinus  →  U=Z^d  → 
      ∀(η:Character) (x z:ℂ) (a height:ℝ),(51/100:ℝ) ≤ a  →  a ≤ 7/8  → 
      x.re=a+16*D.e  →  z.re=17/50  →  0 ≤ height  →  |z.im| ≤ height  → 
      ∀rows:Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U)  → 
      (∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue≠1)  → 
      (∀P:∀i:J,sourcePrimePool F Z i.val,Function.Injective (fun i=>(P i).val))  → 
      (∀i P,P∈sourcePrimePool F Z i → IsCoprime P.val η.modulus)  → 
      (∀i P,P∈sourcePrimePool F Z i → (4:ℝ) ≤ P.val.absNorm)  → 
      (∀i,∀P∈F.S,(P.absNorm:ℝ) ≤ Z^(D.length i))  → 
      (∀i:J,sourcePrimePool F Z i.val)  → 
      ∀bin:BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t,
      let Q := fun (u:FreeRow) s=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length s)) z
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=>D.length s/d) Q bin
      let main := (Finset.univ:Finset (Fin D.N)) \ J
      let q := weightedMean Finset.univ (fun s=>D.length s/d)
        (maskedGain main (binValue Finset.univ ((2*a-1)/2) D.t bin))
      rows'.Nonempty  →  ∀Cs K C0:ℝ,0 ≤ Cs  →  1 ≤ K  →  1 ≤ C0  → 
      (rows'.card:ℝ) ≤ K*C0*Z^(3*D.t)*U^(countingR D.momentKappa (2*a-1) (q/(2*a-1))+sigma)  → 
      (∀u∈rows',‖frequencyWeight z ⟨u.val,u.property.1⟩*numeratorFreeRowScalar F.S F.exclusions F.maximal η u x z‖ ≤ 
        Cs*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^(2*eps)*U^(2*eps)*U^(-(17/50:ℝ))*Z^((17/25)*D.t))  → 
      (∀u∈rows',∀s,‖Q u s‖ ≤ (Z^(D.length s))^
        (HeckePrimeAmplitudeBins.amplitude (Z^(D.length s)) ((2*a-1)/2) D.t (Q u s)+D.t))  → 
      ‖sourceMaskContribution F η rows' J Z x z (Z^Cycle63.Arithmetic.y)‖  ≤ 
        (C*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^((degree:ℝ)+2*eps)*
          Z^(Assembly.signal HeckeZeroSupremum.beta-499/5000000000-(HeckeZeroSupremum.beta-theta)/2-D.t-kernelExponent a D.e) := by
  obtain ⟨degree,C,hC,hclass⟩ := old_source_packet_amplitude_class D F hbeta (by rw [hkap]) hfine J
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [hclass] with U hclass
  refine ⟨hclass.1,?_⟩
  intro Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hheight hzim rows hrows hrow hdis hη hQ hS Pbase bin
  dsimp only
  let Q := fun (u:FreeRow) s=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length s)) z
  let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=>D.length s/d) Q bin
  let main := (Finset.univ:Finset (Fin D.N)) \ J
  let q := weightedMean Finset.univ (fun s=>D.length s/d)
    (maskedGain main (binValue Finset.univ ((2*a-1)/2) D.t bin))
  intro hne Cs K C0 hCs hK hC0 hcard hscalar hupper
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hU0 : 0 < U := zero_lt_one.trans hclass.1
  have hd0 : 0 < d := d0_pos.trans_le hd
  have hδ : 0 < 2*a-1 := by linarith
  have hsub : rows' ⊆ rows := Finset.filter_subset _ _
  have hY : U^(Cycle63.Arithmetic.y/d)=Z^Cycle63.Arithmetic.y := by
    rw [hUZ,←Real.rpow_mul hZ0.le,mul_div_cancel₀ _ hd0.ne']
  have hcount1 : 1 ≤ K*C0*Z^(3*D.t) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hK hC0)
      (Real.one_le_rpow hZ.le (by have := D.t_pos;positivity))
  have hb := hclass.2 Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hheight hzim rows hrows hrow
    hdis hη Pbase bin hne (countingR D.momentKappa (2*a-1) (q/(2*a-1))+sigma)
    (K*C0*Z^(3*D.t)) hcount1 hcard hupper
  have heq (u:FreeRow) (hu:u∈rows') := errorLabelNumerator_eq_packet F.S F.exclusions (4*D.e) F.first η u
    (hrow u (hsub hu)) J (sourcePrimePool F Z) (fun s=>source_prime_pool_outside F Z s) hdis hη hQ
    (fun _=>F.W) (fun s=>Z^(D.length s)) x z (by rw [hx];linarith [D.e_pos]) hz.ge
    (by rw [hx];linarith [D.e_pos]) F.W 1 2 (by norm_num) F.complex_support (F.W.smooth ⊤)
    (Z^Cycle63.Arithmetic.y) (Real.rpow_pos_of_pos hZ0 _)
  have hlabel : (∑u∈rows',‖errorLabelNumerator F.S F.exclusions η u J (sourcePrimePool F Z)
      (fun s=>source_prime_pool_outside F Z s) (fun _=>F.W) (fun s=>Z^(D.length s)) x z F.W (Z^Cycle63.Arithmetic.y)*
      (∏s∈main,Q u s)‖)  ≤ 
    C*(K*C0*Z^(3*D.t))*(1+height)^degree*(U^(Cycle63.Arithmetic.y/d))^(-(1/2:ℝ))*(∏s:J,(Z^(D.length s.val))^(-(4/25:ℝ)))*
      U^(D.t+q*(Cycle63.Arithmetic.ell/d)-q*baseCapacity D.momentKappa d/2+
        (3*(countingR D.momentKappa (2*a-1) (q/(2*a-1))+sigma)+1+D.t+D.t)/4+
        (2*a-1)*Cycle25.sourceMesh D.t/4+(2*a-1)*(D.t+D.t)/2+D.t*(Cycle63.Arithmetic.ell/d)) := by
    convert hb using 1
    calc
      _ = ∑i:rows',‖errorLabelNumerator F.S F.exclusions η i.val J (sourcePrimePool F Z)
          (fun s=>source_prime_pool_outside F Z s) (fun _=>F.W) (fun s=>Z^(D.length s)) x z F.W (Z^Cycle63.Arithmetic.y)*
          (∏s∈main,Q i.val s)‖ := (Finset.sum_coe_sort rows' _).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [heq i.val i.property,hY]
  let A := Cs*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^(2*eps)*U^(2*eps)*
    U^(-(17/50:ℝ))*Z^((17/25)*D.t)
  have hA : 0 ≤ A := by dsimp only [A];positivity
  have hphysical := source_mask_physical_front F η rows' J Z hZ0 x z hz (Z^Cycle63.Arithmetic.y) hS A _ hA hscalar hlabel
  have hselection := old_source_class_main_selection D F hfine Z d 0 (2*a-1) hZ ⟨hd,hdmax⟩ (by norm_num) hδ.le z rows main bin hne
  have hq0 : 0 ≤ q := hselection.1
  have hqmax : q ≤ (2*a-1)/2 := hselection.2.1
  have he := Scalar.source_packet_multiplicative_identity J D.length D.slots_sum Z D.momentKappa d
    (oldCapacityAt D.momentKappa d) (2*a-1) q (C*K*C0*((1+height)^degree)) (physicalLoss D eps sigma 0)
    hZ0 hd0.ne' hδ.ne'
  have hcapscale : oldCapacityAt D.momentKappa d/d=baseCapacity D.momentKappa d := by
    apply (div_eq_iff hd0.ne').mpr
    simpa only [mul_comm] using (base_scaled (κ:=D.momentKappa) hd0).symm
  rw [hcapscale] at he
  dsimp [physicalLoss] at he
  have hcollapse : A*Z^(-(4/25:ℝ)*(∑j:{i:Fin D.N//i ∉ J},D.length j.val))*
      (C*(K*C0*Z^(3*D.t))*(1+height)^degree*(U^(Cycle63.Arithmetic.y/d))^(-(1/2:ℝ))*(∏s:J,(Z^(D.length s.val))^(-(4/25:ℝ)))*
      U^(D.t+q*(Cycle63.Arithmetic.ell/d)-q*baseCapacity D.momentKappa d/2+
        (3*(countingR D.momentKappa (2*a-1) (q/(2*a-1))+sigma)+1+D.t+D.t)/4+
        (2*a-1)*Cycle25.sourceMesh D.t/4+(2*a-1)*(D.t+D.t)/2+D.t*(Cycle63.Arithmetic.ell/d))) =
      (C*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^(2*eps)*(1+height)^degree*
        Z^(numeratorExponent D.momentKappa d (oldCapacityAt D.momentKappa d) (2*a-1) (q/(2*a-1))+
          weightedSourceLoss d (2*a-1) (physicalLoss D eps sigma 0)) := by
    dsimp only [A]
    rw [hUZ]
    calc
      _ = (Cs*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^(2*eps))*
          (((Z^d)^(2*eps)*(Z^d)^(-(17/50:ℝ))*Z^((17/25)*D.t)*
            Z^(-(4/25:ℝ)*(∑j:{i:Fin D.N//i ∉ J},D.length j.val)))*
          (C*(K*C0*Z^(3*D.t))*(1+height)^degree*((Z^d)^(Cycle63.Arithmetic.y/d))^(-(1/2:ℝ))*
            (∏s:J,(Z^(D.length s.val))^(-(4/25:ℝ)))*
            (Z^d)^(D.t+q*(Cycle63.Arithmetic.ell/d)-q*baseCapacity D.momentKappa d/2+
              (3*(countingR D.momentKappa (2*a-1) (q/(2*a-1))+sigma)+1+D.t+D.t)/4+
              (2*a-1)*Cycle25.sourceMesh D.t/4+(2*a-1)*(D.t+D.t)/2+D.t*(Cycle63.Arithmetic.ell/d)))) := by ring
      _ = _ := by
        have hex : (2*a-1)*(Cycle25.sourceMesh D.t+4*D.t)/4 =
          (2*a-1)*Cycle25.sourceMesh D.t/4+(2*a-1)*(D.t+D.t)/2 := by ring
        rw [hex] at he
        have hat : (Finset.univ : Finset J)=J.attach := rfl
        rw [←hat] at he
        dsimp only [physicalLoss]
        simp only [add_zero,zero_div,add_assoc] at he
        convert congrArg
          (fun r : ℝ => (Cs*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^(2*eps))*r) he using 1 <;> ring
  have hphysical' := hphysical.trans_eq hcollapse
  have hheightpow : (1+height)^degree  ≤  (3+height)^(degree:ℝ) := by
    rw [Real.rpow_natCast]
    exact pow_le_pow_left₀ (by linarith) (by linarith) _
  have hcert := old_physical_packet_certificate D eps sigma d a q hgap hbetatop hkap heps.le hsigma hbudget ⟨hd,hdmax⟩ ha hatop ⟨hq0,hqmax⟩
  apply hphysical'.trans
  calc
    _  ≤  (C*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^(2*eps)*(3+height)^(degree:ℝ)*
        Z^(Assembly.signal HeckeZeroSupremum.beta-499/5000000000-(HeckeZeroSupremum.beta-theta)/2-D.t-kernelExponent a D.e) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hheightpow (by positivity)
      · exact Real.rpow_le_rpow_of_exponent_le hZ.le hcert
      · positivity
      · positivity
    _ = _ := by rw [Real.rpow_add (by linarith : 0 < 3+height) (degree:ℝ) (2*eps)];ring


theorem old_source_integrated_amplitude_classes (D : BaselineData)
    (hgap : theta < HeckeZeroSupremum.beta)
    (hbetatop : HeckeZeroSupremum.beta ≤ 7/8)
    (hkap : D.momentKappa=2*HeckeZeroSupremum.beta-1)
    (F : BaselineSourceData D) (hbeta : (51/100:ℝ)  ≤  HeckeZeroSupremum.beta)
    (eps sigma : ℝ) (heps : 0<eps) (hsigma : 0 ≤ sigma)
    (hbudget : 16*D.e+2*eps+3*sigma/4+8*D.t ≤ (HeckeZeroSupremum.beta-theta)/4)
    (hfine : ∀j,D.length j  ≤  Cycle25.sourceMesh D.t/200) :
    ∃Jw : ℝ,0  ≤  Jw ∧ ∃C : ℝ,0 < C ∧ ∀ᶠU : ℝ in atTop,
      1 < U ∧ ∀(Z d : ℝ),1 < Z  →  d0  ≤  d  →  d  ≤  dMinus  →  U=Z^d  → 
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
          U^(countingR D.momentKappa (2*a-1) (q/(2*a-1))+sigma))  → 
      (∀u∈rows,‖frequencyWeight z ⟨u.val,u.property.1⟩*
        numeratorFreeRowScalar F.S F.exclusions F.maximal η u x z‖  ≤ 
        Cs*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^(2*eps)*
          U^(2*eps)*U^(-(17/50:ℝ))*Z^((17/25)*D.t))  → 
      (∀u∈rows,∀s,‖Q u s‖  ≤  (Z^(D.length s))^
        (HeckePrimeAmplitudeBins.amplitude (Z^(D.length s)) ((2*a-1)/2) D.t (Q u s)+D.t))  → 
      ‖Cycle25.Weighted.FullWContour.integratedDyadValue F.S F.exclusions F.maximal η rows (sourcePrimePool F Z)
        (fun s=>source_prime_pool_outside F Z s) (fun _=>F.W) (fun s=>Z^(D.length s)) F.W (Z^Cycle63.Arithmetic.y) x z‖  ≤ 
        (C*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^Jw*
          Z^(Assembly.signal HeckeZeroSupremum.beta-499/5000000000-(HeckeZeroSupremum.beta-theta)/2-D.t-kernelExponent a D.e) := by
  choose degree Cmask hCmask hmask using (fun J : Finset (Fin D.N)=>old_source_mask_amplitude_class D hgap hbetatop hkap F hbeta eps sigma heps hsigma hbudget hfine J)
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
    Z^(Assembly.signal HeckeZeroSupremum.beta-499/5000000000-(HeckeZeroSupremum.beta-theta)/2-D.t-kernelExponent a D.e)
  let A : ℝ := common*Ctot*(3+height)^(Jw+2*eps)
  have hcommon : 0  ≤  common := by dsimp only [common];positivity
  have hA : 0  ≤  A := by dsimp only [A];positivity
  have hmaskBound (bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t)
      (hne : (classRows bin).Nonempty) (J : Finset (Fin D.N)) :
      ‖sourceMaskContribution F η (classRows bin) J Z x z (Z^Cycle63.Arithmetic.y)‖  ≤  A := by
    have hsub : classRows bin  ⊆  rows := Finset.filter_subset _ _
    have hh := (hall J).2 Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hH him
      rows hrows hrow (hdis J) hη hQ hS (fun j:J=>Pbase j.val) bin hne Cs K C0 hCs hK hC0
      (hcount J bin hne) (fun u hu=>hscalar u (hsub hu)) (fun u hu=>hupper u (hsub hu))
    have he := (hheight height eps hH heps.le).1 J
    calc
      _  ≤  (Cmask J*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
          (3+height)^((degree J:ℝ)+2*eps)*
          Z^(Assembly.signal HeckeZeroSupremum.beta-499/5000000000-(HeckeZeroSupremum.beta-theta)/2-D.t-kernelExponent a D.e) := hh
      _ = common*(Cmask J*(3+height)^((degree J:ℝ)+2*eps)) := by dsimp only [common];ring
      _  ≤  common*(Ctot*(3+height)^(Jw+2*eps)) := mul_le_mul_of_nonneg_left he hcommon
      _ = A := by dsimp only [A];ring
  have hclass (bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t)
      (hne : (classRows bin).Nonempty) :
      ‖reconstructedDyadValue F.S F.exclusions F.maximal η (classRows bin) (sourcePrimePool F Z)
        (fun s=>source_prime_pool_outside F Z s) (fun _=>F.W) (fun s=>Z^(D.length s)) x z F.W (Z^Cycle63.Arithmetic.y)‖  ≤  maskFactor*A := by
    calc
      _ = ‖∑J∈Finset.univ.powerset,sourceMaskContribution F η (classRows bin) J Z x z (Z^Cycle63.Arithmetic.y)‖ :=
        congrArg norm (source_reconstructed_sum_masks F η (classRows bin) Z x z (Z^Cycle63.Arithmetic.y))
      _  ≤  ∑J∈Finset.univ.powerset,A := by
        apply (norm_sum_le _ _).trans
        exact Finset.sum_le_sum (fun J _=>hmaskBound bin hne J)
      _ = maskFactor*A := by
        simp only [Finset.sum_const,Finset.card_powerset,Finset.card_univ,Fintype.card_fin,
          nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
        rfl
  have hr := reconstructedDyadValue_class_uniform F.S F.exclusions F.maximal η rows
    (sourcePrimePool F Z) (fun s=>source_prime_pool_outside F Z s) (fun _=>F.W) (fun s=>Z^(D.length s))
    x z F.W (Z^Cycle63.Arithmetic.y) Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (by linarith)
    (fun s=>D.length s/d) Q (maskFactor*A) (mul_nonneg hmf.le hA) hclass
  have heq := integratedDyadValue_reconstruction F.S F.exclusions F.maximal (4*D.e) F.first η rows hrow
    (sourcePrimePool F Z) (fun s=>source_prime_pool_outside F Z s) hdis hdisAll hη hQ
    (fun _=>F.W) (fun s=>Z^(D.length s)) x z (by rw [hx];linarith [D.e_pos]) hz.ge
    (by rw [hx];linarith [D.e_pos]) F.W 1 2 (by norm_num) F.complex_support (Z^Cycle63.Arithmetic.y)
    (Real.rpow_pos_of_pos hZ0 _)
  rw [heq,norm_mul]
  have hpi : ‖(2*Real.pi:ℂ)‖=2*Real.pi := by
    rw [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  rw [hpi]
  apply (mul_le_mul_of_nonneg_left hr (by positivity : 0  ≤  2*Real.pi)).trans_eq
  simp only [Finset.card_univ,Fintype.card_fin]
  dsimp only [classFactor,maskFactor,A,common]
  ring



end Cycle63.Numerator.Source
end

/- Original module: Candidate.Cycle63.Numerator.Source.Combined. -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

noncomputable section
set_option maxHeartbeats 2800000
open scoped Classical BigOperators ContDiff
open Filter
namespace Cycle63.Numerator.Source
open Cycle63.Arithmetic Cycle63.Arithmetic.Bernstein Cycle63.Numerator.Capacity Cycle63.Numerator.Fourth
open Cycle63.Numerator.Scalar
open Cycle25.Weighted.Numerator Cycle25.Numerator
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open Cycle63DetectorCount Cycle25DetectorRowCount HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

theorem source_integrated_all_bands (D : BaselineData)
    (hgap : theta < HeckeZeroSupremum.beta)
    (hbetatop : HeckeZeroSupremum.beta ≤ 7/8)
    (hkap : D.momentKappa=2*HeckeZeroSupremum.beta-1)
    (F : BaselineSourceData D) (hbeta : (51/100:ℝ)  ≤  HeckeZeroSupremum.beta)
    (bPhi mesh affineError : ℝ) (haff : 0<affineError)
    (hsPhi : Function.support (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ → ℂ) ⊆ Set.Iic bPhi)
    (di : ℕ) (control : Finset (ℕ×ℕ)) (Ci : ℝ) (hCi : 0<Ci)
    (hinput : ∀ᶠU:ℝ in atTop,AffineAt F bPhi mesh affineError U di control Ci)
    (hfineAffine : ∀j,D.length j ≤  mesh/200)
    (eps sigma : ℝ) (heps : 0<eps) (hsigma : 0 ≤ sigma)
    (hbudget : 16*D.e+2*eps+3*sigma/4+affineError/4+8*D.t ≤ (HeckeZeroSupremum.beta-theta)/4)
    (hfine : ∀j,D.length j  ≤  Cycle25.sourceMesh D.t/200) :
    ∃Jw : ℝ,0  ≤  Jw ∧ ∃C : ℝ,0 < C ∧ ∀ᶠU : ℝ in atTop,
      1 < U ∧ ∀(Z d : ℝ),1 < Z  →  d0  ≤  d  →  d  ≤  dPlus  →  U=Z^d  → 
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
          U^(countingR D.momentKappa (2*a-1) (q/(2*a-1))+sigma))  → 
      (∀u∈rows,‖frequencyWeight z ⟨u.val,u.property.1⟩*
        numeratorFreeRowScalar F.S F.exclusions F.maximal η u x z‖  ≤ 
        Cs*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^(2*eps)*
          U^(2*eps)*U^(-(17/50:ℝ))*Z^((17/25)*D.t))  → 
      (∀u∈rows,∀s,‖Q u s‖  ≤  (Z^(D.length s))^
        (HeckePrimeAmplitudeBins.amplitude (Z^(D.length s)) ((2*a-1)/2) D.t (Q u s)+D.t))  → 
      ‖Cycle25.Weighted.FullWContour.integratedDyadValue F.S F.exclusions F.maximal η rows (sourcePrimePool F Z)
        (fun s=>source_prime_pool_outside F Z s) (fun _=>F.W) (fun s=>Z^(D.length s)) F.W (Z^Cycle63.Arithmetic.y) x z‖  ≤ 
        (C*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^Jw*
          Z^(Assembly.signal HeckeZeroSupremum.beta-499/5000000000-(HeckeZeroSupremum.beta-theta)/2-D.t-kernelExponent a D.e) := by
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
  by_cases hdn : dMinus≤d
  · have hh := hn.2 Z d hZ hdn hdmax hUZ η x z a height ha hatop hx hz hH him rows
      hrows hrow hdis hdisAll hη hQ hS Pbase Cs K C0 hCs hK hC0 hcount hscalar hupper
    apply hh.trans
    gcongr <;> linarith
  · have hh := ho.2 Z d hZ hd (le_of_not_ge hdn) hUZ η x z a height ha hatop hx hz hH him rows
      hrows hrow hdis hdisAll hη hQ hS Pbase Cs K C0 hCs hK hC0 hcount hscalar hupper
    apply hh.trans
    gcongr <;> linarith
end Cycle63.Numerator.Source
end

/- Original module: Candidate.Cycle63.Numerator.Source.Actual. -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

noncomputable section
set_option maxHeartbeats 3000000
open scoped Classical BigOperators Topology ContDiff
open Filter
namespace Cycle63.Numerator.Source
open Cycle63.Arithmetic Cycle63.Arithmetic.Bernstein Cycle63.Numerator.Scalar Cycle63.Numerator.Fourth
open Cycle25.Weighted.Numerator Cycle25.Numerator
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open Cycle63DetectorCount Cycle25DetectorRowCount HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
open Cycle63.FinalAssembly

/-- The genuine initial physical affine moment, at an error fixed before height. -/
def ActualAffineInput (A : ChosenData) : Prop :=
  ∃bPhi affineError : ℝ,0<affineError ∧ affineError≤(HeckeZeroSupremum.beta-theta)/10000 ∧
  Function.support (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ→ℂ)⊆Set.Iic bPhi ∧
  ∃di : ℕ,∃control : Finset (ℕ×ℕ),∃Ci : ℝ,0<Ci ∧
    ∀ᶠU:ℝ in atTop,AffineAt A.F bPhi A.P.mesh affineError U di control Ci

def sourceTarget : ℝ := Assembly.signal HeckeZeroSupremum.beta-499/5000000000-
  (HeckeZeroSupremum.beta-theta)/2

def RawSourceDyadBound (A : ChosenData) (η : Character) (Z τ : ℝ) (n : ℕ)
    (J C C0 : ℝ) : Prop :=
  ∀(rows : Finset FreeRow) (d a : ℝ) (i : ℕ),d0≤d → d≤dPlus →
  51/100<a → a≤7/8 → i≤n →
  (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
    (calibrationForSet A.F.S A.F.maximal).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-A.D.t)) →
  (∀u∈rows,(Z^d)^(1/100:ℝ)≤rowNorm u ∧ rowNorm u≤Z^d) →
  (∀u∈rows,(rowCharacter A.F.S A.F.exclusions.prime u).residue≠1) →
  (∀u∈rows,Z^(d-2*A.D.t)≤rowNorm u) →
  (∀u∈rows,detectorMaximum (sourceDetectorFamily A.F.S A.F.exclusions.prime η u
    (rayCubeFamily A.F.modulus ⊤ le_top u)) (3*(i+1:ℕ)*Z^τ)<a+2*A.D.e) →
  (∀u∈rows,a≤detectorMaximum (sourceDetectorFamily A.F.S A.F.exclusions.prime η u
    (rayCubeFamily A.F.modulus ⊤ le_top u)) ((3*i:ℕ)*Z^τ)) →
  ∀q∈Cycle25.Weighted.FullWContour.szRectangle ((3*i+1:ℕ)*Z^τ),
  ‖Cycle25.Weighted.FullWContour.integratedDyadValue A.F.S A.F.exclusions A.F.maximal η rows
    (sourcePrimePool A.F Z) (fun j=>source_prime_pool_outside A.F Z j)
    (fun _=>A.F.W) (fun j=>Z^(A.D.length j)) A.F.W (Z^y)
    ((((a+16*A.D.e):ℝ):ℂ)+q.1*Complex.I) ((17/50:ℂ)+q.2*Complex.I)‖≤
  C*C0*(η.modulus.absNorm:ℝ)^(2*A.P.eps)*(3+((3*i+1:ℕ):ℝ)*Z^τ)^J*
    Z^(sourceTarget-A.D.t-kernelExponent a A.D.e)

lemma actual_source_loss_budget (A : ChosenData) (affineError : ℝ)
    (haff : affineError≤(HeckeZeroSupremum.beta-theta)/10000) :
    16*A.D.e+2*A.P.eps+3*((HeckeZeroSupremum.beta-theta)/10000)/4+affineError/4+8*A.D.t≤
      (HeckeZeroSupremum.beta-theta)/4 := by
  have hep : A.P.eps≤A.D.t/100 := by
    have hn : (0:ℝ)≤A.D.N := Nat.cast_nonneg _
    have hp := A.P.eps_pos
    nlinarith [A.P.eps_budget]
  have ht : A.D.t≤(HeckeZeroSupremum.beta-theta)/10000 := by
    linarith [A.count_budget,A.D.epsilon_pos,A.D.t_pos]
  linarith [A.P.e_tsmall,A.D.t_pos]

/-- Genuine count and scalar theorems discharge every finite-class premise. -/
theorem actual_raw_source (hgap : theta<HeckeZeroSupremum.beta) (A : ChosenData)
    (hAffine : ActualAffineInput A) :
    ∃J : ℝ,0≤J ∧ ∀τ : ℝ,HeightAdmissible A.D A.P J τ →
    ∀n : ℕ,∀η : Character,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
    ∀C0 : ℝ,1≤C0 →
    SourceMomentBound A.D.toData (baselineSource A.D A.F) A.counts η Z τ (C0*Z^A.D.t) (Z^(2*τ)) →
    RawSourceDyadBound A η Z τ n J C C0 := by
  obtain ⟨bPhi,affineError,haff,haffsmall,hsPhi,di,control,Ci,hCi,hinput⟩ := hAffine
  have hb : (51/100:ℝ)≤HeckeZeroSupremum.beta := by
    have ht : (51/100:ℝ)<theta := by norm_num [theta]
    linarith
  have hbetatop : HeckeZeroSupremum.beta≤7/8 := by
    have hh := A.D.momentKappa_hi
    rw [A.kappa_exact] at hh
    linarith
  let sigma : ℝ := (HeckeZeroSupremum.beta-theta)/10000
  have hsigma : 0 ≤ sigma := by dsimp [sigma];positivity
  obtain ⟨J,hJ,C,hC,hcollect⟩ := source_integrated_all_bands A.D hgap hbetatop A.kappa_exact A.F hb
    bPhi A.P.mesh affineError haff hsPhi di control Ci hCi hinput A.P.slots_mesh
    A.P.eps sigma A.P.eps_pos hsigma (actual_source_loss_budget A affineError haffsmall) A.fine
  obtain ⟨Cs,hCs,hscalar⟩ := source_scalar_on_rows A.D A.F A.P.eps A.P.eps_pos
  refine ⟨J,hJ,?_⟩
  intro τ hheight n η
  rcases hheight with ⟨hτ,hτzero,hτcost,hτ2,hτeps,hτJ⟩
  obtain ⟨K,hK,hcount⟩ := source_masked_count_with_error A.D.toData (baselineSource A.D A.F)
    A.counts τ sigma n hτ hτzero hτcost hτ2 A.count_budget
  refine ⟨C*Cs*K,by have hk := zero_lt_one.trans_le hK;positivity,?_⟩
  filter_upwards [eventually_uniform_source_conductor d0 d0_pos hcollect,hcount η,
    source_prime_bins A.D A.F A.P τ n hτ hτcost,
    source_prime_reconstruction_geometry A.F η,source_pools_nonempty A.D A.F,
    weighted_source_height_le τ n hτ,
    (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2:ℝ)),eventually_gt_atTop (1:ℝ)]
    with Z hcollect hcount hupper hgeo hpools hheight hT hZ
  intro C0 hC0 hmom
  unfold RawSourceDyadBound
  intro rows d a i hd hdmax ha hatop hi hsource hrows hrow hfreq hnext hcurrent q hq
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hd' : d≤7/8 := hdmax.trans (by norm_num [dPlus,h])
  have hz : ((17/50:ℂ)+q.2*Complex.I).re=17/50 := by norm_num
  have hx : ((((a+16*A.D.e):ℝ):ℂ)+q.1*Complex.I).re=a+16*A.D.e := by simp
  have him : |((17/50:ℂ)+q.2*Complex.I).im|≤((3*i+1:ℕ):ℝ)*Z^τ := by simpa using hq.2
  have hcounts := hcount d a C0 hd hd' ha hatop hC0 rows hsource i hi hnext hcurrent
    ((17/50:ℂ)+q.2*Complex.I) hz (him.trans (hheight i hi).2) hmom
  have heq : canonicalFamily A.D.toData (baselineSource A.D A.F) Z ((17/50:ℂ)+q.2*Complex.I)=
      (fun (u:FreeRow) j=>HeckePrimeRow.canonicalPrimeAmplitude A.F.modulus ⊤ u.val A.F.W 2
        (Z^(A.D.length j)) ((17/50:ℂ)+q.2*Complex.I)) := by
    funext u j
    simp only [canonicalFamily,baselineSource,←A.F.complex_eq]
    rfl
  rw [heq] at hcounts
  let Q (u:FreeRow) (j:Fin A.D.N) := HeckePrimeRow.canonicalPrimeAmplitude A.F.modulus ⊤ u.val A.F.W 2
    (Z^(A.D.length j)) ((17/50:ℂ)+q.2*Complex.I)
  have hupper' : ∀u∈rows,∀j,‖Q u j‖≤(Z^(A.D.length j))^
      (HeckePrimeAmplitudeBins.amplitude (Z^(A.D.length j)) ((2*a-1)/2) A.D.t (Q u j)+A.D.t) := by
    intro u hu j
    have hh := hupper d hd hd' η u (hsource u hu).2.1 (hsource u hu).2.2.1
      (hsource u hu).2.2.2 a i hi ha.le (by linarith) (hnext u hu)
      ((17/50:ℂ)+q.2*Complex.I) hz him j
    simpa only [show a-1/2=(2*a-1)/2 by ring] using hh.2.2.2.1
  have hscalar' := hscalar η rows Z τ d a i hZ0 hT ha.le hatop hfreq
    (fun u hu=>(hrows u hu).2) hnext q hq
  have hbase : ∀j,sourcePrimePool A.F Z j := fun j=>⟨(hpools j).choose,(hpools j).choose_spec⟩
  have hc := (hcollect d hd).2 Z d hZ hd hdmax rfl η
    ((((a+16*A.D.e):ℝ):ℂ)+q.1*Complex.I) ((17/50:ℂ)+q.2*Complex.I)
    a (((3*i+1:ℕ):ℝ)*Z^τ) ha.le hatop hx hz (hheight i hi).1 him rows hrows hrow
    hgeo.2.1 hgeo.2.2.1 hgeo.2.2.2.1 hgeo.2.2.2.2.1 hgeo.2.2.2.2.2 hbase Cs K C0 hCs.le hK hC0
    (by
      dsimp only
      intro J bin hne
      apply (hcounts (Finset.univ\J) bin hne).2.2.trans
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hp : 1≤Z^(3*A.D.t) := Real.one_le_rpow hZ.le (by have := A.D.t_pos;positivity)
      nlinarith [mul_nonneg (zero_le_one.trans hK) (zero_le_one.trans hC0)]) hscalar' hupper'
  simpa only [sourceTarget,mul_assoc] using hc
end Cycle63.Numerator.Source
end
