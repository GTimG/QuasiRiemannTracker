/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.cycle61_c0125139.Bundles.B020
import Submissions.cycle61_c0125139.Bundles.B023
import Submissions.cycle61_c0125139.Bundles.B047
import Submissions.cycle61_c0125139.Bundles.B058
import Submissions.cycle61_c0125139.Bundles.B069
import Submissions.cycle61_c0125139.Bundles.B070

/- BEGIN ORIGINAL Cycle61.Numerator.Scalar.SourcePacket; sha256 62e72521271b46ba87582110596de30f32f317bbf3e9d92c7084a6c1d7272175 -/
section
/-
Copyright (c) 2026 Hailey Collet. All rights reserved.
Released under Apache 2.0 license.
Finite physical slot bookkeeping adapted from Cycle25/Numerator/Scalar;
weighted PR6 predecessor 2fd60c0926b66ea18d7436f5ed55250fd006ab5d.
-/
                                    

noncomputable section
open scoped Classical BigOperators
namespace Cycle61.Numerator.Scalar
open Cycle61.Arithmetic Cycle61.Arithmetic.Bernstein

theorem error_main_source_scale {K : ℕ} (J : Finset (Fin K))
    (Y : Fin K→ℝ) (r : ℝ) :
    (∏j:J,(Y j.val)^r)*(∏j:{i:Fin K//i∉J},(Y j.val)^r)=∏j,(Y j)^r := by
  convert Fintype.prod_subtype_mul_prod_subtype (fun j=>j∈J) (fun j=>(Y j)^r) using 1
  congr 1
  apply Finset.prod_congr
  · ext i
    simp
  · intro i hi
    rfl

theorem error_main_source_power {K : ℕ} (J : Finset (Fin K))
    (Z : ℝ) (hZ : 0 < Z) (lengths : Fin K→ℝ) :
    (∏j:J,(Z^(lengths j.val))^(-(4/25:ℝ)))*
      Z^(-(4/25:ℝ)*(∑j:{i:Fin K//i∉J},lengths j.val)) =
      Z^(-(4/25:ℝ)*(∑j,lengths j)) := by
  have hm : (∏j:{i:Fin K//i∉J},(Z^(lengths j.val))^(-(4/25:ℝ))) =
      Z^(-(4/25:ℝ)*(∑j:{i:Fin K//i∉J},lengths j.val)) := by
    simp_rw [←Real.rpow_mul hZ.le]
    rw [←Real.rpow_sum_of_pos hZ]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _=>mul_comm _ _)
  have hp := error_main_source_scale J (fun j=>Z^(lengths j)) (-(4/25:ℝ))
  rw [hm] at hp
  rw [hp]
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_sum_of_pos hZ,←Finset.sum_mul]
  congr 1
  ring

/-- Error and main slots partition the original source widths. The selected
capacity C is in Z units; neither the row endpoint nor kappa is specialized. -/
theorem source_packet_multiplicative_identity {K : ℕ} (J : Finset (Fin K))
    (lengths : Fin K→ℝ) (hlengths : ∑j,lengths j=ell)
    (Z kap d C delta q A : ℝ) (L : LossData)
    (hZ : 0 < Z) (hd : d ≠ 0) (hdelta : delta ≠ 0) :
    ((Z^d)^L.scalar*(Z^d)^(-(17/50:ℝ))*Z^L.frequency*
      Z^(-(4/25:ℝ)*(∑j:{i:Fin K//i∉J},lengths j.val)))*
    (A*Z^L.front*((Z^d)^(y/d))^(-(1/2:ℝ))*
      (∏j:J,(Z^(lengths j.val))^(-(4/25:ℝ)))*
      (Z^d)^(L.mass+q*(ell/d)-q*(C/d)/2+
        (3*(countingR kap delta (q/delta)+L.count)+1+L.moment)/4+
        L.selection/2+delta*L.mesh/4+L.slack*(ell/d))) =
    A*Z^(numeratorExponent kap d C delta (q/delta)+weightedSourceLoss d delta L) := by
  have hsplit := error_main_source_power J Z hZ lengths
  rw [hlengths] at hsplit
  let E := L.mass+q*(ell/d)-q*(C/d)/2+
    (3*(countingR kap delta (q/delta)+L.count)+1+L.moment)/4+
    L.selection/2+delta*L.mesh/4+L.slack*(ell/d)
  calc
    _ = A*((Z^d)^L.scalar*(Z^d)^(-(17/50:ℝ))*Z^L.frequency*
        Z^(-(4/25:ℝ)*ell)*Z^L.front*((Z^d)^(y/d))^(-(1/2:ℝ))*(Z^d)^E) := by
      rw [←hsplit]
      dsimp only [E]
      ring
    _ = A*Z^(d*L.scalar+d*(-(17/50:ℝ))+L.frequency+(-(4/25))*ell+
        L.front+(d*(y/d))*(-(1/2:ℝ))+d*E) := by
      simp_rw [←Real.rpow_mul hZ.le]
      rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ,
        ←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
    _ = _ := by
      congr 2
      rw [←source_packet_exponent kap d C delta q L hd hdelta]
      dsimp only [E]
      field_simp
      ring

theorem source_kernel_multiplicative_identity (Z kap d C delta p e A : ℝ)
    (L : LossData) (hZ : 0 < Z) :
    A*Z^(numeratorExponent kap d C delta p+weightedSourceLoss d delta L)*
      (Z^x)^(1/2-17/50:ℝ)*Z^((1+delta)/2+16*e+17/50-1) =
    A*Z^(rowExponentAt kap d C delta p+Assembly.signalShift+16*e+weightedSourceLoss d delta L) := by
  rw [←Real.rpow_mul hZ.le,mul_assoc,←Real.rpow_add hZ,mul_assoc,←Real.rpow_add hZ]
  congr 2
  have hi := numerator_kernel_exponent kap d C delta p e
  unfold kernelExponent at hi
  linarith only [hi]

end Cycle61.Numerator.Scalar

end
/- END ORIGINAL Cycle61.Numerator.Scalar.SourcePacket -/

/- BEGIN ORIGINAL Cycle61.Numerator.Source.Ledger; sha256 9e0725dc0574916123bd4455b292ef196e1ac3ee62ac65cf16575b82f0843da7 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                            
                                              
                            

noncomputable section
namespace Cycle61.Numerator.Source
open Cycle61.Arithmetic Cycle61.Arithmetic.Bernstein Cycle61.Numerator.Scalar
open OAI.SevenEighths.Cycle61DetectorCount

def physicalLoss (D : BaselineData) (eps sigma affineError : ℝ) : LossData where
  front := 3*D.t
  frequency := (17/25)*D.t
  scalar := 2*eps
  mass := D.t
  count := sigma
  moment := D.t+affineError+D.t
  selection := 0
  mesh := Cycle25.sourceMesh D.t+4*D.t
  slack := D.t

lemma sourceMesh_le {t : ℝ} (ht : 0<t) : Cycle25.sourceMesh t ≤ t := by
  obtain ⟨_,_,ha,_,_,hm,_,hr,_,_⟩ :=
    OAI.SevenEighths.CenteredMomentEnergyWidthSchedule.bounds 2
      (OAI.SevenEighths.CenteredMomentEnergyWidthRanges.finalSourceCap 2 0 1 (t/4))
      (3/4) (t/4) (by norm_num)
      (OAI.SevenEighths.CenteredMomentEnergyWidthRanges.sourceCap_nonneg 2 0 1 (by norm_num) (by norm_num) _)
      (by norm_num) (by positivity)
  change OAI.SevenEighths.CenteredMomentEnergyWidthSchedule.mesh 2
    (OAI.SevenEighths.CenteredMomentEnergyWidthRanges.finalSourceCap 2 0 1 (t/4)) (3/4) (t/4) ≤ t
  linarith

lemma physical_loss_bound (D : BaselineData) (eps sigma affineError d delta : ℝ)
    (heps : 0 ≤ eps) (hsigma : 0 ≤ sigma) (haff : 0 ≤ affineError)
    (hd : d ≤ 1) (hdelta : 0 ≤ delta ∧ delta ≤ 3/4) :
    weightedSourceLoss d delta (physicalLoss D eps sigma affineError) ≤
      2*eps+3*sigma/4+affineError/4+7*D.t := by
  have hm := (Cycle25.sourceMesh_pos D.t_pos).le
  have ht := D.t_pos.le
  have hl := weightedSourceLoss_le_uniform (physicalLoss D eps sigma affineError) hd hdelta
    (by dsimp [physicalLoss];positivity) ht hsigma (by dsimp [physicalLoss];positivity)
    (by simp [physicalLoss]) (by dsimp [physicalLoss];positivity)
  have hmesh := sourceMesh_le D.t_pos
  have hell : ell ≤ (1/5:ℝ) := by norm_num [ell]
  have hte := mul_le_mul_of_nonneg_left hell ht
  dsimp [uniformSourceLoss,physicalLoss] at hl
  dsimp only [physicalLoss]
  linarith

lemma physical_packet_certificate (D : BaselineData) (eps sigma affineError d a q : ℝ)
    (hgap : theta < OAI.SevenEighths.HeckeZeroSupremum.beta)
    (hbeta : OAI.SevenEighths.HeckeZeroSupremum.beta ≤ 7/8)
    (hk : D.momentKappa=2*OAI.SevenEighths.HeckeZeroSupremum.beta-1)
    (heps : 0 ≤ eps) (hsigma : 0 ≤ sigma) (haff : 0 ≤ affineError)
    (hbudget : 16*D.e+2*eps+3*sigma/4+affineError/4+8*D.t ≤
      (OAI.SevenEighths.HeckeZeroSupremum.beta-theta)/4)
    (hd : dMinus ≤ d ∧ d ≤ dPlus) (ha : 51/100 ≤ a) (hatop : a ≤ 7/8)
    (hq : 0 ≤ q ∧ q ≤ (2*a-1)/2) :
    numeratorExponent D.momentKappa d (newCapacity d) (2*a-1) (q/(2*a-1))+
      weightedSourceLoss d (2*a-1) (physicalLoss D eps sigma affineError) ≤
      Assembly.signal OAI.SevenEighths.HeckeZeroSupremum.beta-4999/5000000000-
        (OAI.SevenEighths.HeckeZeroSupremum.beta-theta)/2-D.t-kernelExponent a D.e := by
  have hdelta : 0 < 2*a-1 := by linarith
  have hdel : 0 ≤ 2*a-1 ∧ 2*a-1 ≤ 3/4 := by constructor <;> linarith
  have hp : q/(2*a-1) ∈ Set.Icc 0 (1/2) :=
    ⟨div_nonneg hq.1 hdelta.le,(div_le_iff₀ hdelta).mpr (by linarith [hq.2])⟩
  have hd1 : d ≤ 1 := hd.2.trans (by norm_num [dPlus,h])
  have hl := physical_loss_bound D eps sigma affineError d (2*a-1) heps hsigma haff hd1 hdel
  have hh := new_packet_certificate (physicalLoss D eps sigma affineError) hgap hbeta hd hdel hp
    (by linarith : 16*D.e+weightedSourceLoss d (2*a-1) (physicalLoss D eps sigma affineError)+D.t ≤
      (OAI.SevenEighths.HeckeZeroSupremum.beta-theta)/4)
  rw [←hk,show (1+(2*a-1))/2=a by ring] at hh
  linarith
lemma old_physical_packet_certificate (D : BaselineData) (eps sigma d a q : ℝ)
    (hgap : theta < OAI.SevenEighths.HeckeZeroSupremum.beta)
    (hbeta : OAI.SevenEighths.HeckeZeroSupremum.beta ≤ 7/8)
    (hk : D.momentKappa=2*OAI.SevenEighths.HeckeZeroSupremum.beta-1)
    (heps : 0 ≤ eps) (hsigma : 0 ≤ sigma) 
    (hbudget : 16*D.e+2*eps+3*sigma/4+8*D.t ≤
      (OAI.SevenEighths.HeckeZeroSupremum.beta-theta)/4)
    (hd : d0 ≤ d ∧ d ≤ dMinus) (ha : 51/100 ≤ a) (hatop : a ≤ 7/8)
    (hq : 0 ≤ q ∧ q ≤ (2*a-1)/2) :
    numeratorExponent D.momentKappa d (oldCapacityAt D.momentKappa d) (2*a-1) (q/(2*a-1))+
      weightedSourceLoss d (2*a-1) (physicalLoss D eps sigma 0) ≤
      Assembly.signal OAI.SevenEighths.HeckeZeroSupremum.beta-4999/5000000000-
        (OAI.SevenEighths.HeckeZeroSupremum.beta-theta)/2-D.t-kernelExponent a D.e := by
  have hdelta : 0 < 2*a-1 := by linarith
  have hdel : 0 ≤ 2*a-1 ∧ 2*a-1 ≤ 3/4 := by constructor <;> linarith
  have hp : q/(2*a-1) ∈ Set.Icc 0 (1/2) :=
    ⟨div_nonneg hq.1 hdelta.le,(div_le_iff₀ hdelta).mpr (by linarith [hq.2])⟩
  have hd1 : d ≤ 1 := hd.2.trans (by norm_num [dMinus,h])
  have hl := physical_loss_bound D eps sigma 0 d (2*a-1) heps hsigma (by norm_num) hd1 hdel
  have hh := old_packet_certificate (physicalLoss D eps sigma 0) hgap hbeta hd hdel hp
    (by linarith : 16*D.e+weightedSourceLoss d (2*a-1) (physicalLoss D eps sigma 0)+D.t ≤
      (OAI.SevenEighths.HeckeZeroSupremum.beta-theta)/4)
  rw [←hk,show (1+(2*a-1))/2=a by ring] at hh
  linarith
end Cycle61.Numerator.Source

end
/- END ORIGINAL Cycle61.Numerator.Source.Ledger -/

/- BEGIN ORIGINAL Cycle61.Numerator.Source.Mask; sha256 705ff3b317761d15c2c448799f5db6665be58b1fa1dd734b6585b402fc64141a -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                     
                                      
                                        
                                     

noncomputable section
set_option maxHeartbeats 2800000
open scoped Classical BigOperators ContDiff
open Filter
namespace Cycle61.Numerator.Source
open Cycle61.Arithmetic Cycle61.Arithmetic.Bernstein Cycle61.Numerator.Capacity Cycle61.Numerator.Fourth
open Cycle61.Numerator.Scalar
open Cycle25.Weighted.Numerator Cycle25.Numerator
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open Cycle61DetectorCount Cycle25DetectorRowCount HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

/-- A literal physical error-mask sum has the uniform pre-height certificate
exponent, with only the original full-class count and actual scalar as inputs. -/
theorem source_mask_amplitude_class (D:BaselineData)
    (hgap:theta < HeckeZeroSupremum.beta)
    (hbetatop : HeckeZeroSupremum.beta ≤ 7/8)
    (hkap : D.momentKappa=2*HeckeZeroSupremum.beta-1)
    (F:BaselineSourceData D) (hbeta:(51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (bPhi mesh affineError : ℝ) (haff : 0<affineError)
    (hsPhi : Function.support (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ → ℂ) ⊆ Set.Iic bPhi)
    (di : ℕ) (control : Finset (ℕ×ℕ)) (Ci : ℝ) (hCi : 0<Ci)
    (hinput : ∀ᶠU:ℝ in atTop,AffineAt F bPhi mesh affineError U di control Ci)
    (hfineAffine : ∀j,D.length j ≤  mesh/200)
    (eps sigma : ℝ) (heps : 0<eps) (hsigma : 0 ≤ sigma)
    (hbudget : 16*D.e+2*eps+3*sigma/4+affineError/4+8*D.t ≤ (HeckeZeroSupremum.beta-theta)/4)
    (hfine:∀j,D.length j ≤  Cycle25.sourceMesh D.t/200) (J:Finset (Fin D.N)) :
    ∃degree:ℕ,∃C:ℝ,0 < C ∧ ∀ᶠU:ℝ in atTop,
      1 < U ∧ ∀(Z d:ℝ),1 < Z  →  dMinus ≤ d  →  d ≤ dPlus  →  U=Z^d  → 
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
      ‖sourceMaskContribution F η rows' J Z x z (Z^Cycle61.Arithmetic.y)‖  ≤ 
        (C*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^((degree:ℝ)+2*eps)*
          Z^(Assembly.signal HeckeZeroSupremum.beta-4999/5000000000-(HeckeZeroSupremum.beta-theta)/2-D.t-kernelExponent a D.e) := by
  obtain ⟨degree,C,hC,hclass⟩ := source_packet_amplitude_class D F hbeta (by rw [hkap]) bPhi mesh affineError haff hsPhi di control Ci hCi hinput hfineAffine hfine J
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
  have hd0 : 0 < d := Cycle61.Physical.physical_d_pos hd
  have hδ : 0 < 2*a-1 := by linarith
  have hsub : rows' ⊆ rows := Finset.filter_subset _ _
  have hY : U^(Cycle61.Arithmetic.y/d)=Z^Cycle61.Arithmetic.y := by
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
    (Z^Cycle61.Arithmetic.y) (Real.rpow_pos_of_pos hZ0 _)
  have hlabel : (∑u∈rows',‖errorLabelNumerator F.S F.exclusions η u J (sourcePrimePool F Z)
      (fun s=>source_prime_pool_outside F Z s) (fun _=>F.W) (fun s=>Z^(D.length s)) x z F.W (Z^Cycle61.Arithmetic.y)*
      (∏s∈main,Q u s)‖)  ≤ 
    C*(K*C0*Z^(3*D.t))*(1+height)^degree*(U^(Cycle61.Arithmetic.y/d))^(-(1/2:ℝ))*(∏s:J,(Z^(D.length s.val))^(-(4/25:ℝ)))*
      U^(D.t+q*(Cycle61.Arithmetic.ell/d)-q*zeroCapacity d/2+
        (3*(countingR D.momentKappa (2*a-1) (q/(2*a-1))+sigma)+1+D.t+affineError+D.t)/4+
        (2*a-1)*Cycle25.sourceMesh D.t/4+(2*a-1)*(D.t+D.t)/2+D.t*(Cycle61.Arithmetic.ell/d)) := by
    convert hb using 1
    calc
      _ = ∑i:rows',‖errorLabelNumerator F.S F.exclusions η i.val J (sourcePrimePool F Z)
          (fun s=>source_prime_pool_outside F Z s) (fun _=>F.W) (fun s=>Z^(D.length s)) x z F.W (Z^Cycle61.Arithmetic.y)*
          (∏s∈main,Q i.val s)‖ := (Finset.sum_coe_sort rows' _).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [heq i.val i.property,hY]
  let A := Cs*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^(2*eps)*U^(2*eps)*
    U^(-(17/50:ℝ))*Z^((17/25)*D.t)
  have hA : 0 ≤ A := by dsimp only [A];positivity
  have hphysical := source_mask_physical_front F η rows' J Z hZ0 x z hz (Z^Cycle61.Arithmetic.y) hS A _ hA hscalar hlabel
  have hselection := source_class_main_selection D F hfine Z d 0 (2*a-1) hZ ⟨hd,hdmax⟩ (by norm_num) hδ.le z rows main bin hne
  have hq0 : 0 ≤ q := hselection.1
  have hqmax : q ≤ (2*a-1)/2 := hselection.2.1
  have he := Scalar.source_packet_multiplicative_identity J D.length D.slots_sum Z D.momentKappa d
    (newCapacity d) (2*a-1) q (C*K*C0*((1+height)^degree)) (physicalLoss D eps sigma affineError)
    hZ0 hd0.ne' hδ.ne'
  have hcapscale : newCapacity d/d=zeroCapacity d := by
    have hh:=scaled_zeroCapacity hd0.ne'
    unfold newCapacity
    apply (div_eq_iff hd0.ne').mpr
    nlinarith only [hh]
  rw [hcapscale] at he
  dsimp [physicalLoss] at he
  have hcollapse : A*Z^(-(4/25:ℝ)*(∑j:{i:Fin D.N//i ∉ J},D.length j.val))*
      (C*(K*C0*Z^(3*D.t))*(1+height)^degree*(U^(Cycle61.Arithmetic.y/d))^(-(1/2:ℝ))*(∏s:J,(Z^(D.length s.val))^(-(4/25:ℝ)))*
      U^(D.t+q*(Cycle61.Arithmetic.ell/d)-q*zeroCapacity d/2+
        (3*(countingR D.momentKappa (2*a-1) (q/(2*a-1))+sigma)+1+D.t+affineError+D.t)/4+
        (2*a-1)*Cycle25.sourceMesh D.t/4+(2*a-1)*(D.t+D.t)/2+D.t*(Cycle61.Arithmetic.ell/d))) =
      (C*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^(2*eps)*(1+height)^degree*
        Z^(numeratorExponent D.momentKappa d (newCapacity d) (2*a-1) (q/(2*a-1))+
          weightedSourceLoss d (2*a-1) (physicalLoss D eps sigma affineError)) := by
    dsimp only [A]
    rw [hUZ]
    calc
      _ = (Cs*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^(2*eps))*
          (((Z^d)^(2*eps)*(Z^d)^(-(17/50:ℝ))*Z^((17/25)*D.t)*
            Z^(-(4/25:ℝ)*(∑j:{i:Fin D.N//i ∉ J},D.length j.val)))*
          (C*(K*C0*Z^(3*D.t))*(1+height)^degree*((Z^d)^(Cycle61.Arithmetic.y/d))^(-(1/2:ℝ))*
            (∏s:J,(Z^(D.length s.val))^(-(4/25:ℝ)))*
            (Z^d)^(D.t+q*(Cycle61.Arithmetic.ell/d)-q*zeroCapacity d/2+
              (3*(countingR D.momentKappa (2*a-1) (q/(2*a-1))+sigma)+1+D.t+affineError+D.t)/4+
              (2*a-1)*Cycle25.sourceMesh D.t/4+(2*a-1)*(D.t+D.t)/2+D.t*(Cycle61.Arithmetic.ell/d)))) := by ring
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
  have hcert := physical_packet_certificate D eps sigma affineError d a q hgap hbetatop hkap heps.le hsigma haff.le hbudget ⟨hd,hdmax⟩ ha hatop ⟨hq0,hqmax⟩
  apply hphysical'.trans
  calc
    _  ≤  (C*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^(2*eps)*(3+height)^(degree:ℝ)*
        Z^(Assembly.signal HeckeZeroSupremum.beta-4999/5000000000-(HeckeZeroSupremum.beta-theta)/2-D.t-kernelExponent a D.e) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hheightpow (by positivity)
      · exact Real.rpow_le_rpow_of_exponent_le hZ.le hcert
      · positivity
      · positivity
    _ = _ := by rw [Real.rpow_add (by linarith : 0 < 3+height) (degree:ℝ) (2*eps)];ring


end Cycle61.Numerator.Source

end
/- END ORIGINAL Cycle61.Numerator.Source.Mask -/

/- BEGIN ORIGINAL Cycle61.Numerator.Source.Collect; sha256 841ff3272b92ba1a4ddd1183214f2f8dd771dc4ffe7e5bd3d07a7a5674984e7d -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                    
                                     

noncomputable section
set_option maxHeartbeats 2800000
open scoped Classical BigOperators ContDiff
open Filter
namespace Cycle61.Numerator.Source
open Cycle61.Arithmetic Cycle61.Arithmetic.Bernstein Cycle61.Numerator.Capacity Cycle61.Numerator.Fourth
open Cycle61.Numerator.Scalar
open Cycle25.Weighted.Numerator Cycle25.Numerator
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open Cycle61DetectorCount Cycle25DetectorRowCount HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

theorem source_integrated_amplitude_classes (D : BaselineData)
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
      1 < U ∧ ∀(Z d : ℝ),1 < Z  →  dMinus  ≤  d  →  d  ≤  dPlus  →  U=Z^d  → 
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
        (fun s=>source_prime_pool_outside F Z s) (fun _=>F.W) (fun s=>Z^(D.length s)) F.W (Z^Cycle61.Arithmetic.y) x z‖  ≤ 
        (C*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^Jw*
          Z^(Assembly.signal HeckeZeroSupremum.beta-4999/5000000000-(HeckeZeroSupremum.beta-theta)/2-D.t-kernelExponent a D.e) := by
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
    Z^(Assembly.signal HeckeZeroSupremum.beta-4999/5000000000-(HeckeZeroSupremum.beta-theta)/2-D.t-kernelExponent a D.e)
  let A : ℝ := common*Ctot*(3+height)^(Jw+2*eps)
  have hcommon : 0  ≤  common := by dsimp only [common];positivity
  have hA : 0  ≤  A := by dsimp only [A];positivity
  have hmaskBound (bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t)
      (hne : (classRows bin).Nonempty) (J : Finset (Fin D.N)) :
      ‖sourceMaskContribution F η (classRows bin) J Z x z (Z^Cycle61.Arithmetic.y)‖  ≤  A := by
    have hsub : classRows bin  ⊆  rows := Finset.filter_subset _ _
    have hh := (hall J).2 Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hH him
      rows hrows hrow (hdis J) hη hQ hS (fun j:J=>Pbase j.val) bin hne Cs K C0 hCs hK hC0
      (hcount J bin hne) (fun u hu=>hscalar u (hsub hu)) (fun u hu=>hupper u (hsub hu))
    have he := (hheight height eps hH heps.le).1 J
    calc
      _  ≤  (Cmask J*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
          (3+height)^((degree J:ℝ)+2*eps)*
          Z^(Assembly.signal HeckeZeroSupremum.beta-4999/5000000000-(HeckeZeroSupremum.beta-theta)/2-D.t-kernelExponent a D.e) := hh
      _ = common*(Cmask J*(3+height)^((degree J:ℝ)+2*eps)) := by dsimp only [common];ring
      _  ≤  common*(Ctot*(3+height)^(Jw+2*eps)) := mul_le_mul_of_nonneg_left he hcommon
      _ = A := by dsimp only [A];ring
  have hclass (bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t)
      (hne : (classRows bin).Nonempty) :
      ‖reconstructedDyadValue F.S F.exclusions F.maximal η (classRows bin) (sourcePrimePool F Z)
        (fun s=>source_prime_pool_outside F Z s) (fun _=>F.W) (fun s=>Z^(D.length s)) x z F.W (Z^Cycle61.Arithmetic.y)‖  ≤  maskFactor*A := by
    calc
      _ = ‖∑J∈Finset.univ.powerset,sourceMaskContribution F η (classRows bin) J Z x z (Z^Cycle61.Arithmetic.y)‖ :=
        congrArg norm (source_reconstructed_sum_masks F η (classRows bin) Z x z (Z^Cycle61.Arithmetic.y))
      _  ≤  ∑J∈Finset.univ.powerset,A := by
        apply (norm_sum_le _ _).trans
        exact Finset.sum_le_sum (fun J _=>hmaskBound bin hne J)
      _ = maskFactor*A := by
        simp only [Finset.sum_const,Finset.card_powerset,Finset.card_univ,Fintype.card_fin,
          nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
        rfl
  have hr := reconstructedDyadValue_class_uniform F.S F.exclusions F.maximal η rows
    (sourcePrimePool F Z) (fun s=>source_prime_pool_outside F Z s) (fun _=>F.W) (fun s=>Z^(D.length s))
    x z F.W (Z^Cycle61.Arithmetic.y) Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (by linarith)
    (fun s=>D.length s/d) Q (maskFactor*A) (mul_nonneg hmf.le hA) hclass
  have heq := integratedDyadValue_reconstruction F.S F.exclusions F.maximal (4*D.e) F.first η rows hrow
    (sourcePrimePool F Z) (fun s=>source_prime_pool_outside F Z s) hdis hdisAll hη hQ
    (fun _=>F.W) (fun s=>Z^(D.length s)) x z (by rw [hx];linarith [D.e_pos]) hz.ge
    (by rw [hx];linarith [D.e_pos]) F.W 1 2 (by norm_num) F.complex_support (Z^Cycle61.Arithmetic.y)
    (Real.rpow_pos_of_pos hZ0 _)
  rw [heq,norm_mul]
  have hpi : ‖(2*Real.pi:ℂ)‖=2*Real.pi := by
    rw [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  rw [hpi]
  apply (mul_le_mul_of_nonneg_left hr (by positivity : 0  ≤  2*Real.pi)).trans_eq
  simp only [Finset.card_univ,Fintype.card_fin]
  dsimp only [classFactor,maskFactor,A,common]
  ring


end Cycle61.Numerator.Source

end
/- END ORIGINAL Cycle61.Numerator.Source.Collect -/
