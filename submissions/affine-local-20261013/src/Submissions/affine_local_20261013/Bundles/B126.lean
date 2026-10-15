/-
Affine local-capacity adaptation for Kari Roegnvaldsson, with AI assistance.
Based on nielstron local44-20261013 at tracker revision 2c3df3b.
Status: candidate under verification; no admission is claimed here.
All inherited attribution and Apache-2.0 notices are retained below.
Section hashes identify original, pre-adaptation module snapshots.
-/
/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B003
import Submissions.affine_local_20261013.Bundles.B040
import Submissions.affine_local_20261013.Bundles.B041
import Submissions.affine_local_20261013.Bundles.B045
import Submissions.affine_local_20261013.Bundles.B072
import Submissions.affine_local_20261013.Bundles.B078
import Submissions.affine_local_20261013.Bundles.B080
import Submissions.affine_local_20261013.Bundles.B124
import Submissions.affine_local_20261013.Bundles.B125

/- BEGIN ORIGINAL MODULE Global.Numerator.LocalSourceMask ; sha256 120cbe8ad6b9e3332bb2860db52769403b66b58e810281decfd006364bab355f -/
section






/-! Actual physical mask contributions on the original full amplitude classes.
The certified moment is already discharged by SourceClass. Count and calibrated
scalar bounds are kept explicit so the same source constants apply to every mask. -/
noncomputable section
set_option maxHeartbeats 2800000
open scoped Classical BigOperators ContDiff
open Filter
namespace Submission20261012.Global.Numerator
open Cycle25.Weighted Cycle25.Weighted.Numerator Scalar
open Cycle25.Numerator
open _root_.Local44.Physical OAI.SevenEighths.Local44.Physical
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open Cycle25DetectorRowCount HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

/-- A literal physical error-mask sum has the uniform pre-height certificate
exponent, with only the original full-class count and actual scalar as inputs. -/
theorem source_mask_amplitude_class_local (D:HighParameters.HighData (HeckeZeroSupremum.beta-theta))
    (hgap:theta < HeckeZeroSupremum.beta)
    (F:WeightedSourceData D.toMomentData) (hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hbetaTop:HeckeZeroSupremum.beta≤7/8)
    (hfine:∀j,D.ell j≤ transportMomentMesh D.t/200) (J:Finset (Fin D.N)) :
    ∃degree:ℕ,∃C:ℝ,0 < C ∧ ∀ᶠU:ℝ in atTop,
      1 < U ∧ ∀(Z d:ℝ),1 < Z → (1/2:ℝ)≤ d → Endpoint.junction≤ d → d≤ h+3*D.t → U=Z^d →
      ∀(η:Character) (x z:ℂ) (a height:ℝ),(51/100:ℝ)≤ a → a≤7/8 → 1/3≤2*a-1 →
      x.re=a+16*D.e → z.re=17/50 → 0≤ height → |z.im|≤ height →
      ∀rows:Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ)≤ rowNorm u ∧ rowNorm u≤ U) →
      (∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue≠1) →
      (∀P:∀i:J,sourcePrimePool F Z i.val,Function.Injective (fun i=>(P i).val)) →
      (∀i P,P∈sourcePrimePool F Z i→IsCoprime P.val η.modulus) →
      (∀i P,P∈sourcePrimePool F Z i→(4:ℝ)≤ P.val.absNorm) →
      (∀i,∀P∈F.S,(P.absNorm:ℝ)≤ Z^(D.ell i)) →
      (∀i:J,sourcePrimePool F Z i.val) →
      ∀bin:BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t,
      let Q := fun (u:FreeRow) s=> HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell s)) z
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=> D.ell s/d) Q bin
      let main := (Finset.univ:Finset (Fin D.N)) \ J
      let q := weightedMean Finset.univ (fun s=> D.ell s/d)
        (maskedGain main (binValue Finset.univ ((2*a-1)/2) D.t bin))
      rows'.Nonempty → ∀Cs K C0:ℝ,0≤ Cs → 1≤ K → 1≤ C0 →
      (rows'.card:ℝ)≤ K*C0*Z^(3*D.t)*U^(rowCount (2*a-1) (q/(2*a-1)) D.momentKappa+159*D.ε+9*D.t) →
      (∀u∈rows',‖frequencyWeight z ⟨u.val,u.property.1⟩*numeratorFreeRowScalar F.S F.exclusions F.maximal η u x z‖≤
        Cs*(η.modulus.absNorm:ℝ)^(2*D.eps)*(3+height)^(2*D.eps)*U^(2*D.eps)*U^(-(17/50:ℝ))*Z^((17/25)*D.t)) →
      (∀u∈rows',∀s,‖Q u s‖≤(Z^(D.ell s))^
        (HeckePrimeAmplitudeBins.amplitude (Z^(D.ell s)) ((2*a-1)/2) D.t (Q u s)+D.t)) →
      ‖sourceMaskContribution F η rows' J Z x z (Z^ly)‖ ≤
        (C*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*D.eps)*(3+height)^((degree:ℝ)+2*D.eps)*
          Z^(weightedTarget-Scalar.weightedSourceSZExponent a D.e-D.t) := by
  obtain ⟨degree,C,hC,hclass⟩ := source_packet_amplitude_class_local D F hbeta hbetaTop hfine J
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [hclass] with U hclass
  refine ⟨hclass.1,?_⟩
  intro Z d hZ hd hdlocal hdmax hUZ η x z a height ha hatop hδlow hx hz hheight hzim rows hrows hrow hdis hη hQ hS Pbase bin
  dsimp only
  let Q := fun (u:FreeRow) s=> HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell s)) z
  let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=> D.ell s/d) Q bin
  let main := (Finset.univ:Finset (Fin D.N)) \ J
  let q := weightedMean Finset.univ (fun s=> D.ell s/d)
    (maskedGain main (binValue Finset.univ ((2*a-1)/2) D.t bin))
  intro hne Cs K C0 hCs hK hC0 hcard hscalar hupper
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hU0 : 0 < U := zero_lt_one.trans hclass.1
  have hd0 : 0 < d := by linarith
  have hδ : 0 < 2*a-1 := by linarith
  have hsub : rows'⊆rows := Finset.filter_subset _ _
  have hY : U^(ly/d)=Z^ly := by
    rw [hUZ,←Real.rpow_mul hZ0.le,mul_div_cancel₀ _ hd0.ne']
  have hcount1 : 1≤ K*C0*Z^(3*D.t) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hK hC0)
      (Real.one_le_rpow hZ.le (by have := D.t_pos;positivity))
  have hdwide : d ≤ h+rowExtension := hdmax.trans (by linarith [D.weighted_top])
  have hb := hclass.2 Z d hZ hd hdlocal hdwide hUZ η x z a height ha hatop hx hz hheight hzim rows hrows hrow
    hdis hη Pbase bin hne (rowCount (2*a-1) (q/(2*a-1)) D.momentKappa+159*D.ε+9*D.t)
    (K*C0*Z^(3*D.t)) hcount1 hcard hupper
  have heq (u:FreeRow) (hu:u∈rows') := errorLabelNumerator_eq_packet F.S F.exclusions (4*D.e) F.first η u
    (hrow u (hsub hu)) J (sourcePrimePool F Z) (fun s=> source_prime_pool_outside F Z s) hdis hη hQ
    (fun _=> F.W) (fun s=> Z^(D.ell s)) x z (by rw [hx];linarith [D.e_pos]) hz.ge
    (by rw [hx];linarith [D.e_pos]) F.W 1 2 (by norm_num) F.complex_support (F.W.smooth ⊤)
    (Z^ly) (Real.rpow_pos_of_pos hZ0 _)
  have hlabel : (∑u∈rows',‖errorLabelNumerator F.S F.exclusions η u J (sourcePrimePool F Z)
      (fun s=> source_prime_pool_outside F Z s) (fun _=> F.W) (fun s=> Z^(D.ell s)) x z F.W (Z^ly)*
      (∏s∈main,Q u s)‖) ≤
    C*(K*C0*Z^(3*D.t))*(1+height)^degree*(U^(ly/d))^(-(1/2:ℝ))*(∏s:J,(Z^(D.ell s.val))^(-(4/25:ℝ)))*
      U^(D.t+q*(ell/d)-q*(baseCapacity (1-ly/d))/2+
        (3*(rowCount (2*a-1) (q/(2*a-1)) D.momentKappa+159*D.ε+9*D.t)+1+2*D.t)/4+
        (2*a-1)*transportMomentMesh D.t/4+(2*a-1)*D.t+D.t*(ell/d)) := by
    convert hb using 1
    calc
      _ = ∑i:rows',‖errorLabelNumerator F.S F.exclusions η i.val J (sourcePrimePool F Z)
          (fun s=> source_prime_pool_outside F Z s) (fun _=> F.W) (fun s=> Z^(D.ell s)) x z F.W (Z^ly)*
          (∏s∈main,Q i.val s)‖ := (Finset.sum_coe_sort rows' _).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [heq i.val i.property,hY]
  let A := Cs*(η.modulus.absNorm:ℝ)^(2*D.eps)*(3+height)^(2*D.eps)*U^(2*D.eps)*
    U^(-(17/50:ℝ))*Z^((17/25)*D.t)
  have hA : 0≤ A := by dsimp only [A];positivity
  have hphysical := source_mask_physical_front F η rows' J Z hZ0 x z hz (Z^ly) hS A _ hA hscalar hlabel
  have hselection := source_class_main_transport_selection D F hfine Z d 0 (2*a-1) hZ hd (by norm_num) hδ.le (local_source_bare_window d hdlocal hdwide) z rows main bin hne
  have hq0 : 0≤ q := hselection.1
  have hqmax : q≤(2*a-1)/2 := hselection.2.1
  have he := local_source_packet_multiplicative_identity J D.ell D.slots_sum Z D.momentKappa d (2*a-1) q D.ε D.eps D.t
    (transportMomentMesh D.t) C K C0 ((1+height)^degree) hZ0 (by linarith [D.momentKappa_lo]) hd0.ne' hδ.ne'
  have hcollapse : A*Z^(-(4/25:ℝ)*(∑j:{i:Fin D.N//i∉J},D.ell j.val))*
      (C*(K*C0*Z^(3*D.t))*(1+height)^degree*(U^(ly/d))^(-(1/2:ℝ))*(∏s:J,(Z^(D.ell s.val))^(-(4/25:ℝ)))*
      U^(D.t+q*(ell/d)-q*(baseCapacity (1-ly/d))/2+
        (3*(rowCount (2*a-1) (q/(2*a-1)) D.momentKappa+159*D.ε+9*D.t)+1+2*D.t)/4+
        (2*a-1)*transportMomentMesh D.t/4+(2*a-1)*D.t+D.t*(ell/d))) =
      (C*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*D.eps)*(3+height)^(2*D.eps)*(1+height)^degree*
        Z^(localNumeratorExponent D.momentKappa d (2*a-1) (q/(2*a-1))+
          localSourceLoss d (2*a-1) D.ε D.eps D.t (transportMomentMesh D.t)) := by
    dsimp only [A]
    rw [hUZ]
    calc
      _ = (Cs*(η.modulus.absNorm:ℝ)^(2*D.eps)*(3+height)^(2*D.eps))*
          (((Z^d)^(2*D.eps)*(Z^d)^(-(17/50:ℝ))*Z^((17/25)*D.t)*
            Z^(-(4/25:ℝ)*(∑j:{i:Fin D.N//i∉J},D.ell j.val)))*
          (C*(K*C0*Z^(3*D.t))*(1+height)^degree*((Z^d)^(ly/d))^(-(1/2:ℝ))*
            (∏s:J,(Z^(D.ell s.val))^(-(4/25:ℝ)))*
            (Z^d)^(D.t+q*(ell/d)-q*(baseCapacity (1-ly/d))/2+
              (3*(rowCount (2*a-1) (q/(2*a-1)) D.momentKappa+159*D.ε+9*D.t)+1+2*D.t)/4+
              (2*a-1)*transportMomentMesh D.t/4+(2*a-1)*D.t+D.t*(ell/d)))) := by ring
      _ = _ := by rw [he];ring
  have hphysical' := hphysical.trans_eq hcollapse
  have hheightpow : (1+height)^degree ≤ (3+height)^(degree:ℝ) := by
    rw [Real.rpow_natCast]
    exact pow_le_pow_left₀ (by linarith) (by linarith) _
  have hcert := source_packet_certificate D hgap d a q hd hdmax hδlow hatop hq0 hqmax
  simp only [piecewiseNumeratorExponent,piecewiseSourceLoss,if_pos hdlocal] at hcert
  apply hphysical'.trans
  calc
    _ ≤ (C*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*D.eps)*(3+height)^(2*D.eps)*(3+height)^(degree:ℝ)*
        Z^(weightedTarget-Scalar.weightedSourceSZExponent a D.e-D.t) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hheightpow (by positivity)
      · exact Real.rpow_le_rpow_of_exponent_le hZ.le hcert
      · positivity
      · positivity
    _ = _ := by rw [Real.rpow_add (by linarith : 0 < 3+height) (degree:ℝ) (2*D.eps)];ring

end Submission20261012.Global.Numerator
end

/- Adapted from weighted-numerator PR6, 2fd60c0926b66ea18d7436f5ed55250fd006ab5d; Apache-2.0. Uses the Cycle25 gap-dependent certificate. -/
end
/- END ORIGINAL MODULE Global.Numerator.LocalSourceMask -/

/- BEGIN ORIGINAL MODULE Global.Numerator.SourceMask ; sha256 cbf1d59db02fd21bba395b325bb0aabbc43c7e334f1963cc2532cc4e7f293a58 -/
section







/-! Actual physical mask contributions on the original full amplitude classes.
The certified moment is already discharged by SourceClass. Count and calibrated
scalar bounds are kept explicit so the same source constants apply to every mask. -/
noncomputable section
set_option maxHeartbeats 2800000
open scoped Classical BigOperators ContDiff
open Filter
namespace Submission20261012.Global.Numerator
open Cycle25.Weighted Cycle25.Weighted.Numerator Scalar
open Cycle25.Numerator
open Cycle25 (sourceMesh)
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open Cycle25DetectorRowCount HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

/-- A literal physical error-mask sum has the uniform pre-height certificate
exponent, with only the original full-class count and actual scalar as inputs. -/
theorem source_mask_amplitude_class (D:HighParameters.HighData (HeckeZeroSupremum.beta-theta))
    (hgap:theta < HeckeZeroSupremum.beta)
    (F:WeightedSourceData D.toMomentData) (hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hbetaTop:HeckeZeroSupremum.beta≤7/8)
    (hfine:∀j,D.ell j≤ OAI.SevenEighths.Local44.Physical.transportMomentMesh D.t/200) (J:Finset (Fin D.N)) :
    ∃degree:ℕ,∃C:ℝ,0 < C ∧ ∀ᶠU:ℝ in atTop,
      1 < U ∧ ∀(Z d:ℝ),1 < Z → (1/2:ℝ)≤ d → d≤ h+3*D.t → U=Z^d →
      ∀(η:Character) (x z:ℂ) (a height:ℝ),(51/100:ℝ)≤ a → a≤7/8 → 1/3≤2*a-1 →
      x.re=a+16*D.e → z.re=17/50 → 0≤ height → |z.im|≤ height →
      ∀rows:Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ)≤ rowNorm u ∧ rowNorm u≤ U) →
      (∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue≠1) →
      (∀P:∀i:J,sourcePrimePool F Z i.val,Function.Injective (fun i=>(P i).val)) →
      (∀i P,P∈sourcePrimePool F Z i→IsCoprime P.val η.modulus) →
      (∀i P,P∈sourcePrimePool F Z i→(4:ℝ)≤ P.val.absNorm) →
      (∀i,∀P∈F.S,(P.absNorm:ℝ)≤ Z^(D.ell i)) →
      (∀i:J,sourcePrimePool F Z i.val) →
      ∀bin:BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t,
      let Q := fun (u:FreeRow) s=> HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell s)) z
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=> D.ell s/d) Q bin
      let main := (Finset.univ:Finset (Fin D.N)) \ J
      let q := weightedMean Finset.univ (fun s=> D.ell s/d)
        (maskedGain main (binValue Finset.univ ((2*a-1)/2) D.t bin))
      rows'.Nonempty → ∀Cs K C0:ℝ,0≤ Cs → 1≤ K → 1≤ C0 →
      (rows'.card:ℝ)≤ K*C0*Z^(3*D.t)*U^(rowCount (2*a-1) (q/(2*a-1)) D.momentKappa+159*D.ε+9*D.t) →
      (∀u∈rows',‖frequencyWeight z ⟨u.val,u.property.1⟩*numeratorFreeRowScalar F.S F.exclusions F.maximal η u x z‖≤
        Cs*(η.modulus.absNorm:ℝ)^(2*D.eps)*(3+height)^(2*D.eps)*U^(2*D.eps)*U^(-(17/50:ℝ))*Z^((17/25)*D.t)) →
      (∀u∈rows',∀s,‖Q u s‖≤(Z^(D.ell s))^
        (HeckePrimeAmplitudeBins.amplitude (Z^(D.ell s)) ((2*a-1)/2) D.t (Q u s)+D.t)) →
      ‖sourceMaskContribution F η rows' J Z x z (Z^ly)‖ ≤
        (C*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*D.eps)*(3+height)^((degree:ℝ)+2*D.eps)*
          Z^(weightedTarget-Scalar.weightedSourceSZExponent a D.e-D.t) := by
  have hfineOld : ∀j,D.ell j≤ _root_.Cycle25.sourceMesh D.t/200 := fun j=>(hfine j).trans
    (div_le_div_of_nonneg_right (OAI.SevenEighths.Local44.Physical.transportMomentMesh_le_old D.t) (by norm_num))
  obtain ⟨no,Co,hCo,ho⟩ := source_mask_amplitude_class_old D hgap F hbeta hfineOld J
  obtain ⟨nl,Cl,hCl,hl⟩ := source_mask_amplitude_class_local D hgap F hbeta hbetaTop hfine J
  refine ⟨max no nl,Co+Cl,by linarith,?_⟩
  filter_upwards [ho,hl] with U ho hl
  refine ⟨ho.1,?_⟩
  intro Z d hZ hd hdmax hUZ η x z a height ha hatop hδlow hx hz hheight hzim rows hrows hrow hdis hη hQ hS Pbase bin
  dsimp only
  intro hne Cs K C0 hCs hK hC0 hcard hscalar hupper
  have hbound (C' : ℝ) (n' : ℕ) (hC' : 0≤ C') (hCC : C'≤ Co+Cl) (hn' : n'≤ max no nl) :
      (C'*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*D.eps)*(3+height)^((n':ℝ)+2*D.eps)*
        Z^(weightedTarget-Scalar.weightedSourceSZExponent a D.e-D.t) ≤
      ((Co+Cl)*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*D.eps)*(3+height)^((max no nl:ℕ)+2*D.eps)*
        Z^(weightedTarget-Scalar.weightedSourceSZExponent a D.e-D.t) := by
    have he : (n':ℝ)+2*D.eps≤((max no nl:ℕ):ℝ)+2*D.eps := by
      have hh : (n':ℝ)≤((max no nl:ℕ):ℝ) := by exact_mod_cast hn'
      linarith
    have hp := Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ)≤3+height) he
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
    exact mul_le_mul (by gcongr) hp (Real.rpow_nonneg (by linarith) _) (by positivity)
  by_cases hj : Endpoint.junction≤ d
  · exact (hl.2 Z d hZ hd hj hdmax hUZ η x z a height ha hatop hδlow hx hz hheight hzim
      rows hrows hrow hdis hη hQ hS Pbase bin hne Cs K C0 hCs hK hC0 hcard hscalar hupper).trans
      (hbound Cl nl hCl.le (by linarith) (le_max_right _ _))
  · exact (ho.2 Z d hZ hd (lt_of_not_ge hj) hdmax hUZ η x z a height ha hatop hδlow hx hz hheight hzim
      rows hrows hrow hdis hη hQ hS Pbase bin hne Cs K C0 hCs hK hC0 hcard hscalar hupper).trans
      (hbound Co no hCo.le (by linarith) (le_max_left _ _))

end Submission20261012.Global.Numerator
end
#print axioms Submission20261012.Global.Numerator.source_mask_amplitude_class
end
/- END ORIGINAL MODULE Global.Numerator.SourceMask -/

/- BEGIN ORIGINAL MODULE Global.Numerator.SourceCollect ; sha256 cd2c024912ef73c34421f5b1c39033848c45a147963d3d784bf39ec98064b300 -/
section



/-! Finite collection of the actual physical error masks and the original full
amplitude classes. One degree and one positive constant precede U and all target,
height and contour choices. No analytic estimate is introduced in this step. -/
noncomputable section
set_option maxHeartbeats 2500000
open scoped Classical BigOperators ContDiff
open Filter
namespace Submission20261012.Global.Numerator
open Cycle25.Weighted Cycle25.Weighted.Numerator Scalar
open Cycle25.Numerator
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open Cycle25DetectorRowCount HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

theorem source_integrated_amplitude_classes (D : HighParameters.HighData (HeckeZeroSupremum.beta-theta))
    (hgap : theta < HeckeZeroSupremum.beta)
    (F : WeightedSourceData D.toMomentData) (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hbetaTop : HeckeZeroSupremum.beta≤7/8)
    (hfine : ∀j,D.ell j ≤ OAI.SevenEighths.Local44.Physical.transportMomentMesh D.t/200) :
    ∃Jw : ℝ,0 ≤ Jw ∧ ∃C : ℝ,0 < C ∧ ∀ᶠU : ℝ in atTop,
      1 < U ∧ ∀(Z d : ℝ),1 < Z → (1/2:ℝ) ≤ d → d ≤ h+3*D.t → U=Z^d →
      ∀(η : Character) (x z : ℂ) (a height : ℝ),(51/100:ℝ) ≤ a → a ≤ 7/8 → 1/3 ≤ 2*a-1 →
      x.re=a+16*D.e → z.re=17/50 → 0 ≤ height → |z.im| ≤ height →
      ∀rows : Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      (∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue≠1) →
      (∀J : Finset (Fin D.N),∀P : ∀i:J,sourcePrimePool F Z i.val,
        Function.Injective (fun i=>(P i).val)) →
      (∀P : ∀i,sourcePrimePool F Z i,Function.Injective (fun i=>(P i).val)) →
      (∀i P,P∈sourcePrimePool F Z i → IsCoprime P.val η.modulus) →
      (∀i P,P∈sourcePrimePool F Z i → (4:ℝ) ≤ P.val.absNorm) →
      (∀i,∀P∈F.S,(P.absNorm:ℝ) ≤ Z^(D.ell i)) →
      (∀i,sourcePrimePool F Z i) →
      ∀Cs K C0 : ℝ,0 ≤ Cs → 1 ≤ K → 1 ≤ C0 →
      let Q := fun (u : FreeRow) s=> HeckePrimeRow.canonicalPrimeAmplitude
        F.modulus ⊤ u.val F.W 2 (Z^(D.ell s)) z
      (∀J : Finset (Fin D.N),∀bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t,
        let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=> D.ell s/d) Q bin
        let q := weightedMean Finset.univ (fun s=> D.ell s/d)
          (maskedGain (Finset.univ\J) (binValue Finset.univ ((2*a-1)/2) D.t bin))
        rows'.Nonempty → (rows'.card:ℝ) ≤ K*C0*Z^(3*D.t)*
          U^(rowCount (2*a-1) (q/(2*a-1)) D.momentKappa+159*D.ε+9*D.t)) →
      (∀u∈rows,‖frequencyWeight z ⟨u.val,u.property.1⟩*
        numeratorFreeRowScalar F.S F.exclusions F.maximal η u x z‖ ≤
        Cs*(η.modulus.absNorm:ℝ)^(2*D.eps)*(3+height)^(2*D.eps)*
          U^(2*D.eps)*U^(-(17/50:ℝ))*Z^((17/25)*D.t)) →
      (∀u∈rows,∀s,‖Q u s‖ ≤ (Z^(D.ell s))^
        (HeckePrimeAmplitudeBins.amplitude (Z^(D.ell s)) ((2*a-1)/2) D.t (Q u s)+D.t)) →
      ‖FullWContour.integratedDyadValue F.S F.exclusions F.maximal η rows (sourcePrimePool F Z)
        (fun s=> source_prime_pool_outside F Z s) (fun _=> F.W) (fun s=> Z^(D.ell s)) F.W (Z^ly) x z‖ ≤
        (C*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*D.eps)*(3+height)^Jw*
          Z^(weightedTarget-Scalar.weightedSourceSZExponent a D.e-D.t) := by
  choose degree Cmask hCmask hmask using (fun J : Finset (Fin D.N)=> source_mask_amplitude_class D hgap F hbeta hbetaTop hfine J)
  obtain ⟨Jw,hJw,Ctot,hCtot,hcoeff,hheight⟩ := finite_height_envelope degree Cmask hCmask
  let classFactor : ℝ := (HeckeDetectorClassBudget.alphabetBound D.t:ℝ)^D.N
  let maskFactor : ℝ := (2:ℝ)^D.N
  have hcf : 0 < classFactor := by
    unfold classFactor HeckeDetectorClassBudget.alphabetBound
    positivity
  have hmf : 0 < maskFactor := by dsimp only [maskFactor];positivity
  refine ⟨Jw+2*D.eps,by linarith [D.eps_pos],(2*Real.pi)*classFactor*maskFactor*Ctot,
    by positivity,?_⟩
  filter_upwards [Filter.eventually_all.mpr hmask] with U hall
  refine ⟨(hall ∅).1,?_⟩
  intro Z d hZ hd hdmax hUZ η x z a height ha hatop hδ hx hz hH him rows hrows hrow
    hdis hdisAll hη hQ hS Pbase Cs K C0 hCs hK hC0
  dsimp only
  let Q := fun (u : FreeRow) s=> HeckePrimeRow.canonicalPrimeAmplitude
    F.modulus ⊤ u.val F.W 2 (Z^(D.ell s)) z
  let classRows := fun bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t=>
    amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=> D.ell s/d) Q bin
  intro hcount hscalar hupper
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  let common : ℝ := Cs*K*C0*(η.modulus.absNorm:ℝ)^(2*D.eps)*
    Z^(weightedTarget-Scalar.weightedSourceSZExponent a D.e-D.t)
  let A : ℝ := common*Ctot*(3+height)^(Jw+2*D.eps)
  have hcommon : 0 ≤ common := by dsimp only [common];positivity
  have hA : 0 ≤ A := by dsimp only [A];positivity
  have hmaskBound (bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t)
      (hne : (classRows bin).Nonempty) (J : Finset (Fin D.N)) :
      ‖sourceMaskContribution F η (classRows bin) J Z x z (Z^ly)‖ ≤ A := by
    have hsub : classRows bin ⊆ rows := Finset.filter_subset _ _
    have hh := (hall J).2 Z d hZ hd hdmax hUZ η x z a height ha hatop hδ hx hz hH him
      rows hrows hrow (hdis J) hη hQ hS (fun j:J=> Pbase j.val) bin hne Cs K C0 hCs hK hC0
      (hcount J bin hne) (fun u hu=> hscalar u (hsub hu)) (fun u hu=> hupper u (hsub hu))
    have he := (hheight height D.eps hH D.eps_pos.le).1 J
    calc
      _ ≤ (Cmask J*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*D.eps)*
          (3+height)^((degree J:ℝ)+2*D.eps)*
          Z^(weightedTarget-Scalar.weightedSourceSZExponent a D.e-D.t) := hh
      _ = common*(Cmask J*(3+height)^((degree J:ℝ)+2*D.eps)) := by dsimp only [common];ring
      _ ≤ common*(Ctot*(3+height)^(Jw+2*D.eps)) := mul_le_mul_of_nonneg_left he hcommon
      _ = A := by dsimp only [A];ring
  have hclass (bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t)
      (hne : (classRows bin).Nonempty) :
      ‖reconstructedDyadValue F.S F.exclusions F.maximal η (classRows bin) (sourcePrimePool F Z)
        (fun s=> source_prime_pool_outside F Z s) (fun _=> F.W) (fun s=> Z^(D.ell s)) x z F.W (Z^ly)‖ ≤ maskFactor*A := by
    calc
      _ = ‖∑J∈Finset.univ.powerset,sourceMaskContribution F η (classRows bin) J Z x z (Z^ly)‖ :=
        congrArg norm (source_reconstructed_sum_masks F η (classRows bin) Z x z (Z^ly))
      _ ≤ ∑J∈Finset.univ.powerset,A := by
        apply (norm_sum_le _ _).trans
        exact Finset.sum_le_sum (fun J _=> hmaskBound bin hne J)
      _ = maskFactor*A := by
        simp only [Finset.sum_const,Finset.card_powerset,Finset.card_univ,Fintype.card_fin,
          nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
        rfl
  have hr := reconstructedDyadValue_class_uniform F.S F.exclusions F.maximal η rows
    (sourcePrimePool F Z) (fun s=> source_prime_pool_outside F Z s) (fun _=> F.W) (fun s=> Z^(D.ell s))
    x z F.W (Z^ly) Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (by linarith)
    (fun s=> D.ell s/d) Q (maskFactor*A) (mul_nonneg hmf.le hA) hclass
  have heq := integratedDyadValue_reconstruction F.S F.exclusions F.maximal (4*D.e) F.first η rows hrow
    (sourcePrimePool F Z) (fun s=> source_prime_pool_outside F Z s) hdis hdisAll hη hQ
    (fun _=> F.W) (fun s=> Z^(D.ell s)) x z (by rw [hx];linarith [D.e_pos]) hz.ge
    (by rw [hx];linarith [D.e_pos]) F.W 1 2 (by norm_num) F.complex_support (Z^ly)
    (Real.rpow_pos_of_pos hZ0 _)
  rw [heq,norm_mul]
  have hpi : ‖(2*Real.pi:ℂ)‖=2*Real.pi := by
    rw [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  rw [hpi]
  apply (mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 2*Real.pi)).trans_eq
  simp only [Finset.card_univ,Fintype.card_fin]
  dsimp only [classFactor,maskFactor,A,common]
  ring

end Submission20261012.Global.Numerator
end

/- Adapted from weighted-numerator PR6, 2fd60c0926b66ea18d7436f5ed55250fd006ab5d; Apache-2.0. Uses the Cycle25 gap-dependent certificate. -/
end
/- END ORIGINAL MODULE Global.Numerator.SourceCollect -/

/- BEGIN ORIGINAL MODULE Global.Numerator.ActualSource ; sha256 b0449bb6f74ed5c3a463bd013e362412ed2de23b5bcaa4130ddbf5622156053b -/
section






/-! The actual source row bound. Every count, phase, coefficient, polynomial
moment, local Euler, and scalar estimate is supplied by a checked theorem. -/
noncomputable section
set_option maxHeartbeats 2800000
open scoped Classical BigOperators
open Filter
namespace Submission20261012.Global.Numerator
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open ProbeAssembly Cycle25DetectorRowCount Detector
open Cycle25.Numerator
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

/-- The raw analytic input for the actual full-w source follows from the
certified moments and source estimates, without an added analytic hypothesis. -/
theorem actual_raw_fullW_input : RawFullWAnalyticInput := by
  intro hβ D hfine F counts
  have hbeta : (51/100:ℝ)≤ HeckeZeroSupremum.beta := by
    have ht : (51/100:ℝ)< theta := by rw [Submission20261012.Global.theta_eq]; linarith [Submission20261012.Global.ell_interval.2]
    exact (ht.trans hβ).le
  obtain ⟨Jw,hJw,C,hC,hcollect⟩ := source_integrated_amplitude_classes D hβ F hbeta FinalAssembly.baseline_beta hfine
  obtain ⟨Cs,hCs,hscalar⟩ := weighted_source_scalar_on_rows D F
  refine ⟨Jw,hJw,?_⟩
  intro τ hτ hτzero hτheight hτt hτ2 hτeps hτJ n η
  obtain ⟨K,hK,hcount⟩ := weighted_source_masked_amplitude_count D F counts τ n hτ hτzero hτheight hτ2
  refine ⟨C*Cs*K,by have := zero_lt_one.trans_le hK;positivity,?_⟩
  filter_upwards [eventually_uniform_source_conductor (1/2) (by norm_num) hcollect,
    hcount η,actual_source_prime_upper D F τ n hτ hτheight,
    source_prime_reconstruction_geometry F η,weighted_source_pools_nonempty D F,
    weighted_source_height_le τ n hτ,
    (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2:ℝ)),
    eventually_gt_atTop (1:ℝ)] with Z hcollect hcount hupper hgeo hpools hheight hT hZ
  intro C0 hC0 hmom
  unfold RawSourceDyadBound
  intro rows d a i hd hdmax ha hatop hδ hi hsource hrows hrow hfreq hnext hcurrent p hp
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hd' : d≤7/8 := by linarith [Submission20261012.Global.h_interval.2,D.t_small]
  have hz : ((17/50:ℂ)+p.2*Complex.I).re=17/50 := by norm_num
  have hx : ((((a+16*D.e):ℝ):ℂ)+p.1*Complex.I).re=a+16*D.e := by simp
  have hzim : |((17/50:ℂ)+p.2*Complex.I).im|≤((3*i+1:ℕ):ℝ)*Z^τ := by simpa using hp.2
  have hdwide : d ≤ h+rowExtension := hdmax.trans (by linarith [D.weighted_top])
  have hupper' := hupper rows d a i hd hdwide ha.le hatop hi η
    (fun u hu=>(hsource u hu).2) hnext p hp
  have hscalar' := hscalar η rows Z τ d a i hZ0 hT ha.le hatop hfreq
    (fun u hu=>(hrows u hu).2) hnext p hp
  have hcounts := hcount d a C0 (by linarith) hd' ha hatop hC0 rows hsource i hi hnext hcurrent
    ((17/50:ℂ)+p.2*Complex.I) hz (hzim.trans (hheight i hi).2) hmom
  have hbase : ∀j,sourcePrimePool F Z j := fun j=>⟨(hpools j).choose,(hpools j).choose_spec⟩
  have hc := hcollect d hd
  -- The remaining line instantiates the literal finite-collection theorem.
  exact hc.2 Z d hZ hd hdmax rfl η
    ((((a+16*D.e):ℝ):ℂ)+p.1*Complex.I) ((17/50:ℂ)+p.2*Complex.I)
    a (((3*i+1:ℕ):ℝ)*Z^τ) ha.le hatop hδ hx hz (hheight i hi).1 hzim rows hrows hrow
    hgeo.2.1 hgeo.2.2.1 hgeo.2.2.2.1 hgeo.2.2.2.2.1 hgeo.2.2.2.2.2 hbase
    Cs K C0 hCs.le hK hC0 (by
      dsimp only
      intro J bin hne
      simpa only [add_assoc] using (hcounts (Finset.univ\J) bin hne).2.2) hscalar' hupper'

/-- The complete, normalized full-W input for the canonical physical source. -/
theorem actual_fullW_input : FullWAnalyticInput :=
  fullW_input_of_raw_source actual_raw_fullW_input

end Submission20261012.Global.Numerator
end

#print axioms Submission20261012.Global.Numerator.actual_raw_fullW_input
#print axioms Submission20261012.Global.Numerator.actual_fullW_input
end
/- END ORIGINAL MODULE Global.Numerator.ActualSource -/

/- BEGIN ORIGINAL MODULE Global.Endpoint ; sha256 81b2c4b6f8895d99c68e9001d490b40e45123f4adf3c3caf45240a4ab14f590b -/
section



/-! Unconditional zero-free endpoint obtained from the actual local/old
physical numerator, detector moments, LOW probe and continuation. -/
namespace Submission20261012.Global
open OAI.SevenEighths

/-- The actual supremum of Hecke zeros is at most the new rational endpoint. -/
theorem beta_le_theta : HeckeZeroSupremum.beta ≤ theta :=
  beta_le_theta_of_raw_fullW_input Numerator.actual_raw_fullW_input

theorem hecke_nonzero (χ : HeckeFamily.Character) (s : ℂ)
    (hs : theta < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    HeckeFamily.LFunction χ s ≠ 0 :=
  hecke_nonzero_of_raw_fullW_input Numerator.actual_raw_fullW_input χ s hs hpole

/-- Canonical all-moduli Dirichlet target, with the sole principal pole excluded. -/
theorem dirichlet_nonzero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : (4374347:ℝ)/5000000 < s.re) (hexc : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  dirichlet_nonzero_of_raw_fullW_input Numerator.actual_raw_fullW_input χ s hs hexc

theorem zeta_nonzero (s : ℂ) (hs : (4374347:ℝ)/5000000 < s.re) : riemannZeta s ≠ 0 :=
  zeta_nonzero_rational_of_raw_fullW_input Numerator.actual_raw_fullW_input s hs

/-- Exact improvement over the pinned cycle25 catalogue endpoint. -/
theorem strictly_better_than_cycle25 : (4374347:ℝ)/5000000 < 683505193/781250000 := by
  norm_num

end Submission20261012.Global
#print axioms Submission20261012.Global.beta_le_theta
#print axioms Submission20261012.Global.hecke_nonzero
#print axioms Submission20261012.Global.dirichlet_nonzero
#print axioms Submission20261012.Global.zeta_nonzero
#print axioms Submission20261012.Global.strictly_better_than_cycle25
#print Submission20261012.Global.dirichlet_nonzero
end
/- END ORIGINAL MODULE Global.Endpoint -/
