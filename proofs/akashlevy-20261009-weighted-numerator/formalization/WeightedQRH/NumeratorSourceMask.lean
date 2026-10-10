import WeightedQRH.NumeratorSourceClass
import WeightedQRH.NumeratorPhysicalCollect
import WeightedQRH.NumeratorSourceExponent
import WeightedQRH.NumeratorSourceScalar

/-! Actual physical mask contributions on the original full amplitude classes.
The certified moment is already discharged by SourceClass. Count and calibrated
scalar bounds are kept explicit so the same source constants apply to every mask. -/
noncomputable section
set_option maxHeartbeats 2800000
open scoped Classical BigOperators ContDiff
open Filter
namespace WeightedQRH.Numerator
open OAI OAI.SevenEighths ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open ProbeFinalAssemblyCertifiedBands HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

/-- A literal physical error-mask sum has the uniform pre-height certificate
exponent, with only the original full-class count and actual scalar as inputs. -/
theorem source_mask_amplitude_class {Δ:ℝ} (D:HighParameters.HighData Δ)
    (F:WeightedSourceData D.toMomentData) (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hfine:∀j,D.ell j≤weighted_detectorMesh D.t/200) (J:Finset (Fin D.N)) :
    ∃degree:ℕ,∃C:ℝ,0 < C ∧ ∀ᶠU:ℝ in atTop,
      1 < U ∧ ∀(Z d:ℝ),1 < Z → (1/2:ℝ)≤d → d≤WeightedQRH.h+rowExtension → U=Z^d →
      ∀(η:Character) (x z:ℂ) (a height:ℝ),(51/100:ℝ)≤a → a≤7/8 → 1/3≤2*a-1 →
      x.re=a+16*D.e → z.re=17/50 → 0≤height → |z.im|≤height →
      ∀rows:Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ)≤rowNorm u ∧ rowNorm u≤U) →
      (∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue≠1) →
      (∀P:∀i:J,sourcePrimePool F Z i.val,Function.Injective (fun i=>(P i).val)) →
      (∀i P,P∈sourcePrimePool F Z i→IsCoprime P.val η.modulus) →
      (∀i P,P∈sourcePrimePool F Z i→(4:ℝ)≤P.val.absNorm) →
      (∀i,∀P∈F.S,(P.absNorm:ℝ)≤Z^(D.ell i)) →
      (∀i:J,sourcePrimePool F Z i.val) →
      ∀bin:BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t,
      let Q := fun (u:FreeRow) s=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell s)) z
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=>D.ell s/d) Q bin
      let main := (Finset.univ:Finset (Fin D.N)) \ J
      let q := weightedMean Finset.univ (fun s=>D.ell s/d)
        (maskedGain main (binValue Finset.univ ((2*a-1)/2) D.t bin))
      rows'.Nonempty → ∀Cs K C0:ℝ,0≤Cs → 1≤K → 1≤C0 →
      (rows'.card:ℝ)≤K*C0*Z^(3*D.t)*U^(rowCount (2*a-1) (q/(2*a-1))+159*D.ε+9*D.t) →
      (∀u∈rows',‖frequencyWeight z ⟨u.val,u.property.1⟩*numeratorFreeRowScalar F.S F.exclusions F.maximal η u x z‖≤
        Cs*(η.modulus.absNorm:ℝ)^(2*D.eps)*(3+height)^(2*D.eps)*U^(2*D.eps)*U^(-(17/50:ℝ))*Z^((17/25)*D.t)) →
      (∀u∈rows',∀s,‖Q u s‖≤(Z^(D.ell s))^
        (HeckePrimeAmplitudeBins.amplitude (Z^(D.ell s)) ((2*a-1)/2) D.t (Q u s)+D.t)) →
      ‖sourceMaskContribution F η rows' J Z x z (Z^ly)‖ ≤
        (C*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*D.eps)*(3+height)^((degree:ℝ)+2*D.eps)*
          Z^(signal theta-1/40000-WeightedHighFinalAssembly.weightedSourceSZExponent a D.e-D.t) := by
  obtain ⟨degree,C,hC,hclass⟩ := source_packet_amplitude_class D F hbeta hfine J
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [hclass] with U hclass
  refine ⟨hclass.1,?_⟩
  intro Z d hZ hd hdmax hUZ η x z a height ha hatop hδlow hx hz hheight hzim rows hrows hrow hdis hη hQ hS Pbase bin
  dsimp only
  let Q := fun (u:FreeRow) s=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell s)) z
  let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=>D.ell s/d) Q bin
  let main := (Finset.univ:Finset (Fin D.N)) \ J
  let q := weightedMean Finset.univ (fun s=>D.ell s/d)
    (maskedGain main (binValue Finset.univ ((2*a-1)/2) D.t bin))
  intro hne Cs K C0 hCs hK hC0 hcard hscalar hupper
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hU0 : 0 < U := zero_lt_one.trans hclass.1
  have hd0 : 0 < d := by linarith
  have hδ : 0 < 2*a-1 := by linarith
  have hsub : rows'⊆rows := Finset.filter_subset _ _
  have hY : U^(ly/d)=Z^ly := by
    rw [hUZ,←Real.rpow_mul hZ0.le,mul_div_cancel₀ _ hd0.ne']
  have hcount1 : 1≤K*C0*Z^(3*D.t) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hK hC0)
      (Real.one_le_rpow hZ.le (by have := D.t_pos;positivity))
  have hb := hclass.2 Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hheight hzim rows hrows hrow
    hdis hη Pbase bin hne (rowCount (2*a-1) (q/(2*a-1))+159*D.ε+9*D.t)
    (K*C0*Z^(3*D.t)) hcount1 hcard hupper
  have heq (u:FreeRow) (hu:u∈rows') := errorLabelNumerator_eq_packet F.S F.exclusions (4*D.e) F.first η u
    (hrow u (hsub hu)) J (sourcePrimePool F Z) (fun s=>source_prime_pool_outside F Z s) hdis hη hQ
    (fun _=>F.W) (fun s=>Z^(D.ell s)) x z (by rw [hx];linarith [D.e_pos]) hz.ge
    (by rw [hx];linarith [D.e_pos]) F.W 1 2 (by norm_num) F.complex_support (F.W.smooth ⊤)
    (Z^ly) (Real.rpow_pos_of_pos hZ0 _)
  have hlabel : (∑u∈rows',‖errorLabelNumerator F.S F.exclusions η u J (sourcePrimePool F Z)
      (fun s=>source_prime_pool_outside F Z s) (fun _=>F.W) (fun s=>Z^(D.ell s)) x z F.W (Z^ly)*
      (∏s∈main,Q u s)‖) ≤
    C*(K*C0*Z^(3*D.t))*(1+height)^degree*(U^(ly/d))^(-(1/2:ℝ))*(∏s:J,(Z^(D.ell s.val))^(-(4/25:ℝ)))*
      U^(D.t+q*(ell/d)-q*((2*(ly/d)-1)/(9/2)-4*D.t/9)/2+
        (3*(rowCount (2*a-1) (q/(2*a-1))+159*D.ε+9*D.t)+1+2*D.t)/4+
        (2*a-1)*weighted_detectorMesh D.t/4+(2*a-1)*D.t/4+D.t*(ell/d)) := by
    convert hb using 1
    calc
      _ = ∑i:rows',‖errorLabelNumerator F.S F.exclusions η i.val J (sourcePrimePool F Z)
          (fun s=>source_prime_pool_outside F Z s) (fun _=>F.W) (fun s=>Z^(D.ell s)) x z F.W (Z^ly)*
          (∏s∈main,Q i.val s)‖ := (Finset.sum_coe_sort rows' _).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [heq i.val i.property,hY]
  let A := Cs*(η.modulus.absNorm:ℝ)^(2*D.eps)*(3+height)^(2*D.eps)*U^(2*D.eps)*
    U^(-(17/50:ℝ))*Z^((17/25)*D.t)
  have hA : 0≤A := by dsimp only [A];positivity
  have hphysical := source_mask_physical_front F η rows' J Z hZ0 x z hz (Z^ly) hS A _ hA hscalar hlabel
  have hselection := source_class_main_selection D F hfine Z d 0 (2*a-1) hZ hd (by norm_num) hδ.le z rows main bin hne
  have hq0 : 0≤q := hselection.1
  have hqmax : q≤(2*a-1)/2 := hselection.2.1
  have he := source_packet_multiplicative_identity J D.ell D.slots_sum Z d (2*a-1) q D.ε D.eps D.t
    (weighted_detectorMesh D.t) C K C0 ((1+height)^degree) hZ0 hd0.ne' hδ.ne'
  have hcollapse : A*Z^(-(4/25:ℝ)*(∑j:{i:Fin D.N//i∉J},D.ell j.val))*
      (C*(K*C0*Z^(3*D.t))*(1+height)^degree*(U^(ly/d))^(-(1/2:ℝ))*(∏s:J,(Z^(D.ell s.val))^(-(4/25:ℝ)))*
      U^(D.t+q*(ell/d)-q*((2*(ly/d)-1)/(9/2)-4*D.t/9)/2+
        (3*(rowCount (2*a-1) (q/(2*a-1))+159*D.ε+9*D.t)+1+2*D.t)/4+
        (2*a-1)*weighted_detectorMesh D.t/4+(2*a-1)*D.t/4+D.t*(ell/d))) =
      (C*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*D.eps)*(3+height)^(2*D.eps)*(1+height)^degree*
        Z^(numeratorExponent d (2*a-1) (q/(2*a-1))+
          weightedSourceLoss d (2*a-1) q D.ε D.eps D.t (weighted_detectorMesh D.t) D.t (2*D.t) D.t D.t) := by
    dsimp only [A]
    rw [hUZ]
    calc
      _ = (Cs*(η.modulus.absNorm:ℝ)^(2*D.eps)*(3+height)^(2*D.eps))*
          (((Z^d)^(2*D.eps)*(Z^d)^(-(17/50:ℝ))*Z^((17/25)*D.t)*
            Z^(-(4/25:ℝ)*(∑j:{i:Fin D.N//i∉J},D.ell j.val)))*
          (C*(K*C0*Z^(3*D.t))*(1+height)^degree*((Z^d)^(ly/d))^(-(1/2:ℝ))*
            (∏s:J,(Z^(D.ell s.val))^(-(4/25:ℝ)))*
            (Z^d)^(D.t+q*(ell/d)-q*((2*(ly/d)-1)/(9/2)-4*D.t/9)/2+
              (3*(rowCount (2*a-1) (q/(2*a-1))+159*D.ε+9*D.t)+1+2*D.t)/4+
              (2*a-1)*weighted_detectorMesh D.t/4+(2*a-1)*D.t/4+D.t*(ell/d)))) := by ring
      _ = _ := by rw [he];ring
  have hphysical' := hphysical.trans_eq hcollapse
  have hheightpow : (1+height)^degree ≤ (3+height)^(degree:ℝ) := by
    rw [Real.rpow_natCast]
    exact pow_le_pow_left₀ (by linarith) (by linarith) _
  have hcert := weighted_source_packet_certificate D d a q hd hdmax hδlow hatop hq0 hqmax
  apply hphysical'.trans
  calc
    _ ≤ (C*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*D.eps)*(3+height)^(2*D.eps)*(3+height)^(degree:ℝ)*
        Z^(signal theta-1/40000-WeightedHighFinalAssembly.weightedSourceSZExponent a D.e-D.t) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hheightpow (by positivity)
      · exact Real.rpow_le_rpow_of_exponent_le hZ.le hcert
      · positivity
      · positivity
    _ = _ := by rw [Real.rpow_add (by linarith : 0 < 3+height) (degree:ℝ) (2*D.eps)];ring

end WeightedQRH.Numerator
end
