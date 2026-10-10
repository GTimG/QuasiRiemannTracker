import WeightedQRH.NumeratorSourceMask
import WeightedQRH.NumeratorFiniteHeight

/-! Finite collection of the actual physical error masks and the original full
amplitude classes. One degree and one positive constant precede U and all target,
height and contour choices. No analytic estimate is introduced in this step. -/
noncomputable section
set_option maxHeartbeats 2500000
open scoped Classical BigOperators ContDiff
open Filter
namespace WeightedQRH.Numerator
open OAI OAI.SevenEighths ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open ProbeFinalAssemblyCertifiedBands HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

theorem source_integrated_amplitude_classes {Δ : ℝ} (D : HighParameters.HighData Δ)
    (F : WeightedSourceData D.toMomentData) (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hfine : ∀j,D.ell j ≤ weighted_detectorMesh D.t/200) :
    ∃Jw : ℝ,0 ≤ Jw ∧ ∃C : ℝ,0 < C ∧ ∀ᶠU : ℝ in atTop,
      1 < U ∧ ∀(Z d : ℝ),1 < Z → (1/2:ℝ) ≤ d → d ≤ WeightedQRH.h+rowExtension → U=Z^d →
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
      let Q := fun (u : FreeRow) s=>HeckePrimeRow.canonicalPrimeAmplitude
        F.modulus ⊤ u.val F.W 2 (Z^(D.ell s)) z
      (∀J : Finset (Fin D.N),∀bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t,
        let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=>D.ell s/d) Q bin
        let q := weightedMean Finset.univ (fun s=>D.ell s/d)
          (maskedGain (Finset.univ\J) (binValue Finset.univ ((2*a-1)/2) D.t bin))
        rows'.Nonempty → (rows'.card:ℝ) ≤ K*C0*Z^(3*D.t)*
          U^(rowCount (2*a-1) (q/(2*a-1))+159*D.ε+9*D.t)) →
      (∀u∈rows,‖frequencyWeight z ⟨u.val,u.property.1⟩*
        numeratorFreeRowScalar F.S F.exclusions F.maximal η u x z‖ ≤
        Cs*(η.modulus.absNorm:ℝ)^(2*D.eps)*(3+height)^(2*D.eps)*
          U^(2*D.eps)*U^(-(17/50:ℝ))*Z^((17/25)*D.t)) →
      (∀u∈rows,∀s,‖Q u s‖ ≤ (Z^(D.ell s))^
        (HeckePrimeAmplitudeBins.amplitude (Z^(D.ell s)) ((2*a-1)/2) D.t (Q u s)+D.t)) →
      ‖FullWContour.integratedDyadValue F.S F.exclusions F.maximal η rows (sourcePrimePool F Z)
        (fun s=>source_prime_pool_outside F Z s) (fun _=>F.W) (fun s=>Z^(D.ell s)) F.W (Z^ly) x z‖ ≤
        (C*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*D.eps)*(3+height)^Jw*
          Z^(signal theta-1/40000-WeightedHighFinalAssembly.weightedSourceSZExponent a D.e-D.t) := by
  choose degree Cmask hCmask hmask using (fun J : Finset (Fin D.N)=>source_mask_amplitude_class D F hbeta hfine J)
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
  let Q := fun (u : FreeRow) s=>HeckePrimeRow.canonicalPrimeAmplitude
    F.modulus ⊤ u.val F.W 2 (Z^(D.ell s)) z
  let classRows := fun bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t=>
    amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=>D.ell s/d) Q bin
  intro hcount hscalar hupper
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  let common : ℝ := Cs*K*C0*(η.modulus.absNorm:ℝ)^(2*D.eps)*
    Z^(signal theta-1/40000-WeightedHighFinalAssembly.weightedSourceSZExponent a D.e-D.t)
  let A : ℝ := common*Ctot*(3+height)^(Jw+2*D.eps)
  have hcommon : 0 ≤ common := by dsimp only [common];positivity
  have hA : 0 ≤ A := by dsimp only [A];positivity
  have hmaskBound (bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t)
      (hne : (classRows bin).Nonempty) (J : Finset (Fin D.N)) :
      ‖sourceMaskContribution F η (classRows bin) J Z x z (Z^ly)‖ ≤ A := by
    have hsub : classRows bin ⊆ rows := Finset.filter_subset _ _
    have hh := (hall J).2 Z d hZ hd hdmax hUZ η x z a height ha hatop hδ hx hz hH him
      rows hrows hrow (hdis J) hη hQ hS (fun j:J=>Pbase j.val) bin hne Cs K C0 hCs hK hC0
      (hcount J bin hne) (fun u hu=>hscalar u (hsub hu)) (fun u hu=>hupper u (hsub hu))
    have he := (hheight height D.eps hH D.eps_pos.le).1 J
    calc
      _ ≤ (Cmask J*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*D.eps)*
          (3+height)^((degree J:ℝ)+2*D.eps)*
          Z^(signal theta-1/40000-WeightedHighFinalAssembly.weightedSourceSZExponent a D.e-D.t) := hh
      _ = common*(Cmask J*(3+height)^((degree J:ℝ)+2*D.eps)) := by dsimp only [common];ring
      _ ≤ common*(Ctot*(3+height)^(Jw+2*D.eps)) := mul_le_mul_of_nonneg_left he hcommon
      _ = A := by dsimp only [A];ring
  have hclass (bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t)
      (hne : (classRows bin).Nonempty) :
      ‖reconstructedDyadValue F.S F.exclusions F.maximal η (classRows bin) (sourcePrimePool F Z)
        (fun s=>source_prime_pool_outside F Z s) (fun _=>F.W) (fun s=>Z^(D.ell s)) x z F.W (Z^ly)‖ ≤ maskFactor*A := by
    calc
      _ = ‖∑J∈Finset.univ.powerset,sourceMaskContribution F η (classRows bin) J Z x z (Z^ly)‖ :=
        congrArg norm (source_reconstructed_sum_masks F η (classRows bin) Z x z (Z^ly))
      _ ≤ ∑J∈Finset.univ.powerset,A := by
        apply (norm_sum_le _ _).trans
        exact Finset.sum_le_sum (fun J _=>hmaskBound bin hne J)
      _ = maskFactor*A := by
        simp only [Finset.sum_const,Finset.card_powerset,Finset.card_univ,Fintype.card_fin,
          nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
        rfl
  have hr := reconstructedDyadValue_class_uniform F.S F.exclusions F.maximal η rows
    (sourcePrimePool F Z) (fun s=>source_prime_pool_outside F Z s) (fun _=>F.W) (fun s=>Z^(D.ell s))
    x z F.W (Z^ly) Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (by linarith)
    (fun s=>D.ell s/d) Q (maskFactor*A) (mul_nonneg hmf.le hA) hclass
  have heq := integratedDyadValue_reconstruction F.S F.exclusions F.maximal (4*D.e) F.first η rows hrow
    (sourcePrimePool F Z) (fun s=>source_prime_pool_outside F Z s) hdis hdisAll hη hQ
    (fun _=>F.W) (fun s=>Z^(D.ell s)) x z (by rw [hx];linarith [D.e_pos]) hz.ge
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

end WeightedQRH.Numerator
end
