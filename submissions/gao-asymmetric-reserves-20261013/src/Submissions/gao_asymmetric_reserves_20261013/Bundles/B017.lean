/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B012
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B013
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.DetectorMomentPrimeGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceDeleted
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferencePrimeGates
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorFixedAmplitudeCount
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.ExceptionalRows
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorEnergyInitialState
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFixedIdeal
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFreeExceptional
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.PositiveSummability
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.ParametersSlotLengths
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.Moments

/- BEGIN ORIGINAL MODULE Cycle25.Arithmetic.Certificate ; sha256 e1a840ce94e9b0cbc5bd9c5c61d97998904c084f31b1b7a2fcbcbf0f9a99138d -/
section


/-! The exact polynomial certificate from B0.49. All coefficient identities are
verified in Lean, using the algebraic root relation, rather than numerical sampling. -/

namespace Cycle25.Arithmetic

noncomputable def certT : ℝ := ell0-(h0-4*ell0)/(12*kappa0)
noncomputable def certk0 : ℝ := b0-(1+ell0)/2-h0/3
noncomputable def certk1 : ℝ := -1/2+3*h0/4-certT/2
noncomputable def certK : ℝ := 8*(24-216*kappa0)*certk1+18*h0*(24*kappa0-4)
noncomputable def certA10 : ℝ := 8*(120*kappa0+80)*certk0
noncomputable def certA11 : ℝ :=
  8*((300*kappa0-40)*certT+(120*kappa0+80)*certk1+(144*kappa0-96)*certk0)-15*h0*(48*kappa0)
noncomputable def certA12 : ℝ := 8*((24-216*kappa0)*certT+(144*kappa0-96)*certk1)+18*h0*(48*kappa0)
noncomputable def certA20 : ℝ := 8*((120*kappa0+80)*certT+96*certk0)-15*h0*16
noncomputable def certA21 : ℝ := 8*((144*kappa0-96)*certT+96*certk1)+18*h0*16

noncomputable def certTPoly : ℝ := (-107020651/284324837) + (10777515509/5686496740) * ell0 + (4792397229/568649674) * ell0^2 + (-27460249389/5686496740) * ell0^3
noncomputable def certKPoly : ℝ := (68512621584/284324837) + (-622826635656/1421624185) * ell0 + (122316868800/284324837) * ell0^2 + (-181484567064/1421624185) * ell0^3
noncomputable def certA10Poly : ℝ := (87728742200/284324837) + (-535522104160/284324837) * ell0 + (451803856200/284324837) * ell0^2 + (-114989084640/284324837) * ell0^3
noncomputable def certA11Poly : ℝ := (-61885021440/284324837) + (372585555024/284324837) * ell0 + (-1940825802960/284324837) * ell0^2 + (946378571616/284324837) * ell0^3
noncomputable def certA12Poly : ℝ := (705445344/2516149) + (-2207857008/12580745) * ell0 + (9465572448/2516149) * ell0^2 + (-24316485552/12580745) * ell0^3
noncomputable def certA20Poly : ℝ := (-82067841600/284324837) + (272874521856/284324837) * ell0 + (1865417596320/284324837) * ell0^2 + (-1021092398496/284324837) * ell0^3
noncomputable def certA21Poly : ℝ := (153518482944/284324837) + (317929676448/1421624185) * ell0 + (-3548627116416/284324837) * ell0^2 + (8857647944352/1421624185) * ell0^3

theorem certT_poly : certT = certTPoly := by
  have hk : 12*kappa0 ≠ 0 := ne_of_gt (by linarith [kappa0_range.1])
  have hid : h0-4*ell0 = (ell0-certTPoly)*(12*kappa0) := by
    rw [h0_poly]
    simp only [hPoly, certTPoly, kappa0]
    have hp := ell0_quartic
    unfold quartic at hp
    linear_combination (-((-88868121/2843248370)))*hp
  have hq : (h0-4*ell0)/(12*kappa0) = ell0-certTPoly := (div_eq_iff hk).2 hid
  simp only [certT]
  rw [hq]
  ring

theorem certK_poly : certK = certKPoly := by
  simp only [certK, certk1]
  rw [h0_poly, certT_poly]
  simp only [hPoly, certTPoly, certKPoly, kappa0]
  have hp := ell0_quartic
  unfold quartic at hp
  linear_combination ((3775160196/1421624185))*hp

theorem certA10_poly : certA10 = certA10Poly := by
  simp only [certA10, certk0]
  rw [h0_poly]
  simp only [hPoly, certA10Poly, kappa0, b0]
  have hp := ell0_quartic
  unfold quartic at hp
  linear_combination ((42659840/284324837))*hp

theorem certA11_poly : certA11 = certA11Poly := by
  simp only [certA11, certk0, certk1]
  rw [h0_poly, certT_poly]
  simp only [hPoly, certTPoly, certA11Poly, kappa0, b0]
  have hp := ell0_quartic
  unfold quartic at hp
  linear_combination ((1473081744/284324837))*hp

theorem certA12_poly : certA12 = certA12Poly := by
  simp only [certA12, certk1]
  rw [h0_poly, certT_poly]
  simp only [hPoly, certTPoly, certA12Poly, kappa0]
  have hp := ell0_quartic
  unfold quartic at hp
  linear_combination ((-9683155296/1421624185))*hp

theorem certA20_poly : certA20 = certA20Poly := by
  simp only [certA20, certk0]
  rw [h0_poly, certT_poly]
  simp only [hPoly, certTPoly, certA20Poly, kappa0, b0]
  have hp := ell0_quartic
  unfold quartic at hp
  linear_combination ((710944968/284324837))*hp

theorem certA21_poly : certA21 = certA21Poly := by
  simp only [certA21, certk1]
  rw [h0_poly, certT_poly]
  simp only [hPoly, certTPoly, certA21Poly, kappa0]
  have hp := ell0_quartic
  unfold quartic at hp
  linear_combination ((4265669808/1421624185))*hp

set_option maxHeartbeats 1000000 in
theorem tangency_constant : 8*(300*kappa0-40)*certk0 = certK*delta0^2 := by
  rw [certK_poly, delta0_poly]
  simp only [certk0]
  rw [h0_poly]
  simp only [certKPoly, deltaPoly, hPoly, kappa0, b0]
  have hp := ell0_quartic
  unfold quartic at hp
  linear_combination ((-535841160673310/458293822040679) + (160341946084451/152764607346893) * ell0 + (-43840582925935/305529214693786) * ell0^2 + (-795280181869641/1527646073468930) * ell0^3 + (175627044476289/1527646073468930) * ell0^4 + (114494076246501/1527646073468930) * ell0^5)*hp

set_option maxHeartbeats 1000000 in
theorem tangency_linear : 8*((300*kappa0-40)*certk1+(24-216*kappa0)*certk0)-15*h0*(24*kappa0-4) = -2*certK*delta0 := by
  rw [certK_poly, delta0_poly]
  simp only [certk0, certk1]
  rw [h0_poly, certT_poly]
  simp only [certKPoly, deltaPoly, hPoly, certTPoly, kappa0, b0]
  have hp := ell0_quartic
  unfold quartic at hp
  linear_combination ((-707020991482/208410105521) + (-163660339476/1042050527605) * ell0 + (-211731994908/1042050527605) * ell0^2)*hp

private theorem ell0_power_bounds (n : ℕ) : rootLo^n ≤ ell0^n ∧ ell0^n ≤ rootHi^n := by
  have hlo : 0 ≤ rootLo := by norm_num [rootLo]
  have he : 0 ≤ ell0 := by linarith [ell0_coarse.1]
  exact ⟨pow_le_pow_left₀ hlo (le_of_lt ell0_lo) n,
    pow_le_pow_left₀ he (le_of_lt ell0_hi) n⟩

theorem coefficient_minorants :
    36 < certA10 ∧ -174 < certA11 ∧ 347 < certA12 ∧
    38 < certA20 ∧ 257 < certA21 ∧ 179 < certK ∧ certK < 180 ∧
    117 < 768*certT ∧ 768*certT < 119 := by
  have he := ell0_lo
  have he' := ell0_hi
  have he2 := ell0_power_bounds 2
  have he3 := ell0_power_bounds 3
  norm_num [rootLo, rootHi] at he he' he2 he3
  rw [certA10_poly, certA11_poly, certA12_poly, certA20_poly, certA21_poly, certK_poly, certT_poly]
  simp only [certA10Poly, certA11Poly, certA12Poly, certA20Poly, certA21Poly, certKPoly, certTPoly]
  repeat' constructor
  all_goals linarith

end Cycle25.Arithmetic
end
/- END ORIGINAL MODULE Cycle25.Arithmetic.Certificate -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.FixedAmplitude ; sha256 8b62bcd09949f1f6c254c03febabe9dc87cf06c2c168606b6f1bd060b739ea5d -/
section


namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.Cycle25DetectorFixedAmplitudeCount
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst Cycle25DetectorRowCount
open HeckeDetectorFixedAmplitudeCount

theorem fixed_amplitude_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤ B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃c κ K₀ : ℝ,0< c ∧ c≤1 ∧ 0<κ ∧ 0≤ K₀ ∧ ∀ᶠU : ℝ in atTop,
      ∀(a ε tstar T allowance κplain ν C height q : ℝ) (i : ℕ),
      1< U → 51/100< a → 2*a-1≤3/4 → 0≤ε → ε≤1/1000 →
      1≤ tstar → tstar≤3/2 → 7/10≤κplain → κplain≤3/4 → 0<ν → 0≤ C → 0≤ height →
      2*Real.pi*allowance+(3*i:ℕ)*T≤ height →
      ∀{Label Slot : Type*} [Fintype Label] (B : Batch M H Label Slot U a ε tstar T allowance i),
      (∀u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=> u.val) B.profile B.upper B.widths B.external U) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Cycle25DetectorRawFiber.Moments (B.fiber bin j J K hne) κplain c κ C height εm) →
      (B.rows.card:ℝ)≤(Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2* fiberConstant C height K₀*
        (Fintype.card B.Bin:ℝ)*
        U^(max (shortExponent (2*a-1) (q/(2*a-1)) κplain tstar) (longExponent (2*a-1) tstar)+
          159*ε+εm+B.mesh+7*ν) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hcount⟩ := Cycle25DetectorCountFromMoments.count_from_raw_moments
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hcount] with U hcount
  intro a ε tstar T allowance κplain ν C height q i hU ha hd hε hε' ht ht' hk hk1 hν hC hh hf Label Slot _ B hq moments
  have hb := B.card_bound (fiberConstant C height K₀)
    (fun _=> max (shortExponent (2*a-1) (q/(2*a-1)) κplain tstar) (longExponent (2*a-1) tstar)+
      159*ε+εm+B.mesh+7*ν)
    (fiberConstant_bounds C height K₀ hC hh hK).1 (zero_lt_one.trans hU) (by
      intro bin j J K hne
      have hc' := hcount a ε tstar T allowance κplain ν C height i hU ha hd hε hε' ht ht' hk hk1 hν hC hh hf
        (B.fiber bin j J K hne) (moments bin j J K hne)
      rw [fiber_mean_eq B q hq bin j J K hne] at hc'
      exact hc')
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc] using hb
end SevenEighths.Cycle25DetectorFixedAmplitudeCount

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.FixedAmplitude -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.MomentInverseMarkedReferencePrimeGates ; sha256 ec082d457be367185baef0746540eec6cb4f3e1cbcbece9cc3b5f15c0434ddc4 -/
section




namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
namespace SevenEighths.Cycle25DetectorDictionaryInverseMarkedReference
open DetectorDictionaryInverseMarkedReference Cycle25ProbeFinalAssembly
open HeckeFamily HeckeInverseAmplification InverseInitialDetectorSource
open InverseInitialRawDictionary InverseInitialPhysicalSlots
open DetectorDictionaryInverseRawInitialGates InverseInitialExcludedPeriod
open InverseInitialExcludedPool InverseInitialExcludedOverlap Filter CanonicalQuadraticSieve CanonicalRowCompletion
local notation "O"=> HeckeFamily.O

theorem weighted_deleted_large_eventually {Label Slot:Type*}[Fintype Label][Fintype Slot]
    (data:Label→RowData)(ell:Slot→ℝ)(hell:∀s,0< ell s) :
    ∀ᶠZ:ℝ in atTop,1 ≤ Z ∧ ∀d:ℝ,0< d→∀j:Label,∀s:Slot,
      ((deletedBase (data j)).modulus.absNorm:ℝ)<(Z^d)^(ell s/d) := by
  have ht:∀ᶠZ:ℝ in atTop,∀j:Label,∀s:Slot,
      ((deletedBase (data j)).modulus.absNorm:ℝ)< Z^(ell s) := by
    apply Filter.eventually_all.mpr
    intro j
    apply Filter.eventually_all.mpr
    intro s
    exact (tendsto_rpow_atTop (hell s)).eventually (eventually_gt_atTop _)
  filter_upwards [eventually_ge_atTop (1:ℝ),ht] with Z hZ ht
  refine ⟨hZ,?_⟩
  intro d hd j s
  rw [←Real.rpow_mul (by linarith:0 ≤ Z),mul_div_cancel₀ _ hd.ne']
  exact ht j s

theorem weighted_deletedBase_supported (data:RowData)(I:Ideal O)
    (hI:idealCoeff (deletedBase data) I≠0) : CanonicalQuadraticSieve.Supported I := by
  by_contra hn
  exact hI (deletedBase_zero_unsupported data I hn)

theorem weighted_deleted_source_live_prime {D:Cycle25.Weighted.MomentData}
    (F:Cycle25ProbeFinalAssembly.WeightedSourceData D)(data:RowData)
    (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)
    (X:ℝ)(hX:0< X)(ζ:ℂ)(hζ:ζ.re ≤ 1)
    (hlarge:((deletedBase data).modulus.absNorm:ℝ)< X)
    (P:Ideal O)(hP:P∈livePrimes M H F.W 2 X) :
    Prime P ∧ InverseInitialExcludedPool.outside (excluded data) P ∧
      idealCoeff (deletedBase data) P≠0 ∧ ‖idealCoeff (deletedBase data) P‖=1 ∧
      ‖star (primeProfile F.W X ζ P)/idealCoeff (deletedBase data) P‖ ≤ 1 := by
  have hd:=livePrime_data M H F.W 1 2 X hX F.complex_support P hP
  have hcop:=ProbeRaySlots.prime_coprime_of_norm_gt (deletedBase data) ⟨P,hd.1⟩
    (hlarge.trans_le (by simpa only [one_mul] using hd.2.2.1))
  have hn:=PrincipalSignalComparison.idealCoeff_norm_one_of_coprime (deletedBase data) P hd.1.ne_zero hcop
  have hne:=HeckeDetectorRelativePrime.idealCoeff_ne_zero_of_coprime (deletedBase data) P hd.1.ne_zero hcop
  have hout:outside (excluded data) P := by
    by_contra hh
    exact hne (deleted_zero_outside (baseCharacter data) (excluded data)
      (reflectionExcludedPrimes_prime (basePeriod data)) P hh)
  refine ⟨hd.1,hout,hne,hn,?_⟩
  rw [norm_div,norm_star,hn,div_one]
  exact Cycle25ProbeHighRowFamily.weighted_sourceMoment_primeProfile_norm F X ζ hζ P

end SevenEighths.Cycle25DetectorDictionaryInverseMarkedReference

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.MomentInverseMarkedReferencePrimeGates -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.MomentNaturalFixedRaySourceFreeExceptional ; sha256 b796ae8b5f93303124788aa0428c6b3d4f411b60f0d58e01f049986ac31352e1 -/
section




namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter

namespace SevenEighths.Cycle25CenteredMomentNaturalFixedRaySource
open CenteredMomentNaturalFixedRaySource Cycle25ProbeFinalAssembly
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily UniqueFactorizationMonoid
open CenteredMomentDetectorDictionary CenteredExceptionalProfile CenteredExceptionalCount
open ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O

theorem weighted_fixed_inducing_free_support (η : Character) (Q : Ideal O)
    (hQ0 : Q≠0) (hQ : Q≠⊤) (hQ72 : Q ≤ Ideal.span {(72:O)}) (hQη : Q ≤ η.modulus)
    (m : O) (hm : m≠0) (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (u : FreeRow) (hu : FixedInducingRow η Q m 1 u.val) :
    u.val∈HeckeExceptionalRows.rows (normalizedFactors Q).toFinset := by
  obtain ⟨χ,ψ,hprim,hind,hψ,hχ⟩:=hu
  refine ⟨u.property.1,?_⟩
  intro P hP
  refine ⟨?_,u.property.2 P⟩
  by_contra hout
  have hp : Prime P:=prime_of_normalized_factor P hP
  let : P.IsMaximal:=(Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  obtain ⟨hl,h2,hQP⟩:=outside_fixed_support Q hQ0 hQ72 P hp hout
  have hηP : IsCoprime η.modulus P:=hQP.of_isCoprime_of_dvd_left (Ideal.dvd_iff_le.mpr hQη)
  have hz:=actual_row_numerator_valuation_zero η χ ψ hind Q hQ hQ72 hψ
    m 1 u.val hm one_ne_zero u.property.1 hml hm2
    (by simpa only [one_mul] using hχ) P hl h2 hQP hηP
  simp only [one_pow,one_mul,valuation] at hz
  have hpos:=Multiset.count_pos.mpr hP
  have hlt:=u.property.2 P
  omega

variable {D : Cycle25.Weighted.MomentData}

def weighted_sourceExceptionalBound (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (η : Character) : ℕ :=
  HeckeExceptionalRows.bound (normalizedFactors (internalQ (weighted_sourceFixedIdeal F) η)).toFinset

lemma weighted_source_exceptional_norm (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (η : Character)
    (u : FreeRow) (hu : weighted_sourceExceptional F η u) :
    (Ideal.span {u.val}).absNorm ≤ weighted_sourceExceptionalBound F η := by
  apply HeckeExceptionalRows.row_norm_bound _
    (fun P hP=> prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP))
  apply weighted_fixed_inducing_free_support η (internalQ (weighted_sourceFixedIdeal F) η)
    (internalQ_ne_zero _ (weighted_sourceFixedIdeal_ne_zero F) η)
    (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top F) η)
    (inf_le_left.trans (weighted_sourceFixedIdeal_le_72 F)) inf_le_right
    (fixedBadMask*idealGenerator 1)
    (mul_ne_zero fixedBadMask_ne_zero (idealGenerator_ne_zero _ one_ne_zero))
    ((dvd_mul_right _ _).trans (dvd_mul_right _ _))
    ((dvd_mul_left _ _).trans (dvd_mul_right _ _)) u hu

theorem weighted_eventually_source_no_exceptional (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (η : Character) :
    ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters F.modulus ⊤),∀u : FreeRow,
      Z^(1/100:ℝ) ≤ rowNorm u →
      ¬weighted_sourceExceptional F (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label) u := by
  have hh : ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters F.modulus ⊤),
      (weighted_sourceExceptionalBound F (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label):ℝ)< Z^(1/100:ℝ) := by
    apply Filter.eventually_all.mpr
    intro label
    exact (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/100)).eventually (eventually_gt_atTop _)
  filter_upwards [hh] with Z hz
  intro label u hu hex
  have hb : rowNorm u ≤ (weighted_sourceExceptionalBound F
      (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label):ℝ) := by
    change ((Ideal.span {u.val}).absNorm:ℝ) ≤ _
    exact_mod_cast weighted_source_exceptional_norm F _ u hex
  exact (not_lt_of_ge (hu.trans hb)) (hz label)

end SevenEighths.Cycle25CenteredMomentNaturalFixedRaySource

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.MomentNaturalFixedRaySourceFreeExceptional -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.SlotLengths ; sha256 2ede21ea3758219ef65c85f5566be816d590e9d44dd8cef9ab17d877a1794b7d -/
section


namespace Cycle25.HighParameters
noncomputable section
open scoped BigOperators

theorem exists_distinct_slot_lengths (L : ℝ) (hL : 0 < L) :
    ∃N : ℕ,0 < N ∧ ∃ell : Fin N→ℝ,Function.Injective ell ∧
      (∀j,0 < ell j ∧ ell j < L) ∧ (∑j,ell j)=Cycle25.ell := by
  have hscale : 0 < 6*Cycle25.ell := mul_pos (by norm_num) ell_pos
  obtain ⟨N,hN,old,hi,hb,hs⟩ := OAI.SevenEighths.Parameters.exists_distinct_slot_lengths
    (L/(6*Cycle25.ell)) (by positivity)
  refine ⟨N,hN,(fun j=>(6*Cycle25.ell:ℝ)*old j),?_,?_,?_⟩
  · intro j k he
    apply hi
    exact (mul_left_cancel₀ hscale.ne' he)
  · intro j
    constructor
    · exact mul_pos hscale (hb j).1
    · have hh := (hb j).2
      have hc := (lt_div_iff₀ hscale).mp hh
      nlinarith only [hc]
  · rw [←Finset.mul_sum,hs]
    ring

theorem exists_physical_slot_lengths (dmin dmax mesh R : ℝ)
    (hdmin : 0 < dmin) (hd : dmin ≤ dmax) (hm : 0 < mesh) (hR : 0 < R) :
    ∃N : ℕ,0 < N ∧ ∃ell : Fin N→ℝ,∃rmin : ℝ,0 < rmin ∧
      Function.Injective ell ∧ (∑j,ell j)=Cycle25.ell ∧
      (∀j,0 < ell j ∧ dmax*rmin ≤ ell j ∧ ell j ≤ dmin*mesh ∧ ell j ≤ dmin*R) ∧
      (∀d : ℝ,dmin ≤ d → d ≤ dmax → ∀j,rmin ≤ ell j/d ∧ ell j/d ≤ mesh ∧ ell j/d ≤ R) := by
  obtain ⟨N,hN,ell,hi,he,hS⟩ := exists_distinct_slot_lengths (dmin*min mesh R)
    (mul_pos hdmin (lt_min hm hR))
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0,hN⟩,Finset.mem_univ _⟩
  obtain ⟨j,hj,hjmin⟩ := Finset.exists_min_image Finset.univ ell hne
  have hmax : 0 < dmax := hdmin.trans_le hd
  let rmin := ell j/(2*dmax)
  have hr : 0 < rmin := div_pos (he j).1 (by positivity)
  have hlo (k : Fin N) : dmax*rmin ≤ ell k := by
    have hk := hjmin k (Finset.mem_univ k)
    have hiden : dmax*rmin=ell j/2 := by dsimp [rmin]; field_simp
    rw [hiden]
    linarith [(he j).1]
  have hup (k : Fin N) : ell k ≤ dmin*mesh ∧ ell k ≤ dmin*R := by
    constructor
    · exact (he k).2.le.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hdmin.le)
    · exact (he k).2.le.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hdmin.le)
  refine ⟨N,hN,ell,rmin,hr,hi,hS,fun k=>⟨(he k).1,hlo k,(hup k).1,(hup k).2⟩,?_⟩
  intro d hd' hd'' k
  have hd0 : 0 < d := hdmin.trans_le hd'
  refine ⟨(le_div_iff₀ hd0).mpr ?_,(div_le_iff₀ hd0).mpr ?_,(div_le_iff₀ hd0).mpr ?_⟩
  · exact (by nlinarith : rmin*d ≤ dmax*rmin).trans (hlo k)
  · exact (hup k).1.trans (by nlinarith)
  · exact (hup k).2.trans (by nlinarith)

end
end Cycle25.HighParameters

/- Adapted from weighted numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0. -/
end
/- END ORIGINAL MODULE Cycle25.Assembly.SlotLengths -/

/- BEGIN ORIGINAL MODULE Cycle25.Energy.Physical.PhysicalMoment ; sha256 dad4ece50f86fd832a4a026b30d76a6a14cac659ece3a14450fbf93a31304dd0 -/
section





namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
namespace SevenEighths.Cycle25WeightedNumeratorPhysical
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CenteredMomentDetectorDictionary CenteredMomentNaturalFixedRaySource
open CenteredMomentNaturalRowSource CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentRetainedEnergy CenteredMomentPositiveSummability CenteredMomentInductionEnergy
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorEnergyInitialState
open CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondHeightFamily ConcreteTraceCRT CenteredMomentRowNorm ActualEisensteinCubic
local notation "O" => HeckeFamily.O

/-- The physical numerator and the source moment character have identical coefficients,
including all natural zero extensions. -/
theorem numerator_polynomial_eq_moment (S : Finset (Ideal O))
    (hS : ∀P∈S, Prime P) (hbad : CanonicalQuadraticSieve.fixedBadPrimes ⊆ S)
    (u : FreeRow) (W : ℝ → ℂ) (X σ t : ℝ) :
    polynomial (rowCharacter S hS u) false W X σ t =
      polynomial ((momentData (fixedSourcePrincipal S hS)).character (momentElement u))
        false W X σ t := by
  unfold polynomial
  congr 1
  apply tsum_congr
  intro I
  simp only [summand,coefficient,Bool.false_eq_true,ite_false,
    numerator_moment_coeff S hS hbad u I.val]

lemma twistProfile_zero_zero (W : ℝ → ℂ) : twistProfile W 0 0 = W := by
  funext x
  simp [twistProfile,HeckeDyadic.shift]

/-- Arbitrary two profiles and scales, rather than only detector witness profiles. -/
theorem actual_pair_source_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (η : Character) (u : FreeRow) (W₁ W₂ : ℝ → ℂ)
    (slots : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hP : ∀i, 0 < P i) :
    positiveSlotRow η (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 u.val
      W₁ W₂ slots β P 0 X₁ X₂ =
      polynomial ((momentData η).character (momentElement u)) false W₁ X₁ 0 0 *
      polynomial ((momentData η).character (momentElement u)) false W₂ X₂ 0 0 *
        ∏i, normalizedSlot η rowMaskElement 1 u.val (slots i) (β i) 0 (P i) := by
  rw [natural_unit_mask_positive (naturalRow η u.val u.property.1)]
  rw [←rowMaskElement_eq_fixed]
  have he := positiveSlotRow_eq_product η ((momentData η).character (momentElement u))
    rowMaskElement 1 u.val
    (by simpa only [momentData,momentElement,one_mul] using
      (momentData η).character_spec (momentElement u))
    W₁ W₂ slots β P X₁ X₂ 0 0 hX₁ hX₂ hP
  simpa only [twistProfile_zero_zero] using he

/-- Restricting the actual nonnegative radial energy to a finite physical row set. -/
theorem finite_actual_pair_le_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rows : Finset FreeRow) (η : Character) (Q : Ideal O)
    (Φ : 𝓢(ℝ,ℂ)) (U bΦ δ : ℝ) (hU : 1 ≤ U) (hδ : 0 ≤ δ)
    (hs : Function.support (Φ:ℝ→ℂ) ⊆ Set.Iic bΦ) (hp : ∀x, 0 ≤ (Φ x).re)
    (hη : (η.modulus.absNorm:ℝ) ≤ U^δ)
    (hrows : ∀u∈rows, rowNorm u ≤ U)
    (hkeep : ∀u∈rows, initialKeep η Q u.val)
    (hone : ∀x∈Set.Icc (0:ℝ) 1, Φ x = 1)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ : ℝ)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁) (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (slots : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (hP : ∀i, 0 < P i) :
    (∑u∈rows, ‖polynomial ((momentData η).character (momentElement u)) false W₁ X₁ 0 0 *
      polynomial ((momentData η).character (momentElement u)) false W₂ X₂ 0 0 *
        ∏i, normalizedSlot η rowMaskElement 1 u.val (slots i) (β i) 0 (P i)‖^2)
      ≤ energy η (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 0 W₁ W₂
        slots β P X₁ X₂ (initialKeep η Q) Φ U := by
  let m := fixedBadMask*ConcretePrimeRowBridge.idealGenerator (1:Ideal O)
  let f (z : O) : ℝ := if initialKeep η Q z then
    ‖positiveSlotRow η m 1 z W₁ W₂ slots β P 0 X₁ X₂‖^2*
      (Φ (‖eisEmbedding z‖^2/U)).re else 0
  have hUp : 0 < U := zero_lt_one.trans_le hU
  obtain ⟨B,hB⟩ := product_bounded η m 1 0
    (Real.sqrt (X₁*X₂*∏i,P i):ℂ)⁻¹ W₁ W₂ b₁ b₂ X₁ X₂
    hs₁ hs₂ hX₁ hX₂ slots β
  have hsum : Summable f :=
    bounded_radial_summable _ B hB (initialKeep η Q) Φ U hUp
  have hf0 (z : O) : 0 ≤ f z := by
    dsimp [f]
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (hp _)
    · exact le_rfl
  have he (u : FreeRow) (hu : u ∈ rows) :
      f u.val = ‖polynomial ((momentData η).character (momentElement u)) false W₁ X₁ 0 0 *
        polynomial ((momentData η).character (momentElement u)) false W₂ X₂ 0 0 *
          ∏i, normalizedSlot η rowMaskElement 1 u.val (slots i) (β i) 0 (P i)‖^2 := by
    have hx : ‖eisEmbedding u.val‖^2/U ∈ Set.Icc (0:ℝ) 1 := by
      refine ⟨div_nonneg (sq_nonneg _) hUp.le,(div_le_one hUp).mpr ?_⟩
      rw [eisEmbedding_norm_sq_eq_absNorm_span]
      exact hrows u hu
    dsimp [f]
    rw [if_pos (hkeep u hu),hone _ hx,Complex.one_re,mul_one]
    rw [actual_pair_source_identity η u W₁ W₂ slots β P X₁ X₂ hX₁ hX₂ hP]
  calc
    _ = ∑u∈rows, f u.val := Finset.sum_congr rfl (fun u hu => (he u hu).symm)
    _ = ∑z∈rows.image Subtype.val, f z := by
      rw [Finset.sum_image (fun x _ y _ hxy => Subtype.val_injective hxy)]
    _ ≤ ∑'z, f z := Summable.sum_le_tsum _ (fun z _ => hf0 z) hsum
    _ = _ := rfl

end SevenEighths.Cycle25WeightedNumeratorPhysical
end
end OAI

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 uses the common-mesh variable-kappa positive endpoint and unconditional zero endpoint. -/
end
/- END ORIGINAL MODULE Cycle25.Energy.Physical.PhysicalMoment -/
