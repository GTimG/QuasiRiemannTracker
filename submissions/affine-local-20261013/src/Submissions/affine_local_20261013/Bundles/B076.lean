/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B012
import Submissions.affine_local_20261013.Bundles.B033
import Submissions.affine_local_20261013.Bundles.B037
import Submissions.affine_local_20261013.Bundles.B041
import Submissions.affine_local_20261013.Bundles.B072
import Submissions.affine_local_20261013.Bundles.B073
import Submissions.affine_local_20261013.Bundles.B074
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.NonfloorDictionary
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Reflection.LowInactiveEnergy

/- BEGIN ORIGINAL MODULE Analytic.JointRetainedData ; sha256 7a02030ade4692aabe104d182986757f34906485bf421f79bdd8b92f154fe671 -/
section


/-! Every nonzero complete retained fiber has two actual buffered products
at the same reconstructed row. Their source identities, admissibility and
reduction lengths are retained before choosing a maximizing fiber. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff
open Set
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification HeckeDyadic ConcretePrimeRowBridge
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentRetainedProfile CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentDivisorAllocation CenteredMomentPrimeSlot CenteredMomentHeckeExpansion
open CenteredMomentDivisorRectangle CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentChildRows
local notation "O" => HeckeFamily.O

namespace CommonSecondKernelLabel
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def fullLeftLength (s : CommonSecondKernelLabel ι) (Z : ℝ) (q : s.FullRetainedFiber) : ℝ :=
  Real.logb Z (secondCommonVolume s.input (s.firstCommon*s.second.val.1) q.2.1)-
    Real.logb Z (formalReductionFactor q.1 q.2.2.2.1 (fun i => s.input.P i.val))

def fullRightLength (s : CommonSecondKernelLabel ι) (Z : ℝ) (q : s.FullRetainedFiber) : ℝ :=
  Real.logb Z (secondCommonVolume s.input (s.firstCommon*s.second.val.2) q.2.2.1)-
    Real.logb Z (formalReductionFactor q.1 q.2.2.2.2.1 (fun i => s.input.P i.val))

end CommonSecondKernelLabel

theorem actual_retained_buffered_data
    (W₁ W₂ : ℝ → ℂ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hs₁ : Function.support W₁ ⊆ Icc a₁ b₁) (hW₁ : ContDiff ℝ ∞ W₁)
    (hs₂ : Function.support W₂ ⊆ Icc a₂ b₂) (hW₂ : ContDiff ℝ ∞ W₂) :
    ∃ profileBound : ℕ → ℝ, (∀ k, 0 < profileBound k) ∧
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
        (orders : Finset ι → ℕ) (edge e : ℝ), edge ≤ 1 → e ≤ 1/1000 →
      ∀ (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
        (hH : RayOrthogonality.globalUnits M ≤ H)
        (η : Character) (w : NonzeroElement) (parentL parentR : JointParentLabel η)
        (NL : NaturalRow parentL.val w.val) (NR : NaturalRow parentR.val w.val)
        (punctureL punctureR : Ideal O) (hpunctureL : punctureL ≠ 0) (hpunctureR : punctureR ≠ 0)
        (s : CommonSecondKernelLabel ι) (Ds : Finset (Ideal O)) (z : O) (t₁ t₂ Z d : ℝ)
        (η₀ : ι → Character) (V : ι → ℝ → ℂ) (alo bhi : ι → ℝ)
        (bin : ℕ) (Rwidth τ ηaux σmin σmax T : ℝ),
      s.input.W₁ = W₁ → s.input.W₂ = W₂ →
      (∀ i, s.input.slots i = primePool M H (bhi i) (s.input.P i)) →
      (∀ i I, s.input.ν i I = idealCoeff (η₀ i).inverse I) → (∀ i, s.input.W i = V i) →
      (∀ I : Ideal O, rowWeight (childCharacter s.parent s.leftRay)
        (fixedBadMask*idealGenerator (s.puncture*(s.firstCommon*s.second.val.1)))
        s.toKernelLabel.frequency z t₁ I =
        rowWeight parentL.val (fixedBadMask*idealGenerator punctureL) 1 w.val t₁ I) →
      (∀ I : Ideal O, rowWeight (childCharacter s.parent (s.rightRay⁻¹))
        (fixedBadMask*idealGenerator (s.puncture*(s.firstCommon*s.second.val.2)))
        s.toKernelLabel.frequency (-z) t₂ I =
        rowWeight parentR.val (fixedBadMask*idealGenerator punctureR) 1 w.val t₂ I) →
      1 < Z → d ≠ 0 → 1 < Z^d → 0 ≤ Rwidth →
      s.input.X₁ ≤ (Z^d)^Rwidth → s.input.X₂ ≤ (Z^d)^Rwidth →
      s.input.Y₁ ≤ (Z^d)^Rwidth → s.input.Y₂ ≤ (Z^d)^Rwidth →
      (∀ i, 1 ≤ s.input.P i ∧ s.input.P i ≤ (Z^d)^Rwidth) → σmin ≤ 0 → 0 ≤ σmax →
      (∀ label, (bufferedProductFamily M H hH η₀
        (excluded NL.character punctureL) label).modulus.absNorm ≤ Z^d) →
      (∀ label, (bufferedProductFamily M H hH η₀
        (excluded NR.character punctureR) label).modulus.absNorm ≤ Z^d) →
      |t₁|+Z^τ/2 ≤ (3*bin+2 : ℕ)*Z^τ → |t₂|+Z^τ/2 ≤ (3*bin+2 : ℕ)*Z^τ →
      (3+(3*bin+2 : ℕ)*Z^τ)^4 ≤ (Z^d)^ηaux →
      (3+(3*bin+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^ηaux →
      (∀ i, 2*(|Real.log (alo i)|+|Real.log (bhi i)|)+1 ≤ Real.log (s.input.P i)) →
      3*(bin+1 : ℕ)*Z^τ ≤ T →
      ∀ q ∈ s.liveFullRetainedFiber Ds t₁ t₂ z,
      ∃ DL DR : SurvivingBufferedData η w ι orders profileBound edge e,
        s.fullFiberValue t₁ t₂ z q =
          ‖DL.value M H η₀ V bhi Z d‖*‖DR.value M H η₀ V bhi Z d‖ ∧
        d*DL.length ≤ s.fullLeftLength Z q+Real.logb Z (max 1 b₁*max 1 b₂) ∧
        d*DR.length ≤ s.fullRightLength Z q+Real.logb Z (max 1 b₁*max 1 b₂) ∧
        DL.Admissible M H hH η₀ alo bhi Rwidth τ ηaux σmin σmax Z d T ∧
        DR.Admissible M H hH η₀ alo bhi Rwidth τ ηaux σmin σmax Z d T := by
  obtain ⟨profileBound,hprofile,hdata⟩ := actual_common_retained_admissible
    W₁ W₂ a₁ b₁ a₂ b₂ ha₁ ha₂ hs₁ hW₁ hs₂ hW₂
  refine ⟨profileBound,hprofile,?_⟩
  intro ι instι instDι orders edge e hedge he M instM H hH η w parentL parentR NL NR
    punctureL punctureR hpunctureL hpunctureR s Ds z t₁ t₂ Z d η₀ V alo bhi bin
    Rwidth τ ηaux σmin σmax T hsW₁ hsW₂ hslots hν hW hrowL hrowR
    hZ hd hbase hR hX₁ hX₂ hY₁ hY₂ hP hσmin hσmax hcondL hcondR
    hfreqL hfreqR hfour htwo hlog hbuffer q hq
  obtain ⟨hnL,hnR⟩ := s.liveFullRetainedFiber_nonzero Ds t₁ t₂ z q hq
  obtain ⟨DL,hslotsL,hnormL,hlenL,hadL⟩ := hdata orders edge e hedge he M H hH
    η w parentL NL punctureL hpunctureL s.input (s.firstCommon*s.second.val.1) s.puncture
    q.2.1 (childCharacter s.parent s.leftRay) s.toKernelLabel.frequency z t₁
    q.1 q.2.2.2.1 q.2.2.2.2.2.1 Z d η₀ V alo bhi bin Rwidth τ ηaux σmin σmax T
    hsW₁ hsW₂ hslots hν hW hrowL hZ hd hbase hR hX₁ hX₂ hY₁ hY₂ hP hσmin hσmax
    hcondL hfreqL hfour htwo (fun i => hlog i.val.val) hbuffer hnL
  obtain ⟨DR,hslotsR,hnormR,hlenR,hadR⟩ := hdata orders edge e hedge he M H hH
    η w parentR NR punctureR hpunctureR s.input (s.firstCommon*s.second.val.2) s.puncture
    q.2.2.1 (childCharacter s.parent (s.rightRay⁻¹)) s.toKernelLabel.frequency (-z) t₂
    q.1 q.2.2.2.2.1 q.2.2.2.2.2.2 Z d η₀ V alo bhi bin Rwidth τ ηaux σmin σmax T
    hsW₁ hsW₂ hslots hν hW hrowR hZ hd hbase hR hX₁ hX₂ hY₁ hY₂ hP hσmin hσmax
    hcondR hfreqR hfour htwo (fun i => hlog i.val.val) hbuffer hnR
  refine ⟨DL,DR,?_,hlenL,hlenR,hadL,hadR⟩
  exact congrArg₂ (fun x y : ℝ => x*y) hnormL hnormR

#print axioms actual_retained_buffered_data
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointRetainedData -/

/- BEGIN ORIGINAL MODULE Cycle25.Energy.Physical.CertifiedFourier ; sha256 bfcf0da80cfcd5f49fae665f71b0d88f284a251f74e327dd62ab811419c413cc -/
section



namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter
namespace SevenEighths.Cycle25WeightedNumeratorPhysical
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CenteredMomentDetectorDictionary CenteredMomentNaturalFixedRaySource
open CenteredMomentHeckeSlots CenteredMomentInductionEnergy CenteredMomentEnergyBands
open CenteredMomentDetectorEnergyInitialState CenteredMomentEnergyState
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentRowNorm
open CenteredMomentWholeSlotDeletion CenteredMomentRetainedEnergy QuadraticInitialBound
open CenteredMomentPrimeSlot CenteredMomentDetectorPlainFiberSource
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
set_option maxHeartbeats 800000

lemma eventually_fixed_source_keep {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (η : Character) :
    ∀ᶠU:ℝ in atTop, ∀u:FreeRow, U^(1/100:ℝ) ≤ rowNorm u →
      initialKeep η (internalQ (weighted_sourceFixedIdeal F) η) u.val := by
  have ht : ∀ᶠU:ℝ in atTop, (weighted_sourceExceptionalBound F η:ℝ) < U^(1/100:ℝ) :=
    (tendsto_rpow_atTop (by norm_num:(0:ℝ)<1/100)).eventually (eventually_gt_atTop _)
  filter_upwards [ht] with U hU
  intro u hu
  apply (weighted_source_keep_iff F η u).mpr
  intro hh
  have hn : rowNorm u ≤ (weighted_sourceExceptionalBound F η:ℝ) := by
    change ((Ideal.span {u.val}).absNorm:ℝ) ≤ _
    exact_mod_cast weighted_source_exceptional_norm F η u hh
  exact (not_lt_of_ge (hu.trans hn)) hU

/-- Direct certified fixed-scale Fourier moments for the actual reflected
numerator and arbitrary selected physical prime slots. Both Fourier frequencies
are unrestricted; the degree and constant precede every scale and height. -/
theorem certified_reflected_fourier_moment {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (κ : ℝ) (hκlo : 7/10 ≤ κ) (hκhi : κ ≤ 3/4)
    (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1 ≤ κ) :
    ∃degree J:ℕ, ∃C:ℝ, 0 < C ∧ ∀ᶠU:ℝ in atTop,
      1 < U ∧ ∀rows:Finset FreeRow,
      (∀u∈rows, U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀T:Finset (Fin D.N), ∀width:T→ℝ, ∀z:T→ℂ, ∀height:ℝ,
      (∀i, 0 ≤ width i) →
      (∀i, width i ≤ Cycle25.Energy.commonMesh 2 0 1 (D.t/4)) →
      (∀i, (z i).re = 17/50) → 0 ≤ height → (∀i, |(z i).im| ≤ height) →
      ∀X₁ X₂:ℝ, 0 < X₁ → 0 < X₂ → X₁ ≤ U → X₂ ≤ U →
      length U X₁+length U X₂+6*κ*(∑i,width i) ≤ 1 →
      ∀j k:Fin 2, ∀v w:ℝ,
      (∑u∈rows, ‖polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
        (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (2*Real.pi*v) *
        polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
          (scaleTest (fun y:ℝ=>(annulus y:ℂ)) k) X₂ 0 (2*Real.pi*w) *
        ∏i,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (U^(width i)) (z i)‖^2)
        ≤ (C*(1+height)^degree*U^(1+D.t))*((1+‖v‖)^J)^2*((1+‖w‖)^J)^2 := by
  obtain ⟨bΦ,hbΦ,hsΦ⟩ := radialMajorant_support_bound
  obtain ⟨degree,control,henergy⟩ := weighted_terminal_positive_energy F κ hκlo hκhi hbeta hκbeta bΦ hbΦ
  let η := fixedSourcePrincipal F.S F.exclusions.prime
  obtain ⟨Cp,hCp,hbound⟩ := henergy η
  obtain ⟨J,Cprofile,hCprofile,hprofile⟩ := numerator_fourier_profiles_control control
  let C := Cp*(1+diagonalControl radialMajorant)*Cprofile
  have hC : 0 < C := by
    have hd := diagonalControl_nonneg radialMajorant
    dsimp [C]; positivity
  have hmod : ∀ᶠU:ℝ in atTop, (η.modulus.absNorm:ℝ) ≤ U^(D.t/4) :=
    (tendsto_rpow_atTop (div_pos D.t_pos (by norm_num))).eventually (eventually_ge_atTop _)
  refine ⟨degree,J,C,hC,?_⟩
  filter_upwards [hbound,hmod,eventually_fixed_source_keep F η,eventually_gt_atTop (1:ℝ)]
    with U henergy hmod hkeep hU
  refine ⟨hU,?_⟩
  intro rows hrows T width z height hw hwmax hz hh hzim X₁ X₂ hX₁ hX₂ hX₁max hX₂max hcap j k v w
  have hδ : 0 ≤ D.t/4 := div_nonneg D.t_pos.le (by norm_num)
  have hδtop : D.t/4 ≤ 1 := by linarith [D.t_small]
  have hc : length U X₁+length U X₂+6*κ*(∑i,width i) ≤ 1+D.t/4 := by linarith
  have he := finite_physical_pair_positiveAt F rows η radialMajorant U bΦ (D.t/4)
    (Cycle25.Energy.commonMesh 2 0 1 (D.t/4)) (D.t/4) κ
    hU.le hδ hδtop hsΦ radialMajorant_nonneg hmod (fun u hu=>(hrows u hu).2)
    (fun u hu=> hkeep u (hrows u hu).1) radialMajorant_one degree control Cp henergy.2
    T width z height hw hwmax hz hh hzim (numeratorFourierProfiles j k v w)
    X₁ X₂ hX₁ hX₂ hX₁max hX₂max hc
  have heq :
      (∑u∈rows, ‖polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
        (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (2*Real.pi*v) *
        polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
          (scaleTest (fun y:ℝ=>(annulus y:ℂ)) k) X₂ 0 (2*Real.pi*w) *
        ∏i,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (U^(width i)) (z i)‖^2) =
      (∑u∈rows, ‖polynomial ((momentData η).character (momentElement u)) false
        ((numeratorFourierProfiles j k v w).profile 0) X₁ 0 0 *
        polynomial ((momentData η).character (momentElement u)) false
        ((numeratorFourierProfiles j k v w).profile 1) X₂ 0 0 *
        ∏i,normalizedSlot η rowMaskElement 1 u.val (primePool F.modulus ⊤ 2 (U^(width i)))
          (physicalSlotCoefficient η F.W (U^(width i)) (z i)) 0 (U^(width i))‖^2) := by
    apply Finset.sum_congr rfl
    intro u hu
    dsimp only [η]
    simp_rw [numerator_fourier_polynomial_zero,numerator_fourier_polynomial_one,
      source_physical_slot_conj F u _ _ (Real.rpow_pos_of_pos (zero_lt_one.trans hU) _),
      norm_mul,inverse_annular_norm_eq F u j v X₁ hX₁,
      inverse_annular_norm_eq F u k w X₂ hX₂,←map_prod,Complex.norm_conj]
  rw [heq]
  apply he.trans
  have hd := diagonalControl_nonneg radialMajorant
  have hp := hprofile j k v w
  have hx : U^(1+D.t/4+D.t/4) ≤ U^(1+D.t) :=
    Real.rpow_le_rpow_of_exponent_le hU.le (by linarith [D.t_pos])
  calc
    _ ≤ (Cp*(1+diagonalControl radialMajorant))*
        (Cprofile*((1+‖v‖)^J)^2*((1+‖w‖)^J)^2)*
        (1+height)^degree*U^(1+D.t) := by
      apply mul_le_mul _ hx (Real.rpow_nonneg (zero_lt_one.trans hU).le _) (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hCp.le) hp
        (sq_nonneg _) (by positivity)
    _ = _ := by dsimp [C]; ring

end SevenEighths.Cycle25WeightedNumeratorPhysical
end
end OAI

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 keeps the original physical family and explicit variable-kappa capacity. -/
end
/- END ORIGINAL MODULE Cycle25.Energy.Physical.CertifiedFourier -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.SourceSelection ; sha256 b1b591716a2fd4c0af0e55ea1136952fee01b54bd31c73d0a525825aff2db3d4 -/
section





/-! A single selected prime subset for every row in an actual full amplitude
class, with only the numerator's error slots masked out of the lower mean. -/
noncomputable section
open scoped Classical BigOperators
namespace Cycle25.Numerator
open OAI OAI.SevenEighths HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst
open HeckeDetectorFiberPartition ProbeHighRowFamily Cycle25ProbeFinalAssembly Cycle25DetectorRowCount
open ProbePhysical HeckeFamily HeckeInverseAmplification

 theorem masked_main_product_upper {α : Type*} [Fintype α] [DecidableEq α]
    (main : Finset α) (width g : α→ℝ) (U mesh : ℝ) (Q : α→ℂ)
    (hU : 1 ≤ U) (hm : 0 ≤ mesh) (hw : ∀j,0 ≤ width j)
    (hL : 0 < ∑j,width j)
    (hQ : ∀j∈main,‖Q j‖ ≤ U^(width j*(g j+mesh))) :
    ‖∏j∈main,Q j‖ ≤ U^(weightedMean Finset.univ width (maskedGain main g)*(∑j,width j)+
      mesh*(∑j,width j)) := by
  have hUpos : 0 < U := zero_lt_one.trans_le hU
  have he : (∑j,width j*maskedGain main g j)=∑j∈main,width j*g j := by
    calc
      _ = ∑j∈main,width j*maskedGain main g j :=
        (Finset.sum_subset (Finset.subset_univ main) (fun j _ hj=> by simp [maskedGain,hj])).symm
      _ = _ := Finset.sum_congr rfl (fun j hj=> by simp [maskedGain,hj])
  have hmean : weightedMean Finset.univ width (maskedGain main g)*(∑j,width j)=
      ∑j∈main,width j*g j := by
    unfold weightedMean
    rw [div_mul_cancel₀ _ hL.ne',he]
  have hsum : ∑j∈main,width j ≤ ∑j,width j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ main) (fun j _ _=> hw j)
  calc
    _ ≤ ∏j∈main,U^(width j*(g j+mesh)) := by
      rw [norm_prod]
      exact Finset.prod_le_prod₀ (fun j _=> norm_nonneg _) hQ
    _ = U^(∑j∈main,width j*(g j+mesh)) := (Real.rpow_sum_of_pos hUpos _ _).symm
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le hU
      rw [hmean]
      have hh := mul_le_mul_of_nonneg_left hsum hm
      have he' : (∑j∈main,width j*(g j+mesh))=
          (∑j∈main,width j*g j)+mesh*(∑j∈main,width j) := by
        rw [Finset.mul_sum,←Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      rw [he']
      linarith

/-- Exact identification of the source-count physical family with canonical
prime amplitudes at the original physical slot lengths. -/
theorem source_count_physical_eq {Δ : ℝ} (D : HighParameters.HighData Δ)
    (F : WeightedSourceData D.toMomentData) (Z d : ℝ) (hZ : 0 < Z) (hd : d≠0)
    (z : ℂ) (u : FreeRow) (j : Fin D.N) :
    physical F.modulus ⊤ (fun u : FreeRow=> u.val) (fun _ y=>(F.w y:ℂ)) (fun _=>2)
      (fun j=> D.ell j/d) (fun _=> z) (Z^d) u j=
      HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z := by
  calc
    _ = HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val (fun y=>(F.w y:ℂ)) 2 (Z^(D.ell j)) z :=
      source_physical_amplitude F.modulus ⊤ D.ell (fun _ y=>(F.w y:ℂ)) Z d 2 z hZ hd u j
    _ = _ := by
      congr 1
      funext y
      exact (F.complex_eq y).symm

/-- Common selection on a canonical full amplitude class. The analytic upper
premise is supplied by weighted_source_prime_bins; lower spikes are automatic. -/
theorem source_class_main_selection {Δ : ℝ} (D : HighParameters.HighData Δ)
    (F : WeightedSourceData D.toMomentData)
    (hfine : ∀j,D.ell j ≤ Cycle25.sourceMesh D.t/200)
    (Z d v δ : ℝ) (hZ : 1 < Z) (hd : (1/2:ℝ) ≤ d) (hv : 0 ≤ v) (hδ : 0 ≤ δ)
    (z : ℂ) (rows : Finset FreeRow) (main : Finset (Fin D.N))
    (bin : BinLabel (Finset.univ : Finset (Fin D.N)) (δ/2) D.t)
    (hne : (amplitudeRows rows Finset.univ (Z^d) (δ/2) D.t D.t_pos (fun j=> D.ell j/d)
      (fun u j=> HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z) bin).Nonempty) :
    let Q := fun (u : FreeRow) j=> HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z
    let rows' := amplitudeRows rows Finset.univ (Z^d) (δ/2) D.t D.t_pos (fun j=> D.ell j/d) Q bin
    let g := binValue Finset.univ (δ/2) D.t bin
    let q := weightedMean Finset.univ (fun j=> D.ell j/d) (maskedGain main g)
    0 ≤ q ∧ q ≤ δ/2 ∧ ∃selected : Finset (Fin D.N),selected⊆main ∧
      (∑j∈selected,D.ell j/d) ≤ SlotSelection.reflectedCapacity D.momentKappa d v ∧
      ∀u∈rows',
        (Z^d)^(2*q*SlotSelection.reflectedCapacity D.momentKappa d v-
          δ*Cycle25.sourceMesh D.t) ≤ ‖∏j∈selected,Q u j‖^2 ∧
        ((∀j,‖Q u j‖ ≤ (Z^(D.ell j))^(HeckePrimeAmplitudeBins.amplitude (Z^(D.ell j)) (δ/2) D.t (Q u j)+D.t)) →
          ‖∏j∈main,Q u j‖ ≤ (Z^d)^(q*(ell/d)+D.t*(ell/d))) := by
  dsimp only
  let Q := fun (u : FreeRow) j=> HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z
  let rows' := amplitudeRows rows Finset.univ (Z^d) (δ/2) D.t D.t_pos (fun j=> D.ell j/d) Q bin
  let g := binValue Finset.univ (δ/2) D.t bin
  have hdpos : 0 < d := by linarith
  have hZpos : 0 < Z := zero_lt_one.trans hZ
  have hU : 1 < Z^d := Real.one_lt_rpow hZ hdpos
  have hscale (j : Fin D.N) : (Z^d)^(D.ell j/d)=Z^(D.ell j) := by
    rw [←Real.rpow_mul hZpos.le,mul_div_cancel₀ _ hdpos.ne']
  have hgfull : ∀j,0 ≤ g j ∧ g j ≤ δ/2 := by
    obtain ⟨u,hu⟩ := hne
    intro j
    have he := amplitude_class_value rows Finset.univ (Z^d) (δ/2) D.t D.t_pos
      (fun j=> D.ell j/d) Q bin u hu j (Finset.mem_univ j)
    dsimp only [g]
    rw [←he]
    exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by positivity)
  have hg : ∀j,0 ≤ maskedGain main g j ∧ maskedGain main g j ≤ δ/2 := by
    intro j
    unfold maskedGain
    split_ifs
    · exact hgfull j
    · exact ⟨le_rfl,by positivity⟩
  obtain ⟨hqeq,hq0,hqtop,T,hT,hTpos,hTcap,hgain,hgain',hspike⟩ :=
    SlotSelection.highData_weighted_selection D hfine d v δ hd hv hδ main
      (maskedGain main g) hg (fun j hj=> by simp [maskedGain,hj])
  refine ⟨hq0,hqtop,T,hT,hTcap,?_⟩
  intro u hu
  have hgrow (j : Fin D.N) : HeckePrimeAmplitudeBins.amplitude (Z^(D.ell j)) (δ/2) D.t (Q u j)=g j := by
    have he := amplitude_class_value rows Finset.univ (Z^d) (δ/2) D.t D.t_pos
      (fun j=> D.ell j/d) Q bin u hu j (Finset.mem_univ j)
    simpa only [hscale] using he
  refine ⟨?_,?_⟩
  · apply hspike (Z^d) hU.le (Q u)
    intro j hj
    have hjmain : j∈main := by
      by_contra hm
      simp only [maskedGain,ite_eq_right hm,lt_self_iff_false] at hj
    have hgm : maskedGain main g j=g j := by simp [maskedGain,hjmain]
    have hpos : 0 < HeckePrimeAmplitudeBins.amplitude ((Z^d)^(D.ell j/d)) (δ/2) D.t (Q u j) := by
      rw [hscale,hgrow]
      rwa [hgm] at hj
    have hh := HeckePrimeAmplitudeBins.squared_spike (Z^d) (D.ell j/d) (δ/2) D.t
      (Q u j) hU (div_pos (D.slots_bounds j).1 hdpos) D.t_pos hpos
    simpa only [hscale,hgrow,hgm] using hh
  · intro hupper
    have hL : (∑j,D.ell j/d)=ell/d := by rw [←Finset.sum_div,D.slots_sum]
    have hh := masked_main_product_upper main (fun j=> D.ell j/d) g (Z^d) D.t (Q u)
      hU.le D.t_pos.le (fun j=>(div_pos (D.slots_bounds j).1 hdpos).le)
      (by rw [hL];exact div_pos ell_pos hdpos) (by
        intro j hj
        calc
          _ ≤ (Z^(D.ell j))^(g j+D.t) := by
            have he := hupper j
            change ‖Q u j‖ ≤ (Z^(D.ell j))^(HeckePrimeAmplitudeBins.amplitude (Z^(D.ell j)) (δ/2) D.t (Q u j)+D.t) at he
            rwa [hgrow] at he
          _ = _ := by rw [←hscale j,←Real.rpow_mul (by positivity)])
    simpa only [hL] using hh


/-- The positive real square root of the selected squared spike. -/
theorem squared_selected_lower (U q cap δ mesh : ℝ) (Q : ℂ) (hU : 0 < U)
    (hQ : U^(2*q*cap-δ*mesh) ≤ ‖Q‖^2) :
    U^(q*cap-δ*mesh/2) ≤ ‖Q‖ := by
  apply (sq_le_sq₀ (Real.rpow_nonneg hU.le _) (norm_nonneg _)).mp
  have he : (U^(q*cap-δ*mesh/2))^2=U^(2*q*cap-δ*mesh) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hU.le]
    congr 1
    ring
  rwa [he]

/-- Main-product upper slack depends on the original class and main mask only,
and is independent of the subset selected for any particular dilation box. -/
theorem amplitude_class_main_upper {Row Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (rows : Finset Row) (main : Finset Slot) (U δ mesh : ℝ) (hm : 0 < mesh)
    (width : Slot→ℝ) (Q : Row→Slot→ℂ)
    (bin : BinLabel (Finset.univ : Finset Slot) (δ/2) mesh)
    (u : Row)
    (hu : u∈amplitudeRows rows Finset.univ U (δ/2) mesh hm width Q bin)
    (hU : 1 ≤ U) (hw : ∀j,0 ≤ width j) (hL : 0 < ∑j,width j)
    (hupper : ∀j∈main,‖Q u j‖ ≤ (U^(width j))^
      (HeckePrimeAmplitudeBins.amplitude (U^(width j)) (δ/2) mesh (Q u j)+mesh)) :
    ‖∏j∈main,Q u j‖ ≤ U^(weightedMean Finset.univ width
      (maskedGain main (binValue Finset.univ (δ/2) mesh bin))*(∑j,width j)+mesh*(∑j,width j)) := by
  apply masked_main_product_upper main width _ U mesh (Q u) hU hm.le hw hL
  intro j hj
  have he := amplitude_class_value rows Finset.univ U (δ/2) mesh hm width Q bin u hu j (Finset.mem_univ j)
  have hh := hupper j hj
  rw [he,←Real.rpow_mul (zero_le_one.trans hU)] at hh
  exact hh

/-- Every subset of source slots satisfies the crude selected-product cutoff
required when discarding the Fourier tail. -/
theorem source_selected_product_crude {Δ : ℝ} (D : HighParameters.HighData Δ)
    (Z d δ : ℝ) (hZ : 1 < Z) (hd : 1/2 ≤ d) (hδ : 0 ≤ δ) (hδ' : δ ≤ 3/4)
    (selected : Finset (Fin D.N)) (Q : Fin D.N→ℂ)
    (hQ : ∀j,‖Q j‖ ≤ (Z^(D.ell j))^
      (HeckePrimeAmplitudeBins.amplitude (Z^(D.ell j)) (δ/2) D.t (Q j)+D.t)) :
    ‖∏j∈selected,Q j‖ ≤ Z^d := by
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have ht := D.t_pos
  have hlength : ∑j∈selected,D.ell j ≤ (1/5:ℝ) := by
    apply le_trans _ Cycle25.ell_lt_one_fifth.le
    rw [←D.slots_sum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ selected)
      (fun j _ _=>(D.slots_bounds j).1.le)
  calc
    _ ≤ ∏j∈selected,Z^(D.ell j*(δ/2+D.t)) := by
      rw [norm_prod]
      apply Finset.prod_le_prod₀ (fun j _=> norm_nonneg _)
      intro j hj
      have ha := (HeckePrimeAmplitudeBins.amplitude_bounds
        (Z^(D.ell j)) (δ/2) D.t (Q j) (by positivity)).2
      apply (hQ j).trans
      rw [←Real.rpow_mul hZ0.le]
      apply Real.rpow_le_rpow_of_exponent_le hZ.le
      exact mul_le_mul_of_nonneg_left (by linarith :
        HeckePrimeAmplitudeBins.amplitude (Z^(D.ell j)) (δ/2) D.t (Q j)+D.t ≤ δ/2+D.t)
        (D.slots_bounds j).1.le
    _ = Z^((∑j∈selected,D.ell j)*(δ/2+D.t)) := by
      rw [←Real.rpow_sum_of_pos hZ0,←Finset.sum_mul]
    _ ≤ Z^d := by
      apply Real.rpow_le_rpow_of_exponent_le hZ.le
      have hh := mul_le_mul_of_nonneg_right hlength
        (by positivity : 0 ≤ δ/2+D.t)
      nlinarith only [hh,hδ',D.t_small,hd]

end Cycle25.Numerator
end

/- Adapted from weighted-numerator PR6, 2fd60c0926b66ea18d7436f5ed55250fd006ab5d; Apache-2.0. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.SourceSelection -/

/- BEGIN ORIGINAL MODULE Global.Final.Height ; sha256 822f6d4954fb54ea93693b07e746a8a90fe2c6d4608b259fd974f6d8d812b378 -/
section




/-! The height is chosen after both source-moment degrees and the weighted
cell degree.  One character-dependent constant then controls both moment
families at that height.  Adapted from weighted upstream HighRows/ConditionalFinal,
revision 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0. -/
namespace Submission20261012.Global.FinalAssembly
noncomputable section
open scoped Classical
open Filter OAI OAI.SevenEighths
open HeckeFamily Cycle25ProbeFinalAssembly

theorem chosen_data_height {Δ : ℝ} (D : Submission20261012.Global.HighParameters.HighData Δ)
    (F : WeightedSourceData D.toMomentData)
    (counts : Cycle25ProbeHighRowFamily.CountParameters F.modulus ⊤ D.t)
    (oldcounts : ProbeFinalAssembly.CountParameters F.modulus ⊤ D.t)
    (J Jo Jw : ℝ) (hJ : 0 ≤ J) (hJo : 0 ≤ Jo) (hJw : 0 ≤ Jw)
    (hbound : ∀η : Character,∃C : ℝ,0 < C ∧
      ∀τ : ℝ,0 < τ → τ ≤ 1 → ∀ᶠZ : ℝ in atTop,
        weighted_SourceMomentBound F D.momentKappa counts η Z τ
          (C*(1+Z^(2*τ))^J) (Z^(2*τ)))
    (hboundOld : ∀η : Character,∃C : ℝ,0 < C ∧
      ∀τ : ℝ,0 < τ → τ ≤ 1 → ∀ᶠZ : ℝ in atTop,
        old_sourceMomentBound F oldcounts η Z τ
          (C*(1+Z^(2*τ))^Jo) (Z^(2*τ))) :
    ∃τ : ℝ,0 < τ ∧ τ < (1/200:ℝ)/2 ∧ 4*τ < (1/200)*D.cost ∧ τ < D.t ∧
      2*τ ≤ D.t ∧ τ*(2+4*D.eps) < D.t ∧ 2*τ*(1+Jw) ≤ D.t ∧
      ∀η : Character,∃C : ℝ,1 ≤ C ∧ ∀ᶠZ : ℝ in atTop,
        weighted_SourceMomentBound F D.momentKappa counts η Z τ (C*Z^D.t) (Z^(2*τ)) ∧
        old_sourceMomentBound F oldcounts η Z τ (C*Z^D.t) (Z^(2*τ)) := by
  obtain ⟨τ,hτ,hτd,hτcost,hτt,hτJtotal,hτeps⟩ :=
    D.height_choice (J+Jo+Jw) (by positivity)
  have hτJ : 2*τ*(1+J) ≤ D.t := by
    nlinarith only [hτJtotal,mul_nonneg hτ.le hJo,mul_nonneg hτ.le hJw]
  have hτJo : 2*τ*(1+Jo) ≤ D.t := by
    nlinarith only [hτJtotal,mul_nonneg hτ.le hJ,mul_nonneg hτ.le hJw]
  have hτJw : 2*τ*(1+Jw) ≤ D.t := by
    nlinarith only [hτJtotal,mul_nonneg hτ.le hJ,mul_nonneg hτ.le hJo]
  have htau1 : τ ≤ 1 := by linarith only [hτd]
  refine ⟨τ,hτ,hτd,hτcost,hτt,by nlinarith only [hτJ,mul_nonneg hτ.le hJ],
    hτeps,hτJw,?_⟩
  intro η
  obtain ⟨C,hC,hbound⟩ := hbound η
  obtain ⟨Co,hCo,hboundOld⟩ := hboundOld η
  have hP : 0 ≤ C*2^J := by positivity
  have hPo : 0 ≤ Co*2^Jo := by positivity
  refine ⟨C*2^J+Co*2^Jo+1,by linarith,?_⟩
  filter_upwards [hbound τ hτ htau1,hboundOld τ hτ htau1,
    eventually_ge_atTop (1:ℝ)] with Z hb hbo hZ
  have habs := ProbeFinalAssembly.polynomial_height_absorption C Z τ J D.t
    hC.le hZ hτ.le hJ (by linarith only [hτJ])
  have habso := ProbeFinalAssembly.polynomial_height_absorption Co Z τ Jo D.t
    hCo.le hZ hτ.le hJo (by linarith only [hτJo])
  constructor
  · apply weighted_SourceMomentBound.mono_constant (by linarith only [hZ]) hb
    exact habs.trans (mul_le_mul_of_nonneg_right
      (by linarith : C*2^J ≤ C*2^J+Co*2^Jo+1) (by positivity))
  · apply old_sourceMomentBound.mono_constant (by linarith only [hZ]) hbo
    exact habso.trans (mul_le_mul_of_nonneg_right
      (by linarith : Co*2^Jo ≤ C*2^J+Co*2^Jo+1) (by positivity))
end
end Submission20261012.Global.FinalAssembly

#print axioms Submission20261012.Global.FinalAssembly.chosen_data_height
end
/- END ORIGINAL MODULE Global.Final.Height -/

/- BEGIN ORIGINAL MODULE Global.Low.Reflection.LowInactiveEnergy ; sha256 fd7f89c8325282f67c21d1951413dab389558a4420fea4ae1a5c02362bf194f1 -/
section



/-! Adapted from OpenAI/math family003, pinned original module Reflection.LowInactiveEnergy.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

namespace Submission20261012.Global
open OAI OAI.SevenEighths

namespace LowReflection
open InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel : Eis}

theorem low_original_inactive_energy
    {γ : Type*} [Fintype γ] (a c₀ : γ→Eis) (mode : γ→Bool)
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (lo hi : ℝ) (hlo : 0< lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : ∀ i,FixedCuspShape (ControlledStratumArithmetic.fixedCusp (a i) (c₀ i) (mode i))) (hc₀ : ∀ i,c₀ i≠0)
    (hNlevel : ∀ i,(9:Eis)*c₀ i∣Nlevel)
    (hbase : ∀ i,if mode i then ConcretePrimeRowBridge.goodLambda^2∣a i-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀ i-1)
    (hac : ∀ i,IsCoprime (a i) (c₀ i))
    (Q : Ideal Eis) (hQ : Q≠0) (Ck η : ℝ) (hCk : 0< Ck) (hη : 0<η) (hη1 : η≤1) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0< C ∧ 1< Z₀ ∧
    ∀ g : γ,∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (J F Q₀ : Ideal Eis)
      (_hJ : J≠0) (_hF : F≠0),
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z d ell0 shift O₀ : ℝ),
      Z₀≤ Z → 0≤ d → d≤ Submission20261012.Global.ell → 0≤ ell0 → ell0≤ Submission20261012.Global.ell-d+η → |shift|≤η →
      O₀=normWidth Z (rowPowerfulPart J) →
    ∀ (parents rows : Finset (Ideal Eis)),
      (∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤ Ck*Z^((1-Submission20261012.Global.ell)-2*d)) →
      rows⊆originalResidualRows parents J Q →
      (∀ P∈fixedBadPrimes,P∣Q) →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let jF := fun b : A => completedLocalExponent J F b.val.val
    ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ)
      (_hdis : Pairwise (fun i j => Disjoint (lists i) (lists j)))
      (hmax : ∀ i,∀ P∈lists i,P.IsMaximal)
      (hgood : ∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P)
      (_hprime : ∀ i,∀ P∈lists i,Prime P)
      (hrows : ∀ K∈rows,Admissible K),
      (∀ i,1≤ H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤ H i) → (∏ i,H i)≤ Z^ell0 →
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ i,∀ P∈lists i,IsCoprime (Ideal.span {Nlevel}) P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
    ∀ T : Finset σ,
    ∃ D : ∀ K : rows,
      ∀ _b : supportedSlotChoices (fun i : {i // i∉T} => lists i.val) (poolPrimeFamily J Q Q₀).ideal K.val,
      ∀ p : supportedSlotChoices (fun i : T => lists i.val) (poolPrimeFamily J Q Q₀).ideal K.val,
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property)
        (slotChoiceFamily (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator
          Nlevel (a g) (c₀ g) (mode g),
    ∀ (θ : ℝ) (w : ∀ i,lists i→ℂ), (∀ i P,‖w i P‖≤1) →
      (∑ K : rows,‖∑ b : supportedSlotChoices (fun i : {i // i∉T} => lists i.val)
        (poolPrimeFamily J Q Q₀).ideal K.val,
        ((∏ i : {i // i∉T},(Ideal.absNorm (b.val i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b.val i)))*
        ∑ p : supportedSlotChoices (fun i : T => lists i.val) (poolPrimeFamily J Q Q₀).ideal K.val,
          (∏ i : T,w i.val (p.val i))*mixedReflectedValue (D K b p) (s g)
          (G.reflected K.val (hrows K.val K.property)
            (slotChoiceFamily (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator_ne_zero (hc₀ g)
          (G.reflected K.val (hrows K.val K.property)
            (slotChoiceFamily (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator_good
          (reflectedExponent jF) (slotIndices A (PrimeIndex K.val) T)
          (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift))‖^2)≤
        (∏ i : {i // i∉T},256*(columnDyadicLength (H i.val)+1:ℝ))^2*
          (C*(1+‖θ‖)^degree*Z^(((1-Submission20261012.Global.ell)-d)+505*η-O₀/2)) := by
  have hsubmissionEll := Submission20261012.Global.ell_interval
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := low_original_choice_energy a c₀ mode lo hi hlo W hWs hW
    s hc₀ hNlevel hbase hac Q hQ Ck η hCk hη hη1
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro g σ _ _ J F Q₀ hJ hF A Z d ell0 shift O₀ hZ hd hd1 hell hellcap hshift hOeq parents rows hparents hsub hbad
  dsimp only
  intro lists H hdis hmax hgood hprime hrows hH1 hH hprod hGN hGchar hrowcop hLN hLchar T
  let G := (poolPrimeFamily J Q Q₀).restrict A
  let FF := (poolPrimeFamily J Q Q₀).ideal
  let rowsb := fun b : ∀ i : {i // i∉T},lists i.val => inactiveRowSet rows lists T FF b
  have hbsub (b : ∀ i : {i // i∉T},lists i.val) : rowsb b⊆rows := by
    intro K hK
    exact ((inactiveRows_mem rows lists T FF b K).mp hK).1
  have hbr (b : ∀ i : {i // i∉T},lists i.val) : ∀ K∈rowsb b,Admissible K := fun K hK => hrows K (hbsub b hK)
  have hdisT : Pairwise (fun i j : T => Disjoint (lists i.val) (lists j.val)) := by
    intro i j hij
    exact hdis (fun hv => hij (Subtype.ext hv))
  have hpT : (∏ i : T,H i.val)≤ Z^ell0 := by
    rw [Finset.prod_coe_sort]
    apply le_trans _ hprod
    exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ T)
      (fun i _ => zero_le_one.trans (hH1 i)) (fun i _ _ => hH1 i)
  have hall := fun b : ∀ i : {i // i∉T},lists i.val =>
    he g J F Q₀ hJ hF A Z d ell0 shift O₀
      hZ hd hd1 hell hellcap hshift hOeq
      parents (rowsb b) hparents ((hbsub b).trans hsub) hbad
      (fun i : T => lists i.val) (fun i : T => H i.val) hdisT
      (fun i => hmax i.val) (fun i => hgood i.val) (fun i => hprime i.val) (hbr b)
      (fun i => hH i.val) hpT hGN hGchar (fun K hK => hrowcop K (hbsub b hK))
      (fun i => hLN i.val) (fun i => hLchar i.val)
  choose Db hDb using hall
  let D := fun (K : rows)
    (b : supportedSlotChoices (fun i : {i // i∉T} => lists i.val) FF K.val)
    (p : supportedSlotChoices (fun i : T => lists i.val) FF K.val) =>
      Db b.val ⟨K.val,(inactiveRows_mem rows lists T FF b.val K.val).mpr ⟨K.property,b.property⟩⟩ p
  refine ⟨D,?_⟩
  intro θ w hw
  let f := fun (K : rows) (b : supportedSlotChoices (fun i : {i // i∉T} => lists i.val) FF K.val) =>
    ∑ p : supportedSlotChoices (fun i : T => lists i.val) FF K.val,
      (∏ i : T,w i.val (p.val i))*mixedReflectedValue (D K b p) (s g)
      (G.reflected K.val (hrows K.val K.property)
        (slotChoiceFamily (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator_ne_zero (hc₀ g)
      (G.reflected K.val (hrows K.val K.property)
        (slotChoiceFamily (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator_good
      (reflectedExponent (fun b : A => completedLocalExponent J F b.val.val)) (slotIndices A (PrimeIndex K.val) T)
      (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift))
  have hzpos : 0< Z := lt_trans zero_lt_one (lt_of_lt_of_le hZ₀ hZ)
  apply supported_inactive_source_energy rows lists T FF H (fun i P hP => (hprime i P hP).ne_zero)
    hH w hw f (C*(1+‖θ‖)^degree*Z^(((1-Submission20261012.Global.ell)-d)+505*η-O₀/2)) (by positivity)
  intro b
  exact hDb b θ (fun i : T => w i.val) (fun i P => hw i.val P)
end
end LowReflection

end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Low.Reflection.LowInactiveEnergy -/

/- BEGIN ORIGINAL MODULE Global.Numerator.SourceSelection ; sha256 90ee011e27d87354d5a063dc6beabaf0badd5204db7dbd9032c5f890f1665212 -/
section





/-! A single selected prime subset for every row in an actual full amplitude
class, with only the numerator's error slots masked out of the lower mean. -/
noncomputable section
open scoped Classical BigOperators
namespace Submission20261012.Global.Numerator
open Cycle25.Numerator
open OAI OAI.SevenEighths HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst
open HeckeDetectorFiberPartition ProbeHighRowFamily Cycle25ProbeFinalAssembly Cycle25DetectorRowCount
open ProbePhysical HeckeFamily HeckeInverseAmplification

 theorem masked_main_product_upper {α : Type*} [Fintype α] [DecidableEq α]
    (main : Finset α) (width g : α→ℝ) (U mesh : ℝ) (Q : α→ℂ)
    (hU : 1 ≤ U) (hm : 0 ≤ mesh) (hw : ∀j,0 ≤ width j)
    (hL : 0 < ∑j,width j)
    (hQ : ∀j∈main,‖Q j‖ ≤ U^(width j*(g j+mesh))) :
    ‖∏j∈main,Q j‖ ≤ U^(weightedMean Finset.univ width (maskedGain main g)*(∑j,width j)+
      mesh*(∑j,width j)) := by
  have hUpos : 0 < U := zero_lt_one.trans_le hU
  have he : (∑j,width j*maskedGain main g j)=∑j∈main,width j*g j := by
    calc
      _ = ∑j∈main,width j*maskedGain main g j :=
        (Finset.sum_subset (Finset.subset_univ main) (fun j _ hj=> by simp [maskedGain,hj])).symm
      _ = _ := Finset.sum_congr rfl (fun j hj=> by simp [maskedGain,hj])
  have hmean : weightedMean Finset.univ width (maskedGain main g)*(∑j,width j)=
      ∑j∈main,width j*g j := by
    unfold weightedMean
    rw [div_mul_cancel₀ _ hL.ne',he]
  have hsum : ∑j∈main,width j ≤ ∑j,width j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ main) (fun j _ _=> hw j)
  calc
    _ ≤ ∏j∈main,U^(width j*(g j+mesh)) := by
      rw [norm_prod]
      exact Finset.prod_le_prod₀ (fun j _=> norm_nonneg _) hQ
    _ = U^(∑j∈main,width j*(g j+mesh)) := (Real.rpow_sum_of_pos hUpos _ _).symm
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le hU
      rw [hmean]
      have hh := mul_le_mul_of_nonneg_left hsum hm
      have he' : (∑j∈main,width j*(g j+mesh))=
          (∑j∈main,width j*g j)+mesh*(∑j∈main,width j) := by
        rw [Finset.mul_sum,←Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      rw [he']
      linarith

/-- Exact identification of the source-count physical family with canonical
prime amplitudes at the original physical slot lengths. -/
theorem source_count_physical_eq {Δ : ℝ} (D : HighParameters.HighData Δ)
    (F : WeightedSourceData D.toMomentData) (Z d : ℝ) (hZ : 0 < Z) (hd : d≠0)
    (z : ℂ) (u : FreeRow) (j : Fin D.N) :
    physical F.modulus ⊤ (fun u : FreeRow=> u.val) (fun _ y=>(F.w y:ℂ)) (fun _=>2)
      (fun j=> D.ell j/d) (fun _=> z) (Z^d) u j=
      HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z := by
  calc
    _ = HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val (fun y=>(F.w y:ℂ)) 2 (Z^(D.ell j)) z :=
      source_physical_amplitude F.modulus ⊤ D.ell (fun _ y=>(F.w y:ℂ)) Z d 2 z hZ hd u j
    _ = _ := by
      congr 1
      funext y
      exact (F.complex_eq y).symm

/-- Common selection on a canonical full amplitude class. The analytic upper
premise is supplied by weighted_source_prime_bins; lower spikes are automatic. -/
theorem source_class_main_selection {Δ : ℝ} (D : HighParameters.HighData Δ)
    (F : WeightedSourceData D.toMomentData)
    (hfine : ∀j,D.ell j ≤ Cycle25.sourceMesh D.t/200)
    (Z d v δ : ℝ) (hZ : 1 < Z) (hd : (1/2:ℝ) ≤ d) (hv : 0 ≤ v) (hδ : 0 ≤ δ)
    (z : ℂ) (rows : Finset FreeRow) (main : Finset (Fin D.N))
    (bin : BinLabel (Finset.univ : Finset (Fin D.N)) (δ/2) D.t)
    (hne : (amplitudeRows rows Finset.univ (Z^d) (δ/2) D.t D.t_pos (fun j=> D.ell j/d)
      (fun u j=> HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z) bin).Nonempty) :
    let Q := fun (u : FreeRow) j=> HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z
    let rows' := amplitudeRows rows Finset.univ (Z^d) (δ/2) D.t D.t_pos (fun j=> D.ell j/d) Q bin
    let g := binValue Finset.univ (δ/2) D.t bin
    let q := weightedMean Finset.univ (fun j=> D.ell j/d) (maskedGain main g)
    0 ≤ q ∧ q ≤ δ/2 ∧ ∃selected : Finset (Fin D.N),selected⊆main ∧
      (∑j∈selected,D.ell j/d) ≤ SlotSelection.reflectedCapacity D.momentKappa d v ∧
      ∀u∈rows',
        (Z^d)^(2*q*SlotSelection.reflectedCapacity D.momentKappa d v-
          δ*Cycle25.sourceMesh D.t) ≤ ‖∏j∈selected,Q u j‖^2 ∧
        ((∀j,‖Q u j‖ ≤ (Z^(D.ell j))^(HeckePrimeAmplitudeBins.amplitude (Z^(D.ell j)) (δ/2) D.t (Q u j)+D.t)) →
          ‖∏j∈main,Q u j‖ ≤ (Z^d)^(q*(ell/d)+D.t*(ell/d))) := by
  dsimp only
  let Q := fun (u : FreeRow) j=> HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z
  let rows' := amplitudeRows rows Finset.univ (Z^d) (δ/2) D.t D.t_pos (fun j=> D.ell j/d) Q bin
  let g := binValue Finset.univ (δ/2) D.t bin
  have hdpos : 0 < d := by linarith
  have hZpos : 0 < Z := zero_lt_one.trans hZ
  have hU : 1 < Z^d := Real.one_lt_rpow hZ hdpos
  have hscale (j : Fin D.N) : (Z^d)^(D.ell j/d)=Z^(D.ell j) := by
    rw [←Real.rpow_mul hZpos.le,mul_div_cancel₀ _ hdpos.ne']
  have hgfull : ∀j,0 ≤ g j ∧ g j ≤ δ/2 := by
    obtain ⟨u,hu⟩ := hne
    intro j
    have he := amplitude_class_value rows Finset.univ (Z^d) (δ/2) D.t D.t_pos
      (fun j=> D.ell j/d) Q bin u hu j (Finset.mem_univ j)
    dsimp only [g]
    rw [←he]
    exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by positivity)
  have hg : ∀j,0 ≤ maskedGain main g j ∧ maskedGain main g j ≤ δ/2 := by
    intro j
    unfold maskedGain
    split_ifs
    · exact hgfull j
    · exact ⟨le_rfl,by positivity⟩
  obtain ⟨hqeq,hq0,hqtop,T,hT,hTpos,hTcap,hgain,hgain',hspike⟩ :=
    SlotSelection.highData_weighted_selection D hfine d v δ hd hv hδ main
      (maskedGain main g) hg (fun j hj=> by simp [maskedGain,hj])
  refine ⟨hq0,hqtop,T,hT,hTcap,?_⟩
  intro u hu
  have hgrow (j : Fin D.N) : HeckePrimeAmplitudeBins.amplitude (Z^(D.ell j)) (δ/2) D.t (Q u j)=g j := by
    have he := amplitude_class_value rows Finset.univ (Z^d) (δ/2) D.t D.t_pos
      (fun j=> D.ell j/d) Q bin u hu j (Finset.mem_univ j)
    simpa only [hscale] using he
  refine ⟨?_,?_⟩
  · apply hspike (Z^d) hU.le (Q u)
    intro j hj
    have hjmain : j∈main := by
      by_contra hm
      simp only [maskedGain,ite_eq_right hm,lt_self_iff_false] at hj
    have hgm : maskedGain main g j=g j := by simp [maskedGain,hjmain]
    have hpos : 0 < HeckePrimeAmplitudeBins.amplitude ((Z^d)^(D.ell j/d)) (δ/2) D.t (Q u j) := by
      rw [hscale,hgrow]
      rwa [hgm] at hj
    have hh := HeckePrimeAmplitudeBins.squared_spike (Z^d) (D.ell j/d) (δ/2) D.t
      (Q u j) hU (div_pos (D.slots_bounds j).1 hdpos) D.t_pos hpos
    simpa only [hscale,hgrow,hgm] using hh
  · intro hupper
    have hL : (∑j,D.ell j/d)=ell/d := by rw [←Finset.sum_div,D.slots_sum]
    have hh := masked_main_product_upper main (fun j=> D.ell j/d) g (Z^d) D.t (Q u)
      hU.le D.t_pos.le (fun j=>(div_pos (D.slots_bounds j).1 hdpos).le)
      (by rw [hL];exact div_pos ell_pos hdpos) (by
        intro j hj
        calc
          _ ≤ (Z^(D.ell j))^(g j+D.t) := by
            have he := hupper j
            change ‖Q u j‖ ≤ (Z^(D.ell j))^(HeckePrimeAmplitudeBins.amplitude (Z^(D.ell j)) (δ/2) D.t (Q u j)+D.t) at he
            rwa [hgrow] at he
          _ = _ := by rw [←hscale j,←Real.rpow_mul (by positivity)])
    simpa only [hL] using hh


/-- The positive real square root of the selected squared spike. -/
theorem squared_selected_lower (U q cap δ mesh : ℝ) (Q : ℂ) (hU : 0 < U)
    (hQ : U^(2*q*cap-δ*mesh) ≤ ‖Q‖^2) :
    U^(q*cap-δ*mesh/2) ≤ ‖Q‖ := by
  apply (sq_le_sq₀ (Real.rpow_nonneg hU.le _) (norm_nonneg _)).mp
  have he : (U^(q*cap-δ*mesh/2))^2=U^(2*q*cap-δ*mesh) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hU.le]
    congr 1
    ring
  rwa [he]

/-- Main-product upper slack depends on the original class and main mask only,
and is independent of the subset selected for any particular dilation box. -/
theorem amplitude_class_main_upper {Row Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (rows : Finset Row) (main : Finset Slot) (U δ mesh : ℝ) (hm : 0 < mesh)
    (width : Slot→ℝ) (Q : Row→Slot→ℂ)
    (bin : BinLabel (Finset.univ : Finset Slot) (δ/2) mesh)
    (u : Row)
    (hu : u∈amplitudeRows rows Finset.univ U (δ/2) mesh hm width Q bin)
    (hU : 1 ≤ U) (hw : ∀j,0 ≤ width j) (hL : 0 < ∑j,width j)
    (hupper : ∀j∈main,‖Q u j‖ ≤ (U^(width j))^
      (HeckePrimeAmplitudeBins.amplitude (U^(width j)) (δ/2) mesh (Q u j)+mesh)) :
    ‖∏j∈main,Q u j‖ ≤ U^(weightedMean Finset.univ width
      (maskedGain main (binValue Finset.univ (δ/2) mesh bin))*(∑j,width j)+mesh*(∑j,width j)) := by
  apply masked_main_product_upper main width _ U mesh (Q u) hU hm.le hw hL
  intro j hj
  have he := amplitude_class_value rows Finset.univ U (δ/2) mesh hm width Q bin u hu j (Finset.mem_univ j)
  have hh := hupper j hj
  rw [he,←Real.rpow_mul (zero_le_one.trans hU)] at hh
  exact hh

/-- Every subset of source slots satisfies the crude selected-product cutoff
required when discarding the Fourier tail. -/
theorem source_selected_product_crude {Δ : ℝ} (D : HighParameters.HighData Δ)
    (Z d δ : ℝ) (hZ : 1 < Z) (hd : 1/2 ≤ d) (hδ : 0 ≤ δ) (hδ' : δ ≤ 3/4)
    (selected : Finset (Fin D.N)) (Q : Fin D.N→ℂ)
    (hQ : ∀j,‖Q j‖ ≤ (Z^(D.ell j))^
      (HeckePrimeAmplitudeBins.amplitude (Z^(D.ell j)) (δ/2) D.t (Q j)+D.t)) :
    ‖∏j∈selected,Q j‖ ≤ Z^d := by
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have ht := D.t_pos
  have hlength : ∑j∈selected,D.ell j ≤ (1/5:ℝ) := by
    apply le_trans _ Submission20261012.Global.ell_lt_one_fifth.le
    rw [←D.slots_sum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ selected)
      (fun j _ _=>(D.slots_bounds j).1.le)
  calc
    _ ≤ ∏j∈selected,Z^(D.ell j*(δ/2+D.t)) := by
      rw [norm_prod]
      apply Finset.prod_le_prod₀ (fun j _=> norm_nonneg _)
      intro j hj
      have ha := (HeckePrimeAmplitudeBins.amplitude_bounds
        (Z^(D.ell j)) (δ/2) D.t (Q j) (by positivity)).2
      apply (hQ j).trans
      rw [←Real.rpow_mul hZ0.le]
      apply Real.rpow_le_rpow_of_exponent_le hZ.le
      exact mul_le_mul_of_nonneg_left (by linarith :
        HeckePrimeAmplitudeBins.amplitude (Z^(D.ell j)) (δ/2) D.t (Q j)+D.t ≤ δ/2+D.t)
        (D.slots_bounds j).1.le
    _ = Z^((∑j∈selected,D.ell j)*(δ/2+D.t)) := by
      rw [←Real.rpow_sum_of_pos hZ0,←Finset.sum_mul]
    _ ≤ Z^d := by
      apply Real.rpow_le_rpow_of_exponent_le hZ.le
      have hh := mul_le_mul_of_nonneg_right hlength
        (by positivity : 0 ≤ δ/2+D.t)
      nlinarith only [hh,hδ',D.t_small,hd]

end Submission20261012.Global.Numerator
end

/- Adapted from weighted-numerator PR6, 2fd60c0926b66ea18d7436f5ed55250fd006ab5d; Apache-2.0. -/

-- New geometry wrapper, 13 October 2026; inherited analytic core unchanged.
end
/- END ORIGINAL MODULE Global.Numerator.SourceSelection -/
