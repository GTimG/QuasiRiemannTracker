/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B031
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B033
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B036
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B068
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B073
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B076
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Reflection.LowFrozenEnergy

/- BEGIN ORIGINAL MODULE Analytic.JointRetainedShortGates ; sha256 e6503c5d4e69531d373ce647074ee4a465940315b76edc6c847ead0a04a7e7ef -/
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

theorem actual_retained_buffered_short_gates
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
      (∀ i I, I ∈ s.input.slots i → s.input.ν i I = idealCoeff (η₀ i).inverse I) → (∀ i, s.input.W i = V i) →
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
      3*(bin+1 : ℕ)*Z^τ ≤ T →
      ∀ q ∈ s.liveFullRetainedFiber Ds t₁ t₂ z,
      ∃ DL DR : SurvivingBufferedData η w ι orders profileBound edge e,
        s.fullFiberValue t₁ t₂ z q =
          ‖DL.value M H η₀ V bhi Z d‖*‖DR.value M H η₀ V bhi Z d‖ ∧
        d*DL.length ≤ s.fullLeftLength Z q+Real.logb Z (max 1 b₁*max 1 b₂) ∧
        d*DR.length ≤ s.fullRightLength Z q+Real.logb Z (max 1 b₁*max 1 b₂) ∧
        DL.ShortSlotGates M H hH η₀ Rwidth τ ηaux σmin σmax Z d T ∧
        DR.ShortSlotGates M H hH η₀ Rwidth τ ηaux σmin σmax Z d T ∧
        (∀ j : DL.slots, (Z^d)^(DL.data.r j) = s.input.P j.val) ∧
        (∀ j : DR.slots, (Z^d)^(DR.data.r j) = s.input.P j.val) ∧
        (∀ j, DL.data.σ j = 0 ∧ DL.data.v j = 0) ∧ DL.data.t = t₁ ∧ DL.data.bin = bin ∧
        (∀ j, DR.data.σ j = 0 ∧ DR.data.v j = 0) ∧ DR.data.t = t₂ ∧ DR.data.bin = bin := by
  obtain ⟨profileBound,hprofile,hdata⟩ := actual_common_retained_short_gates
    W₁ W₂ a₁ b₁ a₂ b₂ ha₁ ha₂ hs₁ hW₁ hs₂ hW₂
  refine ⟨profileBound,hprofile,?_⟩
  intro ι instι instDι orders edge e hedge he M instM H hH η w parentL parentR NL NR
    punctureL punctureR hpunctureL hpunctureR s Ds z t₁ t₂ Z d η₀ V alo bhi bin
    Rwidth τ ηaux σmin σmax T hsW₁ hsW₂ hslots hν hW hrowL hrowR
    hZ hd hbase hR hX₁ hX₂ hY₁ hY₂ hP hσmin hσmax hcondL hcondR
    hfreqL hfreqR hfour htwo hbuffer q hq
  obtain ⟨hnL,hnR⟩ := s.liveFullRetainedFiber_nonzero Ds t₁ t₂ z q hq
  obtain ⟨DL,hslotsL,hnormL,hlenL,hadL,hscaleL,hzeroL,htL,hbiL⟩ := hdata orders edge e hedge he M H hH
    η w parentL NL punctureL hpunctureL s.input (s.firstCommon*s.second.val.1) s.puncture
    q.2.1 (childCharacter s.parent s.leftRay) s.toKernelLabel.frequency z t₁
    q.1 q.2.2.2.1 q.2.2.2.2.2.1 Z d η₀ V alo bhi bin Rwidth τ ηaux σmin σmax T
    hsW₁ hsW₂ hslots hν hW hrowL hZ hd hbase hR hX₁ hX₂ hY₁ hY₂ hP hσmin hσmax
    hcondL hfreqL hfour htwo hbuffer hnL
  obtain ⟨DR,hslotsR,hnormR,hlenR,hadR,hscaleR,hzeroR,htR,hbiR⟩ := hdata orders edge e hedge he M H hH
    η w parentR NR punctureR hpunctureR s.input (s.firstCommon*s.second.val.2) s.puncture
    q.2.2.1 (childCharacter s.parent (s.rightRay⁻¹)) s.toKernelLabel.frequency (-z) t₂
    q.1 q.2.2.2.2.1 q.2.2.2.2.2.2 Z d η₀ V alo bhi bin Rwidth τ ηaux σmin σmax T
    hsW₁ hsW₂ hslots hν hW hrowR hZ hd hbase hR hX₁ hX₂ hY₁ hY₂ hP hσmin hσmax
    hcondR hfreqR hfour htwo hbuffer hnR
  refine ⟨DL,DR,?_,hlenL,hlenR,hadL,hadR,hscaleL,hscaleR,hzeroL,htL,hbiL,hzeroR,htR,hbiR⟩
  exact congrArg₂ (fun x y : ℝ => x*y) hnormL hnormR

#print axioms actual_retained_buffered_short_gates
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointRetainedShortGates -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.WeightedSourceMaskedCount ; sha256 16cb3877bce6c78638d6b28911fe70374dc4853a99f49c90aaf0cd027775d816 -/
section



/-! The original certified full-amplitude count, expressed in the actual
canonical source polynomials and weakened to the diluted main-slot mean. -/
noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace OAI.SevenEighths.Cycle25WeightedHighFinalAssembly
open Cycle25ProbeFinalAssembly Cycle25ProbeHighRowFamily ProbeFinalAssembly ProbeHighRowFamily HeckeFamily ProbePhysical HeckeInverseAmplification
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

theorem weighted_source_masked_amplitude_count {Δ : ℝ}
    (D : Cycle25.HighParameters.HighData Δ) (F : WeightedSourceData D.toMomentData)
    (counts : Cycle25ProbeHighRowFamily.CountParameters F.modulus ⊤ D.t) (τ : ℝ) (n : ℕ)
    (hτ : 0 < τ) (hτzero : τ < (1/200:ℝ)/2)
    (hτheight : 4*τ < (1/200:ℝ)*D.cost) (hτ2 : 2*τ ≤ D.t) :
    ∃C : ℝ,1 ≤ C ∧ ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀d a C0 : ℝ,(1/200:ℝ) ≤ d → d ≤ 7/8 → 51/100 < a → a ≤ 7/8 → 1 ≤ C0 →
      ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ) ≤ rowNorm u ∧
        (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧ rowNorm u ≤ Z^(d-D.t)) →
      ∀i : ℕ,i ≤ n →
      (∀u∈rows,detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        (3*(i+1:ℕ)*Z^τ) < a+2*D.e) →
      (∀u∈rows,a ≤ detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        ((3*i:ℕ)*Z^τ)) →
      ∀z : ℂ,z.re=17/50 → |z.im| ≤ Z^(2*τ) →
      weighted_SourceMomentBound F D.momentKappa counts η Z τ (C0*Z^D.t) (Z^(2*τ)) →
      let Q := fun (u : FreeRow) j=>
        HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z
      ∀main : Finset (Fin D.N),
      ∀bin : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t,
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun j=> D.ell j/d) Q bin
      let q := weightedMean Finset.univ (fun j=> D.ell j/d)
        (Cycle25DetectorRowCount.maskedGain main (binValue Finset.univ ((2*a-1)/2) D.t bin))
      rows'.Nonempty → 0 ≤ q ∧ q ≤ (2*a-1)/2 ∧
        (rows'.card:ℝ) ≤ C*C0*Z^(3*D.t)*
          (Z^d)^(Cycle25DetectorRowCount.rowCount (2*a-1) (q/(2*a-1)) D.momentKappa+(159*D.ε+9*D.t)) := by
  obtain ⟨C,hC,hcount⟩ := weighted_source_amplitude_count D F counts τ n hτ hτzero hτheight hτ2
  refine ⟨C,hC,?_⟩
  intro η
  filter_upwards [hcount η,eventually_gt_atTop (1:ℝ)] with Z hc hZ
  intro d a C0 hd hd' ha ha' hC0 rows hrows i hi hnext hcurrent z hz hzim hmom
  dsimp only
  intro main bin hne
  have hdpos : 0 < d := by linarith
  have hZpos : 0 < Z := zero_lt_one.trans hZ
  let Q := fun (u : FreeRow) j=>
    HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z
  have heq : physical F.modulus ⊤ (fun u : FreeRow=> u.val) (fun _ y=>(F.w y:ℂ))
      (fun _=>2) (fun j=> D.ell j/d) (fun _=> z) (Z^d)=Q := by
    funext u j
    exact Cycle25.Numerator.source_count_physical_eq D F Z d hZpos hdpos.ne' z u j
  have hb := hc d a C0 hd hd' ha ha' hC0 rows hrows i hi hnext hcurrent z hz hzim hmom
  dsimp only at hb
  rw [heq] at hb
  have hcard := (hb bin hne).2.2
  exact Cycle25DetectorRowCount.masked_amplitude_class_count rows Finset.univ main (Z^d) (2*a-1) D.momentKappa
    D.t D.t_pos (fun j=> D.ell j/d) Q bin (by linarith) (by linarith) D.momentKappa_lo D.momentKappa_hi
    (Real.one_le_rpow hZ.le hdpos.le)
    (fun j _=>(div_pos (D.slots_bounds j).1 hdpos).le)
    (by rw [←Finset.sum_div,D.slots_sum];exact div_pos Cycle25.ell_pos hdpos)
    (C*C0*Z^(3*D.t)) (159*D.ε+9*D.t)
    (by have := zero_le_one.trans hC;have := zero_le_one.trans hC0;positivity) hne hcard

end OAI.SevenEighths.Cycle25WeightedHighFinalAssembly
end
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.WeightedSourceMaskedCount -/

/- BEGIN ORIGINAL MODULE Cycle25.Energy.Physical.CertifiedZero ; sha256 d8998bf78f03ccb77767f78fa68fc1dac0ea59b0a4d8feb5ea96ce5006a23b8b -/
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
open CenteredMomentRowNorm CenteredMomentRetainedEnergy QuadraticInitialBound
open CenteredMomentDetectorPlainFiberSource CenteredMomentScaleSupremum CenteredMomentSectorLocalization
set_option maxHeartbeats 800000

/-- The empty-slot terminal estimate has no capacity condition on the two
plain lengths. Here each is permitted up to U². -/
theorem finite_pair_zeroAt {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (rows : Finset FreeRow)
    (η : Character) (Φ : 𝓢(ℝ,ℂ)) (U bΦ δ ε : ℝ)
    (hU : 1 ≤ U) (hδ : 0 ≤ δ) (hδtop : δ ≤ 1)
    (hs : Function.support (Φ:ℝ→ℂ) ⊆ Set.Iic bΦ) (hp : ∀x, 0 ≤ (Φ x).re)
    (hη : (η.modulus.absNorm:ℝ) ≤ U^δ)
    (hrows : ∀u∈rows, rowNorm u ≤ U)
    (hkeep : ∀u∈rows, initialKeep η (internalQ (weighted_sourceFixedIdeal F) η) u.val)
    (hone : ∀x∈Set.Icc (0:ℝ) 1, Φ x = 1)
    (degree : ℕ) (control : Finset (ℕ×ℕ)) (C : ℝ)
    (hzero : ZeroAt (internalQ (weighted_sourceFixedIdeal F) η) (1/4) (9/4) bΦ 0 2 2
      ε U degree control C)
    (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hX₁max : X₁ ≤ U^(2:ℝ)) (hX₂max : X₂ ≤ U^(2:ℝ)) :
    (∑u∈rows, ‖polynomial ((momentData η).character (momentElement u)) false
        (p.profile 0) X₁ 0 0 *
      polynomial ((momentData η).character (momentElement u)) false (p.profile 1) X₂ 0 0‖^2)
      ≤ C*diagonalControl Φ*(p.control control)^2*U^(1+δ+ε) := by
  let state := initialState η (internalQ (weighted_sourceFixedIdeal F) η)
    Φ bΦ U δ hU hδ hs hp hη
  have hwidth : state.width ≤ 2 := by change 1+δ ≤ 2; linarith
  have hz := hzero state rfl hwidth p 0 X₁ X₂ hX₁ hX₂ hX₁max hX₂max
  have he := finite_actual_pair_le_energy rows η (internalQ (weighted_sourceFixedIdeal F) η)
    Φ U bΦ δ hU hδ hs hp hη hrows hkeep hone (p.profile 0) (p.profile 1)
    (9/4) (9/4) X₁ X₂
    (fun _ hx=>(p.support 0 hx).2) (fun _ hx=>(p.support 1 hx).2) hX₁ hX₂
    (fun _:Fin 0=>∅) (fun _:Fin 0=>0) (fun _:Fin 0=>1) (by intro i; exact zero_lt_one)
  simp only [Finset.univ_eq_empty,Finset.prod_empty,mul_one] at he
  exact he.trans (by simpa [state,initialState,NaturalState.width,NaturalState.mask,
    NaturalState.plainEnergy] using hz)

/-- Actual inverse physical row Fourier moment for the empty selected family,
including reflected annuli with lengths larger than the square-root scale. -/
theorem certified_reflected_zero_fourier_moment {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) :
    ∃J:ℕ, ∃C:ℝ, 0 < C ∧ ∀ᶠU:ℝ in atTop,
      1 < U ∧ ∀rows:Finset FreeRow,
      (∀u∈rows, U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀X₁ X₂:ℝ, 0 < X₁ → 0 < X₂ → X₁ ≤ U^(2:ℝ) → X₂ ≤ U^(2:ℝ) →
      ∀j k:Fin 2, ∀v w:ℝ,
      (∑u∈rows, ‖polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
        (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (2*Real.pi*v) *
        polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
          (scaleTest (fun y:ℝ=>(annulus y:ℂ)) k) X₂ 0 (2*Real.pi*w)‖^2)
        ≤ (C*U^(1+D.t))*((1+‖v‖)^J)^2*((1+‖w‖)^J)^2 := by
  obtain ⟨bΦ,hbΦ,hsΦ⟩ := radialMajorant_support_bound
  obtain ⟨degree,control,henergy⟩ := weighted_terminal_zero_energy F bΦ hbΦ
  let η := fixedSourcePrincipal F.S F.exclusions.prime
  obtain ⟨Cz,hCz,hbound⟩ := henergy η
  obtain ⟨J,Cprofile,hCprofile,hprofile⟩ := numerator_fourier_profiles_control control
  let C := Cz*(1+diagonalControl radialMajorant)*Cprofile
  have hC : 0 < C := by
    have hd := diagonalControl_nonneg radialMajorant
    dsimp [C]; positivity
  have hmod : ∀ᶠU:ℝ in atTop, (η.modulus.absNorm:ℝ) ≤ U^(D.t/4) :=
    (tendsto_rpow_atTop (div_pos D.t_pos (by norm_num))).eventually (eventually_ge_atTop _)
  refine ⟨J,C,hC,?_⟩
  filter_upwards [hbound,hmod,eventually_fixed_source_keep F η,eventually_gt_atTop (1:ℝ)]
    with U henergy hmod hkeep hU
  refine ⟨hU,?_⟩
  intro rows hrows X₁ X₂ hX₁ hX₂ hX₁max hX₂max j k v w
  have hδ : 0 ≤ D.t/4 := div_nonneg D.t_pos.le (by norm_num)
  have hδtop : D.t/4 ≤ 1 := by linarith [D.t_small]
  have he := finite_pair_zeroAt F rows η radialMajorant U bΦ (D.t/4) (D.t/4)
    hU.le hδ hδtop hsΦ radialMajorant_nonneg hmod (fun u hu=>(hrows u hu).2)
    (fun u hu=> hkeep u (hrows u hu).1) radialMajorant_one degree control Cz henergy.2
    (numeratorFourierProfiles j k v w) X₁ X₂ hX₁ hX₂ hX₁max hX₂max
  have heq :
      (∑u∈rows, ‖polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
        (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (2*Real.pi*v) *
        polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
          (scaleTest (fun y:ℝ=>(annulus y:ℂ)) k) X₂ 0 (2*Real.pi*w)‖^2) =
      (∑u∈rows, ‖polynomial ((momentData η).character (momentElement u)) false
        ((numeratorFourierProfiles j k v w).profile 0) X₁ 0 0 *
        polynomial ((momentData η).character (momentElement u)) false
        ((numeratorFourierProfiles j k v w).profile 1) X₂ 0 0‖^2) := by
    apply Finset.sum_congr rfl
    intro u hu
    dsimp only [η]
    simp_rw [numerator_fourier_polynomial_zero,numerator_fourier_polynomial_one,
      norm_mul,inverse_annular_norm_eq F u j v X₁ hX₁,
      inverse_annular_norm_eq F u k w X₂ hX₂]
  rw [heq]
  apply he.trans
  have hd := diagonalControl_nonneg radialMajorant
  have hp := hprofile j k v w
  have hx : U^(1+D.t/4+D.t/4) ≤ U^(1+D.t) :=
    Real.rpow_le_rpow_of_exponent_le hU.le (by linarith [D.t_pos])
  calc
    _ ≤ (Cz*(1+diagonalControl radialMajorant))*
        (Cprofile*((1+‖v‖)^J)^2*((1+‖w‖)^J)^2)*U^(1+D.t) := by
      apply mul_le_mul _ hx (Real.rpow_nonneg (zero_lt_one.trans hU).le _) (by positivity)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hCz.le) hp
        (sq_nonneg _) (by positivity)
    _ = _ := by dsimp [C]; ring

end SevenEighths.Cycle25WeightedNumeratorPhysical
end
end OAI

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 keeps the original physical family and explicit variable-kappa capacity. -/
end
/- END ORIGINAL MODULE Cycle25.Energy.Physical.CertifiedZero -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.SourceParameters ; sha256 396c2be814b2dc9ba10d3cd7cef0715942194755ccb52b01e90788e7a9c1157f -/
section




/-! Eligibility of the actual physical source for the coefficient packet bound. -/
noncomputable section
open scoped BigOperators Classical
namespace Cycle25.Numerator
open Cycle25.Weighted OAI.SevenEighths.Cycle25DetectorRowCount
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification

theorem source_packet_lines {Δ : ℝ} (D : HighParameters.HighData Δ) (a : ℝ)
    (ha : (51/100:ℝ) ≤ a) (hatop : a ≤ 7/8) :
    0 ≤ (2*a-1)/4 ∧ (2*a-1)/4 ≤ 1 ∧
    1-a-6*D.e ≤ 1/2-(2*a-1)/4 ∧
    -(1/100:ℝ) ≤ 1/2-(2*a-1)/4 ∧
    1+4*D.e ≤ (a+16*D.e)+(1/2-(2*a-1)/4) := by
  have he := D.e_pos
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> linarith

theorem source_complex_profile_norm {D : MomentData} (F : WeightedSourceData D) (y : ℝ) :
    ‖F.W y‖ ≤ 1 := by
  rw [F.complex_eq,Complex.norm_real,Real.norm_of_nonneg (F.bounded y).1]
  exact (F.bounded y).2

theorem source_main_normalized_upper {Δ : ℝ} (D : HighParameters.HighData Δ)
    (F : WeightedSourceData D.toMomentData) (Z d delta : ℝ) (hZ : 1 < Z) (hd : 0 < d)
    (main : Finset (Fin D.N)) (g : Fin D.N→ℝ) (u : FreeRow) (z : ℂ)
    (hupper : ∀j∈main,‖HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z‖ ≤
      (Z^(D.ell j))^(g j+D.t)) :
    let q := HeckeDetectorPhysicalSelection.weightedMean Finset.univ (fun j=> D.ell j/d) (maskedGain main g)
    ‖(∏j∈main,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z) /
      (((Z^d)^(D.t*(ell/d)):ℝ):ℂ)‖ ≤ (Z^d)^(q*(ell/d)) := by
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hU : 1 < Z^d := Real.one_lt_rpow hZ hd
  have hw (j : Fin D.N) : 0 ≤ D.ell j/d := (div_pos (D.slots_bounds j).1 hd).le
  have hL : (∑j,D.ell j/d)=ell/d := by rw [←Finset.sum_div,D.slots_sum]
  have hscale (j : Fin D.N) : (Z^d)^(D.ell j/d)=Z^(D.ell j) := by
    rw [←Real.rpow_mul hZ0.le,mul_div_cancel₀ _ hd.ne']
  have hb := masked_main_product_upper main (fun j=> D.ell j/d) g (Z^d) D.t
    (fun j=> HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z)
    hU.le D.t_pos.le hw (by rw [hL];exact div_pos ell_pos hd) (by
      intro j hj
      calc
        _ ≤ (Z^(D.ell j))^(g j+D.t) := hupper j hj
        _ = _ := by rw [←hscale j,←Real.rpow_mul (zero_lt_one.trans hU).le])
  rw [hL] at hb
  exact upper_bin_normalized _ (Z^d) _ _ (zero_lt_one.trans hU) hb

end Cycle25.Numerator

/- Adapted from weighted-numerator PR6, 2fd60c0926b66ea18d7436f5ed55250fd006ab5d; Apache-2.0. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.SourceParameters -/

/- BEGIN ORIGINAL MODULE Global.Detector.WeightedSourceMaskedCount ; sha256 1b6ac1665ebd603f9f630844cb1d3eb626e86c9cf1a99f76e9c1bd5e0ab578f1 -/
section



/-! The original certified full-amplitude count, expressed in the actual
canonical source polynomials and weakened to the diluted main-slot mean. -/
noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace Submission20261012.Global.Detector
open OAI OAI.SevenEighths
open Cycle25ProbeFinalAssembly Cycle25ProbeHighRowFamily ProbeFinalAssembly ProbeHighRowFamily HeckeFamily ProbePhysical HeckeInverseAmplification
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

theorem weighted_source_masked_amplitude_count {Δ : ℝ}
    (D : Submission20261012.Global.HighParameters.HighData Δ) (F : WeightedSourceData D.toMomentData)
    (counts : Cycle25ProbeHighRowFamily.CountParameters F.modulus ⊤ D.t) (τ : ℝ) (n : ℕ)
    (hτ : 0 < τ) (hτzero : τ < (1/200:ℝ)/2)
    (hτheight : 4*τ < (1/200:ℝ)*D.cost) (hτ2 : 2*τ ≤ D.t) :
    ∃C : ℝ,1 ≤ C ∧ ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀d a C0 : ℝ,(1/200:ℝ) ≤ d → d ≤ 7/8 → 51/100 < a → a ≤ 7/8 → 1 ≤ C0 →
      ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ) ≤ rowNorm u ∧
        (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧ rowNorm u ≤ Z^(d-D.t)) →
      ∀i : ℕ,i ≤ n →
      (∀u∈rows,detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        (3*(i+1:ℕ)*Z^τ) < a+2*D.e) →
      (∀u∈rows,a ≤ detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        ((3*i:ℕ)*Z^τ)) →
      ∀z : ℂ,z.re=17/50 → |z.im| ≤ Z^(2*τ) →
      weighted_SourceMomentBound F D.momentKappa counts η Z τ (C0*Z^D.t) (Z^(2*τ)) →
      let Q := fun (u : FreeRow) j=>
        HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z
      ∀main : Finset (Fin D.N),
      ∀bin : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t,
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun j=> D.ell j/d) Q bin
      let q := weightedMean Finset.univ (fun j=> D.ell j/d)
        (Cycle25DetectorRowCount.maskedGain main (binValue Finset.univ ((2*a-1)/2) D.t bin))
      rows'.Nonempty → 0 ≤ q ∧ q ≤ (2*a-1)/2 ∧
        (rows'.card:ℝ) ≤ C*C0*Z^(3*D.t)*
          (Z^d)^(Cycle25DetectorRowCount.rowCount (2*a-1) (q/(2*a-1)) D.momentKappa+(159*D.ε+9*D.t)) := by
  obtain ⟨C,hC,hcount⟩ := weighted_source_amplitude_count D F counts τ n hτ hτzero hτheight hτ2
  refine ⟨C,hC,?_⟩
  intro η
  filter_upwards [hcount η,eventually_gt_atTop (1:ℝ)] with Z hc hZ
  intro d a C0 hd hd' ha ha' hC0 rows hrows i hi hnext hcurrent z hz hzim hmom
  dsimp only
  intro main bin hne
  have hdpos : 0 < d := by linarith
  have hZpos : 0 < Z := zero_lt_one.trans hZ
  let Q := fun (u : FreeRow) j=>
    HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z
  have heq : physical F.modulus ⊤ (fun u : FreeRow=> u.val) (fun _ y=>(F.w y:ℂ))
      (fun _=>2) (fun j=> D.ell j/d) (fun _=> z) (Z^d)=Q := by
    funext u j
    exact Submission20261012.Global.Numerator.source_count_physical_eq D F Z d hZpos hdpos.ne' z u j
  have hb := hc d a C0 hd hd' ha ha' hC0 rows hrows i hi hnext hcurrent z hz hzim hmom
  dsimp only at hb
  rw [heq] at hb
  have hcard := (hb bin hne).2.2
  exact Cycle25DetectorRowCount.masked_amplitude_class_count rows Finset.univ main (Z^d) (2*a-1) D.momentKappa
    D.t D.t_pos (fun j=> D.ell j/d) Q bin (by linarith) (by linarith) D.momentKappa_lo D.momentKappa_hi
    (Real.one_le_rpow hZ.le hdpos.le)
    (fun j _=>(div_pos (D.slots_bounds j).1 hdpos).le)
    (by rw [←Finset.sum_div,D.slots_sum];exact div_pos Submission20261012.Global.ell_pos hdpos)
    (C*C0*Z^(3*D.t)) (159*D.ε+9*D.t)
    (by have := zero_le_one.trans hC;have := zero_le_one.trans hC0;positivity) hne hcard

end Submission20261012.Global.Detector
end

#print axioms Submission20261012.Global.Detector.weighted_source_masked_amplitude_count
end
/- END ORIGINAL MODULE Global.Detector.WeightedSourceMaskedCount -/

/- BEGIN ORIGINAL MODULE Global.Low.Reflection.LowFrozenEnergy ; sha256 e99e47685f3b963fe54f860b6b6ec922430202c0aded67f26d49396e1b8264b0 -/
section



/-! Adapted from OpenAI/math family003, pinned original module Reflection.LowFrozenEnergy.
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

theorem low_original_frozen_energy
    {γ : Type*} [Fintype γ] (a c₀ : γ→Eis) (mode : γ→Bool)
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (lo hi : ℝ) (hlo : 0< lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : ∀ i,FixedCuspShape (ControlledStratumArithmetic.fixedCusp (a i) (c₀ i) (mode i))) (hc₀ : ∀ i,c₀ i≠0)
    (hNlevel : ∀ i,(9:Eis)*c₀ i∣Nlevel)
    (hbase : ∀ i,if mode i then ConcretePrimeRowBridge.goodLambda^2∣a i-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀ i-1)
    (hac : ∀ i,IsCoprime (a i) (c₀ i))
    (Q : Ideal Eis) (hQ : Q≠0) (Ck η : ℝ) (hCk : 0< Ck) (hη : 0<η) (hη1 : η≤1) (rmax : ℕ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0< C ∧ 1< Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (J F Q₀ : Ideal Eis)
      (_hJ : J≠0) (_hF : F≠0),
    ∀ (Z d ell0 shift O₀ : ℝ),
      Z₀≤ Z → 0≤ d → d≤ Submission20261012.Global.ell → 0≤ ell0 → ell0≤ Submission20261012.Global.ell-d+η → |shift|≤η →
      O₀=normWidth Z (rowPowerfulPart J) → (Ideal.absNorm J:ℝ)≤ Ck*Z^((1-Submission20261012.Global.ell)-2*d) →
    ∀ (parents rows : Finset (Ideal Eis)),
      (∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤ Ck*Z^((1-Submission20261012.Global.ell)-2*d)) →
      rows⊆originalResidualRows parents J Q →
      (∀ P∈fixedBadPrimes,P∣Q) →
    Fintype.card σ≤ rmax → ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ)
      (_hdis : Pairwise (fun i j => Disjoint (lists i) (lists j)))
      (hmax : ∀ i,∀ P∈lists i,P.IsMaximal)
      (hgood : ∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P)
      (_hprime : ∀ i,∀ P∈lists i,Prime P)
      (hrows : ∀ K∈rows,Admissible K),
      (∀ i,1≤ H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤ H i) → (∏ i,H i)≤ Z^ell0 →
      (∀ f,IsCoprime (Ideal.span {Nlevel}) ((poolPrimeFamily J Q Q₀).ideal f)) →
      (∀ f,ringChar (Eis⧸(poolPrimeFamily J Q Q₀).ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime ((poolPrimeFamily J Q Q₀).ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ i,∀ P∈lists i,IsCoprime (Ideal.span {Nlevel}) P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
    ∃ D : ∀ g : γ,∀ A : Finset (FreeReflection.pool J Q Q₀),∀ T : Finset σ,
      OriginalSplitCompletion (N:=Nlevel) (a:=a g) (c:=c₀ g) (mode:=mode g)
        ((poolPrimeFamily J Q Q₀).restrict A) (poolPrimeFamily J Q Q₀).ideal
        rows hrows lists hmax hgood T,
    ∀ (θ : ℝ) (w : ∀ i,lists i→ℂ) (scalar : γ → rows → ℂ),
      (∀ i P,‖w i P‖≤1) → (∀ g K,‖scalar g K‖≤1) →
      (∑ K : rows,‖thetaDerivativeScalar⁻¹*∑ g : γ,scalar g K*
        ∑ A : Finset (FreeReflection.pool J Q Q₀),frozenInactiveWeight J F Q Q₀ A*
          ∑ T : Finset σ,originalInactivePhysical
            ((poolPrimeFamily J Q Q₀).restrict A) (poolPrimeFamily J Q Q₀).ideal
            rows hrows lists hmax hgood T (D g A T) (s g) (hc₀ g)
            (fun b : A => completedLocalExponent J F b.val.val)
            (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift)) w K‖^2)≤
        C*(1+‖θ‖)^degree*Z^(((1-Submission20261012.Global.ell)-d)+506*η-O₀/2) := by
  have hsubmissionEll := Submission20261012.Global.ell_interval
  obtain ⟨degree,C,Z₁,hC,hZ₁,he⟩ := low_original_inactive_energy a c₀ mode lo hi hlo W hWs hW
    s hc₀ hNlevel hbase hac Q hQ Ck η hCk hη hη1
  let ε := η/8
  have hε : 0<ε := by dsimp [ε];positivity
  obtain ⟨Cb,hCb,hcost⟩ := original_source_cost_budget (χ:=γ) rmax ε hε
  let Z₀ := max Z₁ (max 2 (max Ck (Ideal.absNorm Q:ℝ)))
  refine ⟨degree,(‖thetaDerivativeScalar⁻¹‖^2+1)*Cb*C,Z₀,by positivity,hZ₁.trans_le (le_max_left _ _),?_⟩
  intro σ _ _ J F Q₀ hJ hF Z d ell0 shift O₀ hZ hd hd1 hell hellcap hshift hOeq hJn
    parents rows hparents hsub hbad
    hcard lists H hdis hmax hgood hprime hrows hH1 hH hprod hGN hGchar hrowcop hLN hLchar
  have hz1 : Z₁≤ Z := (le_max_left _ _).trans hZ
  have hz : 1< Z := lt_of_lt_of_le hZ₁ hz1
  have hzp : 0< Z := lt_trans zero_lt_one hz
  let FF := (poolPrimeFamily J Q Q₀).ideal
  have hall := fun (g : γ) (A : Finset (FreeReflection.pool J Q Q₀)) (T : Finset σ) =>
    he g J F Q₀ hJ hF A Z d ell0 shift O₀
      hz1 hd hd1 hell hellcap hshift hOeq
      parents rows hparents hsub hbad lists H hdis hmax hgood hprime hrows hH1 hH hprod
      (fun f => hGN f.val) (fun f => hGchar f.val)
      (fun K hK => ⟨fun f => (hrowcop K hK).1 f.val,(hrowcop K hK).2⟩) hLN hLchar T
  choose D hD using hall
  refine ⟨D,?_⟩
  intro θ w scalar hw hscalar
  let energy := C*(1+‖θ‖)^degree*Z^(((1-Submission20261012.Global.ell)-d)+505*η-O₀/2)
  let harm := (∏ i,256*(columnDyadicLength (H i)+1:ℝ))^2
  let source := fun (g : γ) (A : Finset (FreeReflection.pool J Q Q₀)) (T : Finset σ) (K : rows) =>
    originalInactivePhysical ((poolPrimeFamily J Q Q₀).restrict A) FF rows hrows lists hmax hgood T
      (D g A T) (s g) (hc₀ g) (fun b : A => completedLocalExponent J F b.val.val)
      (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift)) w K
  have hs (g : γ) (A : Finset (FreeReflection.pool J Q Q₀)) (T : Finset σ) :
      (∑ K : rows,‖source g A T K‖^2)≤ harm*energy := by
    apply (hD g A T θ w hw).trans
    apply mul_le_mul_of_nonneg_right _ (by dsimp [energy];positivity)
    apply pow_le_pow_left₀ (by positivity)
    exact subtype_product_le_full (fun i => i∉T) (fun i => 256*(columnDyadicLength (H i)+1:ℝ)) (fun i => by have hn : (0:ℝ)≤ columnDyadicLength (H i) := Nat.cast_nonneg _; linarith)
  let Labels := γ×(Finset (FreeReflection.pool J Q Q₀)×Finset σ)
  let f := fun (b : Labels) (K : rows) => (scalar b.1 K*frozenInactiveWeight J F Q Q₀ b.2.1)*source b.1 b.2.1 b.2.2 K
  have hf (b : Labels) : (∑ K : rows,‖f b K‖^2)≤ harm*energy := by
    apply (bounded_row_multiplier_energy Finset.univ _ _ (fun K hK => ?_)).trans (hs b.1 b.2.1 b.2.2)
    rw [norm_mul]
    exact (mul_le_mul (hscalar b.1 K) (frozenInactiveWeight_norm J F Q Q₀ b.2.1)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hfam := weighted_finite_row_energy_uniform (Finset.univ : Finset Labels) (Finset.univ : Finset rows)
    (fun _ => (1:ℂ)) f (harm*energy) (fun b _ => hf b)
  simp only [one_mul,norm_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hfam
  have hid (K : rows) : (∑ b : Labels,f b K)=∑ g : γ,scalar g K*
      ∑ A : Finset (FreeReflection.pool J Q Q₀),frozenInactiveWeight J F Q Q₀ A*
        ∑ T : Finset σ,source g A T K := by
    simp only [Labels,f,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]
  have hsource : (∑ K : rows,‖thetaDerivativeScalar⁻¹*∑ g : γ,scalar g K*
      ∑ A : Finset (FreeReflection.pool J Q Q₀),frozenInactiveWeight J F Q Q₀ A*
        ∑ T : Finset σ,source g A T K‖^2)≤
      ‖thetaDerivativeScalar⁻¹‖^2*(Fintype.card Labels:ℝ)^2*harm*energy := by
    simp_rw [←hid]
    simp only [norm_mul,mul_pow,←Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left hfam (sq_nonneg _)).trans_eq (by ring)
  apply hsource.trans
  have hQn : (Ideal.absNorm Q:ℝ)≤ Z := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hZ))
  have hCkZ : Ck≤ Z := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hZ))
  have hJcap : (Ideal.absNorm J:ℝ)≤ Z^(2:ℝ) := by
    apply hJn.trans
    calc
      Ck*Z^((1-Submission20261012.Global.ell)-2*d) ≤ Z*Z^((1-Submission20261012.Global.ell)-2*d) := mul_le_mul_of_nonneg_right hCkZ (Real.rpow_nonneg hzp.le _)
      _ = Z^(1+((1-Submission20261012.Global.ell)-2*d)) := by rw [Real.rpow_add hzp,Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hz.le (by linarith [Submission20261012.Global.ell_pos,Submission20261012.Global.ell_lt_one_fifth])
  have hpool : (Ideal.absNorm (J*Q):ℝ)≤ Z^(3:ℝ) := by
    rw [map_mul,Nat.cast_mul]
    calc
      _ ≤ Z^(2:ℝ)*Z := mul_le_mul hJcap hQn (Nat.cast_nonneg _) (Real.rpow_nonneg hzp.le _)
      _ = _ := by norm_num;ring
  have hslot : (∏ i,H i)≤ Z^(2:ℝ) := hprod.trans
    (Real.rpow_le_rpow_of_exponent_le hz.le (by linarith [Submission20261012.Global.ell_pos,Submission20261012.Global.ell_lt_one_fifth]))
  have hcst := hcost H hcard hH1 J Q Q₀ hJ hQ Z 3 2 η hz hpool hslot (by dsimp [ε];linarith)
  calc
    _ = ‖thetaDerivativeScalar⁻¹‖^2*((Fintype.card Labels:ℝ)^2*harm)*energy := by ring
    _ ≤ (‖thetaDerivativeScalar⁻¹‖^2+1)*(Cb*Z^(η))*energy := by
      apply mul_le_mul_of_nonneg_right _ (by dsimp [energy];positivity)
      exact mul_le_mul (by linarith [Submission20261012.Global.ell_pos,Submission20261012.Global.ell_lt_one_fifth]) hcst (by dsimp [harm];positivity) (by positivity)
    _ = ((‖thetaDerivativeScalar⁻¹‖^2+1)*Cb*C)*(1+‖θ‖)^degree*
        Z^(η+(((1-Submission20261012.Global.ell)-d)+505*η-O₀/2)) := by
      dsimp only [energy]
      rw [Real.rpow_add hzp]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hz.le (by linarith [Submission20261012.Global.ell_pos,Submission20261012.Global.ell_lt_one_fifth])) (by positivity)
end
end LowReflection

end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Low.Reflection.LowFrozenEnergy -/
