import Candidate.Cycle63.Physical.InitialMass.GeometrySecondSplit
import Candidate.Cycle63.Physical.InitialMass.GeometryErrorActiveInput

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentSecondLocalization CenteredMomentSourceSecondZeroEnergy
open CenteredMomentSupportedTailAggregate EisensteinSchwartzPoisson
open CenteredMomentCommonAllocationSum CenteredMomentFirstAnnularInput
open CenteredMomentCommonProfile CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationActiveFactor CenteredMomentPrimeElements
open CenteredMomentFirstPhysicalSource CenteredMomentSourceLiveColumn
open CenteredMomentFirstReferenceSource CenteredMomentAmplifiedRetainedRadius
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O
local instance {ι : Type*} : DecidableEq ι := Classical.decEq _

theorem actual_heterogeneous_normalized_source_budget {Label : Type*} [Fintype Label]
    (α : Label→Type*) [∀l,Fintype (α l)] (s : (l : Label)→Input (α l))
    (R seed : Label→Ideal O) (W : 𝓢(ℝ,ℂ)) (K Tsec : Label→ℝ) (Z ξ : ℝ)
    (hK : ∀l,0<K l)(weight : Label→ℝ)(hw : ∀l,0≤weight l) :
    (∑l,weight l*normalizedGaussSource (s l) (R l) (seed l) W (K l))≤
      (∑l,(weight l/volume (s l))*(‖originalSecondZero (s l) (R l) (seed l) W (K l)‖+
        ‖secondDiscardedEnergy (s l).η (s l).t (original (s l) (R l) (seed l)).columns
          (original (s l) (R l) (seed l)).beta W (K l) (Tsec l) Z ξ‖))+
      ‖∑l,((weight l/volume (s l):ℝ):ℂ)*secondRetainedEnergy (s l).η (s l).t
        (original (s l) (R l) (seed l)).columns (original (s l) (R l) (seed l)).beta
          W (K l) (Tsec l) Z ξ‖ := by
  let ret := fun l=>secondRetainedEnergy (s l).η (s l).t
    (original (s l) (R l) (seed l)).columns (original (s l) (R l) (seed l)).beta
      W (K l) (Tsec l) Z ξ
  let tail := fun l=>secondDiscardedEnergy (s l).η (s l).t
    (original (s l) (R l) (seed l)).columns (original (s l) (R l) (seed l)).beta
      W (K l) (Tsec l) Z ξ
  let zero := fun l=>originalSecondZero (s l) (R l) (seed l) W (K l)
  let c := fun l=>weight l/volume (s l)
  have hc (l : Label) : 0≤c l := div_nonneg (hw l) (volume_pos (s l)).le
  have he (l : Label) : weight l*normalizedGaussSource (s l) (R l) (seed l) W (K l)=
      c l*(zero l).re+c l*(ret l).re+c l*(tail l).re := by
    unfold normalizedGaussSource
    rw [sourceGaussEnergy_localized _ _ _ _ W (K l) (Tsec l) Z ξ (hK l)]
    simp only [Complex.add_re]
    dsimp only [c,zero,ret,tail,originalSecondZero]
    ring
  have hr : (∑l,c l*(ret l).re)≤‖∑l,(c l:ℂ)*ret l‖ := by
    have heq : (∑l,c l*(ret l).re)=(∑l,(c l:ℂ)*ret l).re := by
      simp only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rw [heq]
    exact Complex.re_le_norm _
  have hz : (∑l,(c l*(zero l).re+c l*(tail l).re))≤
      ∑l,c l*(‖zero l‖+‖tail l‖) := by
    apply Finset.sum_le_sum
    intro l hl
    calc
      _≤c l*‖zero l‖+c l*‖tail l‖ := add_le_add
        (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (hc l))
        (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (hc l))
      _=_ := by ring
  simp_rw [he]
  calc
    _=(∑l,(c l*(zero l).re+c l*(tail l).re))+(∑l,c l*(ret l).re) := by
      simp only [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro l hl
      ring
    _≤_ := add_le_add hz hr


/-- The literal extracted-prime sources, across a heterogeneous family
of first common children, retain one joint second-transform sum. -/
theorem actual_joint_error_second_split {First : Type*}[Fintype First]
    (α : First→Type*) [∀q,Fintype (α q)]
    (s : (q : First)→Input (α q))(g : First→FirstBranchGeometry)
    (w : First→ℝ)(hw : ∀q,0≤w q)(Z sigma Csec ξ reserve : ℝ)(hZ : 0<Z)
    (P : Finset (Ideal O))
    (τ : First→elementPool P→Fin 3→RayCharacter→Character) :
    let Label := (q : First) × (p : elementPool P) × (i : Fin 3) ×
      (_ψ : RayCharacter) × actualAllocations (activeInput (s q)).pools
        ((Ideal.span {p.val})^(errorIndex i+1))
    let E := fun l : Label=>(Ideal.span {l.2.1.val})^(errorIndex l.2.2.1+1)
    let source := fun l : Label=>child (s l.1) (E l) (g l.1).R
      (errorActiveAllocation (s l.1) _ l.2.2.2.2) (τ l.1 l.2.1 l.2.2.1 l.2.2.2.1) (s l.1).t
    let radius := fun l : Label=>errorCommonRadius Z (g l.1).d
      (nominalLog (g l.1).I (g l.1).J (g l.1).E (g l.1).K (g l.1).X Z)
      (g l.1).cLog sigma (frequencyLoss Z (32*Csec) ξ) reserve l.2.1.val (errorIndex l.2.2.1+1)
    let coeff := fun l : Label=>w l.1*
      (16*(errorIndex l.2.2.1+2:ℝ)*localErrorCost l.2.1.val (errorIndex l.2.2.1))
    let c := fun l : Label=>coeff l/volume (source l)
    ∀Tsec : Label→ℝ,
    (∑q : First,w q*actualErrorSources (s q) (g q) Z sigma Csec ξ reserve P (τ q))≤
      (∑l : Label,c l*(‖originalSecondZero (source l) ((g l.1).R*E l) (g l.1).seed ballProfile (radius l)‖+
        ‖secondDiscardedEnergy (source l).η (source l).t
          (original (source l) ((g l.1).R*E l) (g l.1).seed).columns
          (original (source l) ((g l.1).R*E l) (g l.1).seed).beta
          ballProfile (radius l) (Tsec l) Z ξ‖))+
      ‖∑l : Label,(c l:ℂ)*secondRetainedEnergy (source l).η (source l).t
        (original (source l) ((g l.1).R*E l) (g l.1).seed).columns
        (original (source l) ((g l.1).R*E l) (g l.1).seed).beta
        ballProfile (radius l) (Tsec l) Z ξ‖ := by
  intro Label E source radius coeff c Tsec
  have hh := actual_heterogeneous_normalized_source_budget
    (fun l : Label=>liveIndices l.2.2.2.2.val) source
    (fun l=>(g l.1).R*E l) (fun l=>(g l.1).seed) ballProfile radius Tsec Z ξ
    (fun l=>Real.rpow_pos_of_pos hZ _) coeff (by
      intro l
      have he := localErrorCost_nonneg l.2.1.val (errorIndex l.2.2.1)
      have hwq := hw l.1
      dsimp only [coeff]
      positivity)
  apply (le_of_eq ?_).trans hh
  simp_rw [actual_error_sources_lifted]
  simp only [Label,Fintype.sum_sigma,Finset.mul_sum,childNormalizedGaussSource]
  dsimp only [coeff,source,radius,E]
  simp only [mul_assoc]
  rfl

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_heterogeneous_normalized_source_budget
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_joint_error_second_split
