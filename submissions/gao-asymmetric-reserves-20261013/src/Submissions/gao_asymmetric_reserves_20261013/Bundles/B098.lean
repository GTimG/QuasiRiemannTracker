/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B067
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B069
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B084
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B096
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B097
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstDivisorSupport
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstSourceConductorCaps
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondExceptionalPhysicalSaving

/- BEGIN ORIGINAL MODULE Analytic.ActualErrorSourceGates ; sha256 b0b46bd8c93f774bef1adc9c7cc4a2fefacc8c877b58341b7ad01fbb4ff2d9e3 -/
section



/-! The error families chosen by actual amplification supply both the
relative moving-conductor bound and the absolute Ready conductor cap. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI
noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplificationRadicalFamily
open CenteredMomentAmplificationActiveFactor CenteredMomentChildRows
open CenteredMomentFirstSourceConductorCaps CenteredMomentFirstScale
open CenteredMomentFirstPhysicalSource CenteredMomentPrimeElements CenteredMomentPrimePool
open CenteredMomentSecondHeightFamily CenteredMomentSectorLocalization CenteredMomentCanonicalFirst
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstSectors
open RayFourExpansion
local notation "O" => HeckeFamily.O

lemma actual_error_radical_moving_cap
    (ρ υ : Character) (χ : RayCharacter) (p : O) (hp : p ≠ 0)
    (Z cost : ℝ) (hZ : 1 < Z) (hcost : rayCost ≤ cost) (i : Fin 3)
    (hυ : υ.modulus.absNorm ≤ radicalBound (childCharacter ρ χ) fixedBadMask p
      (errorMovingExponent (errorIndex i))) :
    (υ.modulus.absNorm : ℝ) ≤ cost*(ρ.modulus.absNorm : ℝ)*Z^(errorMoving p Z (errorIndex i+1)) := by
  have hi : errorIndex i=0 ∨ errorIndex i=5 ∨ errorIndex i=6 := by fin_cases i <;> norm_num [errorIndex]
  have hrad := radicalBound_error_power (childCharacter ρ χ) fixedBadMask p hp Z hZ (errorIndex i) hi
  have hh : (υ.modulus.absNorm : ℝ) ≤ (radicalBound (childCharacter ρ χ) fixedBadMask p
      (errorMovingExponent (errorIndex i)) : ℝ) := by exact_mod_cast hυ
  rw [hrad] at hh
  have hc := CenteredMomentSecondRadicalBudget.child_modulus_bound ρ χ
  have hc' : ((childCharacter ρ χ).modulus.absNorm : ℝ) ≤
      (ρ.modulus.absNorm : ℝ)*(Ideal.span {(12 : O)}).absNorm := by exact_mod_cast hc
  calc
    _ ≤ _ := hh
    _ ≤ ((ρ.modulus.absNorm : ℝ)*(Ideal.span {(12 : O)}).absNorm*
        (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72 : O)}).absNorm)*
        Z^(errorMoving p Z (errorIndex i+1)) := by gcongr
    _ = rayCost*(ρ.modulus.absNorm : ℝ)*Z^(errorMoving p Z (errorIndex i+1)) := by
      unfold rayCost fixedPresentationCost
      ring
    _ ≤ _ := by gcongr

theorem eventually_fixed_pair_error_source_caps
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes ⊆ Sbad)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (η : Character) (C D : Ideal O) (hC : Supported C)
      (E : Finset (CommonIndex C D)) (ξ₁ ξ₂ : RayCharacter)
      (F : FixedPair η C D hC E ξ₁ ξ₂),
    ∀ (q B sigma cost qmoving : ℝ), (η.modulus.absNorm : ℝ) ≤ Z^q →
      (C.absNorm : ℝ) ≤ Z^B → rayCost ≤ cost → q+2*B+sigma/3+ε ≤ qmoving →
    let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
    ∀ (ρ υ : Character), (ρ=F.left ∨ ρ=F.right) → ∀ (χ : RayCharacter) (p : elementPool P) (i : Fin 3),
      υ.modulus.absNorm ≤ radicalBound (childCharacter ρ χ) fixedBadMask p
        (errorMovingExponent (errorIndex i)) →
      (υ.modulus.absNorm : ℝ) ≤ cost*(ρ.modulus.absNorm : ℝ)*Z^(errorMoving p Z (errorIndex i+1)) ∧
      (υ.modulus.absNorm : ℝ) ≤ Z^qmoving := by
  filter_upwards [CenteredMomentFirstSourceConductorCaps.eventually_caps ε hε] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro η C D hC E ξ₁ ξ₂ F q B sigma cost qmoving hη hCcap hcost hq
  dsimp only
  intro ρ υ hρ χ p i hυ
  have hp := elementPool_data _
    (fun Q hQ => (primePool_data M H Sbad hbad _ _ _ Q hQ).1)
    (fun Q hQ => (primePool_data M H Sbad hbad _ _ _ Q hQ).2) p p.property
  have hprime : ((Ideal.span {p.val}).absNorm : ℝ) ≤ Z^(sigma/3) := by
    have hmem := (Finset.mem_sdiff.mp hp.2.1).1
    have hn := (PNT.AnnularPrimeMass.norm_bounds_of_mem_annularPrimeIdeals
      (show (0 : ℝ) ≤ 1/2 by norm_num) (show (1/2 : ℝ) ≤ 1 by norm_num)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ.1) _) hmem).2
    simpa only [one_mul,mul_one] using hn
  refine ⟨actual_error_radical_moving_cap ρ υ χ p hp.1.ne_zero Z cost hZ.1 hcost i hυ,?_⟩
  have hh := (hZ.2 η C D hC E ξ₁ ξ₂ F q B hη hCcap).2.2 ρ υ hρ χ p hp.1.ne_zero
    (errorMovingExponent (errorIndex i)) (sigma/3) hυ hprime
  exact hh.trans (Real.rpow_le_rpow_of_exponent_le hZ.1.le hq)

/-- Every actual first label already has both common norms bounded by
the parent support radius; these are not extra profile assumptions. -/
lemma actual_first_label_norm_caps {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (R seed : Ideal O) (hseed : Squarefree seed)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (Z B : ℝ)
    (hcap : sourceRadius s ≤ Z^B) (p : Labels s R seed) :
    (p.val.1.absNorm : ℝ) ≤ Z^B ∧ (p.val.2.absNorm : ℝ) ≤ Z^B := by
  have hh := actual_common_gates s R seed hseed hz₁ hz₂ p.val.1 p.val.2 p.property
  exact ⟨hh.2.2.2.2.2.1.trans hcap,hh.2.2.2.2.2.2.trans hcap⟩

#print axioms eventually_fixed_pair_error_source_caps
#print axioms actual_first_label_norm_caps
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.ActualErrorSourceGates -/

/- BEGIN ORIGINAL MODULE Analytic.ActualFirstErrorIdentity ; sha256 11076682b66a4bb7f01bbc1b2d04de8b6dc8bcdf5dfde8d782b74d2a9e42c674 -/
section


/-! The final allowance-weight expression is exactly the first source
scalar paired with the literal allocated extracted-error averages. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT ConcretePrimeRowBridge
open CompletedGauss CenteredMomentSectorLocalization CenteredMomentCanonicalFirst ActualEisensteinCubic
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentFirstAnnularInput
open CenteredMomentAmplificationErrorEnergy CenteredMomentFirstPhysicalSource
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstNonexceptionalFixedWeightSum
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentFirstSectors
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentActiveSource CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentSupportedCorrelation CenteredMomentSecondRetainedAggregate
open CenteredMomentFirstScale CenteredMomentFirstMixedAllowance RayFourExpansion
open CenteredMomentSecondHeightFamily CenteredMomentPrimeElements
local notation "O" => HeckeFamily.O
local instance actualFirstErrorIdentityDecEq {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

lemma firstExtractedErrors_nonneg {ι : Type*} [Fintype ι]
    (s : Input ι) (R seed : Ideal O) (Z d K₀ c sigma delta reserve : ℝ) (hZ : 0 < Z)
    (p : O) (family : Fin 3 → RayCharacter → Character) :
    0 ≤ firstExtractedErrors s R seed Z d K₀ c sigma delta reserve p family := by
  unfold firstExtractedErrors
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (mul_nonneg (by positivity) (localErrorCost_nonneg _ _))
  apply Finset.sum_nonneg
  intro χ _
  apply Finset.sum_nonneg
  intro B _
  exact normalizedGaussSource_ball_nonneg _ _ _ _
    (Real.rpow_pos_of_pos hZ _)

lemma allocatedExtractedErrors_nonneg {ι : Type*} [Fintype ι]
    (N : ℕ) (s : Input ι) (C R seed : Ideal O) (τ : Character)
    (t b Z d K₀ c sigma delta reserve : ℝ) (hZ : 0 < Z) (P : Finset (Ideal O))
    (family : actualAllocations s.pools C → elementPool P → Fin 3 → RayCharacter → Character) :
    0 ≤ allocatedExtractedErrors N s C R seed τ t b Z d K₀ c sigma delta reserve P family := by
  unfold allocatedExtractedErrors
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro B _
  split_ifs
  · apply mul_nonneg (sq_nonneg _)
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun p _ => firstExtractedErrors_nonneg _ _ _ _ _ _ _ _ _ _ hZ _ _)
  · exact le_rfl

namespace ExtractedErrorRun
variable {ι : Type*} [Fintype ι] {s : Input ι} {C : Ideal O} {P : Finset (Ideal O)}

def value (x : ExtractedErrorRun s C P) (N : ℕ) (D R seed : Ideal O)
    (E : Finset (CommonIndex C D)) (τ : Character) (upper Z K sigma delta reserve : ℝ) : ℝ :=
  allocatedExtractedErrors N s C R seed τ x.height upper Z
    (Real.logb Z (D.absNorm : ℝ))
    (Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun Q : CommonIndex C D => Q.val) E}) K (volume s)))
    (Real.logb Z (C.absNorm : ℝ)) sigma delta reserve P x.family

lemma value_nonneg (x : ExtractedErrorRun s C P) (N : ℕ) (D R seed : Ideal O)
    (E : Finset (CommonIndex C D)) (τ : Character) (upper Z K sigma delta reserve : ℝ)
    (hZ : 0 < Z) : 0 ≤ x.value N D R seed E τ upper Z K sigma delta reserve :=
  allocatedExtractedErrors_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hZ _ _

end ExtractedErrorRun

theorem first_extracted_error_pair_eq_source_scalar {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (s : Input ι) (R seedOuter seed : Ideal O) (m A : O) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ) (K r Z upper sigma delta reserve : ℝ) (hZ : 0 < Z)
    (P : Finset (Ideal O)) (p : Labels s R seedOuter)
    (E : Finset (CommonIndex p.val.1 p.val.2)) (τ₁ τ₂ : Character)
    (n : Blocks (effectiveScale p.val.1 p.val.2 E K) r
      (sourceRadius s/p.val.1.absNorm) (sourceRadius s/p.val.2.absNorm))
    (left : ExtractedErrorRun s p.val.1 P) (right : ExtractedErrorRun s p.val.2 P) :
    let h := commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seedOuter)) _ _ p.property
    allowanceWeight s R seedOuter m A t W V K r Z p E τ₁ τ₂ n *
      (Real.sqrt (left.normalizedValue N p.val.2 R seed E τ₁ upper Z K sigma delta reserve)*
       Real.sqrt (right.normalizedValue N p.val.1 R seed
         (CenteredMomentFirstMixedRightTransport.swapSubset p.val.1 p.val.2 E) τ₂ upper Z K sigma delta reserve)) =
    if block s.η m A t (finiteColumns (Fintype.piFinset s.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seedOuter) p.val.1 p.val.2 h.1 h.2 E
      (CenteredMomentSecondRetainedRows.retainedRows r 1) W V K
      (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3)) = 0 then 0
    else ‖scalar p.val.1 p.val.2 h.1 E K (dyadicScale (n 2)) (dyadicScale (n 3))‖*
      Real.sqrt (left.value N p.val.2 R seed E τ₁ upper Z K sigma delta reserve)*
      Real.sqrt (right.value N p.val.1 R seed
        (CenteredMomentFirstMixedRightTransport.swapSubset p.val.1 p.val.2 E) τ₂ upper Z K sigma delta reserve) := by
  exact allowance_weight_pair_eq_source_scalar s R seedOuter m A t W V K r Z hZ p E τ₁ τ₂ n
    (left.value N p.val.2 R seed E τ₁ upper Z K sigma delta reserve)
    (right.value N p.val.1 R seed
      (CenteredMomentFirstMixedRightTransport.swapSubset p.val.1 p.val.2 E) τ₂ upper Z K sigma delta reserve)
    (left.value_nonneg N p.val.2 R seed E τ₁ upper Z K sigma delta reserve hZ)
    (right.value_nonneg N p.val.1 R seed
      (CenteredMomentFirstMixedRightTransport.swapSubset p.val.1 p.val.2 E) τ₂ upper Z K sigma delta reserve hZ)

#print axioms first_extracted_error_pair_eq_source_scalar
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.ActualFirstErrorIdentity -/

/- BEGIN ORIGINAL MODULE Analytic.JointCoherentExceptionalScalar ; sha256 7e4346a58cffa911ebd7ca0115c630adefb410fc5468a6382c9232ff7e52db69 -/
section



/-! Exact original-volume normalization of the coherent exceptional kernel.
The first extraction remains outside the actual second physical ledger. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCanonicalFirst
open CenteredMomentSecondPhysicalLedger CenteredMomentSecondExceptionalPhysicalSaving
open CenteredMomentSecondCanonicalScalar CenteredMomentSectorLocalization
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentRankinRadical CenteredMomentFirstCanonicalAllowance
open CenteredMomentForcing CenteredMomentChildRows CompletedGauss
local notation "O" => HeckeFamily.O

def coherentExceptionalScalar (V P N : ℝ) (C D : Ideal O)
    (U : Finset (CommonIndex C D)) (K : ℝ) (n : Fin 4 → ℤ) : ℝ :=
  secondPrecountFactor V P C D U K n *
    (V/Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3))) *
    ((dyadicScale (n 1))^(1/6:ℝ)/(forcingNorm C D U)^(2/3:ℝ)) *
    (V/(N^2*((C.absNorm:ℝ)*D.absNorm))) /
    (1+SecondKernelLabel.kernelScale n)

theorem coherent_exceptional_scalar_exact (V P N : ℝ) (hV : 0 < V) (hP : 0 < P) (hN : 0 < N)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (K : ℝ) (n : Fin 4 → ℤ) :
    coherentExceptionalScalar V P N C D U K n =
      (N*P)⁻¹*centralPhysicalCost C D U K (V/N) n/
        (((commonRadical C D).absNorm : ℝ)*(forcingNorm C D U)^(1/3:ℝ)) := by
  have hf : 0 < forcingNorm C D U := common_product_pos C D hC _
  have hp : 0 < ((commonRadical C D).absNorm : ℝ) := by
    rw [←common_ideal_product]
    exact common_product_pos C D hC Finset.univ
  have hfp : (forcingNorm C D U)^(2/3:ℝ) =
      (forcingNorm C D U)^(1/3:ℝ)*(forcingNorm C D U)^(1/3:ℝ) := by
    rw [←Real.rpow_add hf]
    congr 1
    ring
  have hs : Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3)) ≠ 0 :=
    (Real.sqrt_pos.mpr (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))).ne'
  unfold coherentExceptionalScalar secondPrecountFactor centralPhysicalCost SecondKernelLabel.kernelScale
  rw [hfp,common_ideal_product]
  field_simp
  <;> ring

theorem coherent_exceptional_scalar_physical (V P N : ℝ) (hV : 0 < V) (hP : 0 < P) (hN : 0 < N)
    (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D) (U : Finset (CommonIndex C D))
    (R : ℝ) (rows : Finset O) (hrows : ∀ z ∈ rows,z ≠ 0) (W : 𝓢(ℝ,ℂ))
    (K : ℝ) (hK : 0 < K) (n : Fin 4 → ℤ) (a Z : ℝ) (ha : 0 < a) (hZ : 1 < Z)
    (hlower : ∀ I : Ideal O, β I ≠ 0 → a*(V/N) ≤ (I.absNorm : ℝ))
    (hne : physicalBlock η t S β C D hC hD U R rows W K n ≠ 0) :
    coherentExceptionalScalar V P N C D U K n ≤
      (N*P)⁻¹*((V/N)^(1/3:ℝ)*K^(5/6:ℝ)*a^(-2/3:ℝ)*
        Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3))/
          ((commonRadical C D).absNorm : ℝ) := by
  have hb := original_block_physical_cost η t S β C D hC hD hCD U R rows hrows W K n
    hK (V/N) a Z (div_pos hV hN) ha hZ hlower hne
  have hp : 0 < ((commonRadical C D).absNorm : ℝ) := by
    rw [←common_ideal_product]
    exact common_product_pos C D hC Finset.univ
  have hf : 1 ≤ (forcingNorm C D U)^(1/3:ℝ) :=
    Real.one_le_rpow (forcingNorm_ge_one C D hC U) (by norm_num)
  rw [coherent_exceptional_scalar_exact V P N hV hP hN C D hC hD U K n]
  calc
    _ ≤ (N*P)⁻¹*((V/N)^(1/3:ℝ)*K^(5/6:ℝ)*a^(-2/3:ℝ)*
        Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3))/
          (((commonRadical C D).absNorm : ℝ)*(forcingNorm C D U)^(1/3:ℝ)) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by positivity)) (by positivity)
    _ ≤ _ := by
      apply div_le_div_of_nonneg_left (by positivity) hp
      exact le_mul_of_one_le_right hp.le hf

#print axioms coherent_exceptional_scalar_exact
#print axioms coherent_exceptional_scalar_physical
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCoherentExceptionalScalar -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstProjectorSupport ; sha256 464f9b921793212512051b33e7081f9f5593ae78bb1c83f1c2c947ae2fa7274b -/
section



/-! The exact first energies discard projector ideals outside the
nonzero source support before applying the amplifier. Their surviving
projectors are squarefree by the actual Möbius coefficient filter. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFirstDivisorSupport CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstDivisorCommonBound CenteredMomentFirstPhysicalSource
local notation "O" => HeckeFamily.O
variable {ι Λ : Type*} [Fintype ι] [DecidableEq Λ]

def firstLeftSourceLabels (labels : Finset Λ) (q : Λ → FirstJointLabel ι) (H : Λ → ℝ) :=
  (firstSourceLabels labels q).filter (fun k =>
    ((k.2.1.val).absNorm : ℝ) ≤ H k.1/((q k.1).C.absNorm : ℝ))

def firstRightSourceLabels (labels : Finset Λ) (q : Λ → FirstJointLabel ι) (H : Λ → ℝ) :=
  (firstSourceLabels labels q).filter (fun k =>
    ((k.2.1.val).absNorm : ℝ) ≤ H k.1/((q k.1).D.absNorm : ℝ))

theorem first_leftEnergy_eq_supported (labels : Finset Λ) (q : Λ → FirstJointLabel ι)
    (H : Λ → ℝ)
    (hsource : ∀ l ∈ labels, ∀ I, (q l).data.beta I ≠ 0 → (I.absNorm : ℝ) ≤ H l)
    (t : ((l : Λ) × (q l).SourceIndex) → ℝ)
    (W : ((l : Λ) × (q l).SourceIndex) → 𝓢(ℝ,ℂ))
    (K : ((l : Λ) × (q l).SourceIndex) → ℝ) :
    (∑ k ∈ firstSourceLabels labels q, ((q k.1).sourceChild k.2).leftEnergy (t k) (W k) (K k)) =
      ∑ k ∈ firstLeftSourceLabels labels q H,
        ((q k.1).sourceChild k.2).leftEnergy (t k) (W k) (K k) := by
  rw [firstLeftSourceLabels,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs with h
  · rfl
  · have hl := (Finset.mem_sigma.mp hk).1
    have hz := commonEnergy_zero (q k.1).data (q k.1).C (q k.1).hC (H k.1)
      (hsource k.1 hl) k.2.1.val (lt_of_not_ge h)
      ((q k.1).sourceChild k.2).pair.left (t k) (W k) (K k)
    exact congrArg Complex.re hz

theorem first_rightEnergy_eq_supported (labels : Finset Λ) (q : Λ → FirstJointLabel ι)
    (H : Λ → ℝ)
    (hsource : ∀ l ∈ labels, ∀ I, (q l).data.beta I ≠ 0 → (I.absNorm : ℝ) ≤ H l)
    (t : ((l : Λ) × (q l).SourceIndex) → ℝ)
    (W : ((l : Λ) × (q l).SourceIndex) → 𝓢(ℝ,ℂ))
    (K : ((l : Λ) × (q l).SourceIndex) → ℝ) :
    (∑ k ∈ firstSourceLabels labels q, ((q k.1).sourceChild k.2).rightEnergy (t k) (W k) (K k)) =
      ∑ k ∈ firstRightSourceLabels labels q H,
        ((q k.1).sourceChild k.2).rightEnergy (t k) (W k) (K k) := by
  rw [firstRightSourceLabels,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs with h
  · rfl
  · have hl := (Finset.mem_sigma.mp hk).1
    have hz := commonEnergy_zero (q k.1).data (q k.1).D (q k.1).hD (H k.1)
      (hsource k.1 hl) k.2.1.val (lt_of_not_ge h)
      ((q k.1).sourceChild k.2).pair.right (t k) (W k) (K k)
    exact congrArg Complex.re hz

theorem firstLeftSourceLabels_gates (labels : Finset Λ) (q : Λ → FirstJointLabel ι)
    (H : Λ → ℝ) (Z B : ℝ) (hZ : 0 ≤ Z)
    (hH : ∀ l ∈ labels, H l ≤ Z^B)
    (k : (l : Λ) × (q l).SourceIndex) (hk : k ∈ firstLeftSourceLabels labels q H) :
    k.1 ∈ labels ∧ Squarefree k.2.1.val ∧ k.2.1.val ≠ 0 ∧ ((k.2.1.val).absNorm : ℝ) ≤ Z^B := by
  obtain ⟨hk,hcap⟩ := Finset.mem_filter.mp hk
  have hl := (Finset.mem_sigma.mp hk).1
  have hsf := (q k.1).projector_squarefree _ k.2.1.property
  have hn : (1:ℝ) ≤ (q k.1).C.absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (q k.1).hC.1)
  refine ⟨hl,hsf,hsf.ne_zero,?_⟩
  exact hcap.trans ((div_le_div_of_nonneg_right (hH k.1 hl) (zero_le_one.trans hn)).trans
    (div_le_self (Real.rpow_nonneg hZ _) hn))

theorem firstRightSourceLabels_gates (labels : Finset Λ) (q : Λ → FirstJointLabel ι)
    (H : Λ → ℝ) (Z B : ℝ) (hZ : 0 ≤ Z)
    (hH : ∀ l ∈ labels, H l ≤ Z^B)
    (k : (l : Λ) × (q l).SourceIndex) (hk : k ∈ firstRightSourceLabels labels q H) :
    k.1 ∈ labels ∧ Squarefree k.2.1.val ∧ k.2.1.val ≠ 0 ∧ ((k.2.1.val).absNorm : ℝ) ≤ Z^B := by
  obtain ⟨hk,hcap⟩ := Finset.mem_filter.mp hk
  have hl := (Finset.mem_sigma.mp hk).1
  have hsf := (q k.1).projector_squarefree _ k.2.1.property
  have hn : (1:ℝ) ≤ (q k.1).D.absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (q k.1).hD.1)
  refine ⟨hl,hsf,hsf.ne_zero,?_⟩
  exact hcap.trans ((div_le_div_of_nonneg_right (hH k.1 hl) (zero_le_one.trans hn)).trans
    (div_le_self (Real.rpow_nonneg hZ _) hn))

#print axioms first_leftEnergy_eq_supported
#print axioms firstLeftSourceLabels_gates
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstProjectorSupport -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstVariableActualSector ; sha256 34aeaa3bb8128ed3b70fd5f6a7d06c04b6b2502fce3e71f51caa78224fcecc46 -/
section




/-! The actual first sector needs only bounded Fourier joint targets.
The literal source coarse sums and lower target exponents are supplied
by the source geometry, before the first Fourier kernel is integrated. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT RayFourExpansion
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentCanonicalFirst
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentSourceMass CenteredMomentSourceRow CenteredMomentActiveSource
open CenteredMomentSecondRetainedAggregate CenteredMomentFirstSectors
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
local instance firstVariableActualSectorDecidableSum {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem eventually_actual_first_variable_sector_from_local_targets
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Wkernel : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ)
    (Mwin : Fin 4 → ℝ) (hMwin : ∀ i, 0 ≤ Mwin i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ Mwin i)
    (hV₂c : HasCompactSupport (V 2)) (hV₂s : ContDiff ℝ ∞ (V 2))
    (hV₃c : HasCompactSupport (V 3)) (hV₃s : ContDiff ℝ ∞ (V 3))
    (decay Ncap : ℕ) (ν F U b₁ b₂ B₁ B₂ D B L Cr Amin Amax J : ℝ)
    (hν : 0 < ν) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hD : 0 ≤ D)
    (hB : 0 ≤ B) (hL : 0 ≤ L) (hCr : 0 < Cr) (hJ : 0 ≤ J) :
    ∃ degree : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ Z : ℝ in atTop,
    ∀ (s : Input ι) (R seed : Ideal O),
    Fintype.card ι ≤ Ncap → (∀ i, s.M i ≤ F) → s.upper ≤ U → s.b₁ ≤ b₁ → s.b₂ ≤ b₂ →
    s.W₁ 0 = 0 → s.W₂ 0 = 0 →
    (∀ x, ‖s.W₁ x‖ ≤ B₁) → (∀ x, ‖s.W₂ x‖ ≤ B₂) →
    0 < sourceRadius s → sourceRadius s ≤ Z^B →
    ∀ (M A δ a window Ch : ℝ), Amin ≤ A → A ≤ Amax → 0 < a → 0 ≤ Ch →
    volume s.toData = Z^A →
    ∀ radius : (p : Labels s R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ,
    (∀ p E, radius p E ≤ Cr*Z^L) →
    let Outer := FirstSourceOuterIndex s R seed (Z^M) radius
    let q := firstSourceOuterLabel s R seed (Z^M) radius
    ∀ (labels : Finset Outer) (ref : Outer) (rows : Outer → Finset O) (t : Outer → ℝ)
      (W : Outer → 𝓢(ℝ,ℂ)) (H : Outer → ℝ),
    (∀ i, ∀ z ∈ rows i, z ≠ 0) →
    (∀ i, 0 < H i) → (∀ i, H i ≤ Z^J) →
    (∀ i, QuadraticInitialBound.diagonalControl (W i) ≤ D) →
    (∀ i ∈ labels, a*Z^A ≤ ((q i).C.absNorm : ℝ)*Real.exp window*dyadicScale (i.2.2 2)) →
    (∀ i ∈ labels, a*Z^A ≤ ((q i).D.absNorm : ℝ)*Real.exp window*dyadicScale (i.2.2 3)) →
    (∀ i ∈ labels, ((q i).C.absNorm : ℝ) ≤ Z^δ*((q ref).C.absNorm : ℝ)) →
    (∀ i ∈ labels, ((q i).D.absNorm : ℝ) ≤ Z^δ*((q ref).D.absNorm : ℝ)) →
    (∀ i ∈ labels, (q ref).activeWidth Z/2+(q ref).punctureWidth Z ≤
      (q i).activeWidth Z/2+(q i).punctureWidth Z) →
    (∀ i ∈ labels, ‖V 0 ((q i).sourceRowLog (Z^M) (dyadicScale (i.2.2 0)))‖ ≤ 1) →
    (∀ i ∈ labels, ∀ z ∈ rows i, ‖V 1 (Real.log (‖eisEmbedding z‖^2/dyadicScale (i.2.2 1)))‖ ≤ 1) →
    (∀ i ∈ labels, ∀ z : O, 0 ≤ (W i (‖eisEmbedding z‖^2/H i)).re) →
    (∀ i ∈ labels, ∀ z ∈ rows i, 1 ≤ (W i (‖eisEmbedding z‖^2/H i)).re) →
    (∀ θ w : ℝ, ‖θ‖ ≤ Z^ν → ‖w‖ ≤ Z^ν →
      (∑ k ∈ firstSourceLabels labels q,
        ((q k.1).sourceChild k.2).leftEnergy (t k.1+2*Real.pi*(w-θ)) (W k.1) (H k.1)) ≤
        (Z^A/((q ref).C.absNorm : ℝ))*(Ch*Z^((q ref).leftTargetWidth Z A))) →
    (∀ θ w : ℝ, ‖θ‖ ≤ Z^ν → ‖w‖ ≤ Z^ν →
      (∑ k ∈ firstSourceLabels labels q,
        ((q k.1).sourceChild k.2).rightEnergy (t k.1+2*Real.pi*(w-(-θ))) (W k.1) (H k.1)) ≤
        (Z^A/((q ref).D.absNorm : ℝ))*(Ch*Z^((q ref).rightTargetWidth Z A))) →
    ‖∑ i ∈ labels,
      (((1+dyadicScale (i.2.2 0)*dyadicScale (i.2.2 1)/
        (dyadicScale (i.2.2 2)*dyadicScale (i.2.2 3)))^decay : ℝ) : ℂ)*
      (q i).sourceBlock (t i) (rows i) Wkernel V (Z^M) (dyadicScale (i.2.2 0))
        (dyadicScale (i.2.2 1)) (dyadicScale (i.2.2 2)) (dyadicScale (i.2.2 3))‖/Z^A ≤
      C*(Ch+firstSourceCoarseConstant Ncap F U b₁ b₂ B₁ B₂ D)*(Real.exp window/a)*Z^(M+δ) := by
  obtain ⟨degree,C,hC,hsector⟩ := joint_first_variable_centered_sector_from_local_joint_targets
    (ι := ι) Wkernel V Mwin hMwin hV hV₂c hV₂s hV₃c hV₃s decay ν
    (J+6*B+Amax+2) (Amin-B) hν
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [eventually_actual_first_source_coarse_powers Ncap F U b₁ b₂ B₁ B₂ D B L Cr Amax J
    hB₁ hB₂ hD hB hL hCr hJ,eventually_ge_atTop (2:ℝ)] with Z hcoarse hZ₂
  have hZ : 1 < Z := lt_of_lt_of_le (by norm_num) hZ₂
  have hz : 0 < Z := zero_lt_one.trans hZ
  intro s R seed hN hF hU hb₁ hb₂ hz₁ hz₂ hbound₁ hbound₂ hsourcepos hsource
    M A δ a window Ch hAmin hAmax ha hCh hvolume radius hr
  dsimp only
  intro labels ref rows t W H hrows hH hHcap hW hl hr' hNC hND hscalarWidth hV₀ hV₁ hpos hmajor hleft hright
  let q := firstSourceOuterLabel s R seed (Z^M) radius
  let Ct := firstSourceCoarseConstant Ncap F U b₁ b₂ B₁ B₂ D
  have hCt : 0 ≤ Ct := by dsimp only [Ct,firstSourceCoarseConstant]; positivity
  have hvolcap : volume s.toData ≤ Z^Amax := by
    rw [hvolume]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le hAmax
  have hc := hcoarse ι s R seed hN hF hU hb₁ hb₂ hz₁ hz₂ hbound₁ hbound₂ hsourcepos hsource
    hvolcap (Z^M) (by positivity) radius hr W H hH hHcap hW ref.1
  rw [hvolume] at hc
  have hsub := firstSourceLabels_subset labels Finset.univ q (Finset.subset_univ _)
  have hcl : (∑ k ∈ firstSourceLabels labels q,
      ((q k.1).sourceChild k.2).leftCoarse (W k.1) (H k.1)) ≤
      (Z^A/((q ref).C.absNorm : ℝ))*(Ct*Z^(J+6*B+Amax+2)) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun k _ _ => CenteredMomentFirstDivisorCommonBound.coarse_nonneg _ _ _ _ _ _)).trans hc.1
  have hcr : (∑ k ∈ firstSourceLabels labels q,
      ((q k.1).sourceChild k.2).rightCoarse (W k.1) (H k.1)) ≤
      (Z^A/((q ref).D.absNorm : ℝ))*(Ct*Z^(J+6*B+Amax+2)) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun k _ _ => CenteredMomentFirstDivisorCommonBound.coarse_nonneg _ _ _ _ _ _)).trans hc.2
  have hn := commonLabel_norm_bounds (finiteColumns (Fintype.piFinset s.pools))
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed) (Z^B)
    (fun I _ hI => (original_column_norm s R seed I hz₁ hz₂ hI).2.trans hsource)
    ref.1.val.1 ref.1.val.2 ref.1.property
  have htarget := (q ref).target_widths_lower Z A Amin B hZ hAmin hn.1 hn.2
  exact hsector labels rows q (q ref) Z M A δ a window Ch Ct hZ ha hCh hCt htarget.1 htarget.2
    t (fun i => dyadicScale (i.2.2 0)) (fun i => dyadicScale (i.2.2 1))
    (fun i => dyadicScale (i.2.2 2)) (fun i => dyadicScale (i.2.2 3)) hrows
    (fun _ => dyadicScale_pos _) (fun _ => dyadicScale_pos _)
    (fun _ => dyadicScale_pos _) (fun _ => dyadicScale_pos _)
    hl hr' hNC hND hscalarWidth hV₀ hV₁ (fun k => W k.1) (fun k => H k.1)
    (fun k _ => hH k.1)
    (fun k hk => hpos k.1 (Finset.mem_sigma.mp hk).1)
    (fun k hk => hmajor k.1 (Finset.mem_sigma.mp hk).1) hleft hright hcl hcr

#print axioms eventually_actual_first_variable_sector_from_local_targets
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstVariableActualSector -/

/- BEGIN ORIGINAL MODULE Analytic.JointHighSourcePhysical ; sha256 d552b33a972b11c3ce7542eb51d26151b89ab8a30cd5034273fe546025106154 -/
section




/-! The actual high physical estimate on the literal nested source indices.
Canonical rows, units and source transports are constructed by the embedding. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open Set Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification HeckeDetectorZeros CanonicalQuadraticSieve
open IdealMobiusDivisorSum LocalMoment ProbeHighRowFamily ConcretePrimeRowBridge
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentSectorLocalization HeckeDetectorDyadicGeometry
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput RayFourExpansion
open NonzeroJointSourceRow
local notation "O" => HeckeFamily.O

section FixedData
variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
variable (η : Character) (η₀ : Slot → Character) (Q : Ideal O) [NeZero Q]
  (hQtop : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hQη : Q ≤ η.modulus)
  (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
  (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
  (hH : RayOrthogonality.globalUnits M ≤ H) (hQM : Q ≤ M)
  (hQη₀ : ∀ j, Q ≤ (η₀ j).modulus)
  (S₀ : Finset (Ideal O))
  (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
  (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
  (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
  (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
  (hβupper : HeckeZeroSupremum.beta ≤ 7/8)
include hQtop hQ72 hQη hβ hH hQM hQη₀ S₀ hφ hφc hφp hφ0 hφne ha₀ hab₀ hB₀ hφs hφB hβupper

theorem actual_joint_high_source_physical
    (V : Slot → ℝ → ℂ) (Aprofile Bprofile : Slot → ℝ) (hA : ∀ j, 0 < Aprofile j)
    (hVs : ∀ j, Function.support (V j) ⊆ Icc (Aprofile j) (Bprofile j))
    (hV : ∀ j, ContDiff ℝ ∞ (V j))
    (ηcommon : Character) (hanchor : ∀ j, η₀ j = ηcommon)
    (Wslot : ℝ → ℂ) (hVslot : ∀ j, V j = Wslot)
    (bslot : ℝ) (hBslot : ∀ j, Bprofile j = bslot)
    (Rwidth dmax ε e κ ηaux σmin σmax productLoss populationLoss loss B : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hκone : κ ≤ 1) (hη : 0 < ηaux)
    (hbudget : 12*e*(Rwidth+2)+8*κ+2*ηaux ≤ ε)
    (hprimebudget : 8*e*Rwidth+κ ≤ ε)
    (hproductLoss : (2+2*(Fintype.card Slot : ℝ))*ε ≤ productLoss)
    (hpopulationLoss : 0 < populationLoss) (hB : 0 ≤ B)
    (hloss : populationLoss+dmax*productLoss ≤ loss)
    (τdetector dmin heightLoss : ℝ) (I : ℕ)
    (hτdetector : 0 < τdetector) (hdmin : 0 < dmin) (hheightLoss : 0 < heightLoss)
    (W₁ W₂ : ℝ → ℂ) (a₁ b₁ a₂ b₂plain : ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hs₁ : Function.support W₁ ⊆ Icc a₁ b₁) (hW₁ : ContDiff ℝ ∞ W₁)
    (hs₂ : Function.support W₂ ⊆ Icc a₂ b₂plain) (hW₂ : ContDiff ℝ ∞ W₂)
    (lo hi : Slot → ℝ) (fiberLoss : ℝ) (hfiberLoss : 0 < fiberLoss)
    (aSource Mslot upper : ℝ) (haSource : 0 < aSource) (hMslot : 0 ≤ Mslot)
    (conductorReserve : ℝ) (hconductorReserve : 0 < conductorReserve)
    (Sbad : Finset (Ideal O)) (primeLoss : ℝ) (hprimeLoss : 0 < primeLoss)
    (hprimeReserve : primeLoss ≤ 144011/219600000)
    (Wkernel : 𝓢(ℝ,ℂ)) (decay : ℕ)
    (tailA targetLower plainBound₁ plainBound₂ : ℝ)
    (hplainBound₁ : 0 ≤ plainBound₁) (hplainBound₂ : 0 ≤ plainBound₂)
    (hplainNorm₁ : ∀ x, ‖W₁ x‖ ≤ plainBound₁) (hplainNorm₂ : ∀ x, ‖W₂ x‖ ≤ plainBound₂) :
    ∃ profileBound : ℕ → ℝ, (∀ k, 0 < profileBound k) ∧
    ∃ (τ ν : ℝ) (orders : Finset Slot → ℕ) (N Nkernel : ℕ) (C : ℝ),
      0 < ν ∧ ν < τ ∧ τ < τdetector ∧ 4*τ < dmin*ηaux ∧
      (∀ J, orders J ≤ N) ∧ 0 < C ∧
      ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (d P W : ℝ), dmin ≤ d → d ≤ dmax → 2 ≤ Z^d → 2 < Z^τ → P ≤ B → W ≤ B →
      ∀ (p : DensityWindow), p.upper < p.lower+2*e →
      ∀ i : ℕ, i ≤ I → p.height = (3*(i+1 : ℕ))*Z^τ →
      ∀ (input : Input Slot) (puncture seed : Ideal O)
        (hpuncture : puncture ≠ 0) (hseed : Squarefree seed)
        (hz₁ : input.W₁ 0 = 0) (hz₂ : input.W₂ 0 = 0)
        (side : Bool) (ξ₁ ξ₂ χ₁ χ₂ : RayCharacter)
        (fallback : NonzeroJointSourceRow (original input puncture seed) side)
        (qs : Finset (NonzeroJointSourceRow (original input puncture seed) side)),
      let S := qs.image NonzeroJointSourceRow.label
      let unit := sourceUnit fallback η ξ₁ ξ₂
      let w := sourceRow fallback η ξ₁ ξ₂
      let s := sourceKernel input puncture seed side hseed hz₁ hz₂ fallback η ξ₁ ξ₂ χ₁ χ₂
      let first := sourceFirst fallback η ξ₁ ξ₂
      let z := sourceFrequency fallback
  let Ds := fun v => (s v).physicalProjectors
  let rayWeight := fun v => (s v).physicalRayWeight
      let Ds := fun v => (s v).physicalProjectors
      let rayWeight := fun v => (s v).physicalRayWeight
      ∀ (R : JointReconstructionLabel →
        JointRelativeLabel η (Option (Slot × RayQuotient.Characters M H)) → Ideal O)
        (hR : ∀ v label, R v label ≠ 0),
      (∀ q ∈ qs, Squarefree q.val.L) →
      (∀ v ∈ S, jointRelativeSourceZeroBin η (relativeSlotTranslate M H hH η₀) Q hQ72
        (relativeSlotTranslate_fixedQ M H hH η₀ Q hQM hQη₀) (R v) (hR v)
        p.lower p.upper p.height (w v)) →
      (∀ v ∈ S, (Ideal.absNorm v.C₁ : ℝ) ≤ Z^B ∧ (Ideal.absNorm v.D₁ : ℝ) ≤ Z^B ∧
        (Ideal.absNorm v.C₂ : ℝ) ≤ Z^B ∧ (Ideal.absNorm v.D₂ : ℝ) ≤ Z^B) →
      (∀ v ∈ S, (Ideal.absNorm (Ideal.span {(w v).val}) : ℝ) ≤ Z^W) →
      (∀ v ∈ S, (Ideal.absNorm (jointMissingRadical v.C₁ (w v).val) : ℝ) ≤ Z^P) →
      ∀ (t K Radius tbase firstU firstTheta : JointReconstructionLabel → ℝ)
        (n : JointReconstructionLabel → Fin 4 → ℤ)
        (σ freq : JointReconstructionLabel → Slot → ℝ)
        (θ : JointReconstructionLabel → Slot → RayQuotient.Characters M H)
        (slotWidth : JointReconstructionLabel → Slot → ℝ),
      (∀ v ∈ S, (∀ j, (s v).input.M j ≤ Mslot) ∧ (s v).input.upper ≤ upper ∧
        (s v).input.b₁ ≤ b₁ ∧ (s v).input.b₂ ≤ b₂plain) →
      (∀ v ∈ S, (∀ j, (s v).input.lo j = lo j) ∧ (∀ j, (s v).input.hi j = hi j)) →
      (∀ v ∈ S, (((s v).firstCommon*(s v).second.val.1).absNorm : ℝ) ≤ Z^(2*B) ∧
        (((s v).firstCommon*(s v).second.val.2).absNorm : ℝ) ≤ Z^(2*B)) →
      (∀ v ∈ S, ∀ L ∈ Ds v, (UniqueFactorizationMonoid.moebius L : ℂ) ≠ 0 →
        (L.absNorm : ℝ) ≤ Z^(2*B)) →
      (∀ v ∈ S, 0 < dyadicScale (n v 2) ∧ 0 < dyadicScale (n v 3) ∧
        aSource*CenteredMomentExceptionalAmplitudePair.volume (s v).input.toData/
          (((s v).firstCommon*(s v).second.val.1).absNorm : ℝ) ≤ dyadicScale (n v 2) ∧
        aSource*CenteredMomentExceptionalAmplitudePair.volume (s v).input.toData/
          (((s v).firstCommon*(s v).second.val.2).absNorm : ℝ) ≤ dyadicScale (n v 3)) →
      ∀ Bmask : ℝ, W+Bmask+conductorReserve ≤ d →
      (∀ v ∈ S, (((first v).leftPuncture (s v)).radical.absNorm : ℝ) ≤ Z^Bmask ∧
        (((first v).rightPuncture (s v)).radical.absNorm : ℝ) ≤ Z^Bmask) →
      (∀ v ∈ S, (s v).input.W₁ = W₁ ∧ (s v).input.W₂ = W₂) →
      (∀ v ∈ S, CenteredMomentAllocatedRayDictionary.Matches M H hH (s v).input
        ηcommon (θ v) (slotWidth v) (σ v) (freq v) Wslot bslot Z) →
      (∀ v ∈ S, (s v).input.X₁ ≤ (Z^d)^Rwidth ∧ (s v).input.X₂ ≤ (Z^d)^Rwidth ∧
        (s v).input.Y₁ ≤ (Z^d)^Rwidth ∧ (s v).input.Y₂ ≤ (Z^d)^Rwidth) →
      (∀ v ∈ S, ∀ j, 1 ≤ (s v).input.P j ∧ (s v).input.P j ≤ (Z^d)^Rwidth) →
      (∀ v ∈ S, t v = tbase v+2*Real.pi*(firstU v-firstTheta v)) →
      (∀ v ∈ S, |tbase v| ≤ Z^ν ∧ |firstU v| ≤ Z^ν ∧ |firstTheta v| ≤ Z^ν) →
      (∀ v ∈ S, ∀ j, σmin ≤ σ v j ∧ σ v j ≤ σmax) →
      (∀ v ∈ S, ∀ j, |freq v j| ≤ Z^ν) →
      ∀ (A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ : ℝ),
      2*b₂ = c₂+d₂ →
      ∀ supportLoss clipLoss commonLoss : ℝ, supportLoss+clipLoss+commonLoss ≤ lengthLoss →
      (∀ v ∈ S, CenteredMomentExceptionalAmplitudePair.volume (s v).input.toData ≤ Z^A) →
      (∀ v ∈ S, Z^(c+c₂-commonLoss) ≤ (((s v).firstCommon*(s v).second.val.1).absNorm : ℝ) ∧
        Z^(c+d₂-commonLoss) ≤ (((s v).firstCommon*(s v).second.val.2).absNorm : ℝ)) →
      (∀ v ∈ S, (max 1 (s v).input.upper)^Fintype.card Slot ≤ Z^supportLoss) →
      Real.logb Z (max 1 b₁*max 1 b₂plain) ≤ clipLoss →
      67/100 ≤ 2*p.lower-1 → 2*p.lower-1 ≤ 3/4 → A ≤ 883/1000 →
      0 ≤ π → π ≤ c → π ≤ d₁ → R₁ ≤ π →
      0 ≤ R₀ → 0 ≤ E → 0 ≤ Bc → L ≤ 5*(R₁-R₀) →
      0 ≤ b₂ → g₂ ≤ b₂ → 0 ≤ t₂cost → 0 ≤ geometryLoss → 0 ≤ lengthLoss →
      W ≤ 1-R₁-max (c-d₁) 0+L-6*(3/500)+geometryLoss → P ≤ π-R₁-E+R₀+missingLoss →
      omegaLoss+fiberLoss+loss+heightLoss+geometryLoss+lengthLoss+missingLoss ≤ 144011/109800000 →
      A-min c d₁+R₁+E-1+5*(3/500)+g₂-t₂cost-b₂+omegaLoss ≤ tailA →

      targetLower ≤ π+A-c+R₁+E+Bc-144011/109800000 →
      ∀ scalarLoss : ℝ,
      (∀ v ∈ S, 0 < K v ∧
        K v ≤ Z^(2*A-c-d₁+R₁+E-1+max (d₁-c) 0+6*(3/500)+(omegaLoss-scalarLoss))) →
      (∀ v ∈ S, (s v).secondLogCost Z ≤ g₂-t₂cost-b₂+scalarLoss) →
      (∑ q ∈ qs, let v := q.label; ∑ D ∈ Ds v,
        ‖(((1+SecondKernelLabel.kernelScale (n v))^decay : ℝ) : ℂ)*
          (s v).physicalRowTerm (Z^(A-c)) (actualHighPrimeCount M H Sbad Z)
            (t v) (z v) Wkernel (K v) (Radius v) (n v) D‖) ≤
        C*Z^(π+A-c+R₁+E+Bc-144011/219600000) := by
  obtain ⟨profileBound,hprofile,τ,ν,orders,N,Nkernel,C,hν,hντ,hτdet,hheight,horders,hC,hhigh⟩ :=
    actual_joint_high_physical_sector_contribution η η₀ Q hQtop hQ72 hQη hβ M H hH hQM hQη₀ S₀
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB hβupper
      V Aprofile Bprofile hA hVs hV ηcommon hanchor Wslot hVslot bslot hBslot
      Rwidth dmax ε e κ ηaux σmin σmax productLoss populationLoss loss B
      hRw hdmax hε he he' hκ hκone hη hbudget hprimebudget hproductLoss hpopulationLoss hB hloss
      τdetector dmin heightLoss I hτdetector hdmin hheightLoss
      W₁ W₂ a₁ b₁ a₂ b₂plain ha₁ ha₂ hs₁ hW₁ hs₂ hW₂ lo hi fiberLoss hfiberLoss
      aSource Mslot upper haSource hMslot conductorReserve hconductorReserve
      Sbad primeLoss hprimeLoss hprimeReserve Wkernel decay tailA targetLower plainBound₁ plainBound₂
      hplainBound₁ hplainBound₂ hplainNorm₁ hplainNorm₂
  refine ⟨profileBound,hprofile,τ,ν,orders,N,Nkernel,C,hν,hντ,hτdet,hheight,horders,hC,?_⟩
  filter_upwards [hhigh] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro d P W hd hdmax' hbase hT hPB hWB p hp i hi hheightBin
    input puncture seed hpuncture hseed hz₁ hz₂ side ξ₁ ξ₂ χ₁ χ₂ fallback qs
  dsimp only
  let S := qs.image NonzeroJointSourceRow.label
  let unit := sourceUnit fallback η ξ₁ ξ₂
  let w := sourceRow fallback η ξ₁ ξ₂
  let s := sourceKernel input puncture seed side hseed hz₁ hz₂ fallback η ξ₁ ξ₂ χ₁ χ₂
  let first := sourceFirst fallback η ξ₁ ξ₂
  let z := sourceFrequency fallback
  let Ds := fun v => (s v).physicalProjectors
  let rayWeight := fun v => (s v).physicalRayWeight
  intro R hR hprojSource hbin hnorm hNw hNr t K Radius tbase firstU firstTheta n
    σ freq θ slotWidth hprofileCaps hsourceIntervals hsourceNorm hprojectorNorm hphysical
    Bmask hconductorBalance hmaskNorm hplain hmatch
    hscale hprimeScale hteq hinputfreq hσrange hslotfreq
    A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ hb₂
    supportLoss clipLoss commonLoss hlengthLossSplit hvolume hcommonDyads hsupport hclip
    hδ hδtop hAtop hp₀ hpc hpd hRp hR₀ hE hBc hL hb₂₀ hg₂ ht₂
    hgeometryLoss hlengthLoss hW hP htotal htailA htarget scalarLoss hKactual hcost
  have hray : ∀ v ∈ S, ‖rayWeight v‖ ≤ 1 := fun v _ => (s v).physicalRayWeight_norm
  have hgates := sourceImage_gates qs hprojSource
  have hw : ∀ v ∈ S, (w v).val = v.row (unit v) :=
    sourceRow_canonical fallback η ξ₁ ξ₂ qs
  have hz : ∀ v, z v ≠ 0 := sourceFrequency_nonzero fallback
  have hparent : ∀ v, (s v).parent = (first v).sourceParent := fun _ => rfl
  have hpunc : ∀ v, (s v).puncture ≠ 0 := fun _ => hpuncture
  have hwsource : ∀ v, w v = (first v).row (s v) (z v) (hz v) := fun _ => rfl
  have hh := hZ.2 d P W hd hdmax' hbase hT hPB hWB p hp i hi hheightBin unit S w hw R hR
    (fun v hv => (hgates v hv).1) (fun v hv => (hgates v hv).2.1)
    (fun v hv => (hgates v hv).2.2) hbin hnorm hNw hNr
    s Ds z t K Radius tbase firstU firstTheta n rayWeight
    σ freq θ slotWidth hray hprofileCaps hsourceIntervals hsourceNorm hprojectorNorm hphysical
    first hz hparent hpunc hwsource Bmask hconductorBalance hmaskNorm hplain hmatch
    hscale hprimeScale hteq hinputfreq hσrange hslotfreq
    A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ hb₂
    supportLoss clipLoss commonLoss hlengthLossSplit hvolume hcommonDyads hsupport hclip
    hδ hδtop hAtop hp₀ hpc hpd hRp hR₀ hE hBc hL hb₂₀ hg₂ ht₂
    hgeometryLoss hlengthLoss hW hP htotal htailA htarget scalarLoss hKactual hcost
  change (∑ v ∈ qs.image NonzeroJointSourceRow.label, _) ≤ _ at hh
  rw [Finset.sum_image (fun _ _ _ _ h => NonzeroJointSourceRow.label_injective h)] at hh
  simpa only [CommonSecondKernelLabel.physicalRowTerm_eq_high,mul_assoc] using hh

end FixedData
#print axioms actual_joint_high_source_physical
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointHighSourcePhysical -/
