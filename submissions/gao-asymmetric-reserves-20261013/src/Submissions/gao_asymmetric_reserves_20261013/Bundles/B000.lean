/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.CubicSieve.KernelEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationGlobal
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.ExceptionalKernel
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedPaidAdmission
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstMixedRoot
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstNonexceptionalFixedWeightSum
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceFixedEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceOriginalData
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.HeckeWindowEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.ReflectedChild
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceInputFirstSectorTailAggregate
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceInputFirstTailUniform

/- BEGIN ORIGINAL MODULE Analytic.JointAllowanceMass ; sha256 d1e80ab02a410e47ae17957ef16126d3a52beb274499409a8726ccf6b2f402e9 -/
section



/-! The actual first-label mass with the paired canonical allowances.
The allowances are paid by the exact scalar/reference root identity,
before the inactive radical and dyadic block sums. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCanonicalFirst RayFourExpansion
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentFirstPhysicalDyadicCount CenteredMomentFirstNonexceptionalPrefactor
open CenteredMomentOriginalCommonHarmonic CenteredMomentCommonRadialData
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockAggregate
open CenteredMomentActiveSource CenteredMomentSupportedCorrelation CenteredMomentFirstSectors
open CenteredMomentSourceRow CenteredMomentSourceMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentSectorLocalization CenteredMomentRankinRadical
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstNonexceptionalFixedWeightSum
open CenteredMomentFirstMixedRoot CenteredMomentFirstMixedAllowance CenteredMomentCompleteCommon
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance jointAllowanceMassDecEq : DecidableEq (ι⊕Fin 2) := Classical.decEq _

lemma first_label_equal_support (s : Input ι) (R seed : Ideal O) (p : Labels s R seed) :
    CompletedGauss.primeSupport p.val.1 = CompletedGauss.primeSupport p.val.2 := by
  obtain ⟨q,hq,he⟩ := Finset.mem_image.mp p.property
  rw [←he]
  exact commonParts_equal_support q.1 q.2

def allowanceWeight (s : Input ι) (R seed : Ideal O) (m A : O) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ) (K r Z : ℝ)
    (p : Labels s R seed) (E : Finset (CommonIndex p.val.1 p.val.2))
    (τ₁ τ₂ : Character)
    (n : Blocks (effectiveScale p.val.1 p.val.2 E K) r
      (sourceRadius s/p.val.1.absNorm) (sourceRadius s/p.val.2.absNorm)) : ℝ :=
  weight s R seed m A t W V K r p E τ₁ τ₂ n*
    Z^((allowance p.val.1 p.val.2 Z+allowance p.val.2 p.val.1 Z)/2)

lemma allowanceWeight_nonneg (s : Input ι) (R seed : Ideal O) (m A : O) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ) (K r Z : ℝ) (hZ : 0 ≤ Z)
    (p : Labels s R seed) (E : Finset (CommonIndex p.val.1 p.val.2))
    (τ₁ τ₂ : Character)
    (n : Blocks (effectiveScale p.val.1 p.val.2 E K) r
      (sourceRadius s/p.val.1.absNorm) (sourceRadius s/p.val.2.absNorm)) :
    0 ≤ allowanceWeight s R seed m A t W V K r Z p E τ₁ τ₂ n := by
  have hvol := volume_pos s.toData
  have hfixed := fixedPresentationCost_pos
  apply mul_nonneg _ (Real.rpow_nonneg hZ _)
  unfold weight
  dsimp only
  split_ifs <;> positivity

theorem allowanceWeight_le (s : Input ι) (R seed : Ideal O) (m A : O) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ) (K r a₁ a₂ win Z : ℝ)
    (hK : 0 < K) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hZ : 1 < Z)
    (hs₁ : ∀ x, s.W₁ x ≠ 0 → a₁ ≤ x) (hs₂ : ∀ x, s.W₂ x ≠ 0 → a₂ ≤ x)
    (hwin : ∀ i y, V i y ≠ 0 → |y| ≤ win)
    (p : Labels s R seed) (E : Finset (CommonIndex p.val.1 p.val.2))
    (ξ₁ ξ₂ : RayCharacter) (F : Families s R seed ξ₁ ξ₂)
    (n : Blocks (effectiveScale p.val.1 p.val.2 E K) r
      (sourceRadius s/p.val.1.absNorm) (sourceRadius s/p.val.2.absNorm)) :
    allowanceWeight s R seed m A t W V K r Z p E (F p E).left (F p E).right n ≤
      ((Real.exp win/((∏ i,s.lo i)*a₁*a₂))*fixedPresentationCost*K*(s.η.modulus.absNorm : ℝ))*
        (CenteredMomentFirstInactiveRadicalMass.inactiveWeight p.val.1 p.val.2 E 0/
          (commonRadical p.val.1 p.val.2).absNorm) := by
  have hp := commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property
  have hvol := volume_pos s.toData
  have hfixed := fixedPresentationCost_pos
  have ha : 0 < (∏ i,s.lo i)*a₁*a₂ :=
    mul_pos (mul_pos (Finset.prod_pos (fun i _ => s.lo_pos i)) ha₁) ha₂
  unfold allowanceWeight weight
  dsimp only
  split_ifs with hn
  · simp only [zero_mul]
    exact mul_nonneg (by positivity)
      (div_nonneg (CenteredMomentFirstInactiveRadicalMass.inactiveWeight_nonneg _ _ _ _)
        (Nat.cast_nonneg _))
  · have hh := original_fixed_reference_pair s R seed a₁ a₂ ha₁ ha₂ hs₁ hs₂ m A t _
      p.val.1 p.val.2 hp.1 hp.2 (first_label_equal_support s R seed p) E ξ₁ ξ₂ (F p E)
      _ W V K (dyadicScale (n 0)) (dyadicScale (n 1))
      (dyadicScale (n 2)) (dyadicScale (n 3)) win Z 1 1 hK
      (dyadicScale_pos _) (dyadicScale_pos _) hZ (by norm_num) (by norm_num) hwin hn
    dsimp only at hh
    rw [paired_reference_root _ _ _ _ _ _ _ _ _ _
      (CenteredMomentFirstScale.norm_pos _ (F p E).left.modulus_ne_bot)
      (CenteredMomentFirstScale.norm_pos _ (F p E).right.modulus_ne_bot)
      hvol (CenteredMomentFirstScale.norm_pos _ hp.1.1)
      (CenteredMomentFirstScale.norm_pos _ hp.2.1) (zero_lt_one.trans hZ)
      (by norm_num) (by norm_num)] at hh
    norm_num only [mul_one,Real.sqrt_one] at hh
    convert hh using 1
    · field_simp
    · simp only [CenteredMomentFirstInactiveRadicalMass.inactiveWeight,Real.rpow_zero,
        div_one,CenteredMomentFirstPhysicalSource.inactiveWeight]
      ring

def sumAllowanceWeight (s : Input ι) (R seed : Ideal O) (m A : O) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ) (K Z : ℝ)
    (radius : (p : Labels s R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ)
    (τ₁ τ₂ : (p : Labels s R seed) → Finset (CommonIndex p.val.1 p.val.2) → Character) : ℝ :=
  ∑ p : Labels s R seed, ∑ E ∈ CenteredMomentFirstDiscardedEnergy.inactiveSubsets p.val.1 p.val.2,
    ∑ n : Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
      (sourceRadius s/p.val.1.absNorm) (sourceRadius s/p.val.2.absNorm),
      allowanceWeight s R seed m A t W V K (radius p E) Z p E (τ₁ p E) (τ₂ p E) n

/-- Both canonical allowances are retained in the real first-label mass.
Only the source's inactive radical mass and dyadic block count are used. -/
theorem original_fixed_allowance_weight_sum (B L Cr ε : ℝ)
    (hB : 0 ≤ B) (hL : 0 ≤ L) (hCr : 0 < Cr) (hε : 0 < ε) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ᶠ Z : ℝ in atTop,
    ∀ (ι : Type*) [Fintype ι] [DecidableEq ι] (s : Input ι) (R seed : Ideal O),
      Squarefree seed → seed ≠ 0 → s.W₁ 0=0 → s.W₂ 0=0 →
      0 < sourceRadius s → sourceRadius s ≤ Z^B →
    ∀ (m A : O) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ) (K a₁ a₂ win : ℝ),
      0 < K → 0 < a₁ → 0 < a₂ →
      (∀ x, s.W₁ x ≠ 0 → a₁ ≤ x) → (∀ x, s.W₂ x ≠ 0 → a₂ ≤ x) →
      (∀ i y, V i y ≠ 0 → |y| ≤ win) →
    ∀ radius : (p : Labels s R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ,
      (∀ p E, radius p E ≤ Cr*Z^L) → ∀ ξ₁ ξ₂ : RayCharacter, ∀ F : Families s R seed ξ₁ ξ₂,
      sumAllowanceWeight s R seed m A t W V K Z radius
        (fun p E => (F p E).left) (fun p E => (F p E).right) ≤
        ((Real.exp win/((∏ i,s.lo i)*a₁*a₂))*fixedPresentationCost*K*(s.η.modulus.absNorm : ℝ))*
          (C₀*Z^ε/(seed.absNorm : ℝ)) := by
  obtain ⟨Cd,hCd,hd⟩ := original_blocks_subpower B L Cr (ε/2) hB hL hCr (by linarith)
  obtain ⟨Cm,hCm,hm⟩ := CenteredMomentFirstInactiveRadicalMass.actual_inactive_radical_mass
    B (ε/2) hB (by linarith)
  refine ⟨Cd*Cm,mul_pos hCd hCm,?_⟩
  filter_upwards [hd,eventually_ge_atTop (2 : ℝ)] with Z hd hZ
  intro ι _ _ s R seed hs hs0 hz₁ hz₂ hH hHcap m A t W V K a₁ a₂ win
    hK ha₁ ha₂ hs₁ hs₂ hwin radius hr ξ₁ ξ₂ F
  let P : ℝ := (Real.exp win/((∏ i,s.lo i)*a₁*a₂))*fixedPresentationCost*K*(s.η.modulus.absNorm : ℝ)
  have ha : 0 < (∏ i,s.lo i)*a₁*a₂ :=
    mul_pos (mul_pos (Finset.prod_pos (fun i _ => s.lo_pos i)) ha₁) ha₂
  have hP : 0 ≤ P := by dsimp [P]; have hf := fixedPresentationCost_pos; positivity
  let f := fun (p : Labels s R seed) (E : Finset (CommonIndex p.val.1 p.val.2)) =>
    CenteredMomentFirstInactiveRadicalMass.inactiveWeight p.val.1 p.val.2 E 0/
      (commonRadical p.val.1 p.val.2).absNorm
  have hf : ∀ p E, 0 ≤ f p E := by
    intro p E
    exact div_nonneg (CenteredMomentFirstInactiveRadicalMass.inactiveWeight_nonneg _ _ _ _) (Nat.cast_nonneg _)
  have hb (p : Labels s R seed) (E : Finset (CommonIndex p.val.1 p.val.2)) :
      (∑ n : Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
          (sourceRadius s/p.val.1.absNorm) (sourceRadius s/p.val.2.absNorm),
        allowanceWeight s R seed m A t W V K (radius p E) Z p E (F p E).left (F p E).right n) ≤
        (Cd*Z^(ε/2)*P)*f p E := by
    have hp := commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property
    have hcard := hd p.val.1 p.val.2 hp.1.1 hp.2.1 E K (radius p E) (sourceRadius s)
      hK hH (hr p E) hHcap
    calc
      _ ≤ ∑ _n : Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
          (sourceRadius s/p.val.1.absNorm) (sourceRadius s/p.val.2.absNorm), P*f p E := by
        exact Finset.sum_le_sum (fun n _ => allowanceWeight_le s R seed m A t W V K (radius p E)
          a₁ a₂ win Z hK ha₁ ha₂ (by linarith) hs₁ hs₂ hwin p E ξ₁ ξ₂ F n)
      _ ≤ _ := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
        convert mul_le_mul_of_nonneg_right hcard (mul_nonneg hP (hf p E)) using 1 <;> ring
  have hmass := hm Z hZ seed hs hs0
    (finiteColumns (Fintype.piFinset s.pools))
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
    (fun I _ hI => original_column_mask s R seed I hI)
    (fun I _ hI => (original_column_norm s R seed I hz₁ hz₂ hI).2.trans hHcap) 0 le_rfl
  calc
    _ ≤ ∑ p : Labels s R seed, ∑ E ∈ CenteredMomentFirstDiscardedEnergy.inactiveSubsets p.val.1 p.val.2,
        (Cd*Z^(ε/2)*P)*f p E := by
      exact Finset.sum_le_sum (fun p _ => Finset.sum_le_sum (fun E _ => hb p E))
    _ = (Cd*Z^(ε/2)*P)*
        (∑ p : Labels s R seed, ∑ E ∈ CenteredMomentFirstDiscardedEnergy.inactiveSubsets p.val.1 p.val.2, f p E) := by
      simp only [Finset.mul_sum]
    _ ≤ (Cd*Z^(ε/2)*P)*(Cm*Z^(ε/2)/(seed.absNorm : ℝ)) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = P*((Cd*Cm)*Z^ε/(seed.absNorm : ℝ)) := by
      have hz : 0 < Z := by linarith
      have he : Z^(ε/2)*Z^(ε/2)=Z^ε := by rw [←Real.rpow_add hz]; congr 1; ring
      calc
        _ = P*(Cd*Cm)*(Z^(ε/2)*Z^(ε/2))/(seed.absNorm : ℝ) := by ring
        _ = _ := by rw [he]; ring

#print axioms allowanceWeight_le
#print axioms original_fixed_allowance_weight_sum
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointAllowanceMass -/

/- BEGIN ORIGINAL MODULE Analytic.JointCommonErrorAllocation ; sha256 b5c908c3563fbc4640d7b8257a23df415f1aa68d39a6ce30eb2b3f9abebf3473 -/
section



/-! Allocate the extracted error polynomial, after amplification. The
main common Gaussian polynomial remains coherent across first allocations. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentFirstPhysicalSource CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentAmplificationLiveMask CenteredMomentLiveDomain CenteredMomentRemainingBox
open CenteredMomentGaussEnergy CenteredMomentHeckeColumnWindow
open CenteredMomentSecondHeightFamily CenteredMomentCommonPuncture CenteredMomentOriginalChildEnergy
open CenteredMomentAmplificationGlobal
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance commonErrorAllocationDecEq : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

/-- Any ideal-column kernel commutes with the exact common allocation.
The residual domain is changed only on zero coefficients. -/
theorem common_column_functional_allocation (D : OriginalData ι)
    (hS : ∀ i, ∀ I ∈ D.S i,I ≠ 0) (hp : ∀ i, ∀ I ∈ D.S (Sum.inl i),Prime I)
    (C : Ideal O) (hC : Supported C) (hseed : D.s ∣ C)
    (L : Ideal O) (f : Ideal O → ℂ) :
    (∑ I ∈ supportedColumns (residualPool C hC.1 D.columns),
      (if IsCoprime C I ∧ L ∣ I then D.beta (C*I) else 0)*f I) =
      ∑ B : actualAllocations D.S C,
        frozenCoefficient B.val C D.R D.nu D.slot D.lengths *
          ∑ I ∈ supportedColumns (allocatedData D C L B).columns,
            (allocatedData D C L B).beta I*f I := by
  let Q := residualPool C hC.1 D.columns
  let b := fun B : actualAllocations D.S C => frozenCoefficient B.val C D.R D.nu D.slot D.lengths
  let c := fun B : actualAllocations D.S C => finiteColumnCoefficient
    (liveBox D.S B.val (allocation_data D.S C B (Finset.mem_filter.mp B.property).1).1)
    (liveProfile B.val C D.R D.nu D.slot D.lengths
      D.W₁ D.W₂ D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂)
  have he (I : Ideal O) (hI : I ∈ supportedColumns Q) :
      (if IsCoprime C I ∧ L ∣ I then D.beta (C*I) else 0)*f I =
        ∑ B,b B*(c B I*((if L ∣ I then 1 else 0)*f I)) := by
    have hc := original_source_punctured_column D.S hS hp C D.R D.s I hC.1
      (Finset.mem_filter.mp hI).2.1 hseed D.nu D.slot D.lengths D.W₁ D.W₂
      D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂
    change (if IsCoprime C I then D.beta (C*I) else 0) = ∑ B,b B*c B I at hc
    by_cases hL : L ∣ I
    · simp only [hL,and_true,ite_true,one_mul]
      rw [hc,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro B _
      ring
    · simp only [hL,and_false,ite_false,zero_mul,mul_zero,Finset.sum_const_zero]
  change (∑ I ∈ supportedColumns Q,_) = _
  rw [Finset.sum_congr rfl he,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro B _
  rw [←Finset.mul_sum]
  apply congrArg (fun x : ℂ => b B*x)
  have hlive := live_column_sum D.S hS hp B.val
    (allocation_data D.S C B (Finset.mem_filter.mp B.property).1).1 C D.R hC
    (Finset.mem_filter.mp B.property).1 (Finset.mem_filter.mp B.property).2
    D.nu D.slot D.lengths D.W₁ D.W₂ D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂
    (fun I => (if L ∣ I then 1 else 0)*f I)
  change (∑ I ∈ supportedColumns Q,c B I*((if L ∣ I then 1 else 0)*f I)) = _ at hlive
  rw [hlive]
  change (∑ I ∈ supportedColumns (allocatedData D C L B).columns,_) = _
  apply Finset.sum_congr rfl
  intro I _
  change _ = finiteColumnCoefficient _ (allocatedData D C L B).profile I*f I
  rw [allocated_profile,maskedLiveProfile,column_mask]
  dsimp only [liveProfile]
  rw [allocated_pools]
  ring

def amplificationIdealKernel (p : O) (k : ℕ) (h : O) (I : Ideal O) : ℂ :=
  if multiplicity p (primaryGenerator I) = k then
    primaryGaussRow I h-primaryGaussRow I (p^6*h) else 0

theorem source_amplificationError (S : Finset (Ideal O)) (c : Ideal O → ℂ)
    (p : O) (k : ℕ) (h : O) :
    amplificationError Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
      (fun I : supportedColumns S => c I)
      (fun I => multiplicity p (sourceGenerator S I)) p k h =
    ∑ I ∈ supportedColumns S,c I*amplificationIdealKernel p k h I := by
  unfold amplificationError
  rw [←Finset.sum_coe_sort (supportedColumns S) (fun I => c I*amplificationIdealKernel p k h I)]
  apply Finset.sum_congr rfl
  intro I _
  unfold amplificationIdealKernel
  rw [primaryGaussRow,primaryGaussRow,dite_eq_left (Finset.mem_filter.mp I.property).2,
    dite_eq_left (Finset.mem_filter.mp I.property).2]
  by_cases hv : multiplicity p (primaryGenerator I.val) = k
  · simp only [sourceGenerator,hv,ite_true]
  · simp only [sourceGenerator,hv,ite_false,mul_zero]

/-- This is the actual extracted error, with the source generator's
multiplicity and both Gaussian frequencies retained exactly. -/
theorem common_amplificationError_allocation (D : OriginalData ι)
    (hS : ∀ i, ∀ I ∈ D.S i,I ≠ 0) (hp : ∀ i, ∀ I ∈ D.S (Sum.inl i),Prime I)
    (C : Ideal O) (hC : Supported C) (hseed : D.s ∣ C)
    (τ : Character) (t : ℝ) (L : Ideal O) (p h : O) (k : ℕ) :
    let Q := residualPool C hC.1 D.columns
    amplificationError Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
      (fun I : supportedColumns Q =>
        (if IsCoprime C (I : Ideal O) ∧ L ∣ (I : Ideal O) then D.beta (C*I) else 0)*heightCoeff τ t I)
      (fun I => multiplicity p (sourceGenerator Q I)) p k h =
      ∑ B : actualAllocations D.S C,
        frozenCoefficient B.val C D.R D.nu D.slot D.lengths *
          amplificationError Finset.univ (sourceGenerator (allocatedData D C L B).columns)
            (sourceGenerator_supported (allocatedData D C L B).columns)
            (fun I : supportedColumns (allocatedData D C L B).columns =>
              (allocatedData D C L B).beta I*heightCoeff τ t I)
            (fun I => multiplicity p (sourceGenerator (allocatedData D C L B).columns I)) p k h := by
  let Q := residualPool C hC.1 D.columns
  let c : Ideal O → ℂ := fun I =>
    (if IsCoprime C I ∧ L ∣ I then D.beta (C*I) else 0)*heightCoeff τ t I
  have hfirst := source_amplificationError Q c p k h
  apply hfirst.trans
  have hmiddle := common_column_functional_allocation D hS hp C hC hseed L
    (fun I => heightCoeff τ t I*amplificationIdealKernel p k h I)
  have hmiddle' : (∑ I ∈ supportedColumns Q,c I*amplificationIdealKernel p k h I) =
      ∑ B : actualAllocations D.S C,
        frozenCoefficient B.val C D.R D.nu D.slot D.lengths *
          ∑ I ∈ supportedColumns (allocatedData D C L B).columns,
            ((allocatedData D C L B).beta I*heightCoeff τ t I)*amplificationIdealKernel p k h I := by
    simpa only [c,Q,mul_assoc] using hmiddle
  apply hmiddle'.trans
  apply Finset.sum_congr rfl
  intro B _
  exact congrArg (fun x : ℂ => frozenCoefficient B.val C D.R D.nu D.slot D.lengths*x)
    (source_amplificationError (allocatedData D C L B).columns
      (fun I => (allocatedData D C L B).beta I*heightCoeff τ t I) p k h).symm

#print axioms common_column_functional_allocation
#print axioms common_amplificationError_allocation
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCommonErrorAllocation -/

/- BEGIN ORIGINAL MODULE Analytic.JointErrorGeometry ; sha256 96316cbd7c93b7c139971a3014fbdd65f88c24c70cc288c4597c06cc8efd47eb -/
section


/-! The exact error affine defect before the incumbent source wrapper
replaces sigma + removal - moving by six times removal. Retaining that
term is what gives the local cost-22/5 reserve. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSourceLiveColumn
open CenteredMomentFirstAmplifiedCapacityRadius CenteredMomentSecondCapacitySourceShift
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonRawScale
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondRadicalBudget
open CenteredMomentAmplifiedRetainedRadius
local notation "O"=> HeckeFamily.O
variable {ι:Type*}[Fintype ι]
local instance jointErrorGeometryInstance1 {κ:Type*}:DecidableEq κ:=Classical.decEq _

open CenteredMomentFirstAmplifiedCapacityCommon CenteredMomentFirstAmplifiedCapacitySource
open CenteredMomentFirstAmplifiedActiveAffine CenteredMomentFirstAmplifiedActiveCapacitySource
open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedChildCapacity

open CenteredMomentFirstAmplifiedPaidAdmission
open CenteredMomentFirstMixedNormalizationActual CenteredMomentCommonRadiusSaving

theorem refined_error_reference_shift (η τ:Character)(C D:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(K V Z red sigma delta reserve cost:ℝ)
    (hK:0< K)(hV:0< V)(hZ:1< Z)(hred:0< red)(hcost:0< cost)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D})
    (p:O)(k:ℕ)(hk:k=1 ∨ k=6 ∨ k=7)(hs:0≤ sigma)
    (hl:sigma/6≤ Real.logb Z (normValue p)):
    let c:=Real.logb Z (C.absNorm:ℝ);
    let d:=Real.logb Z (D.absNorm:ℝ);
    let K0:=Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K V);
    Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p k)-
      Real.logb Z (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k))-
      Real.logb Z (V/(red*Z^(errorRemoval p Z k)))≤
      Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
        (Real.logb Z red-c)-min c d+(sigma+errorRemoval p Z k-errorMoving p Z k)+delta+reserve-
        Real.logb Z fixedPresentationCost-Real.logb Z cost := by
  have hp:0≤ Real.logb Z (normValue p):=by linarith
  have hw:0≤ errorRemoval p Z k:=by unfold errorRemoval;positivity
  have hwo:errorMoving p Z k≤2*errorRemoval p Z k:=by
    rcases hk with rfl|rfl|rfl <;> simp only [errorMoving,errorRemoval] <;> norm_num <;> linarith
  have hh:=actual_reference_shift η τ C D hC hD hCD E K V Z red
    (errorRemoval p Z k) (errorMoving p Z k) cost
    (max (Real.logb Z (D.absNorm:ℝ)-Real.logb Z (C.absNorm:ℝ)-
      2*errorRemoval p Z k+errorMoving p Z k) 0+sigma+delta+reserve)
    hK hV hZ hred hcost hmod
  have hg:=enlarged_gain_extraction (Real.logb Z (C.absNorm:ℝ))
    (Real.logb Z (D.absNorm:ℝ)) (errorRemoval p Z k) (errorMoving p Z k)
    sigma 1 delta reserve hw hwo
  dsimp only at hh ⊢
  simp only [one_mul] at hg
  rw [errorCommonRadius]
  simp only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hh ⊢
  linarith

theorem refined_active_error_admission (s:Input ι)(τ υ:Character)(C D R0:Ideal O)
    (hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(B:actualAllocations s.pools C)(t:ℝ)
    (hB:frozenCoefficient B.val C R0 s.ν s.W s.P≠0)
    (K Z sigma delta reserve cost a:ℝ)(hK:0< K)(hZ:1< Z)(hcost:0< cost)(ha:0< a)
    (p:O)(hp:p≠0)(k:ℕ)(hk:k=1 ∨ k=6 ∨ k=7)(hs:0≤ sigma)
    (hl:sigma/6≤ Real.logb Z (normValue p))
    (hslot:∀i,∀I∈(activeInput (child s C R0 B τ t)).slots i,IsCoprime (Ideal.span {p}) I)
    (Bp:actualAllocations (activeInput (child s C R0 B τ t)).pools ((Ideal.span {p})^k))(v:ℝ)
    (hmod:τ.modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D})
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C₂ D₂:Ideal O)
    (hC₂:Supported C₂)(hD₂:Supported D₂)(hCD₂:primeSupport C₂=primeSupport D₂)
    (U:Finset (CommonIndex C₂ D₂))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(n:Fin 4→ℤ)
    (hlower:∀I:Ideal O,β I≠0→a*volume (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v)≤(I.absNorm:ℝ))
    (hne:physicalBlock υ v S β C₂ D₂ hC₂ hD₂ U R rows W
      (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (Real.logb Z (firstNominalScale C D
          (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume s)))
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k) n≠0)
    (Cpick Rpick:Ideal O)(hside:Cpick=C₂ ∨ Cpick=D₂)
    (B₂:actualAllocations (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v).pools Cpick)
    (hB₂:frozenCoefficient B₂.val Cpick Rpick (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v).ν (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v).W (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v).P≠0)
    (κ Mdecl:ℝ)(hκ:1/6≤κ)(hP:∀i,1≤ s.P i)
    (hcap:CenteredMomentEnergyBands.length Z s.X₁+
      CenteredMomentEnergyBands.length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤ Mdecl)
    (hM:Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ)≤ Mdecl):
    let input:=errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v;
    let delta1:=Mdecl-(Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ))+
      sourceReserve s input C D Z delta reserve cost a;
    0≤ delta1 ∧
    Real.logb Z (volume s)+(6*κ-1)*(∑i:liveIndices B₂.val,Real.logb Z (input.P i.val))≤ Mdecl ∧
    Real.logb Z (preVolume (commonData (withHeight input υ v) Cpick Rpick B₂))-
      Real.logb Z (envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k)) C₂ D₂ U n)≤
      Real.logb Z (volume s)-Mdecl+(sigma+errorRemoval p Z k-errorMoving p Z k)+delta1+Real.logb Z (ratioPenalty n) := by
  dsimp only
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hqref:0< cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k):=by positivity
  have hf:=active_error_parent_affine s C R0 B τ t (Ideal.span {p}) k Bp υ v Z κ Mdecl hZ hκ hP hcap
  have hPchild:∀i,1≤(errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v).P i:=fun i=> hP i.val.val
  have hparent:=common_affine (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v) Cpick B₂ Z κ (Real.logb Z (volume s)) Mdecl hZ hκ hPchild hf
  have hr:=refined_error_reference_shift s.η τ C D hC hD hCD E K (volume s) Z
    (rawReduction B.val s.P) sigma delta reserve cost hK (volume_pos s) hZ
    (rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos) hcost hmod p k hk hs hl
  have he:=frozen_reduction_log s C R0 B Z hZ hB
  have hrad:0< errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume s)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k:=by
    unfold errorCommonRadius;positivity
  have hg:
    Real.logb Z (preVolume (commonData (withHeight (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v) υ v) Cpick Rpick B₂))-
      Real.logb Z (envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k)) C₂ D₂ U n)≤
      Real.logb Z (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (Real.logb Z (firstNominalScale C D
          (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume s)))
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k)-Real.logb Z (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k))-
      Real.logb Z (volume (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v))+Real.logb Z (4/((fixedFactor:ℝ)*a^2))+
      (Fintype.card (liveIndices Bp.val):ℝ)*Real.logb Z (max 1 (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v).upper)+
      Real.logb Z (ratioPenalty n) := by
    rcases hside with hside|hside
    · subst Cpick
      exact common_raw_reference_shift (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v) υ v S β C₂ D₂ Rpick hC₂ hD₂ hCD₂
        B₂ hB₂ U R rows W _ a Z (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k)) n hqref hrad ha hZ hlower hne
    · subst Cpick
      exact common_raw_reference_shift_right (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v) υ v S β C₂ D₂ Rpick hC₂ hD₂ hCD₂
        B₂ hB₂ U R rows W _ a Z (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k)) n hqref hrad ha hZ hlower hne
  have hQ:(Ideal.span {p})≠(0:Ideal O):=Ideal.span_singleton_eq_bot.not.mpr hp
  have hv:=active_error_volume s C R0 B τ t (Ideal.span {p}) hQ k hslot Bp υ v
  have hn:(Ideal.absNorm (Ideal.span {p}):ℝ)=normValue p:=by simp only [normValue]
  rw [hn] at hv
  rw [hv] at hg
  dsimp only at hr
  rw [errorRemoval_power p hp Z hZ k] at hr
  have hres:=le_max_left
    (delta+reserve-(Fintype.card ι:ℝ)*Real.logb Z (min 1 s.lower)-
      min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))-
      Real.logb Z fixedPresentationCost-Real.logb Z cost+
      Real.logb Z (4/((fixedFactor:ℝ)*a^2))+
      (Fintype.card (liveIndices Bp.val):ℝ)*Real.logb Z (max 1 (errorInput s C R0 B τ t (Ideal.span {p}) k Bp υ v).upper)) 0
  refine ⟨add_nonneg (sub_nonneg.mpr hM) (sourceReserve_nonneg _ _ _ _ _ _ _ _ _),hparent,?_⟩
  unfold sourceReserve
  linarith

#print axioms refined_error_reference_shift
#print axioms refined_active_error_admission
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointErrorGeometry -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstBlock ; sha256 caf4f00fdc5e9e8edcdd60199f1e69da40b09977bd900d08b03e0fe410dd710b -/
section



/-! The first Cauchy step retains all arithmetic labels, including the
first projector, in one direct sum at fixed Fourier variables. -/

set_option autoImplicit false

namespace OAI
noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT
open CenteredMomentFirstPhysicalSource CenteredMomentFirstAmplificationChoice
open CenteredMomentSourceRow CenteredMomentGaussEnergy CenteredMomentReflectedChild
open CenteredMomentCauchy RayFourExpansion ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentSecondHeightFamily
open CenteredMomentChildEnergy
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

structure FirstJointLabel (ι : Type*) [Fintype ι] where
  data : OriginalData ι
  parent : Character
  C : Ideal O
  D : Ideal O
  hC : Supported C
  hD : Supported D
  hCD : primeSupport C = primeSupport D
  E : Finset (CommonIndex C D)
  leftRay : RayCharacter
  rightRay : RayCharacter
  projector : Ideal O

namespace FirstJointLabel

def pair (s : FirstJointLabel ι) :=
  fixedPair s.parent s.C s.D s.hC s.E s.leftRay s.rightRay

def leftValue (s : FirstJointLabel ι) (t : ℝ) (z : O) : ℂ :=
  leftChild s.data s.parent (fixedBadMask * idealGenerator s.data.R)
    t s.C s.D s.hC s.E s.leftRay s.projector z

def rightValue (s : FirstJointLabel ι) (t : ℝ) (z : O) : ℂ :=
  rightChild s.data s.parent (fixedBadMask * idealGenerator s.data.R)
    t s.C s.D s.hC s.hD s.E s.rightRay s.projector (-z)

def leftEnergy (s : FirstJointLabel ι) (t : ℝ) (U : 𝓢(ℝ, ℂ)) (K : ℝ) : ℝ :=
  (commonEnergy s.data s.C s.hC s.pair.left t s.projector U K).re

def rightEnergy (s : FirstJointLabel ι) (t : ℝ) (U : 𝓢(ℝ, ℂ)) (K : ℝ) : ℝ :=
  (commonEnergy s.data s.D s.hD s.pair.right t s.projector U K).re

theorem finite_left_energy (s : FirstJointLabel ι) (t : ℝ) (U : 𝓢(ℝ, ℂ))
    (K : ℝ) (hK : 0 < K) (rows : Finset O)
    (hU : ∀ z : O, 0 ≤ (U (‖eisEmbedding z‖ ^ 2 / K)).re)
    (hmajor : ∀ z ∈ rows, 1 ≤ (U (‖eisEmbedding z‖ ^ 2 / K)).re) :
    (∑ z ∈ rows, ‖s.leftValue t z‖ ^ 2) ≤ s.leftEnergy t U K := by
  unfold leftEnergy
  rw [← s.pair.left_common_energy s.data t s.projector U K]
  unfold leftValue leftChild
  exact finite_energy_le_gaussEnergy _ _ _ _ U K hK rows hU hmajor

theorem finite_right_energy (s : FirstJointLabel ι) (t : ℝ) (U : 𝓢(ℝ, ℂ))
    (K : ℝ) (hK : 0 < K) (rows : Finset O)
    (hU : ∀ z : O, 0 ≤ (U (‖eisEmbedding z‖ ^ 2 / K)).re)
    (hmajor : ∀ z ∈ rows, 1 ≤ (U (‖eisEmbedding z‖ ^ 2 / K)).re) :
    (∑ z ∈ rows, ‖s.rightValue t z‖ ^ 2) ≤ s.rightEnergy t U K := by
  unfold rightEnergy
  rw [← s.pair.right_common_energy s.hD s.hCD s.data t s.projector U K]
  unfold rightValue rightChild
  exact finite_reflected_energy_le_gaussEnergy _ _ _ _ U K hK rows hU hmajor

end FirstJointLabel

theorem joint_first_child_abs_bound {Λ : Type*} [DecidableEq Λ]
    (labels : Finset Λ) (rows : Finset O) (s : Λ → FirstJointLabel ι)
    (t₁ t₂ : Λ → ℝ) (U : Λ → 𝓢(ℝ, ℂ)) (K : Λ → ℝ)
    (hK : ∀ l ∈ labels, 0 < K l)
    (hU : ∀ l ∈ labels, ∀ z : O, 0 ≤ (U l (‖eisEmbedding z‖ ^ 2 / K l)).re)
    (hmajor : ∀ l ∈ labels, ∀ z ∈ rows,
      1 ≤ (U l (‖eisEmbedding z‖ ^ 2 / K l)).re) :
    (∑ l ∈ labels, ∑ z ∈ rows,
      ‖(s l).leftValue (t₁ l) z‖ * ‖(s l).rightValue (t₂ l) z‖) ≤
      Real.sqrt (∑ l ∈ labels, (s l).leftEnergy (t₁ l) (U l) (K l)) *
      Real.sqrt (∑ l ∈ labels, (s l).rightEnergy (t₂ l) (U l) (K l)) := by
  have hc := Real.sum_mul_le_sqrt_mul_sqrt (labels ×ˢ rows)
    (fun q => ‖(s q.1).leftValue (t₁ q.1) q.2‖)
    (fun q => ‖(s q.1).rightValue (t₂ q.1) q.2‖)
  have hl : (∑ l ∈ labels, ∑ z ∈ rows, ‖(s l).leftValue (t₁ l) z‖ ^ 2) ≤
      ∑ l ∈ labels, (s l).leftEnergy (t₁ l) (U l) (K l) :=
    Finset.sum_le_sum (fun l hl => (s l).finite_left_energy (t₁ l)
      (U l) (K l) (hK l hl) rows (hU l hl) (hmajor l hl))
  have hr : (∑ l ∈ labels, ∑ z ∈ rows, ‖(s l).rightValue (t₂ l) z‖ ^ 2) ≤
      ∑ l ∈ labels, (s l).rightEnergy (t₂ l) (U l) (K l) :=
    Finset.sum_le_sum (fun l hl => (s l).finite_right_energy (t₂ l)
      (U l) (K l) (hK l hl) rows (hU l hl) (hmajor l hl))
  calc
    _ ≤ Real.sqrt (∑ l ∈ labels, ∑ z ∈ rows,
          ‖(s l).leftValue (t₁ l) z‖ ^ 2) *
        Real.sqrt (∑ l ∈ labels, ∑ z ∈ rows,
          ‖(s l).rightValue (t₂ l) z‖ ^ 2) := by
      simpa only [Finset.sum_product] using hc
    _ ≤ _ := mul_le_mul (Real.sqrt_le_sqrt hl) (Real.sqrt_le_sqrt hr)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem joint_first_child_bound {Λ : Type*} [DecidableEq Λ]
    (labels : Finset Λ) (rows : Finset O) (s : Λ → FirstJointLabel ι)
    (t₁ t₂ : Λ → ℝ) (U : Λ → 𝓢(ℝ, ℂ)) (K : Λ → ℝ)
    (hK : ∀ l ∈ labels, 0 < K l)
    (hU : ∀ l ∈ labels, ∀ z : O, 0 ≤ (U l (‖eisEmbedding z‖ ^ 2 / K l)).re)
    (hmajor : ∀ l ∈ labels, ∀ z ∈ rows,
      1 ≤ (U l (‖eisEmbedding z‖ ^ 2 / K l)).re)
    (w : Λ → O → ℂ) (hw : ∀ l ∈ labels, ∀ z ∈ rows, ‖w l z‖ ≤ 1) :
    ‖∑ l ∈ labels, ∑ z ∈ rows,
      w l z * (s l).leftValue (t₁ l) z * star ((s l).rightValue (t₂ l) z)‖ ≤
      Real.sqrt (∑ l ∈ labels, (s l).leftEnergy (t₁ l) (U l) (K l)) *
      Real.sqrt (∑ l ∈ labels, (s l).rightEnergy (t₂ l) (U l) (K l)) := by
  apply le_trans (norm_sum_le _ _)
  apply le_trans (Finset.sum_le_sum (fun l hl => norm_sum_le _ _))
  apply le_trans _ (joint_first_child_abs_bound labels rows s t₁ t₂ U K hK hU hmajor)
  apply Finset.sum_le_sum
  intro l hl
  apply Finset.sum_le_sum
  intro z hz
  simp only [norm_mul, norm_star]
  have h := mul_le_mul_of_nonneg_right (hw l hl z hz)
    (mul_nonneg (norm_nonneg ((s l).leftValue (t₁ l) z))
      (norm_nonneg ((s l).rightValue (t₂ l) z)))
  simpa only [one_mul, mul_assoc] using h

#print axioms joint_first_child_abs_bound
#print axioms joint_first_child_bound

end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstBlock -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstOriginalTail ; sha256 deca13eb60f73ee2a1af4b7202957e3064cf7d1008ae0ab0488fad1cc608e44d -/
section



/-! The first discarded energy at the literal source support radius.
The normalizing volume is kept separate from that physical radius. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentSourceInputTailUniform CenteredMomentSourceInputFirstTailUniform
open CenteredMomentSourceInputFirstSectorTail CenteredMomentNaturalRadialCutoff
open CenteredMomentExceptionalAmplitudePair CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance firstOriginalTailSumDecEq : DecidableEq (ι⊕Fin 2) := Classical.decEq _

theorem first_original_source_tail (hi : ι → ℝ) (a b ξ saving : ℝ)
    (hhi : ∀ i, 0 ≤ hi i) (ha : 0 < a) (hb : 0 ≤ b) (hξ : 0 < ξ) :
    ∃ S : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (src : Input ι) (W₁ W₂ : 𝓢(ℝ,ℂ)), src.W₁ = W₁ → src.W₂ = W₂ →
      Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc a b →
      Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc a b →
      (∀ i, src.hi i ≤ hi i) → volume src.toData ≤ Z →
      0 < sourceRadius src → sourceRadius src ≤ Z →
    ∀ (m A : O) (R seed : Ideal O) (Φ : 𝓢(ℝ,ℂ)),
      ‖CenteredMomentFirstSectorLocalization.discardedEnergy src.η m A src.t
        (finiteColumns (Fintype.piFinset src.pools)) (coefficient src R seed)
        Φ Z (sourceRadius src) Z ξ‖ / volume src.toData ≤
      C * (plainControl src W₁ W₂)^2 * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ * Z^(1-saving) := by
  obtain ⟨Adec,hdecay⟩ := choose_first_tail_order 1 ξ saving (by norm_num) hξ
  obtain ⟨S,Ctail,hCtail,htail⟩ := local_discarded_energy_bound Adec 1 zero_lt_one
  let Cmass := 1+2*128^(Fintype.card ι+2)*(∏ i,hi i)*b^2
  have hp : 0 ≤ ∏ i,hi i := Finset.prod_nonneg (fun i _ => hhi i)
  have hCmass : 0 < Cmass := by dsimp only [Cmass]; positivity
  refine ⟨S,4*Cmass^2*Ctail,by positivity,?_⟩
  filter_upwards [eventually_tail_threshold 0 ξ hξ] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro src W₁ W₂ he₁ he₂ hs₁ hs₂ hshi hVcap hH hHcap m A R seed Φ
  have hz := zero_lt_one.trans hZ.1
  have hV := CenteredMomentSourceInputTailUniform.volume_pos src
  have hzW (W : 𝓢(ℝ,ℂ)) (hs : Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b) : W 0 = 0 := by
    by_contra hn
    exact (not_le_of_gt ha) (hs hn).1
  have hm := input_mass hi b hhi hb src W₁ W₂ a ha he₁ he₂ hs₁ hs₂ hshi R seed
  have hc := plainControl_nonneg src W₁ W₂
  have hmass : (∑ I ∈ finiteColumns (Fintype.piFinset src.pools),‖coefficient src R seed I‖) ≤
      Cmass*plainControl src W₁ W₂*volume src.toData := by
    apply hm.trans
    apply mul_le_mul_of_nonneg_right _ hV.le
    apply mul_le_mul_of_nonneg_right _ hc
    dsimp only [Cmass]
    linarith
  let Tsec := (sourceRadius src)^2/Z
  have hT : 0 < Tsec := div_pos (sq_pos_of_pos hH) hz
  have hTcap : Tsec ≤ Z^(1:ℝ) := by
    rw [Real.rpow_one]
    dsimp only [Tsec]
    apply (div_le_iff₀ hz).mpr
    nlinarith
  have hn (I : Ideal O) (_hI : I ∈ finiteColumns (Fintype.piFinset src.pools))
      (hn : coefficient src R seed I ≠ 0) : (I.absNorm : ℝ) ≤ Real.exp 0*sourceRadius src := by
    simpa only [Real.exp_zero,one_mul] using
      (original_column_norm src R seed I (he₁.symm ▸ hzW W₁ hs₁) (he₂.symm ▸ hzW W₂ hs₂) hn).2
  have ht := htail src.η m A src.t (finiteColumns (Fintype.piFinset src.pools))
    (coefficient src R seed) Φ Z (sourceRadius src) 0 Tsec Z 1 ξ
    hz hH hZ.1 le_rfl hn le_rfl (by simpa using hZ.2)
  simp only [Real.exp_zero,one_mul,Real.rpow_one] at ht
  have hden : 0 < (min 1 (kernelReference Tsec 0))^2*(1+Z^(ξ/4))^Adec := by
    have hk := kernelReference_pos Tsec 0 hT
    positivity
  have hbnd := hdecay 0 Z Z Tsec hZ.1.le hz (by simp) hT hTcap
  simp only [mul_zero,Real.exp_zero] at hbnd
  norm_num at hbnd
  have hsq := pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hmass 2
  calc
    _ ≤ ((Cmass*plainControl src W₁ W₂*volume src.toData)^2*sourceRadius src*Z*
        (Ctail*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
        ((min 1 (kernelReference Tsec 0))^2*(1+Z^(ξ/4))^Adec))/volume src.toData := by
      apply div_le_div_of_nonneg_right _ hV.le
      apply ht.trans
      apply div_le_div_of_nonneg_right _ hden.le
      gcongr
    _ = (Cmass^2*Ctail*(plainControl src W₁ W₂)^2*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z)*
        ((volume src.toData*sourceRadius src)*((min 1 (kernelReference Tsec 0))^2)⁻¹*
          ((1+Z^(ξ/4))^Adec)⁻¹) := by
      field_simp
    _ ≤ (Cmass^2*Ctail*(plainControl src W₁ W₂)^2*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z)*
        (Z^2*((min 1 (kernelReference Tsec 0))^2)⁻¹*((1+Z^(ξ/4))^Adec)⁻¹) := by
      gcongr
      nlinarith
    _ ≤ (Cmass^2*Ctail*(plainControl src W₁ W₂)^2*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z)*
        (4*Z^(-saving)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      convert hbnd using 1 <;> ring
    _ = _ := by
      rw [show (1:ℝ)-saving=1+(-saving) by ring,Real.rpow_add hz,Real.rpow_one]
      ring

#print axioms first_original_source_tail
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstOriginalTail -/

/- BEGIN ORIGINAL MODULE Analytic.JointFourier ; sha256 69c659b48c0526b3af499563700ca2546bf623b31204a8019e9c2ba6cd809feb -/
section




/-! Common Fourier majorants allow a label-dependent kernel without
paying the number of arithmetic labels. The energies below are joint
sums at the same Fourier variable. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open MeasureTheory
namespace SevenEighths.Local44.Analytic
open CenteredMomentSmooth CenteredMomentCauchy FirstPassCubeLabels

theorem whole_kernel_common_majorant (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ,ℂ),
      (∀ ρ x u v : ℝ, wholeKernel W V R ρ x u v =
        ∫ t : ℝ, separatedKernel V ρ x u v t*b t) ∧
      (∀ t : ℝ, (1+R)^A*‖b t‖ ≤ C*firstLogDensity J t) := by
  obtain ⟨C,hC,hs⟩ := whole_kernel_separation W V M hM hV A (J+2)
  refine ⟨C,hC,?_⟩
  intro R hR
  obtain ⟨b,hb,_,_,hp⟩ := hs R hR
  refine ⟨b,hb,?_⟩
  intro t
  rw [firstLogDensity, ← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1+‖t‖) (J+2))).mpr
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hp t

/-- Finite Hilbert sums with densities that may vary with the full
arithmetic label. A common majorant replaces any count of labels. -/
theorem joint_integral_energy {κ : Type*} [Fintype κ]
    (b φ : κ → ℝ → ℂ) (m w : ℝ → ℝ)
    (hm : ∀ t, 0 ≤ m t) (hw : ∀ t, 0 ≤ w t)
    (E : ℝ) (hE : 0 ≤ E) (hi : Integrable (fun t => m t*w t))
    (hφ : ∀ k, Integrable (fun t => b k t*φ k t))
    (hb : ∀ k t, ‖b k t‖ ≤ m t)
    (he : ∀ t, (∑ k, ‖φ k t‖^2) ≤ E*(w t)^2) :
    (∑ k, ‖∫ t : ℝ, b k t*φ k t‖^2) ≤ E*(∫ t : ℝ, m t*w t)^2 := by
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : κ => ℂ)
  let F : ℝ → EuclideanSpace ℂ κ := fun t => e.symm (fun k => b k t*φ k t)
  have hF (t : ℝ) : ‖F t‖ ≤ (m t*w t)*Real.sqrt E := by
    apply (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (mul_nonneg (hm t) (hw t)) (Real.sqrt_nonneg E))).mp
    rw [EuclideanSpace.norm_sq_eq, mul_pow, mul_pow, Real.sq_sqrt hE]
    change (∑ k, ‖b k t*φ k t‖^2) ≤ (m t)^2*(w t)^2*E
    calc
      _ ≤ ∑ k, (m t)^2*‖φ k t‖^2 := by
        apply Finset.sum_le_sum
        intro k hk
        rw [norm_mul,mul_pow]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) (hb k t) 2) (sq_nonneg _)
      _ = (m t)^2*(∑ k, ‖φ k t‖^2) := (Finset.mul_sum ..).symm
      _ ≤ (m t)^2*(E*(w t)^2) := mul_le_mul_of_nonneg_left (he t) (sq_nonneg _)
      _ = _ := by ring
  have hident : (∫ t : ℝ, F t) = e.symm (fun k => ∫ t : ℝ, b k t*φ k t) := by
    rw [show F = (fun t => e.symm (fun k => b k t*φ k t)) from rfl,
      e.symm.integral_comp_comm]
    congr 1
    funext k
    exact eval_integral hφ k
  have hn : ‖e.symm (fun k => ∫ t : ℝ, b k t*φ k t)‖ ≤
      (∫ t : ℝ, m t*w t)*Real.sqrt E := by
    rw [← hident, ← integral_mul_const]
    exact norm_integral_le_of_norm_le (hi.mul_const _) (Filter.Eventually.of_forall hF)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [EuclideanSpace.norm_sq_eq,mul_pow,Real.sq_sqrt hE] at hs
  simpa [e,mul_comm] using hs

theorem joint_integral_pair_bound {κ : Type*} (rows : Finset κ)
    (b A B : κ → ℝ → ℂ) (m w : ℝ → ℝ)
    (hm : ∀ t, 0 ≤ m t) (E : ℝ)
    (hi : Integrable (fun t => m t*w t))
    (hrow : ∀ k ∈ rows, Integrable (fun t => b k t*A k t*B k t))
    (hb : ∀ k ∈ rows, ∀ t, ‖b k t‖ ≤ m t)
    (he : ∀ t, (∑ k ∈ rows, ‖A k t‖*‖B k t‖) ≤ E*w t) :
    ‖∑ k ∈ rows, ∫ t : ℝ, b k t*A k t*B k t‖ ≤
      E*(∫ t : ℝ, m t*w t) := by
  have hpoint (t : ℝ) : ‖∑ k ∈ rows, b k t*A k t*B k t‖ ≤ E*(m t*w t) := by
    calc
      _ ≤ ∑ k ∈ rows, ‖b k t*A k t*B k t‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ rows, m t*(‖A k t‖*‖B k t‖) := by
        apply Finset.sum_le_sum
        intro k hk
        simp only [norm_mul]
        nlinarith [mul_le_mul_of_nonneg_right (hb k hk t)
          (mul_nonneg (norm_nonneg (A k t)) (norm_nonneg (B k t)))]
      _ = m t*(∑ k ∈ rows, ‖A k t‖*‖B k t‖) := (Finset.mul_sum ..).symm
      _ ≤ m t*(E*w t) := mul_le_mul_of_nonneg_left (he t) (hm t)
      _ = _ := by ring
  rw [← integral_finsetSum _ hrow]
  calc
    _ ≤ ∫ t : ℝ, E*(m t*w t) :=
      norm_integral_le_of_norm_le (hi.const_mul E) (Filter.Eventually.of_forall hpoint)
    _ = _ := integral_const_mul _ _

#print axioms whole_kernel_common_majorant
#print axioms joint_integral_energy
#print axioms joint_integral_pair_bound
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFourier -/
