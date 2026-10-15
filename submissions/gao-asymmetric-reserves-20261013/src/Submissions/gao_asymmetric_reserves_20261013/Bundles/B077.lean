/- Asymmetric reserve and endpoint refinement: Zhongpai Gao, with AI assistance. Adapts Kari Roegnvaldsson’s affine/reserve source at 14ab1618c5133a7d12e06aa76661bbcb34e843cd, following accepted c707738a659786b9a44a79c629bed8c801cca8f3. Original notices below are retained. -/
/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B005
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B006
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B047
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B064
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B065
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B073
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B074
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B075
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B076
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.AllocatedClipped
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainRelativeClass

/- BEGIN ORIGINAL MODULE Physical.Selection ; sha256 1a1a61542523c50d675c95e31599b4f02d245eec0f0b571764fb1d33543cf534 -/
section


noncomputable section
open scoped Classical BigOperators
namespace Local44.Physical
open OAI.SevenEighths HeckeDetectorSlotSelection HeckeDetectorPhysicalSelection

theorem transport_whole_slots {α : Type*} (slots main : Finset α) (w g : α → ℝ)
    (n t δ mesh : ℝ) (hn : BareWindow n) (ht : 0 ≤ t)
    (hδ : 0 ≤ δ) (hmesh : 0 ≤ mesh)
    (hw : ∀ i ∈ slots, 0 ≤ w i) (hwm : ∀ i ∈ slots, w i ≤ mesh)
    (hL : baseCapacity n ≤ ∑ i ∈ slots, w i)
    (hg : ∀ i ∈ slots, 0 ≤ g i ∧ g i ≤ δ/2)
    (herror : ∀ i ∈ slots, i ∉ main → g i = 0) :
    ∃ selected : Finset α, selected ⊆ slots ∧ selected ⊆ main ∧
      (∀ i ∈ selected, 0 < g i) ∧
      (∑ i ∈ selected, w i) ≤ transportCapacity n t ∧
      weightedMean slots w g*transportCapacity n t-(δ/2)*mesh ≤ ∑ i ∈ selected, w i*g i ∧
      ∀ U : ℝ, 1 ≤ U → ∀ Q : α → ℂ,
        (∀ i ∈ slots, 0 < g i → U^(2*w i*g i) ≤ ‖Q i‖^2) →
        U^(2*weightedMean slots w g*transportCapacity n t-δ*mesh) ≤ ‖∏ i ∈ selected, Q i‖^2 := by
  have hLpos : 0 < ∑ i ∈ slots, w i := by
    have hb := (baseCapacity_bounds hn).1
    linarith
  exact Cycle25.Numerator.SlotSelection.zero_error_whole_slots slots main w g δ mesh
    (transportCapacity n t) hδ hmesh hw hwm hLpos hg herror
    (transportCapacity_nonneg n t) (transportCapacity_le_supply hn ht hL)

end Local44.Physical
end
/- END ORIGINAL MODULE Physical.Selection -/

/- BEGIN ORIGINAL MODULE Analytic.JointErrorLedger ; sha256 7093c32b3737b98eca49389c9e3278817879626744a6481fa21c2a2e2dd6cff0 -/
section



/-! The refined source Gaussian power at the exact first common reference.
The actual local scalar cancels the moving conductor, extraction pays its
full prime-power norm, and the normalized prime average stays normalized. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentAmplificationErrorEnergy CenteredMomentFirstMixedNormalization
open CenteredMomentFirstAmplifiedFourCoefficients CenteredMomentPrimePool CenteredMomentPrimeElements
open RayFourExpansion
local notation "O" => HeckeFamily.O

/-- The exceptional, diagonal and tail powers retain the exact source
formulas. Only the nonexceptional removal power uses the refined defect. -/
lemma refined_errorPowers_nonmain (p : O) (k : ℕ)
    (q Z Kerror sigma deficit paid saving r : ℝ) (j : Fin 4) (hj : j ≠ 0) :
    errorPowers p k q Z Kerror (refinedErrorDeficit p Z k sigma deficit) paid saving r j =
      errorPowers p k q Z Kerror deficit paid saving r j := by
  fin_cases j <;> simp_all [errorPowers]

/-- Literal prime scalar, prime-power extraction and first common reference.
The local cost-`22/5` geometry enters only through the original affine gap. -/
theorem refined_error_main_core (p : O) (hp : p ≠ 0) (k : ℕ)
    (hk : k=1 ∨ k=6 ∨ k=7)
    (q V C Z allowance Kerror deficit paid eps saving r : ℝ)
    (hq : 0 < q) (hV : 0 < V) (hC : 0 < C) (hZ : 1 < Z)
    (hB : 0 ≤ allowance) (hdef : deficit ≤ 1/241)
    (hlog : 9/2000 ≤ Real.logb Z (normValue p)) :
    errorCores p k q V C Z allowance Kerror
      (refinedErrorDeficit p Z k (9/500) deficit) paid eps saving r 0 ≤
        Z^(paid-1/1250) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hpv := normValue_pos p hp
  have hw := actual_error_weight p hp Z hZ k hk
  have hs : localErrorCost p (k-1)*Z^(errorMoving p Z k) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hw (Real.rpow_nonneg hz.le (errorMoving p Z k))
    rw [← Real.rpow_add hz,neg_add_cancel,Real.rpow_zero] at hh
    exact hh
  have he : errorCores p k q V C Z allowance Kerror
      (refinedErrorDeficit p Z k (9/500) deficit) paid eps saving r 0 =
      (localErrorCost p (k-1)*Z^(errorMoving p Z k))*
        Z^((refinedErrorDeficit p Z k (9/500) deficit)/6+paid-allowance) := by
    dsimp [errorCores,reference]
    rw [Real.rpow_sub hz,
      show errorRemoval p Z k+refinedErrorDeficit p Z k (9/500) deficit/6+paid =
        errorRemoval p Z k+(refinedErrorDeficit p Z k (9/500) deficit/6+paid) by ring,
      Real.rpow_add hz,errorRemoval_power p hp Z hZ k]
    field_simp
  have hr := amplification_error_positive_excess p Z
    (deficit+9/500+errorRemoval p Z k-errorMoving p Z k) k hk hlog (by linarith)
  have hm := le_max_left (deficit+9/500+errorRemoval p Z k-errorMoving p Z k) (0 : ℝ)
  rw [he]
  calc
    _ ≤ 1*Z^(refinedErrorDeficit p Z k (9/500) deficit/6+paid-allowance) :=
      mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hz.le _)
    _ ≤ _ := by
      rw [one_mul]
      apply Real.rpow_le_rpow_of_exponent_le hZ.le
      unfold refinedErrorDeficit
      linarith

/-- Exact normalization of the first power in `actual_original_subsets_error_power`. -/
theorem refined_error_main_power (p : O) (hp : p ≠ 0) (k : ℕ)
    (hk : k=1 ∨ k=6 ∨ k=7)
    (q V C Z allowance Kerror deficit paid eps saving r : ℝ)
    (hq : 0 < q) (hV : 0 < V) (hC : 0 < C) (hZ : 1 < Z)
    (hB : 0 ≤ allowance) (hdef : deficit ≤ 1/241)
    (hlog : 9/2000 ≤ Real.logb Z (normValue p)) :
    (V/C)*localErrorCost p (k-1)*
      errorPowers p k q Z Kerror (refinedErrorDeficit p Z k (9/500) deficit) paid saving r 0*
        (V/C/(normValue p)^k)^(CenteredMomentSecondChildPowerBudget.powers eps 0)/
          reference q V C Z allowance ≤ Z^(paid-1/1250) := by
  rw [← error_core_power]
  exact refined_error_main_core p hp k hk q V C Z allowance Kerror deficit paid eps saving r
    hq hV hC hZ hB hdef hlog

/-- All first labels and the prime average are retained. The only finite
factor comes from the three actual valuations and fixed ray characters. -/
theorem joint_refined_error_main_average {Λ : Type*}
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes ⊆ Sbad) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^((9/500 : ℝ)/3))
      ∀ labels : Finset Λ, ∀ weight q V C allowance deficit paid : Λ → ℝ,
      ∀ Kerror r : elementPool P → Λ → Fin 3 → RayCharacter → ℝ,
      ∀ eps saving : ℝ, P.Nonempty →
      (∀ l ∈ labels, 0 ≤ weight l) →
      (∀ l ∈ labels, 0 < q l) → (∀ l ∈ labels, 0 < V l) → (∀ l ∈ labels, 0 < C l) →
      (∀ l ∈ labels, 0 ≤ allowance l) → (∀ l ∈ labels, deficit l ≤ 1/241) →
      (56/(P.card : ℝ))*(∑ p : elementPool P, ∑ l ∈ labels, weight l*
        ∑ i : Fin 3, 16*(errorIndex i+2 : ℝ)^2*∑ χ : RayCharacter,
          errorCores p (errorIndex i+1) (q l) (V l) (C l) Z (allowance l) (Kerror p l i χ)
            (refinedErrorDeficit p Z (errorIndex i+1) (9/500) (deficit l))
            (paid l) eps saving (r p l i χ) 0) ≤
        (56*1872*(Fintype.card RayCharacter : ℝ))*(∑ l ∈ labels, weight l*Z^(paid l-1/1250)) := by
  filter_upwards [eventually_pool_prime_quarter_lower M H Sbad hbad (9/500) (by norm_num)]
    with Z hZ
  refine ⟨hZ.1,?_⟩
  dsimp only
  intro labels weight q V C allowance deficit paid Kerror r eps saving hP hw hq hV hC hB hdef
  let P := primePool M H Sbad (1/2) 1 (Z^((9/500 : ℝ)/3))
  have hp : ∀ Q ∈ P, Prime Q := fun Q hQ => (primePool_data M H Sbad hbad (1/2) 1
    (Z^((9/500 : ℝ)/3)) Q hQ).1
  have hbadP : ∀ Q ∈ P, Q ∉ fixedBadPrimes := fun Q hQ => (primePool_data M H Sbad hbad (1/2) 1
    (Z^((9/500 : ℝ)/3)) Q hQ).2
  apply joint_amplification_error_average labels weight (fun l => Z^(paid l-1/1250))
    P hP hp hbadP _ hw (fun _ _ => Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _)
  intro p l hl i χ
  have hdata := elementPool_data P hp hbadP p.val p.property
  apply refined_error_main_core p hdata.1.ne_zero (errorIndex i+1) (by
    fin_cases i <;> norm_num [errorIndex]) (q l) (V l) (C l) Z (allowance l) (Kerror p l i χ)
    (deficit l) (paid l) eps saving (r p l i χ)
    (hq l hl) (hV l hl) (hC l hl) hZ.1 (hB l hl) (hdef l hl)
  linarith [(hZ.2 p p.property).1]

#print axioms refined_error_main_power
#print axioms joint_refined_error_main_average
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointErrorLedger -/

/- BEGIN ORIGINAL MODULE Analytic.JointHighRetained ; sha256 725d891b5b126dec98deb5909db028edda31fa6e60ea877a30633887cad16c6f -/
section




/-! The actual retained source sum uses the joint high theorem exactly
once, after selecting one literal branch in each arithmetic fiber. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification HeckeDetectorZeros CanonicalQuadraticSieve
open IdealMobiusDivisorSum LocalMoment ProbeHighRowFamily ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

def retainedProfileEnvelope {α Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (S : Finset α) (s : α → CommonSecondKernelLabel Slot) (a : ℝ) : ℝ :=
  if h : S.Nonempty then max 1 (S.sup' h (fun v =>
    (secondProfileScalar (s v).input.toData)^2*commonSourceProfile (s v).input/a)) else 1

theorem retainedProfileEnvelope_nonneg {α Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (S : Finset α) (s : α → CommonSecondKernelLabel Slot) (a : ℝ) :
    0 ≤ retainedProfileEnvelope S s a := by
  unfold retainedProfileEnvelope
  split_ifs <;> positivity

theorem retainedProfileEnvelope_bound {α Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (S : Finset α) (s : α → CommonSecondKernelLabel Slot) (a : ℝ) (v : α) (hv : v ∈ S) :
    (secondProfileScalar (s v).input.toData)^2*commonSourceProfile (s v).input/a ≤
      retainedProfileEnvelope S s a := by
  rw [retainedProfileEnvelope,dif_pos ⟨v,hv⟩]
  exact (Finset.le_sup' (fun v =>
    (secondProfileScalar (s v).input.toData)^2*commonSourceProfile (s v).input/a) hv).trans
      (le_max_right _ _)

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

/-- `hsource` is the exact source realization furnished by
`actual_retained_buffered_data`; it contains no bound for the products.
The full allocation mass and the joint high estimate are proved internally.
The maximum of the explicit fixed profile factors is retained for later
uniform source-profile control, without a sum or count of labels. -/
theorem actual_joint_high_retained_contribution
    (V : Slot → ℝ → ℂ) (Aprofile Bprofile : Slot → ℝ) (hA : ∀ j, 0 < Aprofile j)
    (hVs : ∀ j, Function.support (V j) ⊆ Icc (Aprofile j) (Bprofile j))
    (hV : ∀ j, ContDiff ℝ ∞ (V j))
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
    (profileBound : ℕ → ℝ) (hprofile : ∀ k, 0 ≤ profileBound k)
    (lo hi : Slot → ℝ) (fiberLoss : ℝ) (hfiberLoss : 0 < fiberLoss) :
    ∃ (τ ν : ℝ) (orders : Finset Slot → ℕ) (N : ℕ) (C : ℝ),
      0 < ν ∧ ν < τ ∧ τ < τdetector ∧ 4*τ < dmin*ηaux ∧
      (∀ J, orders J ≤ N) ∧ 0 < C ∧
      ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (d P W : ℝ), 0 ≤ d → d ≤ dmax → 2 ≤ Z^d → 2 < Z^τ → P ≤ B → W ≤ B →
      ∀ (p : DensityWindow), p.upper < p.lower+2*e →
      ∀ i : ℕ, i ≤ I → p.height = (3*(i+1 : ℕ))*Z^τ →
      ∀ (unit : JointReconstructionLabel → Oˣ) (S : Finset JointReconstructionLabel)
        (w : JointReconstructionLabel → NonzeroElement),
      (∀ v ∈ S, (w v).val = v.row (unit v)) →
      ∀ (R : JointReconstructionLabel →
        JointRelativeLabel η (Option (Slot × RayQuotient.Characters M H)) → Ideal O)
        (hR : ∀ v label, R v label ≠ 0),
      (∀ v ∈ S, Supported v.C₁ ∧ Supported v.D₁ ∧ Supported v.C₂ ∧ Supported v.D₂) →
      (∀ v ∈ S, primeSupport v.C₁ = primeSupport v.D₁ ∧ primeSupport v.C₂ = primeSupport v.D₂) →
      (∀ v ∈ S, Squarefree v.L ∧ v.L ∣ v.C₂ ∧ v.L ∣ v.D₂) →
      (∀ v ∈ S, jointRelativeSourceZeroBin η (relativeSlotTranslate M H hH η₀) Q hQ72
        (relativeSlotTranslate_fixedQ M H hH η₀ Q hQM hQη₀) (R v) (hR v)
        p.lower p.upper p.height (w v)) →
      (∀ v ∈ S, (Ideal.absNorm v.C₁ : ℝ) ≤ Z^B ∧ (Ideal.absNorm v.D₁ : ℝ) ≤ Z^B ∧
        (Ideal.absNorm v.C₂ : ℝ) ≤ Z^B ∧ (Ideal.absNorm v.D₂ : ℝ) ≤ Z^B) →
      (∀ v ∈ S, (Ideal.absNorm (Ideal.span {(w v).val}) : ℝ) ≤ Z^W) →
      (∀ v ∈ S, (Ideal.absNorm (jointMissingRadical v.C₁ (w v).val) : ℝ) ≤ Z^P) →
      ∀ (s : JointReconstructionLabel → CommonSecondKernelLabel Slot)
        (Ds : JointReconstructionLabel → Finset (Ideal O))
        (z : JointReconstructionLabel → O) (t₁ t₂ H₁ H₂ : JointReconstructionLabel → ℝ)
        (aSource : ℝ), 0 < aSource →
      (∀ v ∈ S, (∀ j, (s v).input.lo j = lo j) ∧ (∀ j, (s v).input.hi j = hi j)) →
      (∀ v ∈ S, (((s v).firstCommon*(s v).second.val.1).absNorm : ℝ) ≤ Z^(2*B) ∧
        (((s v).firstCommon*(s v).second.val.2).absNorm : ℝ) ≤ Z^(2*B)) →
      (∀ v ∈ S, ∀ L ∈ Ds v, (UniqueFactorizationMonoid.moebius L : ℂ) ≠ 0 →
        (L.absNorm : ℝ) ≤ Z^(2*B)) →
      (∀ v ∈ S, 0 < H₁ v ∧ 0 < H₂ v ∧
        aSource*CenteredMomentExceptionalAmplitudePair.volume (s v).input.toData/
          (((s v).firstCommon*(s v).second.val.1).absNorm : ℝ) ≤ H₁ v ∧
        aSource*CenteredMomentExceptionalAmplitudePair.volume (s v).input.toData/
          (((s v).firstCommon*(s v).second.val.2).absNorm : ℝ) ≤ H₂ v) →
      ∀ (A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ : ℝ),
      2*b₂ = c₂+d₂ →
      (∀ v ∈ S, ∀ q ∈ (s v).activeFullRetainedFiber (Ds v) (t₁ v) (t₂ v) (H₁ v) (H₂ v) (z v),
        ∃ DL DR : SurvivingBufferedData η (w v) Slot orders profileBound p.lower e,
          (s v).fullFiberValue (t₁ v) (t₂ v) (z v) q =
            ‖DL.value M H η₀ V Bprofile Z d‖*‖DR.value M H η₀ V Bprofile Z d‖ ∧
          d*DL.length ≤ A-c-c₂+lengthLoss ∧ d*DR.length ≤ A-c-d₂+lengthLoss ∧
          DL.Admissible M H hH η₀ Aprofile Bprofile Rwidth τ ηaux σmin σmax Z d p.height ∧
          DR.Admissible M H hH η₀ Aprofile Bprofile Rwidth τ ηaux σmin σmax Z d p.height) →
      67/100 ≤ 2*p.lower-1 → 2*p.lower-1 ≤ 3/4 → A ≤ 883/1000 →
      0 ≤ π → π ≤ c → π ≤ d₁ → R₁ ≤ π →
      0 ≤ R₀ → 0 ≤ E → 0 ≤ Bc → L ≤ 5*(R₁-R₀) →
      0 ≤ b₂ → g₂ ≤ b₂ → 0 ≤ t₂cost → 0 ≤ geometryLoss → 0 ≤ lengthLoss →
      W ≤ 1-R₁-max (c-d₁) 0+L-6*(3/500)+geometryLoss → P ≤ π-R₁-E+R₀+missingLoss →
      omegaLoss+fiberLoss+loss+heightLoss+geometryLoss+lengthLoss+missingLoss ≤ 144011/109800000 →
      Z^(A-min c d₁+R₁+E-1+5*(3/500)+g₂-t₂cost-b₂+omegaLoss)*
        (∑ v ∈ S, ∑ D ∈ Ds v, ‖(UniqueFactorizationMonoid.moebius D : ℂ)‖ *
          ((s v).withProjector D).retainedPair (t₁ v) (t₂ v) (z v) (H₁ v) (H₂ v)) ≤
        C*retainedProfileEnvelope S s aSource*Z^(π+A-c+R₁+E+Bc-144011/109800000) := by
  obtain ⟨τ,ν,orders,N,Ch,hν,hντ,hτdet,hheight,horders,hCh,hhigh⟩ :=
    actual_joint_high_contribution η η₀ Q hQtop hQ72 hQη hβ M H hH hQM hQη₀ S₀
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB hβupper
      V Aprofile Bprofile hA hVs hV Rwidth dmax ε e κ ηaux σmin σmax
      productLoss populationLoss loss B hRw hdmax hε he he' hκ hκone hη hbudget hprimebudget
      hproductLoss hpopulationLoss hB hloss τdetector dmin heightLoss I hτdetector hdmin hheightLoss
      profileBound hprofile
  obtain ⟨Cm,hCm,hmass⟩ := actual_complete_retained_fiber_mass lo hi (2*B) fiberLoss
    (by positivity) hfiberLoss
  refine ⟨τ,ν,orders,N,Cm*Ch,hν,hντ,hτdet,hheight,horders,mul_pos hCm hCh,?_⟩
  filter_upwards [hmass] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro d P W hd hdmax' hbase hT hPB hWB p hp i hi hheightBin unit S w hw R hR
    hsup heq hproj hbin hnorm hNw hNr s Ds z t₁ t₂ H₁ H₂ aSource haSource
    hsourceIntervals hsourceNorm hprojectorNorm hphysical
    A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ hb₂ hsource
    hδ hδtop hAtop hp₀ hpc hpd hRp hR₀ hE hBc hL hb₂₀ hg₂ ht₂
    hgeometryLoss hlengthLoss hW hP htotal
  let outside := A-min c d₁+R₁+E-1+5*(3/500)+g₂-t₂cost-b₂+omegaLoss
  let target := π+A-c+R₁+E+Bc-144011/109800000
  let envelope := retainedProfileEnvelope S s aSource
  let Ebound := Ch*Z^target/Z^(outside+fiberLoss)
  let massBound := Cm*Z^fiberLoss*envelope
  let fiber := fun v => (s v).activeFullRetainedFiber (Ds v) (t₁ v) (t₂ v) (H₁ v) (H₂ v) (z v)
  let weight := fun v => (s v).fullFiberWeight (t₁ v) (t₂ v) (H₁ v) (H₂ v)
  let value := fun v => (s v).fullFiberValue (t₁ v) (t₂ v) (z v)
  let gate := fun v (DL DR : SurvivingBufferedData η (w v) Slot orders profileBound p.lower e) =>
    d*DL.length ≤ A-c-c₂+lengthLoss ∧ d*DR.length ≤ A-c-d₂+lengthLoss ∧
    DL.Admissible M H hH η₀ Aprofile Bprofile Rwidth τ ηaux σmin σmax Z d p.height ∧
    DR.Admissible M H hH η₀ Aprofile Bprofile Rwidth τ ηaux σmin σmax Z d p.height
  have hZpos : 0 < Z := zero_lt_one.trans hZ.1
  have henv : 0 ≤ envelope := retainedProfileEnvelope_nonneg S s aSource
  have hmassBound (v : JointReconstructionLabel) (hv : v ∈ S) :
      (∑ q ∈ fiber v, weight v q) ≤ massBound := by
    apply ((s v).activeFullRetainedFiber_mass_le (Ds v) (t₁ v) (t₂ v) (H₁ v) (H₂ v) (z v)).trans
    apply (hZ.2 (s v) (hsourceIntervals v hv).1 (hsourceIntervals v hv).2
      (hsourceNorm v hv).1 (hsourceNorm v hv).2 (Ds v) (hprojectorNorm v hv)
      (t₁ v) (t₂ v) (H₁ v) (H₂ v) aSource haSource
      (hphysical v hv).1 (hphysical v hv).2.1 (hphysical v hv).2.2.1 (hphysical v hv).2.2.2).trans
    exact mul_le_mul_of_nonneg_left (retainedProfileEnvelope_bound S s aSource v hv) (by positivity)
  have hselected (T : Finset JointReconstructionLabel) (hTS : T ⊆ S)
      (FL FR : ∀ v, SurvivingBufferedData η (w v) Slot orders profileBound p.lower e)
      (hgates : ∀ v ∈ T, gate v (FL v) (FR v)) :
      (∑ v ∈ T, ‖(FL v).value M H η₀ V Bprofile Z d‖ *
        ‖(FR v).value M H η₀ V Bprofile Z d‖) ≤ Ebound := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hZpos _)).mpr
    have hh := hhigh Z d P W hZ.1 hd hdmax' hbase hT hPB hWB p hp i hi hheightBin
      unit T w (fun v hv => hw v (hTS hv)) R hR (fun v hv => hsup v (hTS hv))
      (fun v hv => heq v (hTS hv)) (fun v hv => hproj v (hTS hv))
      (fun v hv => hbin v (hTS hv)) (fun v hv => hnorm v (hTS hv))
      (fun v hv => hNw v (hTS hv)) (fun v hv => hNr v (hTS hv)) FL FR
      (fun v hv => (hgates v hv).2.2.1) (fun v hv => (hgates v hv).2.2.2)
      A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost (omegaLoss+fiberLoss) geometryLoss lengthLoss missingLoss c₂ d₂
      hb₂ (fun v hv => (hgates v hv).1) (fun v hv => (hgates v hv).2.1)
      hδ hδtop hAtop hp₀ hpc hpd hRp hR₀ hE hBc hL hb₂₀ hg₂ ht₂ hgeometryLoss hlengthLoss
      hW hP (by linarith)
    convert hh using 1 <;> dsimp [outside,target] <;> ring
  have hweighted := joint_buffered_product_fibers_of_exists M H η η₀ V Bprofile
    orders profileBound p.lower e Z d S w fiber weight value massBound Ebound
    (by dsimp [massBound]; positivity) (by dsimp [Ebound]; positivity) gate
    (fun v _ q _ => (s v).fullFiberWeight_nonneg _ _ _ _ q)
    (fun v _ q _ => (s v).withProjector q.1 |>.fiberValue_nonneg _ _ _ q.2)
    hmassBound hsource hselected
  calc
    _ ≤ Z^outside*(∑ v ∈ S, ∑ q ∈ fiber v, weight v q*value v q) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hZpos.le _)
      exact Finset.sum_le_sum (fun v hv =>
        (s v).retained_projector_sum_le_activeFullFiber (Ds v) (t₁ v) (t₂ v) (H₁ v) (H₂ v) (z v))
    _ ≤ Z^outside*(massBound*Ebound) := mul_le_mul_of_nonneg_left hweighted (Real.rpow_nonneg hZpos.le _)
    _ = (Cm*Ch)*retainedProfileEnvelope S s aSource*Z^target := by
      dsimp only [massBound,Ebound,envelope]
      rw [Real.rpow_add hZpos outside fiberLoss]
      field_simp
      <;> ring

end FixedData
#print axioms actual_joint_high_retained_contribution
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointHighRetained -/

/- BEGIN ORIGINAL MODULE Analytic.JointLowAllocated ; sha256 289ca257bcc8a79893e383d54ade6f670a7a6630f78a6d562723f6cd34faf6fc -/
section






/-! The actual low-bin source coefficients after both common and divisor
allocations. The source dictionary map returns surviving indices to the
original fixed slot system while preserving the same low-bin indicator. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open Set Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeDyadic HeckeDetectorZeros HeckePrimeRay HeckePrimeAnnular
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentPrimeSlot ConcretePrimeRowBridge LocalMoment LocalMomentSourceAudit
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyPaidBands
open CenteredMomentRetainedEnergy CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open QuadraticInitialBound
open CenteredMomentEnergyCapacityRemoval
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentDivisorAllocation
open CenteredMomentAllocatedRayDictionary
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance lowAllocatedFiniteQuotient : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)


variable {α : Type*} [Fintype α] [DecidableEq α]

theorem actual_allocated_low_moment
    (W : ℝ → ℂ) (aslot bslot a b radial Bmask L lo hi Mcap εmoment : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0 ≤ bslot)
    (ha : 0 < a) (haUpper : a ≤ 1/4) (hb : 1 ≤ b) (hrad : 0 < radial)
    (hmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hεmoment : 0 < εmoment)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) (hbetaTop : HeckeZeroSupremum.beta ≤ 7/8)
    (Rwidth d τ εslot e κ ηheight loss : ℝ)
    (hRw : 0 < Rwidth) (hd : 0 < d) (hτ : 0 < τ) (hεslot : 0 < εslot)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ ηheight)
    (hbudget : 8*e*Rwidth+κ ≤ εslot)
    (mesh : ℝ) (hmesh : 0 < mesh)
    (hmeshInc : mesh ≤ Cycle25.Energy.commonMesh Mcap Bmask L εmoment)
    (hmeshWidth : mesh ≤ d*Rwidth)
    (hmeshLoss : εmoment+(67/100)*mesh+2*d*εslot*(Fintype.card α) ≤ loss) :
    ∃ (degree : ℕ) (S : Finset (ℕ × ℕ)),
      ∀ (η₀ : Character) (Q : Ideal O) (hQM : Q ≤ M), internalQ Q η₀ ≠ 0 →
      internalQ Q η₀ ≠ ⊤ → internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
      ∃ Cbound : ℝ, 0 < Cbound ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (θ : α → RayQuotient.Characters M H) (w σ freq : α → ℝ)
        (v height : ℝ),
      (∀ i, 0 ≤ w i) → (∀ i, w i ≤ mesh) →
      (∀ i, lo ≤ σ i) → (∀ i, σ i ≤ hi) → 0 ≤ height → (∀ i, |freq i| ≤ height) →
      ∀ (s : NaturalState Z Bmask radial) (hQ : s.fixedModulus = internalQ Q η₀),
      s.width ≤ Mcap → ∀ (low : O → Prop) (abin : ℝ) (k : ℕ),
      51/100 ≤ abin → abin ≤ 167/200 → 2 ≤ Z^d → 2 < Z^τ →
      (∀ z, ∀ hz : s.radial.keep z, low z → NaturalLowGate M H hH s η₀ Q hQM hQ d τ e abin k z hz) →
      (∀ i, |v+freq i|+Z^τ/2 ≤ (3*k+2 : ℕ)*Z^τ) →
      (3+(3*k+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^ηheight →
      ∀ (p : Profiles a b) (X₁ X₂ : ℝ), 0 < X₁ → 0 < X₂ → X₁ ≤ Z^L → X₂ ≤ Z^L →
      ∀ src : Input α, Matches M H hH src η₀ θ w σ freq W bslot Z →
      ∀ (C R : Ideal O) (B : actualAllocations src.pools C) (D : Ideal O)
        (alloc : Allocation D (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
        (J : Finset (CenteredMomentCommonProfile.liveIndices B.val)),
      let data := commonData (withHeight src s.character v) C R B
      energy s.character s.mask 1 0 (p.profile 0) (p.profile 1)
        (fun i : remaining src C B D alloc J => data.slots i.val)
        (fun i : remaining src C B D alloc J =>
          CenteredMomentCommonMaskEnergy.heightCoefficient (data.coefficient i.val) v)
        (fun i : remaining src C B D alloc J => data.P i.val)
        X₁ X₂ (fun z => s.radial.keep z ∧ low z) s.radial.profile s.radial.scale ≤
      Cbound*diagonalControl s.radial.profile*(p.control S)^2*(1+|v|+height)^degree *
        Z^(s.width+(67/450)*max (length Z X₁+length Z X₂+
          (9/2)*(∑ i ∈ originalImage src C B D alloc J, w i)-s.width) 0+loss) := by
  obtain ⟨degree,S,hmain⟩ := actual_joint_low_full_moment (α := α) M H hH W
    aslot bslot a b radial Bmask L lo hi Mcap εmoment haslot hWs hW hbslot
    ha haUpper hb hrad hmask hMcap hεmoment hbeta hbetaTop
    Rwidth d τ εslot e κ ηheight loss hRw hd hτ hεslot he he' hκ hη hbudget
    mesh hmesh hmeshInc hmeshWidth hmeshLoss
  refine ⟨degree,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,hmain⟩ := hmain η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cbound,hCbound,?_⟩
  filter_upwards [hmain] with Z hmain
  refine ⟨hmain.1,?_⟩
  intro θ w σ freq v height hw hwmesh hσlo hσhi hheight hfreq s hQ hs low abin k
    habin habinTop hbase hT hlow hfreqGate hheightSource p X₁ X₂ hX₁ hX₂ hc₁ hc₂
    src hmatch C R B D alloc J data
  dsimp only [data]
  rw [common_energy hmatch s.character v C R B D alloc J s.mask 1
    (p.profile 0) (p.profile 1) X₁ X₂ (fun z => s.radial.keep z ∧ low z)
    s.radial.profile s.radial.scale]
  have hh := hmain.2 (originalImage src C B D alloc J) θ w σ (fun i => v+freq i)
    0 (|v|+height) hw hwmesh hσlo hσhi (add_nonneg (abs_nonneg _) hheight)
    (fun i => (abs_add_le _ _).trans (add_le_add le_rfl (hfreq i))) s hQ hs low abin k
    habin habinTop hbase hT hlow (fun i _ => by simpa only [zero_add] using hfreqGate i)
    hheightSource p X₁ X₂ hX₁ hX₂ hc₁ hc₂
  simpa only [abs_zero,zero_add,add_assoc] using hh

#print axioms actual_allocated_low_moment
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowAllocated -/

/- BEGIN ORIGINAL MODULE Analytic.JointLowSourceGate ; sha256 ea10b7d452a6c9b5e45f2aea636b611a4288823eeb07820e01b78474438d4b89 -/
section



/-! Exact coefficient transport for low-bin source gates. The common
puncture and canceled-prime puncture remain present as their product. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentHeckeColumnWindow ConcretePrimeRowBridge
open CenteredMomentSourceRow
open CenteredMomentHeckeExpansion
local notation "O" => HeckeFamily.O

theorem naturalRow_masked_coeff_of_rowWeight
    (η τ : Character) (j w : O) (Ns : NaturalRow η j) (Nt : NaturalRow τ w)
    (R T : Ideal O) (hR : R ≠ 0) (hT : T ≠ 0)
    (he : ∀ I : Ideal O, rowWeight η fixedBadMask 1 j 0 I =
      heightCoeff (excluded Nt.character T) 0 I) (I : Ideal O) :
    idealCoeff (excluded Ns.character R) I =
      idealCoeff (excluded Nt.character (R*T)) I := by
  have hh := rowWeight_join_puncture η τ j w 0 T R
    (fun J => (he J).trans (naturalRow_masked_height Nt T hT 0 J)) I
  rw [←naturalRow_masked_height Ns R hR 0 I,
    ←naturalRow_masked_height Nt (R*T) (mul_ne_zero hR hT) 0 I] at hh
  simpa only [heightCoeff,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one] using hh

#print axioms naturalRow_masked_coeff_of_rowWeight
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowSourceGate -/

/- BEGIN ORIGINAL MODULE Analytic.JointRetainedLength ; sha256 dfafc75835185e48f6f41fde9241bf94a809db5b34b743782321cccbd108fa75 -/
section



/-! Nonzero extraction weights force the actual common support saving.
The second formal reduction is at least one for the original prime scales. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily CenteredMomentDivisorRaw CenteredMomentDivisorAllocation
open CenteredMomentDivisorRectangle CenteredMomentDivisorExtraction
open CenteredMomentSourceLiveColumn CenteredMomentCommonRadialData
local notation "O" => HeckeFamily.O

theorem formalReductionFactor_one_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Ideal O) (allocation : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (P : ι → ℝ) (hP : ∀ i, 1 ≤ P i) : 1 ≤ formalReductionFactor D allocation P := by
  have hN (j : Fin 2) : (1 : ℝ) ≤ Ideal.absNorm (selectedPlain D allocation j) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ allocation (Sum.inr j)))
  unfold formalReductionFactor selectedNorm
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (hN 0) (hN 1))
    (Finset.one_le_prod₀ (fun i _ => hP i))

namespace CommonSecondKernelLabel
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem activeFullRetainedFiber_frozen_ne (s : CommonSecondKernelLabel ι)
    (Ds : Finset (Ideal O)) (t₁ t₂ H₁ H₂ : ℝ) (z : O) (q : s.FullRetainedFiber)
    (hq : q ∈ s.activeFullRetainedFiber Ds t₁ t₂ H₁ H₂ z) :
    frozenCoefficient q.2.1.val (s.firstCommon*s.second.val.1) s.puncture
      s.input.ν s.input.W s.input.P ≠ 0 ∧
    frozenCoefficient q.2.2.1.val (s.firstCommon*s.second.val.2) s.puncture
      s.input.ν s.input.W s.input.P ≠ 0 := by
  obtain ⟨hL,hR⟩ := s.activeFullRetainedFiber_weights_ne Ds t₁ t₂ H₁ H₂ z q hq
  exact ⟨left_ne_zero_of_mul hL,left_ne_zero_of_mul hR⟩

theorem active_full_lengths (s : CommonSecondKernelLabel ι)
    (Ds : Finset (Ideal O)) (t₁ t₂ H₁ H₂ : ℝ) (z : O) (q : s.FullRetainedFiber)
    (hq : q ∈ s.activeFullRetainedFiber Ds t₁ t₂ H₁ H₂ z)
    (Z A c c₂ d₂ supportLoss clipLoss b₁ b₂ : ℝ)
    (hZ : 1 < Z) (hP : ∀ j, 1 ≤ s.input.P j)
    (hvolume : CenteredMomentExceptionalAmplitudePair.volume s.input.toData ≤ Z^A)
    (hC : Z^(c+c₂) ≤ ((s.firstCommon*s.second.val.1).absNorm : ℝ))
    (hD : Z^(c+d₂) ≤ ((s.firstCommon*s.second.val.2).absNorm : ℝ))
    (hsupport : (max 1 s.input.upper)^Fintype.card ι ≤ Z^supportLoss)
    (hclip : Real.logb Z (max 1 b₁*max 1 b₂) ≤ clipLoss) :
    s.fullLeftLength Z q+Real.logb Z (max 1 b₁*max 1 b₂) ≤ A-c-c₂+(supportLoss+clipLoss) ∧
    s.fullRightLength Z q+Real.logb Z (max 1 b₁*max 1 b₂) ≤ A-c-d₂+(supportLoss+clipLoss) := by
  obtain ⟨hnL,hnR⟩ := s.activeFullRetainedFiber_frozen_ne Ds t₁ t₂ H₁ H₂ z q hq
  have hvolL := actual_second_common_volume_sector s.input _ s.puncture q.2.1 hnL
    Z A (c+c₂) supportLoss hZ hvolume hC hsupport
  have hvolR := actual_second_common_volume_sector s.input _ s.puncture q.2.2.1 hnR
    Z A (c+d₂) supportLoss hZ hvolume hD hsupport
  dsimp only [withProjector] at hvolL hvolR
  have hredL := Real.logb_nonneg hZ
    (formalReductionFactor_one_le q.1 q.2.2.2.1 (fun i => s.input.P i.val) (fun i => hP i.val))
  have hredR := Real.logb_nonneg hZ
    (formalReductionFactor_one_le q.1 q.2.2.2.2.1 (fun i => s.input.P i.val) (fun i => hP i.val))
  unfold fullLeftLength fullRightLength
  constructor <;> linarith

/-- A first common-width sector loses its mesh once in the residual
length. This keeps the genuine cumulative norm instead of substituting
the reference ideal norm. -/
theorem active_full_lengths_with_common_loss (s : CommonSecondKernelLabel ι)
    (Ds : Finset (Ideal O)) (t₁ t₂ H₁ H₂ : ℝ) (z : O) (q : s.FullRetainedFiber)
    (hq : q ∈ s.activeFullRetainedFiber Ds t₁ t₂ H₁ H₂ z)
    (Z A c c₂ d₂ supportLoss clipLoss commonLoss b₁ b₂ : ℝ)
    (hZ : 1 < Z) (hP : ∀ j, 1 ≤ s.input.P j)
    (hvolume : CenteredMomentExceptionalAmplitudePair.volume s.input.toData ≤ Z^A)
    (hC : Z^(c+c₂-commonLoss) ≤ ((s.firstCommon*s.second.val.1).absNorm : ℝ))
    (hD : Z^(c+d₂-commonLoss) ≤ ((s.firstCommon*s.second.val.2).absNorm : ℝ))
    (hsupport : (max 1 s.input.upper)^Fintype.card ι ≤ Z^supportLoss)
    (hclip : Real.logb Z (max 1 b₁*max 1 b₂) ≤ clipLoss) :
    s.fullLeftLength Z q+Real.logb Z (max 1 b₁*max 1 b₂) ≤ A-c-c₂+(supportLoss+clipLoss+commonLoss) ∧
    s.fullRightLength Z q+Real.logb Z (max 1 b₁*max 1 b₂) ≤ A-c-d₂+(supportLoss+clipLoss+commonLoss) := by
  have hh := s.active_full_lengths Ds t₁ t₂ H₁ H₂ z q hq Z A (c-commonLoss) c₂ d₂
    supportLoss clipLoss b₁ b₂ hZ hP hvolume
    (by simpa only [show c-commonLoss+c₂=c+c₂-commonLoss by ring] using hC)
    (by simpa only [show c-commonLoss+d₂=c+d₂-commonLoss by ring] using hD) hsupport hclip
  constructor <;> linarith [hh.1,hh.2]

end CommonSecondKernelLabel
#print axioms CommonSecondKernelLabel.active_full_lengths
#print axioms CommonSecondKernelLabel.active_full_lengths_with_common_loss
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointRetainedLength -/
