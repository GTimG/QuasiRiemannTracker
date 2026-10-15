/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B002
import Submissions.local44_20261013.Bundles.B007
import Submissions.local44_20261013.Bundles.B045
import Submissions.local44_20261013.Bundles.B048
import Submissions.local44_20261013.Bundles.B051
import Submissions.local44_20261013.Bundles.B054
import Submissions.local44_20261013.Bundles.B057
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.CanonicalHighPhysical
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.CappedRequests

/- BEGIN ORIGINAL MODULE Analytic.JointSecondKernel ; sha256 5ad3a8189f2c26d6856be67bd1e0c84a1e025558c3e129350c0e3e055369dea9 -/
section




/-! Common Fourier integration of the literal projected second children.
The two column-window frequencies remain independent and all arithmetic
labels remain in a single paired sum. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion RayFourExpansion CompletedGauss
open CenteredMomentSecondSectorColumns CenteredMomentChildRows
open CenteredMomentHeckeColumnWindow CenteredMomentSmooth CenteredMomentCauchy
open CenteredMomentConjugateWindow CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondWholeKernel CenteredMomentLogDyadic
open CenteredMomentSectorLocalization
open FourierBridge
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentFirstAmplificationChoice CenteredMomentSecondBlockAggregate
open CenteredMomentActiveSource CenteredMomentSecondRetainedAggregate CenteredMomentFirstSectors
open CenteredMomentSourceRow CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentFixedRay
local notation "O" => HeckeFamily.O

/-- Triangle and integration preserve the paired finite sum even when the
two column windows have independent Fourier frequencies. -/
theorem joint_two_integral_pair_bound {κ : Type*} (rows : Finset κ)
    (A B : κ → ℝ → ℂ) (u v : ℝ → ℝ) (E : ℝ)
    (hu : Integrable u) (hv : Integrable v)
    (hA : ∀ k ∈ rows, Integrable (A k)) (hB : ∀ k ∈ rows, Integrable (B k))
    (he : ∀ x y, (∑ k ∈ rows, ‖A k x‖*‖B k y‖) ≤ E*u x*v y) :
    (∑ k ∈ rows, ‖∫ x, A k x‖*‖∫ y, B k y‖) ≤ E*(∫ x, u x)*(∫ y, v y) := by
  have hinner (x : ℝ) :
      (∑ k ∈ rows, ‖A k x‖*‖∫ y, B k y‖) ≤ E*u x*(∫ y, v y) := by
    calc
      _ ≤ ∑ k ∈ rows, ‖A k x‖*(∫ y, ‖B k y‖) :=
        Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left
          (norm_integral_le_integral_norm _) (norm_nonneg _))
      _ = ∫ y, ∑ k ∈ rows, ‖A k x‖*‖B k y‖ := by
        rw [integral_finsetSum _ (fun k hk => (hB k hk).norm.const_mul _)]
        simp only [integral_const_mul]
      _ ≤ ∫ y, E*u x*v y :=
        integral_mono (integrable_finsetSum _ (fun k hk => (hB k hk).norm.const_mul _))
          (hv.const_mul _) (he x)
      _ = _ := integral_const_mul _ _
  calc
    _ ≤ ∑ k ∈ rows, (∫ x, ‖A k x‖)*‖∫ y, B k y‖ :=
      Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_right
        (norm_integral_le_integral_norm _) (norm_nonneg _))
    _ = ∫ x, ∑ k ∈ rows, ‖A k x‖*‖∫ y, B k y‖ := by
      rw [integral_finsetSum _ (fun k hk => (hA k hk).norm.mul_const _)]
      simp only [integral_mul_const]
    _ ≤ ∫ x, E*u x*(∫ y, v y) :=
      integral_mono (integrable_finsetSum _ (fun k hk => (hA k hk).norm.mul_const _))
        ((hu.const_mul E).mul_const _) hinner
    _ = _ := by rw [integral_mul_const, integral_const_mul]

def secondChildValue (η : Character) (t : ℝ) (S : Finset (Ideal O))
    (β : Ideal O → ℂ) (C : Ideal O) (hC : Supported C)
    (A : O) (L : Ideal O) (χ : RayCharacter) (z : O) (H : ℝ) : ℂ :=
  (Real.sqrt H : ℂ)⁻¹ * ∑ I : sectorPool C hC.1 S,
    secondBlockChildCoefficient η t S β C hC A L χ z I

/-- Deleting exactly the zero source coefficients leaves the projected child
unchanged, so the physical active-source domain matches the allocation domain. -/
theorem secondChildValue_active (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (C : Ideal O) (hC : Supported C)
    (A : O) (L : Ideal O) (χ : RayCharacter) (z : O) (H : ℝ) :
    secondChildValue η t (activeSource S β) β C hC A L χ z H =
      secondChildValue η t S β C hC A L χ z H := by
  have hp : supportedColumns (residualPool C hC.1 (activeSource S β)) =
      (supportedColumns (residualPool C hC.1 S)).filter (fun I => β (C*I) ≠ 0) := by
    ext I
    simp only [supportedColumns, Finset.mem_filter, mem_residualPool, mem_activeSource]
    tauto
  simp only [secondChildValue, second_child_sum_eq_source, hp, Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hb : β (C*I) = 0
  · simp [hb]
  · simp [hb]

def secondChildWindow (η : Character) (t : ℝ) (S : Finset (Ideal O))
    (β : Ideal O → ℂ) (C : Ideal O) (hC : Supported C)
    (A : O) (L : Ideal O) (χ : RayCharacter) (z : O)
    (H θ X : ℝ) (V : ℝ → ℂ) : ℂ :=
  (Real.sqrt H : ℂ)⁻¹ * ∑ I : sectorPool C hC.1 S,
    secondBlockChildCoefficient η t S β C hC A L χ z I *
      columnPhase V (Real.log ((I.val.absNorm : ℝ)/X)) θ

theorem second_child_window_integrable (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (C : Ideal O) (hC : Supported C)
    (A : O) (L : Ideal O) (χ : RayCharacter) (z : O) (H θ X : ℝ) (hX : 0 < X)
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) :
    Integrable (fun w : ℝ => columnDensity V hVc hVs w * logPhase (θ-w) (Real.log X) *
      secondChildValue η (t+2*Real.pi*(w-θ)) S β C hC A L χ z H) := by
  have hi (I : sectorPool C hC.1 S) :=
    ((height_column_integrable V hVc hVs (childCharacter η χ) I
      (sectorPool_supported C hC.1 S I).1 t θ X hX).const_mul
      ((Real.sqrt H : ℂ)⁻¹*(if L ∣ (I : Ideal O) then β (C*I) else 0))).mul_const
      (idealRowHom (A*z) I)
  convert integrable_finsetSum Finset.univ (fun I _ => hi I) using 1
  funext w
  simp only [secondChildValue, secondBlockChildCoefficient_eq_ray_row, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  ring

theorem second_child_window_integral (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (C : Ideal O) (hC : Supported C)
    (A : O) (L : Ideal O) (χ : RayCharacter) (z : O) (H θ X : ℝ) (hX : 0 < X)
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) :
    secondChildWindow η t S β C hC A L χ z H θ X V =
      ∫ w : ℝ, columnDensity V hVc hVs w * logPhase (θ-w) (Real.log X) *
        secondChildValue η (t+2*Real.pi*(w-θ)) S β C hC A L χ z H := by
  have hi (I : sectorPool C hC.1 S) :=
    ((height_column_integrable V hVc hVs (childCharacter η χ) I
      (sectorPool_supported C hC.1 S I).1 t θ X hX).const_mul
      ((Real.sqrt H : ℂ)⁻¹*(if L ∣ (I : Ideal O) then β (C*I) else 0))).mul_const
      (idealRowHom (A*z) I)
  calc
    _ = ∑ I : sectorPool C hC.1 S, ∫ w : ℝ,
        ((Real.sqrt H : ℂ)⁻¹*(if L ∣ (I : Ideal O) then β (C*I) else 0)) *
          (columnDensity V hVc hVs w * logPhase (θ-w) (Real.log X) *
            heightCoeff (childCharacter η χ) (t+2*Real.pi*(w-θ)) I) * idealRowHom (A*z) I := by
      simp only [secondChildWindow, Finset.mul_sum, secondBlockChildCoefficient_eq_ray_row]
      apply Finset.sum_congr rfl
      intro I hI
      rw [integral_mul_const, integral_const_mul,
        ← height_column_integral V hVc hVs (childCharacter η χ) I
          (sectorPool_supported C hC.1 S I).1 t θ X hX]
      ring
    _ = _ := by
      rw [← integral_finsetSum _ (fun I _ => hi I)]
      apply integral_congr_ae
      filter_upwards [] with w
      simp only [secondChildValue, secondBlockChildCoefficient_eq_ray_row, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro I hI
      ring

/-- Data of a literal projected second row. No size estimate is a field. -/
structure SecondKernelLabel where
  parent : Character
  columns : Finset (Ideal O)
  beta : Ideal O → ℂ
  C : Ideal O
  D : Ideal O
  hC : Supported C
  hD : Supported D
  hCD : CompletedGauss.primeSupport C = CompletedGauss.primeSupport D
  U : Finset (CommonIndex C D)
  projector : Ideal O
  leftRay : RayCharacter
  rightRay : RayCharacter

namespace SecondKernelLabel

abbrev LeftIndex (s : SecondKernelLabel) := sectorPool s.C s.hC.1 s.columns
abbrev RightIndex (s : SecondKernelLabel) := sectorPool s.D s.hD.1 s.columns

def frequency (s : SecondKernelLabel) : O :=
  commonFrequencyGenerator s.C s.D*nonunitFrequencyGenerator s.C s.D s.U

def leftCoefficient (s : SecondKernelLabel) (t : ℝ) (z : O) (H : ℝ)
    (I : s.LeftIndex) : ℂ :=
  (Real.sqrt H : ℂ)⁻¹ * secondBlockChildCoefficient s.parent t s.columns s.beta
    s.C s.hC s.frequency s.projector s.leftRay z I

def rightCoefficient (s : SecondKernelLabel) (t : ℝ) (z : O) (H : ℝ)
    (I : s.RightIndex) : ℂ :=
  (Real.sqrt H : ℂ)⁻¹ * secondBlockChildCoefficient s.parent t s.columns s.beta
    s.D s.hD s.frequency s.projector (s.rightRay⁻¹) (-z) I

def leftValue (s : SecondKernelLabel) (t : ℝ) (z : O) (H : ℝ) : ℂ :=
  secondChildValue s.parent t s.columns s.beta s.C s.hC s.frequency s.projector s.leftRay z H

def rightValue (s : SecondKernelLabel) (t : ℝ) (z : O) (H : ℝ) : ℂ :=
  secondChildValue s.parent t s.columns s.beta s.D s.hD s.frequency
    s.projector (s.rightRay⁻¹) (-z) H

def leftWindow (s : SecondKernelLabel) (t : ℝ) (z : O) (H θ X : ℝ) : ℂ :=
  secondChildWindow s.parent t s.columns s.beta s.C s.hC s.frequency
    s.projector s.leftRay z H θ X logAnnulus

def rightWindow (s : SecondKernelLabel) (t : ℝ) (z : O) (H θ X : ℝ) : ℂ :=
  secondChildWindow s.parent t s.columns s.beta s.D s.hD s.frequency
    s.projector (s.rightRay⁻¹) (-z) H (-θ) X (fun x => star (logAnnulus x))

theorem leftColumn_eq_window (s : SecondKernelLabel) (t : ℝ) (z : O)
    (H θ X : ℝ) (weight : ℂ) :
    leftColumn Finset.univ (fun I => weight*s.leftCoefficient t z H I) logAnnulus
      (fun I => Real.log ((I.val.absNorm : ℝ)/X)) θ = weight*s.leftWindow t z H θ X := by
  simp only [leftColumn, leftCoefficient, leftWindow, secondChildWindow, Finset.mul_sum, mul_assoc]

theorem rightColumn_eq_window (s : SecondKernelLabel) (t : ℝ) (z : O) (H θ X : ℝ) :
    rightColumn Finset.univ (s.rightCoefficient t z H) logAnnulus
      (fun I => Real.log ((I.val.absNorm : ℝ)/X)) θ = star (s.rightWindow t z H θ X) := by
  simp only [rightColumn, rightCoefficient, rightWindow, secondChildWindow,
    star_mul, star_sum, star_inv₀, Complex.star_def, Complex.conj_ofReal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  have he := star_columnPhase (fun x => star (logAnnulus x))
    (Real.log ((I.val.absNorm : ℝ)/X)) (-θ)
  simp only [star_star, neg_neg] at he
  simp only [Complex.star_def] at he
  rw [he]
  ring

def kernelScale (n : Fin 4 → ℤ) : ℝ :=
  dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))

def kernelRow (s : SecondKernelLabel) (t : ℝ) (z : O)
    (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (n : Fin 4 → ℤ) : ℂ :=
  secondBlockRowPhase s.C s.D s.hC s.hD s.U R z *
    ∑ I : s.LeftIndex, ∑ J : s.RightIndex,
      (s.leftCoefficient t z (dyadicScale (n 2)) I *
        star (s.rightCoefficient t z (dyadicScale (n 3)) J)) *
          secondBlockKernel s.C s.D s.U W K n z I J

/-- Undo precisely the two physical column normalizations. -/
theorem rawRow_eq_scaled (s : SecondKernelLabel) (t : ℝ) (z : O)
    (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (n : Fin 4 → ℤ) :
    secondBlockRowPhase s.C s.D s.hC s.hD s.U R z *
      (∑ I : s.LeftIndex, ∑ J : s.RightIndex,
        (secondBlockChildCoefficient s.parent t s.columns s.beta s.C s.hC s.frequency
            s.projector s.leftRay z I *
          star (secondBlockChildCoefficient s.parent t s.columns s.beta s.D s.hD s.frequency
            s.projector (s.rightRay⁻¹) (-z) J)) *
          secondBlockKernel s.C s.D s.U W K n z I J) =
      (Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3)) : ℂ) *
        s.kernelRow t z W K R n := by
  have h₂ : (Real.sqrt (dyadicScale (n 2)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 (dyadicScale_pos _)))
  have h₃ : (Real.sqrt (dyadicScale (n 3)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 (dyadicScale_pos _)))
  rw [Real.sqrt_mul (dyadicScale_pos _).le, Complex.ofReal_mul]
  simp only [kernelRow, leftCoefficient, rightCoefficient, star_mul, star_inv₀,
    Complex.star_def, Complex.conj_ofReal]
  rw [mul_left_comm (_*_) _]
  congr 1
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  field_simp

end SecondKernelLabel

def projectedSecondKernelLabel (η : Character) (S : Finset (Ideal O))
    (β : Ideal O → ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C = CompletedGauss.primeSupport D)
    (U : Finset (CommonIndex C D)) (L : Ideal O) (χ ξ : RayCharacter) : SecondKernelLabel where
  parent := η
  columns := S
  beta := β
  C := C
  D := D
  hC := hC
  hD := hD
  hCD := hCD
  U := U
  projector := L
  leftRay := χ
  rightRay := ξ

/-- The exact projected second block, normalized by its physical column
dyads. Projectors, rays and retained frequencies all remain in the sum. -/
def projectedSecondKernelSum (η : Character) (t : ℝ) (S : Finset (Ideal O))
    (β : Ideal O → ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C = CompletedGauss.primeSupport D)
    (U : Finset (CommonIndex C D)) (R : ℝ) (rows : Finset O)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4 → ℤ) : ℂ :=
  ∑ L ∈ CenteredMomentMobiusRegroup.divisorPool Finset.univ
      (fun J : sectorPool D hD.1 S => (J : Ideal O)),
    (UniqueFactorizationMonoid.moebius L : ℂ) *
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
        pairCoeff (phaseTable (primaryGenerator C) (primaryGenerator D)) χ ξ *
          ∑ z ∈ rows,
            (projectedSecondKernelLabel η S β C D hC hD hCD U L χ ξ).kernelRow t z W K R n

theorem actualSecondChildren_eq_kernelSum (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C = CompletedGauss.primeSupport D)
    (U : Finset (CommonIndex C D)) (R : ℝ) (rows : Finset O)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4 → ℤ) :
    actualSecondChildren η t S β C D hC hD U R rows W K n =
      (Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3)) : ℂ) *
        projectedSecondKernelSum η t S β C D hC hD hCD U R rows W K n := by
  let f (L : Ideal O) (χ ξ : RayCharacter) (z : O) :=
    (projectedSecondKernelLabel η S β C D hC hD hCD U L χ ξ).kernelRow t z W K R n
  let q : ℂ := Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3))
  calc
    _ = ∑ L ∈ CenteredMomentMobiusRegroup.divisorPool Finset.univ
          (fun J : sectorPool D hD.1 S => (J : Ideal O)),
        (UniqueFactorizationMonoid.moebius L : ℂ) *
          ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
            pairCoeff (phaseTable (primaryGenerator C) (primaryGenerator D)) χ ξ *
              ∑ z ∈ rows, q * f L χ ξ z := by
      unfold actualSecondChildren
      apply Finset.sum_congr rfl
      intro L hL
      congr 1
      apply Finset.sum_congr rfl
      intro χ hχ
      apply Finset.sum_congr rfl
      intro ξ hξ
      congr 1
      apply Finset.sum_congr rfl
      intro z hz
      exact (projectedSecondKernelLabel η S β C D hC hD hCD U L χ ξ).rawRow_eq_scaled
        t z W K R n
    _ = _ := by
      simp only [projectedSecondKernelSum, f, q, Finset.mul_sum,
        mul_assoc, mul_left_comm, mul_comm]


theorem actualSecondChildren_norm_normalized (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C = CompletedGauss.primeSupport D)
    (U : Finset (CommonIndex C D)) (R : ℝ) (rows : Finset O)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4 → ℤ) :
    ‖actualSecondChildren η t S β C D hC hD U R rows W K n‖ /
        Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3)) =
      ‖projectedSecondKernelSum η t S β C D hC hD hCD U R rows W K n‖ := by
  rw [actualSecondChildren_eq_kernelSum η t S β C D hC hD hCD]
  have hs : 0 < Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3)) :=
    Real.sqrt_pos.2 (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  exact mul_div_cancel_left₀ _ hs.ne'

/-- Actual enlarged physical blocks are exactly the normalized joint
kernel sum times the full pre-count scalar. -/
theorem actual_enlarged_secondBlock_kernel (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C = CompletedGauss.primeSupport D)
    (U : Finset (CommonIndex C D)) (R : ℝ) (rows : Finset O)
    (hrows : ∀ z ∈ rows, z ≠ 0) (W : 𝓢(ℝ,ℂ)) (n : Fin 4 → ℤ)
    (Z A c d R₁ E₁ M a omega : ℝ) (hZ : 1 < Z) :
    ‖CenteredMomentSecondPhysicalBlock.physicalBlock η t S β C D hC hD U R rows W
      (Z^(2*A-c-d+R₁+E₁-M+max (d-c) 0+6*a+omega)) n‖/(Z^(A-c)*Z^a) =
      Z^(A-min c d+R₁+E₁-M+5*a+omega+
        Real.logb Z (Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}) : ℝ)-
        Real.logb Z ((∏ Q ∈ U, Q.val).absNorm : ℝ)-
        (Real.logb Z (C.absNorm : ℝ)+Real.logb Z (D.absNorm : ℝ))/2) *
        ‖projectedSecondKernelSum η t S β C D hC hD hCD U R rows W
          (Z^(2*A-c-d+R₁+E₁-M+max (d-c) 0+6*a+omega)) n‖ := by
  rw [actual_enlarged_secondBlock_precount η t S β C D hC hD hCD U R rows hrows W n
    Z A c d R₁ E₁ M a omega hZ,
    actualSecondChildren_norm_normalized η t S β C D hC hD hCD]

theorem joint_second_windows_from_values {κ : Type*} (labels : Finset κ)
    (s : κ → SecondKernelLabel) (t : κ → ℝ) (z : κ → O)
    (H₁ H₂ X₁ X₂ : κ → ℝ) (hX₁ : ∀ k, 0 < X₁ k) (hX₂ : ∀ k, 0 < X₂ k)
    (weight : κ → ℂ) (θ : ℝ) (J₁ J₂ : ℕ) (E : ℝ)
    (he : ∀ u v : ℝ, (∑ k ∈ labels, ‖weight k‖ *
      ‖(s k).leftValue (t k+2*Real.pi*(u-θ)) (z k) (H₁ k)‖ *
      ‖(s k).rightValue (t k+2*Real.pi*(v-(-θ))) (z k) (H₂ k)‖) ≤
        E*(1+‖u‖)^J₁*(1+‖v‖)^J₂) :
    (∑ k ∈ labels, ‖weight k‖ *
      ‖(s k).leftWindow (t k) (z k) (H₁ k) θ (X₁ k)‖ *
      ‖(s k).rightWindow (t k) (z k) (H₂ k) θ (X₂ k)‖) ≤
      E * jointColumnMoment logAnnulus logAnnulus_compact logAnnulus_smooth J₁ *
        jointColumnMoment (fun x => star (logAnnulus x))
          (conjugate_compact logAnnulus logAnnulus_compact)
          (conjugate_smooth logAnnulus logAnnulus_smooth) J₂ := by
  let b := columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth
  let c := columnDensity (fun x => star (logAnnulus x))
    (conjugate_compact logAnnulus logAnnulus_compact)
    (conjugate_smooth logAnnulus logAnnulus_smooth)
  let A : κ → ℝ → ℂ := fun k u => weight k *
    (b u * logPhase (θ-u) (Real.log (X₁ k)) *
      (s k).leftValue (t k+2*Real.pi*(u-θ)) (z k) (H₁ k))
  let B : κ → ℝ → ℂ := fun k v =>
    c v * logPhase (-θ-v) (Real.log (X₂ k)) *
      (s k).rightValue (t k+2*Real.pi*(v-(-θ))) (z k) (H₂ k)
  have hA (k : κ) : Integrable (A k) :=
    (second_child_window_integrable (s k).parent (t k) (s k).columns (s k).beta
      (s k).C (s k).hC (s k).frequency (s k).projector (s k).leftRay (z k)
      (H₁ k) θ (X₁ k) (hX₁ k) logAnnulus logAnnulus_compact logAnnulus_smooth).const_mul _
  have hB (k : κ) : Integrable (B k) :=
    second_child_window_integrable (s k).parent (t k) (s k).columns (s k).beta
      (s k).D (s k).hD (s k).frequency (s k).projector ((s k).rightRay⁻¹) (-(z k))
      (H₂ k) (-θ) (X₂ k) (hX₂ k) (fun x => star (logAnnulus x))
      (conjugate_compact logAnnulus logAnnulus_compact)
      (conjugate_smooth logAnnulus logAnnulus_smooth)
  have hp (u v : ℝ) : (∑ k ∈ labels, ‖A k u‖*‖B k v‖) ≤
      E*((1+‖u‖)^J₁*‖b u‖)*((1+‖v‖)^J₂*‖c v‖) := by
    calc
      _ = (‖b u‖*‖c v‖) * (∑ k ∈ labels, ‖weight k‖ *
          ‖(s k).leftValue (t k+2*Real.pi*(u-θ)) (z k) (H₁ k)‖ *
          ‖(s k).rightValue (t k+2*Real.pi*(v-(-θ))) (z k) (H₂ k)‖) := by
        simp only [A, B, norm_mul, logPhase_norm, mul_one, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ ≤ (‖b u‖*‖c v‖) * (E*(1+‖u‖)^J₁*(1+‖v‖)^J₂) :=
        mul_le_mul_of_nonneg_left (he u v) (by positivity)
      _ = _ := by ring
  have hh := joint_two_integral_pair_bound labels A B
    (fun u => (1+‖u‖)^J₁*‖b u‖) (fun v => (1+‖v‖)^J₂*‖c v‖) E
    (columnDensity_moments logAnnulus logAnnulus_compact logAnnulus_smooth J₁)
    (columnDensity_moments (fun x => star (logAnnulus x))
      (conjugate_compact logAnnulus logAnnulus_compact)
      (conjugate_smooth logAnnulus logAnnulus_smooth) J₂)
    (fun k _ => hA k) (fun k _ => hB k) hp
  have ha (k : κ) : (∫ u, A k u) = weight k*(s k).leftWindow (t k) (z k) (H₁ k) θ (X₁ k) := by
    rw [show A k = (fun u => weight k * (b u * logPhase (θ-u) (Real.log (X₁ k)) *
      (s k).leftValue (t k+2*Real.pi*(u-θ)) (z k) (H₁ k))) from rfl, integral_const_mul]
    exact congrArg (fun q : ℂ => weight k*q)
      (second_child_window_integral (s k).parent (t k) (s k).columns (s k).beta
        (s k).C (s k).hC (s k).frequency (s k).projector (s k).leftRay (z k)
        (H₁ k) θ (X₁ k) (hX₁ k) logAnnulus logAnnulus_compact logAnnulus_smooth).symm
  have hb (k : κ) : (∫ v, B k v) = (s k).rightWindow (t k) (z k) (H₂ k) θ (X₂ k) :=
    (second_child_window_integral (s k).parent (t k) (s k).columns (s k).beta
      (s k).D (s k).hD (s k).frequency (s k).projector ((s k).rightRay⁻¹) (-(z k))
      (H₂ k) (-θ) (X₂ k) (hX₂ k) (fun x => star (logAnnulus x))
      (conjugate_compact logAnnulus logAnnulus_compact)
      (conjugate_smooth logAnnulus logAnnulus_smooth)).symm
  simpa only [ha, hb, norm_mul, jointColumnMoment, b, c] using hh

set_option maxHeartbeats 800000 in
/-- Every outer index may include its entire first label, second common
pair, projector, two rays and reconstructed row. Only their joint window
sum occurs in the input. The Möbius and ray coefficients can stay in weight. -/
theorem joint_second_kernel_from_windows (W : 𝓢(ℝ,ℂ)) (decay J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {κ : Type*} (labels : Finset κ)
      (s : κ → SecondKernelLabel) (t K R : κ → ℝ) (n : κ → Fin 4 → ℤ)
      (z : κ → O) (weight : κ → ℂ) (E : ℝ),
      (∀ θ : ℝ, (∑ k ∈ labels, ‖weight k‖ *
        ‖(s k).leftWindow (t k) (z k) (dyadicScale (n k 2)) θ (dyadicScale (n k 2))‖ *
        ‖(s k).rightWindow (t k) (z k) (dyadicScale (n k 3)) θ (dyadicScale (n k 3))‖) ≤
          E*(1+‖θ‖)^J) →
      ‖∑ k ∈ labels, (((1+SecondKernelLabel.kernelScale (n k))^decay : ℝ) : ℂ) *
        weight k * (s k).kernelRow (t k) (z k) W (K k) (R k) (n k)‖ ≤ C*E := by
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  obtain ⟨C, hC, hc⟩ := whole_kernel_joint_estimate W (fun _ => logAnnulus)
    (fun _ => Real.log 4) (fun _ => hlog)
    (fun _ y hy => abs_le.mpr ⟨(logAnnulus_support hy).1, (logAnnulus_support hy).2.trans hlog⟩)
    decay J
  refine ⟨C, hC, ?_⟩
  intro κ labels s t K R n z weight E he
  have hh := hc labels
    (fun k => (Finset.univ : Finset (s k).LeftIndex))
    (fun k => (Finset.univ : Finset (s k).RightIndex))
    (fun k I => weight k*(s k).leftCoefficient (t k) (z k) (dyadicScale (n k 2)) I)
    (fun k => (s k).rightCoefficient (t k) (z k) (dyadicScale (n k 3)))
    (fun k I => Real.log ((I.val.absNorm : ℝ)/dyadicScale (n k 2)))
    (fun k I => Real.log ((I.val.absNorm : ℝ)/dyadicScale (n k 3)))
    (fun k => SecondKernelLabel.kernelScale (n k))
    (fun k => Real.log (secondEffectiveScale (s k).C (s k).D (s k).frequency (K k)/dyadicScale (n k 0)))
    (fun k => Real.log (normValue (z k)/dyadicScale (n k 1)))
    (fun k => secondBlockRowPhase (s k).C (s k).D (s k).hC (s k).hD (s k).U (R k) (z k))
    (fun k => div_pos (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))
      (mul_pos (dyadicScale_pos _) (dyadicScale_pos _)))
    (fun k _ => secondBlockRowPhase_norm _ _ _ _ (s k).hCD _ _ _)
    (fun k _ => logAnnulus_norm _) (fun k _ => logAnnulus_norm _) E (by
      intro θ
      simp only [SecondKernelLabel.leftColumn_eq_window, SecondKernelLabel.rightColumn_eq_window,
        norm_star, norm_mul]
      exact he θ)
  simpa only [SecondKernelLabel.kernelRow, secondBlockKernel, SecondKernelLabel.kernelScale,
    SecondKernelLabel.frequency, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using hh

set_option maxHeartbeats 800000 in
theorem joint_second_kernel_from_values (W : 𝓢(ℝ,ℂ)) (decay P J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {κ : Type*} (labels : Finset κ)
      (s : κ → SecondKernelLabel) (t K R : κ → ℝ) (n : κ → Fin 4 → ℤ)
      (z : κ → O) (weight : κ → ℂ) (E : ℝ),
      (∀ θ u v : ℝ, (∑ k ∈ labels, ‖weight k‖ *
        ‖(s k).leftValue (t k+2*Real.pi*(u-θ)) (z k) (dyadicScale (n k 2))‖ *
        ‖(s k).rightValue (t k+2*Real.pi*(v-(-θ))) (z k) (dyadicScale (n k 3))‖) ≤
          (E*(1+‖θ‖)^P)*(1+‖u‖)^J₁*(1+‖v‖)^J₂) →
      ‖∑ k ∈ labels, (((1+SecondKernelLabel.kernelScale (n k))^decay : ℝ) : ℂ) *
        weight k * (s k).kernelRow (t k) (z k) W (K k) (R k) (n k)‖ ≤ C*E := by
  let I₁ := jointColumnMoment logAnnulus logAnnulus_compact logAnnulus_smooth J₁
  let I₂ := jointColumnMoment (fun x => star (logAnnulus x))
    (conjugate_compact logAnnulus logAnnulus_compact)
    (conjugate_smooth logAnnulus logAnnulus_smooth) J₂
  have hI₁ : 0 ≤ I₁ := jointColumnMoment_nonneg _ _ _ _
  have hI₂ : 0 ≤ I₂ := jointColumnMoment_nonneg _ _ _ _
  obtain ⟨C, hC, hc⟩ := joint_second_kernel_from_windows W decay P
  refine ⟨C*(I₁*I₂), mul_nonneg hC (mul_nonneg hI₁ hI₂), ?_⟩
  intro κ labels s t K R n z weight E he
  have hw (θ : ℝ) := joint_second_windows_from_values labels s t z
    (fun k => dyadicScale (n k 2)) (fun k => dyadicScale (n k 3))
    (fun k => dyadicScale (n k 2)) (fun k => dyadicScale (n k 3))
    (fun _ => dyadicScale_pos _) (fun _ => dyadicScale_pos _) weight θ J₁ J₂
    (E*(1+‖θ‖)^P) (he θ)
  have hh := hc labels s t K R n z weight (E*(I₁*I₂)) (fun θ =>
    (hw θ).trans_eq (by dsimp only [I₁, I₂]; ring))
  convert hh using 1
  ring

set_option maxHeartbeats 1600000 in
/-- An actual second label of a first common source. The first projector
and the active second common pair are part of the data, not counted apart. -/
structure CommonSecondKernelLabel (ι : Type*) [Fintype ι] where
  input : Input ι
  puncture : Ideal O
  seed : Ideal O
  firstCommon : Ideal O
  firstProjector : Ideal O
  hfirst : Supported firstCommon
  hseed : seed ∣ firstCommon
  parent : Character
  second : ActiveLabel
    (commonSecondColumns (original input puncture seed) firstCommon hfirst)
    (commonSecondBeta (original input puncture seed) firstCommon firstProjector)
  partition : Finset (CommonIndex second.val.1 second.val.2)
  projector : Ideal O
  leftRay : RayCharacter
  rightRay : RayCharacter

namespace CommonSecondKernelLabel
variable {ι : Type*} [Fintype ι]

def toKernelLabel (s : CommonSecondKernelLabel ι) : SecondKernelLabel where
  parent := s.parent
  columns := activeSource
    (commonSecondColumns (original s.input s.puncture s.seed) s.firstCommon s.hfirst)
    (commonSecondBeta (original s.input s.puncture s.seed) s.firstCommon s.firstProjector)
  beta := commonSecondBeta (original s.input s.puncture s.seed) s.firstCommon s.firstProjector
  C := s.second.val.1
  D := s.second.val.2
  hC := (commonLabels_supported (activeSource _ _) _ _ s.second.property).1
  hD := (commonLabels_supported (activeSource _ _) _ _ s.second.property).2
  hCD := (commonLabels_data _ _ _ _ s.second.property).2.2
  U := s.partition
  projector := s.projector
  leftRay := s.leftRay
  rightRay := s.rightRay

theorem toKernelLabel_eq_projected (s : CommonSecondKernelLabel ι) :
    s.toKernelLabel = projectedSecondKernelLabel s.parent
      (activeSource
        (commonSecondColumns (original s.input s.puncture s.seed) s.firstCommon s.hfirst)
        (commonSecondBeta (original s.input s.puncture s.seed) s.firstCommon s.firstProjector))
      (commonSecondBeta (original s.input s.puncture s.seed) s.firstCommon s.firstProjector)
      s.second.val.1 s.second.val.2 s.toKernelLabel.hC s.toKernelLabel.hD
      s.toKernelLabel.hCD s.partition s.projector s.leftRay s.rightRay := rfl

abbrev LeftAllocation (s : CommonSecondKernelLabel ι) :=
  actualAllocations s.input.pools (s.firstCommon*s.second.val.1)

abbrev RightAllocation (s : CommonSecondKernelLabel ι) :=
  actualAllocations s.input.pools (s.firstCommon*s.second.val.2)

variable [DecidableEq ι]

def leftData (s : CommonSecondKernelLabel ι) (B : s.LeftAllocation) (t : ℝ) :=
  secondCommonData s.input (s.firstCommon*s.second.val.1) s.puncture B
    (childCharacter s.parent s.leftRay) s.toKernelLabel.frequency t

def rightData (s : CommonSecondKernelLabel ι) (B : s.RightAllocation) (t : ℝ) :=
  secondCommonData s.input (s.firstCommon*s.second.val.2) s.puncture B
    (childCharacter s.parent (s.rightRay⁻¹)) s.toKernelLabel.frequency t

def leftWeight (s : CommonSecondKernelLabel ι) (B : s.LeftAllocation) (H : ℝ) : ℂ :=
  secondCommonWeightAt s.input (s.firstCommon*s.second.val.1) s.puncture B H

def rightWeight (s : CommonSecondKernelLabel ι) (B : s.RightAllocation) (H : ℝ) : ℂ :=
  secondCommonWeightAt s.input (s.firstCommon*s.second.val.2) s.puncture B H

theorem leftValue_eq_masks (s : CommonSecondKernelLabel ι) (t : ℝ) (z : O) (H : ℝ) :
    s.toKernelLabel.leftValue t z H =
      ∑ B : s.LeftAllocation, s.leftWeight B H *
        secondMaskedValue (s.leftData B t).toSource s.projector z := by
  unfold SecondKernelLabel.leftValue
  rw [show s.toKernelLabel.columns = activeSource
    (commonSecondColumns (original s.input s.puncture s.seed) s.firstCommon s.hfirst)
    (commonSecondBeta (original s.input s.puncture s.seed) s.firstCommon s.firstProjector) from rfl]
  rw [show s.toKernelLabel.beta =
    commonSecondBeta (original s.input s.puncture s.seed) s.firstCommon s.firstProjector from rfl]
  rw [secondChildValue_active]
  exact actual_common_second_child_normalized_at s.input s.puncture s.seed
    s.firstCommon s.firstProjector s.hfirst s.hseed s.second s.toKernelLabel.hC
    s.parent s.toKernelLabel.frequency z t s.projector s.leftRay H

theorem rightValue_eq_masks (s : CommonSecondKernelLabel ι) (t : ℝ) (z : O) (H : ℝ) :
    s.toKernelLabel.rightValue t z H =
      ∑ B : s.RightAllocation, s.rightWeight B H *
        secondMaskedValue (s.rightData B t).toSource s.projector (-z) := by
  unfold SecondKernelLabel.rightValue
  rw [show s.toKernelLabel.columns = activeSource
    (commonSecondColumns (original s.input s.puncture s.seed) s.firstCommon s.hfirst)
    (commonSecondBeta (original s.input s.puncture s.seed) s.firstCommon s.firstProjector) from rfl]
  rw [show s.toKernelLabel.beta =
    commonSecondBeta (original s.input s.puncture s.seed) s.firstCommon s.firstProjector from rfl]
  rw [secondChildValue_active]
  have hh := actual_second_common_first_projector (original s.input s.puncture s.seed)
    s.firstCommon s.firstProjector s.hfirst s.second
  change (Real.sqrt H : ℂ)⁻¹ *
    (∑ I : sectorPool s.second.val.2 s.toKernelLabel.hD.1
      (commonSecondColumns (original s.input s.puncture s.seed) s.firstCommon s.hfirst),
      secondBlockChildCoefficient s.parent t _
        (commonSecondBeta (original s.input s.puncture s.seed) s.firstCommon s.firstProjector)
        s.second.val.2 s.toKernelLabel.hD
        s.toKernelLabel.frequency s.projector (s.rightRay⁻¹) (-z) I) = _
  rw [common_second_child_eq_complete_source (original s.input s.puncture s.seed)
    s.firstCommon s.second.val.2 s.firstProjector s.hfirst s.toKernelLabel.hD hh.2.2.2 hh.2.1]
  exact original_second_child_normalized_at s.input _ s.puncture s.seed
    ((supported_mul_iff _ _).mpr ⟨s.hfirst, s.toKernelLabel.hD⟩)
    (s.hseed.trans (dvd_mul_right _ _)) s.parent s.toKernelLabel.frequency (-z) t
      s.projector (s.rightRay⁻¹) H

/-- All common allocations and all active second-projector allocations
are retained. The expression contains literal X/Y allocated positive rows. -/
def retainedPair (s : CommonSecondKernelLabel ι) (t₁ t₂ : ℝ) (z : O) (H₁ H₂ : ℝ) : ℝ :=
  ∑ B : s.LeftAllocation, ∑ F : s.RightAllocation,
    (‖s.leftWeight B H₁‖*‖s.rightWeight F H₂‖) *
      secondRetainedPairBound (s.leftData B t₁) (s.rightData F t₂) s.projector z (-z)

theorem values_le_retainedPair (s : CommonSecondKernelLabel ι)
    (hL : Squarefree s.projector) (t₁ t₂ : ℝ) (z : O) (H₁ H₂ : ℝ) :
    ‖s.toKernelLabel.leftValue t₁ z H₁‖ * ‖s.toKernelLabel.rightValue t₂ z H₂‖ ≤
      s.retainedPair t₁ t₂ z H₁ H₂ := by
  rw [s.leftValue_eq_masks, s.rightValue_eq_masks]
  calc
    _ ≤ (∑ B : s.LeftAllocation, ‖s.leftWeight B H₁ *
        secondMaskedValue (s.leftData B t₁).toSource s.projector z‖) *
      (∑ F : s.RightAllocation, ‖s.rightWeight F H₂ *
        secondMaskedValue (s.rightData F t₂).toSource s.projector (-z)‖) :=
      mul_le_mul (norm_sum_le _ _) (norm_sum_le _ _) (norm_nonneg _) (by positivity)
    _ = ∑ B : s.LeftAllocation, ∑ F : s.RightAllocation,
        (‖s.leftWeight B H₁‖*‖s.rightWeight F H₂‖) *
          (‖secondMaskedValue (s.leftData B t₁).toSource s.projector z‖ *
            ‖secondMaskedValue (s.rightData F t₂).toSource s.projector (-z)‖) := by
      simp only [norm_mul, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro B hB
      apply Finset.sum_congr rfl
      intro F hF
      ring
    _ ≤ _ := Finset.sum_le_sum (fun B _ => Finset.sum_le_sum (fun F _ =>
      mul_le_mul_of_nonneg_left
        (second_source_masked_pair (s.leftData B t₁) (s.rightData F t₂) s.projector hL z (-z))
        (by positivity)))

end CommonSecondKernelLabel

/-- Concrete source-to-product input for the common second kernel. The
only analytic input is the one joint sum of literal retained products;
all column identities, masks, extraction and Fourier windows are proved. -/
theorem joint_second_kernel_from_retained (W : 𝓢(ℝ,ℂ)) (decay P J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι κ : Type*} [Fintype ι] [DecidableEq ι]
      (labels : Finset κ) (s : κ → CommonSecondKernelLabel ι)
      (t K R : κ → ℝ) (n : κ → Fin 4 → ℤ) (z : κ → O) (weight : κ → ℂ),
      (∀ k ∈ labels, Squarefree (s k).projector) → ∀ E : ℝ,
      (∀ θ u v : ℝ, (∑ k ∈ labels, ‖weight k‖ *
        (s k).retainedPair (t k+2*Real.pi*(u-θ)) (t k+2*Real.pi*(v-(-θ))) (z k)
          (dyadicScale (n k 2)) (dyadicScale (n k 3))) ≤
        (E*(1+‖θ‖)^P)*(1+‖u‖)^J₁*(1+‖v‖)^J₂) →
      ‖∑ k ∈ labels, (((1+SecondKernelLabel.kernelScale (n k))^decay : ℝ) : ℂ) *
        weight k * (s k).toKernelLabel.kernelRow (t k) (z k) W (K k) (R k) (n k)‖ ≤ C*E := by
  obtain ⟨C, hC, hc⟩ := joint_second_kernel_from_values W decay P J₁ J₂
  refine ⟨C, hC, ?_⟩
  intro ι κ instF instD labels s t K R n z weight hL E he
  apply hc labels (fun k => (s k).toKernelLabel) t K R n z weight E
  intro θ u v
  apply (Finset.sum_le_sum (fun k hk => ?_)).trans (he θ u v)
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left
    ((s k).values_le_retainedPair (hL k hk) _ _ _ _ _) (norm_nonneg _)

/-- The actual Möbius scalar automatically removes nonsquarefree
second projectors; no squarefreeness gate is imposed on the source pool. -/
theorem joint_second_kernel_from_moebius_retained (W : 𝓢(ℝ,ℂ)) (decay P J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι κ : Type*} [Fintype ι] [DecidableEq ι]
      (labels : Finset κ) (s : κ → CommonSecondKernelLabel ι)
      (t K R : κ → ℝ) (n : κ → Fin 4 → ℤ) (z : κ → O) (weight : κ → ℂ) (E : ℝ),
      (∀ θ u v : ℝ, (∑ k ∈ labels,
        ‖(UniqueFactorizationMonoid.moebius (s k).projector : ℂ)*weight k‖ *
        (s k).retainedPair (t k+2*Real.pi*(u-θ)) (t k+2*Real.pi*(v-(-θ))) (z k)
          (dyadicScale (n k 2)) (dyadicScale (n k 3))) ≤
        (E*(1+‖θ‖)^P)*(1+‖u‖)^J₁*(1+‖v‖)^J₂) →
      ‖∑ k ∈ labels, (((1+SecondKernelLabel.kernelScale (n k))^decay : ℝ) : ℂ) *
        ((UniqueFactorizationMonoid.moebius (s k).projector : ℂ)*weight k) *
          (s k).toKernelLabel.kernelRow (t k) (z k) W (K k) (R k) (n k)‖ ≤ C*E := by
  obtain ⟨C, hC, hc⟩ := joint_second_kernel_from_values W decay P J₁ J₂
  refine ⟨C, hC, ?_⟩
  intro ι κ instF instD labels s t K R n z weight E he
  apply hc labels (fun k => (s k).toKernelLabel) t K R n z
    (fun k => (UniqueFactorizationMonoid.moebius (s k).projector : ℂ)*weight k) E
  intro θ u v
  apply (Finset.sum_le_sum (fun k hk => ?_)).trans (he θ u v)
  by_cases hm : (UniqueFactorizationMonoid.moebius (s k).projector : ℂ) = 0
  · simp [hm]
  · rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left
      ((s k).values_le_retainedPair
        (CenteredMomentWholeDivisorShell.squarefree_of_moebius_ne_zero _ hm) _ _ _ _ _)
      (norm_nonneg _)

theorem finite_norm_sum_of_unit_phases {κ : Type*} (labels : Finset κ)
    (a : κ → ℂ) (E : ℝ)
    (he : ∀ phase : κ → ℂ, (∀ k, ‖phase k‖ = 1) →
      ‖∑ k ∈ labels, phase k*a k‖ ≤ E) :
    (∑ k ∈ labels, ‖a k‖) ≤ E := by
  choose phase hp heq using (fun k => Complex.exists_norm_eq_mul_self (a k))
  calc
    _ = ‖∑ k ∈ labels, (‖a k‖ : ℂ)‖ := by
      rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Finset.sum_nonneg (fun k _ => norm_nonneg (a k)))]
    _ = ‖∑ k ∈ labels, phase k*a k‖ := by
      congr 1
      exact Finset.sum_congr rfl (fun k _ => heq k)
    _ ≤ E := he phase hp

/-- Triangle over physical blocks and retained rows also preserves the
joint sum: unit phases absorb each summand's argument for free. -/
theorem joint_second_kernel_norm_sum_from_moebius_retained
    (W : 𝓢(ℝ,ℂ)) (decay P J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι κ : Type*} [Fintype ι] [DecidableEq ι]
      (labels : Finset κ) (s : κ → CommonSecondKernelLabel ι)
      (t K R : κ → ℝ) (n : κ → Fin 4 → ℤ) (z : κ → O) (weight : κ → ℂ) (E : ℝ),
      (∀ θ u v : ℝ, (∑ k ∈ labels,
        ‖(UniqueFactorizationMonoid.moebius (s k).projector : ℂ)*weight k‖ *
        (s k).retainedPair (t k+2*Real.pi*(u-θ)) (t k+2*Real.pi*(v-(-θ))) (z k)
          (dyadicScale (n k 2)) (dyadicScale (n k 3))) ≤
        (E*(1+‖θ‖)^P)*(1+‖u‖)^J₁*(1+‖v‖)^J₂) →
      (∑ k ∈ labels,
        ‖(((1+SecondKernelLabel.kernelScale (n k))^decay : ℝ) : ℂ) *
          ((UniqueFactorizationMonoid.moebius (s k).projector : ℂ)*weight k) *
            (s k).toKernelLabel.kernelRow (t k) (z k) W (K k) (R k) (n k)‖) ≤ C*E := by
  obtain ⟨C, hC, hc⟩ := joint_second_kernel_from_moebius_retained W decay P J₁ J₂
  refine ⟨C, hC, ?_⟩
  intro ι κ instF instD labels s t K R n z weight E he
  apply finite_norm_sum_of_unit_phases
  intro phase hp
  have hh := hc labels s t K R n z (fun k => phase k*weight k) E (by
    intro θ u v
    simpa only [norm_mul, hp, one_mul] using he θ u v)
  convert hh using 1 <;>
    simp only [mul_assoc, mul_left_comm, mul_comm]

#print axioms actualSecondChildren_eq_kernelSum
#print axioms actual_enlarged_secondBlock_kernel
#print axioms joint_two_integral_pair_bound
#print axioms second_child_window_integral
#print axioms joint_second_kernel_from_windows
#print axioms joint_second_kernel_from_values
#print axioms joint_second_kernel_from_retained
#print axioms joint_second_kernel_from_moebius_retained
#print axioms joint_second_kernel_norm_sum_from_moebius_retained
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointSecondKernel -/

/- BEGIN ORIGINAL MODULE Analytic.JointSurvivingHighProduct ; sha256 b150207ef0128cd392cd61ac0c5e4294c413321060d8630f9b29941a417ba085 -/
section



/-! Paired high-bin summation with independently varying surviving subsets.
The original slot system remains fixed before all arithmetic labels. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff
open Set
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification HeckeDetectorZeros CanonicalQuadraticSieve
open IdealMobiusDivisorSum LocalMoment ProbeHighRowFamily ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

structure SurvivingBufferedData (η : Character) (w : NonzeroElement)
    (Slot : Type*) [Fintype Slot] [DecidableEq Slot] (orders : Finset Slot → ℕ)
    (profileBound : ℕ → ℝ) (a e : ℝ) where
  slots : Finset Slot
  data : JointBufferedProductData η w slots (orders slots) profileBound a e

namespace SurvivingBufferedData
variable {η : Character} {w : NonzeroElement} {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
  {orders : Finset Slot → ℕ} {profileBound : ℕ → ℝ} {a e : ℝ}

def length (D : SurvivingBufferedData η w Slot orders profileBound a e) : ℝ := D.data.length

def value (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (η₀ : Slot → Character) (V : Slot → ℝ → ℂ) (B : Slot → ℝ) (Z d : ℝ)
    (D : SurvivingBufferedData η w Slot orders profileBound a e) : ℂ :=
  D.data.value M H (fun j : D.slots => η₀ j.val) (fun j : D.slots => V j.val)
    (fun j : D.slots => B j.val) Z d

def Admissible (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (η₀ : Slot → Character)
    (A B : Slot → ℝ) (Rwidth τ ηaux σmin σmax Z d T : ℝ)
    (D : SurvivingBufferedData η w Slot orders profileBound a e) : Prop :=
  D.data.Admissible M H hH (fun j : D.slots => η₀ j.val) (fun j : D.slots => A j.val)
    (fun j : D.slots => B j.val) Rwidth τ ηaux σmin σmax Z d T

end SurvivingBufferedData

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

/-- The paired norm product over one actual joint high bin. Both factors
have the same reconstructed row, with their own fixed ray parent, literal
puncture and independent plain profiles. Their lengths are averaged only
after the source squared estimates, giving `A-c-b₂` exactly. -/
theorem actual_joint_surviving_high_product
    (V : Slot → ℝ → ℂ) (Aprofile Bprofile : Slot → ℝ) (hA : ∀ j, 0 < Aprofile j)
    (hVs : ∀ j, Function.support (V j) ⊆ Icc (Aprofile j) (Bprofile j))
    (hV : ∀ j, ContDiff ℝ ∞ (V j))
    (Rwidth dmax ε e κ ηaux σmin σmax productLoss populationLoss loss B : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hκone : κ ≤ 1) (hη : 0 ≤ ηaux)
    (hbudget : 12*e*(Rwidth+2)+8*κ+2*ηaux ≤ ε)
    (hprimebudget : 8*e*Rwidth+κ ≤ ε)
    (hproductLoss : (2+2*(Fintype.card Slot : ℝ))*ε ≤ productLoss)
    (hpopulationLoss : 0 < populationLoss) (hB : 0 ≤ B)
    (hloss : populationLoss+dmax*productLoss ≤ loss)
    (profileBound : ℕ → ℝ) (hprofile : ∀ k, 0 ≤ profileBound k) :
    ∃ J : ℕ, ∀ τ : ℝ, 0 < τ →
    ∃ (orders : Finset Slot → ℕ) (N : ℕ) (C : ℝ), (∀ I, orders I ≤ N) ∧ 0 < C ∧
      ∀ (Z d P W : ℝ), 1 < Z → 0 ≤ d → d ≤ dmax → 2 ≤ Z^d → 2 < Z^τ →
      P ≤ B → W ≤ B →
      ∀ (p : DensityWindow), p.upper < p.lower+2*e →
      ∀ (unit : JointReconstructionLabel → Oˣ) (S : Finset JointReconstructionLabel)
        (w : JointReconstructionLabel → NonzeroElement),
      (∀ v ∈ S, (w v).val = v.row (unit v)) →
      ∀ (R : JointReconstructionLabel →
        JointRelativeLabel η (Option (Slot × RayQuotient.Characters M H)) → Ideal O)
        (hR : ∀ v label, R v label ≠ 0),
      (∀ v ∈ S, Supported v.C₁ ∧ Supported v.D₁ ∧ Supported v.C₂ ∧ Supported v.D₂) →
      (∀ v ∈ S, primeSupport v.C₁ = primeSupport v.D₁ ∧
        primeSupport v.C₂ = primeSupport v.D₂) →
      (∀ v ∈ S, Squarefree v.L ∧ v.L ∣ v.C₂ ∧ v.L ∣ v.D₂) →
      (∀ v ∈ S, jointRelativeSourceZeroBin η (relativeSlotTranslate M H hH η₀) Q hQ72
        (relativeSlotTranslate_fixedQ M H hH η₀ Q hQM hQη₀) (R v) (hR v)
        p.lower p.upper p.height (w v)) →
      (∀ v ∈ S, (Ideal.absNorm v.C₁ : ℝ) ≤ Z^B ∧
        (Ideal.absNorm v.D₁ : ℝ) ≤ Z^B ∧
        (Ideal.absNorm v.C₂ : ℝ) ≤ Z^B ∧ (Ideal.absNorm v.D₂ : ℝ) ≤ Z^B) →
      (∀ v ∈ S, (Ideal.absNorm (Ideal.span {(w v).val}) : ℝ) ≤ Z^W) →
      (∀ v ∈ S, (Ideal.absNorm (jointMissingRadical v.C₁ (w v).val) : ℝ) ≤ Z^P) →
      ∀ (DL DR : ∀ v, SurvivingBufferedData η (w v) Slot orders profileBound p.lower e),
      (∀ v ∈ S, (DL v).Admissible M H hH η₀ Aprofile Bprofile
        Rwidth τ ηaux σmin σmax Z d p.height) →
      (∀ v ∈ S, (DR v).Admissible M H hH η₀ Aprofile Bprofile
        Rwidth τ ηaux σmin σmax Z d p.height) →
      ∀ A c c₂ d₂ b₂ : ℝ, 2*b₂ = c₂+d₂ →
      (∀ v ∈ S, d*(DL v).length ≤ A-c-c₂) →
      (∀ v ∈ S, d*(DR v).length ≤ A-c-d₂) →
      (∑ v ∈ S, ‖(DL v).value M H η₀ V Bprofile Z d‖ *
        ‖(DR v).value M H η₀ V Bprofile Z d‖) ≤
        C*(1+|p.height|)^J *
          Z^(unmarkedDensity (2*p.lower-1)*W+P+(2*p.lower-1)*(A-c-b₂)+loss) := by
  obtain ⟨J,K,hK,hcount⟩ := actual_joint_natural_population η
    (relativeSlotTranslate M H hH η₀) Q hQtop hQ72 hQη
    (relativeSlotTranslate_fixedQ M H hH η₀ Q hQM hQη₀) hβ M H hH S₀
    φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB hβupper
    B populationLoss hB hpopulationLoss
  refine ⟨J,?_⟩
  intro τ hτ
  obtain ⟨orders,N,Cp,horders,hCp,hpoint⟩ := actual_subset_buffered_bound M H hH η η₀ Q hQ72 hQM hQη₀
    V Aprofile Bprofile hA hVs hV Rwidth dmax τ ε e κ ηaux σmin σmax productLoss
    hRw hdmax hτ hε he he' hκ hκone hη hbudget hprimebudget hproductLoss profileBound hprofile
  refine ⟨orders,N,K*Cp,horders,mul_pos hK hCp,?_⟩
  intro Z d P W hZ hd hdmax' hbase hT hPB hWB p hp unit S w hw R hR
    hsup heq hproj hbin hnorm hNw hNr DL DR hDL hDR A c c₂ d₂ b₂ hb₂ hlenL hlenR
  have hcount' : (S.card : ℝ) ≤
      K*(1+|p.height|)^J*Z^(unmarkedDensity (2*p.lower-1)*W+P+populationLoss) := by
    apply hcount Z P W hZ hPB hWB p unit S R hR hsup heq hproj _ hnorm
    · intro v hv
      simpa only [← hw v hv] using hNw v hv
    · intro v hv
      simpa only [← hw v hv] using hNr v hv
    · intro v hv
      have hrow : v.row (unit v) ≠ 0 := by rw [← hw v hv]; exact (w v).property
      refine ⟨hrow,?_⟩
      have hweq : (⟨v.row (unit v),hrow⟩ : NonzeroElement) = w v :=
        Subtype.ext (hw v hv).symm
      rw [hweq]
      exact hbin v hv
  have hploss : 0 ≤ productLoss := by
    have hcard : (0 : ℝ) ≤ (Fintype.card Slot : ℝ) := by positivity
    have hpos : 0 ≤ (2+2*(Fintype.card Slot : ℝ))*ε := mul_nonneg (by positivity) hε.le
    exact hpos.trans hproductLoss
  have hδ : 0 ≤ 2*p.lower-1 := by linarith [p.lower_bound]
  have hpair (v : JointReconstructionLabel) (hv : v ∈ S) :
      ‖(DL v).value M H η₀ V Bprofile Z d‖ * ‖(DR v).value M H η₀ V Bprofile Z d‖ ≤
      Cp*Z^((2*p.lower-1)*(A-c-b₂)+dmax*productLoss) := by
    have hleft := squared_bound_change_base Z d dmax (2*p.lower-1) (DL v).length
      (A-c-c₂) productLoss Cp _ hZ.le hδ hdmax' hploss (hlenL v hv) hCp.le
      (hpoint Z d hZ.le hd hdmax' hbase hT p hp (w v) (R v) (hR v) (hbin v hv) (DL v).slots (DL v).data (hDL v hv))
    have hright := squared_bound_change_base Z d dmax (2*p.lower-1) (DR v).length
      (A-c-d₂) productLoss Cp _ hZ.le hδ hdmax' hploss (hlenR v hv) hCp.le
      (hpoint Z d hZ.le hd hdmax' hbase hT p hp (w v) (R v) (hR v) (hbin v hv) (DR v).slots (DR v).data (hDR v hv))
    have he : ((2*p.lower-1)*(A-c-c₂)+dmax*productLoss+
        ((2*p.lower-1)*(A-c-d₂)+dmax*productLoss))/2 =
        (2*p.lower-1)*(A-c-b₂)+dmax*productLoss := by nlinarith [hb₂]
    simpa only [he,SurvivingBufferedData.value] using norm_pair_of_squared_bounds Z Cp _ _ _ _
      (zero_lt_one.trans hZ) hCp.le hleft hright
  calc
    (∑ v ∈ S, ‖(DL v).value M H η₀ V Bprofile Z d‖ *
        ‖(DR v).value M H η₀ V Bprofile Z d‖) ≤
        (S.card : ℝ)*(Cp*Z^((2*p.lower-1)*(A-c-b₂)+dmax*productLoss)) := by
      simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hpair
    _ ≤ (K*(1+|p.height|)^J*Z^(unmarkedDensity (2*p.lower-1)*W+P+populationLoss))*
        (Cp*Z^((2*p.lower-1)*(A-c-b₂)+dmax*productLoss)) :=
      mul_le_mul_of_nonneg_right hcount' (by positivity)
    _ = (K*Cp)*(1+|p.height|)^J *
        Z^(unmarkedDensity (2*p.lower-1)*W+P+(2*p.lower-1)*(A-c-b₂)+
          (populationLoss+dmax*productLoss)) := by
      rw [show unmarkedDensity (2*p.lower-1)*W+P+(2*p.lower-1)*(A-c-b₂)+
          (populationLoss+dmax*productLoss) =
          (unmarkedDensity (2*p.lower-1)*W+P+populationLoss)+
          ((2*p.lower-1)*(A-c-b₂)+dmax*productLoss) by ring]
      simp only [Real.rpow_add (zero_lt_one.trans hZ)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)) (by positivity)

end FixedData
#print axioms actual_joint_surviving_high_product
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointSurvivingHighProduct -/

/- BEGIN ORIGINAL MODULE Cycle25.Energy.CappedLowStage ; sha256 258a0db5b575e49eceed07a9191d43b578508e1ee73d25aaa3b47598ce0db953 -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/CappedLowStage.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.Cycle25CenteredMomentEnergyCappedLowStage
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthInduction
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyStageReserveSchedule CenteredMomentEnergyStageMargins
open CenteredMomentEnergyBandMonotonicity CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyCappedRequests CenteredMomentEnergySourceCapSchedule
open CenteredMomentNaturalFixedRaySource
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem actual_capped_low
    (W:ℝ→ℂ)(aslot bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (hW:ContDiff ℝ ∞ W)(haslot:0< aslot)
    (hWs:Function.support W⊆Set.Icc aslot bslot)(hbslot:0≤ bslot)
    (ha:0< a)(hb:0≤ b)(hrad:2≤ radial)(hmask:0≤ Bmask)(hMcap:0≤ Mcap)
    (hκ:(7/10:ℝ)≤κ)(hε:0<ε)(hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκbeta:2*HeckeZeroSupremum.beta-1≤κ)(k:ℕ)(hk:k< count Mcap ε)
    (hold:CenteredMomentEnergyCappedWidthInduction.CertifiedBand (α:=α) M H hH
      W bslot a b radial Bmask L lo hi Mcap κ ε k):
    ∃U:Finset (ℕ×ℕ),∃J:ℕ,∀η₀:Character,∀Q:Ideal O,Q≤ M→
      internalQ Q η₀≠0→internalQ Q η₀≠⊤→internalQ Q η₀≤ Ideal.span {(72:O)}→
      ∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧
        PositiveLowAt (α:=α) M H hH W bslot (lowerAt a b Mcap ε (k+1)) b radial Bmask
          (requestLength Mcap Bmask (lengthAt Mcap Bmask L ε (k+1)))
          (fineMesh Mcap Bmask L κ ε) lo hi
          (bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε (k+1))
          (physicalLoss Mcap (finalSourceCap Mcap Bmask L ε) ε k) κ Z η₀ Q J U C ∧
        ZeroLowAt (internalQ Q η₀) (lowerAt a b Mcap ε (k+1)) b radial Bmask
          (requestLength Mcap Bmask (lengthAt Mcap Bmask L ε (k+1)))
          (bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε (k+1))
          (physicalLoss Mcap (finalSourceCap Mcap Bmask L ε) ε k) Z J U C :=by
  let Bs:=finalSourceCap Mcap Bmask L ε
  let Ag:=2*range Mcap Bmask L (count Mcap ε)+Mcap+1
  let Mp:=bandWidth Mcap Bs ε (k+1)
  let Mc:=bandWidth Mcap Bs ε k
  let Lreq:=requestLength Mcap Bmask (lengthAt Mcap Bmask L ε (k+1))
  have hBs:0≤ Bs:=sourceCap_nonneg Mcap Bmask L hMcap hmask _
  have hRange:=range_nonneg Mcap Bmask L hMcap hmask (count Mcap ε)
  have hAg:0≤ Ag:=by dsimp [Ag];positivity
  have hMp:0≤ Mp:=bandWidth_nonneg Mcap Bs ε hMcap hBs hε (k+1)
  have hMc:0≤ Mc:=bandWidth_nonneg Mcap Bs ε hMcap hBs hε k
  have hMpCap:Mp≤ Mcap:=bandWidth_le Mcap Bs ε (k+1)
  have hMpAg:Mp≤ Ag:=by dsimp [Ag];linarith
  have hLnext:0≤ lengthAt Mcap Bmask L ε (k+1):=
    range_nonneg Mcap Bmask L hMcap hmask _
  have hLreq:0≤ Lreq:=(request_bounds Mcap Bmask _ hMcap hmask hLnext).1
  have hκ0:0≤κ:=by linarith
  have hbounds:=bounds Mcap Bs κ ε hMcap hBs hκ0 hε
  have hmesh:0≤ fineMesh Mcap Bmask L κ ε:=hbounds.2.2.2.2.1.le
  have hr:0< reserve Mcap Bs ε:=hbounds.2.2.2.1
  have hr4:reserve Mcap Bs ε/4≤1:=by
    have hh:reserve Mcap Bs ε≤ amplification ε/100:=min_le_left _ _
    have hs:=hbounds.2.1
    linarith
  have hready:CenteredMomentEnergyFirstLiveAdmission.readyBudget Ag Bmask≤ Bs:=
    readyBudget_le_schedule Mcap Bmask L ε Ag Bmask hMcap hmask le_rfl le_rfl
  have hdrop:Mp-amplification ε/2≤ Mc:=parent_drop Mcap Bs ε hε k
  have hlength:2*max Lreq Mp+reserve Mcap Bs ε/4≤ lengthAt Mcap Bmask L ε k:=
    previous_admits Mcap Bmask L ε Mp (reserve Mcap Bs ε/4) hMcap hmask hMpCap hr4 k hk
  have hsupport:=child_support a b Mcap ε k hk
  obtain ⟨degree,S,hold⟩:=hold
  obtain ⟨U,J,hstage⟩:=Cycle25CenteredMomentEnergyNaturalLowStage.actual_low_from_bands
    (α:=α) M H hH W hW aslot bslot lo hi (lowerAt a b Mcap ε (k+1)) b radial
    haslot hWs hbslot (lowerAt_pos a b Mcap ε ha (k+1)) hb hrad
    Mcap Ag Bs Bmask Mp Mc Lreq (fineMesh Mcap Bmask L κ ε) κ ε k
    hMcap hAg hBs hmask hMp hMc hLreq hmesh hMpAg hready hκ hbeta hκbeta hε
    le_rfl hdrop degree S
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cz,Cp,hCz,hCp,hold⟩:=hold η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cs,hCs,hstage⟩:=hstage η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cs*(Cz+Cp+1),by positivity,?_⟩
  filter_upwards [hold,hstage] with Z hold hs
  have hz:=hold.2.1
  have hp:=hold.2.2
  rw [hsupport] at hz hp
  have hz':ZeroAt (internalQ Q η₀) (lowerAt a b Mcap ε (k+1)/max 1 b) b radial Bmask
      (2*max Lreq Mp+reserve Mcap Bs ε/4) Mc (stageLoss Mcap Bs ε k) Z degree S Cz:=
    zeroAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
      degree degree S S Cz Cz hold.1.le le_rfl le_rfl le_rfl le_rfl hlength le_rfl le_rfl
      le_rfl (Finset.Subset.refl _) hCz.le le_rfl hz
  have hp':PositiveAt (α:=α) M H hH W bslot (lowerAt a b Mcap ε (k+1)/max 1 b) b radial Bmask
      (2*max Lreq Mp+reserve Mcap Bs ε/4) (fineMesh Mcap Bmask L κ ε) lo hi Mc
      (stageLoss Mcap Bs ε k) κ Z η₀ Q degree S Cp:=
    positiveAt_transport (α:=α) M H hH W bslot _ _ _ _ _ _ _ _ _ _ κ Z
      _ _ _ _ _ _ _ η₀ Q degree degree S S Cp Cp hold.1.le
      le_rfl le_rfl le_rfl le_rfl hlength le_rfl le_rfl le_rfl (Finset.Subset.refl _)
      hCp.le le_rfl hp
  exact ⟨hs.1,hs.2 (stageLoss Mcap Bs ε k) Cz Cp le_rfl hCz.le hCp.le hz' hp'⟩

end SevenEighths.Cycle25CenteredMomentEnergyCappedLowStage

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Energy.CappedLowStage -/

/- BEGIN ORIGINAL MODULE Cycle25.Energy.PositiveHighPhysical ; sha256 8a849b031342e30a6d0a0ac1378ea890ee914aac5174b6e358c118ea1c6efa36 -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/PositiveHighPhysical.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/








namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.Cycle25CenteredMomentEnergyPositiveHighPhysical
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
open Cycle25CenteredMomentEnergyPositiveHighSource Cycle25CenteredMomentEnergyPositiveHighSourceBound
open Cycle25CenteredMomentEnergyPositiveHighParameters Cycle25CenteredMomentEnergyPositiveBalancedAdmission
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyStageMargins Cycle25CenteredMomentEnergyFirstSourceParameters
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergyNaturalInputMatches
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem actual_positive_high_physical
    (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(aslot bslot lo hi a b bΦ:ℝ)
    (haslot:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤ bslot)(ha:0< a)(hb:0≤ b)
    (Mglobal A B Bmask Mparent Mchild Lgoal Lslot rho κ ε:ℝ)(k:ℕ)
    (hMg:0≤ Mglobal)(hA:0≤ A)(hB:0≤ B)(hBm:0≤ Bmask)
    (_hMp:0≤ Mparent)(hMc:0≤ Mchild)(hL:0≤ Lgoal)(hLs:0≤ Lslot)
    (hMA:Mparent≤ A)(hready:readyBudget A Bmask≤ B)
    (hκ:(7/10:ℝ)≤κ)(hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκbeta:2*HeckeZeroSupremum.beta-1≤κ)(hε:0<ε)
    (hslot:Lslot≤ mesh Mglobal B κ ε)
    (hdrop:Mparent-amplification ε/2≤ Mchild)
    (Ψ:(T:Finset α)→𝓢(ℝ,ℂ))(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃U:Finset (ℕ×ℕ),∃J:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤ M→internalQ Q η₀≠0→internalQ Q η₀≠⊤→
      internalQ Q η₀≤ Ideal.span {(72:O)}→
    ∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧
    ∀εchild C₀ C₁:ℝ,εchild≤ stageLoss Mglobal B ε k→0≤ C₀→0≤ C₁→
      ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 (max Lgoal Mparent)
        Mchild εchild Z degree S C₀→
      PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 (max Lgoal Mparent)
        Lslot lo hi Mchild εchild κ Z η₀ Q degree S C₁→
      PhysicalHighAt (α:=α) M H hH W hW.continuous aslot bslot lo hi haslot hWs
        a b bΦ Bmask Lgoal Lslot rho Mparent κ (reserve Mglobal B ε/4)
        (physicalLoss Mglobal B ε k) Z ha Ψ η₀ Q U J (C*(C₀+C₁+1)) := by
  let r:=reserve Mglobal B ε
  let N:=Fintype.card α
  let Mslot:=profileBound W hW.continuous aslot bslot lo hi haslot hWs
  let a0:=CenteredMomentSecondInputCapacitySource.lowerFactor N aslot a
  let lp:=(min 1 aslot)^N*a*a
  have hMslot:1≤ Mslot:=profileBound_ge_one W hW.continuous aslot bslot lo hi haslot hWs
  have ha0:0< a0:=CenteredMomentSecondInputCapacitySource.lowerFactor_pos N aslot a haslot ha
  have hlp:0< lp:=by dsimp [lp];positivity
  obtain ⟨hsigma,hsigma1,hr,hxi,hxi1,hes,hes1,hem,hmesh,hmesheta,heta,hetastrict,_,_⟩:=
    parameter_gates Mglobal A B κ ε hMg hA hB hκ hε
  have hrpos:0< r/4:=hr
  have hκsmall:(1/6:ℝ)≤κ:=by linarith
  have hLphys:0≤ max Lgoal Mparent:=hL.trans (le_max_left _ _)
  obtain ⟨U,J,hphysical⟩:=CenteredMomentEnergyCanonicalHighPhysical.actual_high_physical (α:=α)
    M H hH W aslot bslot Mchild Lslot (r/4) lo hi κ a b Mslot (maskEpsilon Mglobal B ε)
    (zero_le_one.trans hMslot) hem ha hb (max Lgoal Mparent) hLphys degree S haslot hWs hW hMc hLs hr
    hκsmall hbeta hκbeta N aslot (max 1 bslot) a0 (r/4) haslot (le_max_left _ _) ha0 hr
    (fun _=> aslot) (fun _=> bslot) (fun _=> hbslot)
    (sourceEpsilon Mglobal A B ε) (r/4) (r/4) (A+1) (r/4) (2*amplification ε+1)
    hes hr hr hr (amplification ε) hsigma hxi A Bmask (amplification ε/12) (r/4) (r/4)
    hA hBm hetastrict hr hsigma1 hxi1 hr hes1 le_rfl Ψ (r/4) lp hr hlp
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,Z₀,hZ₀,hbound⟩:=hphysical η₀ Q hQM hQ0 hQt hQ72
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop Z₀,
    eventually_actual_four_fit Mglobal A Bmask B κ ε hMg hA hBm hB hready hκ hε,
    (Filter.tendsto_atTop.1 (tendsto_rpow_atTop (by linarith : 0<2*(r/4)))) (max 1 b*max 1 b)]
    with Z hZZ hfit hclipPow
  have hZ:1< Z:=hZ₀.trans_le hZZ
  have hclip:Real.logb Z (max 1 b*max 1 b)≤2*(r/4):=by
    have hh:=Real.logb_le_logb_of_le hZ (by positivity:0< max 1 b*max 1 b) hclipPow
    simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh
  refine ⟨hZ,?_⟩
  intro εchild C₀ C₁ hell hC₀ hC₁ hzero hpos
    T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hrho hstate
    p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcapacity hlarge
  dsimp only
  intro hfour
  let inp:=balancedInput M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂
  have hN:Fintype.card T≤ N:=Fintype.card_le_of_injective (fun i:T=> i.val) Subtype.val_injective
  have hm:=balanced_matches M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂
  have hu:=four_upper_scales M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂ κ (max Lgoal Mparent)
    hZ hw hκ hcapacity (hstate.trans (le_max_right _ _))
  have hp:=fixed_lower_product M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂ N hN
  have hr:=CenteredMomentEnergyNaturalSourceAdmission.radial_admission state
  have hwidth:=actual_width_le state hZ
  have hh:=hbound T θ Z hZZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height (mesh Mglobal B κ ε)
    hmesh.le hw (fun i=>(hwL i).trans hslot)
    (fun i=>((hwL i).trans hslot).trans hmesheta) hwL hσlo hσhi hheight hfreq
    inp hm (fun _=> le_rfl) (fun _=> le_rfl) (fun _=> rfl) (fun _=> rfl) hN le_rfl (le_max_right _ _)
    hb hb (le_max_right _ _) (le_max_right _ _) hp.2 state.puncture 1 state.puncture_ne_zero
    state.puncture_bound (by simp) (by simp) state.radial.scale hr.1 p rfl rfl
    hu.1 hu.2.1 hu.2.2.1 hu.2.2.2 state.width state.width (r/4) (columnLoss Mglobal B ε k)
    hrpos.le (hstate.trans hMA) hcapacity hwidth hwidth (by linarith only [hstate,hdrop])
    hclip le_rfl le_rfl hfour.1 hfour.2.1 hfour.2.2.1 hfour.2.2.2 (hfit.2 k εchild hell)
  have hcost:state.width+columnLoss Mglobal B ε k+r/4=state.width+physicalLoss Mglobal B ε k:=by
    rw [add_assoc]
    exact congrArg (state.width+·) (columnLoss_physical Mglobal B ε k)
  rw [hcost] at hh
  have ht:inp.t=t:=rfl
  rw [ht] at hh
  dsimp only [inp,r] at hh
  have hN1:((1:Ideal O).absNorm:ℝ)=1:=by norm_num
  simpa only [hN1,div_one,mul_assoc] using hh

end SevenEighths.Cycle25CenteredMomentEnergyPositiveHighPhysical

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Energy.PositiveHighPhysical -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.BoxReconstruction ; sha256 0c088bc1f8e5d45d7e6c984dfce0966895338b81ecaec1d96a51ec420529a4d3 -/
section



/-! Exact finite normalized dilation decomposition of the reconstructed numerator. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators Classical ContDiff
namespace Cycle25.Numerator
open Cycle25.Weighted Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O

def normalizedBox {κ : Type*} (U xi : ℝ) (n j : ℕ) (rho M : ℝ)
    (t : κ → ℝ) (f : κ → ℂ) : ℂ :=
  ((U^(rho*((j : ℝ)*xi))/M : ℝ) : ℂ) * ∑' e, boxSeriesTerm U xi n j t f e

theorem normalized_box_reconstruction {κ : Type*} (U xi : ℝ) (n : ℕ)
    (rho M : ℝ) (hU : 0 < U) (hM : M ≠ 0)
    (t : κ → ℝ) (f : κ → ℂ) (hf : Summable (fun e => ‖f e‖)) :
    (∑' e, f e) = ∑ j ∈ Finset.range (n+1),
      ((M*U^(-rho*((j : ℝ)*xi)) : ℝ) : ℂ) * normalizedBox U xi n j rho M t f := by
  rw [tsum_box_decomposition U xi n t f hf]
  apply Finset.sum_congr rfl
  intro j hj
  unfold normalizedBox
  rw [←mul_assoc,←Complex.ofReal_mul]
  have he : M*U^(-rho*((j : ℝ)*xi))*(U^(rho*((j : ℝ)*xi))/M) = 1 := by
    rw [show M*U^(-rho*((j : ℝ)*xi))*(U^(rho*((j : ℝ)*xi))/M) =
      (M/M)*(U^(-rho*((j : ℝ)*xi))*U^(rho*((j : ℝ)*xi))) by ring,
      div_self hM,one_mul,←Real.rpow_add hU]
    simp
  rw [he,Complex.ofReal_one,one_mul]

/-- Every term outside the exact source cutoff is zero, including before any
coefficient mass bound or choice of a row-dependent dilation box. -/
theorem actual_label_term_zero_of_cutoff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (η : Character) (u : FreeRow)
    (T : ι→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (weight : ∀i,T i→ℂ) (x z : ℂ) (W : ℝ→ℂ) (a b Y : ℝ)
    (hY : 0 < Y) (hsupp : Function.support W ⊆ Set.Icc a b)
    (e : LabelPacketIndex S u T) (hcut : b*Y < (labelPacketScale S u T e : ℝ)) :
    labelPacketCoefficient S hS η u T hT weight x z e *
      (labelPacketScale S u T e : ℂ)^(-(1/2:ℂ)) *
      HeckeDyadic.polynomial (rowCharacter S hS.prime u) false W
        (Y/(labelPacketScale S u T e : ℝ)) 0 0 = 0 := by
  have hp := MellinReconstruction.polynomial_zero_of_scale_cutoff
    (rowCharacter S hS.prime u) W a b Y
    (labelPacketScale S u T e : ℝ) hsupp hY
    (lt_of_lt_of_le zero_lt_one (by exact_mod_cast labelPacketScale_one_le S u T e)) hcut
  rw [hp,mul_zero]


/-- A real packet box inherits the actual polynomial choice moment. The cutoff
condition is used only to identify the finite active scales. -/
theorem normalized_dilation_box_fourth {ι : Type*} [Fintype ι] {α : ι → Type*}
    (base : ∀ i, α i) (A S : ∀ i, α i → ℂ) (N : ∀ i, α i → ℝ)
    (hN : ∀ i e, 0 < N i e) (L : ι → ℝ) (rho U xi : ℝ) (n j : ℕ)
    (valid : ∀ i, α i → Prop) [∀ i e, Decidable (valid i e)]
    (Q : ι → ℂ) (M E : ℝ) (hM : 0 < M) (hU : 1 ≤ U) (hxi : 0 ≤ xi) (hrho : 0 ≤ rho)
    (hzero : ∀ i e, ¬valid i e → S i e = 0)
    (hupper : ∀ i e, valid i e → max 1 (L i * N i e) ≤ U^((n : ℝ)*xi))
    (hs : ∀ i, Summable (fun e => ‖A i e‖ * (N i e)^(-(1 / 2 : ℝ)) *
      max 1 (L i * N i e)^rho))
    (hm : ∀ i, (∑' e, ‖A i e‖ * (N i e)^(-(1 / 2 : ℝ)) *
      max 1 (L i * N i e)^rho) ≤ M)
    (hselection : ∀ e : ∀ i, α i,
      (∑ i, ‖if valid i (e i) ∧ dilationBox U xi n (max 1 (L i*N i (e i))) = j
        then S i (e i) else 0‖^4 * ‖Q i‖^2) ≤ E) :
    (∑ i, ‖normalizedBox U xi n j rho M (fun e=> max 1 (L i*N i e))
      (fun e=> A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e)‖^4 * ‖Q i‖^2) ≤ E := by
  have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU
  let active (i : ι) (e : α i) := valid i e ∧ dilationBox U xi n (max 1 (L i*N i e)) = j
  have hlo (i : ι) (e : α i) (he : active i e) : U^((j : ℝ)*xi) ≤ max 1 (L i*N i e) := by
    have hh := (dilationBox_spec U xi hU hxi n (max 1 (L i*N i e))
      (le_max_left _ _) (hupper i e he.1)).1
    rwa [he.2] at hh
  have hh := packet_box_fourth base A S N hN L rho U ((j : ℝ)*xi) active Q M E hM hU0 hrho
    hlo hs hm hselection
  have ht (i : ι) (e : α i) :
      boxSeriesTerm U xi n j (fun e=> max 1 (L i*N i e))
        (fun e=> A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e) e =
      A i e*(N i e:ℂ)^(-(1/2:ℂ))*(if active i e then S i e else 0) := by
    by_cases hv : valid i e
    · by_cases hb : dilationBox U xi n (max 1 (L i*N i e)) = j
      · simp [boxSeriesTerm,active,hv,hb]
      · simp [boxSeriesTerm,active,hv,hb]
    · simp [boxSeriesTerm,active,hv,hzero i e hv]
  simpa only [normalizedBox,ht] using hh


theorem actual_label_series_norm_summable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (hrow : (rowCharacter S hS.prime u).residue ≠ 1)
    (T : ι→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (weight : ∀i,T i→ℂ) (x z : ℂ)
    (hx : (51/100:ℝ)≤ x.re) (hz : (17/50:ℝ)≤ z.re)
    (hmargin : 1+firsteps≤ x.re+1/2)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0< a) (hsupp : Function.support W⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (Y : ℝ) (hY : 0< Y) :
    Summable (fun e : LabelPacketIndex S u T =>
      ‖labelPacketCoefficient S hS η u T hT weight x z e *
      (labelPacketScale S u T e : ℂ)^(-(1/2:ℂ)) *
      HeckeDyadic.polynomial (rowCharacter S hS.prime u) false W
        (Y/(labelPacketScale S u T e : ℝ)) 0 0‖) :=
  MellinReconstruction.reconstructed_series_norm_summable (rowCharacter S hS.prime u) hrow
    W a b ha hsupp hW Y hY _ _
    (fun e=> lt_of_lt_of_le zero_lt_one (by exact_mod_cast labelPacketScale_one_le S u T e))
    (label_packet_central_summable S hS firsteps hfirst η u T hT weight x z hx hz hmargin)

theorem errorLabelNumerator_zero_of_no_labels {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (η : Character) (u : FreeRow)
    (J : Finset (Fin K)) (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x z : ℂ) (W1 : ℝ→ℂ) (Y : ℝ)
    (hempty : ¬Nonempty (∀ i:J,T i.val)) :
    errorLabelNumerator S hS η u J T hT W Yp x z W1 Y = 0 := by
  letI : IsEmpty (∀ i:J,T i.val) := not_nonempty_iff.mp hempty
  simp only [errorLabelNumerator,Finset.univ_eq_empty,Finset.sum_empty]

end Cycle25.Numerator

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 generalizes the moment parameter and retains explicit mesh losses. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.BoxReconstruction -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorPhysicalPacketMass ; sha256 a8d6890e7418f7dcc0ba3518a61be43b0a36a618063dcf10ad4cdd10dee41f71 -/
section



/-! Actual error-label coefficient mass, with every physical prime label summed
and with the final subpower loss chosen independently of the label count. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators Classical
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
local notation "O" => HeckeFamily.O

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem actual_physical_label_mass (epsilon c d B : ℝ)
    (hepsilon : 0 < epsilon) (hc : 0 < c) (hd : 0 < d) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
      (T : ι → Finset ProbePhysical.PrimeIdeal) (hT : ∀ i P, P ∈ T i → P.val ∉ S)
      (hdis : ∀ P : ∀ i, T i, Function.Injective (fun i => (P i).val))
      (hη : ∀ i P, P ∈ T i → IsCoprime P.val η.modulus)
      (W : ι → ℝ → ℂ) (Y : ι → ℝ),
      (∀ i, 1 ≤ Y i) → (∀ i, Function.support (W i) ⊆ Set.Icc c d) →
      (∀ i y, ‖W i y‖ ≤ B) → ∀ (x z : ℂ) (alpha eps rho Ccond Cu : ℝ),
      (51 / 100 : ℝ) ≤ alpha → alpha ≤ 1 → 0 < eps → eps ≤ 1 / 1000 →
      x.re = alpha + 16 * eps → z.re = 17 / 50 → 0 ≤ rho → rho ≤ 1 →
      1 - alpha - 6 * eps ≤ 1 / 2 - rho → -(1 / 100 : ℝ) ≤ 1 / 2 - rho →
      1 + firsteps ≤ x.re + (1 / 2 - rho) →
      0 < Ccond → 0 ≤ Cu → Cu ≤ Ccond * ((Ideal.span {u.val} : Ideal O).radical.absNorm : ℝ) →
      let L := Cu / (Ccond * (Ideal.span {u.val} : Ideal O).absNorm)
      let weight : ∀ i, T i → ℂ := fun i P => physicalSlotWeight P.val (W i) (Y i) z
      Summable (fun e : LabelPacketIndex S u T => ‖labelPacketCoefficient S hS η u T hT weight x z e‖ *
        (labelPacketScale S u T e : ℝ)^(-(1 / 2 : ℝ)) * max 1 (L*(labelPacketScale S u T e : ℝ))^rho) ∧
      (∑' e : LabelPacketIndex S u T, ‖labelPacketCoefficient S hS η u T hT weight x z e‖ *
        (labelPacketScale S u T e : ℝ)^(-(1 / 2 : ℝ)) * max 1 (L*(labelPacketScale S u T e : ℝ))^rho) ≤
        C * ((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^epsilon * ∏ i, (Y i)^(-(4 / 25 : ℝ)) := by
  obtain ⟨C1,hC1,hmass⟩ := actual_label_packet_mass (ι:=ι) (epsilon/2) (by linarith)
  obtain ⟨C2,hC2,hprime⟩ := error_label_prime_product_bound (epsilon/2) c d B (Fintype.card ι)
    (by linarith) hc hd hB
  refine ⟨C1*C2,mul_pos hC1 hC2,?_⟩
  intro S hS firsteps hfirst η u T hT hdis hη W Y hY hWS hWB x z alpha eps rho Ccond Cu
    halpha halpha1 heps heps1 hx hz hrho hrho1 hline hleft hmargin hCcond hCu0 hCu
  let weight : ∀ i, T i → ℂ := fun i P => physicalSlotWeight P.val (W i) (Y i) z
  obtain ⟨hs,hm⟩ := hmass S hS firsteps hfirst η u T hT hdis hη weight x z alpha eps rho Ccond Cu
    halpha halpha1 heps heps1 hx hz hrho hrho1 hline hleft hmargin hCcond hCu0 hCu
  refine ⟨hs,hm.trans ?_⟩
  have hp := hprime ι le_rfl u T Y W hY hWS hWB z hz
  change (∏ i, ∑ P : T i, 2880*‖weight i P‖*errorSize u P.val) ≤ _ at hp
  have hNu : (0 : ℝ) < (Ideal.span {u.val} : Ideal O).absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
  calc
    _ ≤ (C1*((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^(epsilon/2)) *
        (C2*((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^(epsilon/2) * ∏ i, (Y i)^(-(4 / 25 : ℝ))) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by
      rw [show (C1*((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^(epsilon/2)) *
          (C2*((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^(epsilon/2) * ∏ i, (Y i)^(-(4 / 25 : ℝ))) =
          (C1*C2)*((((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^(epsilon/2))*
          (((Ideal.span {u.val} : Ideal O).absNorm : ℝ)^(epsilon/2))) * ∏ i, (Y i)^(-(4 / 25 : ℝ)) by ring]
      rw [←Real.rpow_add hNu,show epsilon/2+epsilon/2=epsilon by ring]

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorPhysicalPacketMass -/
