/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
This specializes the original OpenAI finite-cube integral and corrected
calibrated-tuple factorization to the genuine Q source data and selection.
Inherited Collet/Levy/Gao/Bebel transport attributions remain in the imports. -/
import Candidate.C092.transport.SelectedActualFloor

/-!
The analytic consumer for the literal selected finite numerator. It integrates
the original calibrated row, full prime pools and buffered three-dimensional
cube. In particular the row contains the true Hecke reciprocal and compensated
local factors, not an unweighted source energy. The integral estimate in the
last theorem remains an explicit obligation.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open Filter MeasureTheory
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily
open OAI.SevenEighths.ProbeHighRowFamily OAI.SevenEighths.HeckeInverseAmplification
open OAI.SevenEighths.ProbePhysical OAI.SevenEighths.PrincipalSignalComparison
open OAI.SevenEighths.ProbeRaySlots OAI.SevenEighths.ProbeMellinBoundary
open OAI.SevenEighths.BoundaryDensitySplitReturn.TransportHighTransport
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open QRH.Cycle092.ProbeAssembly

namespace QRH.Cycle092.SelectedActualIntegral
variable [Geometry.Parameters]

def primePool (D : BaselineData) (F : BaselineSourceData D) (Z : ℝ)
    (j : Fin D.N) : Finset ProbePhysical.PrimeIdeal :=
  pool (RayQuotient.identityClass F.modulus ⊤) F.S 1 2 (Z^(D.length j))

theorem pool_outside (D : BaselineData) (F : BaselineSourceData D) (Z : ℝ)
    (j : Fin D.N) (P : ProbePhysical.PrimeIdeal) (hP : P ∈ primePool D F Z j) :
    P.val ∉ F.S :=
  (mem_pool (RayQuotient.identityClass F.modulus ⊤) F.S 1 2 (Z^(D.length j)) P).mp hP |>.2.2.2

def selectedRows (D : BaselineData) (F : BaselineSourceData D)
    (padding Z : ℝ) (grid : FreeRow → ℕ) : Finset FreeRow :=
  supportedNonfloorRows F.S F.maximal (rowBand (Z^(1/100 : ℝ)) (Z^(Geometry.h+padding))) grid

/-- Both finite sums precede integration. Each summand keeps its own row's
actual zero band, original buffer and all three independent height variables. -/
def selectedIntegrand (D : BaselineData) (F : BaselineSourceData D)
    (padding tau : ℝ) (η : Character) (Z : ℝ)
    (idx grid : FreeRow → ℕ) (t : HeightSpace) : ℂ :=
  ∑ u ∈ selectedRows D F padding Z grid, ∑ P : (∀ j, primePool D F Z j),
    cubeWeightedRow F.S F.exclusions F.maximal (fun j => (P j).val)
      (fun j => pool_outside D F Z j _ (P j).property) η u
      (fun (_ : Fin D.N) y => (F.w y : ℂ)) (fun j => Z^(D.length j)) F.W F.W
      (Z^Geometry.x) (Z^Geometry.y) Z (51/100+D.e*grid u) D.e
      ((3*idx u+1 : ℕ)*Z^tau) t

/-- Exact integrability and equality for the selected finite numerator. No
old conductor/cap/coarse-geometry instance or analytic moment bound is used. -/
theorem numerator_integral (D : BaselineData) (F : BaselineSourceData D)
    (padding tau : ℝ) (n : ℕ) (η : Character) (Z : ℝ) (idx grid : FreeRow → ℕ)
    (hZ : 0 < Z) (hZT : 2 < Z^tau)
    (hsel : selected D F padding tau n η Z idx grid) :
    Integrable (selectedIntegrand D F padding tau η Z idx grid) heightMeasure ∧
    numerator D F padding tau η Z idx grid =
      ((1/(2*Real.pi) : ℝ) : ℂ)^3 *
        ∫ t, selectedIntegrand D F padding tau η Z idx grid t ∂heightMeasure := by
  have hR : ∀ u ∈ selectedRows D F padding Z grid, u.val ≠ 1 := by
    intro u hu
    exact (mem_rowBand.mp ((mem_supportedNonfloorRows F.S F.maximal _ grid u).mp hu).1).1
  have hbin : ∀ u ∈ selectedRows D F padding Z grid,
      (51/100 : ℝ) ≤ 51/100+D.e*grid u ∧ 51/100+D.e*grid u ≤ 1 ∧
      2 < Z^tau ∧ (3*idx u+1 : ℕ)*Z^tau ≤ (3*idx u+2 : ℕ)*Z^tau ∧
      detectorMaximum (sourceDetectorFamily F.S F.exclusions.prime η u
        (rayCubeFamily F.modulus ⊤ le_top u)) (3*(idx u+1 : ℕ)*Z^tau) <
          51/100+D.e*grid u+2*D.e := by
    intro u _hu
    have hb := hsel.2.1 u
    have hbuffer := (hsel.1 u).2.2.2
    have hp : 0 ≤ Z^tau := Real.rpow_nonneg hZ.le _
    exact ⟨hb.1, hb.2.1.trans (by norm_num), hZT, by linarith, hb.2.2.2.2.1⟩
  exact finiteCentralCubeRows_eq_integral D.e D.e_pos D.e_small
    F.S F.exclusions F.maximal F.first η (selectedRows D F padding Z grid) hR
    (primePool D F Z) (pool_outside D F Z)
    (fun u => 51/100+D.e*grid u) (fun _ => Z^tau)
    (fun u => (3*idx u+1 : ℕ)*Z^tau) idx (rayCubeFamily F.modulus ⊤ le_top) hbin
    (fun (_ : Fin D.N) y => (F.w y : ℂ)) (fun j => Z^(D.length j))
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num) F.complex_support F.complex_support
    (Z^Geometry.x) (Z^Geometry.y) Z (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _) hZ

/-- Complete source pools eventually have genuinely distinct primes in every
assignment. This supplies the exact hypothesis of the corrected reciprocal
factorization `calibratedTupleValue_factor`, retaining all selected factors. -/
theorem tuples_injective (D : BaselineData) (F : BaselineSourceData D) :
    ∀ᶠ Z : ℝ in atTop, ∀ P : (∀ j, primePool D F Z j),
      Function.Injective (fun j => (P j).val) :=
  power_pool_tuples_eventually_injective (RayQuotient.identityClass F.modulus ⊤) F.S
    (fun _ : Fin D.N => (1 : ℝ)) (fun _ => (2 : ℝ)) D.length
    (fun _ => by norm_num) (fun _ => by norm_num) D.slots_injective

/-- The exact corrected row factor: the denominator is the original masked
target-row Hecke L-function. The calibration, marked exclusions and every
completed local main/error factor remain, including their natural zeros. -/
def rawFactor (D : BaselineData) (F : BaselineSourceData D)
    (η : Character) (u : FreeRow) (Z : ℝ) (P : ∀ j, primePool D F Z j)
    (x w z : ℂ) : ℂ :=
  (star ((calibrationForSet F.S F.maximal).residueMonoid u.val) *
    (LFunction (fixedSourcePrincipal F.S F.exclusions.prime) (6*z) *
      HeckeOrigin.continued (rowCharacter F.S F.exclusions.prime u) w *
      HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes F.S F.exclusions.prime) x)) *
  (continuedCorrection (markExclusions F.S (Finset.univ.image (fun j => (P j).val)))
    (markedSourceExclusions F.S F.exclusions (Finset.univ.image (fun j => (P j).val))) η u x w z *
    ∏ j, (F.w (((P j).val.val.absNorm : ℝ)/Z^(D.length j)) : ℂ) *
      ((P j).val.val.absNorm : ℂ)^(z-1) *
      continuedCompensatedLocal η u (P j).val
        (outside_prime_supported F.S F.exclusions.bad (P j).val
          (pool_outside D F Z j _ (P j).property)) x w z
        (star (idealCoeff η (P j).val.val)*((P j).val.val.absNorm : ℂ)^x)
        (((P j).val.val.absNorm : ℂ)^(-w)))

/-- This exact factorization applies to each tuple supplied by
`tuples_injective`; it does not replace the reciprocal by its absolute majorant
or divide a source character value at a nonunit. -/
theorem calibrated_row_factor (D : BaselineData) (F : BaselineSourceData D)
    (η : Character) (u : FreeRow) (Z : ℝ) (P : ∀ j, primePool D F Z j)
    (hP : Function.Injective (fun j => (P j).val)) (x w z : ℂ) :
    calibratedTupleValue F.S F.exclusions F.maximal η u (fun j => (P j).val)
      (fun j => pool_outside D F Z j _ (P j).property)
      (fun (_ : Fin D.N) y => (F.w y : ℂ)) (fun j => Z^(D.length j)) x w z =
        rawFactor D F η u Z P x w z :=
  calibratedTupleValue_factor F.S F.exclusions F.maximal η u (fun j => (P j).val)
    hP (fun j => pool_outside D F Z j _ (P j).property)
    (fun (_ : Fin D.N) y => (F.w y : ℂ)) (fun j => Z^(D.length j)) x w z

/-- The exact analytic input consumed by the literal numerator bound. The
integrand retains the reciprocal, completed Euler factors, calibration zeros,
prime assignment and original buffered selection. -/
def IntegralBound (D : BaselineData) (F : BaselineSourceData D)
    (padding tau saving : ℝ) (n : ℕ) (η : Character) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, ∀ idx grid : FreeRow → ℕ,
    selected D F padding tau n η Z idx grid →
    ‖∫ t, selectedIntegrand D F padding tau η Z idx grid t ∂heightMeasure‖ ≤
      C*‖normalizer D F Z‖*Z^(HeckeZeroSupremum.beta+ProbeAssembly.shift-saving)

/-- Actual raw integral control discharges precisely the finite-numerator
input already consumed by ProbeAssembly, without changing its signal. -/
theorem finite_numerator_of_integral (D : BaselineData) (F : BaselineSourceData D)
    (padding tau saving : ℝ) (htau : 0 < tau) (n : ℕ) (η : Character)
    (hinput : IntegralBound D F padding tau saving n η) :
    FiniteNumeratorBound D F padding tau saving n η := by
  obtain ⟨C, hC, hbound⟩ := hinput
  let k : ℂ := ((1/(2*Real.pi) : ℝ) : ℂ)^3
  refine ⟨(‖k‖+1)*C, by positivity, ?_⟩
  filter_upwards [hbound, source_cube_height_eventually tau htau] with Z hb hZ
  intro idx grid hsel
  have heq := (numerator_integral D F padding tau n η Z idx grid
    (zero_lt_one.trans_le hZ.1) hZ.2 hsel).2
  rw [heq, norm_mul]
  have hi := hb idx grid hsel
  calc
    _ ≤ ‖k‖*(C*‖normalizer D F Z‖*Z^(HeckeZeroSupremum.beta+ProbeAssembly.shift-saving)) :=
      mul_le_mul_of_nonneg_left hi (norm_nonneg _)
    _ ≤ (‖k‖+1)*(C*‖normalizer D F Z‖*Z^(HeckeZeroSupremum.beta+ProbeAssembly.shift-saving)) := by
      exact mul_le_mul_of_nonneg_right (by linarith [norm_nonneg k])
        (mul_nonneg (mul_nonneg hC.le (norm_nonneg _))
          (Real.rpow_nonneg (zero_le_one.trans hZ.1) _))
    _ = _ := by ring

end QRH.Cycle092.SelectedActualIntegral
#print axioms QRH.Cycle092.SelectedActualIntegral.numerator_integral
#print axioms QRH.Cycle092.SelectedActualIntegral.tuples_injective
#print axioms QRH.Cycle092.SelectedActualIntegral.calibrated_row_factor
#print axioms QRH.Cycle092.SelectedActualIntegral.finite_numerator_of_integral
