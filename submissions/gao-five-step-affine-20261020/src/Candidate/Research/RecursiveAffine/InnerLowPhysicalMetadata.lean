/- Genuine physical LOW constants before the moving source. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativePhysicalLedgerUniform
import Candidate.Research.RecursiveAffine.NativeLowCoarseSchedule
import Candidate.Research.RecursiveAffine.NativeLowCoefficient
import Candidate.Research.RecursiveAffine.NativeColumnUniformControl
import Candidate.Research.RecursiveAffine.NativeSelectedOldThreshold

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 5000
namespace OAI.SevenEighths.Cycle153InnerLowSchedule
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open LocalMoment
open Filter HeckeFamily Cycle63InitialMass Cycle153SourceSchedule Cycle153SourceUniform
open Cycle153RegionalLow Cycle153ActualColumn Cycle153ActualSourceGates
open CenteredMomentSecondHeightFamily CenteredMomentSecondInputCapacitySource
open CenteredMomentSecondCanonicalScalar
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentInductionEnergy CenteredMomentEnergyState CenteredMomentFirstAmplificationChoice
variable {alpha : Type}[Fintype alpha][DecidableEq alpha]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
variable (hH : RayOrthogonality.globalUnits M≤H)(j : Fin 4)

def innerPhysicalConstant (r : ℝ)(hr : 0<r)(T : Finset alpha) : ℝ :=
  Classical.choose (eventual_actual_inner_physical_receipt_all_ledgers (alpha:=alpha) (Current:=T)
    (M:=M) (H:=H) (hH:=hH) j T.card 3 r r (by norm_num) hr.le hr)

theorem innerPhysicalConstant_pos (r : ℝ)(hr : 0<r)(T : Finset alpha) :
    0 < innerPhysicalConstant hH j r hr T :=
  (Classical.choose_spec (eventual_actual_inner_physical_receipt_all_ledgers (alpha:=alpha) (Current:=T)
    (M:=M) (H:=H) (hH:=hH) j T.card 3 r r (by norm_num) hr.le hr)).1

def innerPhysicalThreshold (r : ℝ)(hr : 0<r)(T : Finset alpha) : ℝ :=
  Classical.choose (eventually_atTop.mp
    (Classical.choose_spec (eventual_actual_inner_physical_receipt_all_ledgers (alpha:=alpha) (Current:=T)
      (M:=M) (H:=H) (hH:=hH) j T.card 3 r r (by norm_num) hr.le hr)).2)

/-- This is the genuine native residual/ray/buffer operator after a fixed
threshold. Its local source input is supplied by the actual selected-row
producer, not stored as an unproved LOW or energy field. -/
def innerPhysicalAfter (r : ℝ)(hr : 0<r)(T : Finset alpha)(Z : ℝ)
    (hZ : innerPhysicalThreshold hH j r hr T≤Z) :=
  Classical.choose_spec (eventually_atTop.mp
    (Classical.choose_spec (eventual_actual_inner_physical_receipt_all_ledgers (alpha:=alpha) (Current:=T)
      (M:=M) (H:=H) (hH:=hH) j T.card 3 r r (by norm_num) hr.le hr)).2) Z hZ

/-- The source/physical thresholds cover all original subsets and all
actual rebase units before the moving context or its ledger is chosen. -/
theorem eventual_inner_low_auxiliary_thresholds
    (Bnorm : ℝ)(hB : 0≤Bnorm)(budget : ℕ) :
    let r:=postDictionaryRate Bnorm budget
    let hr:=(postDictionaryRate_budgets hB budget).1
    ∀ᶠZ : ℝ in atTop,1<Z ∧∀U : ℝ,(1/50:ℝ)≤U→∀T : Finset alpha,
      innerPhysicalThreshold hH j r hr T≤Z^U ∧
      actualSelectedOldThreshold Bnorm hB budget T.card≤Z^U :=by
  intro r hr
  have localThresholds : ∀T : Finset alpha,∀ᶠY : ℝ in atTop,
      innerPhysicalThreshold hH j r hr T≤Y ∧
      actualSelectedOldThreshold Bnorm hB budget T.card≤Y :=by
    intro T
    exact (eventually_ge_atTop _).and (eventually_ge_atTop _)
  exact eventually_all_rebased_sources _ (Filter.eventually_all.mpr localThresholds)

/-- Exact fixed physical prefactor. Dynamic geometryHighFactor and profile
controls remain outside this constant. -/
def innerPhysicalPrefactor (N : ℕ)(e : ℝ) : ℝ :=
  (1/lowerFactor N 1 (1/4))*((Fintype.card RayFourExpansion.RayCharacter:ℝ)^2*
    (Fintype.card (BufferIndex e):ℝ))

theorem innerPhysicalPrefactor_nonnegative (N : ℕ)(e : ℝ) :
    0 ≤ innerPhysicalPrefactor N e :=by
  have hden:=(lowerFactor_pos N 1 (1/4) (by norm_num) (by norm_num)).le
  unfold innerPhysicalPrefactor
  positivity

/-- The exact return coefficient of the actual complete physical operator. -/
def innerRawReturnConstant (N : ℕ)(e Cu Cg : ℝ) : ℝ :=
  innerPhysicalPrefactor N e*(2*(Cu*Cg))

/-- The exact OLD coefficient after genuine source/box payment. -/
def innerRawOldConstant (N : ℕ)(e Cu Cg Kold Kbox : ℝ) : ℝ :=
  innerPhysicalPrefactor N e*(Cu*(Kold*Cg*Kbox))

theorem innerRawReturnConstant_nonnegative (N : ℕ)(e Cu Cg : ℝ)
    (hCu : 0≤Cu)(hCg : 0≤Cg) : 0 ≤ innerRawReturnConstant N e Cu Cg :=
  mul_nonneg (innerPhysicalPrefactor_nonnegative N e) (by positivity)

theorem innerRawOldConstant_nonnegative (N : ℕ)(e Cu Cg Kold Kbox : ℝ)
    (hCu : 0≤Cu)(hCg : 0≤Cg)(hOld : 0≤Kold)(hbox : 0≤Kbox) :
    0 ≤ innerRawOldConstant N e Cu Cg Kold Kbox :=
  mul_nonneg (innerPhysicalPrefactor_nonnegative N e) (by positivity)

end
end OAI.SevenEighths.Cycle153InnerLowSchedule
#print axioms OAI.SevenEighths.Cycle153InnerLowSchedule.innerPhysicalAfter
#print axioms OAI.SevenEighths.Cycle153InnerLowSchedule.eventual_inner_low_auxiliary_thresholds
