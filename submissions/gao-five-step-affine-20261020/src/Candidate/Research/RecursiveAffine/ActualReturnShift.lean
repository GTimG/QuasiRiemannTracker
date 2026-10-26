/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.DepthReturnedFamily

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle63Moment Cycle153SourceReturn ProbePhysical LocalMoment

variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M ≤ H}

/-- Absorb an explicitly paid source power into the count-form exponent.
The actual finite HIGH classes, labels, zero witnesses and arithmetic
caps stay exactly the same. -/
def shiftedHighCount {Base : Type} {base : Base→Character} {eta : Character}
    {Z Bnorm T : ℝ}{left : Bool}{root : O}{unit : FirstSourceLabel→O}
    (R : SecondStepHighCount M H hH base eta Z Bnorm T left root unit)(shift : ℝ) :
    SecondStepHighCount M H hH base eta Z Bnorm T left root unit :=
  { R with exponent := fun sigma=>R.exponent sigma+shift }

theorem shiftedHighCount_pays {Base : Type} {base : Base→Character} {eta : Character}
    {Z Bnorm T : ℝ}{left : Bool}{root : O}{unit : FirstSourceLabel→O}
    (R : SecondStepHighCount M H hH base eta Z Bnorm T left root unit)
    (shift q scale length amp loss : ℝ)(hp : R.Pays q scale length amp loss) :
    (shiftedHighCount R shift).Pays q scale length amp (loss+shift) := by
  intro sigma
  obtain ⟨hlo,hhi,hpay⟩ := hp sigma
  refine ⟨hlo,hhi,?_⟩
  change R.exponent sigma+shift-scale+R.missExp sigma+
    unmarkedDensity (2*R.zeroBin sigma-1)*
      (R.rowExp sigma-Real.logb Z ((Ideal.span {root}).absNorm:ℝ)) ≤ _
  simp only [shiftedHighCount]
  linarith only [hpay]

theorem shiftedHighCount_value {Base : Type} {base : Base→Character} {eta : Character}
    {Z Bnorm T : ℝ}{left : Bool}{root : O}{unit : FirstSourceLabel→O}
    (R : SecondStepHighCount M H hH base eta Z Bnorm T left root unit)
    (shift : ℝ)(hZ : 0<Z) :
    (shiftedHighCount R shift).value=Z^shift*R.value := by
  unfold SecondStepHighCount.value
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sigma hsigma
  change Z^(R.exponent sigma+shift)*(R.labels sigma).card=
    Z^shift*(Z^(R.exponent sigma)*(R.labels sigma).card)
  rw [Real.rpow_add hZ]
  ring

/-- The charged source power increases the native loss by exactly the
same amount. The physical scale, volume, amplifier, units and witnesses
are unchanged. -/
def shiftedReturnedPart {junction : ℝ} {Base : Type}
    {base : Character→Base→Character}{eta : Character}{Z Bnorm T : ℝ}{root : O}
    (P : ReturnedPartAt M H hH junction base eta Z Bnorm T root)(shift : ℝ) :
    ReturnedPartAt M H hH junction base eta Z Bnorm T root where
  unit := P.unit
  record := fun b=>shiftedHighCount (P.record b) shift
  scale := P.scale
  length := P.length
  amp := P.amp
  loss := P.loss+shift
  pays := fun b=>shiftedHighCount_pays (P.record b) shift junction P.scale P.length P.amp P.loss (P.pays b)

theorem shiftedReturnedPart_value {junction : ℝ} {Base : Type}
    {base : Character→Base→Character}{eta : Character}{Z Bnorm T : ℝ}{root : O}
    (P : ReturnedPartAt M H hH junction base eta Z Bnorm T root)(shift : ℝ)(hZ : 0<Z) :
    (shiftedReturnedPart P shift).value=Z^shift*P.value := by
  unfold ReturnedPartAt.value
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  exact shiftedHighCount_value (P.record b) shift hZ

/-- Pay a genuine operator source loss in every terminal HIGH exponent,
retaining the literal raw edge weights and historical missing radicals.
Thus exact physical path traces need no fictional extra LOW edge. -/
def shiftedReturnedForest {Depth : Type} [Fintype Depth]
    {junction : Depth→ℝ}{Base : Depth→Type}
    {base : (d : Depth)→Character→Base d→Character}
    {eta : Character}{Z Bnorm T : ℝ}{root : O}
    (F : DepthReturnedFamily M H hH junction Base base eta Z Bnorm T root)(shift : ℝ) :
    DepthReturnedFamily M H hH junction Base base eta Z Bnorm T root where
  Prefix := F.Prefix
  prefixFintype := F.prefixFintype
  multiplier := F.multiplier
  root_divides := F.root_divides
  historyMissing := F.historyMissing
  historyMissing_nonneg := F.historyMissing_nonneg
  part := fun d p=>shiftedReturnedPart (F.part d p) shift
  weight := F.weight
  weight_nonneg := F.weight_nonneg

theorem shiftedReturnedForest_value {Depth : Type} [Fintype Depth]
    {junction : Depth→ℝ}{Base : Depth→Type}
    {base : (d : Depth)→Character→Base d→Character}
    {eta : Character}{Z Bnorm T : ℝ}{root : O}
    (F : DepthReturnedFamily M H hH junction Base base eta Z Bnorm T root)(shift : ℝ)(hZ : 0<Z) :
    (shiftedReturnedForest F shift).value=Z^shift*F.value := by
  unfold DepthReturnedFamily.value
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  change F.weight d p*(shiftedReturnedPart (F.part d p) shift).value=
    Z^shift*(F.weight d p*(F.part d p).value)
  rw [shiftedReturnedPart_value (F.part d p) shift hZ]
  ring

end
end OAI.SevenEighths.Cycle153RegionalLow

#print axioms OAI.SevenEighths.Cycle153RegionalLow.shiftedHighCount_pays
#print axioms OAI.SevenEighths.Cycle153RegionalLow.shiftedReturnedForest_value
