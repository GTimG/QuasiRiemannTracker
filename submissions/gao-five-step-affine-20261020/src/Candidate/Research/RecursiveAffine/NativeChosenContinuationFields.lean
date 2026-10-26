/- Literal source fields of the native chosen continuation. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.ActualReachableChild
import Candidate.Research.RecursiveAffine.NativeContinuationUnit

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators ContDiff HeckeNotation
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands QuadraticInitialBound
open CenteredMomentNaturalFixedRaySource CenteredMomentFiniteProfileExceptional
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentFirstSourceReduction CenteredMomentInductionEnergy
open Cycle63InitialSource Cycle63Moment Cycle153HighProvider Cycle153RegionalLow
open Cycle153ReachableGeometry

variable {α : Type} [Fintype α] [DecidableEq α]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable (hH : RayOrthogonality.globalUnits M ≤ H)
variable (C : SourceContext (α:=α) M H) (j : Fin 4)
variable (Zparent parentUnit u oldMask : ℝ)
variable (hparentUnit : 0<parentUnit) (hu : 0<u)
variable (hbase : Zparent=C.globalBase^parentUnit)
variable (st : NaturalState Zparent oldMask 2) (hwidth : st.width ≤ u)
variable (hmask : (st.puncture.absNorm:ℝ) ≤ (Zparent^u)^(20:ℝ))
variable (slots : Finset α) (p : Profiles (1/4) (9/4))
variable (X1 X2 : ℝ) (hX1 : 0<X1) (hX2 : 0<X2)

variable (P : PrefixHighPresentation (prefixDictionary j.val C.etaSeed) st.character st.puncture)
variable (hPnorm : ((Ideal.span {P.mult}).absNorm:ℝ) ≤ C.globalBase^(prefixCap j.val))
variable (hfixed : st.fixedModulus=internalQ C.Q C.etaSeed)
variable (t height : ℝ) (hheight : 0 ≤ height)
variable (hfreq : ∀ i : slots,|C.frequency i| ≤ height)
variable (geom : NativeChildGeometry C j Zparent parentUnit u slots X1 X2)
variable (hPhistory : Real.logb C.globalBase (st.puncture.absNorm:ℝ) ≤
  modelMissing j geom.coordinates+modelReduction j geom.coordinates+
    ((j.val:ℝ)+1)/1000000000000000)

/-- Every identifying field of the actual Columns child comes from its
literal nodeOfNativeContinuation constructor. The independent source
height is preserved as child.t; the original frequency height is retained
separately. These identities feed the real edge transport, without a new
IH/output selection or a desired energy/count premise. -/
theorem actual_chosen_continuation_fields :
    let chosen:=nodeOfNativeContinuation C j Zparent parentUnit u oldMask hu hbase st hwidth hmask
      slots p X1 X2 hX1 hX2 P hPnorm hfixed t height hheight hfreq geom hPhistory
    chosen.unit=parentUnit*u ∧ chosen.coordinates=geom.coordinates ∧
      chosen.presentation.mult=P.mult ∧
      chosen.unit*chosen.state.rowWidth=parentUnit*st.rowWidth ∧
      chosen.t=t ∧ chosen.height=height :=by
  intro chosen
  refine ⟨rfl,rfl,rfl,?_,rfl,rfl⟩
  change (parentUnit*u)*(nativeContinuationState st u hu hwidth hmask).rowWidth=_
  change (parentUnit*u)*(st.rowWidth/u)=parentUnit*st.rowWidth
  field_simp [hu.ne']

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.actual_chosen_continuation_fields
