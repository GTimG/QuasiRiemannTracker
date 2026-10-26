/- Literal history code for the actual continuing carrier used by
NativeForestAttach. Residual choices remain attached metadata. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.PhysicalHistoryCode
import Candidate.Cycle63.Moment.DepthTwoCount
import Candidate.Research.RecursiveAffine.HistoryPrepend
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowPayment
import Candidate.Cycle63.Physical.InitialMass.SecondLabelDisintegration

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SevenEighths.Cycle153JointCount
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentSectorLocalization CenteredMomentEnergyState
open CenteredMomentSecondHeightFamily

variable {alpha Label : Type} [Fintype alpha] [DecidableEq alpha] [Fintype Label]
variable (reflected : Bool) (s : Input alpha) (R seed : Ideal O)
variable (Z Mrow amp xi reserve b firstHeight : ℝ) (N : ℕ) (hZ : 1<Z)
variable (key : ℤ×(Fin 5→ℤ)) (hz1 : s.W₁ 0=0) (hz2 : s.W₂ 0=0)
variable (firstIndex : Label → GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z xi
  (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)

local notation "Rows" => ↥(mainLowSelectedNonzeroRows reflected s R seed Z Mrow amp xi reserve b
  firstHeight N hZ key hz1 hz2 firstIndex)
local notation "first" => fun l=>geometryFirstLabel s R seed (Z^Mrow) Z xi
  (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l).1.val

/-- Exact arithmetic child prefix, old projector seed and all four native
dyads of the selected original nonzero physical block. -/
def nativeLowHistoryCode (r : Rows) : DecoratedPrefix :=
  (⟨first r.val.1,Cycle63InitialMass.actualSecondArithmeticLabel _ _ _ _ _ _ _ r.val.2⟩,
    (firstIndex r.val.1).1.val.2.1.val,
    Cycle63InitialMass.actualSecondDyad _ _ _ _ _ _ _ r.val.2)

/-- The same first-label/projector injection supplied by the physical
selector gives an injection of the literal continuing carrier. Neither
the selected deleted subset nor common/residual attainers are recounted. -/
theorem nativeLowHistoryCode_injective
    (hfirst : Function.Injective (fun l=>(first l,(firstIndex l).1.val.2.1.val))) :
    Function.Injective (nativeLowHistoryCode reflected s R seed Z Mrow amp xi reserve b
      firstHeight N hZ key hz1 hz2 firstIndex) := by
  rintro ⟨⟨l,n⟩,hr⟩ ⟨⟨l',n'⟩,hr'⟩ h
  have hf : first l=first l' := congrArg (fun x : DecoratedPrefix=>x.1.1) h
  have hs : (firstIndex l).1.val.2.1.val=(firstIndex l').1.val.2.1.val :=
    congrArg (fun x : DecoratedPrefix=>x.2.1) h
  have hl : l=l' := hfirst (Prod.ext hf hs)
  cases hl
  have ha : Cycle63InitialMass.actualSecondArithmeticLabel _ _ _ _ _ _ _ n=
      Cycle63InitialMass.actualSecondArithmeticLabel _ _ _ _ _ _ _ n' :=
    congrArg (fun x : DecoratedPrefix=>x.1.2) h
  have hd : Cycle63InitialMass.actualSecondDyad _ _ _ _ _ _ _ n=
      Cycle63InitialMass.actualSecondDyad _ _ _ _ _ _ _ n' :=
    congrArg (fun x : DecoratedPrefix=>x.2.2) h
  have hn : n=n' := Cycle63InitialMass.actual_second_label_dyad_injective _ _ _ _ _ Z xi (Prod.ext ha hd)
  exact Subtype.ext (Sigma.ext rfl (heq_of_eq hn))

/-- The forest's literal child multiplier is precisely the multiplier of
this history key, with the actual parent's multiplier and natural units. -/
theorem nativeLowHistoryCode_multiplier (root : O) (units : FirstSourceLabel→O) (r : Rows) :
    childMultiplier (!reflected) root units
      (nativeLowHistoryCode reflected s R seed Z Mrow amp xi reserve b firstHeight N hZ key hz1 hz2 firstIndex r).1=
      Cycle63Moment.childMultiplier (!reflected) root units
        ⟨first r.val.1,Cycle63InitialMass.actualSecondArithmeticLabel _ _ _ _ _ _ _ r.val.2⟩ := rfl

/-- The history adds exactly the native first missing radical once. -/
theorem nativeLowHistoryCode_missing (r : Rows) :
    stepMissing (!reflected) Z
      (nativeLowHistoryCode reflected s R seed Z Mrow amp xi reserve b firstHeight N hZ key hz1 hz2 firstIndex r).1=
      Real.logb Z ((firstSourceMissing (!reflected) (first r.val.1)).absNorm:ℝ) := rfl

/-- The dependent sum of literal selected parent rows and actual daughter
prefixes injects into the full source history. This is the exact carrier
used by `DepthReturnedFamily.attach`, with each daughter's code supplied
by the strictly smaller-depth construction. -/
theorem attached_native_low_code_injective (n : ℕ)
    (hfirst : Function.Injective (fun l=>(first l,(firstIndex l).1.val.2.1.val)))
    (Child : Rows→Type*) (childCode : (r : Rows)→Child r→History n)
    (hchild : ∀r,Function.Injective (childCode r)) :
    Function.Injective (fun p : Σr : Rows,Child r=>prependHistory n
      (nativeLowHistoryCode reflected s R seed Z Mrow amp xi reserve b firstHeight N hZ key hz1 hz2 firstIndex p.1)
      (childCode p.1 p.2)) := by
  rintro ⟨r,p⟩ ⟨r',p'⟩ h
  let code:=nativeLowHistoryCode reflected s R seed Z Mrow amp xi reserve b firstHeight N hZ key hz1 hz2 firstIndex
  have he:=@prependHistory_pair_injective n (code r,childCode r p) (code r',childCode r' p') h
  have hd : code r=code r' := congrArg (fun x : DecoratedPrefix×History n=>x.1) he
  have hr : r=r' := nativeLowHistoryCode_injective reflected s R seed Z Mrow amp xi reserve b
    firstHeight N hZ key hz1 hz2 firstIndex hfirst hd
  cases hr
  have hc : childCode r p=childCode r p' := congrArg (fun x : DecoratedPrefix×History n=>x.2) he
  have hp : p=p' := hchild r hc
  exact Sigma.ext rfl (heq_of_eq hp)

end
end OAI.SevenEighths.Cycle153JointCount
#print axioms OAI.SevenEighths.Cycle153JointCount.nativeLowHistoryCode_injective
#print axioms OAI.SevenEighths.Cycle153JointCount.nativeLowHistoryCode_multiplier
