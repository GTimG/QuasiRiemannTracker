/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual kept complete second family injects into its original modified row family. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.SecondSectorDatumFamily
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.ModifiedFibersSelection
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedSecondFibers
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily Cycle61Moment Cycle61InitialMass
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentSecondLiveBlock CenteredMomentSectorLocalization
open QRH.Record1252270103Source.High.GlobalPhysical SecondSectorDatum ModifiedFibers
local notation "O" => HeckeFamily.O
local instance {ι : Type*} : DecidableEq ι := Classical.decEq _
variable {α Label : Type*} [Fintype α] [Fintype Label]
variable (slots : Label→Finset α) (s : ∀l,Input (slots l)) (modifier : ∀l,Tuple (slots l)→ℂ)
    (R seed : Label→Ideal O) (K Tsec : Label→ℝ) (Z ξ : ℝ) (W : 𝓢(ℝ,ℂ))

def completeIndex (q : CompleteFamily slots s modifier R seed W K Tsec (fun _=>Z) (fun _=>ξ)) :
    JointIndex slots s modifier R seed K Tsec Z ξ := ⟨q.1,q.2.val⟩

theorem complete_index_injective : Function.Injective (completeIndex slots s modifier R seed K Tsec Z ξ W) := by
  rintro ⟨l,⟨q,hq⟩⟩ ⟨m,⟨v,hv⟩⟩ h
  have hl : l=m := congrArg Sigma.fst h
  cases hl
  have hqv : q=v := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  cases hqv
  rfl

variable (hseed : ∀l,Squarefree (seed l)) (hz₁ : ∀l,(s l).W₁ 0=0) (hz₂ : ∀l,(s l).W₂ 0=0)
    (hK : ∀l,0<K l)
    (keep : ∀l,Record1252270103Second.BlockIndex (s l) (modifier l) (R l) (seed l) (K l) (Tsec l) Z ξ→O→Prop)

def keptBlock (q : CompleteFamily slots s modifier R seed W K Tsec (fun _=>Z) (fun _=>ξ)) : SecondBlockSource :=
  (familyDatum slots s modifier R seed hseed hz₁ hz₂ W K Tsec (fun _=>Z) (fun _=>ξ) hK keep q).block

/-- Beta is irrelevant to the live-row carrier; all retained coefficient data
remain in the actual modifiedDatumBlock used by the phase identity. -/
theorem kept_live_rows_modified :
    secondLiveRows (keptBlock slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK keep)=
    secondLiveRows (fun q=>modifiedDatumBlock
      (familyDatum slots s modifier R seed hseed hz₁ hz₂ W K Tsec (fun _=>Z) (fun _=>ξ) hK keep q)
      (modifier q.1)) := rfl

/-- Inclusion drops only the original complete-block proof and the kept-row
membership proof. Label, both rays and the actual ring row are unchanged. -/
def originalRow
    (r : secondLiveRows (keptBlock slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK keep)) :
    secondLiveRows (jointBlock slots s modifier R seed K Tsec Z ξ hseed hz₁ hz₂ hK) := by
  let q:=completeIndex slots s modifier R seed K Tsec Z ξ W r.val.1
  let z : (jointBlock slots s modifier R seed K Tsec Z ξ hseed hz₁ hz₂ hK q).rows :=
    ⟨r.val.2.2.2.val,(Finset.mem_filter.mp (Finset.mem_filter.mp r.val.2.2.2.property).1).1⟩
  refine ⟨⟨q,r.val.2.1,r.val.2.2.1,z⟩,?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp r.property).2⟩

theorem original_row_injective :
    Function.Injective (originalRow slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK keep) := by
  intro r t h
  apply Subtype.ext
  have hl : r.val.1=t.val.1 := complete_index_injective slots s modifier R seed K Tsec Z ξ W
    (congrArg (fun q=>q.val.1) h)
  rcases r with ⟨⟨l,χr,ψr,zr⟩,hr⟩
  rcases t with ⟨⟨m,χt,ψt,zt⟩,ht⟩
  dsimp only at hl
  subst m
  have hc : χr=χt := congrArg (fun q=>q.val.2.1) h
  have hp : ψr=ψt := congrArg (fun q=>q.val.2.2.1) h
  have hz : zr=zt := Subtype.ext (congrArg (fun q=>q.val.2.2.2.val) h)
  subst χt ψt zt
  rfl

/-- The original first-label/seed pair and both ray labels survive exactly. -/
theorem original_row_coordinates
    (r : secondLiveRows (keptBlock slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK keep)) :
    let r₀:=originalRow slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK keep r
    (r₀.val.1.1,seed r₀.val.1.1,r₀.val.2.1,r₀.val.2.2.1,r₀.val.2.2.2.val)=
      (r.val.1.1,seed r.val.1.1,r.val.2.1,r.val.2.2.1,r.val.2.2.2.val) := rfl

theorem original_row_encoded (first : Label→FirstSourceLabel)
    (r : secondLiveRows (keptBlock slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK keep)) :
    secondEncodedRow (jointBlock slots s modifier R seed K Tsec Z ξ hseed hz₁ hz₂ hK)
      (fun q=>first q.1) (originalRow slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK keep r)=
    secondEncodedRow (keptBlock slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK keep)
      (fun q=>first q.1) r := rfl

/-- A full-family nonzero first frequency transfers without a new zero gate. -/
theorem original_row_signed_key (first : Label→FirstSourceLabel) (left reflected : Bool)
    (u₀ : O) (unit : FirstSourceLabel→O)
    (hf : ∀r : secondLiveRows (jointBlock slots s modifier R seed K Tsec Z ξ hseed hz₁ hz₂ hK),
      jointFirstFrequency left u₀ unit (secondEncodedRow _ (fun q=>first q.1) r)≠0)
    (r : secondLiveRows (keptBlock slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK keep)) :
    let r₀:=originalRow slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK keep r
    let key₀:=secondEncodedNonzeroRow (jointBlock slots s modifier R seed K Tsec Z ξ hseed hz₁ hz₂ hK)
      (fun q=>first q.1) r₀ left u₀ unit (hf r₀)
    let key:=secondEncodedNonzeroRow (keptBlock slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK keep)
      (fun q=>first q.1) r left u₀ unit (hf r₀)
    (if reflected then reflectedNonzeroJointLabel key₀ else key₀)=
      (if reflected then reflectedNonzeroJointLabel key else key) := rfl

end
end QRH.Record1252270103Source.Admission.SelectedSecondFibers
#print axioms QRH.Record1252270103Source.Admission.SelectedSecondFibers.complete_index_injective
#print axioms QRH.Record1252270103Source.Admission.SelectedSecondFibers.kept_live_rows_modified
#print axioms QRH.Record1252270103Source.Admission.SelectedSecondFibers.original_row_injective
#print axioms QRH.Record1252270103Source.Admission.SelectedSecondFibers.original_row_coordinates
#print axioms QRH.Record1252270103Source.Admission.SelectedSecondFibers.original_row_encoded
#print axioms QRH.Record1252270103Source.Admission.SelectedSecondFibers.original_row_signed_key
