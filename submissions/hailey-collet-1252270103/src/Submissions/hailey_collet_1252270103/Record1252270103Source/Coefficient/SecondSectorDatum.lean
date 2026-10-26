/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Restrict only the actual retained second datum's rows. Every coefficient,
arithmetic field and character family remains the original one. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalSecondRetainedData
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.SecondSectorDatum
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentSecondLiveBlock CenteredMomentSecondPhysicalBlock
open CenteredMomentSectorLocalization Cycle61InitialMass Record1252270103Second
open QRH.Record1252270103Source.High.GlobalPhysical
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
local instance secondSectorDatumSumDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def restrictDatum (d : SecondInputDatum α) (keep : O→Prop) : SecondInputDatum α :=
  { d with
    rows := (liveRows d.C d.D d.inactive d.radius d.rows).filter keep
    rows_ne := fun z hz => d.rows_ne z
      (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1 }

/-- The row restriction changes no geometric or arithmetic field. -/
theorem restrictDatum_fields (d : SecondInputDatum α) (keep : O→Prop) :
    (restrictDatum d keep).slots=d.slots ∧
    (restrictDatum d keep).input=d.input ∧
    (restrictDatum d keep).C=d.C ∧ (restrictDatum d keep).D=d.D ∧
    (restrictDatum d keep).R=d.R ∧ (restrictDatum d keep).seed=d.seed ∧
    (restrictDatum d keep).inactive=d.inactive ∧
    (restrictDatum d keep).τ=d.τ ∧ (restrictDatum d keep).radius=d.radius ∧
    (restrictDatum d keep).K=d.K ∧ (restrictDatum d keep).dyad=d.dyad := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

def restrictedRetainedDatum (slots : Finset α) (s : Input slots) (modifier : Tuple slots→ℂ)
    (R seed : Ideal O) (hseed : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (H Tsec Z ξ : ℝ) (hH : 0<H) (q : BlockIndex s modifier R seed H Tsec Z ξ)
    (keep : O→Prop) : SecondInputDatum α :=
  restrictDatum (modifiedRetainedDatum slots s modifier R seed hseed hz₁ hz₂ H Tsec Z ξ hH q) keep

/-- This is the literal selected physical block, with the full modified
coefficient. No nonzero assertion on the selected block is needed. -/
theorem restricted_retained_block (slots : Finset α) (s : Input slots)
    (modifier : Tuple slots→ℂ) (R seed : Ideal O)
    (hseed : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (H Tsec Z ξ : ℝ) (hH : 0<H) (q : BlockIndex s modifier R seed H Tsec Z ξ)
    (keep : O→Prop) (W : 𝓢(ℝ,ℂ)) :
    (modifiedDatumBlock
      (restrictedRetainedDatum slots s modifier R seed hseed hz₁ hz₂ H Tsec Z ξ hH q keep)
      modifier).value W = selectedSecondBlock s modifier R seed W H Tsec Z ξ q keep := rfl

theorem restricted_retained_rows (slots : Finset α) (s : Input slots)
    (modifier : Tuple slots→ℂ) (R seed : Ideal O)
    (hseed : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (H Tsec Z ξ : ℝ) (hH : 0<H) (q : BlockIndex s modifier R seed H Tsec Z ξ)
    (keep : O→Prop) (z : O) :
    z∈(restrictedRetainedDatum slots s modifier R seed hseed hz₁ hz₂ H Tsec Z ξ hH q keep).rows ↔
      z∈liveRows q.1.val.val.1 q.1.val.val.2 q.2.1 (frequencyRadius Tsec Z ξ)
        (Record1252270103Second.blockRows _ _ q.2.1 (frequencyRadius Tsec Z ξ)) ∧ keep z := by
  exact Finset.mem_filter

end
end QRH.Record1252270103Source.SecondSectorDatum
#print axioms QRH.Record1252270103Source.SecondSectorDatum.restrictDatum_fields
#print axioms QRH.Record1252270103Source.SecondSectorDatum.restricted_retained_block
#print axioms QRH.Record1252270103Source.SecondSectorDatum.restricted_retained_rows
