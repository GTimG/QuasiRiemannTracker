/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact source codes for modified retained blocks. No ordinary active source is used. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalSecondRetainedData
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.SecondLabelDisintegration
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.ModifiedFibers
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve Cycle61Moment Cycle61InitialMass
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentFirstSectors
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentFirstDiscardedEnergy
open Record1252270103Second High.GlobalPhysical
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq ι:=Classical.decEq _

/-- Literal ideal pair, partition and four actual dyads. -/
def modifiedSecondBlockCode {ι:Type*} [Fintype ι] (s:Input ι) (modifier:Tuple ι→ℂ)
    (R seed:Ideal O) (K Tsec Z ξ:ℝ) (q:BlockIndex s modifier R seed K Tsec Z ξ) : SecondBlockCode :=
  ⟨q.1.val.val,q.2.1,fun i=>(q.2.2 i:ℤ)⟩

theorem modified_second_block_code_injective {ι:Type*} [Fintype ι] (s:Input ι) (modifier:Tuple ι→ℂ)
    (R seed:Ideal O) (K Tsec Z ξ:ℝ) :
    Function.Injective (modifiedSecondBlockCode s modifier R seed K Tsec Z ξ) := by
  rintro ⟨p,U,n⟩ ⟨p',U',n'⟩ h
  have hp:p.val.val=p'.val.val:=congrArg Sigma.fst h
  have hp':p=p':=Subtype.ext (Subtype.ext hp)
  cases hp'
  have ht:=eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have hU:U=U':=congrArg Prod.fst ht
  cases hU
  have hn:=congrArg Prod.snd ht
  have hn':n=n':=funext (fun i=>Subtype.ext (congrFun hn i))
  cases hn'
  rfl

variable {α Label Aux:Type*} [Fintype α]
variable (slots:Label→Finset α) (s:∀l,Input (slots l)) (modifier:∀l,Tuple (slots l)→ℂ)
    (R seed:Label→Ideal O) (K Tsec:Label→ℝ) (Z ξ:ℝ)

abbrev JointIndex := (l:Label)×BlockIndex (s l) (modifier l) (R l) (seed l) (K l) (Tsec l) Z ξ

/-- All first-stage choices not determined by (first,seed) must remain in aux. -/
theorem modified_joint_block_code_injective_aux (first:Label→FirstSourceLabel) (aux:Label→Aux)
    (hfirst:Function.Injective (fun l=>(first l,aux l,seed l))) :
    Function.Injective (fun q:JointIndex slots s modifier R seed K Tsec Z ξ=>
      (first q.1,(aux q.1,seed q.1),modifiedSecondBlockCode (s q.1) (modifier q.1)
        (R q.1) (seed q.1) (K q.1) (Tsec q.1) Z ξ q.2)) := by
  rintro ⟨l,q⟩ ⟨m,v⟩ h
  have hf:first l=first m:=congrArg Prod.fst h
  have ha:(aux l,seed l)=(aux m,seed m):=congrArg (fun x=>x.2.1) h
  have hl:l=m:=hfirst (Prod.ext hf ha)
  cases hl
  have hq:q=v:=modified_second_block_code_injective (s l) (modifier l) (R l) (seed l)
    (K l) (Tsec l) Z ξ (congrArg (fun x=>x.2.2) h)
  cases hq
  rfl

/-- At a genuinely selected/fixed first-allocation boundary only seed remains auxiliary. -/
theorem modified_joint_block_code_injective (first:Label→FirstSourceLabel)
    (hfirst:Function.Injective (fun l=>(first l,seed l))) :
    Function.Injective (fun q:JointIndex slots s modifier R seed K Tsec Z ξ=>
      (first q.1,seed q.1,modifiedSecondBlockCode (s q.1) (modifier q.1)
        (R q.1) (seed q.1) (K q.1) (Tsec q.1) Z ξ q.2)) := by
  rintro ⟨l,q⟩ ⟨m,v⟩ h
  have hf:first l=first m:=congrArg Prod.fst h
  have hs:seed l=seed m:=congrArg (fun x=>x.2.1) h
  have hl:l=m:=hfirst (Prod.ext hf hs)
  cases hl
  have hq:q=v:=modified_second_block_code_injective (s l) (modifier l) (R l) (seed l)
    (K l) (Tsec l) Z ξ (congrArg (fun x=>x.2.2) h)
  cases hq
  rfl

variable (hseed:∀l,Squarefree (seed l)) (hz₁:∀l,(s l).W₁ 0=0) (hz₂:∀l,(s l).W₂ 0=0)
    (hK:∀l,0<K l)

def jointDatum (q:JointIndex slots s modifier R seed K Tsec Z ξ):SecondInputDatum α :=
  modifiedRetainedDatum (slots q.1) (s q.1) (modifier q.1) (R q.1) (seed q.1)
    (hseed q.1) (hz₁ q.1) (hz₂ q.1) (K q.1) (Tsec q.1) Z ξ (hK q.1) q.2

def jointBlock (q:JointIndex slots s modifier R seed K Tsec Z ξ):SecondBlockSource :=
  modifiedDatumBlock (jointDatum slots s modifier R seed K Tsec Z ξ hseed hz₁ hz₂ hK q) (modifier q.1)

lemma joint_block_code (q:JointIndex slots s modifier R seed K Tsec Z ξ) :
    secondBlockCode (jointBlock slots s modifier R seed K Tsec Z ξ hseed hz₁ hz₂ hK q)=
      modifiedSecondBlockCode (s q.1) (modifier q.1) (R q.1) (seed q.1)
        (K q.1) (Tsec q.1) Z ξ q.2 := rfl

theorem modified_joint_source_keys_aux (first:Label→FirstSourceLabel) (aux:Label→Aux)
    (hfirst:Function.Injective (fun l=>(first l,aux l,seed l))) :
    Function.Injective (fun q:JointIndex slots s modifier R seed K Tsec Z ξ=>
      (first q.1,(aux q.1,seed q.1),secondBlockCode
        (jointBlock slots s modifier R seed K Tsec Z ξ hseed hz₁ hz₂ hK q))) :=
  modified_joint_block_code_injective_aux slots s modifier R seed K Tsec Z ξ first aux hfirst

theorem modified_joint_source_keys (first:Label→FirstSourceLabel)
    (hfirst:Function.Injective (fun l=>(first l,seed l))) :
    Function.Injective (fun q:JointIndex slots s modifier R seed K Tsec Z ξ=>
      (first q.1,seed q.1,secondBlockCode
        (jointBlock slots s modifier R seed K Tsec Z ξ hseed hz₁ hz₂ hK q))) :=
  modified_joint_block_code_injective slots s modifier R seed K Tsec Z ξ first hfirst

/-- The actual modified complete-block nonzero gate supplies the canonical
partition gate; no ordinary coefficient or ordinary block value is substituted. -/
theorem modified_original_nonzero_inactive (W:𝓢(ℝ,ℂ))
    (q:JointIndex slots s modifier R seed K Tsec Z ξ)
    (hn:(jointBlock slots s modifier R seed K Tsec Z ξ hseed hz₁ hz₂ hK q).value W≠0) :
    q.2.2.1∈inactiveSubsets q.2.1.val.val.1 q.2.1.val.val.2 :=
  second_block_nonzero_inactive
    (jointBlock slots s modifier R seed K Tsec Z ξ hseed hz₁ hz₂ hK q) W hn

lemma joint_seed_divides (q:JointIndex slots s modifier R seed K Tsec Z ξ) :
    seed q.1∣(jointBlock slots s modifier R seed K Tsec Z ξ hseed hz₁ hz₂ hK q).C ∧
    seed q.1∣(jointBlock slots s modifier R seed K Tsec Z ξ hseed hz₁ hz₂ hK q).D := by
  have h:=modified_retained_seed_and_caps (slots q.1) (s q.1) (modifier q.1) (R q.1) (seed q.1)
    (hseed q.1) (hz₁ q.1) (hz₂ q.1) (K q.1) (Tsec q.1) Z ξ (hK q.1) q.2
  exact ⟨h.1,h.2.1⟩

end
end QRH.Record1252270103Source.Admission.ModifiedFibers
#print axioms QRH.Record1252270103Source.Admission.ModifiedFibers.modified_second_block_code_injective
#print axioms QRH.Record1252270103Source.Admission.ModifiedFibers.modified_joint_source_keys_aux
#print axioms QRH.Record1252270103Source.Admission.ModifiedFibers.modified_joint_source_keys
#print axioms QRH.Record1252270103Source.Admission.ModifiedFibers.modified_original_nonzero_inactive
