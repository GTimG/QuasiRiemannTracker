/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Genuine modified-row fiber bounds, keeping all auxiliary multiplicities explicit. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.ModifiedFibersCode
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.ModifiedFibers
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve Cycle61Moment Cycle61InitialMass RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum
open CenteredMomentAllocationCost IdealMobiusDivisorSum
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq ι:=Classical.decEq _

/-- These are precisely the labels forgotten by the signed joint-row encoding. -/
def rowAux {Label Aux:Type*} [Fintype Label] (s:Label→SecondBlockSource) (aux:Label→Aux)
    (r:secondLiveRows s) : Aux×(Fin 4→ℤ)×RayCharacter×RayCharacter :=
  (aux r.val.1,(s r.val.1).dyad,r.val.2.1,r.val.2.2.1)

/-- Fixing genuine auxiliaries, all dyads and both ray labels makes the
original signed encoded key injective. No injection of the whole family is asserted. -/
theorem fixed_aux_encoded_injective {Label Aux:Type*} [Fintype Label]
    (s:Label→SecondBlockSource) (first:Label→FirstSourceLabel) (aux:Label→Aux)
    (hlabel:Function.Injective (fun l=>(first l,aux l,secondBlockCode (s l))))
    (a:Aux×(Fin 4→ℤ)×RayCharacter×RayCharacter) :
    Function.Injective (fun r:{r:secondLiveRows s // rowAux s aux r=a}=>
      secondEncodedRow s first r.val) := by
  intro r t h
  apply Subtype.ext
  apply actual_second_row_key_injective s first aux hlabel
  exact Prod.ext h (r.property.trans t.property.symm)

section Actual
variable {α Label Aux:Type*} [Fintype α] [Fintype Label]
variable (slots:Label→Finset α) (s:∀l,Input (slots l)) (modifier:∀l,Tuple (slots l)→ℂ)
    (R seed:Label→Ideal O) (K Tsec:Label→ℝ) (Z ξ:ℝ)
    (hseed:∀l,Squarefree (seed l)) (hz₁:∀l,(s l).W₁ 0=0) (hz₂:∀l,(s l).W₂ 0=0)
    (hK:∀l,0<K l) (first:Label→FirstSourceLabel) (aux:Label→Aux)
    (hfirst:Function.Injective (fun l=>(first l,aux l,seed l)))
include hfirst
local notation "Blocks"=>jointBlock slots s modifier R seed K Tsec Z ξ hseed hz₁ hz₂ hK
local notation "First"=>(fun q:JointIndex slots s modifier R seed K Tsec Z ξ=>first (Sigma.fst q))
local notation "Auxiliary"=>(fun q:JointIndex slots s modifier R seed K Tsec Z ξ=>(aux (Sigma.fst q),seed (Sigma.fst q)))

theorem modified_joint_row_key_injective :
    Function.Injective (fun r:secondLiveRows Blocks=>
      (secondEncodedRow Blocks First r,rowAux Blocks Auxiliary r)) :=
  actual_second_row_key_injective Blocks First Auxiliary
    (modified_joint_source_keys_aux slots s modifier R seed K Tsec Z ξ hseed hz₁ hz₂ hK first aux hfirst)

theorem modified_fixed_aux_encoded_injective
    (a:(Aux×Ideal O)×(Fin 4→ℤ)×RayCharacter×RayCharacter) :
    Function.Injective (fun r:{r:secondLiveRows Blocks // rowAux Blocks Auxiliary r=a}=>
      secondEncodedRow Blocks First r.val) :=
  fixed_aux_encoded_injective Blocks First Auxiliary
    (modified_joint_source_keys_aux slots s modifier R seed K Tsec Z ξ hseed hz₁ hz₂ hK first aux hfirst) a

/-- The fiber counts the actual auxiliary set, projector set, four dyads
and two rays. It does not pay a source-pool cardinality or residual projector. -/
theorem modified_row_fiber_card (j:JointSourceLabel) (A:Finset Aux)
    (P:Finset (Ideal O)) (N:Finset (Fin 4→ℤ))
    (haux:∀r:secondLiveRows Blocks,secondEncodedRow Blocks First r=j→aux r.val.1.1∈A)
    (hprojector:∀r:secondLiveRows Blocks,secondEncodedRow Blocks First r=j→seed r.val.1.1∈P)
    (hdyad:∀r:secondLiveRows Blocks,secondEncodedRow Blocks First r=j→(Blocks r.val.1).dyad∈N) :
    (Finset.univ.filter (fun r:secondLiveRows Blocks=>secondEncodedRow Blocks First r=j)).card≤
      A.card*P.card*N.card*(Fintype.card RayCharacter)^2 := by
  have h:=actual_second_row_fiber_card Blocks First Auxiliary
    (modified_joint_source_keys_aux slots s modifier R seed K Tsec Z ξ hseed hz₁ hz₂ hK first aux hfirst)
    j (A×ˢP) N (fun r hr=>Finset.mem_product.mpr ⟨haux r hr,hprojector r hr⟩) hdyad
  simpa only [Finset.card_product] using h
end Actual

/-- Uniform divisor subpower for the FIRST projector, retaining the full
remaining auxiliary set, four dyads and both rays. Constants precede all data. -/
theorem projector_aux_fiber_bound (B ε:ℝ) (hB:0≤B) (hε:0<ε) :
    ∃K₀:ℝ,0<K₀ ∧ ∀Z:ℝ,1≤Z→∀{Label Aux:Type*} [Fintype Label]
      (s:Label→SecondBlockSource) (first:Label→FirstSourceLabel) (seed:Label→Ideal O) (aux:Label→Aux),
      Function.Injective (fun l=>(first l,(aux l,seed l),secondBlockCode (s l)))→
      (∀l,Squarefree (seed l))→(∀l,seed l∣(s l).C ∧ seed l∣(s l).D)→
      ∀(left:Bool) (u₀:O) (unit:FirstSourceLabel→O) (j:NonzeroJointSourceLabel left u₀ unit)
        (A:Finset Aux) (N:Finset (Fin 4→ℤ)),
      ((Ideal.span {jointSourceRow left u₀ unit j.val}).absNorm:ℝ)≤Z^B→
      (∀r:secondLiveRows s,secondEncodedRow s first r=j.val→aux r.val.1∈A)→
      (∀r:secondLiveRows s,secondEncodedRow s first r=j.val→(s r.val.1).dyad∈N)→
      ((Finset.univ.filter (fun r:secondLiveRows s=>secondEncodedRow s first r=j.val)).card:ℝ)≤
        (K₀*Z^ε)*A.card*N.card*(Fintype.card RayCharacter:ℝ)^2 := by
  obtain ⟨K₀,hK₀,hbound⟩:=first_projector_small_power B ε hB hε
  refine ⟨K₀,hK₀,?_⟩
  intro Z hZ Label Aux inst s first seed aux hinj hseed hdiv left u₀ unit j A N hnorm haux hdyad
  let P:=(idealDivisors (Ideal.span {jointSourceRow left u₀ unit j.val})).filter Squarefree
  have hI:Ideal.span {jointSourceRow left u₀ unit j.val}≠0:=Ideal.span_singleton_eq_bot.not.mpr j.property
  have hmem (r:secondLiveRows s) (hr:secondEncodedRow s first r=j.val) : seed r.val.1∈P := by
    have hd:=actual_second_encoded_first_projector s first r left u₀ unit (seed r.val.1)
      (hseed r.val.1) (hdiv r.val.1).1 (hdiv r.val.1).2
    rw [hr] at hd
    exact Finset.mem_filter.mpr ⟨(mem_idealDivisors hI).mpr hd,hseed r.val.1⟩
  have hcard:=actual_second_row_fiber_card s first (fun l=>(aux l,seed l)) hinj j.val (A×ˢP) N
    (fun r hr=>Finset.mem_product.mpr ⟨haux r hr,hmem r hr⟩) hdyad
  have hsmall:(P.card:ℝ)≤K₀*Z^ε:=hbound Z hZ _ j.property hnorm P
    (fun L hL=>(Finset.mem_filter.mp hL).2)
    (fun L hL=>(mem_idealDivisors hI).mp (Finset.mem_filter.mp hL).1)
  have hc:((Finset.univ.filter (fun r:secondLiveRows s=>secondEncodedRow s first r=j.val)).card:ℝ)≤
      (A.card:ℝ)*P.card*N.card*(Fintype.card RayCharacter:ℝ)^2 := by
    exact_mod_cast (show _≤A.card*P.card*N.card*(Fintype.card RayCharacter)^2 by
      simpa only [Finset.card_product] using hcard)
  apply hc.trans
  have hh:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg A.card))
      (Nat.cast_nonneg N.card)) (sq_nonneg (Fintype.card RayCharacter:ℝ))
  convert hh using 1; ring

/-- If first allocations remain auxiliary, their genuine complete cardinality
has a uniform small-power bound from the actual common-ideal norm cap. -/
theorem allocation_auxiliary_small_power (N:ℕ) (B ε:ℝ) (hB:0≤B) (hε:0<ε) :
    ∃K₀:ℝ,0<K₀ ∧ ∀Z:ℝ,1≤Z→∀{ι:Type*} [Fintype ι],Fintype.card ι≤N→
      ∀(S:(ι⊕Fin 2)→Finset (Ideal O)) (C:Ideal O),C≠0→(C.absNorm:ℝ)≤Z^B→
        ((actualAllocations S C).card:ℝ)≤K₀*Z^ε := by
  let δ:=ε/(B+1)
  have hδ:0<δ:=div_pos hε (by positivity)
  obtain ⟨K₀,hK₀,hbound⟩:=actualAllocations_uniform_small_power (N+2) δ hδ
  refine ⟨K₀,hK₀,?_⟩
  intro Z hZ ι inst hι S C hC hnorm
  have hcard:Fintype.card (ι⊕Fin 2)≤N+2 := by
    simpa only [Fintype.card_sum,Fintype.card_fin] using Nat.add_le_add_right hι 2
  have hexp:B*δ≤ε := by
    have he:δ*(B+1)=ε := by dsimp [δ];field_simp
    nlinarith
  apply (hbound hcard S C hC).trans
  apply (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hnorm hδ.le) hK₀.le).trans
  rw [←Real.rpow_mul (zero_le_one.trans hZ)]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hexp) hK₀.le

end
end QRH.Record1252270103Source.Admission.ModifiedFibers
#print axioms QRH.Record1252270103Source.Admission.ModifiedFibers.fixed_aux_encoded_injective
#print axioms QRH.Record1252270103Source.Admission.ModifiedFibers.modified_joint_row_key_injective
#print axioms QRH.Record1252270103Source.Admission.ModifiedFibers.modified_fixed_aux_encoded_injective
#print axioms QRH.Record1252270103Source.Admission.ModifiedFibers.modified_row_fiber_card
#print axioms QRH.Record1252270103Source.Admission.ModifiedFibers.projector_aux_fiber_bound
#print axioms QRH.Record1252270103Source.Admission.ModifiedFibers.allocation_auxiliary_small_power
