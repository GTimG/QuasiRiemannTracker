/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0.
The native residual and complete physical operators remain literal. -/
import Candidate.Research.RecursiveAffine.NativePhysicalSelection
import Candidate.Research.RecursiveAffine.ActualReturnShift
import Candidate.Research.RecursiveAffine.LowPhysical.NativeResidualShells

set_option autoImplicit false
set_option maxHeartbeats 550000
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondEnergySplit
open CenteredMomentSectorLocalization CenteredMomentCommonAllocationSum
open CenteredMomentSecondCanonicalScalar CenteredMomentCommonPairedSource
open CenteredMomentSourceLiveColumn CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional LocalMoment CenteredMomentSecondHeightFamily
open CenteredMomentSourceMass CenteredMomentEligibleEnergy CenteredMomentChildRows
open CenteredMomentCommonHeightEnvelope CenteredMomentSecondInputCapacitySource
open CenteredMomentCommonLinearNormalization CenteredMomentWholeDivisorShell
open CenteredMomentLogDyadic Cycle153SourceReturn Cycle153LowPhysical

variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M ≤ H}
variable {Depth : Type} [Fintype Depth] {junction : Depth→ℝ} {Base : Depth→Type}
variable {base : (d : Depth)→Character→Base d→Character}

private theorem uniform_squarefree_projector_shells {Label : Type} [Fintype Label]
    (Ds : Label→Finset (Ideal O)) :
    selectedShells (sharedProjectors (fun r=>(Ds r).filter Squarefree))=
      selectedShells (sharedProjectors Ds) := by
  have hlive : live (sharedProjectors (fun r=>(Ds r).filter Squarefree))=
      live (sharedProjectors Ds) := by
    ext D
    simp only [mem_live,sharedProjectors,Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_filter]
    constructor
    · rintro ⟨⟨r,hr,_⟩,hm⟩
      exact ⟨⟨r,hr⟩,hm⟩
    · rintro ⟨⟨r,hr⟩,hm⟩
      exact ⟨⟨r,hr,squarefree_of_moebius_ne_zero D hm⟩,hm⟩
  exact congrArg (fun S=>S.image normKey) hlive

theorem eventual_actual_residual_shell_forest_uniform_metadata
    (N : ℕ) (U eps epsUnion : ℝ) (hU : 0≤ U) (heps : 0≤ eps) (hUnion : 0< epsUnion) :
    ∃Cu : ℝ,0< Cu ∧ ∀ᶠ Z : ℝ in Filter.atTop,1< Z ∧
    ∀(eta : Character)(Bnorm T : ℝ)(root : O),
    ∀{Label : Type}[Fintype Label](second : Bool)(datum : Label→SecondInputDatum alpha),
    (∀r,Fintype.card (datum r).slots≤ N) →
    (∀r i I,I∈(datum r).input.pools i→(I.absNorm:ℝ)≤ Z^U) →
    ∀(coefficient : Label→ℝ)(ray : Label→RayFourExpansion.RayCharacter)(height : Label→ℝ)
      (zs : Label→Finset O)(rowWeight : Label→O→ℝ)(oldBound sourceConstant : ℝ),
    (∀r,0≤ coefficient r) → (∀r z,z∈zs r→0≤ rowWeight r z) → 0≤ oldBound → 0≤ sourceConstant →
    ∀(Trace : ℤ→DepthReturnedFamily M H hH junction Base base eta Z Bnorm T root→Prop),
    (∀n∈selectedShells (sharedProjectors (fun r=>(datum r).block.divisors.filter Squarefree)),
      ∃F : DepthReturnedFamily M H hH junction Base base eta Z Bnorm T root,
        Trace n F ∧
        (∑r,∑D∈shell (sharedProjectors (fun r=>(datum r).block.divisors.filter Squarefree)) n,
          nativeResidualCost second datum coefficient ray height zs rowWeight r D)≤
          (oldBound+sourceConstant*F.value)*(2*dyadicScale n)^(3*eps)) →
    ∃F : DepthReturnedFamily M H hH junction Base base eta Z Bnorm T root,
      ((F.value=0 ∧ selectedShells (sharedProjectors (fun r=>(datum r).block.divisors.filter Squarefree))=∅) ∨
        ∃n,n∈selectedShells (sharedProjectors (fun r=>(datum r).block.divisors.filter Squarefree)) ∧ Trace n F) ∧
      (∑r,∑D∈(datum r).block.divisors.filter Squarefree,
        nativeResidualCost second datum coefficient ray height zs rowWeight r D)≤
        (oldBound+sourceConstant*F.value)*(Cu*Z^(epsUnion+3*(((N:ℝ)+2)*U)*eps)) := by
  obtain ⟨Cu,hCu,hpaid⟩ := actual_second_low_weighted_shells (α:=alpha) N U eps epsUnion hU heps hUnion
  refine ⟨Cu,hCu,?_⟩
  filter_upwards [hpaid] with Z hz
  refine ⟨hz.1,?_⟩
  intro eta Bnorm T root Label _ second datum hN hpool coefficient ray height zs rowWeight oldBound sourceConstant
    hcoefficient hweight hold hconstant Trace hlocal
  obtain ⟨F,hF,hcost⟩ := actual_residual_shell_forest second datum coefficient ray height zs rowWeight
    eps oldBound sourceConstant (zero_lt_one.trans hz.1).le hcoefficient hweight hconstant Trace hlocal
  refine ⟨F,hF,hcost.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (add_nonneg hold (mul_nonneg hconstant (F.value_nonneg (zero_lt_one.trans hz.1).le)))
  rw [uniform_squarefree_projector_shells]
  exact hz.2 datum hN hpool

variable [Cycle63.AffineLedger] in
/-- Compose the actual second-projector union with the actual ray and
buffer operator. Each local receipt is the literal one-shell sum on the
native source rows. The shell power shifts terminal count exponents and
native losses by the SAME amount, preserving all raw edge weights. The
fixed shell coefficient stays outside the return. No moving power is
hidden in a coefficient chosen before Z, and no seed reciprocal is
applied to the returned family. -/
theorem eventual_complete_low_shells_forest_uniform_metadata
    (N : ℕ) (U eps epsUnion : ℝ) (hU : 0 ≤ U) (heps : 0 ≤ eps) (hUnion : 0<epsUnion) :
    ∃(Cu : ℝ)(_hCu : 0<Cu),∀ᶠ Z : ℝ in atTop,1<Z ∧
    ∀(eta : Character)(Bnorm T : ℝ)(root : O),
    ∀{Label : Type}[Fintype Label](hZbase : 1<Z)(supply ap : ℝ)(second : Bool)
      (datum : Label→SecondInputDatum alpha)(coefficient : Label→ℝ)(t u e : ℝ)
      (select : (r : Label)→(chi psi : RayFourExpansion.RayCharacter)→
        mainLowSourceRows second (datum r) (fun _=>True)→BufferIndex e),
    (∀r,Fintype.card (datum r).slots ≤ N) →
    (∀r i I,I∈(datum r).input.pools i→(I.absNorm:ℝ) ≤ Z^U) →
    (∀r,0 ≤ coefficient r*(datum r).K*
      normalizer (datum r).C (datum r).D (datum r).inactive) →
    ∀(oldBound sourceConstant : ℝ),0 ≤ oldBound → 0 ≤ sourceConstant →
    0<lowerFactor N supply ap →
    (∀r chi psi p z,z∈mainLowPaymentRows (mainLowSourceRows second (datum r) (fun _=>True))
      (select r chi psi) p→1 ≤ p.1.val) →
    ∀(Trace : RayFourExpansion.RayCharacter→RayFourExpansion.RayCharacter→BufferIndex e→ℤ→
      DepthReturnedFamily M H hH junction Base base eta Z Bnorm T root→Prop),
    (∀(chi psi : RayFourExpansion.RayCharacter)(p : BufferIndex e),1 ≤ p.1.val →
      ∀n∈selectedShells (sharedProjectors (fun r=>(datum r).block.divisors.filter Squarefree)),
      ∃F : DepthReturnedFamily M H hH junction Base base eta Z Bnorm T root,
        Trace chi psi p n F ∧
        (∑r,∑D∈shell (sharedProjectors (fun r=>(datum r).block.divisors.filter Squarefree)) n,
          nativeResidualCost second datum
            (fun r=>coefficient r*(datum r).K*normalizer (datum r).C (datum r).D (datum r).inactive)
            (fun _=>if second then psi⁻¹ else chi)
            (fun r=>(datum r).input.t+2*Real.pi*(u-(if second then -t else t)))
            (fun r=>mainLowPaymentRows (mainLowSourceRows second (datum r) (fun _=>True))
              (select r chi psi) p) (fun _ _=>1) r D) ≤
          (oldBound+sourceConstant*F.value)*(2*dyadicScale n)^(3*eps)) →
    ∃F : DepthReturnedFamily M H hH junction Base base eta Z Bnorm T root,
      (F=emptyReturnedForest ∨ ∃(chi psi : RayFourExpansion.RayCharacter)(p : BufferIndex e)(n : ℤ)
        (Fraw : DepthReturnedFamily M H hH junction Base base eta Z Bnorm T root),
        1 ≤ p.1.val ∧ n∈selectedShells (sharedProjectors
          (fun r=>(datum r).block.divisors.filter Squarefree)) ∧ Trace chi psi p n Fraw ∧
        F=shiftedReturnedForest Fraw (epsUnion+3*(((N:ℝ)+2)*U)*eps)) ∧
      mainLowPhysicalCompleteCost N supply ap second datum coefficient t u select ≤
        (1/lowerFactor N supply ap)*
          ((Fintype.card RayFourExpansion.RayCharacter:ℝ)^2*
            (Fintype.card (BufferIndex e):ℝ)*
              (oldBound*(Cu*Z^(epsUnion+3*(((N:ℝ)+2)*U)*eps))+2*(Cu*sourceConstant)*F.value)) := by
  obtain ⟨Cu,hCu,hresidual⟩ := eventual_actual_residual_shell_forest_uniform_metadata
    (alpha:=alpha) (M:=M) (H:=H) (hH:=hH) (junction:=junction) (Base:=Base)
    (base:=base)
    N U eps epsUnion hU heps hUnion
  refine ⟨Cu,hCu,?_⟩
  filter_upwards [hresidual] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro eta Bnorm T root Label _ hZbase supply ap second datum coefficient t u e select hN hpool hcoefficient
    oldBound sourceConstant hold hsourceConstant hlower hpositive Trace hlocal
  let shellFactor := Cu*Z^(epsUnion+3*(((N:ℝ)+2)*U)*eps)
  have hfactor : 0 ≤ shellFactor := by dsimp only [shellFactor];positivity
  let ReturnedTrace := fun chi psi p
      (F : DepthReturnedFamily M H hH junction Base base eta Z Bnorm T root)=>
    F.value=0 ∨ ∃(n : ℤ) (Fraw : DepthReturnedFamily M H hH junction Base base eta Z Bnorm T root),
      n∈selectedShells (sharedProjectors (fun r=>(datum r).block.divisors.filter Squarefree)) ∧
      Trace chi psi p n Fraw ∧ F=shiftedReturnedForest Fraw (epsUnion+3*(((N:ℝ)+2)*U)*eps)
  have hbuffer : ∀(chi psi : RayFourExpansion.RayCharacter)(p : BufferIndex e),1 ≤ p.1.val →
      ∃F : DepthReturnedFamily M H hH junction Base base eta Z Bnorm T root,
        ReturnedTrace chi psi p F ∧
        nativeBufferedColumnCost second datum coefficient t u e select chi psi p ≤
          oldBound*shellFactor+(Cu*sourceConstant)*F.value := by
    intro chi psi p hp
    let ray := fun _ : Label=>if second then psi⁻¹ else chi
    let height := fun r : Label=>(datum r).input.t+2*Real.pi*(u-(if second then -t else t))
    let zs := fun r : Label=>mainLowPaymentRows (mainLowSourceRows second (datum r) (fun _=>True))
      (select r chi psi) p
    let coeff := fun r : Label=>coefficient r*(datum r).K*
      normalizer (datum r).C (datum r).D (datum r).inactive
    obtain ⟨Fraw,hraw,hbound⟩ := hZ.2 eta Bnorm T root second datum hN hpool coeff ray height zs (fun _ _=>1)
      oldBound sourceConstant hcoefficient (fun _ _ _=>by norm_num) hold hsourceConstant
      (Trace chi psi p) (hlocal chi psi p hp)
    let F := shiftedReturnedForest Fraw (epsUnion+3*(((N:ℝ)+2)*U)*eps)
    have hvalue : F.value=Z^(epsUnion+3*(((N:ℝ)+2)*U)*eps)*Fraw.value :=
      shiftedReturnedForest_value Fraw _ (zero_lt_one.trans hZ.1)
    refine ⟨F,?_,?_⟩
    · cases hraw with
      | inl hzero =>
        left
        rw [hvalue,hzero.1,mul_zero]
      | inr htrace =>
        right
        obtain ⟨n,hn,ht⟩ := htrace
        exact ⟨n,Fraw,hn,ht,rfl⟩
    · have hcost : nativeBufferedColumnCost second datum coefficient t u e select chi psi p=
          ∑r,∑D∈(datum r).block.divisors.filter Squarefree,
            nativeResidualCost second datum coeff ray height zs (fun _ _=>1) r D := by
        unfold nativeBufferedColumnCost nativeResidualCost
        simp only [one_mul]
        dsimp only [coeff,ray,height,zs]
        cases second <;> rfl
      rw [hcost,hvalue]
      apply hbound.trans_eq
      change (oldBound+sourceConstant*Fraw.value)*(Cu*Z^(epsUnion+3*(((N:ℝ)+2)*U)*eps))=
        oldBound*(Cu*Z^(epsUnion+3*(((N:ℝ)+2)*U)*eps))+
          (Cu*sourceConstant)*(Z^(epsUnion+3*(((N:ℝ)+2)*U)*eps)*Fraw.value)
      ring
  obtain ⟨F,htrace,hbound⟩ := actual_complete_low_choose_forest N supply ap second datum coefficient
    t u e select ReturnedTrace (oldBound*shellFactor) (Cu*sourceConstant)
    (zero_lt_one.trans hZ.1).le hlower (mul_nonneg hold hfactor) (mul_nonneg hCu.le hsourceConstant)
    hpositive hbuffer
  by_cases hz : F.value=0
  · refine ⟨emptyReturnedForest,Or.inl rfl,?_⟩
    simpa only [emptyReturnedForest_value,hz] using hbound
  · refine ⟨F,?_,hbound⟩
    cases htrace with
    | inl hempty=>exact False.elim (hz (by rw [hempty];exact emptyReturnedForest_value))
    | inr ht=>
      obtain ⟨chi,psi,p,hp,hF⟩ := ht
      cases hF with
      | inl hzero=>exact False.elim (hz hzero)
      | inr ht=>
        obtain ⟨n,Fraw,hn,hraw,heq⟩ := ht
        exact Or.inr ⟨chi,psi,p,n,Fraw,hp,hn,hraw,heq⟩

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.eventual_actual_residual_shell_forest_uniform_metadata
#print axioms OAI.SevenEighths.Cycle153RegionalLow.eventual_complete_low_shells_forest_uniform_metadata
