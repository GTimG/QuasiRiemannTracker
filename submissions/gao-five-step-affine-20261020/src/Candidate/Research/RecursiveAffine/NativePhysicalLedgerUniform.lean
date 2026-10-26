/- Actual physical shell operators with a uniform threshold before the regional ledger.
Copyright (c)2026 Zhongpai Gao. Native analytic operators by Hailey Collet. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeUniformPhysicalForest
import Candidate.Research.RecursiveAffine.NativeInnerPhysicalReceipt
import Candidate.Research.RecursiveAffine.NativeRootPhysicalReceipt

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 700000
set_option maxRecDepth 5000
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
open CenteredMomentLogDyadic Cycle153SourceReturn Cycle153LowPhysical Cycle153Reachable Cycle153JointCount
variable {alpha Current : Type} [Fintype alpha] [DecidableEq alpha] [Fintype Current] [DecidableEq Current]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M ≤ H}
variable {Depth : Type} [Fintype Depth] {junction : Depth→ℝ} {Base : Depth→Type}
variable {base : (d : Depth)→Character→Base d→Character}
theorem eventual_complete_low_shells_forest_uniform_all_ledgers
    (N : ℕ) (U eps epsUnion : ℝ) (hU : 0 ≤ U) (heps : 0 ≤ eps) (hUnion : 0<epsUnion) :
    ∃(Cu : ℝ)(_hCu : 0<Cu),∀ᶠ Z : ℝ in atTop,1<Z ∧
    ∀L : Cycle63.AffineLedger,letI : Cycle63.AffineLedger:=L;
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
  intro L
  letI : Cycle63.AffineLedger:=L
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


theorem eventual_actual_inner_physical_receipt_all_ledgers
    (j : Fin 4)(N : ℕ)(U eps epsUnion : ℝ)(hU : 0 ≤ U)(heps : 0 ≤ eps)(hUnion : 0<epsUnion) :
    ∃Cu : ℝ,0<Cu ∧ ∀ᶠ Z : ℝ in atTop,1<Z ∧
    ∀L : Cycle63.AffineLedger,letI : Cycle63.AffineLedger:=L;
    ∀(C : SourceContext (α:=alpha) M H)(node : ReachableNode C j)(hbase : node.localBase=Z)
      (Bsrc : ℝ)(boxes : ℕ→Finset (Fin 4→ℤ)),
    ∀{Label : Type}[Fintype Label](supply ap : ℝ)(second : Bool)
      (datum : Label→SecondInputDatum Current)(coefficient : Label→ℝ)(t u e : ℝ)
      (select : (r : Label)→(chi psi : RayFourExpansion.RayCharacter)→
        mainLowSourceRows second (datum r) (fun _=>True)→BufferIndex e),
    (∀r,Fintype.card (datum r).slots ≤ N) →
    (∀r i I,I∈(datum r).input.pools i→(I.absNorm:ℝ) ≤ Z^U) →
    (∀r,0 ≤ coefficient r*(datum r).K*normalizer (datum r).C (datum r).D (datum r).inactive) →
    ∀(oldBound sourceConstant : ℝ),0 ≤ oldBound → 0 ≤ sourceConstant →
    0<lowerFactor N supply ap →
    (∀r chi psi p z,z∈mainLowPaymentRows (mainLowSourceRows second (datum r) (fun _=>True))
      (select r chi psi) p→1 ≤ p.1.val) →
    (∀(chi psi : RayFourExpansion.RayCharacter)(p : BufferIndex e),1 ≤ p.1.val →
      ∀n∈selectedShells (sharedProjectors (fun r=>(datum r).block.divisors.filter Squarefree)),
      ∃receipt : NativeNodeForestReceipt hH node Bsrc boxes,
        (∀d z,(receipt.family.part d z).loss+
          (epsUnion+3*(((N:ℝ)+2)*U)*eps) ≤ terminalLossCap j) ∧
        (∑r,∑D∈shell (sharedProjectors (fun r=>(datum r).block.divisors.filter Squarefree)) n,
          nativeResidualCost second datum
            (fun r=>coefficient r*(datum r).K*normalizer (datum r).C (datum r).D (datum r).inactive)
            (fun _=>if second then psi⁻¹ else chi)
            (fun r=>(datum r).input.t+2*Real.pi*(u-(if second then -t else t)))
            (fun r=>mainLowPaymentRows (mainLowSourceRows second (datum r) (fun _=>True))
              (select r chi psi) p) (fun _ _=>1) r D) ≤
          (oldBound+sourceConstant*receipt.family.value)*(2*dyadicScale n)^(3*eps)) →
    ∃receipt : NativeNodeForestReceipt hH node Bsrc boxes,
      mainLowPhysicalCompleteCost N supply ap second datum coefficient t u select ≤
        (1/lowerFactor N supply ap)*
          ((Fintype.card RayFourExpansion.RayCharacter:ℝ)^2*
            (Fintype.card (BufferIndex e):ℝ)*
              (oldBound*(Cu*Z^(epsUnion+3*(((N:ℝ)+2)*U)*eps))+
                2*(Cu*sourceConstant)*receipt.family.value)) := by
  obtain ⟨Cu,hCu,hoperator⟩ := eventual_complete_low_shells_forest_uniform_all_ledgers (alpha:=Current) (M:=M) (H:=H) (hH:=hH) (Depth:=SuffixDepth (4-j.val)) (junction:=suffixJunction j.val (4-j.val)) (Base:=suffixBase j.val (4-j.val)) (base:=suffixDictionary j.val (4-j.val)) N U eps epsUnion hU heps hUnion
  refine ⟨Cu,hCu,?_⟩
  filter_upwards [hoperator] with Z hz
  refine ⟨hz.1,?_⟩
  intro L
  letI : Cycle63.AffineLedger:=L
  intro C node hbase Bsrc boxes Label _ supply ap second datum coefficient t u e select hN hpool hcoefficient
    oldBound sourceConstant hold hconstant hlower hpositive hlocal
  subst Z
  let shellFee:=epsUnion+3*(((N:ℝ)+2)*U)*eps
  let Trace:=fun (_chi _psi : RayFourExpansion.RayCharacter)(_p : BufferIndex e)(_n : ℤ)
      (F : node.Family hH)=>
    ∃receipt : NativeNodeForestReceipt hH node Bsrc boxes,
      receipt.family=F ∧ ∀d z,(receipt.family.part d z).loss+shellFee ≤ terminalLossCap j
  have hlocal' : ∀(chi psi : RayFourExpansion.RayCharacter)(p : BufferIndex e),1 ≤ p.1.val →
      ∀n∈selectedShells (sharedProjectors (fun r=>(datum r).block.divisors.filter Squarefree)),
      ∃F : node.Family hH,Trace chi psi p n F ∧
        (∑r,∑D∈shell (sharedProjectors (fun r=>(datum r).block.divisors.filter Squarefree)) n,
          nativeResidualCost second datum
            (fun r=>coefficient r*(datum r).K*normalizer (datum r).C (datum r).D (datum r).inactive)
            (fun _=>if second then psi⁻¹ else chi)
            (fun r=>(datum r).input.t+2*Real.pi*(u-(if second then -t else t)))
            (fun r=>mainLowPaymentRows (mainLowSourceRows second (datum r) (fun _=>True))
              (select r chi psi) p) (fun _ _=>1) r D) ≤
          (oldBound+sourceConstant*F.value)*(2*dyadicScale n)^(3*eps) := by
    intro chi psi p hp n hn
    obtain ⟨receipt,hloss,hbound⟩:=hlocal chi psi p hp n hn
    exact ⟨receipt.family,⟨receipt,rfl,hloss⟩,hbound⟩
  obtain ⟨F,hselected,hbound⟩:=hz.2 L C.etaSeed C.Bnorm C.Tz node.presentation.mult node.localBase_gt_one supply ap second datum coefficient t u e select
    hN hpool hcoefficient oldBound sourceConstant hold hconstant hlower hpositive Trace hlocal'
  cases hselected with
  | inl hempty=>
    refine ⟨native_empty_forest_receipt hH node Bsrc boxes,?_⟩
    simpa only [hempty,native_empty_forest_receipt] using hbound
  | inr htrace=>
    obtain ⟨chi,psi,p,n,Fraw,hp,hn,hraw,hshift⟩:=htrace
    obtain ⟨receipt,hfamily,hloss⟩:=hraw
    let selected:=NativeNodeForestReceipt.shiftShell receipt shellFee hloss
    refine ⟨selected,?_⟩
    have hselected : selected.family=F := by
      change shiftedReturnedForest receipt.family shellFee=F
      rw [hfamily]
      exact hshift.symm
    simpa only [hselected] using hbound


theorem eventual_actual_root_physical_receipt_all_ledgers
    (N : ℕ)(U eps epsUnion : ℝ)(hU : 0 ≤ U)(heps : 0 ≤ eps)(hUnion : 0<epsUnion) :
    ∃Cu : ℝ,0<Cu ∧ ∀ᶠ Z : ℝ in atTop,1<Z ∧
    ∀L : Cycle63.AffineLedger,letI : Cycle63.AffineLedger:=L;
    ∀(C : SourceContext (α:=alpha) M H)(hbase : C.globalBase=Z)
      (Bsrc : ℝ)(boxes : ℕ→Finset (Fin 4→ℤ)),
    ∀{Label : Type}[Fintype Label](supply ap : ℝ)(second : Bool)
      (datum : Label→SecondInputDatum Current)(coefficient : Label→ℝ)(t u e : ℝ)
      (select : (r : Label)→(chi psi : RayFourExpansion.RayCharacter)→
        mainLowSourceRows second (datum r) (fun _=>True)→BufferIndex e),
    (∀r,Fintype.card (datum r).slots ≤ N) →
    (∀r i I,I∈(datum r).input.pools i→(I.absNorm:ℝ) ≤ Z^U) →
    (∀r,0 ≤ coefficient r*(datum r).K*normalizer (datum r).C (datum r).D (datum r).inactive) →
    ∀(oldBound sourceConstant : ℝ),0 ≤ oldBound → 0 ≤ sourceConstant →
    0<lowerFactor N supply ap →
    (∀r chi psi p z,z∈mainLowPaymentRows (mainLowSourceRows second (datum r) (fun _=>True))
      (select r chi psi) p→1 ≤ p.1.val) →
    (∀(chi psi : RayFourExpansion.RayCharacter)(p : BufferIndex e),1 ≤ p.1.val →
      ∀n∈selectedShells (sharedProjectors (fun r=>(datum r).block.divisors.filter Squarefree)),
      ∃receipt : NativeRootForestReceipt (hH:=hH) (C:=C) Bsrc boxes,
        (∀d z,(receipt.family.part d z).loss+
          (epsUnion+3*(((N:ℝ)+2)*U)*eps) ≤ 6/1000000000000) ∧
        (∑r,∑D∈shell (sharedProjectors (fun r=>(datum r).block.divisors.filter Squarefree)) n,
          nativeResidualCost second datum
            (fun r=>coefficient r*(datum r).K*normalizer (datum r).C (datum r).D (datum r).inactive)
            (fun _=>if second then psi⁻¹ else chi)
            (fun r=>(datum r).input.t+2*Real.pi*(u-(if second then -t else t)))
            (fun r=>mainLowPaymentRows (mainLowSourceRows second (datum r) (fun _=>True))
              (select r chi psi) p) (fun _ _=>1) r D) ≤
          (oldBound+sourceConstant*receipt.family.value)*(2*dyadicScale n)^(3*eps)) →
    ∃receipt : NativeRootForestReceipt (hH:=hH) (C:=C) Bsrc boxes,
      mainLowPhysicalCompleteCost N supply ap second datum coefficient t u select ≤
        (1/lowerFactor N supply ap)*
          ((Fintype.card RayFourExpansion.RayCharacter:ℝ)^2*
            (Fintype.card (BufferIndex e):ℝ)*
              (oldBound*(Cu*Z^(epsUnion+3*(((N:ℝ)+2)*U)*eps))+
                2*(Cu*sourceConstant)*receipt.family.value)) := by
  obtain ⟨Cu,hCu,hoperator⟩ := eventual_complete_low_shells_forest_uniform_all_ledgers (alpha:=Current) (M:=M) (H:=H) (hH:=hH) (Depth:=SuffixDepth 4) (junction:=suffixJunction 0 4) (Base:=suffixBase 0 4) (base:=suffixDictionary 0 4) N U eps epsUnion hU heps hUnion
  refine ⟨Cu,hCu,?_⟩
  filter_upwards [hoperator] with Z hz
  refine ⟨hz.1,?_⟩
  intro L
  letI : Cycle63.AffineLedger:=L
  intro C hbase Bsrc boxes Label _ supply ap second datum coefficient t u e select hN hpool hcoefficient
    oldBound sourceConstant hold hconstant hlower hpositive hlocal
  subst Z
  let shellFee:=epsUnion+3*(((N:ℝ)+2)*U)*eps
  let Trace:=fun (_chi _psi : RayFourExpansion.RayCharacter)(_p : BufferIndex e)(_n : ℤ)
      (F : RootLowFamily (hH:=hH) C)=>
    ∃receipt : NativeRootForestReceipt (hH:=hH) (C:=C) Bsrc boxes,
      receipt.family=F ∧ ∀d z,(receipt.family.part d z).loss+shellFee ≤ 6/1000000000000
  have hlocal' : ∀(chi psi : RayFourExpansion.RayCharacter)(p : BufferIndex e),1 ≤ p.1.val →
      ∀n∈selectedShells (sharedProjectors (fun r=>(datum r).block.divisors.filter Squarefree)),
      ∃F : RootLowFamily (hH:=hH) C,Trace chi psi p n F ∧
        (∑r,∑D∈shell (sharedProjectors (fun r=>(datum r).block.divisors.filter Squarefree)) n,
          nativeResidualCost second datum
            (fun r=>coefficient r*(datum r).K*normalizer (datum r).C (datum r).D (datum r).inactive)
            (fun _=>if second then psi⁻¹ else chi)
            (fun r=>(datum r).input.t+2*Real.pi*(u-(if second then -t else t)))
            (fun r=>mainLowPaymentRows (mainLowSourceRows second (datum r) (fun _=>True))
              (select r chi psi) p) (fun _ _=>1) r D) ≤
          (oldBound+sourceConstant*F.value)*(2*dyadicScale n)^(3*eps) := by
    intro chi psi p hp n hn
    obtain ⟨receipt,hloss,hbound⟩:=hlocal chi psi p hp n hn
    exact ⟨receipt.family,⟨receipt,rfl,hloss⟩,hbound⟩
  obtain ⟨F,hselected,hbound⟩:=hz.2 L C.etaSeed C.Bnorm C.Tz (1:O) C.globalBase_gt_one supply ap second datum coefficient t u e select
    hN hpool hcoefficient oldBound sourceConstant hold hconstant hlower hpositive Trace hlocal'
  cases hselected with
  | inl hempty=>
    refine ⟨native_empty_root_forest_receipt Bsrc boxes,?_⟩
    simpa only [hempty,native_empty_root_forest_receipt] using hbound
  | inr htrace=>
    obtain ⟨chi,psi,p,n,Fraw,hp,hn,hraw,hshift⟩:=htrace
    obtain ⟨receipt,hfamily,hloss⟩:=hraw
    let selected:=NativeRootForestReceipt.shiftShell receipt shellFee hloss
    refine ⟨selected,?_⟩
    have hselected : selected.family=F := by
      change shiftedReturnedForest receipt.family shellFee=F
      rw [hfamily]
      exact hshift.symm
    simpa only [hselected] using hbound

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.eventual_complete_low_shells_forest_uniform_all_ledgers
#print axioms OAI.SevenEighths.Cycle153RegionalLow.eventual_actual_inner_physical_receipt_all_ledgers
#print axioms OAI.SevenEighths.Cycle153RegionalLow.eventual_actual_root_physical_receipt_all_ledgers
