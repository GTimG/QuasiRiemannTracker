import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryErrorOrdinaryContraction
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineExceptionalPayment
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineErrorRemainder
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryExceptionalErrorNormPayment
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency true

namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceMass CenteredMomentPrimeElements CenteredMomentPrimePool
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplificationErrorEnergy
open CenteredMomentEnergyFirstAnnularAdmission CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyState CenteredMomentEnergyBands Cycle63InitialSource
open CenteredMomentCommonProfile CenteredMomentAmplificationRadicalFamily
open CenteredMomentChildRows CenteredMomentSecondHeightFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentAllocatedRayDictionary
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondEnergySplit
open CenteredMomentExceptionalAmplitudePair CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
attribute [local instance] geometryErrorOrdinaryContractionDecidable

private theorem affine_error_sum_transport {Label : Type*} [Fintype Label]
    {f : Label→ℝ} {r : ℝ} (h : ∑j,f j≤ r)
    (g : Label→ℝ) (hg : ∀j,g j=f j) : ∑j,g j≤ r := by
  simpa only [hg] using h

private theorem affine_error_rhs_transport {a b c : ℝ} (h : a≤b) (he : b=c) : a≤ c :=
  h.trans_eq he

private theorem affine_error_combine {a exceptional mass cap ordinary : ℝ}
    (h : a≤exceptional+ordinary)(hp : exceptional≤ mass)(hc : mass≤ cap) :
    a≤ cap+ordinary := by
  linarith only [h,hp,hc]

private theorem affine_error_distribute {Label : Type*} [Fintype Label]
    {a c : ℝ} {f : Label→ℝ} (h : a≤ c*∑j,f j) : a≤∑j,c*f j := by
  simpa only [Finset.mul_sum] using h

private theorem affine_error_sigma_ray_payment {Label : Type*} [Fintype Label]
    {Rows : Label→Type*} [∀l,Fintype (Rows l)]
    {f : (l : Label)→(Rows l→RayCharacter)→Rows l→ℝ} {g : Label→ℝ}
    (h : ∀l χ,∑n,f l χ n≤g l) (χ : ((l : Label)×Rows l)→RayCharacter) :
    (∑j : (l : Label)×Rows l,f j.1 (fun n=>χ ⟨j.1,n⟩) j.2)≤∑l,g l := by
  rw [Fintype.sum_sigma]
  exact Finset.sum_le_sum (fun l _=>h l (fun n=>χ ⟨l,n⟩))

local syntax (name := affineErrorSource) "affine_error_source " term ", " term ", " term : term
open Lean Meta Elab Term in
@[term_elab affineErrorSource] private def elabAffineErrorSource : TermElab := fun stx _=>do
  let h ← elabTerm stx[1] none
  let q ← elabTerm stx[3] none
  let m ← elabTerm stx[5] none
  let ht ← inferType h
  forallBoundedTelescope ht (some 1) fun xs _=>do
    unless xs.size=1 do throwError "expected a raw-character binder"
    let paid:=mkAppN h #[xs[0]!,q,m]
    let result ← mkAppM ``affine_error_distribute #[paid]
    mkLambdaFVars xs result

local syntax (name := affineErrorCollect) "affine_error_collect " term : term
open Lean Meta Elab Term in
@[term_elab affineErrorCollect] private def elabAffineErrorCollect : TermElab := fun stx _=>do
  let h ← elabTerm stx[1] none
  let h ← instantiateMVars h
  let ht ← inferType h
  forallTelescope ht fun xs body=>do
    unless xs.size=2 do throwError "expected source and raw-character binders"
    let l:=xs[0]!
    let chi:=xs[1]!
    let chiType ← inferType chi
    let .forallE _ _ _ _:=chiType | throwError "expected raw character function"
    let leArgs:=body.getAppArgs
    unless body.getAppFn.isConstOf ``LE.le && leArgs.size≥2 do
      throwError "expected a real inequality"
    let lhs:=leArgs[leArgs.size-2]!
    let rhs:=leArgs[leArgs.size-1]!
    let sumArgs:=lhs.getAppArgs
    unless lhs.getAppFn.isConstOf ``Finset.sum && sumArgs.size≥2 do
      throwError "expected a finite raw row sum"
    let univ:=sumArgs[sumArgs.size-2]!
    let univArgs:=univ.getAppArgs
    unless univ.getAppFn.isConstOf ``Finset.univ && univArgs.size=2 do
      throwError "expected the complete raw finite carrier"
    if rhs.containsFVar chi.fvarId! then throwError "source cap depends on inducing ray"
    let label ← inferType l
    let labelClass ← mkAppM ``Fintype #[label]
    let labelInst ← synthInstance labelClass
    let rows ← mkLambdaFVars #[l] univArgs[0]!
    let rowsInst ← mkLambdaFVars #[l] univArgs[1]!
    let f ← mkLambdaFVars #[l,chi] sumArgs[sumArgs.size-1]!
    let g ← mkLambdaFVars #[l] rhs
    let u ← getDecLevel label
    let v ← getDecLevel univArgs[0]!
    pure (mkAppN (mkConst ``affine_error_sigma_ray_payment [u,v])
      #[label,labelInst,rows,rowsInst,f,g,h])

local syntax (name := affineErrorApply) "affine_error_apply " term ", " term : term
open Lean Meta Elab Term in
@[term_elab affineErrorApply] private def elabAffineErrorApply : TermElab := fun stx _=>do
  let h ← elabTerm stx[1] none
  let x ← elabTerm stx[3] none
  pure (mkApp h x)

local syntax (name := affineErrorCall) "affine_error_call " term "," "[" term,* "]" : term
open Lean Meta Elab Term in
@[term_elab affineErrorCall] private def elabAffineErrorCall : TermElab := fun stx _=>do
  let h ← elabTerm stx[1] none
  let mut args:=#[]
  for i in [:stx[4].getSepArgs.size] do
    let a ← elabTerm stx[4].getSepArgs[i]! none
    args:=args.push a
  pure (mkAppN h args)

/- The final bridge term is fully specified. Skip only the elaborator's
repeated expected-type search; the declaration's kernel check remains mandatory. -/
local syntax (name := affineErrorExact) "affine_error_exact " term : tactic
open Lean Meta Elab Tactic in
@[tactic affineErrorExact] private def elabAffineErrorExact : Tactic := fun stx=>withMainContext do
  let proof ← Term.elabTerm stx[1] none
  Term.synthesizeSyntheticMVarsNoPostponing
  let proof ← instantiateMVars proof
  if proof.hasMVar then throwError "the exact source bridge contains unresolved metavariables"
  let goal ← getMainGoal
  goal.assign proof
  replaceMainGoal []

local syntax (name := affineErrorTransport) "affine_error_transport " term ", " term ", " term : term
open Lean Meta Elab Term in
@[term_elab affineErrorTransport] private def elabAffineErrorTransport : TermElab := fun stx _=>do
  let h ← elabTerm stx[1] none
  let g ← elabTerm stx[3] none
  let he ← elabTerm stx[5] none
  let ht ← inferType h
  let args:=ht.getAppArgs
  unless ht.getAppFn.isConstOf ``LE.le && args.size≥2 do throwError "expected an inequality"
  let lhs:=args[args.size-2]!
  let rhs:=args[args.size-1]!
  let sa:=lhs.getAppArgs
  unless lhs.getAppFn.isConstOf ``Finset.sum && sa.size≥2 do throwError "expected a raw sum"
  let ua:=sa[sa.size-2]!.getAppArgs
  let u ← getDecLevel ua[0]!
  pure (mkAppN (mkConst ``affine_error_sum_transport [u])
    #[ua[0]!,ua[1]!,sa[sa.size-1]!,rhs,h,g,he])

local syntax (name := affineErrorCap) "affine_error_cap " term ", " term ", " term : term
open Lean Meta Elab Term in
@[term_elab affineErrorCap] private def elabAffineErrorCap : TermElab := fun stx _=>do
  let h ← elabTerm stx[1] none
  let c ← elabTerm stx[3] none
  let ht ← inferType h
  let args:=ht.getAppArgs
  unless ht.getAppFn.isConstOf ``LE.le && args.size≥2 do throwError "expected a paid inequality"
  let a:=args[args.size-2]!
  let b:=args[args.size-1]!
  let he ← elabTerm stx[5] none
  pure (mkAppN (mkConst ``affine_error_rhs_transport) #[a,b,c,h,he])

/- Avoid unfolding the frozen pointwise geometry predicate while selecting
its ordinary constant. These are plain Classical.choose and And projections. -/
local syntax (name := affineErrorChoice) "affine_error_choice " term ", " num : term
open Lean Meta Elab Term in
@[term_elab affineErrorChoice] private def elabAffineErrorChoice : TermElab := fun stx _=>do
  let h ← elabTerm stx[1] none
  let ht ← instantiateMVars (← inferType h)
  let ht:=ht.headBeta
  unless ht.getAppFn.isConstOf ``Exists do throwError "expected a checked existential; head is {ht.getAppFn}"
  let ea:=ht.getAppArgs
  let carrier:=ea[ea.size-2]!
  let pred:=ea[ea.size-1]!
  let u ← getLevel carrier
  let chosen:=mkAppN (mkConst ``Classical.choose [u]) #[carrier,pred,h]
  let some mode:=stx[3].isNatLit? | throwError "expected an explicit selector"
  if mode=0 then return chosen
  let body:=(mkApp pred chosen).headBeta
  unless body.getAppFn.isConstOf ``And do throwError "expected a conjunction after the witness"
  let ba:=body.getAppArgs
  let spec:=mkAppN (mkConst ``Classical.choose_spec [u]) #[carrier,pred,h]
  if mode=1 then return mkAppN (mkConst ``And.left) #[ba[0]!,ba[1]!,spec]
  if mode=2 then return mkAppN (mkConst ``And.right) #[ba[0]!,ba[1]!,spec]
  throwError "expected witness, positive projection, or endpoint projection"

/- Read only the exact endpoint predicate of the frozen existential. -/
local syntax (name := affineErrorFrozenSpec) "affine_error_frozen_spec " term ", " term : term
open Lean Meta Elab Term in
@[term_elab affineErrorFrozenSpec] private def elabAffineErrorFrozenSpec : TermElab := fun stx _=>do
  let h ← elabTerm stx[1] none
  let c ← elabTerm stx[3] none
  let ht ← instantiateMVars (←inferType h)
  unless ht.getAppFn.isConstOf ``Exists do throwError "expected the frozen ordinary existential"
  let ea:=ht.getAppArgs
  lambdaTelescope ea[ea.size-1]! fun cs body=>do
    unless cs.size=1 && body.getAppFn.isConstOf ``And do throwError "expected positivity and the frozen endpoint"
    let ba:=body.getAppArgs
    let pred ← mkLambdaFVars cs ba[ba.size-1]!
    pure ((mkApp pred c).headBeta)

local syntax (name := affineErrorJoin) "affine_error_join " term ", " term ", " term : term
open Lean Meta Elab Term in
@[term_elab affineErrorJoin] private def elabAffineErrorJoin : TermElab := fun stx _=>do
  let h ← elabTerm stx[1] none
  let hp ← elabTerm stx[3] none
  let hc ← elabTerm stx[5] none
  let ht ← instantiateMVars (←inferType h)
  let pt ← instantiateMVars (←inferType hp)
  let ct ← instantiateMVars (←inferType hc)
  unless ht.getAppFn.isConstOf ``LE.le && pt.getAppFn.isConstOf ``LE.le &&
      ct.getAppFn.isConstOf ``LE.le do throwError "expected the three exact paid inequalities"
  let ha:=ht.getAppArgs
  let pa:=pt.getAppArgs
  let ca:=ct.getAppArgs
  let rhs:=ha[ha.size-1]!
  unless rhs.getAppFn.isConstOf ``HAdd.hAdd do throwError "expected exceptional plus ordinary"
  let ra:=rhs.getAppArgs
  pure (mkAppN (mkConst ``affine_error_combine)
    #[ha[ha.size-2]!,ra[ra.size-2]!,pa[pa.size-1]!,ca[ca.size-1]!,ra[ra.size-1]!,h,hp,hc])

variable {ι : Type*} [Fintype ι]

/-- The exact unchanged endpoint of the frozen ordinary contraction. -/
def GeometryErrorOrdinaryFrozenSpec
    (A degree windowDegree : ℕ)(hc : HasCompactSupport logAnnulus)
    (hs : ContDiff ℝ ∞ logAnnulus)(C : ℝ) : Prop :=
  affine_error_frozen_spec (actual_geometry_error_ordinary_contraction (α:=ι)
    A degree windowDegree hc hs), C

attribute [local irreducible] geometryErrorSecondDatum geometryErrorNonzeroBlocks
  geometryErrorChild geometryLowFirstChild geometryJointErrorDatum geometryJointErrorWeight

section Source
variable (reflected : Bool) (s : Input ι) (R seed : Ideal O) (Ψ : 𝓢(ℝ,ℂ))
  (Z Mrow amp ξ reserve t : ℝ) (hZ : 1<Z) (key : ℤ×(Fin 5→ℤ))
  (P : Finset (Ideal O)) (Qfix : Ideal O) (m : O)
local notation "hK" => Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow
variable (υ : GeometryLowFirstIndex (α:=ι) reflected s R seed
    (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) key→
    elementPool P→Fin 3→RayCharacter→ Character)
  (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
local notation "Sources" => GeometryJointErrorSourceIndex (α:=ι) reflected s R seed Z Mrow ξ t hZ key P
local notation "Selected" => GeometryJointErrorSelectedIndex (α:=ι) reflected s R seed Z Mrow amp ξ reserve (9/4) t hZ key P υ hz₁ hz₂
local notation "phase" => fun c=>normPhase (coordinateBlock s R seed Ψ (Z^Mrow) Z ξ c)
local notation "weight" => geometryJointErrorWeight (α:=ι) reflected s R seed Z Mrow amp ξ reserve (9/4) t hZ key P υ
  Mrow (Real.logb Z (volume s)) phase hz₁ hz₂
local notation "datum" => geometryJointErrorDatum (α:=ι) reflected s R seed Z Mrow amp ξ reserve (9/4) t hZ key P υ hz₁ hz₂

set_option linter.defProp false in
set_option maxHeartbeats 10000 in
private def affine_error_source_raw_payment (l : Sources) :=
  actual_geometry_error_exceptional_selected_norm_le (ι:=ι) reflected s R seed Ψ
    Z Mrow amp ξ reserve (9/4) t hZ key l.1 P l.2.1.val l.2.2.1 l.2.2.2.2
    (υ l.1 l.2.1 l.2.2.1 l.2.2.2.1) t hz₁ hz₂

set_option linter.defProp false in
set_option maxHeartbeats 10000 in
private def affine_error_source_selected_payment (l : Sources) :=
  affine_error_source (affine_error_source_raw_payment (ι:=ι) reflected s R seed Ψ Z Mrow amp ξ reserve t hZ key
    P υ hz₁ hz₂ l), Qfix, m

set_option linter.defProp false in
set_option maxHeartbeats 15000 in
private def affine_error_joint_raw_payment :=
  affine_error_collect (fun l : Sources=>
    affine_error_source_selected_payment (ι:=ι) reflected s R seed Ψ Z Mrow amp ξ reserve t hZ key
      P Qfix m υ hz₁ hz₂ l)

set_option linter.defProp false in
private def affine_error_point_block_transport (j : Selected) (χ : RayCharacter) :=
  congrArg (fun b=>‖weight j*b.value ballProfile‖)
    (geometry_joint_error_exceptional_datum_block (α:=ι) reflected s R seed Z Mrow amp ξ reserve
      (9/4) t hZ key P υ hz₁ hz₂ j χ Qfix m)

set_option linter.defProp false in
set_option maxHeartbeats 15000 in
private def affine_error_joint_selected_payment (χ : Selected→RayCharacter) :=
  affine_error_transport
    (affine_error_apply (affine_error_joint_raw_payment (ι:=ι) reflected s R seed Ψ Z Mrow amp ξ reserve
      t hZ key P Qfix m υ hz₁ hz₂), χ),
    (fun j : Selected=>‖weight j*(mainExceptionalDatum (datum j) (χ j) Qfix m).block.value ballProfile‖),
    (fun j : Selected=>affine_error_point_block_transport (ι:=ι) reflected s R seed Ψ Z Mrow amp ξ reserve
      t hZ key P Qfix m υ hz₁ hz₂ j (χ j))

private theorem affine_error_source_mass_sum :
    (∑l : Sources,∑χ₀ : RayCharacter,geometryExceptionalErrorNormSourceMass (ι:=ι)
      reflected s R seed Ψ Z Mrow amp ξ reserve (9/4) t hZ key l.1 P l.2.1.val l.2.2.1
      l.2.2.2.2 (υ l.1 l.2.1 l.2.2.1 l.2.2.2.1) t Qfix m χ₀)=
    geometryAffineErrorExceptionalMass s R seed Ψ Z Mrow amp ξ reserve t t hZ reflected key P Qfix m υ := by
  simp only [GeometryJointErrorSourceIndex,GeometryLowFirstIndex,
    geometryAffineErrorExceptionalMass,Fintype.sum_sigma]

set_option linter.defProp false in
set_option maxHeartbeats 20000 in
def actual_geometry_error_exceptional_sum_payment (χ : Selected→RayCharacter) :=
  affine_error_cap
    (affine_error_joint_selected_payment (ι:=ι) reflected s R seed Ψ Z Mrow amp ξ reserve t hZ key
      P Qfix m υ hz₁ hz₂ χ),
    (geometryAffineErrorExceptionalMass s R seed Ψ Z Mrow amp ξ reserve t t hZ reflected key P Qfix m υ),
    (affine_error_source_mass_sum (ι:=ι) reflected s R seed Ψ Z Mrow amp ξ reserve t hZ key P Qfix m υ)

end Source
/-- Literal retained error sum. The first allocation weight is undivided and
its actual Fourier cardinality is retained. -/
def geometryAffineErrorRetainedContractSum
    (reflected : Bool)(s : Input ι)(R seed : Ideal O)(Ψ : 𝓢(ℝ,ℂ))(Z Mrow amp ξ reserve t : ℝ)
    (hZ : 1<Z)(key : ℤ×(Fin 5→ℤ))(P : Finset (Ideal O))
    (υ : GeometryLowFirstIndex (α:=ι) reflected s R seed
      (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) key→
      elementPool P→Fin 3→RayCharacter→ Character) : ℂ :=
  let hK:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow
  let phase:=fun c=>normPhase (coordinateBlock s R seed Ψ (Z^Mrow) Z ξ c)
  jointErrorRetained
    (fun q : GeometryLowFirstIndex (α:=ι) reflected s R seed (Z^Mrow) Z ξ hK key=>liveIndices q.2.val)
    (fun q=>geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ hK key t q)
    (fun q=>geometryBranch reflected s R seed (Z^Mrow) Z ξ hK key q.1.val)
    (fun q=>geometryAllocationWeight reflected s R seed (Z^Mrow) Z ξ Mrow
      (Real.logb Z (volume s)) hK key phase (Fintype.card ι) (9/4) q.1.val q.2)
    ballProfile Z (3*amp) ξ reserve P υ
    (fun q p i=>geometryErrorFourierScale reflected s R seed Z Mrow amp ξ reserve (9/4)
      (Fintype.card ι) hZ key q p.val i)

set_option maxHeartbeats 15000 in
private theorem geometry_affine_error_fourier_eq_original
    {β : Type}[Fintype β][DecidableEq β]
    (reflected : Bool)(s : Input β)(R seed : Ideal O)(Z Mrow amp ξ reserve : ℝ)(hZ : 1<Z)
    (key : ℤ×(Fin 5→ℤ))(P : Finset (Ideal O))
    (q : GeometryLowFirstIndex (α:=β) reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) key)
    (p : elementPool P)(i : Fin 3) :
    geometryErrorFourierScale reflected s R seed Z Mrow amp ξ reserve (9/4) (Fintype.card β)
      hZ key q p.val i=
    firstErrorTailFourier (Fintype.card β) (9/4) (volume s)
      (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) key q.1.val)
      p.val (errorIndex i+1)
      (firstErrorTailRadius reflected (geometryFirstLabel s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) key q.1.val)
        Z Mrow (volume s) amp (frequencyLoss Z 32 ξ) reserve p.val (errorIndex i+1)) := by
  unfold geometryErrorFourierScale firstErrorTailFourier
  rw [div_mul_eq_div_div]
  rfl

set_option maxHeartbeats 15000 in
/-- Exact identity with the retained source used by the frozen affine budget. -/
theorem geometry_affine_error_retained_contract_sum_eq_original
    {β : Type}[Fintype β][DecidableEq β]
    (reflected : Bool)(s : Input β)(R seed : Ideal O)(Ψ : 𝓢(ℝ,ℂ))(Z Mrow amp ξ reserve t : ℝ)
    (hZ : 1<Z)(key : ℤ×(Fin 5→ℤ))(P : Finset (Ideal O))
    (υ : GeometryLowFirstIndex (α:=β) reflected s R seed
      (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) key→
      elementPool P→Fin 3→RayCharacter→ Character) :
    geometryAffineErrorRetainedContractSum reflected s R seed Ψ Z Mrow amp ξ reserve t hZ key P υ=
      geometryAffineErrorRetainedSum s R seed Ψ Z Mrow amp ξ reserve t hZ reflected key P υ := by
  unfold geometryAffineErrorRetainedContractSum geometryAffineErrorRetainedSum
  simp only [geometry_affine_error_fourier_eq_original]

/-- Exact joint ordinary normalized intermediate and resulting retained bound. -/
def GeometryErrorSourceRetainedSpec
    (A degree windowDegree : ℕ)(reflected : Bool)(s : Input ι)(R seed : Ideal O)(Ψ : 𝓢(ℝ,ℂ))
    (Z Mrow amp ξ reserve t : ℝ)(hZ : 1<Z)(key : ℤ×(Fin 5→ℤ))(P : Finset (Ideal O))
    (υ : GeometryLowFirstIndex (α:=ι) reflected s R seed
      (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) key→
      elementPool P→Fin 3→RayCharacter→ Character)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (Qfix : Ideal O)(m : O)(exceptional C : ℝ) : Prop :=
    let selected:=GeometryJointErrorSelectedIndex (α:=ι) reflected s R seed Z Mrow amp ξ reserve
      (9/4) t hZ key P υ hz₁ hz₂
    let d:=geometryJointErrorDatum (α:=ι) reflected s R seed Z Mrow amp ξ reserve (9/4) t hZ key P υ hz₁ hz₂
    let phase:=fun c=>normPhase (coordinateBlock s R seed Ψ (Z^Mrow) Z ξ c)
    let coeff:=geometryJointErrorWeight (α:=ι) reflected s R seed Z Mrow amp ξ reserve (9/4) t hZ key P υ
      Mrow (Real.logb Z (volume s)) phase hz₁ hz₂
    ∀(χ : selected→RayCharacter)(E Hratio : ℤ→ℝ),
    (∀r∈secondRatioBins (fun j=>(d j).block),0≤E r) →
    (∀r∈secondRatioBins (fun j=>(d j).block),0<Hratio r) →
    SecondNormalizedBound ballProfile degree windowDegree
      (fun j=>ordinarySecondDatum (d j) (χ j) Qfix m) coeff E Hratio →
    (56/(P.card:ℝ))*‖geometryAffineErrorRetainedContractSum reflected s R seed Ψ Z Mrow amp ξ reserve t hZ key P υ‖≤
      exceptional+C*∑r∈secondRatioBins (fun j=>(d j).block),E r/(1+dyadicScale r)^A

set_option maxHeartbeats 15000 in
private theorem affine_error_paid_source_bridge
    (reflected : Bool)(s : Input ι)(R seed : Ideal O)(Ψ : 𝓢(ℝ,ℂ))
    (Z Mrow amp ξ reserve t : ℝ)(hZ : 1<Z)(key : ℤ×(Fin 5→ℤ))(P : Finset (Ideal O))
    (Qfix : Ideal O)(m : O)
    (υ : GeometryLowFirstIndex (α:=ι) reflected s R seed
      (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) key→
      elementPool P→Fin 3→RayCharacter→ Character)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (A degree windowDegree : ℕ)(hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus)
    (C cap : ℝ)(hordinary : GeometryErrorOrdinaryFrozenSpec (ι:=ι) A degree windowDegree hc hs C)
    (hcap : geometryAffineErrorExceptionalMass s R seed Ψ Z Mrow amp ξ reserve t t hZ reflected key P Qfix m υ≤ cap) :
    GeometryErrorSourceRetainedSpec A degree windowDegree reflected s R seed Ψ Z Mrow amp ξ reserve t hZ
      key P υ hz₁ hz₂ Qfix m cap C := by
  dsimp only [GeometryErrorSourceRetainedSpec]
  intro χ E Hratio hE hHratio hnorm
  let phase:=fun c=>normPhase (coordinateBlock s R seed Ψ (Z^Mrow) Z ξ c)
  have ho:=affine_error_call hordinary, [reflected,s,R,seed,Z,Mrow,amp,
    ξ,reserve,(9/4:ℝ),t,hZ,key,P,υ,hz₁,hz₂,Mrow,(Real.logb Z (volume s)),phase,
    χ,Qfix,m,E,Hratio,hE,hHratio,hnorm]
  have hp:=actual_geometry_error_exceptional_sum_payment (ι:=ι) reflected s R seed Ψ Z Mrow amp ξ reserve
    t hZ key P Qfix m υ hz₁ hz₂ χ
  unfold geometryAffineErrorRetainedContractSum
  affine_error_exact affine_error_join ho, hp, hcap

/-- The paid source contract keeps the entire normalized input and exact
retained sum. Its scalar exceptional cap is supplied by a proved payment. -/
def GeometryErrorPaidSourceSpec
    (A degree windowDegree : ℕ)(_hc : HasCompactSupport logAnnulus)
    (_hs : ContDiff ℝ ∞ logAnnulus)(C : ℝ) : Prop :=
  ∀(reflected : Bool)(s : Input ι)(R seed : Ideal O)(Ψ : 𝓢(ℝ,ℂ))(Z Mrow amp ξ reserve t : ℝ)
    (hZ : 1<Z)(key : ℤ×(Fin 5→ℤ))(P : Finset (Ideal O))(Qfix : Ideal O)(m : O)
    (υ : GeometryLowFirstIndex (α:=ι) reflected s R seed
      (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) key→
      elementPool P→Fin 3→RayCharacter→ Character)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)(cap : ℝ),
    geometryAffineErrorExceptionalMass s R seed Ψ Z Mrow amp ξ reserve t t hZ reflected key P Qfix m υ≤ cap →
    GeometryErrorSourceRetainedSpec A degree windowDegree reflected s R seed Ψ Z Mrow amp ξ reserve t hZ
      key P υ hz₁ hz₂ Qfix m cap C

set_option maxHeartbeats 15000 in
private theorem affine_error_frozen_to_paid
    (A degree windowDegree : ℕ)(hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus)
    (C : ℝ)(hordinary : GeometryErrorOrdinaryFrozenSpec (ι:=ι) A degree windowDegree hc hs C) :
    GeometryErrorPaidSourceSpec (ι:=ι) A degree windowDegree hc hs C := by
  dsimp only [GeometryErrorPaidSourceSpec]
  intro reflected s R seed Ψ Z Mrow amp ξ reserve t hZ key P Qfix m υ hz₁ hz₂ cap hcap
  affine_error_exact affine_error_call (affine_error_paid_source_bridge (ι:=ι)),
    [reflected,s,R,seed,Ψ,Z,Mrow,amp,ξ,reserve,t,hZ,key,P,Qfix,m,υ,hz₁,hz₂,
      A,degree,windowDegree,hc,hs,C,cap,hordinary,hcap]

private theorem affine_error_uniform_map {Index : Type*}{p q : Index→ℝ→Prop}
    (h : ∃C : ℝ,0<C ∧ ∀i,p i C)(map : ∀i C,p i C→q i C) :
    ∃C : ℝ,0<C ∧ ∀i,q i C := by
  obtain ⟨C,hC,hp⟩:=h
  exact ⟨C,hC,fun i=>map i C (hp i)⟩

local syntax (name := affineErrorUniformPaid) "affine_error_uniform_paid " term ", " term : term
open Lean Meta Elab Term in
@[term_elab affineErrorUniformPaid] private def elabAffineErrorUniformPaid : TermElab := fun stx _=>do
  let h ← elabTerm stx[1] none
  let map ← elabTerm stx[3] none
  let ht ← instantiateMVars (←inferType h)
  unless ht.getAppFn.isConstOf ``Exists do throwError "expected the checked uniform constant"
  let ea:=ht.getAppArgs
  lambdaTelescope ea[ea.size-1]! fun cs body=>do
    unless cs.size=1 && body.getAppFn.isConstOf ``And do throwError "expected a positive uniform constant"
    let ba:=body.getAppArgs
    let p ← forallBoundedTelescope ba[ba.size-1]! (some 1) fun ix point=>do
      unless ix.size=1 do throwError "expected the finite original subset"
      mkLambdaFVars #[ix[0]!,cs[0]!] point
    let mt ← instantiateMVars (←inferType map)
    forallBoundedTelescope mt (some 3) fun ix result=>do
      unless ix.size=3 do throwError "expected subset, constant, and frozen proof"
      if result.containsFVar ix[2]!.fvarId! then throwError "paid source predicate depends on its proof"
      let index ← inferType ix[0]!
      let u ← getDecLevel index
      let q ← mkLambdaFVars #[ix[0]!,ix[1]!] result
      pure (mkAppN (mkConst ``affine_error_uniform_map [u]) #[index,p,q,h,map])

private theorem affine_error_cap_increase {a b c C x : ℝ}
    (hc : c≤C)(hx : 0≤x)(h : a≤b+c*x) : a≤b+C*x :=
  h.trans (add_le_add_right (mul_le_mul_of_nonneg_right hc hx) b)

variable {α : Type*} [Fintype α] [DecidableEq α]

private theorem affine_error_ratio_sum_nonneg (bins : Finset ℤ)(E : ℤ→ℝ)(A : ℕ)
    (hE : ∀r∈bins,0≤E r) : 0≤∑r∈bins,E r/(1+dyadicScale r)^A :=
  Finset.sum_nonneg (fun r hr=>div_nonneg (hE r hr)
    (pow_nonneg (by linarith [dyadicScale_pos r]) A))

private theorem affine_error_uniform_constant {Index : Type*}[Fintype Index]
    {p : Index→ℝ→Prop}(data : ∀i,∃c : ℝ,0≤ c ∧ p i c)
    (mono : ∀i {c C : ℝ},c≤C→p i c→p i C) :
    ∃C : ℝ,0<C ∧ ∀i,p i C := by
  choose c hc hp using data
  let total:=1+∑i,c i
  have ht : 0<total := by
    have hh:=Finset.sum_nonneg (s:=Finset.univ) (fun i _=>hc i)
    dsimp only [total]
    linarith
  have hl (i : Index) : c i≤total := by
    have hh:=Finset.single_le_sum (fun i _=>hc i) (Finset.mem_univ i)
    dsimp only [total]
    linarith
  exact ⟨total,ht,fun i=>mono i (hl i) (hp i)⟩

/- This module-local adapter only reads the frozen ordinary telescope and
its final scalar coefficient. It emits applications of the two elementary
lemmas above; every emitted proof is checked by Lean's ordinary kernel. -/
local syntax (name := affineErrorUniform) "affine_error_uniform " term : term
open Lean Meta Elab Term in
@[term_elab affineErrorUniform] private def elabAffineErrorUniform : TermElab := fun stx _=>do
  let data ← elabTerm stx[1] none
  let dt ← inferType data
  forallBoundedTelescope dt (some 1) fun ix ex=>do
    unless ix.size=1 do throwError "expected one finite-family binder"
    let i:=ix[0]!
    unless ex.getAppFn.isConstOf ``Exists do throwError "expected an ordinary constant"
    let ea:=ex.getAppArgs
    lambdaTelescope ea[ea.size-1]! fun cs ab=>do
      unless cs.size=1 && ab.getAppFn.isConstOf ``And do throwError "expected nonnegative constant and endpoint"
      let c:=cs[0]!
      let aa:=ab.getAppArgs
      let pointSpec:=aa[aa.size-1]!
      let pred ← mkLambdaFVars #[i,c] pointSpec
      withLocalDeclD `upper (mkConst ``Real) fun upper=>do
        let leType ← mkAppM ``LE.le #[c,upper]
        withLocalDeclD `hle leType fun hle=>do
          withLocalDeclD `point pointSpec fun hp=>do
            let raised ← forallTelescope pointSpec fun xs body=>do
              unless xs.size≥5 && body.getAppFn.isConstOf ``LE.le do throwError "expected the frozen real endpoint"
              let ba:=body.getAppArgs
              let lhs:=ba[ba.size-2]!
              let rhs:=ba[ba.size-1]!
              unless rhs.getAppFn.isConstOf ``HAdd.hAdd do throwError "expected exceptional plus ordinary"
              let ra:=rhs.getAppArgs
              let exceptional:=ra[ra.size-2]!
              let product:=ra[ra.size-1]!
              unless product.getAppFn.isConstOf ``HMul.hMul do throwError "expected a scalar ordinary payment"
              let pa:=product.getAppArgs
              unless pa[pa.size-2]! == c do throwError "ordinary coefficient is not the quantified constant"
              let ratio:=pa[pa.size-1]!
              unless ratio.getAppFn.isConstOf ``Finset.sum do throwError "expected the exact ratio sum"
              let sa:=ratio.getAppArgs
              let bins:=sa[sa.size-2]!
              let E:=xs[xs.size-5]!
              let hE:=xs[xs.size-3]!
              let A ← lambdaTelescope sa[sa.size-1]! fun rs fraction=>do
                unless rs.size=1 && fraction.getAppFn.isConstOf ``HDiv.hDiv do throwError "expected one real ratio summand"
                let fa:=fraction.getAppArgs
                unless fa[fa.size-2]! == mkApp E rs[0]! do throwError "ratio numerator changed"
                let power:=fa[fa.size-1]!
                unless power.getAppFn.isConstOf ``HPow.hPow do throwError "expected a dyadic power"
                let xa:=power.getAppArgs
                let A:=xa[xa.size-1]!
                if A.containsFVar rs[0]!.fvarId! then throwError "ratio exponent depends on the bin"
                pure A
              let hn:=mkAppN (mkConst ``affine_error_ratio_sum_nonneg) #[bins,E,A,hE]
              let paid:=mkAppN hp xs
              let result:=mkAppN (mkConst ``affine_error_cap_increase)
                #[lhs,exceptional,c,upper,ratio,hle,hn,paid]
              mkLambdaFVars xs result
            let mono ← mkLambdaFVars #[i,c,upper,hle,hp] raised
            let index ← inferType i
            let cl ← mkAppM ``Fintype #[index]
            let inst ← synthInstance cl
            let u ← getDecLevel index
            pure (mkAppN (mkConst ``affine_error_uniform_constant [u]) #[index,inst,pred,data,mono])

set_option linter.defProp false in
set_option maxHeartbeats 15000 in
def uniform_actual_geometry_error_ordinary_contraction
    (A degree windowDegree : ℕ)(hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus) :=
  affine_error_uniform (fun T : Finset α=>actual_geometry_error_ordinary_contraction (α:=T)
    A degree windowDegree hc hs)

set_option linter.defProp false in
set_option maxHeartbeats 15000 in
def uniform_actual_geometry_error_paid_contraction
    (A degree windowDegree : ℕ)(hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus) :=
  affine_error_uniform_paid
    (uniform_actual_geometry_error_ordinary_contraction (α:=α) A degree windowDegree hc hs),
    (fun T : Finset α=>affine_error_frozen_to_paid (ι:=T) A degree windowDegree hc hs)

variable (rayM : Ideal O) [NeZero rayM]
local instance affineErrorContractionFiniteQuotient : Finite (O ⧸ rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O ⧸ rayM)ˣ)(hH : RayOrthogonality.globalUnits rayM≤H)

set_option maxHeartbeats 30000 in
variable [Cycle63.AffineLedger] in
/-- Genuine exceptional payment and the original retained error identity are
composed with the ordinary normalized intermediate contract, at every parent input with
source gates of profile cap `Cs`, first puncture of norm at most `Z^20`, seed and radial
scale `Mrow`. -/
theorem actual_affine_error_retained_contraction
    (A ordinaryDegree windowDegree : ℕ)
    (hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus)
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(εaffine mesh : ℝ)(hε : 0<εaffine)
    (hmesh : mesh<Cycle63.AffineLedger.amplifierFloor/2)
    (Qfix : Ideal O)(hQ : Qfix≠0)(hQt : Qfix≠⊤)(hQ72 : Qfix≤Ideal.span {(72:O)})
    (m : O)(hm : m≠0)(hml : goodLambda∣m)(hm2 : (2:O)∣m)(Cs : ℝ) :
    ∃Ce : ℝ,0<Ce ∧ ∃Sp : Finset (ℕ×ℕ),∃exceptionalDegree : ℕ,
    ∃Co : ℝ,0<Co ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(hZ : 1<Z)(T : Finset α)(s : Input T)(p : Profiles (1/4) (9/4))
      (caps : GeometryAffineExceptionalSourceGates s p (Fintype.card T) Cs Z)
      (η₀ : Character)(θ : T→RayQuotient.Characters rayM H)(w σ freq : T→ℝ),
      Matches rayM H hH s η₀ θ w σ freq W 2 Z →
      ∀(R seed : Ideal O)(Mrow : ℝ),R≠0 → Squarefree seed →
      (R.absNorm:ℝ)≤Z^(20:ℝ) → 0≤ Mrow → Mrow≤1 →
      Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ)≤1+geometryLossUnit 1 εaffine/16 →
      (∀j,w j≤ mesh) →
      (Cycle63.AffineLedger.slotFloor≤∑j,Real.logb Z (s.P j) ∧
        (∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.slotTop) →
      length Z s.X₁+length Z s.X₂+Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j))≤
        Cycle63.AffineLedger.B →
      ∀beta : ℝ,beta=Cycle63.AffineLedger.cellUpper
        (Cycle63.AffineLedger.originalCell (∑j,Real.logb Z (s.P j))) →
      let amp:=Cycle63.AffineLedger.amp beta
      let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^amp)
      let μ:=geometryLossUnit 1 εaffine
      ∀(Ψ : 𝓢(ℝ,ℂ))(reflected : Bool)(key : ℤ×(Fin 5→ℤ))(firstHeight : ℝ)
        (υ : GeometryLowFirstIndex (α:=T) reflected s R seed
          (Z^Mrow) Z (μ/64) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) key→
          elementPool P→Fin 3→RayCharacter→ Character),
      (∀q p i ψ,(υ q p i ψ).modulus.absNorm≤ radicalBound (childCharacter
        (geometryColumnCharacter reflected s R seed (Z^Mrow) Z (μ/64)
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) key q.1.val) ψ)
        fixedBadMask p.val (errorMovingExponent (errorIndex i))) →
      letI : DecidableEq T := Classical.decEq T;
      GeometryErrorSourceRetainedSpec (ι:=T) A ordinaryDegree windowDegree reflected s R seed Ψ
        Z Mrow amp (μ/64) (μ/8) firstHeight hZ key P υ caps.zero₁ caps.zero₂ Qfix m
        (Ce*geometryAffineExceptionalShell reflected Z key*(p.control Sp)^2*
          (1+‖firstHeight‖)^exceptionalDegree*Z^(-(1/100:ℝ)+(1-Mrow))/(seed.absNorm:ℝ)) Co := by
  let ordinary:=uniform_actual_geometry_error_paid_contraction (α:=α)
    A ordinaryDegree windowDegree hc hs
  let Co:=affine_error_choice ordinary, 0
  have hCo:=affine_error_choice ordinary, 1
  have hordinary:=affine_error_choice ordinary, 2
  obtain ⟨Ce,hCe,Sp,exceptionalDegree,hexceptional⟩:=actual_affine_error_exceptional_parent_payment
    (α:=α) rayM H hH Sbad hbad W εaffine mesh hε hmesh Qfix hQ hQt hQ72 m hm hml hm2 Cs
  refine ⟨Ce,hCe,Sp,exceptionalDegree,Co,hCo,?_⟩
  filter_upwards [hexceptional] with Z hz
  refine ⟨hz.1,?_⟩
  intro hZ T s p caps η₀ θ w σ freq hmatch R seed Mrow hR hseed hRcap hMrow hMrow1 hfit hwm hzslot
    haff beta hbeta amp P μ Ψ reflected key firstHeight υ hυ
  let : DecidableEq T := Classical.decEq T
  have he:=hz.2 T hZ s p caps η₀ θ w σ freq hmatch R seed Mrow hR hseed hRcap hMrow hMrow1 hfit
    hwm hzslot haff beta hbeta Ψ reflected key firstHeight firstHeight υ hυ
  affine_error_exact affine_error_call (affine_error_apply hordinary, T),
    [reflected,s,R,seed,Ψ,Z,Mrow,amp,(μ/64),(μ/8),firstHeight,hZ,key,P,Qfix,m,υ,
      caps.zero₁,caps.zero₂,
      (Ce*geometryAffineExceptionalShell reflected Z key*(p.control Sp)^2*
        (1+‖firstHeight‖)^exceptionalDegree*Z^(-(1/100:ℝ)+(1-Mrow))/(seed.absNorm:ℝ)),he]

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
