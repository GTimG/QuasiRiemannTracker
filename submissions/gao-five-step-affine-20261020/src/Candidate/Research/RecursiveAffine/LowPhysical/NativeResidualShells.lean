/- Copyright (c) 2026 Hailey Collet; whole-source shell selection (c) 2026 Zhongpai Gao.
Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowFull
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowPhysicalPayment
import Candidate.Research.RecursiveAffine.NativeCommonForest
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle153LowPhysical
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondEnergySplit
open CenteredMomentSectorLocalization CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentSecondHeightFamily
open CenteredMomentCommonPairedSource
open CenteredMomentCommonWindowColumn CenteredMomentHeckeColumnWindow
open CenteredMomentCommonLinearNormalization
open CenteredMomentLogDyadic CenteredMomentWholeDivisorShell
open Cycle153SourceReturn Cycle153RegionalLow

variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O ⧸ M)ˣ}
variable {hH : RayOrthogonality.globalUnits M ≤ H}
variable {Depth : Type} [Fintype Depth] {junction : Depth→ℝ} {Base : Depth→Type}
variable {base : (d : Depth)→Character→Base d→Character}
variable {eta : Character} {Z Bnorm T : ℝ} {root : O}

/-- The actual normalized-column cost at one complete block and projector.
The physical coefficient, original mask, source height, and seed stay literal. -/
def nativeResidualCost {Label : Type} [Fintype Label]
    (second : Bool) (datum : Label→SecondInputDatum alpha)
    (coefficient : Label→ℝ) (ray : Label→RayFourExpansion.RayCharacter)
    (height : Label→ℝ) (zs : Label→Finset O) (rowWeight : Label→O→ℝ)
    (r : Label) (D : Ideal O) : ℝ :=
  coefficient r * ∑z∈zs r,rowWeight r z *
    ‖normalizedColumn (withHeight (datum r).input ((datum r).τ (ray r)) (height r))
      (if second then (datum r).D else (datum r).C) (mainLowPhysicalSupported second (datum r))
      (datum r).R (datum r).seed D z‖^2

private theorem squarefree_projector_shells {Label : Type} [Fintype Label]
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

/-- Sum the literal residual projector shells after selecting ONE actual
whole forest. The local producer supplies an entire forest for each shell;
maximization keeps its source provenance and all depths together. The old
term can retain its native seed reciprocal; none is inserted into the return. -/
theorem actual_residual_shell_forest {Label : Type} [Fintype Label]
    (second : Bool) (datum : Label→SecondInputDatum alpha)
    (coefficient : Label→ℝ) (ray : Label→RayFourExpansion.RayCharacter)
    (height : Label→ℝ) (zs : Label→Finset O) (rowWeight : Label→O→ℝ)
    (eps oldBound sourceConstant : ℝ)
    (hZ : 0≤ Z) (hcoefficient : ∀r,0≤ coefficient r)
    (hweight : ∀r z,z∈zs r→0≤ rowWeight r z)
    (hsourceConstant : 0≤ sourceConstant)
    (Trace : ℤ→DepthReturnedFamily M H hH junction Base base eta Z Bnorm T root→Prop)
    (hlocal : ∀n∈selectedShells (sharedProjectors (fun r=>(datum r).block.divisors.filter Squarefree)),
      ∃F : DepthReturnedFamily M H hH junction Base base eta Z Bnorm T root,
        Trace n F ∧
        (∑r,∑D∈shell (sharedProjectors (fun r=>(datum r).block.divisors.filter Squarefree)) n,
          nativeResidualCost second datum coefficient ray height zs rowWeight r D)≤
          (oldBound+sourceConstant*F.value)*(2*dyadicScale n)^(3*eps)) :
    ∃F : DepthReturnedFamily M H hH junction Base base eta Z Bnorm T root,
      ((F.value=0 ∧ selectedShells (sharedProjectors (fun r=>(datum r).block.divisors.filter Squarefree))=∅) ∨
        ∃n,n∈selectedShells (sharedProjectors (fun r=>(datum r).block.divisors.filter Squarefree)) ∧ Trace n F) ∧
      (∑r,∑D∈(datum r).block.divisors.filter Squarefree,
        nativeResidualCost second datum coefficient ray height zs rowWeight r D)≤
        (oldBound+sourceConstant*F.value)*
          (∑n∈selectedShells (sharedProjectors (fun r=>(datum r).block.divisors.filter Squarefree)),
            (2*dyadicScale n)^(3*eps)) := by
  let Ds:=fun r=>(datum r).block.divisors.filter Squarefree
  let S:=selectedShells (sharedProjectors Ds)
  let cost:=nativeResidualCost second datum coefficient ray height zs rowWeight
  have hcost (r : Label) (D : Ideal O) : 0≤ cost r D := by
    dsimp only [cost,nativeResidualCost]
    exact mul_nonneg (hcoefficient r) (Finset.sum_nonneg fun z hz=>mul_nonneg (hweight r z hz) (sq_nonneg _))
  have hsq (r : Label) (D : Ideal O) (hD : D∈Ds r) : Squarefree D := (Finset.mem_filter.mp hD).2
  by_cases hne : S.Nonempty
  · letI : Nonempty ↥S := ⟨⟨hne.choose,hne.choose_spec⟩⟩
    let F : ↥S→DepthReturnedFamily M H hH junction Base base eta Z Bnorm T root :=
      fun n=>Classical.choose (hlocal n.val n.property)
    have hF (n : ↥S) := Classical.choose_spec (hlocal n.val n.property)
    obtain ⟨nmax,hmax⟩ := Finite.exists_max (fun n : ↥S=>(F n).value)
    refine ⟨F nmax,Or.inr ⟨nmax.val,nmax.property,(hF nmax).1⟩,?_⟩
    apply (shared_projector_shell_sum_le Ds hsq cost hcost).trans
    calc
      _ ≤ ∑n∈S,(oldBound+sourceConstant*(F nmax).value)*(2*dyadicScale n)^(3*eps) := by
        refine Finset.sum_le_sum fun n hn=>?_
        apply (hF ⟨n,hn⟩).2.trans
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (mul_nonneg (by norm_num) (dyadicScale_pos n).le) _)
        exact add_le_add_right (mul_le_mul_of_nonneg_left (hmax ⟨n,hn⟩) hsourceConstant) oldBound
      _ = _ := (Finset.mul_sum _ _ _).symm
  · have hS : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    refine ⟨emptyReturnedForest,Or.inl ⟨emptyReturnedForest_value,hS⟩,?_⟩
    have hs:=shared_projector_shell_sum_le Ds hsq cost hcost
    change (∑r,∑D∈Ds r,cost r D)≤_
    have hzero : (∑n∈S,∑r,∑D∈shell (sharedProjectors Ds) n,cost r D)=0 := by rw [hS];simp
    change (∑r,∑D∈Ds r,cost r D)≤(oldBound+sourceConstant*emptyReturnedForest.value)*
      (∑n∈S,(2*dyadicScale n)^(3*eps))
    rw [hS];simp only [Finset.sum_empty,mul_zero]
    change (∑r,∑D∈Ds r,cost r D)≤(∑n∈S,∑r,∑D∈shell (sharedProjectors Ds) n,cost r D) at hs
    rw [hS] at hs
    simpa only [Finset.sum_empty] using hs

/-- The genuine union-of-second-projectors theorem pays every residual
shell at once, uniformly over moving actual blocks. Only the explicit
one-shell recursive source producer remains an input to the operator. -/
theorem eventual_actual_residual_shell_forest
    (N : ℕ) (U eps epsUnion : ℝ) (hU : 0≤ U) (heps : 0≤ eps) (hUnion : 0< epsUnion) :
    ∃Cu : ℝ,0< Cu ∧ ∀ᶠ Z : ℝ in Filter.atTop,1< Z ∧
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
  intro Label _ second datum hN hpool coefficient ray height zs rowWeight oldBound sourceConstant
    hcoefficient hweight hold hconstant Trace hlocal
  obtain ⟨F,hF,hcost⟩ := actual_residual_shell_forest second datum coefficient ray height zs rowWeight
    eps oldBound sourceConstant (zero_lt_one.trans hz.1).le hcoefficient hweight hconstant Trace hlocal
  refine ⟨F,hF,hcost.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (add_nonneg hold (mul_nonneg hconstant (F.value_nonneg (zero_lt_one.trans hz.1).le)))
  rw [squarefree_projector_shells]
  exact hz.2 datum hN hpool
end
end OAI.SevenEighths.Cycle153LowPhysical
#print axioms OAI.SevenEighths.Cycle153LowPhysical.actual_residual_shell_forest
#print axioms OAI.SevenEighths.Cycle153LowPhysical.eventual_actual_residual_shell_forest
