import Candidate.Research.RecursiveAffine.MarkedRootHigh.RootUniform
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 60000
namespace OAI.SevenEighths.Cycle153RootHigh
open Cycle63InitialMass
noncomputable section
open Cycle63MarkedPlain
open scoped Classical ContDiff HeckeNotation
open Filter HeckeFamily CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CanonicalQuadraticSieve ConcretePrimeRowBridge Cycle63Moment

variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
variable [L : Cycle63.AffineLedger] [Cycle153.MarkedRootPrice.RootLedgerBinding L]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- Select every actual-subset density dictionary before fixing one common
height cutoff. Only the scalar loss rate uses the ambient cardinality.
The exact fiber receipt remains explicit until its separate proof is joined. -/
theorem actual_affine_high_uniform_schedule_of_fibers_capped
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (W : ℝ→ℂ)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)(hW : ContDiff ℝ ∞ W)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (hMarkedUpper : 2*HeckeZeroSupremum.beta-1≤Cycle63.Optimization.plainCapacityCost)
    (μ Cs bΦ τcap : ℝ)(hμ : 0<μ)(hμcap : μ≤Cycle63.Optimization.geometryLossCap)(hCs : 1≤Cs)(hbΦ : 2≤bΦ)(hτcap : 0<τcap)
    (fiberReceipt : ∀T : Finset α,
      GeometryAffineHighSelectedFiberReceipt (α:=T) η₀ u₀ F₀ R₀ (9/4) (9/4)
        (μ/8) 3 1 (μ/64)) :
    let δ:=geometryAffineHighDictionaryRate μ (Fintype.card α)
    ∃τ : ℝ,0<τ ∧ τ≤μ/16 ∧ τ<τcap ∧ ∃g : GeometryAffineLowSchedule,
      g.μ=μ ∧ g.δ=δ ∧ g.τ=τ ∧
      ∀T : Finset α,∃P : HighSourceParameters,
        P.τ=τ ∧ P.bΦ=bΦ ∧ g.e=P.e ∧ g.κ=P.κ ∧ g.vslot=P.vslot ∧
        GeometryAffineHighScheduleGates W μ δ P ∧
        ∃Sp : Finset (ℕ×ℕ),(0,0)∈Sp ∧ ∃degree : ℕ,∃K : ℝ,0<K ∧
        ∀(Q : Ideal O)(hQM : Q≤M)(hQ72 : internalQ Q η₀≤Ideal.span {(72:O)}),
          ∀ᶠZ : ℝ in atTop,2≤Z ∧
            GeometryAffineHighSelectedCostSpec (α:=T) M H hH W hbeta P μ δ
              (geometryAffineHighTarget μ δ) (fun _ _ _ _ _=>True)
              (excluded F₀.character R₀) Cs Sp degree K η₀ Q hQM hQ72 Z := by
  intro δ
  obtain ⟨τ,hτ,hτμ,hτsmall,g,hgμ,hgδ,hgτ,hT⟩:=affine_high_uniform_schedule_of_high W hWs hW μ bΦ τcap hμ hμcap hbΦ hτcap _
    (fun T=>actual_affine_high_selected_all_height_of_fibers
      (α:=T) M H hH η₀ u₀ F₀ R₀ hu₀ W hWs hW hbeta hMarkedUpper μ Cs (Fintype.card α)
      hμ hμcap hCs (Fintype.card_le_of_injective (fun i : T=>i.val) Subtype.val_injective)
      (fiberReceipt T))
  exact ⟨τ,hτ,hτμ,hτsmall,g,hgμ,hgδ,hgτ,hT⟩

/-- Actual source caps are fixed before the shared schedule; each literal
affine high estimate then has its constants before any moving source. -/
theorem actual_affine_high_uniform_literal_schedule_of_fibers_capped
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (W : ℝ→ℂ)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)(hW : ContDiff ℝ ∞ W)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (hMarkedUpper : 2*HeckeZeroSupremum.beta-1≤Cycle63.Optimization.plainCapacityCost)
    (μ bΦ τcap : ℝ)(hμ : 0<μ)(hμcap : μ≤Cycle63.Optimization.geometryLossCap)(hbΦ : 2≤bΦ)(hτcap : 0<τcap)
    (fiberReceipt : ∀T : Finset α,
      GeometryAffineHighSelectedFiberReceipt (α:=T) η₀ u₀ F₀ R₀ (9/4) (9/4)
        (μ/8) 3 1 (μ/64)) :
    let δ:=geometryAffineHighDictionaryRate μ (Fintype.card α)
    ∃τ : ℝ,0<τ ∧ τ≤μ/16 ∧ τ<τcap ∧ ∃g : GeometryAffineLowSchedule,
      g.μ=μ ∧ g.δ=δ ∧ g.τ=τ ∧
      ∀T : Finset α,∃P : HighSourceParameters,
        P.τ=τ ∧ P.bΦ=bΦ ∧ g.e=P.e ∧ g.κ=P.κ ∧ g.vslot=P.vslot ∧
        GeometryAffineHighScheduleGates W μ δ P ∧
        ∃Sp : Finset (ℕ×ℕ),(0,0)∈Sp ∧ ∃degree : ℕ,∃K : ℝ,0<K ∧
        ∀(Q : Ideal O)(hQM : Q≤M)(hQ72 : internalQ Q η₀≤Ideal.span {(72:O)}),
          ∀ᶠZ : ℝ in atTop,2≤Z ∧
            GeometryAffineMainHighSpec (α:=T) M H hH W hW.continuous hWs hbeta P μ δ
              (geometryAffineHighTarget μ δ) (excluded F₀.character R₀)
              Sp degree K η₀ Q hQM hQ72 Z := by
  intro δ
  obtain ⟨Cs,hCs,hcaps⟩:=eventual_actual_affine_exceptional_source_gates (α:=α) M H hH
    W hW.continuous hWs
  obtain ⟨τ,hτ,hτmu,hτsmall,g,hgμ,hgδ,hgτ,hhigh⟩:=actual_affine_high_uniform_schedule_of_fibers_capped
    (α:=α) M H hH η₀ u₀ F₀ R₀ hu₀ W hWs hW hbeta hMarkedUpper μ Cs bΦ τcap hμ hμcap hCs hbΦ hτcap fiberReceipt
  refine ⟨τ,hτ,hτmu,hτsmall,g,hgμ,hgδ,hgτ,?_⟩
  intro T
  obtain ⟨P,hPτ,hPb,he,hκ,hv,gates,Sp,hSp,degree,K,hK,hpaid⟩:=hhigh T
  refine ⟨P,hPτ,hPb,he,hκ,hv,gates,Sp,hSp,degree,K,hK,?_⟩
  intro Q hQM hQ72
  filter_upwards [hpaid Q hQM hQ72,hcaps,eventual_geometry_small_frequency μ hμ]
    with Z hp hc hf
  refine ⟨hp.1,?_⟩
  apply affine_main_high_spec_of_receipts (α:=T) M H hH W hW.continuous hWs hbeta
    P μ δ (geometryAffineHighTarget μ δ) (excluded F₀.character R₀) Cs Sp degree K
    η₀ Q hQM hQ72 Z hμ (hμcap.trans (by norm_num [Cycle63.Optimization.geometryLossCap, Cycle63.Optimization.lowReserveWeight, Cycle63.Optimization.allowanceUnit, Cycle63.Optimization.planeQuadratic, Cycle63.Optimization.slotPrice, Cycle63.Optimization.betaBound])) hf.2 _ hp.2
  unfold GeometryAffineMainLowSourceSpec
  intro θ η w σ freq hσ b state p t X₁ X₂ hX₁ hX₂ hw hwin inp
  exact geometry_affine_source_gates_actual_card inp p (Fintype.card α) Cs Z
    (hc.2 T η θ w σ freq hσ b state p t X₁ X₂ hX₁ hX₂ hw hwin)

/-- One actual root HIGH source schedule; all allocation-fiber and source-cap gates are discharged. -/
theorem actual_root_high_uniform_literal_schedule_capped
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (W : ℝ→ℂ)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)(hW : ContDiff ℝ ∞ W)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (hMarkedUpper : 2*HeckeZeroSupremum.beta-1≤Cycle63.Optimization.plainCapacityCost)
    (μ bΦ τcap : ℝ)(hμ : 0<μ)(hμcap : μ≤Cycle63.Optimization.geometryLossCap)(hbΦ : 2≤bΦ)(hτcap : 0<τcap)
 :
    let δ:=geometryAffineHighDictionaryRate μ (Fintype.card α)
    ∃τ : ℝ,0<τ ∧ τ≤μ/16 ∧ τ<τcap ∧ ∃g : GeometryAffineLowSchedule,
      g.μ=μ ∧ g.δ=δ ∧ g.τ=τ ∧
      ∀T : Finset α,∃P : HighSourceParameters,
        P.τ=τ ∧ P.bΦ=bΦ ∧ g.e=P.e ∧ g.κ=P.κ ∧ g.vslot=P.vslot ∧
        GeometryAffineHighScheduleGates W μ δ P ∧
        ∃Sp : Finset (ℕ×ℕ),(0,0)∈Sp ∧ ∃degree : ℕ,∃K : ℝ,0<K ∧
        ∀(Q : Ideal O)(hQM : Q≤M)(hQ72 : internalQ Q η₀≤Ideal.span {(72:O)}),
          ∀ᶠZ : ℝ in atTop,2≤Z ∧
            GeometryAffineMainHighSpec (α:=T) M H hH W hW.continuous hWs hbeta P μ δ
              (geometryAffineHighTarget μ δ) (excluded F₀.character R₀)
              Sp degree K η₀ Q hQM hQ72 Z := by
  exact actual_affine_high_uniform_literal_schedule_of_fibers_capped (α:=α) M H hH
    η₀ u₀ F₀ R₀ hu₀ W hWs hW hbeta hMarkedUpper μ bΦ τcap hμ hμcap hbΦ hτcap
    (fun T=>geometry_affine_high_selected_fiber_receipt (α:=T) η₀ u₀ F₀ R₀ hu₀ μ hμ)

end
end OAI.SevenEighths.Cycle153RootHigh
#print axioms OAI.SevenEighths.Cycle153RootHigh.actual_root_high_uniform_literal_schedule_capped
