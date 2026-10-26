import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.MarkedUniformSchedule
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineHighPayment
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffinePhysicalSelection
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 60000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open Cycle63MarkedPlain
open scoped Classical ContDiff HeckeNotation
open Filter HeckeFamily CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CanonicalQuadraticSieve ConcretePrimeRowBridge Cycle63Moment

variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- One schedule for every subset of the slots, below a height cap: when every subset `T` has a HIGH estimate with its
own profile bound and density degree, there is one height `τ` below `μ/16` and below `τcap`, a schedule `g` of loss
`μ` and dictionary rate `δ` at the height `τ`, and for every subset the literal HIGH source parameters at `τ` satisfy
the schedule gates and the estimate. -/
theorem affine_high_uniform_schedule_of_high
    (W : ℝ→ℂ)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)(hW : ContDiff ℝ ∞ W)
    (μ bΦ τcap : ℝ)(hμ : 0<μ)(hμcap : μ≤Cycle63.Optimization.geometryLossCap)(hbΦ : 2≤bΦ)(hτcap : 0<τcap)
    (Conclusion : Finset α → HighSourceParameters → Prop)
    (high : ∀T : Finset α,∃bound : ℕ→ℝ,(∀k,0<bound k) ∧ ∃J : ℕ,
      ∀P : HighSourceParameters,P.profileBound=bound →
      GeometryAffineHighScheduleGates W μ (geometryAffineHighDictionaryRate μ (Fintype.card α)) P →
      MarkedSchedule P (Fintype.card T) W (33/50) (33/50) →
      8*P.τ≤P.d*P.vslot → 16*P.τ≤P.d*P.vplain → 2*P.τ*(J+1)≤μ/8 → Conclusion T P) :
    ∃τ : ℝ,0<τ ∧ τ≤μ/16 ∧ τ<τcap ∧ ∃g : GeometryAffineLowSchedule,
      g.μ=μ ∧ g.δ=geometryAffineHighDictionaryRate μ (Fintype.card α) ∧ g.τ=τ ∧
      ∀T : Finset α,∃P : HighSourceParameters,
        P.τ=τ ∧ P.bΦ=bΦ ∧ g.e=P.e ∧ g.κ=P.κ ∧ g.vslot=P.vslot ∧
        GeometryAffineHighScheduleGates W μ (geometryAffineHighDictionaryRate μ (Fintype.card α)) P ∧
        Conclusion T P := by
  choose bound hbound J hhigh using high
  let Jcap : ℕ := ⌈μ/(16*τcap)⌉₊
  let J' : Finset α → ℕ := fun T=>max (J T) Jcap
  have hL : 0≤3*((Fintype.card α:ℝ)+2) := by positivity
  have hb : 0≤bΦ := by linarith
  obtain ⟨τ,hτ,hτμ,hτzero,hτw,g,hgμ,hgδ,hgτ,hschedule⟩:=geometry_affine_marked_uniform_schedule
    W hWs hW μ 130 (3*((Fintype.card α:ℝ)+2)) bΦ (Fintype.card α) bound J'
    hμ hμcap (by norm_num) hL hb (fun T k=>(hbound T k).le)
  have hτcap' : τ<τcap := by
    obtain ⟨T⟩ : Nonempty (Finset α) := ⟨∅⟩
    have hs := (hschedule T).2.2.2.2.2.2.1
    change 2*τ*((J' T:ℝ)+1)≤μ/8 at hs
    have hceil : μ/(16*τcap)≤(J' T:ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_max_right (J T) Jcap)
    have hpos : 0<16*τcap := by positivity
    rw [div_le_iff₀ hpos] at hceil
    nlinarith
  refine ⟨τ,hτ,hτμ,hτcap',g,hgμ,hgδ,hgτ,?_⟩
  intro T
  let P:=geometryAffineFinalHighSchedule W hWs hW μ 130 (3*((Fintype.card α:ℝ)+2))
    bΦ τ (Fintype.card α) (bound T) hμ (by norm_num) hL hb hτ (fun k=>(hbound T k).le)
  have hs:=hschedule T
  have gates : GeometryAffineHighScheduleGates W μ (geometryAffineHighDictionaryRate μ (Fintype.card α)) P :=
    geometry_affine_high_schedule_gates W hWs hW μ bΦ τ (Fintype.card α) (bound T)
      hμ hbΦ hτ (fun k=>(hbound T k).le)
  refine ⟨P,rfl,rfl,hs.2.1,hs.2.2.1,hs.2.2.2.1,gates,?_⟩
  have hmarked : MarkedSchedule P (Fintype.card T) W (33/50) (33/50) :=
    (geometry_final_marked_schedule W hWs hW μ 130 (3*((Fintype.card α:ℝ)+2))
      bΦ τ (Fintype.card α) (bound T) hμ hμcap (by norm_num) hL hb hτ
      (fun k=>(hbound T k).le) hτzero hτw).of_card_le
      (Fintype.card_le_of_injective (fun i : T=>i.val) Subtype.val_injective)
  have hdensity : 2*P.τ*((J T:ℝ)+1)≤μ/8 := by
    have h' := hs.2.2.2.2.2.2.1
    change 2*τ*((J' T:ℝ)+1)≤μ/8 at h'
    have hJ : (J T:ℝ)≤(J' T:ℝ) := by exact_mod_cast le_max_left (J T) Jcap
    change 2*τ*((J T:ℝ)+1)≤μ/8
    nlinarith
  exact hhigh T P hs.1 gates hmarked hs.2.2.2.2.1 hs.2.2.2.2.2.1 hdensity

/-- Select every actual-subset density dictionary before fixing one common
height cutoff. Only the scalar loss rate uses the ambient cardinality.
The exact fiber receipt remains explicit until its separate proof is joined. -/
theorem actual_affine_high_uniform_schedule_of_fibers
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (W : ℝ→ℂ)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)(hW : ContDiff ℝ ∞ W)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (hMarkedUpper : 2*HeckeZeroSupremum.beta-1≤Cycle63.Optimization.plainCapacityCost)
    (μ Cs bΦ : ℝ)(hμ : 0<μ)(hμcap : μ≤Cycle63.Optimization.geometryLossCap)(hCs : 1≤Cs)(hbΦ : 2≤bΦ)
    (fiberReceipt : ∀T : Finset α,
      GeometryAffineHighSelectedFiberReceipt (α:=T) η₀ u₀ F₀ R₀ (9/4) (9/4)
        (μ/8) 3 1 (μ/64)) :
    let δ:=geometryAffineHighDictionaryRate μ (Fintype.card α)
    ∃τ : ℝ,0<τ ∧ τ≤μ/16 ∧ ∃g : GeometryAffineLowSchedule,
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
  obtain ⟨τ,hτ,hτμ,-,g,hgμ,hgδ,hgτ,hT⟩:=affine_high_uniform_schedule_of_high W hWs hW μ bΦ 1 hμ hμcap hbΦ one_pos _
    (fun T=>actual_affine_high_selected_all_height_of_fibers
      (α:=T) M H hH η₀ u₀ F₀ R₀ hu₀ W hWs hW hbeta hMarkedUpper μ Cs (Fintype.card α)
      hμ hμcap hCs (Fintype.card_le_of_injective (fun i : T=>i.val) Subtype.val_injective)
      (fiberReceipt T))
  exact ⟨τ,hτ,hτμ,g,hgμ,hgδ,hgτ,hT⟩

/-- Actual source caps are fixed before the shared schedule; each literal
affine high estimate then has its constants before any moving source. -/
theorem actual_affine_high_uniform_literal_schedule_of_fibers
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (W : ℝ→ℂ)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)(hW : ContDiff ℝ ∞ W)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (hMarkedUpper : 2*HeckeZeroSupremum.beta-1≤Cycle63.Optimization.plainCapacityCost)
    (μ bΦ : ℝ)(hμ : 0<μ)(hμcap : μ≤Cycle63.Optimization.geometryLossCap)(hbΦ : 2≤bΦ)
    (fiberReceipt : ∀T : Finset α,
      GeometryAffineHighSelectedFiberReceipt (α:=T) η₀ u₀ F₀ R₀ (9/4) (9/4)
        (μ/8) 3 1 (μ/64)) :
    let δ:=geometryAffineHighDictionaryRate μ (Fintype.card α)
    ∃τ : ℝ,0<τ ∧ τ≤μ/16 ∧ ∃g : GeometryAffineLowSchedule,
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
  obtain ⟨τ,hτ,hτcap,g,hgμ,hgδ,hgτ,hhigh⟩:=actual_affine_high_uniform_schedule_of_fibers
    (α:=α) M H hH η₀ u₀ F₀ R₀ hu₀ W hWs hW hbeta hMarkedUpper μ Cs bΦ hμ hμcap hCs hbΦ fiberReceipt
  refine ⟨τ,hτ,hτcap,g,hgμ,hgδ,hgτ,?_⟩
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

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
