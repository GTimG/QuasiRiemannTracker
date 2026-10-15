/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineMainCompletePayment
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineErrorCompletePayment
import Candidate.Cycle63.Physical.InitialMass.GeometryAffinePaidAssembly

set_option autoImplicit false
set_option maxHeartbeats 80000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonProfile
open CenteredMomentEnergyState CenteredMomentEnergyBands Cycle63InitialSource
local notation "O" => HeckeFamily.O

variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- Both original retained terms already include their single prime payment.
Specializing the moving state does not alter the original error witness. -/
theorem affine_paid_subset_components_of_specs
    (Sbad : Finset (Ideal O))(W : ℝ→ℂ)(hW : Continuous W)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (η η₀ : Character)(Q : Ideal O)(bΦ mesh εaffine τ : ℝ)(Ψ : 𝓢(ℝ,ℂ))(T : Finset α)
    (Sm Se : Finset (ℕ×ℕ))(Dm De : ℕ)(Cm Ce Z : ℝ)
    (hm : GeometryAffineMainPaidSpec M H hH Sbad W hW hWs η η₀ mesh
      (geometryLossUnit 1 εaffine) T Sm Dm Cm Z)
    (he : GeometryAffineErrorPaidSpec M H hH Sbad W hW hWs Ψ η η₀ mesh εaffine T Se De Ce Z) :
    GeometryAffinePaidSubsetComponents M H hH Sbad W hW hWs η η₀ Q bΦ mesh
      (geometryLossUnit 1 εaffine) τ Ψ T Sm Se Dm De Cm Ce Z := by
  intro hZ θ w σ freq t height hw hwm hσlo hσhi hh hv hcut Φ hsΦ hpΦ p X₁ X₂ hX₁ hX₂
    hlo₁ hhi₁ hlo₂ hhi₂ hwlo hwhi hcone state s amp P key hkey reflected firstHeight
    side phase hK First
  have hη : state.character=η := rfl
  have hmain:=hm hZ θ w σ freq (fun i=>⟨hσlo i,hσhi i⟩) bΦ state hη p t X₁ X₂ hX₁ hX₂
    hw hwm hlo₁ hlo₂ hhi₁ hhi₂ hwlo hwhi hcone Ψ reflected key firstHeight height hh hv 1
  constructor
  · simpa only [mul_assoc] using hmain
  · intro υ hυ
    have herror:=he hZ θ w σ freq (fun i=>⟨hσlo i,hσhi i⟩) bΦ state hη p t X₁ X₂ hX₁ hX₂
      hw hwm hlo₁ hlo₂ hhi₁ hhi₂ hwlo hwhi hcone reflected key firstHeight height hh hv υ hυ
    simpa only [mul_assoc] using herror

/-- Uniform paid main and error families give the literal geometry budget.
The error family remains an explicit premise until its source aggregation is joined. -/
theorem literal_affine_geometry_budget_of_main_error
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (η η₀ : Character)(Q : Ideal O)(bΦ mesh εaffine τ : ℝ)(hε : 0<εaffine)
    (hmesh : mesh<(902420521/120632400000:ℝ)/2)
    (hmain : ∀T : Finset α,∃S : Finset (ℕ×ℕ),∃D : ℕ,∃C : ℝ,0≤C ∧
      ∀ᶠZ : ℝ in atTop,1<Z ∧ GeometryAffineMainPaidSpec M H hH Sbad W hW hWs η η₀ mesh
        (geometryLossUnit 1 εaffine) T S D C Z)
    (herror : ∀Ψ : 𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) →
      (∀x,0≤(Ψ x).re) →
      ∀T : Finset α,∃S : Finset (ℕ×ℕ),∃D : ℕ,∃C : ℝ,0≤C ∧
        ∀ᶠZ : ℝ in atTop,1<Z ∧
          GeometryAffineErrorPaidSpec M H hH Sbad W hW hWs Ψ η η₀ mesh εaffine T S D C Z) :
    LiteralAffineGeometryBudget (α:=α) M H hH W hW hWs η η₀ Q bΦ mesh εaffine τ
      (geometryLossUnit 1 εaffine/64) := by
  have hμ:=geometry_loss_unit_pos 1 εaffine (by norm_num) hε
  have hμcap : geometryLossUnit 1 εaffine≤1/128 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  apply literal_affine_geometry_budget_of_paid_components M H hH Sbad hbad W hW hWs
    η η₀ Q bΦ εaffine mesh (geometryLossUnit 1 εaffine) εaffine τ
    hε hμ hμcap hmesh hε.le
  intro Ψ hΨ hpΨ T
  obtain ⟨Sm,Dm,Cm,hCm,hm⟩:=hmain T
  obtain ⟨Se,De,Ce,hCe,he⟩:=herror Ψ hΨ hpΨ T
  refine ⟨Sm,Se,Dm,De,Cm,Ce,hCm,hCe,?_⟩
  filter_upwards [hm,he] with Z hmZ heZ
  exact affine_paid_subset_components_of_specs M H hH Sbad W hW hWs η η₀ Q bΦ mesh εaffine
    τ Ψ T Sm Se Dm De Cm Ce Z hmZ.2 heZ.2

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.affine_paid_subset_components_of_specs
#print axioms OAI.SevenEighths.Cycle63InitialMass.literal_affine_geometry_budget_of_main_error
