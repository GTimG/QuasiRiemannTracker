/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Fixed-Q adaptation of CorrectedGeometricEnergy; inherited source notices remain required.
The actual completed corrected energy is paid from finite source geometry. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.CorrectedGeometry
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.CorrectedFixedQCompleted
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open ConcretePrimeRowBridge CompletedGauss CanonicalRowCompletion
open CenteredExceptionalProfile CenteredMomentRestrictedSource
open CenteredMomentFiniteProfileExceptional CenteredMomentAllocatedDetectorAmplitude
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentCanonicalFirst
open CenteredMomentAmplificationChildInput CenteredMomentAddedZeroUniform
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSecondHeightFamily
open CenteredMomentHeckeExpansion CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalFrequency CenteredMomentForcing CenteredMomentChildRows
open QRH.Record1252270103Low QRH.Record1252270103Source.High.CorrectedCentered
open Record1252270103Second
local notation "O"=>ActualEisensteinCubic.O
local instance correctedFixedQGeometricEnergyTupleDecidableEq (ι : Type*) : DecidableEq (ι⊕Fin 2) := Classical.decEq _

theorem corrected_fixedQ_source_energy_from_geometry
    (a b ε Bχ BA Bpool α : ℝ) (depth : ℕ)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hBχ : 0≤Bχ) (hBA : 0≤BA)
    (hBpool : 0≤Bpool) (hα0 : 0≤α) (hα : α<1/2) :
    ∃J : ℕ,∃S : Finset (ℕ×ℕ),(0,0)∈S ∧
      ∀Q : Ideal O,Q≠0→Q≠⊤→Q≤Ideal.span {(72:O)}→∃C₀ : ℝ,0<C₀ ∧
      ∀W₁ W₂ : 𝓢(ℝ,ℂ),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b→
      ∀ι : Type*,∀inst : Fintype ι,∀s : Input ι,
      ∀Z : ℝ,1<Z→∀η τ : Character,∀χ : RayFourExpansion.RayCharacter,
      ∀C D : Ideal O,∀hC : Supported C,∀U : Finset (CommonIndex C D),
      idealCoeff η C≠0→
      ∀A₁ A₂ Df K R : Ideal O,∀P : Finset (Ideal O),
      CorrectedSourceGeometry s W₁ W₂ b Z BA Bpool depth A₁ A₂ Df K R P→
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      ∀Cm : Ideal O,Cm∣R→
      (∀I : Ideal O,Supported I→IsCoprime Cm I→∀t : ℝ,
        heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*
          RayFourExpansion.rayCharacter χ (primaryGenerator I))→
      ∀keep : O→Prop,∀Φ : 𝓢(ℝ,ℂ),(∀x,0≤(Φ x).re)→∀H Cr Mrow : ℝ,0≤Cr→
      CorrectedRowGeometry Q η χ C D U R Z Bχ Cr Mrow keep Φ H→
      ∀t L : ℝ,0<L→L≤s.X₁→L≤s.X₂→L≤s.Y₁→L≤s.Y₂→
      sourceRestrictedEnergy keep (finiteColumns (Fintype.piFinset s.pools))
        (QRH.Record1252270103Source.High.CoupledFirst.coefficient s
          (Collision.markedSourceModifier A₁ A₂ Df K (poolCorrection P)) R 1)
        (heightCoeff τ t) Φ H/volume s≤
      exceptionalRowCost Q C D U Z Cr Mrow*
        (C₀*(sourceControl S W₁*sourceControl S W₂)*Z^ε*(1+‖t‖)^J*
          (max 1 L)^(-α)*slotControl s.toData)^2*volume s*SchwartzMap.seminorm ℝ 0 0 Φ := by
  obtain ⟨J,S,hS,hsource⟩:=corrected_fixedQ_marked_completed_exceptional_energy
    a b ε Bχ BA Bpool α depth ha hb hε hBχ hBA hBpool hα0 hα
  refine ⟨J,S,hS,?_⟩
  intro Q hQ0 hQ hQ72
  obtain ⟨C₀,hC₀,hsource⟩:=hsource Q hQ0 hQ hQ72
  refine ⟨C₀,hC₀,?_⟩
  intro W₁ W₂ hs₁ hs₂ ι inst s Z hZ η τ χ C D hC U hη A₁ A₂ Df K R P hg
    A Cm hCm hτ keep Φ hΦ H Cr Mrow hCr hr t L hL hX₁ hX₂ hY₁ hY₂
  rw [source_family_energy s _ Cm R 1 hCm η τ χ A hτ t keep Φ H]
  exact hsource W₁ W₂ hs₁ hs₂ ι inst s hg.profile_left hg.profile_right
    hg.support_left hg.support_right Z hZ η χ C D hC U hη R hg.puncture_ne
    keep Φ hΦ H hr.row_nonzero hr.inducing hr.conductor Cr Mrow hCr hr.radius
    A₁ A₂ Df K hg.frozen_left_ne hg.frozen_right_ne hg.correction_dvd hg.frozen_norm
    P hg.pool_nonempty hg.pool_prime hg.pool_norm_lower hg.pool_norm_upper hg.pool_avoids
    hg.pool_budget t L hL hX₁ hX₂ hY₁ hY₂ hg.residual_count
end
end OAI.SevenEighths.Record1252270103Source
#print axioms OAI.SevenEighths.Record1252270103Source.corrected_fixedQ_source_energy_from_geometry
