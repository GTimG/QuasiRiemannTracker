/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The earlier global source supplies the complete finite fixed-ray anchor family,
with a common source mesh chosen before every ambient slot type. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.PhysicalParentSources
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.PhysicalParentSources
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths Filter
open QRH.Record12518109Source QRH.Record12518109Existence
open HeckeFamily CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorEnergyInitialState CenteredMomentInductionEnergy
open ConcretePrimeRowBridge CenteredMomentPrimeSlot Cycle61Moment RayFourExpansion
local notation "O" => HeckeFamily.O
local instance parentGlobalQuotientFinite (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

theorem global_second_dictionary_sources (B lam cap Mmin Mmax ε : ℝ)
    (hsource : GlobalSource B lam cap) (hMmin : 0<Mmin) (hε : 0<ε) :
    ∃meshMax : ℝ,0<meshMax ∧ ∀mesh : ℝ,mesh≤meshMax →
      ∀(α : Type)[Fintype α][DecidableEq α],
      ∀(rayM : Ideal O)[NeZero rayM](H : Subgroup (O⧸rayM)ˣ)
        (hH : RayOrthogonality.globalUnits rayM≤H),
      ∀(W : ℝ→ℂ),ContDiff ℝ ∞ W → Function.support W⊆Set.Icc (1:ℝ) 2 →
      ∀bΦ : ℝ,2≤bΦ → ∀(ηanchor η₀ : Character)(Q : Ideal O),
        Q≤rayM → internalQ Q η₀≠0 → internalQ Q η₀≠⊤ →
        internalQ Q η₀≤Ideal.span {(72:O)} →
      ∃degree : ℕ,∃S : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
        ∀ray ψ : RayCharacter,InitialAffineAt (α:=α) rayM H hH (globalFace B lam cap) W
          2 (1/4) (9/4) bΦ mesh (33/50) (33/50) Mmin Mmax ε Z
          (secondFixedDictionary ηanchor (ray,ψ)) η₀ Q degree S C := by
  let unitε := ε/(max 1 Mmax)
  have hden : 0<max (1:ℝ) Mmax := zero_lt_one.trans_le (le_max_left _ _)
  have hue : 0<unitε := div_pos hε hden
  obtain ⟨unitMesh,hum,hu⟩ := hsource unitε hue
  have he : Mmax*unitε≤ε := by
    calc
      Mmax*unitε≤(max 1 Mmax)*unitε := mul_le_mul_of_nonneg_right (le_max_right _ _) hue.le
      _=ε := mul_div_cancel₀ ε hden.ne'
  refine ⟨unitMesh*Mmin,mul_pos hum hMmin,?_⟩
  intro mesh hm α _ _ rayM _ H hH W hW hWs bΦ hbΦ ηanchor η₀ Q hQray hQ0 hQt hQ72
  exact unit_source_second_dictionary (α:=α) hu rayM H hH W hW hWs bΦ mesh Mmin Mmax ε hbΦ
    hMmin hum.le hm hue.le he ηanchor η₀ Q hQray hQ0 hQt hQ72

end
end QRH.Record1252270103Source.PhysicalParentSources
#print axioms QRH.Record1252270103Source.PhysicalParentSources.global_second_dictionary_sources
