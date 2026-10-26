import Candidate.Uneven.BootstrapSchedule
import Candidate.Uneven.MainCellGeometry
import Candidate.Cycle63.Physical.InitialMass.GeometryMeshChoice
import Candidate.Uneven.MainInitialContract
import Candidate.Uneven.MainZeroPayment
import Candidate.Uneven.MainHighMainCompletePayment
import Candidate.Uneven.MainAffineErrorSpecs
import Candidate.Uneven.MainAssemblyPaidAssembly
import Candidate.Uneven.MainAssemblyInitialHeight
import Candidate.Uneven.MainAmplifiedRemainder
import Candidate.Uneven.MainErrorMain
import Candidate.Uneven.MainErrorParameters
import Candidate.Uneven.MainAffineErrorPayment
import Candidate.Affine.Supply
import Candidate.Target830.Physical.AffineInput
import Candidate.Uneven.MainHighMainUniform
import Candidate.Uneven.MainAffineErrorFamily
import Candidate.Uneven.MainAffineInput

/- Original module: Candidate.Uneven.MainAssemblyMesh. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
noncomputable section
namespace OAI.SevenEighths.MainAssembly
open Cycle63InitialMass SaturatedPlain BootstrapPlain

def chosenMesh (ε : ℝ) : ℝ :=
  min (min (geometryAnalyticMesh 1 1 (ε/4) 2 28 1)
    (Cycle63FirstActual.comparisonMesh 1 1 (ε/2)))
    (min (Sil.Uneven.MainSource.amplifierMinimum/4) (bootstrapRawMesh*fineRawCore/31))

theorem chosen_mesh_admission (ε : ℝ) (hε : 0<ε) :
    let μ:=geometryLossUnit 1 (ε/4)
    0< chosenMesh ε ∧
    chosenMesh ε≤ Cycle63FirstActual.comparisonMesh 1 1 (ε/2) ∧
    chosenMesh ε≤ Cycle25.Energy.commonMesh 2 28 1 (μ/8) ∧
    chosenMesh ε≤μ/8 ∧ chosenMesh ε< Sil.Uneven.MainSource.amplifierMinimum/2 ∧
    chosenMesh ε≤ bootstrapRawMesh*fineRawCore := by
  intro μ
  have ha:=geometry_analytic_mesh_admission 1 1 (ε/4) 2 28 1
    (by norm_num) (by norm_num) (by positivity) (by norm_num) (by norm_num)
  have hc:=Cycle63FirstActual.comparisonMesh_pos 1 1 (ε/2)
    (by norm_num) (by norm_num) (by positivity)
  have hf : 0< Sil.Uneven.MainSource.amplifierMinimum := by norm_num [Sil.Uneven.MainSource.amplifierMinimum]
  have hfm : 0 < bootstrapRawMesh := bootstrap_raw_mesh_gates.1
  have hfc : 0 < fineRawCore := by norm_num [fineRawCore]
  have hm : 0 < bootstrapRawMesh*fineRawCore/31 := by positivity
  have hleft : chosenMesh ε ≤ min (geometryAnalyticMesh 1 1 (ε/4) 2 28 1)
      (Cycle63FirstActual.comparisonMesh 1 1 (ε/2)) := min_le_left _ _
  have hright : chosenMesh ε ≤ min (Sil.Uneven.MainSource.amplifierMinimum/4)
      (bootstrapRawMesh*fineRawCore/31) := min_le_right _ _
  have han:=hleft.trans (min_le_left _ _)
  have hamp:=hright.trans (min_le_left _ _)
  have hmark:=hright.trans (min_le_right _ _)
  have hpos : 0< chosenMesh ε := lt_min (lt_min ha.1 hc) (lt_min (by positivity) hm)
  refine ⟨hpos,hleft.trans (min_le_right _ _),han.trans ha.2.2.1,
    han.trans ha.2.2.2.1,by linarith only [hamp,hf],?_⟩
  exact hmark.trans (by nlinarith [mul_pos hfm hfc])

end OAI.SevenEighths.MainAssembly
end

/- Original module: Candidate.Uneven.MainAssemblySourceMesh. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
namespace OAI.SevenEighths.MainAssembly
noncomputable section
open Sil.Uneven.MainSource
/-- The fixed cap licenses the entire actual marked schedule. It is chosen
before the detector; final error monotonicity restores the requested error. -/
def cappedError (ε : ℝ) : ℝ := min ε (1/10000000000000000000000000000)
def sourceMesh (ε : ℝ) : ℝ := chosenMesh (cappedError ε)
theorem capped_error_bounds {ε : ℝ} (hε : 0<ε) :
    0< cappedError ε ∧ cappedError ε≤ε ∧
      cappedError ε≤1/10000000000000000000000000000 := by
  exact ⟨lt_min hε (by norm_num),min_le_left _ _,min_le_right _ _⟩
theorem source_mesh_pos {ε : ℝ} (hε : 0<ε) : 0< sourceMesh ε :=
  (chosen_mesh_admission (cappedError ε) (capped_error_bounds hε).1).1
end
end OAI.SevenEighths.MainAssembly
end

/- Original module: Candidate.Uneven.MainAssemblyPaidComponents. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 80000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.MainAssembly
open Target830.Source.Uneven
noncomputable section
open Sil.Uneven.MainSource
open OAI.SevenEighths.Cycle63InitialMass OAI.SevenEighths.Cycle63Physical OAI.SevenEighths.Cycle63SecondZero
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonProfile
open CenteredMomentEnergyState CenteredMomentEnergyBands Cycle63InitialSource
local notation "O" => HeckeFamily.O

variable {plane : Sil.Uneven.MainSource.Plane}
variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- Both original retained terms already include their single prime payment.
Specializing the moving state does not alter the original error witness. -/
theorem affine_paid_subset_components_of_specs
    (Sbad : Finset (Ideal O))(W : ℝ→ℂ)(hW : Continuous W)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (η η₀ : Character)(Q : Ideal O)(bΦ mesh εaffine τ : ℝ)(Ψ : 𝓢(ℝ,ℂ))(T : Finset α)
    (Sm Se : Finset (ℕ×ℕ))(Dm De : ℕ)(Cm Ce Z : ℝ)
    (hm : MainHigh.GeometryAffineMainPaidSpec (plane:=plane) M H hH Sbad W hW hWs η η₀ mesh
      (geometryLossUnit 1 εaffine) T Sm Dm Cm Z)
    (he : MainErrorReconstruction.GeometryAffineErrorPaidSpec (plane:=plane) M H hH Sbad W hW hWs Ψ η η₀ mesh εaffine T Se De Ce Z) :
    GeometryAffinePaidSubsetComponents (plane:=plane) M H hH Sbad W hW hWs η η₀ Q bΦ mesh
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
    (hmesh : mesh< Sil.Uneven.MainSource.amplifierMinimum/2)
    (hmain : ∀T : Finset α,∃S : Finset (ℕ×ℕ),∃D : ℕ,∃C : ℝ,0≤ C ∧
      ∀ᶠZ : ℝ in atTop,1< Z ∧ MainHigh.GeometryAffineMainPaidSpec (plane:=plane) M H hH Sbad W hW hWs η η₀ mesh
        (geometryLossUnit 1 εaffine) T S D C Z)
    (herror : ∀Ψ : 𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) →
      (∀x,0≤(Ψ x).re) →
      ∀T : Finset α,∃S : Finset (ℕ×ℕ),∃D : ℕ,∃C : ℝ,0≤ C ∧
        ∀ᶠZ : ℝ in atTop,1< Z ∧
          MainErrorReconstruction.GeometryAffineErrorPaidSpec (plane:=plane) M H hH Sbad W hW hWs Ψ η η₀ mesh εaffine T S D C Z) :
    LiteralAffineGeometryBudget (plane:=plane) (α:=α) M H hH W hW hWs η η₀ Q bΦ mesh εaffine τ
      (geometryLossUnit 1 εaffine/64) := by
  have hμ:=geometry_loss_unit_pos 1 εaffine (by norm_num) hε
  have hμcap : geometryLossUnit 1 εaffine≤1/128 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  apply literal_affine_geometry_budget_of_paid_components (plane:=plane) M H hH Sbad hbad W hW hWs
    η η₀ Q bΦ εaffine mesh (geometryLossUnit 1 εaffine) εaffine τ
    hε hμ hμcap hmesh hε.le
  intro Ψ hΨ hpΨ T
  obtain ⟨Sm,Dm,Cm,hCm,hm⟩:=hmain T
  obtain ⟨Se,De,Ce,hCe,he⟩:=herror Ψ hΨ hpΨ T
  refine ⟨Sm,Se,Dm,De,Cm,Ce,hCm,hCe,?_⟩
  filter_upwards [hm,he] with Z hmZ heZ
  exact affine_paid_subset_components_of_specs (plane:=plane) M H hH Sbad W hW hWs η η₀ Q bΦ mesh εaffine
    τ Ψ T Sm Se Dm De Cm Ce Z hmZ.2 heZ.2

end
end OAI.SevenEighths.MainAssembly
end

/- Original module: Candidate.Uneven.MainAssemblyErrorMono. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
set_option autoImplicit false
namespace OAI.SevenEighths.MainAssembly
noncomputable section
open Sil.Uneven.MainSource
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource QuadraticInitialBound Cycle63Moment
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (R : Ideal O) [NeZero R]
local instance : Finite (O ⧸ R) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne R)
variable (H : Subgroup (O ⧸ R)ˣ) (hH : RayOrthogonality.globalUnits R≤ H)

/-- A proved smaller source error is enlarged only after the finite
parameters, mesh and controls have been fixed. -/
theorem initial_affine_error_mono (plane : Sil.Uneven.MainSource.Plane)
    (W : ℝ→ℂ) (bslot a b bΦ mesh lo hi Mmin Mmax εsmall εbig Z : ℝ)
    (η η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ×ℕ)) (C : ℝ)
    (hC : 0≤ C) (hZ : 1< Z) (he : εsmall≤εbig)
    (h : MainInitial.InitialAffineAt (P:=plane) (α:=α) R H hH W bslot a b bΦ mesh lo hi Mmin Mmax
      εsmall Z η η₀ Q degree S C) :
    MainInitial.InitialAffineAt (P:=plane) (α:=α) R H hH W bslot a b bΦ mesh lo hi Mmin Mmax
      εbig Z η η₀ Q degree S C := by
  intro T θ w σ v t height hw hwm hσlo hσhi hh hv width hwidth hwidthmax
    Φ hΦ hΦpos p X₁ X₂ hX₁ hX₂ hl₁ hu₁ hl₂ hu₂ hwl hwu hcap
  have hb:=h T θ w σ v t height hw hwm hσlo hσhi hh hv width hwidth hwidthmax
    Φ hΦ hΦpos p X₁ X₂ hX₁ hX₂ hl₁ hu₁ hl₂ hu₂ hwl hwu hcap
  apply hb.trans
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))
    (by have hd:=diagonalControl_nonneg Φ; positivity)
end
end OAI.SevenEighths.MainAssembly
end

/- Original module: Candidate.Uneven.MainAffineErrorCompletePayment. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.MainErrorReconstruction
open OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open Sil.Uneven.MainSource
variable {plane : Plane}
open OAI.SevenEighths.MainReconstruction
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondEnergySplit
open CenteredMomentAmplificationErrorEnergy CenteredMomentAllocatedRayDictionary
open CenteredMomentPrimeElements CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentLogDyadic RayFourExpansion
open Filter CenteredMomentCommonProfile CenteredMomentEnergyState CenteredMomentEnergyBands
open Cycle63InitialSource CenteredMomentAmplificationRadicalFamily CenteredMomentChildRows
open CenteredMomentSecondHeightFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O
attribute [local instance] geometryErrorOrdinaryContractionDecidable

variable {α : Type}[Fintype α]

/-- Increasing the positive numerator preserves the exact ratio-fiber bound. -/
theorem affine_error_second_normalized_envelope_mono
    {Label : Type*}[Fintype Label][DecidableEq α]
    (W : 𝓢(ℝ,ℂ))(degree windowDegree : ℕ)
    (d : Label→SecondInputDatum α)(w : Label→ℂ)(E E' Hratio : ℤ→ℝ)
    (hH : ∀r∈secondRatioBins (fun l=>(d l).block),0 < Hratio r)
    (hE : ∀r∈secondRatioBins (fun l=>(d l).block),E r ≤ E' r)
    (h : SecondNormalizedBound W degree windowDegree d w E Hratio) :
    SecondNormalizedBound W degree windowDegree d w E' Hratio := by
  intro r hr reflected t u
  have he : (if reflected then E r/Hratio r else E r*Hratio r) ≤ 
      (if reflected then E' r/Hratio r else E' r*Hratio r) := by
    cases reflected
    · exact mul_le_mul_of_nonneg_right (hE r hr) (hH r hr).le
    · exact div_le_div_of_nonneg_right (hE r hr) (hH r hr).le
  exact (h r hr reflected t u).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right he (by positivity)) (by positivity))

/-- The original selected datum and coefficient are preserved by an envelope increase. -/
theorem geometry_affine_error_normalized_receipt_mono
    (degree windowDegree : ℕ)(reflected : Bool)(s : Input α)(Ψ : 𝓢(ℝ,ℂ))
    (Z amp ξ reserve t : ℝ)(hZ : 1 < Z)(key : ℤ×(Fin 5→ℤ))(P : Finset (Ideal O))
    (υ : GeometryLowFirstIndex (α:=α) reflected s (1:Ideal O) (1:Ideal O)
      (Z^(1:ℝ)) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key→
      elementPool P→Fin 3→RayCharacter→Character)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (Qfix : Ideal O)(m : O)(numerator numerator' : ℝ)
    (hle : numerator ≤ numerator')
    (h : GeometryErrorNormalizedFamilyReceipt degree windowDegree reflected s Ψ
      Z amp ξ reserve t hZ key P υ hz₁ hz₂ Qfix m numerator) :
    GeometryErrorNormalizedFamilyReceipt degree windowDegree reflected s Ψ
      Z amp ξ reserve t hZ key P υ hz₁ hz₂ Qfix m numerator' := by
  obtain ⟨χ,Hratio,hH,hn⟩:=h
  refine ⟨χ,Hratio,hH,?_⟩
  exact affine_error_second_normalized_envelope_mono _ degree windowDegree _ _ _ _ _
    hH (fun _ _=> hle) hn

private theorem affine_error_complete_profile_zero (p : Profiles (1/4) (9/4))(i : Fin 2) :
    p.profile i 0=0 := by
  by_contra h
  have hh:=(p.support i h).1
  norm_num at hh

variable [DecidableEq α]
variable (rayM : Ideal O)[NeZero rayM]
local instance affineErrorCompletePaymentFiniteQuotient : Finite (O⧸rayM):=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ)(hH : RayOrthogonality.globalUnits rayM ≤ H)

/-- Conditional adapter from the exact uniform normalized-family callback to
paid original retained error. The callback is the remaining analytic obligation. -/
theorem actual_affine_error_complete_payment
    (T : Finset α)(A degree windowDegree dN : ℕ)
    (hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus)
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (Ψ : 𝓢(ℝ,ℂ))(ηseed η₀ : Character)(εaffine mesh : ℝ)(hε : 0 < εaffine)(hεcap : εaffine ≤ 1/10000000000000000000000000000)
    (hmesh : mesh < Sil.Uneven.MainSource.amplifierMinimum/2)
    (Qfix : Ideal O)(hQ : Qfix≠0)(hQt : Qfix≠⊤)(hQ72 : Qfix ≤ Ideal.span {(72:O)})
    (SN : Finset (ℕ×ℕ))(Cn : ℝ)(hCn : 0 ≤ Cn)
    (hnormalized : ∀ᶠZ : ℝ in atTop,
      GeometryAffineErrorNormalizedSpec (plane:=plane) rayM H hH Sbad W hW hWs Ψ ηseed η₀ mesh εaffine T
        degree windowDegree Qfix SN dN Cn Z) :
    ∃S : Finset (ℕ×ℕ),∃D : ℕ,∃Ce : ℝ,0 ≤ Ce ∧
      ∀ᶠZ : ℝ in atTop,1 < Z ∧
        GeometryAffineErrorPaidSpec (plane:=plane) rayM H hH Sbad W hW hWs Ψ ηseed η₀ mesh εaffine T S D Ce Z := by
  obtain ⟨K,hK,SE,dE,hpaid⟩:=actual_affine_error_uniform_component_payment (plane:=plane) (α:=α) rayM H hH
    A degree windowDegree hc hs Sbad hbad W hW hWs ηseed εaffine mesh hε hεcap hmesh
    Qfix hQ hQt hQ72 Cn hCn
  let S:=SE∪SN
  let D:=max dE dN
  have hSE : SE⊆S := Finset.subset_union_left
  have hSN : SN⊆S := Finset.subset_union_right
  have hdE : dE ≤ D := le_max_left _ _
  have hdN : dN ≤ D := le_max_right _ _
  refine ⟨S,D,K,hK,?_⟩
  filter_upwards [hpaid,hnormalized] with Z hp hn
  refine ⟨hp.1,?_⟩
  intro hZ θ w σ freq hσ bΦ state hη p t X₁ X₂ hX₁ hX₂ hw hwm hlo₁ hlo₂ hhi₁ hhi₂
    hwlo hwhi hcone reflected key firstHeight height hheight hfreq s μ N δ amp P control υ hυ
  letI : DecidableEq T:=Classical.decEq T
  have hsource:=hn hZ θ w σ freq hσ bΦ state hη p t X₁ X₂ hX₁ hX₂ hw hwm
    hlo₁ hlo₂ hhi₁ hhi₂ hwlo hwhi hcone reflected key firstHeight height hheight hfreq υ hυ
  have hside : 0 ≤ geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key :=
    (geometry_high_factor_pos reflected _ key (by unfold geometrySupportConstant;positivity)).le
  have hprofile := pow_le_pow_left₀ (p.control_nonneg SN) (Cycle63Physical.profile_control_mono p hSN) 2
  have hbase : (1+|firstHeight|+height)^dN ≤ (1+|firstHeight|+height)^D :=
    pow_le_pow_right₀ (by linarith [abs_nonneg firstHeight]) hdN
  have hcontrol : (p.control SN)^2*geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*
        (1+|firstHeight|+height)^dN ≤ control := by
    exact mul_le_mul (mul_le_mul_of_nonneg_right hprofile hside) hbase
      (pow_nonneg (by positivity) _) (by positivity)
  let exponent:=(2*δ+3*(3*((N:ℝ)+2))*δ)+(4*δ+δ-(1/2000000000:ℝ))
  have hnum : Cn*((p.control SN)^2*geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*
        (1+|firstHeight|+height)^dN)*Z^exponent ≤ Cn*control*Z^exponent :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcontrol hCn)
      (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
  have hreceipt := geometry_affine_error_normalized_receipt_mono degree windowDegree reflected s Ψ
    Z amp (μ/64) (μ/8) firstHeight hZ key P υ (affine_error_complete_profile_zero p 0)
    (affine_error_complete_profile_zero p 1) Qfix fixedBadMask _ _ hnum hsource
  exact hp.2 hZ T η₀ θ w σ freq hσ bΦ state hη p t X₁ X₂ hX₁ hX₂ hw hwm
    hlo₁ hlo₂ hhi₁ hhi₂ hwlo hwhi hcone S D hSE hdE Ψ reflected key firstHeight height hheight υ hυ hreceipt

/-- Conditional finite-carrier adapter. Each exact normalized callback fixes
its constants before Z and all moving sources, then the original error is paid. -/
theorem actual_affine_error_uniform_paid_of_normalized
    (A : ℕ)(hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus)
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (Ψ : 𝓢(ℝ,ℂ))(ηseed η₀ : Character)(εaffine mesh : ℝ)(hε : 0 < εaffine)(hεcap : εaffine ≤ 1/10000000000000000000000000000)
    (hmesh : mesh < Sil.Uneven.MainSource.amplifierMinimum/2)
    (Qfix : Ideal O)(hQ : Qfix≠0)(hQt : Qfix≠⊤)(hQ72 : Qfix ≤ Ideal.span {(72:O)})
    (hnormalized : ∀T : Finset α,∃degree windowDegree dN : ℕ,
      ∃SN : Finset (ℕ×ℕ),∃Cn : ℝ,0 ≤ Cn ∧ ∀ᶠZ : ℝ in atTop,
        GeometryAffineErrorNormalizedSpec (plane:=plane) rayM H hH Sbad W hW hWs Ψ ηseed η₀ mesh εaffine T
          degree windowDegree Qfix SN dN Cn Z) :
    ∀T : Finset α,∃S : Finset (ℕ×ℕ),∃D : ℕ,∃Ce : ℝ,0 ≤ Ce ∧
      ∀ᶠZ : ℝ in atTop,1 < Z ∧
        GeometryAffineErrorPaidSpec (plane:=plane) rayM H hH Sbad W hW hWs Ψ ηseed η₀ mesh εaffine T S D Ce Z := by
  intro T
  obtain ⟨degree,windowDegree,dN,SN,Cn,hCn,hn⟩:=hnormalized T
  exact actual_affine_error_complete_payment (plane:=plane) rayM H hH T A degree windowDegree dN hc hs
    Sbad hbad W hW hWs Ψ ηseed η₀ εaffine mesh hε hεcap hmesh Qfix hQ hQt hQ72 SN Cn hCn hn

end
end OAI.SevenEighths.MainErrorReconstruction
end

/- Original module: Candidate.Uneven.MainAssemblyInitialSupplier. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Actual arbitrary detector-label supplier for .874830.
Character identities and predecessor attribution retained; Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.MainAssembly
open Target830.Source.Uneven
noncomputable section
open Sil.Uneven.MainSource
open scoped Classical BigOperators ContDiff ComplexConjugate SchwartzMap
open Filter HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CenteredMomentSecondHeightFamily CenteredMomentNaturalRowSource
open ProbePhysical CenteredMomentDetectorDictionary Cycle25ProbeFinalAssembly
open Cycle25WeightedNumeratorPhysical CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput CenteredMomentLogDyadic
open Cycle63MarkedPlain Cycle63InitialMass
local notation "O" => HeckeFamily.O
/-- The initial affine moment for one detector label. -/
theorem detector_label_initial_affine_capped (plane : Sil.Uneven.MainSource.Plane) {D : Cycle25.Weighted.MomentData} (S : WeightedSourceData D)
    (η : Character) (label : Sum Bool (RayQuotient.Characters S.modulus ⊤))
    (hβlo : 51/100≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (hκbeta : 2*HeckeZeroSupremum.beta-1≤ plane.incumbent)
    (ε : ℝ) (hε : 0< ε) (hεcap : ε≤1/10000000000000000000000000000) (mesh : ℝ) (hmesh0 : 0< mesh)
    (hmesh : mesh ≤ chosenMesh ε) (bΦ : ℝ) (hbΦ : 2≤ bΦ) :
    let ηl := sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label
    ∃degree : ℕ,∃Sd : Finset (ℕ×ℕ),∃C : ℝ,0< C ∧ ∀ᶠU : ℝ in atTop,
      MainInitial.InitialAffineAt (P:=plane) (α:=Fin D.N) S.modulus ⊤ le_top
        (fun x=> conj (S.W x)) 2 (1/4) (9/4) bΦ mesh (33/50) (33/50) 1 1 ε U
        ηl ηl (weighted_sourceFixedIdeal S) degree Sd C := by
  intro ηl
  let W:=fun x=> conj (S.W x)
  have hW : ContDiff ℝ ∞ W:=Complex.conjCLE.contDiff.comp (S.W.smooth ⊤)
  have hs : Function.support W⊆Set.Icc (1:ℝ) 2:=by
    intro x hx
    exact S.complex_support (by intro hz;exact hx (by change conj (S.W x)=0;rw [hz];simp))
  obtain ⟨hm0,hmcomp,hmcommon,hmmu,hmamp,hmmarked⟩:=chosen_mesh_admission ε hε
  have hmeshlt : mesh< Sil.Uneven.MainSource.amplifierMinimum/2:=hmesh.trans_lt hmamp
  have hmeshμ : mesh≤ geometryLossUnit 1 (ε/4)/8:=hmesh.trans hmmu
  have hmeshcap : mesh≤ Cycle25.Energy.commonMesh 2 28 1 (geometryLossUnit 1 (ε/4)/8):=
    hmesh.trans hmcommon
  have hmarkedmesh : mesh≤ BootstrapPlain.bootstrapRawMesh*SaturatedPlain.fineRawCore:=hmesh.trans hmmarked
  have hε4 : 0< ε/4 := by positivity
  let row := naturalRowOf ηl (detector_label_modulus S η label)
  obtain ⟨τ,hτ,_hτcap,hpaid⟩:=MainHigh.actual_affine_main_uniform_paid (plane:=plane) (α:=Fin D.N)
    S.modulus ⊤ le_top 0 logAnnulus_compact logAnnulus_smooth S.S S.exclusions.bad
    W hW hs hβlo hβhi hκbeta ηl 1 row 1 (by norm_num) (ε/4) mesh bΦ hε4 (by linarith) hmeshlt hmesh0.le
    hmeshμ hmeshcap hmarkedmesh hbΦ
  have hp:=hpaid (weighted_sourceFixedIdeal S) (weighted_sourceFixedIdeal_le_modulus S)
    (weighted_source_fixed_gates S ηl).1
    (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top S) ηl)
    (weighted_source_fixed_gates S ηl).2.2.2
  have hex : excluded row.character 1 = ηl := detector_label_excluded S η label
  rw [hex] at hp
  have herror : ∀Ψ : 𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) →
      (∀x,0≤(Ψ x).re) →
      ∀T : Finset (Fin D.N),∃Se : Finset (ℕ×ℕ),∃De : ℕ,∃Ce : ℝ,0≤ Ce ∧
        ∀ᶠZ : ℝ in atTop,1< Z ∧
          MainErrorReconstruction.GeometryAffineErrorPaidSpec (plane:=plane) S.modulus ⊤ le_top S.S W hW.continuous hs Ψ ηl ηl mesh (ε/4)
            T Se De Ce Z := by
    intro Ψ _ _
    apply MainErrorReconstruction.actual_affine_error_uniform_paid_of_normalized (plane:=plane) (α:=Fin D.N) S.modulus ⊤ le_top
      0 logAnnulus_compact logAnnulus_smooth S.S S.exclusions.bad W hW.continuous hs Ψ ηl ηl (ε/4) mesh
      hε4 (by linarith) hmeshlt (internalQ (weighted_sourceFixedIdeal S) ηl) (weighted_source_fixed_gates S ηl).1
      (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top S) ηl)
      (weighted_source_fixed_gates S ηl).2.2.2
    exact MainErrorReconstruction.actual_affine_error_normalized_family (plane:=plane) (α:=Fin D.N) S.modulus ⊤ le_top
      S.S S.exclusions.bad W hW hs hβlo hκbeta Ψ ηl ηl (weighted_sourceFixedIdeal S)
      (weighted_sourceFixedIdeal_le_modulus S) (weighted_source_fixed_gates S ηl).1
      (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top S) ηl)
      (weighted_source_fixed_gates S ηl).2.2.2 (ε/4) mesh hε4 (by linarith) hmesh0.le hmeshlt hmeshμ hmeshcap
  have hbudget := literal_affine_geometry_budget_of_main_error (plane:=plane) S.modulus ⊤ le_top S.S S.exclusions.bad
    W hW.continuous hs ηl ηl (weighted_sourceFixedIdeal S) bΦ mesh (ε/4) τ hε4 hmeshlt hp herror
  obtain ⟨degree,Sd,C,hC,hev⟩ := literal_geometry_initial_affine (plane:=plane) (α:=Fin D.N) S.modulus ⊤ le_top
    W hW hs ηl ηl (weighted_sourceFixedIdeal S) bΦ mesh ε τ (geometryLossUnit 1 (ε/4)/64)
    (by linarith) hmesh0 hε hτ
    (div_pos (geometry_loss_unit_pos 1 (ε/4) (by norm_num) hε4) (by norm_num))
    (hmesh.trans hmcomp) hβlo (by linarith) (weighted_sourceFixedIdeal_le_modulus S)
    (weighted_source_fixed_gates S ηl).1 (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top S) ηl)
    (weighted_source_fixed_gates S ηl).2.2.2 logAnnulus_compact logAnnulus_smooth hbudget
  exact ⟨degree,Sd,C,hC,hev⟩

/-- The actual source is proved at a smaller capped error and then enlarged;
all masks, profiles, heights and the fixed mesh are unchanged. -/
theorem detector_label_initial_affine (plane : Sil.Uneven.MainSource.Plane)
    {D : Cycle25.Weighted.MomentData} (S : WeightedSourceData D)
    (η : Character) (label : Sum Bool (RayQuotient.Characters S.modulus ⊤))
    (hβlo : 51/100≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (hκbeta : 2*HeckeZeroSupremum.beta-1≤ plane.incumbent)
    (ε : ℝ) (hε : 0<ε) (mesh : ℝ) (hmesh0 : 0 < mesh)
    (hmesh : mesh ≤ sourceMesh ε) (bΦ : ℝ) (hbΦ : 2≤ bΦ) :
    let ηl:=sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label
    ∃degree : ℕ,∃Sd : Finset (ℕ×ℕ),∃C : ℝ,0< C ∧ ∀ᶠU : ℝ in atTop,
      MainInitial.InitialAffineAt (P:=plane) (α:=Fin D.N) S.modulus ⊤ le_top
        (fun x=> conj (S.W x)) 2 (1/4) (9/4) bΦ mesh (33/50) (33/50) 1 1 ε U
        ηl ηl (weighted_sourceFixedIdeal S) degree Sd C := by
  intro ηl
  have hs:=capped_error_bounds hε
  obtain ⟨degree,Sd,C,hC,hev⟩:=detector_label_initial_affine_capped plane S η label hβlo hβhi hκbeta
    (cappedError ε) hs.1 hs.2.2 mesh hmesh0 hmesh bΦ hbΦ
  refine ⟨degree,Sd,C,hC,?_⟩
  filter_upwards [hev,eventually_gt_atTop (1:ℝ)] with U hu hU
  exact initial_affine_error_mono (α:=Fin D.N) S.modulus ⊤ le_top plane
    (fun x=> conj (S.W x)) 2 (1/4) (9/4) bΦ mesh (33/50) (33/50) 1 1
    (cappedError ε) ε U ηl ηl (weighted_sourceFixedIdeal S) degree Sd C hC.le hU hs.2.1 hu

end
end OAI.SevenEighths.MainAssembly
end

/- Original module: Candidate.Uneven.MainActualLabelMoments. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
namespace OAI.SevenEighths.MainAssembly
noncomputable section
open HeckeFamily Cycle25ProbeFinalAssembly

/-- The four genuine source contracts, with the incumbent hypothesis explicit. -/
theorem actual_label_initial_moments (plane : Sil.Uneven.MainSource.Plane)
    {D : Cycle25.Weighted.MomentData} (S : WeightedSourceData D)
    (hβlo : 51/100 ≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta ≤ 7/8)
    (hκbeta : 2*HeckeZeroSupremum.beta-1 ≤ plane.incumbent)
    (mesh : ℝ) (hmesh0 : 0 < mesh) (hmesh : mesh ≤ sourceMesh D.t) :
    MainInitialTransport.LabelInitialMoments plane S mesh := by
  intro η bΦ hbΦ label
  exact detector_label_initial_affine plane S η label hβlo hβhi hκbeta
    D.t D.t_pos mesh hmesh0 hmesh bΦ hbΦ

end
end OAI.SevenEighths.MainAssembly
end
