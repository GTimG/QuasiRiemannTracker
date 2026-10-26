/- Copyright (c) 2026 Sil. Apache-2.0.
Constructs the restricted unit source in the contrary branch theta < beta
and restores the exact full source. The source mesh is fixed before the
ambient finite type, and the structural root inputs and analytic estimates
are supplied by the preceding source constructions.
-/
import Candidate.FourthPower.RepairedSourceSetupBound
import Candidate.FourthPower.RepairedActualSideProvider
import Candidate.FourthPower.SourceContract

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.RepairedRestrictedSource
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily
open QRH.Record1252270103KernelMass QRH.Record1252270103Source
open CenteredMomentNaturalFixedRaySource CenteredMomentFiniteProfileExceptional
open CenteredMomentSourceMass CenteredMomentSourceProfileMass
open RestoredRootEnergy RestoredInitialSource
open RepairedRootParameters RepairedSourceSideSupply RepairedSourceRootGeometry RepairedSourceSetupBound
open QRH.Record12518109Source
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
local instance (M : Id) [NeZero M] : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

abbrev targetFace : SourceFace := globalFace (99999/100000) (93/25) (3/50)

set_option maxHeartbeats 1500000 in
/-- Derives the restricted source on the target face from the explicit
retained raw-side estimate in the contrary branch. -/
theorem restricted_unit_source_of_raw_sides
    (hsupply : ContraryRawSideProvider) (hcontra : theta < HeckeZeroSupremum.beta)
    (ε : ℝ) (hε : 0 < ε) : RestrictedUnitSource targetFace (mesh ε) ε := by
  intro α instα instDec M instM H hH W hW hWs bΦ hbΦ η η₀ Q hQM hQ0 hQt hQ72
  letI : NeZero (internalQ Q η₀) := ⟨hQ0⟩
  have hQray : internalQ Q η₀ ≤ M := inf_le_left.trans hQM
  have hQη : internalQ Q η₀ ≤ η₀.modulus := inf_le_right
  obtain ⟨J,control,C,hC,hbound⟩ := uniform_setup_of_side_provider hsupply hcontra ε hε α M H hH
    W hW hWs bΦ hbΦ η η₀ (internalQ Q η₀) hQt hQ72 hQray hQη
  refine ⟨J,control,C,hC,?_⟩
  filter_upwards [hbound] with Z hz
  intro T0 chars w sigma freq t V hw hwm hsigmaLo hsigmaHi hV hfreq
    Φ hΦs hΦ p X₁ X₂ hX₁ hX₂ hface rows r tc A ti hti Y₁ Y₂ hY₁ hy₁ hY₂ hy₂
  let s : Setup M H T0 :=
    { Z := Z
      hZ := by linarith [hz.1]
      Lcap := windowCap (Fintype.card α) ε
      hLcap := windowCap_ge_eight _ ε hε
      W := W
      hW := hW.continuous
      hWs := hWs
      η₀ := η₀
      θ := chars
      w := w
      σ := sigma
      v := freq
      hw := hw
      hσlo := hsigmaLo
      hσhi := hsigmaHi
      t := t
      p := p
      X₁ := X₁
      X₂ := X₂
      Y₁ := Y₁
      Y₂ := Y₂
      hY₁ := hY₁
      hY₂ := hY₂
      hy₁ := hy₁
      hy₂ := hy₂
      hface := hface
      r := r
      tc := tc
      A := A
      ti := ti }
  exact hz.2 T0 s rfl rfl rfl rfl V hV hfreq hwm Q Φ hΦs hΦ rows

/-- Mesh-before-N quantifier order is literal. The ambient contrary
branch is retained; the final candidate will use beta<=theta by cases. -/
theorem uniform_restricted_unit_source_of_raw_sides
    (hsupply : ContraryRawSideProvider) (hcontra : theta < HeckeZeroSupremum.beta) :
    UniformRestrictedUnitSource targetFace := by
  intro ε hε
  exact ⟨mesh ε,(mesh_spec ε hε).1,restricted_unit_source_of_raw_sides hsupply hcontra ε hε⟩

/-- Concrete E endpoint. The actual checked Large/Small side provider is
supplied here; only the normal contrary branch remains as a hypothesis. -/
theorem actual_uniform_restricted_unit_source
    (hcontra : theta < HeckeZeroSupremum.beta) : UniformRestrictedUnitSource targetFace :=
  uniform_restricted_unit_source_of_raw_sides
    RepairedActualSideProvider.actual_contrary_raw_side_provider hcontra

/-- Restores the exact full source face from the proved restricted source,
without a separate moment or source hypothesis. -/
theorem actual_global_source (hcontra : theta < HeckeZeroSupremum.beta) :
    QRH.Record1252270103Source.GlobalSource (99999/100000) (93/25) (3/50) :=
  RestoredInitialSource.global_source_of_restricted
    (actual_uniform_restricted_unit_source hcontra)

/-- Exact face dictionary, supplied by the already checked literal contract. -/
theorem target_face_eq_source_contract : targetFace=SourceContract.face :=
  SourceContract.face_exact.symm

/-- Literal source interface consumed by the return. This is still confined
only to the contrary branch and does not itself assert beta<=theta. -/
theorem actual_required_source (hcontra : theta < HeckeZeroSupremum.beta) :
    SourceContract.RequiredSource := by
  change QRH.Record12518109Existence.UniformUnitFaceSource SourceContract.face
  rw [←target_face_eq_source_contract]
  exact actual_global_source hcontra

end
end Candidate.FourthPower.RepairedRestrictedSource

