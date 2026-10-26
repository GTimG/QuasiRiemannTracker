/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Uniformity interface for the literal new-face initial energy. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Source.RescaleUniform
set_option autoImplicit false
namespace QRH.Record12518109Existence
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths QRH.Record12518109Source
open HeckeFamily CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorEnergyInitialState CenteredMomentInductionEnergy
open ConcretePrimeRowBridge CenteredMomentPrimeSlot Filter
local notation "O" => HeckeFamily.O
local instance (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

/-- A single mesh precedes the ambient finite slot type, modulus, source,
inducing characters, profile support and all live row parameters. -/
def UnitFaceSource (face : SourceFace) (mesh ε : ℝ) : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α],
  ∀ (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM≤H),
  ∀ (W : ℝ→ℂ), ContDiff ℝ ∞ W → Function.support W⊆Set.Icc (1:ℝ) 2 →
  ∀ bΦ : ℝ, 2≤bΦ → ∀ (η η₀ : Character) (Q : Ideal O),
    Q≤rayM → internalQ Q η₀≠0 → internalQ Q η₀≠⊤ →
    internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃degree : ℕ, ∃controls : Finset (ℕ×ℕ), ∃C : ℝ, 0<C ∧
      ∀ᶠZ : ℝ in atTop,
        InitialAffineAt (α:=α) rayM H hH face W 2 (1/4) (9/4) bΦ mesh
          (33/50) (33/50) 1 1 ε Z η η₀ Q degree controls C

def UniformUnitFaceSource (face : SourceFace) : Prop :=
  ∀ε : ℝ,0<ε → ∃mesh : ℝ,0<mesh ∧ UnitFaceSource face mesh ε

/-- Shrinking the width bound preserves the exact source, energy and controls. -/
theorem initialAffineAt_mono_mesh {α : Type} [Fintype α] [DecidableEq α]
    (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM≤H)
    (face : SourceFace) (W : ℝ→ℂ)
    (bslot a b bΦ mesh mesh' σlo σhi Mmin Mmax ε Z : ℝ)
    (η η₀ : Character) (Q : Ideal O) (degree : ℕ) (controls : Finset (ℕ×ℕ)) (C : ℝ)
    (hle : mesh'≤mesh)
    (hsource : InitialAffineAt (α:=α) rayM H hH face W bslot a b bΦ mesh
      σlo σhi Mmin Mmax ε Z η η₀ Q degree controls C) :
    InitialAffineAt (α:=α) rayM H hH face W bslot a b bΦ mesh'
      σlo σhi Mmin Mmax ε Z η η₀ Q degree controls C := by
  intro T θ w σ v t height hw hwm
  exact hsource T θ w σ v t height hw (fun i=>(hwm i).trans hle)

theorem UnitFaceSource.mono_mesh {face : SourceFace} {mesh mesh' ε : ℝ}
    (hsource : UnitFaceSource face mesh ε) (hle : mesh'≤mesh) : UnitFaceSource face mesh' ε := by
  intro α _ _ rayM _ H hH W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  obtain ⟨degree,controls,C,hC,hsource⟩ := hsource α rayM H hH W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  exact ⟨degree,controls,C,hC,hsource.mono (fun Z hZ=>initialAffineAt_mono_mesh rayM H hH face W
    2 (1/4) (9/4) bΦ mesh mesh' (33/50) (33/50) 1 1 ε Z η η₀ Q degree controls C hle hZ)⟩
end
end QRH.Record12518109Existence
#print axioms QRH.Record12518109Existence.initialAffineAt_mono_mesh
#print axioms QRH.Record12518109Existence.UnitFaceSource.mono_mesh
