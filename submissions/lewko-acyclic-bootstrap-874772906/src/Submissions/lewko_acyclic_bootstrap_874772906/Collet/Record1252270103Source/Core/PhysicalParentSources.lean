/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Finite fixed-anchor source uniformization. Control monotonicity follows the
earlier Record12518109Induction.FiniteSources argument, isolated here from its
obsolete finite face chain. The uniform radial transport is the same checked
InitialAffineAt rescaling primitive; no anchor-uniform source is postulated. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.Contract
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.BandMonotonicity
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Moment.ActualRowDensity
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
local instance parentSourcesQuotientFinite (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

theorem initial_controls_mono {α : Type} [Fintype α] [DecidableEq α]
    (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM≤H)
    (face : SourceFace) (W : ℝ→ℂ)
    (bslot a b bΦ mesh σlo σhi Mmin Mmax ε Z : ℝ)
    (η η₀ : Character) (Q : Ideal O) (degree degree' : ℕ)
    (controls controls' : Finset (ℕ×ℕ)) (C C' : ℝ) (hZ : 0≤Z)
    (hdegree : degree≤degree') (hcontrols : controls⊆controls') (hC : 0≤C) (hCC : C≤C')
    (hsource : InitialAffineAt (α:=α) rayM H hH face W bslot a b bΦ mesh
      σlo σhi Mmin Mmax ε Z η η₀ Q degree controls C) :
    InitialAffineAt (α:=α) rayM H hH face W bslot a b bΦ mesh
      σlo σhi Mmin Mmax ε Z η η₀ Q degree' controls' C' := by
  intro T θ w σ v t height hw hwm hσlo hσhi hh hv M hMlo hMhi Φ hΦ hpΦ p X₁ X₂ hX₁ hX₂ hadm
  apply (hsource T θ w σ v t height hw hwm hσlo hσhi hh hv M hMlo hMhi Φ hΦ hpΦ p X₁ X₂ hX₁ hX₂ hadm).trans
  have hdiag := QuadraticInitialBound.diagonalControl_nonneg Φ
  have hp := CenteredMomentEnergyBandMonotonicity.profile_control_mono p hcontrols
  have hpn := p.control_nonneg controls
  have hbase : 1≤1+|t|+height := by linarith [abs_nonneg t]
  have hpow := pow_le_pow_right₀ hbase hdegree
  have hCp : 0≤C' := hC.trans hCC
  gcongr <;> first | assumption | positivity

/-- The whole finite family is fixed before degree, profile controls, C and Z.
The same controls cover the complete radial interval and every moving height. -/
theorem unit_source_finite_anchors {face : SourceFace} {unitMesh unitε : ℝ}
    (hsource : UnitFaceSource face unitMesh unitε)
    {α : Type} [Fintype α] [DecidableEq α] {κ : Type} [Fintype κ]
    (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM≤H)
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (bΦ mesh Mmin Mmax ε : ℝ) (hbΦ : 2≤bΦ)
    (hMmin : 0<Mmin) (hunitMesh : 0≤unitMesh) (hmesh : mesh≤unitMesh*Mmin)
    (hunitε : 0≤unitε) (hε : Mmax*unitε≤ε)
    (anchors : κ→Character) (η₀ : Character) (Q : Ideal O)
    (hQray : Q≤rayM) (hQ0 : internalQ Q η₀≠0) (hQt : internalQ Q η₀≠⊤)
    (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)}) :
    ∃degree : ℕ, ∃S : Finset (ℕ×ℕ), ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
      ∀i : κ,InitialAffineAt (α:=α) rayM H hH face W 2 (1/4) (9/4) bΦ mesh
        (33/50) (33/50) Mmin Mmax ε Z (anchors i) η₀ Q degree S C := by
  classical
  choose degree controls C hC hs using fun i =>
    hsource α rayM H hH W hW hWs bΦ hbΦ (anchors i) η₀ Q hQray hQ0 hQt hQ72
  have hscaled (i : κ) := initialAffineAt_uniform_rescale rayM H hH face W
    2 (1/4) (9/4) bΦ mesh unitMesh (33/50) (33/50) Mmin Mmax ε unitε (anchors i) η₀ Q
    (degree i) (controls i) (C i) hMmin (hC i).le hunitMesh hmesh hunitε hε (hs i)
  let degree' := ∑i,degree i
  let controls' := Finset.univ.biUnion controls
  let C' := 1+∑i,C i
  have hsum : 0≤∑i,C i := Finset.sum_nonneg (fun i _ => (hC i).le)
  have hC' : 0<C' := by dsimp only [C'];linarith
  refine ⟨degree',controls',C',hC',?_⟩
  filter_upwards [Filter.eventually_all.mpr hscaled,eventually_ge_atTop (0:ℝ)] with Z hsource hZ
  intro i
  have hdi : degree i≤degree' := Finset.single_le_sum (fun j _=>Nat.zero_le _) (Finset.mem_univ i)
  have hsi : controls i⊆controls' := Finset.subset_biUnion_of_mem controls (Finset.mem_univ i)
  have hci : C i≤C' := by
    have hh : C i≤∑j,C j := Finset.single_le_sum (fun j _=>(hC j).le) (Finset.mem_univ i)
    dsimp only [C']
    linarith
  exact initial_controls_mono rayM H hH face W 2 (1/4) (9/4) bΦ mesh (33/50) (33/50)
    Mmin Mmax ε Z (anchors i) η₀ Q (degree i) degree' (controls i) controls' (C i) C'
    hZ hdi hsi (hC i).le hci (hsource i)

/-- This is the literal ray-pair family used by the collected retained LOW
source. Both original arithmetic anchors precede the common controls. -/
theorem unit_source_second_dictionary {face : SourceFace} {unitMesh unitε : ℝ}
    (hsource : UnitFaceSource face unitMesh unitε)
    {α : Type} [Fintype α] [DecidableEq α]
    (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM≤H)
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (bΦ mesh Mmin Mmax ε : ℝ) (hbΦ : 2≤bΦ)
    (hMmin : 0<Mmin) (hunitMesh : 0≤unitMesh) (hmesh : mesh≤unitMesh*Mmin)
    (hunitε : 0≤unitε) (hε : Mmax*unitε≤ε)
    (ηanchor η₀ : Character) (Q : Ideal O)
    (hQray : Q≤rayM) (hQ0 : internalQ Q η₀≠0) (hQt : internalQ Q η₀≠⊤)
    (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)}) :
    ∃degree : ℕ, ∃S : Finset (ℕ×ℕ), ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
      ∀ray ψ : RayCharacter,InitialAffineAt (α:=α) rayM H hH face W 2 (1/4) (9/4) bΦ mesh
        (33/50) (33/50) Mmin Mmax ε Z (secondFixedDictionary ηanchor (ray,ψ)) η₀ Q degree S C := by
  obtain ⟨degree,S,C,hC,hs⟩ := unit_source_finite_anchors (α:=α) hsource rayM H hH W hW hWs
    bΦ mesh Mmin Mmax ε hbΦ hMmin hunitMesh hmesh hunitε hε
    (secondFixedDictionary ηanchor) η₀ Q hQray hQ0 hQt hQ72
  exact ⟨degree,S,C,hC,hs.mono (fun _ h ray ψ => h (ray,ψ))⟩

end
end QRH.Record1252270103Source.PhysicalParentSources
#print axioms QRH.Record1252270103Source.PhysicalParentSources.initial_controls_mono
#print axioms QRH.Record1252270103Source.PhysicalParentSources.unit_source_finite_anchors
#print axioms QRH.Record1252270103Source.PhysicalParentSources.unit_source_second_dictionary
