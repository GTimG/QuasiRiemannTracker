import Candidate.Cycle63.Physical.InitialMass.GeometryAffineMainUniform
import Candidate.Cycle63.Physical.InitialMass.GeometrySourceNaturalRow
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineAssembly
import Candidate.Cycle63.Physical.InitialMass.GeometryAffinePaidComponents
import Candidate.Cycle63.Physical.InitialMass.GeometrySourceErrorPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryChosenSetup
import Candidate.Affine.Supply
import Candidate.Cycle25.Energy.Endpoint

/- Original module: Candidate.Cycle63.Physical.InitialMass.GeometrySourceMainPayment. -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 80000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open Cycle63MarkedPlain
open scoped Classical ContDiff ComplexConjugate
open Filter HeckeFamily Cycle25ProbeFinalAssembly Cycle25WeightedNumeratorPhysical
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentDetectorDictionary ProbePhysical
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentLogDyadic

/-- The exact reflected weighted source has a paid retained main estimate
with every low/high analytic premise discharged. The error family remains
a separate obligation for the full geometry budget. -/
theorem actual_weighted_source_main_paid {D : Cycle25.Weighted.MomentData}
    (F : WeightedSourceData D)(εaffine mesh bΦ : ℝ)(hε : 0<εaffine)
    (hmesh : mesh<(902420521/120632400000:ℝ)/2)(hmesh0 : 0≤ mesh)
    (hmeshμ : mesh≤geometryLossUnit 1 εaffine/8)
    (hmeshcap : mesh≤Cycle25.Energy.commonMesh 2 28 1 (geometryLossUnit 1 εaffine/8))
    (hmarkedmesh : mesh≤ markedRawMesh*markedCoreMin)
    (hbΦ : 2≤bΦ)(hβlo : 51/100≤HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta≤7/8) :
    let W:=fun x=>conj (F.W x)
    let hW : Continuous W:=(Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)).continuous
    let hs : Function.support W⊆Set.Icc (1:ℝ) 2:=by
      intro x hx
      exact F.complex_support (by intro hz;exact hx (by change conj (F.W x)=0;rw [hz];simp))
    let η:=fixedSourcePrincipal F.S F.exclusions.prime
    ∃τ : ℝ,0<τ ∧ τ≤geometryLossUnit 1 εaffine/16 ∧
      ∀T : Finset (Fin D.N),∃S : Finset (ℕ×ℕ),∃degree : ℕ,∃C : ℝ,0≤C ∧
        ∀ᶠZ : ℝ in atTop,1<Z ∧
          GeometryAffineMainPaidSpec F.modulus ⊤ le_top F.S W hW hs η η mesh
            (geometryLossUnit 1 εaffine) T S degree C Z := by
  intro W hW hs η
  have hSmooth : ContDiff ℝ ∞ W:=Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)
  obtain ⟨τ,hτ,hτcap,hpaid⟩:=actual_affine_main_uniform_paid (α:=Fin D.N)
    F.modulus ⊤ le_top 0 logAnnulus_compact logAnnulus_smooth F.S F.exclusions.bad
    W hSmooth hs hβlo hβhi η 1 (fixedSourceNaturalRow F.S F.exclusions.prime F.exclusions.bad)
    1 (by norm_num) εaffine mesh bΦ hε hmesh hmesh0 hmeshμ hmeshcap hmarkedmesh hbΦ
  refine ⟨τ,hτ,hτcap,?_⟩
  have hp:=hpaid (weighted_sourceFixedIdeal F) (weighted_sourceFixedIdeal_le_modulus F)
    (weighted_source_fixed_gates F η).1
    (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top F) η)
    (weighted_source_fixed_gates F η).2.2.2
  rw [←actual_weighted_source_natural_excluded F] at hp
  exact hp

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_weighted_source_main_paid
end

/- Original module: Candidate.Cycle63.Physical.InitialMass.GeometrySourceBudget. -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 80000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open Cycle63MarkedPlain
open scoped Classical ContDiff ComplexConjugate SchwartzMap
open Filter HeckeFamily Cycle25ProbeFinalAssembly Cycle25WeightedNumeratorPhysical
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentDetectorDictionary ProbePhysical
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput

/-- The fixed weighted-source geometry budget has only its exact paid error
family left to supply. All retained main and source identities are internal. -/
theorem actual_weighted_source_geometry_budget_of_error {D : Cycle25.Weighted.MomentData}
    (F : WeightedSourceData D)(εaffine mesh bΦ : ℝ)(hε : 0<εaffine)
    (hmesh : mesh<(902420521/120632400000:ℝ)/2)(hmesh0 : 0≤ mesh)
    (hmeshμ : mesh≤geometryLossUnit 1 εaffine/8)
    (hmeshcap : mesh≤Cycle25.Energy.commonMesh 2 28 1 (geometryLossUnit 1 εaffine/8))
    (hmarkedmesh : mesh≤ markedRawMesh*markedCoreMin)
    (hbΦ : 2≤bΦ)(hβlo : 51/100≤HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta≤7/8) :
    let W:=fun x=>conj (F.W x)
    let hW : Continuous W:=(Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)).continuous
    let hs : Function.support W⊆Set.Icc (1:ℝ) 2:=by
      intro x hx
      exact F.complex_support (by intro hz;exact hx (by change conj (F.W x)=0;rw [hz];simp))
    let η:=fixedSourcePrincipal F.S F.exclusions.prime
    (∀Ψ : 𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) →
      (∀x,0≤(Ψ x).re) →
      ∀T : Finset (Fin D.N),∃S : Finset (ℕ×ℕ),∃degree : ℕ,∃C : ℝ,0≤C ∧
        ∀ᶠZ : ℝ in atTop,1<Z ∧
          GeometryAffineErrorPaidSpec F.modulus ⊤ le_top F.S W hW hs Ψ η η mesh εaffine T S degree C Z) →
    ∃τ : ℝ,0<τ ∧ τ≤geometryLossUnit 1 εaffine/16 ∧
      SourceLiteralAffineGeometryBudget F bΦ mesh εaffine τ (geometryLossUnit 1 εaffine/64) := by
  intro W hW hs η herror
  obtain ⟨τ,hτ,hτcap,hmain⟩:=actual_weighted_source_main_paid F εaffine mesh bΦ hε
    hmesh hmesh0 hmeshμ hmeshcap hmarkedmesh hbΦ hβlo hβhi
  refine ⟨τ,hτ,hτcap,?_⟩
  exact literal_affine_geometry_budget_of_main_error F.modulus ⊤ le_top F.S F.exclusions.bad
    W hW hs η η (weighted_sourceFixedIdeal F) bΦ mesh εaffine τ hε hmesh hmain herror

/-- The exact weighted source satisfies the geometry budget from the original
main and error estimates, without an additional analytic hypothesis. -/
theorem actual_weighted_source_geometry_budget {D : Cycle25.Weighted.MomentData}
    (F : WeightedSourceData D)(εaffine mesh bΦ : ℝ)(hε : 0<εaffine)
    (hmesh : mesh<(902420521/120632400000:ℝ)/2)(hmesh0 : 0≤ mesh)
    (hmeshμ : mesh≤geometryLossUnit 1 εaffine/8)
    (hmeshcap : mesh≤Cycle25.Energy.commonMesh 2 28 1 (geometryLossUnit 1 εaffine/8))
    (hmarkedmesh : mesh≤ markedRawMesh*markedCoreMin)
    (hbΦ : 2≤bΦ)(hβlo : 51/100≤HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta≤7/8) :
    ∃τ : ℝ,0<τ ∧ τ≤geometryLossUnit 1 εaffine/16 ∧
      SourceLiteralAffineGeometryBudget F bΦ mesh εaffine τ (geometryLossUnit 1 εaffine/64) := by
  apply actual_weighted_source_geometry_budget_of_error F εaffine mesh bΦ hε
    hmesh hmesh0 hmeshμ hmeshcap hmarkedmesh hbΦ hβlo hβhi
  intro Ψ _hsΨ _hΨ
  exact actual_weighted_source_error_paid F εaffine mesh hε hmesh hmesh0 hmeshμ hmeshcap hβlo Ψ

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_weighted_source_geometry_budget_of_error
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_weighted_source_geometry_budget
end

/- Original module: Candidate.Cycle63.Assembly.Unconditional. -/
section
/- Source integration: PR50 8cb265dc base; PR56 67edfb7a detector affine interfaces.
   Original Hailey Collet, OpenAI and predecessor notices are retained.
   Detector affine contribution: DaysSky, with Claude assistance; Apache-2.0. -/

/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                       
                                                        

set_option autoImplicit false
namespace Cycle63.FinalAssembly
noncomputable section
open OAI.SevenEighths Cycle63InitialMass

/-- The actual chosen affine input follows from the original main and error
families and the fixed source geometry. -/
theorem chosen_affine_input : ChosenAffineInput :=
  chosen_affine_of_source_geometry actual_weighted_source_geometry_budget

/-- Cycle63's exact advertised supremum bound. -/
theorem beta_le_rational : HeckeZeroSupremum.beta≤(Cycle63.Arithmetic.theta:ℝ) :=
  beta_le_rational_of_chosen_affine
    Cycle25ProbeFinalAssemblyCertifiedBands.actual_detector_affine_input chosen_affine_input

end
end Cycle63.FinalAssembly
#print axioms Cycle63.FinalAssembly.chosen_affine_input
#print axioms Cycle63.FinalAssembly.beta_le_rational
end

/- Original module: Candidate.Cycle63.Verification. -/
section
/- Source integration: PR50 8cb265dc base; PR56 67edfb7a detector affine interfaces.
   Original Hailey Collet, OpenAI and predecessor notices are retained.
   Detector affine contribution: DaysSky, with Claude assistance; Apache-2.0. -/

/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                     

set_option autoImplicit false
namespace Cycle63Verification
open scoped _root_.DirichletCharacter
open Cycle63.FinalAssembly

theorem allDirichlet {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (Cycle63.Arithmetic.theta : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  exact dirichlet_nonzero_of_chosen_affine
    OAI.SevenEighths.Cycle25ProbeFinalAssemblyCertifiedBands.actual_detector_affine_input
    chosen_affine_input χ s hs hpole

theorem zeta {s : ℂ}
    (hs : (Cycle63.Arithmetic.theta : ℝ) < s.re) (hpole : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  exact zeta_nonzero_off_pole_of_chosen_affine
    OAI.SevenEighths.Cycle25ProbeFinalAssemblyCertifiedBands.actual_detector_affine_input
    chosen_affine_input s hs hpole

theorem allHecke (χ : OAI.SevenEighths.HeckeFamily.Character) {s : ℂ}
    (hs : (Cycle63.Arithmetic.theta : ℝ) < s.re)
    (hpole : ¬ (χ.residue = 1 ∧ s = 1)) :
    OAI.SevenEighths.HeckeFamily.LFunction χ s ≠ 0 := by
  exact hecke_nonzero_of_chosen_affine
    OAI.SevenEighths.Cycle25ProbeFinalAssemblyCertifiedBands.actual_detector_affine_input
    chosen_affine_input χ s hs (by tauto)

/-- Mathlib's total zeta function also has a nonzero value at its pole. -/
theorem zetaTotal {s : ℂ} (hs : (Cycle63.Arithmetic.theta : ℝ) < s.re) :
    riemannZeta s ≠ 0 := by
  exact riemannZeta_nonzero_of_chosen_affine
    OAI.SevenEighths.Cycle25ProbeFinalAssemblyCertifiedBands.actual_detector_affine_input
    chosen_affine_input s hs

end Cycle63Verification
#print axioms Cycle63Verification.allDirichlet
#print axioms Cycle63Verification.zeta
#print axioms Cycle63Verification.allHecke
#print axioms Cycle63Verification.zetaTotal
end

/- Original module: Candidate.Target836.SourceProvider.AcceptedIncumbent. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Target874836.SourceProvider
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths
open Filter HeckeFamily CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthSchedule
open CenteredMomentEnergyWidthRanges
local notation "O" => HeckeFamily.O

def incumbentKappa : ℝ := 9371/12500

/-- This is the frozen accepted theorem, not the target currently being proved. -/
theorem accepted_beta : HeckeZeroSupremum.beta ≤ (21871/25000 : ℝ) := by
  simpa only [Cycle63.Arithmetic.theta] using Cycle63.FinalAssembly.beta_le_rational

theorem incumbent_kappa_bound : 2*HeckeZeroSupremum.beta-1 ≤ incumbentKappa := by
  have h := accepted_beta
  norm_num [incumbentKappa]
  linarith

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Complete positive/zero incumbent pair at accepted kappa, with degree and
profile control fixed before the base character and the moving row data.
The common mesh is the existing compact mesh used by accepted callers. -/
theorem accepted_incumbent
    (W : ℝ → ℂ) (aslot bslot a b radial Bmask L lo hi Mcap ε : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0 ≤ bslot)
    (ha : 0 < a) (haUpper : a ≤ 1/4) (hb : 1 ≤ b) (hrad : 0 < radial)
    (hmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hε : 0 < ε)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) :
    ∃ degree : ℕ, ∃ S : Finset (ℕ × ℕ), ∀ η0 : Character, ∀ Q : Ideal O, Q ≤ M →
      internalQ Q η0 ≠ 0 → internalQ Q η0 ≠ ⊤ →
      internalQ Q η0 ≤ Ideal.span {(72 : O)} →
      ∃ C0 C1 : ℝ, 0 < C0 ∧ 0 < C1 ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
        ZeroAt (internalQ Q η0) a b radial Bmask L Mcap ε Z degree S C0 ∧
        PositiveAt (α := α) M H hH W bslot a b radial Bmask L
          (Cycle25.Energy.commonMesh Mcap Bmask L ε) lo hi Mcap ε incumbentKappa
          Z η0 Q degree S C1 := by
  have hcert := Cycle25CenteredMomentEnergyCertifiedExistence.terminal_certificate
    (α := α) M H hH W aslot bslot a b radial Bmask L lo hi Mcap incumbentKappa ε
    haslot hWs hW hbslot ha haUpper hb hrad hmask hMcap
    (by norm_num [incumbentKappa]) hε hbeta incumbent_kappa_bound
  obtain ⟨degree, S, hbound⟩ := certified_terminal (α := α) M H hH W bslot a b radial
    Bmask L lo hi Mcap incumbentKappa ε hmask hMcap.le
    (by norm_num [incumbentKappa]) hε hcert
  have hmesh := Cycle25.Energy.compact_mesh_le Mcap Bmask L incumbentKappa ε hMcap.le hmask hε
    (by norm_num [incumbentKappa]) (by norm_num [incumbentKappa])
  refine ⟨degree, S, ?_⟩
  intro η0 Q hQM hQ0 hQt hQ72
  obtain ⟨C0, C1, hC0, hC1, hev⟩ := hbound η0 Q hQM hQ0 hQt hQ72
  refine ⟨C0, C1, hC0, hC1, ?_⟩
  filter_upwards [hev] with Z hZ
  refine ⟨hZ.1, hZ.2.1, ?_⟩
  intro T theta w sigma v t height hw hwL hsiglo hsighi hheight hv s hQ hs p
    X1 X2 hX1 hX2 hLX1 hLX2 hcapacity
  exact hZ.2.2 T theta w sigma v t height hw (fun i => (hwL i).trans hmesh)
    hsiglo hsighi hheight hv s hQ hs p X1 X2 hX1 hX2 hLX1 hLX2 hcapacity

end
end Target874836.SourceProvider

#print axioms Target874836.SourceProvider.accepted_beta
#print axioms Target874836.SourceProvider.incumbent_kappa_bound
#print axioms Target874836.SourceProvider.accepted_incumbent
end
