/- Cycle61 successor parameter adaptation by Zhongpai Gao, with AI assistance. Nominal θ=4374299/5000000, q=67/100; exact reserves and actual source consumers are changed by scoped ownership maps. Original notices/provenance remain intact. Full source replay and independent verification are pending. -/
/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B138
import Candidate.Bundles.B139
import Candidate.Bundles.B189
import Candidate.Bundles.B191

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometrySourceMainPayment; sha256 30162a835443cf5fb97edeb9db3cdc7293ad6aba4a35484d5fd682c924cf18fd -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                             
                                                            
                                                          

set_option autoImplicit false
set_option maxHeartbeats 80000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
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
    (hmesh : mesh<(62485051/9854400000:ℝ)/2)(hmesh0 : 0≤ mesh)
    (hmeshμ : mesh≤ geometryLossUnit 1 εaffine/8)
    (hmeshcap : mesh≤ Cycle25.Energy.commonMesh 2 28 1 (geometryLossUnit 1 εaffine/8))
    (hbΦ : 2≤ bΦ)(hβlo : 51/100≤ HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta≤7/8) :
    let W:=fun x=>conj (F.W x)
    let hW : Continuous W:=(Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)).continuous
    let hs : Function.support W⊆Set.Icc (1:ℝ) 2:=by
      intro x hx
      exact F.complex_support (by intro hz;exact hx (by change conj (F.W x)=0;rw [hz];simp))
    let η:=fixedSourcePrincipal F.S F.exclusions.prime
    ∃τ : ℝ,0<τ ∧ τ≤ geometryLossUnit 1 εaffine/16 ∧
      ∀T : Finset (Fin D.N),∃S : Finset (ℕ×ℕ),∃degree : ℕ,∃C : ℝ,0≤ C ∧
        ∀ᶠZ : ℝ in atTop,1< Z ∧
          GeometryAffineMainPaidSpec F.modulus ⊤ le_top F.S W hW hs η η mesh
            (geometryLossUnit 1 εaffine) T S degree C Z := by
  intro W hW hs η
  have hSmooth : ContDiff ℝ ∞ W:=Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)
  obtain ⟨τ,hτ,hτcap,hpaid⟩:=actual_affine_main_uniform_paid (α:=Fin D.N)
    F.modulus ⊤ le_top 0 logAnnulus_compact logAnnulus_smooth F.S F.exclusions.bad
    W hSmooth hs hβlo hβhi η 1 (fixedSourceNaturalRow F.S F.exclusions.prime F.exclusions.bad)
    1 (by norm_num) εaffine mesh bΦ hε hmesh hmesh0 hmeshμ hmeshcap hbΦ
  refine ⟨τ,hτ,hτcap,?_⟩
  have hp:=hpaid (weighted_sourceFixedIdeal F) (weighted_sourceFixedIdeal_le_modulus F)
    (weighted_source_fixed_gates F η).1
    (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top F) η)
    (weighted_source_fixed_gates F η).2.2.2
  rw [←actual_weighted_source_natural_excluded F] at hp
  exact hp

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_weighted_source_main_paid

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometrySourceMainPayment -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometrySourceBudget; sha256 b1b20a99bdf8d44558929d16cc0f5aae730f1427c687f59050dc897290af137f -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                             
                                                                
                                                              

set_option autoImplicit false
set_option maxHeartbeats 80000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical ContDiff ComplexConjugate SchwartzMap
open Filter HeckeFamily Cycle25ProbeFinalAssembly Cycle25WeightedNumeratorPhysical
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentDetectorDictionary ProbePhysical
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput

/-- The fixed weighted-source geometry budget has only its exact paid error
family left to supply. All retained main and source identities are internal. -/
theorem actual_weighted_source_geometry_budget_of_error {D : Cycle25.Weighted.MomentData}
    (F : WeightedSourceData D)(εaffine mesh bΦ : ℝ)(hε : 0<εaffine)
    (hmesh : mesh<(62485051/9854400000:ℝ)/2)(hmesh0 : 0≤ mesh)
    (hmeshμ : mesh≤ geometryLossUnit 1 εaffine/8)
    (hmeshcap : mesh≤ Cycle25.Energy.commonMesh 2 28 1 (geometryLossUnit 1 εaffine/8))
    (hbΦ : 2≤ bΦ)(hβlo : 51/100≤ HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta≤7/8) :
    let W:=fun x=>conj (F.W x)
    let hW : Continuous W:=(Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)).continuous
    let hs : Function.support W⊆Set.Icc (1:ℝ) 2:=by
      intro x hx
      exact F.complex_support (by intro hz;exact hx (by change conj (F.W x)=0;rw [hz];simp))
    let η:=fixedSourcePrincipal F.S F.exclusions.prime
    (∀Ψ : 𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) →
      (∀x,0≤(Ψ x).re) →
      ∀T : Finset (Fin D.N),∃S : Finset (ℕ×ℕ),∃degree : ℕ,∃C : ℝ,0≤ C ∧
        ∀ᶠZ : ℝ in atTop,1< Z ∧
          GeometryAffineErrorPaidSpec F.modulus ⊤ le_top F.S W hW hs Ψ η η mesh εaffine T S degree C Z) →
    ∃τ : ℝ,0<τ ∧ τ≤ geometryLossUnit 1 εaffine/16 ∧
      SourceLiteralAffineGeometryBudget F bΦ mesh εaffine τ (geometryLossUnit 1 εaffine/64) := by
  intro W hW hs η herror
  obtain ⟨τ,hτ,hτcap,hmain⟩:=actual_weighted_source_main_paid F εaffine mesh bΦ hε
    hmesh hmesh0 hmeshμ hmeshcap hbΦ hβlo hβhi
  refine ⟨τ,hτ,hτcap,?_⟩
  exact literal_affine_geometry_budget_of_main_error F.modulus ⊤ le_top F.S F.exclusions.bad
    W hW hs η η (weighted_sourceFixedIdeal F) bΦ mesh εaffine τ hε hmesh hmain herror

/-- The exact weighted source satisfies the geometry budget from the original
main and error estimates, without an additional analytic hypothesis. -/
theorem actual_weighted_source_geometry_budget {D : Cycle25.Weighted.MomentData}
    (F : WeightedSourceData D)(εaffine mesh bΦ : ℝ)(hε : 0<εaffine)
    (hmesh : mesh<(62485051/9854400000:ℝ)/2)(hmesh0 : 0≤ mesh)
    (hmeshμ : mesh≤ geometryLossUnit 1 εaffine/8)
    (hmeshcap : mesh≤ Cycle25.Energy.commonMesh 2 28 1 (geometryLossUnit 1 εaffine/8))
    (hbΦ : 2≤ bΦ)(hβlo : 51/100≤ HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta≤7/8) :
    ∃τ : ℝ,0<τ ∧ τ≤ geometryLossUnit 1 εaffine/16 ∧
      SourceLiteralAffineGeometryBudget F bΦ mesh εaffine τ (geometryLossUnit 1 εaffine/64) := by
  apply actual_weighted_source_geometry_budget_of_error F εaffine mesh bΦ hε
    hmesh hmesh0 hmeshμ hmeshcap hbΦ hβlo hβhi
  intro Ψ _hsΨ _hΨ
  exact actual_weighted_source_error_paid F εaffine mesh hε hmesh hmesh0 hmeshμ hmeshcap hβlo Ψ

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_weighted_source_geometry_budget_of_error
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_weighted_source_geometry_budget

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometrySourceBudget -/

/- BEGIN ORIGINAL Cycle61.Assembly.Unconditional; sha256 96fc445a406dc2ef3726ec666b743f2bc71ecdb8b45a195d12d48af0479c3825 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                       
                                                        

set_option autoImplicit false
namespace Cycle61.FinalAssembly
noncomputable section
open OAI.SevenEighths Cycle61InitialMass

/-- The actual chosen affine input follows from the original main and error
families and the fixed source geometry. -/
theorem chosen_affine_input : ChosenAffineInput :=
  chosen_affine_of_source_geometry actual_weighted_source_geometry_budget

/-- Cycle61's exact advertised supremum bound. -/
theorem beta_le_rational : HeckeZeroSupremum.beta≤(4374299 / 5000000:ℝ) :=
  beta_le_rational_of_chosen_affine chosen_affine_input

end
end Cycle61.FinalAssembly
#print axioms Cycle61.FinalAssembly.chosen_affine_input
#print axioms Cycle61.FinalAssembly.beta_le_rational

end
/- END ORIGINAL Cycle61.Assembly.Unconditional -/

/- BEGIN ORIGINAL Cycle61.Verification; sha256 b966ba23494d14cdbc0cfb220e8e07864646ef9d3a66539b8933d1f3e2c48ae1 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                     

set_option autoImplicit false
namespace Cycle61Verification
open scoped _root_.DirichletCharacter
open Cycle61.FinalAssembly

theorem allDirichlet {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (4374299 / 5000000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  exact dirichlet_nonzero_of_chosen_affine chosen_affine_input χ s hs hpole

theorem zeta {s : ℂ}
    (hs : (4374299 / 5000000 : ℝ) < s.re) (hpole : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  exact zeta_nonzero_off_pole_of_chosen_affine chosen_affine_input s hs hpole

theorem allHecke (χ : OAI.SevenEighths.HeckeFamily.Character) {s : ℂ}
    (hs : (4374299 / 5000000 : ℝ) < s.re)
    (hpole : ¬ (χ.residue = 1 ∧ s = 1)) :
    OAI.SevenEighths.HeckeFamily.LFunction χ s ≠ 0 := by
  exact hecke_nonzero_of_chosen_affine chosen_affine_input χ s hs (by tauto)

/-- Mathlib's total zeta function also has a nonzero value at its pole. -/
theorem zetaTotal {s : ℂ} (hs : (4374299 / 5000000 : ℝ) < s.re) :
    riemannZeta s ≠ 0 := by
  exact riemannZeta_nonzero_of_chosen_affine chosen_affine_input s hs

end Cycle61Verification
#print axioms Cycle61Verification.allDirichlet
#print axioms Cycle61Verification.zeta
#print axioms Cycle61Verification.allHecke
#print axioms Cycle61Verification.zetaTotal

end
/- END ORIGINAL Cycle61.Verification -/
