/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Metaplectic/Intertwining/RankOne/CoordinateIntegrability.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.TailAbsoluteConvergence

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneShellRepair
open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation
variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q)

theorem actual_standard_integral_coordinate_integrable
    (P : Polarization S.heisenberg)
    (J : CompactOpenLevel (ActualCover F ζ hζ q))
    (hJ : (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤ S.iwasawa.compact.toOpenSubgroup)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (ε : Sign) (s : ℂ) (hs : convergenceHalfPlane ε s)
    (φ : compactLevel S.borel P S.iwasawa (sourceSign ε) J)
    (k : S.iwasawa.compact.toOpenSubgroup) (h : actualTorus F ζ hζ q) :
    Integrable (actualStandardIntegrand F ζ hζ q S P ε s φ.val k h) μ := by
  obtain ⟨M, hM⟩ := actual_tail_absolute_convergence F ζ hζ q S P J hJ μ hμ π hπ ε
  obtain ⟨hC, hmC, _, _, hcover⟩ := actual_shell_compact_partition F q M
  have hc := standardIntegral_integrableOn_compact (LocalField F q) S.borel P S.iwasawa μ ε s φ.val k h _ hC hmC
  change IntegrableOn (actualStandardIntegrand F ζ hζ q S P ε s φ.val k h) _ μ at hc
  have hall := hc.union (hM s hs φ k h)
  rw [hcover, integrableOn_univ] at hall
  exact hall

end DedekindZetaZeroFree.KPRankOneShellRepair

end
