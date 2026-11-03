/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Whittaker/SelectedJacquet/LiteralArchSeparation.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Whittaker.SelectedJacquet.LiteralArchSlices

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.SheetRescaling
open NumberField KPLiteralRaw KPCplxCharacterHaar KPCplxPrincipalSeriesCharts
open KPLiteralScalarArchIndependentSlices
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def literalArchProduct (K : Subgroup (G F ζ hζ)) (f : Flat F ζ hζ K)
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (a : InfinitePlace F → ComplexGL2) : ℂ :=
  f.val 0 (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
    (fun w => Matrix.ProjGenLinGroup.mk (a w)) * c.val)

theorem literalArchProduct_slice (K : Subgroup (G F ζ hζ)) (f : Flat F ζ hζ K)
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (w : InfinitePlace F) (a : InfinitePlace F → ComplexGL2) (g : ComplexGL2) :
    literalArchProduct F ζ hζ K f c (Function.update a w g) =
      literalArchSlice F ζ hζ K f w (fun v => Matrix.ProjGenLinGroup.mk (a v)) c g := by
  unfold literalArchProduct literalArchSlice
  have he : (fun v => Matrix.ProjGenLinGroup.mk (Function.update a w g v)) =
      Function.update (fun v => Matrix.ProjGenLinGroup.mk (a v)) w
        (Matrix.ProjGenLinGroup.mk g) := by
    funext v
    by_cases hv : v = w <;> simp [hv]
  rw [he]

theorem literalArchProduct_separation
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (f : Flat F ζ hζ K) :
    ∃ (n : ℕ) (p : Fin n → (InfinitePlace F → ComplexGL2))
      (b : Fin n → ℂ) (h : Fin n → InfinitePlace F → KPLiteralTensor.harmonicPlus),
      ∀ (c : KPGlobalTorusFunctionData.finitePart F ζ hζ)
        (a : InfinitePlace F → ComplexGL2),
        literalArchProduct F ζ hζ K f c a =
          ∑ i, b i * literalArchProduct F ζ hζ K f c (p i) * ∏ w, (h i w).val (a w) := by
  obtain ⟨B, hB⟩ := literalArchPrincipalSeries_uniform_band F ζ hζ K hK f
  apply KPLiteralScalarArchCoefficientGeneration.harmonic_family_sampling
    (fun _ : InfinitePlace F => B) (literalArchProduct F ζ hζ K f)
  intro c w a
  refine ⟨⟨literalArchPrincipalSeries F ζ hζ K f w
    (fun v => Matrix.ProjGenLinGroup.mk (a v)) c, hB w _ c⟩, ?_⟩
  funext g
  exact (literalArchProduct_slice F ζ hζ K f c w a g).symm

end DedekindZetaZeroFree.SheetRescaling

end
