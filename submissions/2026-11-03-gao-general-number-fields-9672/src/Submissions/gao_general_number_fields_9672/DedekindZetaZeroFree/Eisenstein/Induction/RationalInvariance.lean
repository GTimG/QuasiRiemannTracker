/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Induction/RationalInvariance.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Eisenstein.Induction.RationalBorelCovariance

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPLiteralExceptionalResidue.ResidueAutomorphy
open KPLiteralRaw

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 def cosetRight (γ : Matrix.ProjGenLinGroup (Fin 2) F) :
    KPChamberBruhatTwoCells.RationalQuotient F ≃
      KPChamberBruhatTwoCells.RationalQuotient F :=
  Quotient.congr (Equiv.mulRight γ) (by
    intro a b
    simp only [QuotientGroup.rightRel_apply]
    change b * a⁻¹ ∈ KPChamberBruhatTwoCells.rationalBorel F ↔
      (b * γ) * (a * γ)⁻¹ ∈ KPChamberBruhatTwoCells.rationalBorel F
    simp only [mul_inv_rev, mul_assoc, mul_inv_cancel_left])

theorem eisenstein_rational (K : Subgroup (G F ζ hζ))
    (f : Flat F ζ hζ K) (s : ℂ) (hs : (1 : ℝ) / 3 < s.re)
    (γ : Matrix.ProjGenLinGroup (Fin 2) F) (g : G F ζ hζ) :
    eisenstein F ζ hζ K f s (rationalLift F ζ hζ γ * g) =
      eisenstein F ζ hζ K f s g := by
  let e := cosetRight F γ
  unfold eisenstein
  rw [← e.tsum_eq (fun c => f.val s (rationalLift F ζ hζ (Quotient.out c) * g))]
  apply tsum_congr
  intro c
  have he : e c = KPChamberBruhatTwoCells.rationalCoset F (Quotient.out c * γ) := by
    change (cosetRight F γ) c = _
    conv_lhs => rw [← Quotient.out_eq c]
    rfl
  rw [he, val_rationalCoset_out_eq, rationalLift_mul, mul_assoc]

end DedekindZetaZeroFree.KPLiteralExceptionalResidue.ResidueAutomorphy

end
