/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
   Literal per-row polynomial identities, before any Gauss row summation. -/
import Candidate.C092.transport.FixedPhysicalClassLedgerFinite
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.FixedFrameRowWitness
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentFirstSectors CenteredMomentSecondSectorEnergy
open CenteredMomentSecondMaskedWindow CenteredMomentSecondSectorColumns CenteredMomentRowNorm
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentSourceRow
open CenteredMomentFirstAmplificationChoice CenteredMomentHeckeColumnWindow
open CenteredMomentRestrictedEnergy CenteredMomentRestrictedSource CenteredMomentSourceLiveColumn
open CenteredMomentSecondHeightFamily CenteredMomentSecondExceptionalFamily CenteredMomentChildRows
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame
open QRH.Cycle092.FixedFourierH15 QRH.Cycle092.SignedCenter
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {L mesh Z : ℝ} {θ : GData L}

/-- Exact original H15 polynomial, at each z separately. This proof refines
    masked_child_energy before its tsum; it does not infer summand equality
    from an equality of total energies. -/
lemma masked_polynomial_eq_native (s : Source (Fin θ.N) θ.a θ.b) (ha : 0<θ.a)
    (ω₁ ω₂ ψ τ : Character) (χ : RayFourExpansion.RayCharacter)
    (D : FixedCubeDatum) (G : Id) (hG : Supported G) (E : Id)
    (hτ : ∀I : Id,Supported I → IsCoprime G I → ∀t,
      heightCoeff τ t I=heightCoeff ψ t I*CanonicalRowCompletion.idealRowHom D.A I*
        RayFourExpansion.rayCharacter χ (primaryGenerator I)) (v : ℝ) :
    rowPolynomial Finset.univ (sourceGenerator (residualPool G hG.1 (sourceColumns s)))
      (fun I : supportedColumns (residualPool G hG.1 (sourceColumns s))=>
        (if IsCoprime G (I:Id) ∧ E∣(I:Id) then
          TwistedRawSource.sourceColumn s ha (idealCoeff ω₁) (idealCoeff ω₂) 1 (G*I) else 0)*
            heightCoeff τ v I) D.z =
      nativeRowPolynomial s ha D ω₁ ω₂ ψ χ G hG E v := by
  symm
  unfold nativeRowPolynomial
  have he := funext (masked_divisor_coefficient ψ τ χ D.A G hG hτ (sourceColumns s)
    (TwistedRawSource.sourceColumn s ha (idealCoeff ω₁) (idealCoeff ω₂) 1) E v)
  rw [he,sector_rowPolynomial (sourceColumns s)
    (fun I=>(if E∣I then TwistedRawSource.sourceColumn s ha (idealCoeff ω₁) (idealCoeff ω₂) 1 (G*I) else 0)*
      heightCoeff τ v I) G hG D.z]
  congr 1
  funext I
  split_ifs <;> simp_all

/-- Coefficient transport is pointwise on the same original masked column,
    and hence preserves its polynomial at every row z. -/
lemma polynomial_character_congr (τ τ' : Character) (S : Finset Id) (c : Id→ℂ)
    (wm : O) (hwm : wm≠0)
    (hcoef : ∀I : Id,Supported I → IsCoprime I (Ideal.span {wm}) → idealCoeff τ I=idealCoeff τ' I)
    (hcol : ∀I∈S,Supported I → c I≠0 → IsCoprime I (Ideal.span {wm})) (v : ℝ) (z : O) :
    rowPolynomial Finset.univ (sourceGenerator S) (fun I : supportedColumns S=>c I*heightCoeff τ v I) z =
      rowPolynomial Finset.univ (sourceGenerator S) (fun I : supportedColumns S=>c I*heightCoeff τ' v I) z := by
  unfold rowPolynomial
  apply Finset.sum_congr rfl
  intro I _
  have hs := (Finset.mem_filter.mp I.property).2
  by_cases hc : c I=0
  · simp only [hc,zero_mul]
  · unfold heightCoeff
    dsimp only
    rw [hcoef I hs (hcol I (Finset.mem_filter.mp I.property).1 hs hc)]

#print axioms masked_polynomial_eq_native
#print axioms polynomial_character_congr
end
end QRH.Cycle092.FixedFrameRowWitness
