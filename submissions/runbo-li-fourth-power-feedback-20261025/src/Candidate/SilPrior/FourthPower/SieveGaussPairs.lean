/- Copyright (c) 2026 Sil. Apache-2.0.
Exact normalized Gauss coupling for two coprime sixth-power-free ideals.
Both cross-character values and the minus-one phase are retained. -/
import Candidate.SilPrior.FourthPower.SieveCoupling

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.SieveGaussPairs
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic CompletedGauss ConcreteTraceCRT
open CanonicalRowCompletion CanonicalQuadraticSieve SievePrimitive SexticSieve
open ConcreteBreveE
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem trace_phase (I : Id) (hI : Supported I) :
    normalizedTraceGauss (modulus I) (modulus_ne_zero I) (character I hI) = phase I hI := rfl

theorem inverse_trace (m : O) (hm : m ≠ 0) (χ : MulChar (O ⧸ Ideal.span {m}) ℂ) :
    normalizedTraceGauss m hm χ⁻¹ = χ⁻¹ (-1) * star (normalizedTraceGauss m hm χ) := by
  let : Finite (O ⧸ Ideal.span {m}) := finite_quotient_span hm
  let : Fintype (O ⧸ Ideal.span {m}) := Fintype.ofFinite _
  let ψ := eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates m hm
  have he : χ⁻¹ (-1) * star (gaussSum χ ψ) = gaussSum χ⁻¹ ψ := by
    rw [star_gaussSum_eq, ψ.inv_mulShift, ← Units.coe_neg_one]
    exact gaussSum_mulShift χ⁻¹ ψ (-1)
  dsimp only [normalizedTraceGauss]
  have hr : star (‖eisEmbedding m‖ : ℂ) = (‖eisEmbedding m‖ : ℂ) := by simp
  rw [star_div₀, hr]
  change gaussSum χ⁻¹ ψ / _ = _
  rw [← he]
  ring

def pairGauss (I J : Id) (hI : Supported I) (hJ : Supported J) : ℂ :=
  normalizedTraceGaussProduct (modulus I) (modulus J) (modulus_ne_zero I) (modulus_ne_zero J)
    (character I hI) (character J hJ)⁻¹

theorem pair_coupling (I J : Id) (hI : Supported I) (hJ : Supported J)
    (hfI : PowerFree 6 I) (hfJ : PowerFree 6 J) (hcop : IsCoprime I J) :
    pairGauss I J hI hJ =
      (character J hJ)⁻¹ (-1) * phase I hI * star (phase J hJ) *
        idealRowHom (modulus J) I * star (idealRowHom (modulus I) J) := by
  let : Finite (O ⧸ Ideal.span {modulus J}) := finite_quotient_span (modulus_ne_zero J)
  have hmod : IsCoprime (Ideal.span {modulus I}) (Ideal.span {modulus J}) := by
    rw [span_modulus I hI.1, span_modulus J hJ.1]
    exact SieveCoupling.radical_coprime I J hcop
  rw [pairGauss, normalizedTraceGaussProduct_crt _ _ _ _ hmod,
    inverse_trace, trace_phase, trace_phase]
  rw [← MulChar.star_apply', character_mk I hI hfI, character_mk J hJ hfJ]
  ring

theorem pair_modulus_norm (I J : Id) (hI : Supported I) (hJ : Supported J) :
    (Ideal.absNorm (Ideal.span {modulus I * modulus J}) : ℝ) *
      (Ideal.absNorm (SieveCoupling.sharp I) : ℝ) * Ideal.absNorm (SieveCoupling.sharp J) =
        (Ideal.absNorm I : ℝ) * Ideal.absNorm J := by
  rw [← Ideal.span_singleton_mul_span_singleton, span_modulus I hI.1, span_modulus J hJ.1,
    map_mul, Nat.cast_mul]
  calc
    _ = ((Ideal.absNorm I.radical : ℝ) * Ideal.absNorm (SieveCoupling.sharp I)) *
        ((Ideal.absNorm J.radical : ℝ) * Ideal.absNorm (SieveCoupling.sharp J)) := by ring
    _ = _ := by rw [SieveCoupling.norm_normal_form I hI.1, SieveCoupling.norm_normal_form J hJ.1]

end
end Candidate.SilPrior.FourthPower.SieveGaussPairs
