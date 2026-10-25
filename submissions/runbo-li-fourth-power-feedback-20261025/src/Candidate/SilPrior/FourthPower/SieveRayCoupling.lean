/- Copyright (c) 2026 Sil. Apache-2.0.
Finite ray and unit bookkeeping for the repeated-prime Gauss coupling.
The nonseparable character factors are explicit; only finite labels enter eta.
This closes the algebraic coupling step, not the subsequent sieve estimate. -/
import Candidate.SilPrior.FourthPower.SieveGaussPairs

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.SieveRayCoupling
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic CompletedGauss ConcreteTraceCRT
open CanonicalRowCompletion CanonicalQuadraticSieve CanonicalUnitEuler
open SexticSieve SievePrimitive SieveCoupling SieveGaussPairs
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem exists_unit (I : Id) (hI : Supported I) :
    ∃ u : Oˣ, modulus I = u.val * primaryGenerator I.radical := by
  have hr := radical_supported I hI
  have he : Ideal.span {primaryGenerator I.radical} = Ideal.span {modulus I} :=
    (primaryGenerator_spec I.radical (supported_primaryGenerator_ne_zero _ hr)).1.trans
      (span_modulus I hI.1).symm
  obtain ⟨u,hu⟩ := Ideal.span_singleton_eq_span_singleton.mp he
  exact ⟨u, by simpa only [mul_comm] using hu.symm⟩

def unit (I : Id) (hI : Supported I) : Oˣ := Classical.choose (exists_unit I hI)

theorem unit_spec (I : Id) (hI : Supported I) :
    modulus I = (unit I hI).val * primaryGenerator I.radical := Classical.choose_spec (exists_unit I hI)

def unitExponent (I : Id) : Fin 6 := ⟨((Ideal.absNorm I - 1)/6)%6, Nat.mod_lt _ (by decide)⟩

def unitPhase (e : Fin 6) (u : Oˣ) : ℂ := eisEmbedding (u.val^e.val)

theorem unit_value (I : Id) (hI : Supported I) (u : Oˣ) :
    idealRowHom u.val I = unitPhase (unitExponent I) u := by
  rw [idealRowHom_unit_norm u I hI.1 (supported_factors_good I hI)]
  exact congrArg eisEmbedding (pow_eq_pow_mod _ (unit_pow_six u))

abbrev Label := Oˣ × Fin 6 × EisensteinEPrimaryPhase.Coord

noncomputable instance : Fintype Label := by
  let : Finite Oˣ := PrimaryIdealUnitReindex.finite_units
  let : Fintype Oˣ := Fintype.ofFinite _
  exact inferInstance

def label (I : Id) (hI : Supported I) : Label :=
  (unit I hI, unitExponent I, SieveOperator.ray I.radical)

def eta (a b : Label) : ℂ :=
  star (unitPhase b.2.1 (-1)) * unitPhase a.2.1 b.1 * star (unitPhase b.2.1 a.1) *
    SieveOperator.phase a.2.2 b.2.2

theorem unitPhase_norm (e : Fin 6) (u : Oˣ) : ‖unitPhase e u‖ = 1 := by
  simp only [unitPhase, map_pow, norm_pow, GaussGeneratorTransport.norm_eisEmbedding_unit, one_pow]

theorem eta_norm_le (a b : Label) : ‖eta a b‖ ≤ 1 := by
  simpa only [eta, norm_mul, norm_star, unitPhase_norm, one_mul] using
    SieveOperator.phase_norm_le a.2.2 b.2.2

theorem labels_finite : Fintype.card Label = 576 := by
  let : Finite Oˣ := PrimaryIdealUnitReindex.finite_units
  let : Fintype Oˣ := Fintype.ofFinite _
  have hcard : Fintype.card Oˣ = 6 := by
    simpa only [Nat.card_eq_fintype_card] using PrimaryIdealUnitReindex.card_units_eq_six
  simp only [Label, EisensteinEPrimaryPhase.Coord, Fintype.card_prod, Fintype.card_fin, ZMod.card, hcard]

theorem modulus_symbol (I J : Id) (hI : Supported I) (hJ : Supported J) :
    idealRowHom (modulus J) I =
      unitPhase (unitExponent I) (unit J hJ) * rowValue J.radical I := by
  rw [unit_spec J hJ, idealRowHom_argument_mul, unit_value I hI]
  rfl

theorem minus_one (I : Id) (hI : Supported I) (hf : PowerFree 6 I) :
    (character I hI)⁻¹ (-1) = star (unitPhase (unitExponent I) (-1)) := by
  let : Finite (O ⧸ Ideal.span {modulus I}) := finite_quotient_span (modulus_ne_zero I)
  have he : character I hI (-1) = unitPhase (unitExponent I) (-1) := by
    simpa only [map_neg, map_one, Units.val_neg, Units.val_one] using
      (character_mk I hI hf (-1)).trans (unit_value I hI (-1))
  rw [← MulChar.star_apply', he]

/-- Literal normalized Gauss-sum coupling with a uniformly finite phase space.
No assumption of squarefree I or J, and no removal of the sharp cross terms. -/
theorem gauss_coupling (I J : Id) (hI : Supported I) (hJ : Supported J)
    (hfI : PowerFree 6 I) (hfJ : PowerFree 6 J) (hcop : IsCoprime I J) :
    pairGauss I J hI hJ = eta (label I hI) (label J hJ) * phase I hI * star (phase J hJ) *
      rowValue J.radical (sharp I) * star (rowValue I.radical (sharp J)) := by
  rw [pair_coupling I J hI hJ hfI hfJ hcop, minus_one J hJ hfJ,
    modulus_symbol I J hI hJ, modulus_symbol J I hJ hI, star_mul]
  calc
    _ = (star (unitPhase (unitExponent J) (-1)) *
        unitPhase (unitExponent I) (unit J hJ) * star (unitPhase (unitExponent J) (unit I hI))) *
        phase I hI * star (phase J hJ) *
        (rowValue J.radical I * star (rowValue I.radical J)) := by ring
    _ = _ := by
      rw [column_coupling I J hI hJ hcop]
      dsimp only [eta, label]
      ring

end
end Candidate.SilPrior.FourthPower.SieveRayCoupling
