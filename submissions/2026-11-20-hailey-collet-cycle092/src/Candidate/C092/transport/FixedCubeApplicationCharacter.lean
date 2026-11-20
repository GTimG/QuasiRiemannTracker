/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.CubePairSupplying

set_option autoImplicit false
namespace QRH.Cycle092.SignedCenter
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentHeckeVolume HeckeRowClosure
local notation "O" => HeckeFamily.O

/-- The original fixed-inducing predicate, rather than an assumed ordinary
character or assumed factorization of the physical row coefficient. -/
structure FixedCubeDatum where
  η : Character
  Q : Ideal O
  m : O
  A : O
  z : O
  hQ : Q ≠ 0
  hm : m ≠ 0
  hA : A ≠ 0
  hz : z ≠ 0
  hml : ConcretePrimeRowBridge.goodLambda ∣ m
  hm2 : (2 : O) ∣ m
  fixed : CenteredExceptionalProfile.FixedInducingRow η Q m A z

def FixedCubeDatum.actualCoefficient (D : FixedCubeDatum) (I : Ideal O) : ℂ :=
  idealCoeff D.η I*CanonicalRowCompletion.idealRowHom (D.m^6*(D.A*D.z)) I

/-- The authentic original row coefficient has a primitive inducing character
and a presented-character conductor bounded by the original row conductor.
This is obtained from upstream fixedInducingRow_controlled and idealCoeff_eq_row. -/
theorem FixedCubeDatum.exists_ordinaryRow (D : FixedCubeDatum) :
    ∃ R : OrdinaryRow,R.Q=D.Q ∧
      Ideal.absNorm R.χ.modulus ≤ rowConductorBound D.η D.m 1 (D.A*D.z) ∧
      FiniteFourier.IsPrimitiveOnIdeals R.ψ.residue ∧
      ∀ I : Ideal O,idealCoeff R.χ I=D.actualCoefficient I := by
  obtain ⟨χ,ψ,hn,hprim,hind,hQ,hrow⟩ := fixedInducingRow_controlled D.η D.Q D.m D.A D.z
    D.hm D.hA D.hz D.hml D.hm2 D.fixed
  let R : OrdinaryRow := {
    η := D.η
    χ := χ
    ψ := ψ
    Q := D.Q
    hQ := D.hQ
    hQψ := hQ
    hind := hind
    m := D.m
    A := D.A
    z := D.z
    hml := D.hml
    hm2 := D.hm2
    hrow := hrow }
  refine ⟨R,rfl,hn,hprim,?_⟩
  intro I
  simpa only [FixedCubeDatum.actualCoefficient,one_pow,mul_one] using
    idealCoeff_eq_row D.η χ D.m 1 (D.A*D.z) hrow I

noncomputable def FixedCubeDatum.row (D : FixedCubeDatum) : OrdinaryRow :=
  Classical.choose D.exists_ordinaryRow

lemma FixedCubeDatum.row_spec (D : FixedCubeDatum) :
    D.row.Q=D.Q ∧
      Ideal.absNorm D.row.χ.modulus ≤ rowConductorBound D.η D.m 1 (D.A*D.z) ∧
      FiniteFourier.IsPrimitiveOnIdeals D.row.ψ.residue ∧
      ∀ I : Ideal O,idealCoeff D.row.χ I=D.actualCoefficient I :=
  Classical.choose_spec D.exists_ordinaryRow

lemma FixedCubeDatum.actualCoefficient_inducing (D : FixedCubeDatum) (I : Ideal O) :
    D.actualCoefficient I=
      if IsCoprime I D.row.χ.modulus then idealCoeff D.row.ψ I else 0 := by
  rw [←D.row_spec.2.2.2 I,D.row.hind I]

/-- The physical ideal source is defined from the original canonical row
factors before choosing any inducing characters. -/
def fixedCubePhysicalSource (D₁ D₂ : FixedCubeDatum) (P₁ P₂ : OrdinaryProfile)
    (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (x y : ℝ) : ℂ :=
  ∑' p : Ideal O×Ideal O,
    (if PairAllowed bad allowed p.1 p.2 then
      D₁.actualCoefficient p.1*D₂.actualCoefficient p.2 else 0)*
      P₁.normalized ((Ideal.absNorm p.1 : ℝ)/x)*P₂.normalized ((Ideal.absNorm p.2 : ℝ)/y)

/-- Discharges the authentic-character identification for both physical
ordinary factors, without relating their profiles, heights, rows or characters. -/
theorem fixedCubePhysicalSource_eq_literal (D₁ D₂ : FixedCubeDatum) (P₁ P₂ : OrdinaryProfile)
    (bad : Finset PrimeIdeal) (allowed : PrimeIdeal → Finset (ℕ×ℕ)) (x y : ℝ) :
    fixedCubePhysicalSource D₁ D₂ P₁ P₂ bad allowed x y=
      literalCubePairSource D₁.row D₂.row P₁ P₂ bad allowed x y := by
  apply tsum_congr
  intro p
  simp only [physicalPairTerm,literalCubePairCoefficient,
    D₁.row_spec.2.2.2 p.1,D₂.row_spec.2.2.2 p.2]

#print axioms FixedCubeDatum.exists_ordinaryRow
#print axioms FixedCubeDatum.actualCoefficient_inducing
#print axioms fixedCubePhysicalSource_eq_literal
end
end QRH.Cycle092.SignedCenter
