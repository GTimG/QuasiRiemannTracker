/- Copyright (c) 2026 Sil. Apache-2.0.
Witnesses of the proved natural reflection, with conductor bounds and exact
finite annuli. Data is inhabited unconditionally for every nonprincipal row.
-/
import Candidate.FourthPower.ReferenceReflection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.ReferenceNaturalData
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily EisensteinSchwartzPoisson
open CenteredMomentNaturalPrimitive CenteredMomentReflectionDeletion
open CenteredMomentReflectionMass CenteredMomentReflectionTailMass
open CenteredMomentSectorLocalization CenteredMomentReflectedTruncation
open CenteredMomentReflectedAnnuli
local notation "Id" => Ideal HeckeFamily.O

structure Data (χ : Character) where
  primitive : Character
  phase : ℂ
  isPrimitive : FiniteFourier.IsPrimitiveOnIdeals primitive.residue
  nonprincipal : primitive.residue ≠ 1
  phase_norm : ‖phase‖ = 1
  conductor_bound : primitive.modulus.absNorm *
    (redundantIdeal χ.modulus primitive.modulus).absNorm ≤ χ.modulus.absNorm
  reflection : let S := redundantSet χ.modulus primitive.modulus
    ∀ (W : 𝓢(ℝ,ℂ)) (X R : ℝ), 0 < X →
      let Y := fun (D : Finset Id) (H : SmoothIdeal S) =>
        (primitive.modulus.absNorm : ℝ)*(Ideal.absNorm (∏ P ∈ D, P) : ℝ)/(X*norm H.val)
      HeckeDyadic.polynomial χ false W X 0 0 = phase *
        ((∑ D ∈ S.powerset, ∑' H : SmoothIdeal S, coefficient primitive primitive.inverse S D H *
          HeckeDyadic.polynomial χ.inverse false
            (fun x => (retainedWeight R x : ℂ)*paperRadialFourier W x) (Y D H) 0 0) +
         ∑ D ∈ S.powerset, ∑' H : SmoothIdeal S, coefficient primitive primitive.inverse S D H *
          HeckeDyadic.polynomial χ.inverse false
            (fun x => (discardedWeight R x : ℂ)*paperRadialFourier W x) (Y D H) 0 0)

theorem data_exists (χ : Character) (hn : χ.residue ≠ 1) : Nonempty (Data χ) := by
  obtain ⟨ψ,G,hp,hne,hG,hcap,heq⟩ := ReferenceReflection.original_retained_reflection χ hn
  exact ⟨⟨ψ,G,hp,hne,hG,hcap,heq⟩⟩

namespace Data

def support {χ : Character} (r : Data χ) : Finset Id :=
  redundantSet χ.modulus r.primitive.modulus

def conductor {χ : Character} (r : Data χ) : ℝ := r.primitive.modulus.absNorm

def radicalNorm {χ : Character} (r : Data χ) : ℝ :=
  (redundantIdeal χ.modulus r.primitive.modulus).absNorm

def dualLength {χ : Character} (r : Data χ) (X : ℝ)
    (D : Finset Id) (H : SmoothIdeal r.support) : ℝ :=
  r.conductor*(Ideal.absNorm (∏ P ∈ D, P) : ℝ)/(X*norm H.val)

theorem conductor_one_le {χ : Character} (r : Data χ) : 1 ≤ r.conductor := by
  unfold conductor
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr r.primitive.modulus_ne_bot)

theorem conductor_radical_le {χ : Character} (r : Data χ) :
    r.conductor*r.radicalNorm ≤ (χ.modulus.absNorm : ℝ) := by
  unfold conductor radicalNorm
  exact_mod_cast r.conductor_bound

theorem radical_le {χ : Character} (r : Data χ) : r.radicalNorm ≤ (χ.modulus.absNorm : ℝ) := by
  exact (le_mul_of_one_le_left (Nat.cast_nonneg _) r.conductor_one_le).trans r.conductor_radical_le

theorem dualLength_bound {χ : Character} (r : Data χ) (X U : ℝ) (hX : 0 < X)
    (hcap : (χ.modulus.absNorm : ℝ) ≤ U*X) (D : Finset Id) (hD : D ∈ r.support.powerset)
    (H : SmoothIdeal r.support) : 0 < r.dualLength X D H ∧ r.dualLength X D H ≤ U := by
  exact dual_scale_bounds r.support D (redundantSet_prime _ _)
    (Finset.mem_powerset.mp hD) H r.conductor X U (zero_lt_one.trans_le r.conductor_one_le) hX
    (r.conductor_radical_le.trans hcap)

/-- The retained polynomial is a genuinely finite annular sum with the
original inverse character, not an arbitrary selected subset of ideals. -/
theorem retained_finite {χ : Character} (r : Data χ) (W : 𝓢(ℝ,ℂ)) (X R : ℝ)
    (hX : 0 < X) (D : Finset Id) (hD : D ∈ r.support.powerset) (H : SmoothIdeal r.support) :
    HeckeDyadic.polynomial χ.inverse false
      (fun x => (retainedWeight R x : ℂ)*paperRadialFourier W x) (r.dualLength X D H) 0 0 =
      ∑ n ∈ retainedAnnuli R (r.dualLength X D H)
        ((r.dualLength_bound X ((χ.modulus.absNorm : ℝ)/X) hX (by rw [div_mul_cancel₀ _ hX.ne']) D hD H).1),
        (Real.sqrt (dyadicScale n) : ℂ) * HeckeDyadic.polynomial χ.inverse false
          (annularProfile (paperRadialFourier W) (dyadicScale n))
          (dyadicScale n*r.dualLength X D H) 0 0 := by
  exact retained_finite_series χ.inverse _ (reflected_decayTwo W) R _ _

/-- All natural reflection coefficients have subpower total mass, uniformly
before choosing the row character or its primitive inducing character. -/
theorem coefficient_mass (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : Character) (r : Data χ) (Z : ℝ), 1 ≤ Z →
      (χ.modulus.absNorm : ℝ) ≤ Z^L →
      (∑ D ∈ r.support.powerset, ∑' H : SmoothIdeal r.support,
        ‖coefficient r.primitive r.primitive.inverse r.support D H‖) ≤ C*Z^ε := by
  obtain ⟨C,hC,hb⟩ := reflection_mass_subpower (ε/L) (div_pos hε hL)
  refine ⟨C,hC,?_⟩
  intro χ r Z hZ hmod
  apply (hb r.support (redundantSet_prime _ _) r.primitive r.primitive.inverse).2.trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  change r.radicalNorm^(ε/L) ≤ Z^ε
  calc
    _ ≤ (Z^L)^(ε/L) := Real.rpow_le_rpow (Nat.cast_nonneg _)
      (r.radical_le.trans hmod) (div_pos hε hL).le
    _ = _ := by
      rw [← Real.rpow_mul (zero_le_one.trans hZ)]
      congr 1
      exact mul_div_cancel₀ ε hL.ne'

end Data
end
end Candidate.FourthPower.ReferenceNaturalData
