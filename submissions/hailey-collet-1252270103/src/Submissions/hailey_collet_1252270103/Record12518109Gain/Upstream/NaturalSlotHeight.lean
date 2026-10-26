/- Adapted from PR63 gao-balanced-marked-20261017; Apache-2.0. Exact source provenance is in evidence/homogeneous-gain/upstream-provenance.json. -/
import Submissions.hailey_collet_1252270103.Record12518109Gain.Upstream.AnnularHeight
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonMaskExpansion
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.PrimeAnnular

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61MarkedHeight
noncomputable section
open scoped Classical BigOperators
open Set HeckeFamily CenteredMomentCommonMaskExpansion HeckePrimeAnnular
local notation "O" => HeckeFamily.O

/-- The annular sum model is exactly the normalized natural prime slot,
with arbitrary arithmetic coefficients and actual character. -/
theorem naturalSlot_eq_annular (χ : Character) (pool : Finset (Ideal O))
    (ν : Ideal O→ℂ) (W : ℝ→ℂ) (P σ t : ℝ) :
    naturalSlot χ pool (fun I=>ν I*annularWeight W P σ t I) P=
      annularSum pool (fun I=>(Real.sqrt P:ℂ)⁻¹*idealCoeff χ I*ν I)
        (fun I=>(I.absNorm:ℝ)/P) W σ t := by
  unfold naturalSlot annularSum annularWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  have he : -HeckeDyadic.shift σ t=-(σ:ℂ)+(t:ℂ)*Complex.I := by
    unfold HeckeDyadic.shift
    ring
  rw [he]
  ring

/-- An actual marked natural-slot product may choose its common frequency
separately at every row. The energy hypotheses are genuine fixed-frequency
moments for finitely many smooth common profiles. -/
theorem naturalSlot_rowwise_energy {Row Slot : Type*} [DecidableEq Slot]
    (rows : Finset Row) (slots : Finset Slot) (N : ℕ) (hN : slots.card≤N)
    (χ : Row→Character) (pools : Slot→Finset (Ideal O))
    (hpools : ∀s∈slots,∀I∈pools s,I≠0)
    (ν : Slot→Ideal O→ℂ) (W : ℝ→ℂ) (P σ v : Slot→ℝ)
    (hP : ∀s∈slots,0<P s) (C : Row→ℂ)
    (a b E : ℝ) (hab : a≤b) (hE : 0≤E)
    (choice : Row→ℝ) (hchoice : ∀u∈rows,choice u∈Icc a b)
    (hmoment : ∀j : Fin (N+1),∀t∈Icc a b,
      ∑u∈rows,‖C u*(∏s∈slots,naturalSlot (χ u) (pools s)
        (fun I=>ν s I*annularWeight (commonProfile W j.val) (P s) (σ s) (t+v s) I)
        (P s))‖^2≤E) :
    (∑u∈rows,‖C u*(∏s∈slots,naturalSlot (χ u) (pools s)
      (fun I=>ν s I*annularWeight W (P s) (σ s) (choice u+v s) I) (P s))‖^2)≤
      (1+2*(b-a))*commonProfileCost N*E := by
  simp_rw [naturalSlot_eq_annular] at hmoment ⊢
  apply annular_rowwise_energy rows slots N hN pools
    (fun u s I=>(Real.sqrt (P s):ℂ)⁻¹*idealCoeff (χ u) I*ν s I)
    (fun s I=>(I.absNorm:ℝ)/(P s)) ?_ W σ v C a b E hab hE choice hchoice hmoment
  intro s hs I hI
  apply div_pos _ (hP s hs)
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hpools s hs I hI))

end
end OAI.SevenEighths.Cycle61MarkedHeight
#print axioms OAI.SevenEighths.Cycle61MarkedHeight.naturalSlot_rowwise_energy
