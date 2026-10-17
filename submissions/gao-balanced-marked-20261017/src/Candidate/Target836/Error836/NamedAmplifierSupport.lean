import Candidate.Target836.SourceProvider.ErrorMain
import Candidate.Cycle63.Physical.AmplifierSupport
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.PrimeElements

set_option autoImplicit false
namespace OAI.SevenEighths.Target836ErrorPayment
noncomputable section
open Target874836.SourceProvider
open scoped BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve CenteredMomentPrimeElements CenteredMomentPrimePool
open CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O

/-- The actual annular pool supplies the extracted-error prime width.
The threshold is common to every amplifier cell and every prime element. -/
theorem eventual_actual_affine_error_prime_width
    (rayM : Ideal O)[NeZero rayM](H : Subgroup (O⧸rayM)ˣ)
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad) :
    ∀ᶠZ : ℝ in atTop,1 < Z ∧ ∀beta : ℝ,
      3401/100000 ≤ beta → beta ≤ 1/25 →
      let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1
        (Z^(Named.amp beta))
      ∀q : elementPool P,
        3*Named.amp beta/4 ≤ Real.logb Z (normValue q.val) := by
  have hmin : 0 < (902420521/120632400000:ℝ) := by norm_num
  filter_upwards [Cycle63.Physical.uniform_amplifier_norm_lower _ hmin] with Z hz
  refine ⟨hz.1,?_⟩
  intro beta hb₁ hb₂ P q
  have hp : ∀Q∈P,Prime Q:=fun Q hQ=>(primePool_data rayM H Sbad hbad _ _ _ Q hQ).1
  have hgood : ∀Q∈P,Q∉fixedBadPrimes:=fun Q hQ=>(primePool_data rayM H Sbad hbad _ _ _ Q hQ).2
  have hq:=elementPool_data P hp hgood q.val q.property
  have hn:=PNT.AnnularPrimeMass.norm_bounds_of_mem_annularPrimeIdeals
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) ≤ 1)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hz.1) _) (Finset.mem_sdiff.mp hq.2.1).1
  have hlo : Z^(Named.amp beta)/2 ≤ ((Ideal.span {q.val}).absNorm:ℝ) := by linarith [hn.1]
  have hnorm : 0 < ((Ideal.span {q.val}).absNorm:ℝ) :=
    (div_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hz.1) _) (by norm_num)).trans_le hlo
  apply (Real.le_logb_iff_rpow_le hz.1 (by simpa only [normValue] using hnorm)).mpr
  simpa only [normValue] using hz.2 (Named.amp beta) (Named.amp_bounds ⟨hb₁,hb₂⟩).1
    ((Ideal.span {q.val}).absNorm:ℝ) hlo

end
end OAI.SevenEighths.Target836ErrorPayment
#print axioms OAI.SevenEighths.Target836ErrorPayment.eventual_actual_affine_error_prime_width
