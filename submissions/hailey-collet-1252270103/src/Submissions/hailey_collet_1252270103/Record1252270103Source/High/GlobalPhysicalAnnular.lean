/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact finite annular payment for actual modified coefficients. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalAllocation
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.ActiveColumns
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstAnnularMajorant
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.CoupledFirst
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstAnnularMajorant
open CenteredMomentSectorLocalization Cycle61InitialMass
local notation "O" => HeckeFamily.O

lemma finite_dyadic_energy_le (f : O→ℂ) (rows : Finset O) (n : ℤ) :
    (∑z∈rows,dyadicWeight n (normValue z)*‖f z‖^2)≤
      ∑'z:O,dyadicWeight n (normValue z)*‖f z‖^2 := by
  rw [dyadic_energy_eq_sum]
  have he : (∑z∈rows,dyadicWeight n (normValue z)*‖f z‖^2)=
      ∑z∈rows.filter (fun z=>dyadicWeight n (normValue z)≠0),
        dyadicWeight n (normValue z)*‖f z‖^2 := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z hz
    split_ifs with h
    · rfl
    · simp only [not_not] at h
      rw [h,zero_mul]
  rw [he]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro z hz
    exact (mem_dyadRows n z).mpr (Finset.mem_filter.mp hz).2
  · intro z _ _
    exact mul_nonneg (dyadicWeight_bounds n _).1 (sq_nonneg _)

/-- The finite annular set costs only its actual dyadic bands, without
counting rows or choosing a bound separately for each row. -/
theorem finite_annular_energy_le_bands (f : O→ℂ) (H : ℝ) (hH : 0<H)
    (rows : Finset O)
    (hrows : ∀z∈rows,H/4≤‖eisEmbedding z‖^2 ∧ ‖eisEmbedding z‖^2≤H) :
    (∑z∈rows,‖f z‖^2)≤
      ∑n∈bands H,∑'z:O,dyadicWeight n (normValue z)*‖f z‖^2 := by
  have he (z : O) (hz : z∈rows) :
      ‖f z‖^2=∑n∈bands H,dyadicWeight n (normValue z)*‖f z‖^2 := by
    have hp := weighted_partition H (normValue z) hH
    have h1 := scaled_majorant H (normValue z) hH
      (by simpa only [normValue_eq_embedding] using (hrows z hz).1)
      (by simpa only [normValue_eq_embedding] using (hrows z hz).2)
    rw [h1,mul_one] at hp
    rw [←Finset.sum_mul,←hp,one_mul]
  calc
    _=∑z∈rows,∑n∈bands H,dyadicWeight n (normValue z)*‖f z‖^2 :=
      Finset.sum_congr rfl he
    _=∑n∈bands H,∑z∈rows,dyadicWeight n (normValue z)*‖f z‖^2 := Finset.sum_comm
    _≤_ := Finset.sum_le_sum (fun n _=>finite_dyadic_energy_le f rows n)

theorem finite_signed_annular_energy_le_bands (reflected : Bool) (f : O→ℂ)
    (H : ℝ) (hH : 0<H) (rows : Finset O)
    (hrows : ∀z∈rows,H/4≤‖eisEmbedding z‖^2 ∧ ‖eisEmbedding z‖^2≤H) :
    (∑z∈rows,‖f (firstSignedRow reflected z)‖^2)≤
      ∑n∈bands H,∑'z:O,dyadicWeight n (normValue z)*‖f z‖^2 := by
  cases reflected
  · exact finite_annular_energy_le_bands f H hH rows hrows
  · have hh := finite_annular_energy_le_bands f H hH (rows.image (fun z=>-z)) (by
      intro z hz
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
      simpa only [map_neg,norm_neg] using hrows x hx)
    rw [Finset.sum_image (fun x _ y _ h=>neg_injective h)] at hh
    exact hh

end
end QRH.Record1252270103Source.High.CoupledFirst
#print axioms QRH.Record1252270103Source.High.CoupledFirst.finite_annular_energy_le_bands
#print axioms QRH.Record1252270103Source.High.CoupledFirst.finite_signed_annular_energy_le_bands
