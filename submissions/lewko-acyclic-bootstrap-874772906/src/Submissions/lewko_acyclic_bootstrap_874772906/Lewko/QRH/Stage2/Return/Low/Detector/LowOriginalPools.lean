/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.Low.Geometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowSlotScales
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.RayPoolGood
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.Low.Detector.LowSlotScales
/-! Adapted from OpenAI/math family003, module Detector.LowOriginalPools at openai/math fd4aeeb2e
(the pruned source fork c388e88e6 no longer has it, so this file imports that module's own
imports). Changed physical geometry and explicit compensation bookkeeping.
Apache-2.0 upstream attribution retained. -/

set_option autoImplicit false

namespace OAI

noncomputable section
variable [QRH.LewkoStage2Return.Geometry.Parameters]
open scoped Classical
namespace SevenEighths.LewkoStage2ProbeLow
open ProbePhysical
open CompletedGauss CanonicalQuadraticSieve ProbeRaySlots
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma originalPool_element_norm (R : Set Id) (S : Finset Id) (hS : SourceExclusions S)
    (a b Y : ℝ) (ha : 0≤a) (hab : a≤b) (hY : 0<Y) (n : O)
    (hn : n∈canonicalSlotSupport (pool R S a b Y)) : elementNorm n≤Y*b := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
  rw [primaryTuple_norm P (pool_supported R S hS a b Y P hP)]
  exact (pool_norm_bounds R S ha hab hY P hP).2

theorem originalPools_low_scales {K : ℕ} (R : Set Id) (S : Finset Id)
    (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤QRH.LewkoStage2Return.Geometry.ell)
    (a b : ℝ) (ha : 0≤a) (hab : a≤b) :
    ∀ᶠ Z : ℝ in Filter.atTop,1≤Z ∧
      let T := fun i=>canonicalSlotSupport (pool R S a b (Z^(ell i)))
      ∀(J : Finset (Fin K))(p : LowUnselectedTuple T J),
      let L := elementNorm (∏i : J,(p i).val)
      1≤Z^(QRH.LewkoStage2Return.Geometry.y:ℝ)/L ∧
      1≤(Z^(QRH.LewkoStage2Return.Geometry.y:ℝ)/L)^2/lowPhysicalScale (calibrationForSet S hmax) (Z^(QRH.LewkoStage2Return.Geometry.x:ℝ)/L) (Z^(QRH.LewkoStage2Return.Geometry.y:ℝ)/L) ∧
      ∀δ : ℝ,0≤δ→lowGramFactor (calibrationForSet S hmax) (Z^(QRH.LewkoStage2Return.Geometry.x:ℝ)/L) (Z^(QRH.LewkoStage2Return.Geometry.y:ℝ)/L) δ≤
        Real.sqrt (3*elementNorm (calibrationForSet S hmax).generator/L)*Z^((QRH.LewkoStage2Return.Geometry.signal QRH.LewkoStage2Return.Geometry.theta)+((QRH.LewkoStage2Return.Geometry.y/2))*δ:ℝ) := by
  filter_upwards [eventually_original_slot_scales (calibrationForSet S hmax) ell hell hsum
    (max 1 b) (le_max_left _ _)] with Z hZ
  refine ⟨hZ.1,?_⟩
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ.1
  apply hZ.2
  · intro i n hn
    exact canonicalSlotSupport_nonzero _ (pool_supported R S hS a b _) n hn
  · intro i n hn
    apply (originalPool_element_norm R S hS a b (Z^(ell i)) ha hab (by positivity) n hn).trans
    calc
      _≤Z^(ell i)*max 1 b := mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
      _=_ := mul_comm _ _

end SevenEighths.LewkoStage2ProbeLow
end

end OAI
