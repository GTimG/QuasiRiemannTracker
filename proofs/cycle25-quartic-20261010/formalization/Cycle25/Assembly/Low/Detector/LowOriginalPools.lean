import Cycle25.Assembly.Low.Geometry
import OAI.NumberTheory.DirichletL.Detector.LowSlotScales
import OAI.NumberTheory.DirichletL.Detector.RayPoolGood
import Cycle25.Assembly.Low.Detector.LowSlotScales
/-! Adapted from OpenAI/math family003, module Detector.LowOriginalPools at openai/math fd4aeeb2e
(the pruned source fork c388e88e6 no longer has it, so this file imports that module's own
imports). Changed physical geometry and explicit compensation bookkeeping.
Apache-2.0 upstream attribution retained. -/

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.Cycle25WeightedProbeLow
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
    (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤Cycle25.ell)
    (a b : ℝ) (ha : 0≤a) (hab : a≤b) :
    ∀ᶠ Z : ℝ in Filter.atTop,1≤Z ∧
      let T := fun i=>canonicalSlotSupport (pool R S a b (Z^(ell i)))
      ∀(J : Finset (Fin K))(p : LowUnselectedTuple T J),
      let L := elementNorm (∏i : J,(p i).val)
      1≤Z^(Cycle25.ly:ℝ)/L ∧
      1≤(Z^(Cycle25.ly:ℝ)/L)^2/lowPhysicalScale (calibrationForSet S hmax) (Z^(Cycle25.lx:ℝ)/L) (Z^(Cycle25.ly:ℝ)/L) ∧
      ∀δ : ℝ,0≤δ→lowGramFactor (calibrationForSet S hmax) (Z^(Cycle25.lx:ℝ)/L) (Z^(Cycle25.ly:ℝ)/L) δ≤
        Real.sqrt (3*elementNorm (calibrationForSet S hmax).generator/L)*Z^((Cycle25.signal Cycle25.theta)+((Cycle25.ly/2))*δ:ℝ) := by
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

end SevenEighths.Cycle25WeightedProbeLow
end

end OAI
