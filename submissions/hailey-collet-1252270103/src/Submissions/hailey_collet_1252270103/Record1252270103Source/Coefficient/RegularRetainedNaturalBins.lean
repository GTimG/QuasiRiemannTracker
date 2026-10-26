/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
The checked Cycle61 buffered partition is retained with the actual source cut
(q+1)/2. Both height intervals and the full natural character remain literal. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.RegularRetainedNaturalState
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.GeometryZeroPartition

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators
open Set Filter HeckeFamily HeckeDetectorZeros LocalMoment
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource ConcreteTraceCRT
open Cycle61Moment Cycle61Moment.LowBranch Cycle61InitialMass
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Only actual buffered intervals enter this source-facing predicate. -/
def RetainedZeroBin {Z Bmask bΦ : ℝ} (st : NaturalState Z Bmask bΦ)
    (η₀ : Character) (hQM : st.fixedModulus ≤ M) (hQη : st.fixedModulus ≤ η₀.modulus)
    (z : O) (hz : st.radial.keep z) (e T : ℝ) (p : BufferIndex e) : Prop :=
    1 ≤ p.1.val ∧ p.1.val ≤ bufferCount e ∧
    51 / 100 ≤ bufferValue e p ∧ bufferValue e p ≤ HeckeZeroSupremum.beta ∧
    bufferValue e p ≤ 7 / 8 ∧
    bufferValue e p ≤ geometryRowMaximum M H hH st η₀ hQM hQη z hz ((3 * p.1.val : ℕ) * T) ∧
    geometryRowMaximum M H hH st η₀ hQM hQη z hz ((3 * p.1.val : ℕ) * T) < bufferValue e p + e ∧
    bufferValue e p ≤ geometryRowMaximum M H hH st η₀ hQM hQη z hz (3 * (p.1.val + 1 : ℕ) * T) ∧
    geometryRowMaximum M H hH st η₀ hQM hQη z hz (3 * (p.1.val + 1 : ℕ) * T) < bufferValue e p + 2 * e

theorem actual_retained_zero_partition {Z Bmask bΦ : ℝ} (st : NaturalState Z Bmask bΦ)
    (η₀ : Character) (hQM : st.fixedModulus ≤ M) (hQη : st.fixedModulus ≤ η₀.modulus)
    (z : O) (hz : st.radial.keep z) (e T : ℝ) (he : 0 < e) (hT : 2 < T)
    (hβlo : 51 / 100 ≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta ≤ 7 / 8) :
    ∃ p : BufferIndex e, RetainedZeroBin M H hH st η₀ hQM hQη z hz e T p := by
  obtain ⟨p, hi, hin, ha, ha', hcl, hcu, hnl, hnu, _⟩ :=
    actual_geometry_zero_partition M H hH st η₀ hQM hQη z hz e T he hT hβlo hβhi
  have hmax := zeroMaximum_le_beta (geometryRowFamily M H hH st η₀ z hz)
    (geometry_row_family_nonprincipal M H hH st η₀ hQM hQη z hz) hβlo
    ((3 * p.1.val : ℕ) * T)
  exact ⟨p, hi, hin, ha, hcl.trans hmax, ha', hcl, hcu, hnl, hnu⟩

/-- The strict LOW cut is the actual node's q; no numerical cutoff is substituted. -/
theorem retained_zero_bin_low {Z Bmask bΦ : ℝ} (st : NaturalState Z Bmask bΦ)
    (η₀ : Character) (hQM : st.fixedModulus ≤ M) (hQη : st.fixedModulus ≤ η₀.modulus)
    (z : O) (hz : st.radial.keep z) (e T q : ℝ) (p : BufferIndex e)
    (hbin : RetainedZeroBin M H hH st η₀ hQM hQη z hz e T p)
    (hlow : bufferValue e p < (q + 1) / 2)
    (hs : st.radial.profile (‖eisEmbedding z‖ ^ 2 / st.radial.scale) ≠ 0) :
    ActualLow M H hH st η₀ hQM hQη ((q + 1) / 2) e
      (3 * (p.1.val + 1 : ℕ) * T) z := by
  apply whole_source_upper_actual_low M H hH st η₀ hQM hQη z hz _ _ _ hs
  have hu := hbin.2.2.2.2.2.2.2.2
  change geometryRowMaximum M H hH st η₀ hQM hQη z hz _ < _
  linarith

/-- In HIGH the actual density lies in the certified node interval and below
the true supremum. In particular HIGH is empty when 2 beta - 1 < q. -/
theorem retained_zero_bin_high {Z Bmask bΦ : ℝ} (st : NaturalState Z Bmask bΦ)
    (η₀ : Character) (hQM : st.fixedModulus ≤ M) (hQη : st.fixedModulus ≤ η₀.modulus)
    (z : O) (hz : st.radial.keep z) (e T q : ℝ) (p : BufferIndex e)
    (hbin : RetainedZeroBin M H hH st η₀ hQM hQη z hz e T p)
    (hq : 1 / 2 ≤ q) (hhigh : (q + 1) / 2 ≤ bufferValue e p) :
    3 / 4 ≤ bufferValue e p ∧ bufferValue e p ≤ 7 / 8 ∧
      q ≤ 2 * bufferValue e p - 1 ∧ 2 * bufferValue e p - 1 ≤ 3 / 4 ∧
      2 * bufferValue e p - 1 ≤ 2 * HeckeZeroSupremum.beta - 1 := by
  obtain ⟨_, _, _, hb, hb', _⟩ := hbin
  refine ⟨by linarith, hb', by linarith, by linarith, by linarith⟩

theorem retained_zero_high_empty {Z Bmask bΦ : ℝ} (st : NaturalState Z Bmask bΦ)
    (η₀ : Character) (hQM : st.fixedModulus ≤ M) (hQη : st.fixedModulus ≤ η₀.modulus)
    (z : O) (hz : st.radial.keep z) (e T q : ℝ) (p : BufferIndex e)
    (hbin : RetainedZeroBin M H hH st η₀ hQM hQη z hz e T p)
    (hκ : 2 * HeckeZeroSupremum.beta - 1 < q) : bufferValue e p < (q + 1) / 2 := by
  have hb := hbin.2.2.2.1
  linarith

/-- Exact finite reassembly at any node cut. -/
theorem retained_zero_low_high_reassembly (e q : ℝ) (weight : BufferIndex e → ℝ) :
    (∑ p, weight p) =
      (∑ p ∈ Finset.univ.filter (fun p => bufferValue e p < (q + 1) / 2), weight p) +
      (∑ p ∈ Finset.univ.filter (fun p => (q + 1) / 2 ≤ bufferValue e p), weight p) := by
  simpa only [not_lt] using
    (Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := fun p => bufferValue e p < (q + 1) / 2) (f := weight)).symm

#print axioms RetainedZeroBin
#print axioms actual_retained_zero_partition
#print axioms retained_zero_bin_low
#print axioms retained_zero_bin_high
#print axioms retained_zero_high_empty
#print axioms retained_zero_low_high_reassembly
end
end OAI.SevenEighths.Record1252270103Source
