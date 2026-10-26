/- Adapted from OpenAI, Hailey Collet, DaysSky and accepted PR60. Apache-2.0.
Private .874836 assembly; the new affine analytic input remains explicit. -/
import Candidate.Target836.Target836Counts
/- Copyright (c) 2026. Released under Apache 2.0. -/
import Candidate.Cycle25.Assembly.Count.MomentDetectorPlainUnmarkedRestrictedField
import Candidate.Cycle25.Assembly.Count.SourceParametersCount
import Candidate.Cycle25.Assembly.Count.SourceMomentInput
import Candidate.Cycle25.Assembly.Count.MomentInput

/-! Source-parameter count and moment contract at the region-aware cutoff. -/

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.Target836SourceCount
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst Cycle25DetectorRowCount
open Cycle25ProbeHighRowFamily
open ProbeHighRowFamily

theorem balanced_source_count_affine
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (εm : ℝ) (Label : Type) [Fintype Label] (N n : ℕ)
    (dmin dmax τ logCost heightCost momentCost binWidth : ℝ)
    (hdmin : 0<dmin) (hdmax : 0<dmax) (hτ : 0<τ)
    (hl : 0<logCost) (hh : τ<heightCost) (hb : 0<binWidth) (counts : Target836Count.CountParameters M H εm) :
    ∃K : ℝ,0<K ∧ ∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax →
      ∀(a ε κplain ν C q : ℝ) (i : ℕ),i≤n → 51/100<a → 2*a-1≤3/4 → a≤1 → 0≤ε → ε≤1/100000 →
      7/10≤κplain → κplain≤3/4 → 0<ν → ν≤1/100 → 0≤C →
      ∀{Slot : Type} (B : Batch M H Label Slot (Z^d) a ε
        (Detector836.cutoff (2*a-1) (q/(2*a-1)) κplain) (Z^τ) ((Z^d)^(τ/(2*dmax))) i),
      B.slots.card≤N → B.binWidth=binWidth →
      B.rows.Nonempty →
      (∀u∈B.rows,rowMean B.slots (Z^d) ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=>u.val) B.profile B.upper B.widths B.external (Z^d)) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Cycle25DetectorRawFiber.Moments (B.fiber bin j J K hne) κplain counts.c counts.k (C*Z^momentCost) (Z^heightCost) εm) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Cycle25DetectorRawFiber.AffineMarkedMoment836 (B.fiber bin j J K hne) (C*Z^momentCost) (Z^heightCost) εm) →
      (B.rows.card:ℝ)≤K*C*Z^(logCost+heightCost+momentCost)*
        (Z^d)^(Detector836.count κplain (2*a-1) (q/(2*a-1))+159*ε+εm+B.mesh+7*ν) := by
  obtain ⟨K₀,hK₀,hcount⟩ := counts.affine
  obtain ⟨K,hK,hpref⟩ := source_count_prefactor_eventually (Label:=Label)
    N dmin dmax logCost heightCost momentCost binWidth K₀ hdmin hdmax hl (by linarith) hb
  refine ⟨K,hK,?_⟩
  filter_upwards [eventually_all_rpow_ge hcount dmin hdmin,hpref,
    source_count_frequency_eventually n dmax τ heightCost hdmax hτ hh,
    eventually_all_rpow_ge (eventually_gt_atTop (1:ℝ)) dmin hdmin,
    eventually_ge_atTop (1:ℝ)] with Z hcount hpref hfreq hU hZ
  intro d hd hd' a ε κplain ν C q i hi ha haδ ha' hε hε' hk hk1 hν hν1 hC Slot B hslots hbin hne hq hmom haff
  have hcard := hcount d hd a ε (Z^τ) ((Z^d)^(τ/(2*dmax))) κplain ν
    (C*Z^momentCost) (Z^heightCost) q i (hU d hd) ha haδ hε hε' hk hk1 hν hν1 (by positivity)
    (by positivity) (hfreq d hd' i hi) B hne hq hmom haff
  apply hcard.trans
  exact mul_le_mul_of_nonneg_right
    (hpref d hd hd' C a ε (Detector836.cutoff (2*a-1) (q/(2*a-1)) κplain) (Z^τ)
      ((Z^d)^(τ/(2*dmax))) i hC ha' B hslots hbin) (Real.rpow_nonneg (Real.rpow_nonneg (by linarith) _) _)

end SevenEighths.Target836SourceCount
end
end OAI

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Target836SourceCount
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorBatch HeckeDetectorRawFiber
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- Moments at the region-aware cutoff: the original fields and the affine
marked plain moment, for every fiber of every admissible source batch. -/
def SourceMomentsAtA {N : ℕ} (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (rows : Finset FreeRow) (ell : Fin N→ℝ) (W : Fin N→ℝ→ℂ)
    (Z d a ε τ dmax b slotMesh binWidth : ℝ) (i : ℕ) (z : ℂ)
    (κplain c κ C height εm : ℝ) : Prop :=
  ∀q : ℝ,∀B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N)
      (Z^d) a ε (Detector836.cutoff (2*a-1) (q/(2*a-1)) κplain) (Z^τ) ((Z^d)^(τ/(2*dmax))) i,
    B.rows⊆rows → B.data=sourceMomentData M H hH S hS η →
    B.reverse=sourceMomentReverse M H → B.slots=Finset.univ →
    B.widths=(fun j=>ell j/d) → B.profile=W → B.upper=(fun _=>b) → B.external=(fun _=>z) →
    B.mesh=slotMesh → B.binWidth=binWidth →
    (∀u∈B.rows,∀j,B.family u j=sourceDetectorFamily S hS η u (rayCubeFamily M H hH u) j) →
    ∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
      Cycle25DetectorRawFiber.Moments (B.fiber bin j J K hne) κplain c κ C height εm ∧
      Cycle25DetectorRawFiber.AffineMarkedMoment836 (B.fiber bin j J K hne) C height εm

end SevenEighths.Target836SourceCount

end

end OAI

#print axioms OAI.SevenEighths.Target836SourceCount.balanced_source_count_affine
