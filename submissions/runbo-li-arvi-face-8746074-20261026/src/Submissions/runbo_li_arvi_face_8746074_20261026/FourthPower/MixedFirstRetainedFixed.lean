/- Copyright (c) 2026 Sil. Apache-2.0.
Exact selected first-Poisson expansion on a common label set fixed before
the selected product. The actual source may already contain avoidance.
No moment or block estimate is assumed.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedFirstPhysicalBudget
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedFirstCommonSum
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstRetainedAssembly
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstRetainedActive
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalActiveDictionary
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalDyadicRows

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedFirstRetainedFixed
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentSecondHeightFamily
open CenteredMomentActiveSource CenteredMomentSupportedCorrelation CenteredMomentCommonSupport
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst CenteredMomentFirstColumns
open CenteredMomentFirstRetainedAssembly CenteredMomentFirstRetainedActive
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentFirstPhysicalDyadicRows
open CenteredMomentFirstPhysicalActiveDictionary CenteredMomentFirstSectorLocalization
open CenteredMomentFirstDiscardedEnergy CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentFirstScale
open CenteredMomentFirstSectorTransform
open CenteredMomentSecondRetainedRows CenteredMomentRowNorm CenteredMomentFirstReduced
open MixedPrincipalPair MixedPrincipalWindow MixedOriginalTail MixedOriginalNormCap
open MixedInnerExceptionalBlock MixedInnerExceptionalLedger
open MixedFirstPhysicalApplication MixedFirstPhysicalBudget MixedFirstCommonSum
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- The filtering coefficient and the coefficient in the retained form
need not be equal: only actual zero-support containment is used. -/
theorem retained_on_fixed_support (η : Character) (m A : O) (t : ℝ)
    (S : Finset Id) (base c : Id→ℂ) (hc : ∀I,base I=0→c I=0)
    (Φ : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    retainedEnergy η m A t (activeSource S base) c Φ K X Z ξ=
      retainedEnergy η m A t S c Φ K X Z ξ := by
  rw [retained_energy_sum,retained_energy_sum,supportedColumns_active]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hi : base I=0
  · simp only [hi,ne_eq,not_true_eq_false,ite_false,hc I hi,zero_mul,Finset.sum_const_zero]
  · rw [if_pos hi]
    apply Finset.sum_congr rfl
    intro J hJ
    by_cases hj : base J=0
    · simp only [hj,ne_eq,not_true_eq_false,ite_false,hc J hj,zero_mul,star_zero,mul_zero]
    · simp only [hj,ne_eq,not_false_eq_true,ite_true]

/-- Restore the original column pool after fixing labels by base support.
This does not infer that any untwisted physical block is nonzero. -/
theorem block_on_fixed_support (η : Character) (m A : O) (t : ℝ)
    (S : Finset Id) (base c : Id→ℂ) (hc : ∀I,base I=0→c I=0)
    (C D : Id) (hC : Supported C) (hD : Supported D)
    (E : Finset (CommonIndex C D)) (rows : Finset O)
    (Φ : 𝓢(ℝ,ℂ)) (windows : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ) :
    block η m A t (activeSource S base) c C D hC hD E rows Φ windows K K₀ H₀ A₀ B₀=
      block η m A t S c C D hC hD E rows Φ windows K K₀ H₀ A₀ B₀ := by
  rw [block_eq_ideal_sums,block_eq_ideal_sums]
  congr 1
  apply Finset.sum_congr rfl
  intro z hz
  exact column_pair_sum_active C D hC.1 hD.1 S base
    (physicalTerm η m A t c C D hC E Φ windows K K₀ H₀ A₀ B₀ z)
    (fun I J hi=>physicalTerm_zero_left η m A t c C D hC E Φ windows K K₀ H₀ A₀ B₀ z I J
      (hc (C*I) hi))
    (fun I J hj=>physicalTerm_zero_right η m A t c C D hC E Φ windows K K₀ H₀ A₀ B₀ z I J
      (hc (D*J) hj))

def firstRadius (s : Source ι a b) (C D : Id) (E : Finset (CommonIndex C D))
    (K Z ξ : ℝ) : ℝ :=
  frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K (sourceVolume s)) Z ξ

/-- The literal retained row disk, intersected with the exact dyadic
window. Keeping the intersection avoids enlarging an equality to a bound. -/
def fixedRows (radius : ℝ) (n : Fin 4→ℤ) : Finset O :=
  activeRows (retainedRows radius 1) n

theorem fixedRows_nonzero (radius : ℝ) (n : Fin 4→ℤ) (z : O)
    (hz : z∈fixedRows radius n) : z≠0 :=
  activeRows_nonzero (retainedRows radius 1) n z hz

/-- This is exactly the annular support to which the checked child
cutoffs apply. No equality between the two different child scales is used. -/
theorem fixedRows_annular (radius : ℝ) (n : Fin 4→ℤ) :
    fixedRows radius n⊆MixedFirstExceptionalWindow.annularRows (n 1) := by
  intro z hz
  apply (MixedFirstExceptionalWindow.mem_annularRows (n 1) z).mpr
  have hnorm := activeRows_norm (retainedRows radius 1) n z hz
  refine ⟨fixedRows_nonzero radius n z hz,?_⟩
  have hpos := dyadicScale_pos (n 1)
  linarith [hnorm.2.2]

/-- Exact expansion for one selected product, with fixed actual labels.
The source is unrestricted here; in applications it is avoidSource s u. -/
theorem selected_retained_fixed (s : Source ι a b) (ha : 0<a) (seed F : Id)
    (η : Character) (t : ℝ) (Φ : 𝓢(ℝ,ℂ)) (K Z ξ H : ℝ)
    (hK : 0<K) (hH : sourceNormCap s.P b s.T s.d≤H) :
    retainedEnergy η (fixedBadMask*idealGenerator s.R) 1 t (sourceColumns s)
      (selectedCoefficient s ha seed F) Φ K (sourceVolume s) Z ξ=
    ∑p : Labels s ha seed,∑E∈inactiveSubsets p.val.1 p.val.2,
      ∑n : Blocks (effectiveScale p.val.1 p.val.2 E K)
        (firstRadius s p.val.1 p.val.2 E K Z ξ)
        (H/p.val.1.absNorm) (H/p.val.2.absNorm),
      commonHeight s η t p.val.1 p.val.2*
        block η (fixedBadMask*idealGenerator s.R) 1 t (sourceColumns s)
          (selectedCoefficient s ha seed F) p.val.1 p.val.2
          (commonLabels_supported (activeSource (sourceColumns s) (sourceCoefficient s ha seed)) p).1
          (commonLabels_supported (activeSource (sourceColumns s) (sourceCoefficient s ha seed)) p).2
          E (fixedRows (firstRadius s p.val.1 p.val.2 E K Z ξ) (fun i=>n i))
          Φ (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
            (dyadicScale (n 2)) (dyadicScale (n 3)) := by
  dsimp only [firstRadius]
  have hz (I : Id) (hI : sourceCoefficient s ha seed I=0) :
      selectedCoefficient s ha seed F I=0 := by
    simp only [selectedCoefficient,hI,zero_mul]
  have hcap (I : Id) (hI : selectedCoefficient s ha seed F I≠0) :
      (I.absNorm:ℝ)≤H :=
    (original_coefficient_cap s ha seed I (selected_support s ha seed F I hI)).2.trans hH
  rw [←retained_on_fixed_support η (fixedBadMask*idealGenerator s.R) 1 t
    (sourceColumns s) (sourceCoefficient s ha seed) (selectedCoefficient s ha seed F) hz]
  rw [retained_energy_blocks]
  apply Finset.sum_congr rfl
  intro p hp
  change commonHeight s η t p.val.1 p.val.2*
    infiniteSector η (fixedBadMask*idealGenerator s.R) 1 t
      (activeSource (sourceColumns s) (sourceCoefficient s ha seed))
      (selectedCoefficient s ha seed F) p.val.1 p.val.2 _ _ Φ K (sourceVolume s) Z ξ=_
  unfold infiniteSector
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro E hE
  rw [retainedInfiniteBlock_eq_finite,retainedBlock_eq_blocks _ _ _ _ _ _ _ _ _ _ _ _
    (retained_rows_nonzero _) _ _ _ H hK hcap,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [block_on_fixed_support _ _ _ _ _ _ _ hz,
    block_activeRows (n:=fun i=>(n i:ℤ))]
  rfl

/-- Exact selected average. The three finite index sets and the row set
are chosen before F. commonHeight is included once by physicalAverage. -/
theorem selected_retained_average (s : Source ι a b) (ha : 0<a) (seed : Id)
    (η : Character) (t : ℝ) (Φ : 𝓢(ℝ,ℂ)) (K Z ξ H : ℝ)
    (hK : 0<K) (hH : sourceNormCap s.P b s.T s.d≤H)
    (Ds : Finset Id) (weight : Id→ℝ) (W : ℝ) :
    (∑F∈Ds,((weight F/W:ℝ):ℂ)*
      retainedEnergy η (fixedBadMask*idealGenerator s.R) 1 t (sourceColumns s)
        (selectedCoefficient s ha seed F) Φ K (sourceVolume s) Z ξ)=
    ∑p : Labels s ha seed,∑E∈inactiveSubsets p.val.1 p.val.2,
      ∑n : Blocks (effectiveScale p.val.1 p.val.2 E K)
        (firstRadius s p.val.1 p.val.2 E K Z ξ)
        (H/p.val.1.absNorm) (H/p.val.2.absNorm),
      physicalAverage s ha seed η t p.val.1 p.val.2
        (commonLabels_supported (activeSource (sourceColumns s) (sourceCoefficient s ha seed)) p).1
        (commonLabels_supported (activeSource (sourceColumns s) (sourceCoefficient s ha seed)) p).2
        E (fixedRows (firstRadius s p.val.1 p.val.2 E K Z ξ) (fun i=>n i))
        Ds weight W Φ K (dyadicScale (n 0)) (dyadicScale (n 1))
          (dyadicScale (n 2)) (dyadicScale (n 3)) := by
  simp_rw [selected_retained_fixed s ha seed _ η t Φ K Z ξ H hK hH,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro E hE
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  unfold physicalAverage
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro F hF
  ring

end
end Candidate.FourthPower.MixedFirstRetainedFixed
