/- Copyright (c) 2026 Joseph Bebel. -/
import Candidate.Local.Qrh.JointDetector.NaturalSwapBound

/-! Actual finite sector estimate: literal mixed Poisson packet identity,
the common Mellin bound, and the exact ideal-Möbius price. The only operator
inputs are the two selected squarefree pivot norms. -/
namespace Qrh.JointDetector.NaturalSectorBound
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ActualEisensteinCubic ActualEisensteinCoordinates
open CanonicalRowCompletion CanonicalQuadraticSieve ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open NaturalSelectedNorm NaturalSharedTables NaturalPairPackets NaturalNearPackets
local notation "O" => ActualEisensteinCubic.O

def prefactorBound (F : Finset ColourTuple) (g : SharedTable) (L : ℝ)
    (E : Finset (SourceMaskIndex F)) (DL DR : ℝ) : ℝ :=
  8*L/(‖eisEmbedding (primeSubsetGenerator (sourceMaskPrime F) E)‖^2*
    Real.sqrt ((Ideal.absNorm (offDiagonalIdeal g):ℝ)*DL*DR))

theorem packetPrefactor_norm_le (F : Finset ColourTuple) (g : SharedTable) (L : ℝ)
    (hL : 0 ≤ L) (E : Finset (SourceMaskIndex F)) (DL DR : ℝ) :
    ‖packetPrefactor F g L E DL DR‖ ≤ prefactorBound F g L E DL DR := by
  have hmu := QuadraticInitialBound.norm_ideal_moebius_le_one (NaturalActualTail.maskIdeal F E)
  calc
    _ = (8*L)*‖(UniqueFactorizationMonoid.moebius (NaturalActualTail.maskIdeal F E):ℂ)‖/
        (‖eisEmbedding (primeSubsetGenerator (sourceMaskPrime F) E)‖^2*
          Real.sqrt ((Ideal.absNorm (offDiagonalIdeal g):ℝ)*DL*DR)) := by
      simp [packetPrefactor,norm_div,norm_mul,abs_of_nonneg hL,abs_of_nonneg (Real.sqrt_nonneg _)]
    _ ≤ prefactorBound F g L E DL DR :=
      div_le_div_of_nonneg_right (mul_le_of_le_one_right (by positivity) hmu) (by positivity)

/-- The profile constant is fixed before every actual family, table,
puncture, bad-frequency sector, ordinary source set, scale and dual vector.
All cross selectors remain inside the proved finite swap. -/
theorem actual_sector_bound (W : 𝓢(ℝ,ℂ)) (decay : ℕ) :
    ∃ C : ℝ,0 ≤ C ∧
    ∀ (F : Finset ColourTuple) (hF : ∀ c ∈ F,∀ j,Admissible (c j))
      (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
      (g : SharedTable) (hgn : ∀ j k,g j k ≠ 0)
      (hgp : Pairwise (fun p q : Fin 5 × Fin 5 => IsCoprime (g p.1 p.2) (g q.1 q.2)))
      (hLF : ∀ a ∈ leftFamily F g,∀ j,Admissible (a j))
      (hRF : ∀ a ∈ rightFamily F g,∀ j,Admissible (a j))
      (α β : ColourTuple → ℂ) (L : ℝ) (hL : 0 ≤ L)
      (E : Finset (SourceMaskIndex F)) (k : Oˣ × ℕ × ℕ) (S : Finset (Ideal O))
      (hS : ∀ I ∈ S,Supported I) (rL rR : EisensteinEPrimaryPhase.Coord)
      (hrL : ∀ a ∈ leftFamily F g,residue (primaryGenerator (a 0))=rL)
      (hrR : ∀ a ∈ rightFamily F g,residue (primaryGenerator (a 0))=rR)
      (Y DL DR KL KR BL BR ε : ℝ) (hε : 0 < ε),
      0 < DL → 0 < DR → 0 < Y → 0 < packetScale F g L E k Y DL DR →
      0 ≤ KL → 0 ≤ KR → 0 ≤ BL → 0 ≤ BR →
      (∀ v,selectedNorm (leftRows F g v) S ≤ KL) →
      (∀ w,selectedNorm (rightRows F g w) S ≤ KR) →
      (∀ a ∈ leftFamily F g,(Ideal.absNorm (a 0):ℝ) ≤ BL) →
      (∀ a ∈ rightFamily F g,(Ideal.absNorm (a 0):ℝ) ≤ BR) →
      (∀ a ∈ leftFamily F g,radicalNorm a/DL ∈ Set.Icc (1:ℝ) 2) →
      (∀ a ∈ rightFamily F g,radicalNorm a/DR ∈ Set.Icc (1:ℝ) 2) →
      (∀ I ∈ S,(Ideal.absNorm I:ℝ)/Y ∈ Set.Icc (1:ℝ) 2) →
      ‖actualSectorForm F hF g α β W L E k S‖ ≤
        prefactorBound F g L E DL DR*(C/(1+packetScale F g L E k Y DL DR)^decay)*
        Real.sqrt (((rightFamily F g).image higherTuple).card*KL*
          (idealDivisorConstant ε hε*BL^ε)*(∑ a ∈ leftFamily F g,‖α (recoverLeft g a)‖^2))*
        Real.sqrt (((leftFamily F g).image higherTuple).card*KR*
          (idealDivisorConstant ε hε*BR^ε)*(∑ a ∈ rightFamily F g,‖β (recoverRight g a)‖^2)) := by
  obtain ⟨C,hC,hbound⟩ := NaturalSwapBound.natural_radial_bound_original_mass W decay
  refine ⟨C,hC,?_⟩
  intro F hF hpF g hgn hgp hLF hRF α β L hL E k S hS rL rR hrL hrR Y DL DR KL KR BL BR ε hε
    hDL hDR hY hR hKL hKR hBL hBR hEL hER hNL hNR hx hy hz
  have ht := hbound (packetScale F g L E k Y DL DR) hR F hF hpF g hgp hLF hRF α β
    (primeSubsetGenerator (sourceMaskPrime F) E) (BadFrequencySectors.keyFactor k) rL rR DL DR S Y
    KL KR BL BR ε hε hKL hKR hBL hBR hEL hER hNL hNR hDL hDR hY hx hy hz
  rw [actualSectorForm_eq_radialSwap F hF hpF g hgn hgp hLF hRF α β W L E k S hS rL rR
    hrL hrR Y DL DR hY hDL hDR,norm_mul]
  change ‖packetPrefactor F g L E DL DR‖*
    ‖NaturalSwapBound.naturalRadialSwap F hF g hLF hRF α β
      (primeSubsetGenerator (sourceMaskPrime F) E) (BadFrequencySectors.keyFactor k)
      rL rR DL DR S Y W (packetScale F g L E k Y DL DR)‖ ≤ _
  have hpref : 0 ≤ prefactorBound F g L E DL DR := by unfold prefactorBound; positivity
  exact (mul_le_mul (packetPrefactor_norm_le F g L hL E DL DR) ht (norm_nonneg _) hpref).trans_eq (by ring)

end
end Qrh.JointDetector.NaturalSectorBound

#print axioms Qrh.JointDetector.NaturalSectorBound.packetPrefactor_norm_le
#print axioms Qrh.JointDetector.NaturalSectorBound.actual_sector_bound
