/- Copyright (c) 2026 Joseph Bebel. -/
import Candidate.Local.Qrh.JointDetector.NaturalActualTail
import Candidate.Local.Qrh.JointDetector.UniformReflection

/-! Exact ordinary-ideal source dyads for the actual natural Poisson packet.
The finite frequency set, bad-output sector, and source dyad are fixed before
any residual pivot is summed. Unit ideals and arbitrary good prime powers are
retained. There is no squarefree projection or operator estimate here. -/
namespace Qrh.JointDetector.NaturalFrequencyReindex
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ActualEisensteinCubic ActualEisensteinCoordinates ConcreteTraceCRT EisensteinSchwartzPoisson
open CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open NaturalSelectedNorm NaturalSharedTables NaturalPairPackets FiveColourPoisson FiniteGaussPhase
local notation "O" => ActualEisensteinCubic.O

/-- A common ordinary-ideal source set; its definition contains no row or pivot. -/
def sourceDyad (frequencies : Finset BadFrequencySectors.NonzeroFrequency) (T : ℝ)
    (k : Oˣ × ℕ × ℕ) (j : Fin (columnDyadicLength T+1)) : Finset (Ideal O) :=
  divisorDyadicBin (selectedFrequencySources frequencies k) T j

theorem sourceDyad_subset (frequencies : Finset BadFrequencySectors.NonzeroFrequency)
    (T : ℝ) (k : Oˣ × ℕ × ℕ) (j : Fin (columnDyadicLength T+1)) :
    sourceDyad frequencies T k j ⊆ selectedFrequencySources frequencies k :=
  Finset.filter_subset _ _

theorem sourceDyad_supported (frequencies : Finset BadFrequencySectors.NonzeroFrequency)
    (T : ℝ) (k : Oˣ × ℕ × ℕ) (j : Fin (columnDyadicLength T+1))
    (I : Ideal O) (hI : I ∈ sourceDyad frequencies T k j) : Supported I :=
  selectedFrequencySources_supported frequencies k I (sourceDyad_subset frequencies T k j hI)

theorem sourceDyad_pool (frequencies : Finset BadFrequencySectors.NonzeroFrequency)
    (T : ℝ) (k : Oˣ × ℕ × ℕ) (hk : k ∈ BadFrequencySectors.boundedKeys T)
    (j : Fin (columnDyadicLength T+1)) :
    sourceDyad frequencies T k j ⊆ selectedFrequencyPool frequencies T := by
  intro I hI
  exact Finset.mem_biUnion.mpr ⟨k,hk,sourceDyad_subset frequencies T k j hI⟩

theorem source_bounds (frequencies : Finset BadFrequencySectors.NonzeroFrequency) (T : ℝ)
    (hT : ∀ h ∈ frequencies, ‖eisEmbedding h.val‖^2 ≤ T) (k : Oˣ × ℕ × ℕ)
    (I : Ideal O) (hI : I ∈ selectedFrequencySources frequencies k) :
    1 ≤ (Ideal.absNorm I : ℝ) ∧ (Ideal.absNorm I : ℝ) ≤ T := by
  refine ⟨?_,selectedFrequencySources_norm_le frequencies T hT k I hI⟩
  have hn := (selectedFrequencySources_supported frequencies k I hI).1
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hn)

/-- The output sector is paid separately; its bad norm is never inserted into
an ordinary good source. -/
theorem source_norm_le_div_sector
    (frequencies : Finset BadFrequencySectors.NonzeroFrequency) (T : ℝ)
    (hT : ∀ h ∈ frequencies, ‖eisEmbedding h.val‖^2 ≤ T) (k : Oˣ × ℕ × ℕ)
    (I : Ideal O) (hI : I ∈ selectedFrequencySources frequencies k) :
    (Ideal.absNorm I : ℝ) ≤ T/inputSectorScale k := by
  obtain ⟨H,hH,rfl⟩ := Finset.mem_image.mp hI
  apply (le_div_iff₀ (inputSectorScale_pos k)).mpr
  simpa only [inputSectorScale,mul_comm] using
    BadFrequencySectors.fiberSource_norm_le frequencies T hT k H hH

theorem sourceDyad_bounds (frequencies : Finset BadFrequencySectors.NonzeroFrequency) (T : ℝ)
    (hT : ∀ h ∈ frequencies, ‖eisEmbedding h.val‖^2 ≤ T) (k : Oˣ × ℕ × ℕ)
    (j : Fin (columnDyadicLength T+1)) (I : Ideal O) (hI : I ∈ sourceDyad frequencies T k j) :
    divisorDyadicScale j.val ≤ (Ideal.absNorm I : ℝ) ∧
      (Ideal.absNorm I : ℝ) ≤ 2*divisorDyadicScale j.val :=
  divisorDyadicBin_bounds _ T (source_bounds frequencies T hT k) j I hI

theorem sourceDyad_coordinate (frequencies : Finset BadFrequencySectors.NonzeroFrequency) (T : ℝ)
    (hT : ∀ h ∈ frequencies, ‖eisEmbedding h.val‖^2 ≤ T) (k : Oˣ × ℕ × ℕ)
    (j : Fin (columnDyadicLength T+1)) (I : Ideal O) (hI : I ∈ sourceDyad frequencies T k j) :
    (Ideal.absNorm I : ℝ)/divisorDyadicScale j.val ∈ Set.Icc (1:ℝ) 2 := by
  have hp : 0 < divisorDyadicScale j.val := lt_of_lt_of_le (by norm_num) (divisorDyadicScale_ge_one _)
  obtain ⟨hlo,hhi⟩ := sourceDyad_bounds frequencies T hT k j I hI
  exact ⟨(le_div_iff₀ hp).mpr (by simpa using hlo),(div_le_iff₀ hp).mpr hhi⟩

theorem sourceDyad_scale_le (frequencies : Finset BadFrequencySectors.NonzeroFrequency) (T : ℝ)
    (hT : ∀ h ∈ frequencies, ‖eisEmbedding h.val‖^2 ≤ T) (k : Oˣ × ℕ × ℕ)
    (j : Fin (columnDyadicLength T+1)) (hj : (sourceDyad frequencies T k j).Nonempty) :
    divisorDyadicScale j.val ≤ T/inputSectorScale k := by
  obtain ⟨I,hI⟩ := hj
  exact (sourceDyad_bounds frequencies T hT k j I hI).1.trans
    (source_norm_le_div_sector frequencies T hT k I (sourceDyad_subset frequencies T k j hI))

/-- Every original frequency appears exactly once, with every unit and both
bad valuations explicit. The source dyad includes the unit when it occurs. -/
theorem sum_by_sectors_dyads (frequencies : Finset BadFrequencySectors.NonzeroFrequency) (T : ℝ)
    (hT : ∀ h ∈ frequencies, ‖eisEmbedding h.val‖^2 ≤ T) (f : O → ℂ) :
    (∑ h ∈ frequencies, f h.val) =
      ∑ k ∈ BadFrequencySectors.boundedKeys T, ∑ j : Fin (columnDyadicLength T+1),
        ∑ I ∈ sourceDyad frequencies T k j, f (BadFrequencySectors.keyFactor k*primaryGenerator I) := by
  rw [BadFrequencySectors.sum_by_bounded_sectors frequencies T hT f]
  apply Finset.sum_congr rfl
  intro k hk
  unfold sourceDyad
  rw [← sum_divisorDyadicBins (selectedFrequencySources frequencies k) T
    (fun I => f (BadFrequencySectors.keyFactor k*primaryGenerator I))]
  unfold selectedFrequencySources
  rw [Finset.sum_image (fun I hI J hJ he => Subtype.val_injective he)]
  rfl

/-- The literal zero mode is split off before every nonzero sector; no zero
mode or bad-output sector is silently discarded. -/
theorem cutoff_sum_by_sectors_dyads (T : ℝ) (hT : 0 ≤ T) (f : O → ℂ) :
    (∑ h ∈ reflectionCutoff T, f h) = f 0+
      ∑ k ∈ BadFrequencySectors.boundedKeys T, ∑ j : Fin (columnDyadicLength T+1),
        ∑ I ∈ sourceDyad (reflectionFrequencies T) T k j,
          f (BadFrequencySectors.keyFactor k*primaryGenerator I) := by
  rw [reflectionCutoff_sum T f,
    sum_by_sectors_dyads (reflectionFrequencies T) T (reflectionFrequencies_bound T hT) f]

/-- Every ideal in the original sector, including the unit, occurs in its
unique dyad. No arithmetic restriction is added by the dyadic adapter. -/
theorem mem_unique_sourceDyad (frequencies : Finset BadFrequencySectors.NonzeroFrequency)
    (T : ℝ) (k : Oˣ × ℕ × ℕ) (I : Ideal O)
    (hI : I ∈ selectedFrequencySources frequencies k) :
    ∃! j : Fin (columnDyadicLength T+1), I ∈ sourceDyad frequencies T k j := by
  refine ⟨divisorDyadicLabel T I,?_,?_⟩
  · exact Finset.mem_filter.mpr ⟨hI,rfl⟩
  · intro j hj
    exact (Finset.mem_filter.mp hj).2.symm

/-- The original global source cap survives every sector and dyad. -/
theorem sourceDyad_cap (frequencies : Finset BadFrequencySectors.NonzeroFrequency)
    (T : ℝ) (hT : ∀ h ∈ frequencies, ‖eisEmbedding h.val‖^2 ≤ T)
    (Z P : ℝ) (hcap : T ≤ Z^P) (k : Oˣ × ℕ × ℕ)
    (j : Fin (columnDyadicLength T+1)) (I : Ideal O)
    (hI : I ∈ sourceDyad frequencies T k j) : (Ideal.absNorm I : ℝ) ≤ Z^P :=
  (source_bounds frequencies T hT k I (sourceDyad_subset frequencies T k j hI)).2.trans hcap

/-- Polynomial near cutoffs pay all output sectors and all source dyads with
one arbitrarily small ambient power, independently of rows and coefficients. -/
theorem sector_dyad_budget (P ε : ℝ) (hP : 0 ≤ P) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z T : ℝ, 1 ≤ Z → 0 < T → T ≤ Z^P →
      ((BadFrequencySectors.boundedKeys T).card : ℝ)*(columnDyadicLength T+1 : ℕ) ≤ C*Z^ε :=
  badSector_dyadic_small_power P ε hP hε

/-- The actual literal natural packet, not a squarefree substitute. -/
theorem packetTerm_sum_by_sectors_dyads
    (F : Finset ColourTuple) (hF : ∀ c ∈ F, ∀ j, Admissible (c j))
    (c d : ColourTuple) (W : 𝓢(ℝ,ℂ)) (L : ℝ) (E : Finset (SourceMaskIndex F))
    (frequencies : Finset BadFrequencySectors.NonzeroFrequency) (T : ℝ)
    (hT : ∀ h ∈ frequencies, ‖eisEmbedding h.val‖^2 ≤ T) (w : O → ℂ) :
    (∑ h ∈ frequencies, w h.val*NaturalActualTail.packetTerm F hF c d W L E h.val) =
      ∑ k ∈ BadFrequencySectors.boundedKeys T, ∑ j : Fin (columnDyadicLength T+1),
        ∑ I ∈ sourceDyad frequencies T k j,
          w (BadFrequencySectors.keyFactor k*primaryGenerator I)*
          NaturalActualTail.packetTerm F hF c d W L E
            (BadFrequencySectors.keyFactor k*primaryGenerator I) :=
  sum_by_sectors_dyads frequencies T hT
    (fun h => w h*NaturalActualTail.packetTerm F hF c d W L E h)

/-- Exact raw norm in a sector; no row-dependent frequency completion. -/
theorem sector_frequency_norm (k : Oˣ × ℕ × ℕ) (I : Ideal O) (hI : Supported I) :
    ‖eisEmbedding (BadFrequencySectors.keyFactor k*primaryGenerator I)‖^2 =
      inputSectorScale k*(Ideal.absNorm I : ℝ) := by
  simpa only [BadFrequencySectors.decode,BadFrequencySectors.rebuild,
    BadFrequencySectors.keyFactor,inputSectorScale] using
    BadFrequencySectors.decode_norm (BadFrequencySectors.rebuild k ⟨I,hI⟩)

/-- The literal unit and bad powers have exactly the sector norm used by the
common radial scale. -/
theorem keyFactor_norm (k : Oˣ × ℕ × ℕ) :
    ‖eisEmbedding (BadFrequencySectors.keyFactor k)‖^2 = inputSectorScale k := by
  have h1 : Supported (1 : Ideal O) := by
    refine ⟨one_ne_zero,?_⟩
    intro P hP
    simp only [UniqueFactorizationMonoid.normalizedFactors_one,Multiset.notMem_zero] at hP
  simpa only [primaryGenerator_one,mul_one,map_one,Nat.cast_one] using
    sector_frequency_norm k 1 h1

/-- The true radial argument has the bad-output norm as a separate scalar. -/
theorem packet_radial_argument (F : Finset ColourTuple) (c d : ColourTuple) (L : ℝ)
    (E : Finset (SourceMaskIndex F)) (k : Oˣ × ℕ × ℕ) (I : Ideal O) (hI : Supported I) :
    NaturalActualTail.packetScale F c d L E*
      ‖eisEmbedding (BadFrequencySectors.keyFactor k*primaryGenerator I)‖^2 =
      L*(inputSectorScale k*(Ideal.absNorm I : ℝ))/
        (‖eisEmbedding (primeSubsetGenerator (sourceMaskPrime F) E)‖^2*
          ‖eisEmbedding (primitiveElement F c d)‖^2) := by
  rw [sector_frequency_norm k I hI]
  unfold NaturalActualTail.packetScale
  ring

/-- The actual selected source character after freezing the output sector.
All q/b own coefficients and the reciprocity weight are retained literally. -/
theorem actual_source_factor
    (F : Finset ColourTuple) (hF : ∀ c ∈ F, ∀ j, Admissible (c j))
    (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k)))
    (frequencies : Finset BadFrequencySectors.NonzeroFrequency) (T : ℝ)
    (k : Oˣ × ℕ × ℕ) (j : Fin (columnDyadicLength T+1))
    (I : Ideal O) (hI : I ∈ sourceDyad frequencies T k j) (q : O)
    (rL rR : EisensteinEPrimaryPhase.Coord)
    (hrL : residue (primaryGenerator (leftResidual c d 0))=rL)
    (hrR : residue (primaryGenerator (rightResidual c d 0))=rR) :
    let a := leftResidual c d
    let a' := rightResidual c d
    let b := BadFrequencySectors.keyFactor k
    primitiveRow F hF c d q*star (primitiveRow F hF c d (b*primaryGenerator I)) =
      (idealRowHom q (a 0)*star (idealRowHom b (a 0)))*
      (star (idealRowHom q (a' 0))*idealRowHom b (a' 0))*
      (higherFrequencyWeight F hF (table c d) (higherTuple a) (higherTuple a') q b I*
        frozenReciprocityWeight rL rR I)*
      star (idealRowHom (primaryGenerator (a 0)) I)*idealRowHom (primaryGenerator (a' 0)) I :=
  actual_dual_frequency_factor F hF c d hc hd hcPair hdPair I
    (sourceDyad_supported frequencies T k j I hI) q (BadFrequencySectors.keyFactor k)
    rL rR hrL hrR

/-- This common weight has only table/higher/ray labels and the ordinary
source. In particular it has no free pivot. -/
def commonWeight (F : Finset ColourTuple) (hF : ∀ c ∈ F, ∀ j, Admissible (c j))
    (g : SharedTable) (v w : HigherTuple) (q b : O)
    (rL rR : EisensteinEPrimaryPhase.Coord) (I : Ideal O) : ℂ :=
  higherFrequencyWeight F hF g v w q b I*frozenReciprocityWeight rL rR I

theorem higherFeature_norm_le (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (g : SharedTable) (v w : HigherTuple) (n : O) :
    ‖higherFeature F hF g v w n‖ ≤ 1 := by
  unfold higherFeature
  exact featureBlock_norm_le _ _ _ _ _

theorem commonWeight_norm_le (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (g : SharedTable) (v w : HigherTuple)
    (q b : O) (rL rR : EisensteinEPrimaryPhase.Coord) (I : Ideal O) :
    ‖commonWeight F hF g v w q b rL rR I‖ ≤ 1 := by
  have hh : ‖higherFrequencyWeight F hF g v w q b I‖ ≤ 1 := by
    unfold higherFrequencyWeight
    rw [norm_mul,norm_star]
    exact (mul_le_mul (higherFeature_norm_le F hF g v w q)
      (higherFeature_norm_le F hF g v w (b*primaryGenerator I))
      (norm_nonneg _) (by norm_num)).trans (by norm_num)
  unfold commonWeight
  rw [norm_mul]
  exact (mul_le_mul hh (frozenReciprocityWeight_norm_le rL rR I)
    (norm_nonneg _) (by norm_num)).trans (by norm_num)

/-- Literal packet after the exact character factorization. The common
source weight and both own q/b coefficients are kept with their orientation. -/
theorem packetTerm_eq_factored_source
    (F : Finset ColourTuple) (hF : ∀ c ∈ F, ∀ j, Admissible (c j))
    (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k)))
    (W : 𝓢(ℝ,ℂ)) (L : ℝ) (E : Finset (SourceMaskIndex F))
    (k : Oˣ × ℕ × ℕ) (I : Ideal O) (hI : Supported I)
    (rL rR : EisensteinEPrimaryPhase.Coord)
    (hrL : residue (primaryGenerator (leftResidual c d 0))=rL)
    (hrR : residue (primaryGenerator (rightResidual c d 0))=rR) :
    let a := leftResidual c d
    let a' := rightResidual c d
    let b := BadFrequencySectors.keyFactor k
    let q := primeSubsetGenerator (sourceMaskPrime F) E
    NaturalActualTail.packetTerm F hF c d W L E (b*primaryGenerator I) =
      (((L:ℂ)*primitiveGauss F hF c d/(‖eisEmbedding (primitiveElement F c d)‖:ℂ))*
        ((UniqueFactorizationMonoid.moebius (NaturalActualTail.maskIdeal F E):ℂ)/
          (‖eisEmbedding q‖^2:ℝ)))*
      ((idealRowHom q (a 0)*star (idealRowHom b (a 0)))*
        (star (idealRowHom q (a' 0))*idealRowHom b (a' 0)))*
      commonWeight F hF (table c d) (higherTuple a) (higherTuple a') q b rL rR I*
      star (idealRowHom (primaryGenerator (a 0)) I)*idealRowHom (primaryGenerator (a' 0)) I*
      paperRadialFourier W (L*(inputSectorScale k*(Ideal.absNorm I:ℝ))/
        (‖eisEmbedding q‖^2*‖eisEmbedding (primitiveElement F c d)‖^2)) := by
  dsimp only
  have he := actual_dual_frequency_factor F hF c d hc hd hcPair hdPair I hI
    (primeSubsetGenerator (sourceMaskPrime F) E) (BadFrequencySectors.keyFactor k) rL rR hrL hrR
  dsimp only at he
  unfold NaturalActualTail.packetTerm
  rw [packet_radial_argument F c d L E k I hI]
  unfold NaturalActualTail.packetCoefficient
  calc
    _ = (((L:ℂ)*primitiveGauss F hF c d/(‖eisEmbedding (primitiveElement F c d)‖:ℂ))*
        ((UniqueFactorizationMonoid.moebius (NaturalActualTail.maskIdeal F E):ℂ)/
          (‖eisEmbedding (primeSubsetGenerator (sourceMaskPrime F) E)‖^2:ℝ)))*
      (primitiveRow F hF c d (primeSubsetGenerator (sourceMaskPrime F) E)*
        star (primitiveRow F hF c d (BadFrequencySectors.keyFactor k*primaryGenerator I)))*
      paperRadialFourier W (L*(inputSectorScale k*(Ideal.absNorm I:ℝ))/
        (‖eisEmbedding (primeSubsetGenerator (sourceMaskPrime F) E)‖^2*
          ‖eisEmbedding (primitiveElement F c d)‖^2)) := by ring
    _ = _ := by rw [he]; unfold commonWeight; ring

end
end Qrh.JointDetector.NaturalFrequencyReindex

#print axioms Qrh.JointDetector.NaturalFrequencyReindex.sum_by_sectors_dyads
#print axioms Qrh.JointDetector.NaturalFrequencyReindex.sourceDyad_coordinate
#print axioms Qrh.JointDetector.NaturalFrequencyReindex.sourceDyad_cap
#print axioms Qrh.JointDetector.NaturalFrequencyReindex.sector_dyad_budget
#print axioms Qrh.JointDetector.NaturalFrequencyReindex.packetTerm_sum_by_sectors_dyads
#print axioms Qrh.JointDetector.NaturalFrequencyReindex.keyFactor_norm
#print axioms Qrh.JointDetector.NaturalFrequencyReindex.commonWeight_norm_le
#print axioms Qrh.JointDetector.NaturalFrequencyReindex.packetTerm_eq_factored_source
