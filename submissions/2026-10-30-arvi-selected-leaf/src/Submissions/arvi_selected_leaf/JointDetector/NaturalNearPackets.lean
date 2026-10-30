/- Copyright (c) 2026 Joseph Bebel. -/
import Submissions.arvi_selected_leaf.JointDetector.NaturalPairPackets
import Submissions.arvi_selected_leaf.JointDetector.NaturalTupleFibres
import Submissions.arvi_selected_leaf.JointDetector.NaturalTuplePartition
import Submissions.arvi_selected_leaf.JointDetector.NaturalFrequencyReindex

/-! Literal finite near-frequency packets. The full residual radical is
the row coordinate in ONE common radial Fourier kernel. Shared table,
puncture and output-sector labels are fixed before the two free pivots. -/
namespace Qrh.JointDetector.NaturalNearPackets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ActualEisensteinCubic ActualEisensteinCoordinates ConcreteTraceCRT EisensteinSchwartzPoisson
open CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open GaussGeneratorTransport FiniteGaussPhase MixedCrossSeparation MixedGaussConversion
open RayFourExpansion QuadraticGaussRay
open NaturalSelectedNorm NaturalSharedTables NaturalPairPackets FiveColourPoisson
local notation "O" => ActualEisensteinCubic.O

def offDiagonalIdeal (g : SharedTable) : Ideal O :=
  ∏ q : Fin 5 × Fin 5, if q.1=q.2 then 1 else g q.1 q.2

def primitiveIdeal (F : Finset ColourTuple) (c d : ColourTuple) : Ideal O :=
  ∏ i : primitivePrimes F c d,i.val.val

theorem residual_support_product_left (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) :
    (∏ i ∈ tupleSupport F (leftResidual c d),i.val)=TuplePartition.radical (leftResidual c d) := by
  unfold tupleSupport TuplePartition.radical
  rw [Finset.prod_biUnion]
  · apply Finset.prod_congr rfl
    intro j hj
    exact support_product_of_dvd_colour F hF c hc j _
      (admissible_of_dvd (hF c hc j) (leftResidual_dvd hdPair j)).2.1 (leftResidual_dvd hdPair j)
  · intro j hj k hk hjk
    exact idealSupport_disjoint_of_coprime _ _ _ (leftResidual_pairwise hcPair hdPair hjk)

theorem residual_support_product_right (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) :
    (∏ i ∈ tupleSupport F (rightResidual c d),i.val)=TuplePartition.radical (rightResidual c d) := by
  unfold tupleSupport TuplePartition.radical
  rw [Finset.prod_biUnion]
  · apply Finset.prod_congr rfl
    intro j hj
    exact support_product_of_dvd_colour F hF d hd j _
      (admissible_of_dvd (hF d hd j) (rightResidual_dvd hcPair j)).2.1 (rightResidual_dvd hcPair j)
  · intro j hj k hk hjk
    exact idealSupport_disjoint_of_coprime _ _ _ (rightResidual_pairwise hcPair hdPair hjk)

theorem offDiagonal_support_product (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) :
    (∏ i ∈ offDiagonalPrimes F (table c d),i.val)=offDiagonalIdeal (table c d) := by
  unfold offDiagonalPrimes offDiagonalIdeal
  rw [Finset.prod_biUnion]
  · apply Finset.prod_congr rfl
    rintro ⟨j,k⟩ hjk
    by_cases he : j=k
    · simp [he]
    · simp only [he,ite_false]
      exact support_product_of_dvd_colour F hF c hc j _
        (table_admissible (hF c hc) j k).2.1 (gcd_dvd_left _ _)
  · intro q hq r hr hqr
    dsimp only [Function.onFun]
    split_ifs <;> first
      | exact Finset.disjoint_empty_left _
      | exact Finset.disjoint_empty_right _
      | exact idealSupport_disjoint_of_coprime _ _ _ (table_pairwise hcPair hdPair hqr)

/-- The exact primitive conductor after fixing all25 shared cells. This is
the scalar identity needed by the common FULL-radical Mellin coordinates. -/
theorem primitiveIdeal_factor (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) :
    primitiveIdeal F c d=offDiagonalIdeal (table c d)*
      TuplePartition.radical (leftResidual c d)*TuplePartition.radical (rightResidual c d) := by
  have hset : primitivePrimes F c d=tupleSupport F (leftResidual c d) ∪
      (tupleSupport F (rightResidual c d) ∪ offDiagonalPrimes F (table c d)) := by
    ext i
    rw [Finset.mem_union,Finset.mem_union,
      tupleSupport_leftResidual_code F hF c d hc hd hcPair hdPair,
      tupleSupport_rightResidual_code F hF c d hc hd hcPair hdPair,
      ← sharedPrimitivePrimes_eq_table F hF c d hc hd hcPair hdPair]
    simp only [primitivePrimes,sharedPrimitivePrimes,Finset.mem_filter,Finset.mem_univ,true_and]
    omega
  have hLR : Disjoint (tupleSupport F (leftResidual c d)) (tupleSupport F (rightResidual c d)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hl := (tupleSupport_leftResidual_code F hF c d hc hd hcPair hdPair i).mp hi
    have hr := (tupleSupport_rightResidual_code F hF c d hc hd hcPair hdPair i).mp hj
    omega
  have hLT : Disjoint (tupleSupport F (leftResidual c d)) (offDiagonalPrimes F (table c d)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hl := (tupleSupport_leftResidual_code F hF c d hc hd hcPair hdPair i).mp hi
    rw [← sharedPrimitivePrimes_eq_table F hF c d hc hd hcPair hdPair] at hj
    have ht := (Finset.mem_filter.mp hj).2
    omega
  have hRT : Disjoint (tupleSupport F (rightResidual c d)) (offDiagonalPrimes F (table c d)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hr := (tupleSupport_rightResidual_code F hF c d hc hd hcPair hdPair i).mp hi
    rw [← sharedPrimitivePrimes_eq_table F hF c d hc hd hcPair hdPair] at hj
    have ht := (Finset.mem_filter.mp hj).2
    omega
  unfold primitiveIdeal
  rw [Finset.prod_coe_sort (primitivePrimes F c d) (fun i : PrimeIndex F => i.val),hset,
    Finset.prod_union (Finset.disjoint_union_right.mpr ⟨hLR,hLT⟩),Finset.prod_union hRT,
    residual_support_product_left F hF c d hc hd hcPair hdPair,
    residual_support_product_right F hF c d hc hd hcPair hdPair,
    offDiagonal_support_product F hF c d hc hd hcPair hdPair]
  ring

theorem offDiagonalIdeal_ne_zero (g : SharedTable) (hg : ∀ j k,g j k ≠ 0) :
    offDiagonalIdeal g ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  rintro ⟨j,k⟩ hjk
  dsimp only
  split_ifs
  · exact one_ne_zero
  · exact hg j k

theorem primitiveElement_norm_sq_factor (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) :
    ‖eisEmbedding (primitiveElement F c d)‖^2=
      (Ideal.absNorm (offDiagonalIdeal (table c d)):ℝ)*
      (Ideal.absNorm (TuplePartition.radical (leftResidual c d)):ℝ)*
      (Ideal.absNorm (TuplePartition.radical (rightResidual c d)):ℝ) := by
  have hn : ‖eisEmbedding (primitiveElement F c d)‖^2=(Ideal.absNorm (primitiveIdeal F c d):ℝ) := by
    simp only [primitiveElement,map_prod,norm_prod]
    rw [← Finset.prod_pow]
    simp only [eisEmbedding_norm_sq_eq_absNorm_span,primitivePrimary_span F hF,
      primitiveIdeal,map_prod,Nat.cast_prod]
  rw [hn,primitiveIdeal_factor F hF c d hc hd hcPair hdPair]
  simp only [map_mul,Nat.cast_mul]

/-- ONE radial ratio for all higher fibres and both free pivots. Full
residual radical coordinates enter x and y, and the same source shell Y
enters z. There is no independently varying kernel for each higher pair. -/
theorem actual_radial_ratio (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k)))
    (q b : O) (H : Ideal O) (hH : Supported H) (L Y DL DR : ℝ)
    (hY : 0 < Y) (hDL : 0 < DL) (hDR : 0 < DR) :
    L*‖eisEmbedding (b*primaryGenerator H)‖^2/
      (‖eisEmbedding q‖^2*‖eisEmbedding (primitiveElement F c d)‖^2) =
    (L*‖eisEmbedding b‖^2*Y/
      (‖eisEmbedding q‖^2*(Ideal.absNorm (offDiagonalIdeal (table c d)):ℝ)*DL*DR))*
      ((Ideal.absNorm H:ℝ)/Y)/
        (((Ideal.absNorm (TuplePartition.radical (leftResidual c d)):ℝ)/DL)*
          ((Ideal.absNorm (TuplePartition.radical (rightResidual c d)):ℝ)/DR)) := by
  rw [map_mul,norm_mul,mul_pow,primaryGenerator_norm_sq H (supported_primaryGenerator_ne_zero H hH),
    primitiveElement_norm_sq_factor F hF c d hc hd hcPair hdPair]
  field_simp
  <;> ring

/-- Exact separation of the conductor prefactor into own contractive row
weights. This fixes the mass normalization used by the finite swap. -/
theorem radical_prefactor (T RA RB DL DR : ℝ) (hT : 0 < T) (hRA : 0 < RA) (hRB : 0 < RB)
    (hDL : 0 < DL) (hDR : 0 < DR) :
    (Real.sqrt (T*RA*RB))⁻¹=(Real.sqrt (T*DL*DR))⁻¹*
      Real.sqrt (DL/RA)*Real.sqrt (DR/RB) := by
  rw [Real.sqrt_mul (mul_nonneg hT.le hRA.le),Real.sqrt_mul hT.le,
    Real.sqrt_mul (mul_nonneg hT.le hDL.le),Real.sqrt_mul hT.le,
    Real.sqrt_div hDL.le,Real.sqrt_div hDR.le]
  have hTs : Real.sqrt T ≠ 0 := (Real.sqrt_pos.mpr hT).ne'
  have hRAs : Real.sqrt RA ≠ 0 := (Real.sqrt_pos.mpr hRA).ne'
  have hRBs : Real.sqrt RB ≠ 0 := (Real.sqrt_pos.mpr hRB).ne'
  have hDLs : Real.sqrt DL ≠ 0 := (Real.sqrt_pos.mpr hDL).ne'
  have hDRs : Real.sqrt DR ≠ 0 := (Real.sqrt_pos.mpr hDR).ne'
  field_simp

theorem radical_weight_le_one (D R : ℝ) (hD : 0 ≤ D) (hR : 0 < R) (hDR : D ≤ R) :
    Real.sqrt (D/R) ≤ 1 := by
  apply (Real.sqrt_le_iff).mpr
  exact ⟨zero_le_one,by simpa using (div_le_one hR).mpr hDR⟩

theorem gaussWithExponent_norm_le (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (e : PrimeIndex F → ℕ)
    (S : Finset (PrimeIndex F)) (he : ∀ i ∈ S,0 < e i ∧ e i < 6) :
    ‖gaussWithExponent F hF e S‖ ≤ 1 := by
  let e' : PrimeIndex F → ℕ := fun i => if i ∈ S then e i else 1
  have he' (i : PrimeIndex F) : 0 < e' i ∧ e' i < 6 := by
    by_cases hi : i ∈ S
    · simpa only [e',ite_eq_left hi] using he i hi
    · simp [e',hi]
  letI := admissiblePoolMaximal (colourIdeals F) (colourIdeals_admissible F hF)
  unfold gaussWithExponent
  rw [unaryGauss_congr_on (poolPrimary (colourIdeals F))
    (poolPrimary_ne_zero (colourIdeals F) (colourIdeals_admissible F hF))
    (poolPrimary_good (colourIdeals F) (colourIdeals_admissible F hF)) e e' S
    (fun i hi => by simp only [e',ite_eq_left hi])]
  exact varyingUnaryGauss_norm_le _ _ _
    (poolPrimary_odd (colourIdeals F) (colourIdeals_admissible F hF)) e'
    (fun i => (he' i).1.ne') (fun i => (he' i).2) S

theorem gaussBlockOnPool_norm_le (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) (S : Finset (PrimeIndex F))
    (hS : S ⊆ primitivePrimes F c d) : ‖gaussBlockOnPool F hF c d S‖ ≤ 1 :=
  gaussWithExponent_norm_le F hF _ S (fun i hi => quotientExponent_range
    (colourExponent_range F c hcPair i) (colourExponent_range F d hdPair i)
    (Finset.mem_filter.mp (hS hi)).2)

theorem crossBlockOnPool_norm_le (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (S T : Finset (PrimeIndex F)) :
    ‖crossBlockOnPool F hF c d S T‖ ≤ 1 := by
  letI := admissiblePoolMaximal (colourIdeals F) (colourIdeals_admissible F hF)
  exact crossBlock_norm_le _ _ _ S T

theorem leftUnaryFactor_norm_actual (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) :
    ‖leftUnaryFactor F hF (table c d) (leftResidual c d)‖ ≤ 1 := by
  rw [leftUnaryFactor_actual F hF c d hc hd hcPair hdPair,norm_mul,norm_mul]
  have hS : pivotLeftPrimes F c d ⊆ primitivePrimes F c d := by
    intro i hi
    have h := (Finset.mem_filter.mp hi).2
    simp only [primitivePrimes,Finset.mem_filter,Finset.mem_univ,true_and]
    omega
  exact mul_le_one₀ (mul_le_one₀ (gaussBlockOnPool_norm_le F hF c d hcPair hdPair _ hS)
    (norm_nonneg _) (crossBlockOnPool_norm_le F hF c d _ _))
    (norm_nonneg _) (crossBlockOnPool_norm_le F hF c d _ _)

theorem rightUnaryFactor_norm_actual (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) :
    ‖rightUnaryFactor F hF (table c d) (rightResidual c d)‖ ≤ 1 := by
  rw [rightUnaryFactor_actual F hF c d hc hd hcPair hdPair,norm_mul,norm_mul]
  have hS : pivotRightPrimes F c d ⊆ primitivePrimes F c d := by
    intro i hi
    have h := (Finset.mem_filter.mp hi).2
    simp only [primitivePrimes,Finset.mem_filter,Finset.mem_univ,true_and]
    omega
  exact mul_le_one₀ (mul_le_one₀ (gaussBlockOnPool_norm_le F hF c d hcPair hdPair _ hS)
    (norm_nonneg _) (crossBlockOnPool_norm_le F hF c d _ _))
    (norm_nonneg _) (crossBlockOnPool_norm_le F hF c d _ _)

theorem higherAsTuple_pairwise (a : ColourTuple)
    (ha : Pairwise (fun j k => IsCoprime (a j) (a k))) :
    Pairwise (fun j k => IsCoprime (higherAsTuple (higherTuple a) j)
      (higherAsTuple (higherTuple a) k)) := by
  intro j k hjk
  have he (l : Fin 5) (hl : l ≠ 0) : higherAsTuple (higherTuple a) l=a l := by
    cases l using Fin.cases with
    | zero => exact (hl rfl).elim
    | succ l => rfl
  by_cases hj : j=0
  · subst j
    exact isCoprime_one_left
  · by_cases hk : k=0
    · subst k
      exact isCoprime_one_right
    · rw [he j hj,he k hk]
      exact ha hjk

theorem tableExponent_range (F : Finset ColourTuple) (g : SharedTable)
    (hgp : Pairwise (fun p q : Fin 5 × Fin 5 => IsCoprime (g p.1 p.2) (g q.1 q.2)))
    (i : PrimeIndex F) (hi : i ∈ offDiagonalPrimes F g) :
    0 < tableExponent F g i ∧ tableExponent F g i < 6 := by
  obtain ⟨⟨j,k⟩,hq,hi⟩ := Finset.mem_biUnion.mp hi
  by_cases hjk : j=k
  · simpa [hjk] using hi
  · simp only [hjk,ite_false] at hi
    unfold tableExponent
    rw [tableColourCode_at F g hgp _ i (j,k) hi,tableColourCode_at F g hgp _ i (j,k) hi]
    dsimp only
    apply quotientExponent_range (by omega) (by omega)
    have hn : j.val ≠ k.val := fun he => hjk (Fin.ext he)
    omega

theorem higherPrimitiveExponent_range (F : Finset ColourTuple) (g : SharedTable)
    (hgp : Pairwise (fun p q : Fin 5 × Fin 5 => IsCoprime (g p.1 p.2) (g q.1 q.2)))
    (v w : HigherTuple)
    (hv : Pairwise (fun j k => IsCoprime (higherAsTuple v j) (higherAsTuple v k)))
    (hw : Pairwise (fun j k => IsCoprime (higherAsTuple w j) (higherAsTuple w k)))
    (i : PrimeIndex F) (hi : i ∈ higherPrimes F v ∪ (higherPrimes F w ∪ offDiagonalPrimes F g)) :
    0 < higherPrimitiveExponent F g v w i ∧ higherPrimitiveExponent F g v w i < 6 := by
  unfold higherPrimitiveExponent
  by_cases hvi : i ∈ higherPrimes F v
  · rw [ite_eq_left hvi]
    exact ⟨colourExponent_positive F _ hv i (by rwa [higherAsTuple_support]),colourExponent_range F _ hv i⟩
  · rw [ite_eq_right hvi]
    by_cases hwi : i ∈ higherPrimes F w
    · rw [ite_eq_left hwi]
      have hpos := colourExponent_positive F _ hw i (by rwa [higherAsTuple_support])
      have hlt := colourExponent_range F _ hw i
      omega
    · rw [ite_eq_right hwi]
      exact tableExponent_range F g hgp i ((Finset.mem_union.mp ((Finset.mem_union.mp hi).resolve_left hvi)).resolve_left hwi)

theorem quadraticRayPair_norm_le_two (a b : EisensteinEPrimaryPhase.Coord) :
    ‖quadraticRayPair a b‖ ≤ 2 := by
  rw [quadraticRayPair,div_eq_mul_inv,mul_inv,norm_mul,norm_mul]
  have h1 := (quadraticRayValue_bounds (EisensteinEPrimaryPhase.mul a b)).1
  have h2 := (quadraticRayValue_bounds a).2
  have h3 := (quadraticRayValue_bounds b).2
  have h23 := mul_le_one₀ h2 (norm_nonneg _) h3
  exact (mul_le_mul h1 h23 (by positivity) (by norm_num : (0:ℝ) ≤ 2)).trans_eq (by norm_num)

theorem higherGaussFactor_norm_le_eight (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (g : SharedTable)
    (hgp : Pairwise (fun p q : Fin 5 × Fin 5 => IsCoprime (g p.1 p.2) (g q.1 q.2)))
    (v w : HigherTuple)
    (hv : Pairwise (fun j k => IsCoprime (higherAsTuple v j) (higherAsTuple v k)))
    (hw : Pairwise (fun j k => IsCoprime (higherAsTuple w j) (higherAsTuple w k)))
    (rA rB : EisensteinEPrimaryPhase.Coord) : ‖higherGaussFactor F hF g v w rA rB‖ ≤ 8 := by
  unfold higherGaussFactor
  dsimp only
  simp only [norm_mul]
  have h0 := gaussWithExponent_norm_le F hF _ _ (higherPrimitiveExponent_range F g hgp v w hv hw)
  have h1 := quadraticRayPair_norm_le_two rA rB
  have h2 := quadraticRayPair_norm_le_two rA (blockRay F (higherPrimes F w))
  have h3 := quadraticRayPair_norm_le_two rB (blockRay F (higherPrimes F v))
  have h01 := mul_le_mul h0 h1 (norm_nonneg _) zero_le_one
  have h012 := mul_le_mul h01 h2 (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1*2)
  exact (mul_le_mul h012 h3 (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1*2*2)).trans_eq (by norm_num)

theorem higherFeature_norm_le_one (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (g : SharedTable) (v w : HigherTuple) (n : O) :
    ‖higherFeature F hF g v w n‖ ≤ 1 := featureBlock_norm_le _ _ _ _ n

theorem higherFrequencyWeight_norm_le_one (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (g : SharedTable) (v w : HigherTuple)
    (q b : O) (H : Ideal O) : ‖higherFrequencyWeight F hF g v w q b H‖ ≤ 1 := by
  rw [higherFrequencyWeight,norm_mul,norm_star]
  exact mul_le_one₀ (higherFeature_norm_le_one F hF g v w q) (norm_nonneg _)
    (higherFeature_norm_le_one F hF g v w _)

def higherWord (F : Finset ColourTuple) (w : HigherTuple) : Ideal O :=
  ∏ i ∈ higherPrimes F w,i.val^(colourExponent F (higherAsTuple w) i-1)

def bareHigherModulation (F : Finset ColourTuple) (u : O) (w : HigherTuple) : ℂ :=
  idealRowHom u (higherWord F w)

def higherCrossMask (u : O) (w : HigherTuple) : ℂ :=
  if ∀ j,IsCoprime (Ideal.span {u}) (w j) then 1 else 0

/-- Both natural cross-colour selectors are retained as independent
pivot/higher modulations before Cauchy. No entrywise operator monotonicity. -/
def higherModulation (F : Finset ColourTuple) (u : O) (w : HigherTuple) : ℂ :=
  higherCrossMask u w*bareHigherModulation F u w

def higherPairMask (v w : HigherTuple) : ℂ :=
  if ∀ j k,IsCoprime (v j) (w k) then 1 else 0

theorem higherModulation_norm_le_one (F : Finset ColourTuple) (u : O) (w : HigherTuple) :
    ‖higherModulation F u w‖ ≤ 1 := by
  unfold higherModulation higherCrossMask bareHigherModulation
  split_ifs
  · simpa using idealRowHom_norm u (higherWord F w)
  · simp

theorem higherPairMask_norm_le_one (v w : HigherTuple) : ‖higherPairMask v w‖ ≤ 1 := by
  unfold higherPairMask
  split_ifs <;> norm_num

theorem higherPhase_eq_bareModulation (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c : ColourTuple) (hc : c ∈ F) (j : Fin 5)
    (I : Ideal O) (hI : Squarefree I) (hdiv : I ∣ c j) (w : HigherTuple) :
    higherPhaseOnPool F hF (idealSupport (colourIdeals F) I) (higherPrimes F w)
      (colourExponent F (higherAsTuple w))=bareHigherModulation F (primaryGenerator I) w := by
  letI := admissiblePoolMaximal (colourIdeals F) (colourIdeals_admissible F hF)
  unfold higherPhaseOnPool bareHigherModulation higherWord
  rw [higherCrossPhase_eq_idealRowHom]
  simp_rw [poolPrimary_span (colourIdeals F) (colourIdeals_admissible F hF)]
  rw [primary_product_of_dvd_colour F hF c hc j I hI hdiv]

theorem actualGauss_as_modulations (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k)))
    (rL rR : EisensteinEPrimaryPhase.Coord)
    (hrL : residue (primaryGenerator (leftResidual c d 0))=rL)
    (hrR : residue (primaryGenerator (rightResidual c d 0))=rR) :
    let a := leftResidual c d
    let b := rightResidual c d
    primitiveGauss F hF c d=leftUnaryFactor F hF (table c d) a*
      rightUnaryFactor F hF (table c d) b*
      higherGaussFactor F hF (table c d) (higherTuple a) (higherTuple b) rL rR*
      star (bareHigherModulation F (primaryGenerator (a 0)) (higherTuple b))*
        bareHigherModulation F (primaryGenerator (b 0)) (higherTuple a) := by
  rw [actual_primitive_gauss_independent F hF c d hc hd hcPair hdPair]
  dsimp only
  rw [blockRay_leftResidual F hF c d hc hd hcPair hdPair,
    blockRay_rightResidual F hF c d hc hd hcPair hdPair,hrL,hrR,
    higherPhase_eq_bareModulation F hF c hc 0 _
      (admissible_of_dvd (hF c hc 0) (leftResidual_dvd hdPair 0)).2.1 (leftResidual_dvd hdPair 0),
    higherPhase_eq_bareModulation F hF d hd 0 _
      (admissible_of_dvd (hF d hd 0) (rightResidual_dvd hcPair 0)).2.1 (rightResidual_dvd hcPair 0)]

def leftOwnFactor (F : Finset ColourTuple) (hF : ∀ c ∈ F, ∀ j, Admissible (c j))
    (g : SharedTable) (a : ColourTuple) (q b : O) : ℂ :=
  leftUnaryFactor F hF g a*idealRowHom q (a 0)*star (idealRowHom b (a 0))

def rightOwnFactor (F : Finset ColourTuple) (hF : ∀ c ∈ F, ∀ j, Admissible (c j))
    (g : SharedTable) (a : ColourTuple) (q b : O) : ℂ :=
  rightUnaryFactor F hF g a*star (idealRowHom q (a 0))*idealRowHom b (a 0)

theorem leftOwnFactor_norm_actual (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) (q b : O) :
    ‖leftOwnFactor F hF (table c d) (leftResidual c d) q b‖ ≤ 1 := by
  rw [leftOwnFactor,norm_mul,norm_mul,norm_star]
  exact mul_le_one₀ (mul_le_one₀ (leftUnaryFactor_norm_actual F hF c d hc hd hcPair hdPair)
    (norm_nonneg _) (idealRowHom_norm q _)) (norm_nonneg _) (idealRowHom_norm b _)

theorem rightOwnFactor_norm_actual (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k))) (q b : O) :
    ‖rightOwnFactor F hF (table c d) (rightResidual c d) q b‖ ≤ 1 := by
  rw [rightOwnFactor,norm_mul,norm_mul,norm_star]
  exact mul_le_one₀ (mul_le_one₀ (rightUnaryFactor_norm_actual F hF c d hc hd hcPair hdPair)
    (norm_nonneg _) (idealRowHom_norm q _)) (norm_nonneg _) (idealRowHom_norm b _)

/-- Full literal packet coefficient after actual Γ and ordinary-source
transport. Every factor has the own/higher/source dependence used by swap. -/
theorem packetTerm_eq_independent_factors
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
      (((L:ℂ)*(UniqueFactorizationMonoid.moebius (NaturalActualTail.maskIdeal F E):ℂ))/
        ((‖eisEmbedding q‖^2:ℝ)*(‖eisEmbedding (primitiveElement F c d)‖:ℂ)))*
      leftOwnFactor F hF (table c d) a q b*rightOwnFactor F hF (table c d) a' q b*
      higherGaussFactor F hF (table c d) (higherTuple a) (higherTuple a') rL rR*
      star (bareHigherModulation F (primaryGenerator (a 0)) (higherTuple a'))*
        bareHigherModulation F (primaryGenerator (a' 0)) (higherTuple a)*
      NaturalFrequencyReindex.commonWeight F hF (table c d) (higherTuple a) (higherTuple a') q b rL rR I*
      star (idealRowHom (primaryGenerator (a 0)) I)*idealRowHom (primaryGenerator (a' 0)) I*
      paperRadialFourier W (L*(inputSectorScale k*(Ideal.absNorm I:ℝ))/
        (‖eisEmbedding q‖^2*‖eisEmbedding (primitiveElement F c d)‖^2)) := by
  dsimp only
  rw [NaturalFrequencyReindex.packetTerm_eq_factored_source F hF c d hc hd hcPair hdPair W L E k I hI rL rR hrL hrR]
  rw [actualGauss_as_modulations F hF c d hc hd hcPair hdPair rL rR hrL hrR]
  unfold leftOwnFactor rightOwnFactor
  ring

def radicalNorm (a : ColourTuple) : ℝ := (Ideal.absNorm (TuplePartition.radical a):ℝ)
def radicalWeight (D : ℝ) (a : ColourTuple) : ℂ := Real.sqrt (D/radicalNorm a)
def radicalCoordinate (D : ℝ) (a : ColourTuple) : ℝ := radicalNorm a/D

def fibreTuple (G : Finset ColourTuple) (hG : ∀ a ∈ G,∀ j,Admissible (a j))
    (u : ElementFibre G) : ColourTuple := ((tupleElementFibreEquiv G hG).symm u).val

theorem fibreTuple_mem (G : Finset ColourTuple) (hG : ∀ a ∈ G,∀ j,Admissible (a j))
    (u : ElementFibre G) : fibreTuple G hG u ∈ G := ((tupleElementFibreEquiv G hG).symm u).property

theorem fibreTuple_higher (G : Finset ColourTuple) (hG : ∀ a ∈ G,∀ j,Admissible (a j))
    (u : ElementFibre G) : higherTuple (fibreTuple G hG u)=u.1.val := by
  have he := tupleElementFibreEquiv_higher G hG ((tupleElementFibreEquiv G hG).symm u)
  simpa only [fibreTuple,Equiv.apply_symm_apply] using he.symm

theorem fibreTuple_pivot (G : Finset ColourTuple) (hG : ∀ a ∈ G,∀ j,Admissible (a j))
    (u : ElementFibre G) : primaryGenerator (fibreTuple G hG u 0)=u.2.val := by
  have he := tupleElementFibreEquiv_pivot G hG ((tupleElementFibreEquiv G hG).symm u)
  change primaryGenerator (((tupleElementFibreEquiv G hG).symm u).val 0)=u.2.val
  exact he.symm.trans (congrArg (fun v : ElementFibre G => v.2.val)
    ((tupleElementFibreEquiv G hG).apply_symm_apply u))

theorem fibreTuple_pivot_span (G : Finset ColourTuple) (hG : ∀ a ∈ G,∀ j,Admissible (a j))
    (u : ElementFibre G) : Ideal.span {u.2.val}=fibreTuple G hG u 0 := by
  rw [← fibreTuple_pivot G hG u]
  exact (primaryGenerator_spec _ (primaryGenerator_admissible _ (hG _ (fibreTuple_mem G hG u) 0))).1

abbrev leftRows (F : Finset ColourTuple) (g : SharedTable) (v : (leftFamily F g).image higherTuple) : Finset O :=
  (pivotFamily (leftFamily F g) v.val).image primaryGenerator
abbrev rightRows (F : Finset ColourTuple) (g : SharedTable) (w : (rightFamily F g).image higherTuple) : Finset O :=
  (pivotFamily (rightFamily F g) w.val).image primaryGenerator

def leftPacketArray (F : Finset ColourTuple) (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (g : SharedTable) (hLF : ∀ a ∈ leftFamily F g,∀ j,Admissible (a j))
    (α : ColourTuple → ℂ) (q b : O) (DL : ℝ) (u : ElementFibre (leftFamily F g)) : ℂ :=
  let a := fibreTuple (leftFamily F g) hLF u
  α (recoverLeft g a)*leftOwnFactor F hF g a q b*radicalWeight DL a

def rightPacketArray (F : Finset ColourTuple) (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (g : SharedTable) (hRF : ∀ a ∈ rightFamily F g,∀ j,Admissible (a j))
    (β : ColourTuple → ℂ) (q b : O) (DR : ℝ) (u : ElementFibre (rightFamily F g)) : ℂ :=
  let a := fibreTuple (rightFamily F g) hRF u
  β (recoverRight g a)*rightOwnFactor F hF g a q b*radicalWeight DR a

def leftPacketCoordinate (F : Finset ColourTuple) (g : SharedTable)
    (hLF : ∀ a ∈ leftFamily F g,∀ j,Admissible (a j)) (DL : ℝ)
    (u : ElementFibre (leftFamily F g)) : ℝ := radicalCoordinate DL (fibreTuple (leftFamily F g) hLF u)
def rightPacketCoordinate (F : Finset ColourTuple) (g : SharedTable)
    (hRF : ∀ a ∈ rightFamily F g,∀ j,Admissible (a j)) (DR : ℝ)
    (u : ElementFibre (rightFamily F g)) : ℝ := radicalCoordinate DR (fibreTuple (rightFamily F g) hRF u)

def packetHigherKernel (F : Finset ColourTuple) (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (g : SharedTable) (rL rR : EisensteinEPrimaryPhase.Coord)
    (v : (leftFamily F g).image higherTuple) (w : (rightFamily F g).image higherTuple) : ℂ :=
  (higherGaussFactor F hF g v.val w.val rL rR/8)*higherPairMask v.val w.val

def packetWeight (F : Finset ColourTuple) (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (g : SharedTable) (q b : O) (rL rR : EisensteinEPrimaryPhase.Coord) (S : Finset (Ideal O))
    (v : (leftFamily F g).image higherTuple) (w : (rightFamily F g).image higherTuple) (I : S) : ℂ :=
  NaturalFrequencyReindex.commonWeight F hF g v.val w.val q b rL rR I.val

def packetScale (F : Finset ColourTuple) (g : SharedTable)
    (L : ℝ) (E : Finset (SourceMaskIndex F)) (k : Oˣ × ℕ × ℕ) (Y DL DR : ℝ) : ℝ :=
  L*inputSectorScale k*Y/(‖eisEmbedding (primeSubsetGenerator (sourceMaskPrime F) E)‖^2*
    (Ideal.absNorm (offDiagonalIdeal g):ℝ)*DL*DR)

def packetPrefactor (F : Finset ColourTuple) (g : SharedTable)
    (L : ℝ) (E : Finset (SourceMaskIndex F)) (DL DR : ℝ) : ℂ :=
  8*(L:ℂ)*(UniqueFactorizationMonoid.moebius (NaturalActualTail.maskIdeal F E):ℂ)/
    ((‖eisEmbedding (primeSubsetGenerator (sourceMaskPrime F) E)‖^2:ℝ)*
      (Real.sqrt ((Ideal.absNorm (offDiagonalIdeal g):ℝ)*DL*DR):ℂ))

def actualSectorForm (F : Finset ColourTuple) (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (g : SharedTable) (α β : ColourTuple → ℂ) (W : 𝓢(ℝ,ℂ)) (L : ℝ)
    (E : Finset (SourceMaskIndex F)) (k : Oˣ × ℕ × ℕ) (S : Finset (Ideal O)) : ℂ :=
  ∑ r ∈ residualFibre F g, ∑ I : S,
    α (recoverLeft g r.1)*β (recoverRight g r.2)*
      NaturalActualTail.packetTerm F hF (recoverLeft g r.1) (recoverRight g r.2) W L E
        (BadFrequencySectors.keyFactor k*primaryGenerator I.val)

/-- Pointwise literal packet with the common full-radical Mellin scale and
the exact contractive row normalization. This is an identity, with no norm
or packet assumption. -/
theorem packetTerm_normalized
    (F : Finset ColourTuple) (hF : ∀ c ∈ F, ∀ j, Admissible (c j))
    (c d : ColourTuple) (hc : c ∈ F) (hd : d ∈ F)
    (hcPair : Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hdPair : Pairwise (fun j k => IsCoprime (d j) (d k)))
    (W : 𝓢(ℝ,ℂ)) (L : ℝ) (E : Finset (SourceMaskIndex F))
    (k : Oˣ × ℕ × ℕ) (I : Ideal O) (hI : Supported I)
    (rL rR : EisensteinEPrimaryPhase.Coord)
    (hrL : residue (primaryGenerator (leftResidual c d 0))=rL)
    (hrR : residue (primaryGenerator (rightResidual c d 0))=rR)
    (Y DL DR : ℝ) (hY : 0 < Y) (hDL : 0 < DL) (hDR : 0 < DR) :
    let a := leftResidual c d
    let a' := rightResidual c d
    let b := BadFrequencySectors.keyFactor k
    let q := primeSubsetGenerator (sourceMaskPrime F) E
    NaturalActualTail.packetTerm F hF c d W L E (b*primaryGenerator I) =
      packetPrefactor F (table c d) L E DL DR*
      (leftOwnFactor F hF (table c d) a q b*radicalWeight DL a)*
      (rightOwnFactor F hF (table c d) a' q b*radicalWeight DR a')*
      (higherGaussFactor F hF (table c d) (higherTuple a) (higherTuple a') rL rR/8)*
      star (bareHigherModulation F (primaryGenerator (a 0)) (higherTuple a'))*
        bareHigherModulation F (primaryGenerator (a' 0)) (higherTuple a)*
      NaturalFrequencyReindex.commonWeight F hF (table c d) (higherTuple a) (higherTuple a') q b rL rR I*
      star (idealRowHom (primaryGenerator (a 0)) I)*idealRowHom (primaryGenerator (a' 0)) I*
      paperRadialFourier W (packetScale F (table c d) L E k Y DL DR*((Ideal.absNorm I:ℝ)/Y)/
        (radicalCoordinate DL a*radicalCoordinate DR a')) := by
  dsimp only
  have hT : 0 < (Ideal.absNorm (offDiagonalIdeal (table c d)):ℝ) :=
    CenteredExceptionalCount.norm_pos (offDiagonalIdeal_ne_zero _ (fun j k => (table_admissible (hF c hc) j k).1))
  have hLA := (residuals_admissible (hF c hc) (hF d hd) hcPair hdPair).1
  have hRA := (residuals_admissible (hF c hc) (hF d hd) hcPair hdPair).2
  have hradL : 0 < radicalNorm (leftResidual c d) :=
    CenteredExceptionalCount.norm_pos (TuplePartition.radical_ne_zero _ hLA)
  have hradR : 0 < radicalNorm (rightResidual c d) :=
    CenteredExceptionalCount.norm_pos (TuplePartition.radical_ne_zero _ hRA)
  have hnorm : ‖eisEmbedding (primitiveElement F c d)‖=
      Real.sqrt ((Ideal.absNorm (offDiagonalIdeal (table c d)):ℝ)*
        radicalNorm (leftResidual c d)*radicalNorm (rightResidual c d)) := by
    unfold radicalNorm
    rw [← primitiveElement_norm_sq_factor F hF c d hc hd hcPair hdPair,Real.sqrt_sq (norm_nonneg _)]
  have hpf := radical_prefactor _ _ _ DL DR hT hradL hradR hDL hDR
  have hpc : (Real.sqrt ((Ideal.absNorm (offDiagonalIdeal (table c d)):ℝ)*
      radicalNorm (leftResidual c d)*radicalNorm (rightResidual c d)):ℂ)⁻¹=
      (Real.sqrt ((Ideal.absNorm (offDiagonalIdeal (table c d)):ℝ)*DL*DR):ℂ)⁻¹*
        (Real.sqrt (DL/radicalNorm (leftResidual c d)):ℂ)*
        (Real.sqrt (DR/radicalNorm (rightResidual c d)):ℂ) := by exact_mod_cast hpf
  have harg := actual_radial_ratio F hF c d hc hd hcPair hdPair
    (primeSubsetGenerator (sourceMaskPrime F) E) (BadFrequencySectors.keyFactor k) I hI L Y DL DR hY hDL hDR
  rw [map_mul,norm_mul,mul_pow,primaryGenerator_norm_sq I (supported_primaryGenerator_ne_zero I hI),
    NaturalFrequencyReindex.keyFactor_norm] at harg
  rw [packetTerm_eq_independent_factors F hF c d hc hd hcPair hdPair W L E k I hI rL rR hrL hrR]
  rw [harg]
  unfold packetPrefactor packetScale radicalWeight radicalCoordinate
  simp only [div_eq_mul_inv,mul_inv,hnorm,hpc]
  unfold radicalNorm
  ring

theorem residualFibre_sum_eq_elementFibres {M : Type*} [AddCommMonoid M]
    (F : Finset ColourTuple) (g : SharedTable)
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hgn : ∀ j k,g j k ≠ 0)
    (hgp : Pairwise (fun p q : Fin 5 × Fin 5 => IsCoprime (g p.1 p.2) (g q.1 q.2)))
    (hLF : ∀ a ∈ leftFamily F g,∀ j,Admissible (a j))
    (hRF : ∀ a ∈ rightFamily F g,∀ j,Admissible (a j)) (f : ColourTuple × ColourTuple → M) :
    (∑ r ∈ residualFibre F g,f r)=
      ∑ u : ElementFibre (leftFamily F g), ∑ v : ElementFibre (rightFamily F g),
        if ∀ j k,IsCoprime (fibreTuple (leftFamily F g) hLF u j) (fibreTuple (rightFamily F g) hRF v k)
        then f (fibreTuple (leftFamily F g) hLF u,fibreTuple (rightFamily F g) hRF v) else 0 := by
  rw [residualFibre_eq_cross_filter hF hpF hgn hgp,Finset.sum_filter]
  trans ∑ a ∈ leftFamily F g,∑ b ∈ rightFamily F g,
    if ∀ j k,IsCoprime (a j) (b k) then f (a,b) else 0
  · exact Finset.sum_product (leftFamily F g) (rightFamily F g)
      (fun a : ColourTuple × ColourTuple => if ∀ j k,IsCoprime (a.1 j) (a.2 k) then f a else 0)
  have htyped : (∑ a ∈ leftFamily F g,∑ b ∈ rightFamily F g,
      if ∀ j k,IsCoprime (a j) (b k) then f (a,b) else 0)=
      ∑ a : leftFamily F g,∑ b : rightFamily F g,
        if ∀ j k,IsCoprime (a.val j) (b.val k) then f (a.val,b.val) else 0 := by
    symm
    trans ∑ a ∈ leftFamily F g,∑ b : rightFamily F g,
      if ∀ j k,IsCoprime (a j) (b.val k) then f (a,b.val) else 0
    · exact Finset.sum_coe_sort (leftFamily F g) (fun a => ∑ b : rightFamily F g,
        if ∀ j k,IsCoprime (a j) (b.val k) then f (a,b.val) else 0)
    · apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_coe_sort (rightFamily F g) (fun b : ColourTuple =>
        if ∀ j k,IsCoprime (a j) (b k) then f (a,b) else (0 : M))
  trans ∑ a : leftFamily F g,∑ b : rightFamily F g,
    if ∀ j k,IsCoprime (a.val j) (b.val k) then f (a.val,b.val) else 0
  · exact htyped
  trans ∑ u : ElementFibre (leftFamily F g),∑ b : rightFamily F g,
    if ∀ j k,IsCoprime (fibreTuple (leftFamily F g) hLF u j) (b.val k)
      then f (fibreTuple (leftFamily F g) hLF u,b.val) else 0
  · exact ((tupleElementFibreEquiv (leftFamily F g) hLF).symm.sum_comp
      (fun a : leftFamily F g => ∑ b : rightFamily F g,
        if ∀ j k,IsCoprime (a.val j) (b.val k) then f (a.val,b.val) else 0)).symm
  apply Finset.sum_congr rfl
  intro u hu
  exact ((tupleElementFibreEquiv (rightFamily F g) hRF).symm.sum_comp
    (fun b : rightFamily F g => if ∀ j k,IsCoprime (fibreTuple (leftFamily F g) hLF u j) (b.val k)
      then f (fibreTuple (leftFamily F g) hLF u,b.val) else 0)).symm

section RadialIndex
open FiveColourNorm FiveColourMellin
variable {VL VR : Type} [Fintype VL] [Fintype VR]

/-- The common radial swap in the two independent full-fibre indices.
This is only a finite bijection, before any estimate. -/
theorem radialActualSwap_eq_fibre_pairs
    (EL : VL → Finset O) (ER : VR → Finset O) (S : Finset (Ideal O))
    (A : Fibre EL → ℂ) (B : Fibre ER → ℂ) (FL : O → VR → ℂ) (FR : O → VL → ℂ)
    (H : VL → VR → ℂ) (weight : VL → VR → S → ℂ)
    (x : Fibre EL → ℝ) (y : Fibre ER → ℝ) (z : S → ℝ) (W : 𝓢(ℝ,ℂ)) (R : ℝ) :
    radialActualSwap EL ER S A B FL FR H weight x y z W R=
      ∑ u : Fibre EL,∑ v : Fibre ER,∑ I : S,
        (H u.1 v.1*weight u.1 v.1 I*
          if IsCoprime (Ideal.span {u.2.val}) (Ideal.span {v.2.val}) then
            (star (selectedMatrix (EL u.1) S I u.2)*(A u*star (FL u.2.val v.1)))*
            (selectedMatrix (ER v.1) S I v.2*(B v*FR v.2.val u.1)) else 0)*
        paperRadialFourier W (R*z I/(x u*y v)) := by
  let e : SwapIndex EL ER S ≃ (Fibre EL × Fibre ER × S) :=
    { toFun := fun j => (⟨j.1,j.2.2.2.1⟩,⟨j.2.1,j.2.2.2.2⟩,j.2.2.1)
      invFun := fun j => ⟨j.1.1,j.2.1.1,j.2.2,j.1.2,j.2.1.2⟩
      left_inv := by rintro ⟨v,w,I,u,q⟩; rfl
      right_inv := by rintro ⟨⟨v,u⟩,⟨w,q⟩,I⟩; rfl }
  exact (e.symm.sum_comp (fun j : SwapIndex EL ER S =>
    actualSwapCoefficient EL ER S A B FL FR H weight j*
      paperRadialFourier W (R*z j.2.2.1/(x ⟨j.1,j.2.2.2.1⟩*y ⟨j.2.1,j.2.2.2.2⟩)))).symm.trans
        (by simp only [Fintype.sum_prod_type]; rfl)
end RadialIndex

def normalizedTerm (F : Finset ColourTuple) (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (g : SharedTable) (a a' : ColourTuple) (W : 𝓢(ℝ,ℂ)) (L : ℝ)
    (E : Finset (SourceMaskIndex F)) (k : Oˣ × ℕ × ℕ) (I : Ideal O)
    (rL rR : EisensteinEPrimaryPhase.Coord) (Y DL DR : ℝ) : ℂ :=
  let b := BadFrequencySectors.keyFactor k
  let q := primeSubsetGenerator (sourceMaskPrime F) E
  packetPrefactor F g L E DL DR*
    (leftOwnFactor F hF g a q b*radicalWeight DL a)*
    (rightOwnFactor F hF g a' q b*radicalWeight DR a')*
    (higherGaussFactor F hF g (higherTuple a) (higherTuple a') rL rR/8)*
    star (bareHigherModulation F (primaryGenerator (a 0)) (higherTuple a'))*
      bareHigherModulation F (primaryGenerator (a' 0)) (higherTuple a)*
    NaturalFrequencyReindex.commonWeight F hF g (higherTuple a) (higherTuple a') q b rL rR I*
    star (idealRowHom (primaryGenerator (a 0)) I)*idealRowHom (primaryGenerator (a' 0)) I*
    paperRadialFourier W (packetScale F g L E k Y DL DR*((Ideal.absNorm I:ℝ)/Y)/
      (radicalCoordinate DL a*radicalCoordinate DR a'))

theorem packetTerm_normalized_residual
    (F : Finset ColourTuple) (hF : ∀ c ∈ F, ∀ j, Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    (g : SharedTable) (r : ColourTuple × ColourTuple) (hr : r ∈ residualFibre F g)
    (W : 𝓢(ℝ,ℂ)) (L : ℝ) (E : Finset (SourceMaskIndex F))
    (k : Oˣ × ℕ × ℕ) (I : Ideal O) (hI : Supported I)
    (rL rR : EisensteinEPrimaryPhase.Coord)
    (hrL : residue (primaryGenerator (r.1 0))=rL)
    (hrR : residue (primaryGenerator (r.2 0))=rR)
    (Y DL DR : ℝ) (hY : 0 < Y) (hDL : 0 < DL) (hDR : 0 < DR) :
    NaturalActualTail.packetTerm F hF (recoverLeft g r.1) (recoverRight g r.2) W L E
      (BadFrequencySectors.keyFactor k*primaryGenerator I)=
      normalizedTerm F hF g r.1 r.2 W L E k I rL rR Y DL DR := by
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hr
  have hrec := recover_pair_of_mem hpF hp
  have hrecL := congrArg Prod.fst hrec
  have hrecR := congrArg Prod.snd hrec
  dsimp only [recoverPair] at hrecL hrecR
  have ht := (Finset.mem_filter.mp hp).2
  have hcp := (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  have hdp := (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
  rw [hrecL,hrecR]
  exact (packetTerm_normalized F hF p.1 p.2 hcp hdp (hpF _ hcp) (hpF _ hdp)
    W L E k I hI rL rR hrL hrR Y DL DR hY hDL hDR).trans
      (by simp only [normalizedTerm,ht]; rfl)

theorem cross_coprime_elementFibres (G H : Finset ColourTuple)
    (hG : ∀ a ∈ G,∀ j,Admissible (a j)) (hH : ∀ a ∈ H,∀ j,Admissible (a j))
    (u : ElementFibre G) (v : ElementFibre H) :
    (∀ j k,IsCoprime (fibreTuple G hG u j) (fibreTuple H hH v k)) ↔
      IsCoprime (Ideal.span {u.2.val}) (Ideal.span {v.2.val}) ∧
      (∀ k,IsCoprime (Ideal.span {u.2.val}) (v.1.val k)) ∧
      (∀ j,IsCoprime (Ideal.span {v.2.val}) (u.1.val j)) ∧
      (∀ j k,IsCoprime (u.1.val j) (v.1.val k)) := by
  rw [cross_coprime_split,fibreTuple_higher,fibreTuple_higher,
    ← fibreTuple_pivot_span G hG u,← fibreTuple_pivot_span H hH v]
  exact and_congr Iff.rfl (and_congr Iff.rfl (and_congr
    (forall_congr' fun j => isCoprime_comm) Iff.rfl))

/-- Exact ALL-pair near sector as the actual single-kernel finite swap.
The higher cross masks, full table, puncture, bad sector and ordinary ideal
source remain literal. No two-pivot selector is dropped. -/
theorem actualSectorForm_eq_radialSwap
    (F : Finset ColourTuple) (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    (g : SharedTable) (hgn : ∀ j k,g j k ≠ 0)
    (hgp : Pairwise (fun p q : Fin 5 × Fin 5 => IsCoprime (g p.1 p.2) (g q.1 q.2)))
    (hLF : ∀ a ∈ leftFamily F g,∀ j,Admissible (a j))
    (hRF : ∀ a ∈ rightFamily F g,∀ j,Admissible (a j))
    (α β : ColourTuple → ℂ) (W : 𝓢(ℝ,ℂ)) (L : ℝ)
    (E : Finset (SourceMaskIndex F)) (k : Oˣ × ℕ × ℕ) (S : Finset (Ideal O))
    (hS : ∀ I ∈ S,Supported I) (rL rR : EisensteinEPrimaryPhase.Coord)
    (hrL : ∀ a ∈ leftFamily F g,residue (primaryGenerator (a 0))=rL)
    (hrR : ∀ a ∈ rightFamily F g,residue (primaryGenerator (a 0))=rR)
    (Y DL DR : ℝ) (hY : 0 < Y) (hDL : 0 < DL) (hDR : 0 < DR) :
    actualSectorForm F hF g α β W L E k S = packetPrefactor F g L E DL DR*
      FiveColourMellin.radialActualSwap (leftRows F g) (rightRows F g) S
        (leftPacketArray F hF g hLF α (primeSubsetGenerator (sourceMaskPrime F) E) (BadFrequencySectors.keyFactor k) DL)
        (rightPacketArray F hF g hRF β (primeSubsetGenerator (sourceMaskPrime F) E) (BadFrequencySectors.keyFactor k) DR)
        (fun u w => higherModulation F u w.val) (fun u v => higherModulation F u v.val)
        (packetHigherKernel F hF g rL rR)
        (packetWeight F hF g (primeSubsetGenerator (sourceMaskPrime F) E) (BadFrequencySectors.keyFactor k) rL rR S)
        (leftPacketCoordinate F g hLF DL) (rightPacketCoordinate F g hRF DR)
        (fun I : S => (Ideal.absNorm I.val:ℝ)/Y) W (packetScale F g L E k Y DL DR) := by
  unfold actualSectorForm
  rw [residualFibre_sum_eq_elementFibres F g hF hpF hgn hgp hLF hRF,
    radialActualSwap_eq_fibre_pairs]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  let a := fibreTuple (leftFamily F g) hLF u
  let a' := fibreTuple (rightFamily F g) hRF v
  have ha := fibreTuple_mem (leftFamily F g) hLF u
  have ha' := fibreTuple_mem (rightFamily F g) hRF v
  by_cases hcross : ∀ j k,IsCoprime (fibreTuple (leftFamily F g) hLF u j)
    (fibreTuple (rightFamily F g) hRF v k)
  · simp only [if_pos hcross]
    have hr : (a,a') ∈ residualFibre F g := by
      rw [residualFibre_eq_cross_filter hF hpF hgn hgp]
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha,ha'⟩,hcross⟩
    obtain ⟨h00,h0h,hh0,hhh⟩ := (cross_coprime_elementFibres _ _ hLF hRF u v).mp hcross
    apply Finset.sum_congr rfl
    intro I hI
    rw [packetTerm_normalized_residual F hF hpF g (a,a') hr W L E k I.val (hS _ I.property)
      rL rR (hrL a ha) (hrR a' ha') Y DL DR hY hDL hDR]
    simp only [packetHigherKernel,higherPairMask,if_pos hhh,higherModulation,higherCrossMask,
      if_pos h0h,if_pos hh0,one_mul,mul_one,if_pos h00,selectedMatrix]
    unfold normalizedTerm leftPacketArray rightPacketArray packetWeight leftPacketCoordinate rightPacketCoordinate
    dsimp only
    rw [fibreTuple_higher,fibreTuple_higher,fibreTuple_pivot,fibreTuple_pivot]
    ring
  · simp only [if_neg hcross]
    symm
    apply Finset.sum_eq_zero
    intro I hI
    by_cases h00 : IsCoprime (Ideal.span {u.2.val}) (Ideal.span {v.2.val})
    · by_cases h0h : ∀ j,IsCoprime (Ideal.span {u.2.val}) (v.1.val j)
      · by_cases hh0 : ∀ j,IsCoprime (Ideal.span {v.2.val}) (u.1.val j)
        · by_cases hhh : ∀ j k,IsCoprime (u.1.val j) (v.1.val k)
          · exact (hcross ((cross_coprime_elementFibres _ _ hLF hRF u v).mpr ⟨h00,h0h,hh0,hhh⟩)).elim
          · simp [packetHigherKernel,higherPairMask,hhh]
        · simp [higherModulation,higherCrossMask,hh0,h00]
      · simp [higherModulation,higherCrossMask,h0h,h00]
    · simp [h00]

end
end Qrh.JointDetector.NaturalNearPackets

#print axioms Qrh.JointDetector.NaturalNearPackets.primitiveIdeal_factor
#print axioms Qrh.JointDetector.NaturalNearPackets.packetTerm_normalized
#print axioms Qrh.JointDetector.NaturalNearPackets.residualFibre_sum_eq_elementFibres
#print axioms Qrh.JointDetector.NaturalNearPackets.radialActualSwap_eq_fibre_pairs
#print axioms Qrh.JointDetector.NaturalNearPackets.actualSectorForm_eq_radialSwap
#print axioms Qrh.JointDetector.NaturalNearPackets.higherGaussFactor_norm_le_eight
#print axioms Qrh.JointDetector.NaturalNearPackets.actual_radial_ratio
#print axioms Qrh.JointDetector.NaturalNearPackets.radical_prefactor
