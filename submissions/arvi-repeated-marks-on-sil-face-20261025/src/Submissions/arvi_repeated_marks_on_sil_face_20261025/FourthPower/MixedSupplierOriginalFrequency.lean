/- Copyright (c) 2026 Sil. Apache-2.0.
Actual supplier dictionary at the ORIGINAL physical frequency.
The selected D character remains in the source coefficient. No K4 step.

-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedSupplierOuterActive
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedSupplierCanonical

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedSupplierOriginalFrequency
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge CompletedGauss CenteredMomentFixedRay RayFourExpansion
open CenteredMomentFirstColumns QRH.Record1252270103KernelMass QRH.Record1252270103TwoIdeal
open CenteredMomentHeckeColumnWindow CenteredMomentGaussEnergy CenteredMomentSourceRow
open CenteredMomentSecondSourceEnergy CenteredMomentOriginalChildEnergy
open CenteredMomentFirstSectors CenteredMomentCommonSectors CenteredMomentLiveDomain
open CenteredMomentSourceRectangle CenteredMomentSourceProfileMass CenteredMomentSourceMass
open MixedSupplierKernel MixedSupplierFourthRow MixedSupplierSource MixedSupplierCanonical
open MixedSupplierReconstruction MixedLiteralAllocation
open MixedSupplierOuterActive MixedTupleRows MixedCommonRestriction MixedHeightEnergy
open MixedLiveRows MixedLiveNormalization
open MixedSelectedCommon (idealGauss primary_supported)
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]
local instance {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- CRT and the finite ray table alone; fifth-freeness and frequency
dilation are not needed for this original-frequency identity. -/
theorem fixed_supplier_row_original {ι : Type*} (V : Finset ι)
    (n : ι→Id) (hn : ∀v,Supported (n v)) (A : ℂ) (B : ι→ℂ)
    (f D : Id) (hf : Supported f) (hD : Supported D)
    (τ : Character) (t : ℝ) (k : O) :
    (∑v∈V,A*B v*heightCoeff τ t ((f*D)*n v)*
      (if IsCoprime (f*D) (n v) then
        idealGauss ((f*D)*n v)
          ((supported_mul_iff _ _).mpr ⟨(supported_mul_iff _ _).mpr ⟨hf,hD⟩,hn v⟩) k
        else 0)) =
      ∑χ : RayCharacter,∑ξ : RayCharacter,pairCoeff firstPhaseTable χ ξ*
        (A*heightCoeff τ t (f*D)*rayCharacter χ (primaryGenerator (f*D))*
          idealGauss (f*D) ((supported_mul_iff _ _).mpr ⟨hf,hD⟩) k)*
        gaussPolynomial V (fun v=>primaryGenerator (n v))
          (fun v=>primary_supported (n v) (hn v))
          (fun v=>fixedCommonCoefficient n B f τ t ξ v*
            (idealRowHom (primaryGenerator D) (n v))^2) k := by
  have hrow (v : ι) := fixed_product_rays f D (n v) hf hD (hn v) k
  simp_rw [hrow,heightCoeff_mul]
  simp only [gaussPolynomial,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ξ hξ
  apply Finset.sum_congr rfl
  intro v hv
  simp only [fixedCommonCoefficient,idealGauss]
  ring

/-- Literal selected summand including unsupported and zero cases.
Both f and D twists remain in the coefficient at the ORIGINAL k. -/
theorem selected_row_original (q : Data α) (x : Frozen q) (y : Selected q)
    (seed : Id) (hseed : q.u=frozenProduct q x*seed)
    (τ : Character) (t : ℝ) (k : O) :
    selectedRow q x y τ t k =
      ∑χ : RayCharacter,∑ξ : RayCharacter,pairCoeff firstPhaseTable χ ξ*
        selectedScalar q x y τ t k χ*originalPolynomial q x y seed τ t ξ k := by
  by_cases hf : Supported (frozenProduct q x)
  · by_cases hD : Supported (selectedProduct q y)
    · by_cases hy : selectedWeight q y=0
      · rw [selected_row_zero q x y hy τ t k]
        simp only [selectedScalar,hy,mul_zero,zero_mul,Finset.sum_const_zero]
      · rw [selected_supported_row q x y seed hseed hf hD hy τ t k]
        have he := fixed_supplier_row_original Finset.univ
          (fun v : keptResidual q=>residualColumn q v.val) (kept_supported q)
          ((if selectedGate q.R (frozenProduct q x) (selectedProduct q y) then 1 else 0)*
            selectedWeight q y) (fun v=>baseCoefficient q x seed v.val)
          (frozenProduct q x) (selectedProduct q y) hf hD τ t k
        have hscalar (χ : RayCharacter) : selectedScalar q x y τ t k χ=
            (((if selectedGate q.R (frozenProduct q x) (selectedProduct q y) then 1 else 0)*
              selectedWeight q y)*heightCoeff τ t (frozenProduct q x*selectedProduct q y)*
              rayCharacter χ (primaryGenerator (frozenProduct q x*selectedProduct q y))*
              idealGauss (frozenProduct q x*selectedProduct q y)
                ((supported_mul_iff _ _).mpr ⟨hf,hD⟩) k) := by
          unfold selectedScalar
          rw [primary_supported_eq _ ((supported_mul_iff _ _).mpr ⟨hf,hD⟩)]
        refine Eq.trans ?_ (he.trans ?_)
        · apply Finset.sum_congr (by ext; simp)
          intro v hv
          rfl
        · apply Finset.sum_congr (by ext; simp)
          intro χ hχ
          apply Finset.sum_congr (by ext; simp)
          intro ξ hξ
          rw [←hscalar χ]
          apply congrArg (fun z : ℂ=>pairCoeff firstPhaseTable χ ξ*
            selectedScalar q x y τ t k χ*z)
          unfold originalPolynomial gaussPolynomial
          apply Finset.sum_congr (by ext; simp)
          intro v hv
          rfl
    · have hz (n : Id) := primary_product_zero (frozenProduct q x) (selectedProduct q y)
        n (Or.inr (Or.inl hD)) k
      have hfn : ¬Supported (frozenProduct q x*selectedProduct q y) := by
        rw [supported_mul_iff]
        tauto
      have hscalar (χ : RayCharacter) : selectedScalar q x y τ t k χ=0 := by
        simp only [selectedScalar,primaryGaussRow,dif_neg hfn,mul_zero]
      rw [selected_row_literal q x y seed hseed τ t k]
      simp_rw [hz]
      simp only [hscalar,mul_zero,Finset.sum_const_zero,zero_mul]
  · have hz (n : Id) := primary_product_zero (frozenProduct q x) (selectedProduct q y)
      n (Or.inl hf) k
    have hfn : ¬Supported (frozenProduct q x*selectedProduct q y) := by
      rw [supported_mul_iff]
      tauto
    have hscalar (χ : RayCharacter) : selectedScalar q x y τ t k χ=0 := by
      simp only [selectedScalar,primaryGaussRow,dif_neg hfn,mul_zero]
    rw [selected_row_literal q x y seed hseed τ t k]
    simp_rw [hz]
    simp only [hscalar,mul_zero,Finset.sum_const_zero,zero_mul]

/-- The ideal column coefficient for the second Poisson step. tau is
kept separate: both cubic twists are explicit, including their natural zeros. -/
def outerColumn (q : Data α) (x : Frozen q) (y : Selected q) (seed : Id)
    (ξ : RayCharacter) (I : Id) : ℂ :=
  commonColumn q x seed I * (idealRowHom (primaryGenerator (frozenProduct q x)) I)^2 *
    (idealRowHom (primaryGenerator (selectedProduct q y)) I)^2 *
    rayCharacter ξ (primaryGenerator I)

/-- Nonzero GROUPED source columns supply an actual active original
tuple. Cancellation can remove terms, but cannot create a nonzero sum from
zero terms. This passes common-sector divisors to OuterActive exactly. -/
theorem outer_column_active_tuple (q : Data α) (x : Frozen q) (y : Selected q)
    (seed : Id) (τ : Character) (t : ℝ) (ξ : RayCharacter) (I : Id)
    (hI : Supported I) (hn : outerColumn q x y seed ξ I * heightCoeff τ t I ≠ 0) :
    ∃v : keptResidual q,residualColumn q v.val=I ∧
      originalMovingCoefficient q x y seed τ t ξ v ≠ 0 := by
  simp only [outerColumn,mul_ne_zero_iff] at hn
  rcases hn with ⟨⟨⟨⟨hbase,hf⟩,hD⟩,hr⟩,ht⟩
  unfold commonColumn at hbase
  obtain ⟨v,hv,hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero hbase
  have he : residualColumn q v=I := (Finset.mem_filter.mp hv).2
  have hkeep : v∈keptResidual q :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ v,he.symm ▸ hI⟩
  refine ⟨⟨v,hkeep⟩,he,?_⟩
  change (((baseCoefficient q x seed v*heightCoeff τ t (residualColumn q v))*
    (idealRowHom (primaryGenerator (frozenProduct q x)) (residualColumn q v))^2)*
    rayCharacter ξ (primaryGenerator (residualColumn q v)))*
    (idealRowHom (primaryGenerator (selectedProduct q y)) (residualColumn q v))^2 ≠ 0
  rw [he]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hb ht) hf) hr) hD

/-- Finite fiber regrouping onto actual ideals, before any estimate.
Unsupported ideals disappear only because their primary Gauss row is zero. -/
theorem original_polynomial_source (q : Data α) (x : Frozen q) (y : Selected q)
    (seed : Id) (τ : Character) (t : ℝ) (ξ : RayCharacter) (k : O) :
    originalPolynomial q x y seed τ t ξ k =
      gaussPolynomial Finset.univ (sourceGenerator (commonColumns q))
        (sourceGenerator_supported (commonColumns q))
        (fun I : supportedColumns (commonColumns q)=>
          outerColumn q x y seed ξ I * heightCoeff τ t I) k := by
  rw [source_gauss_sum (commonColumns q)
    (fun I=>outerColumn q x y seed ξ I*heightCoeff τ t I) k]
  let F : Id→ℂ := fun I=>heightCoeff τ t I*
    (idealRowHom (primaryGenerator (frozenProduct q x)) I)^2*
    (idealRowHom (primaryGenerator (selectedProduct q y)) I)^2*
    rayCharacter ξ (primaryGenerator I)*primaryGaussRow I k
  have hgroup : (∑I∈commonColumns q,outerColumn q x y seed ξ I*
      heightCoeff τ t I*primaryGaussRow I k)=
      ∑v : Residual q,baseCoefficient q x seed v*F (residualColumn q v) := by
    rw [←common_column_sum q x seed F]
    apply Finset.sum_congr rfl
    intro I hI
    unfold outerColumn F
    ring
  rw [hgroup]
  have hactual : originalPolynomial q x y seed τ t ξ k=
      ∑v : keptResidual q,baseCoefficient q x seed v.val*F (residualColumn q v.val) := by
    unfold originalPolynomial gaussPolynomial
    apply Finset.sum_congr rfl
    intro v hv
    unfold originalMovingCoefficient commonVector fixedCommonCoefficient F
    rw [primary_supported_eq _ (kept_supported q v)]
    unfold idealGauss
    ring
  rw [hactual,Finset.sum_coe_sort (keptResidual q)
    (fun v : Residual q=>baseCoefficient q x seed v*F (residualColumn q v)),
    keptResidual,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hs : Supported (residualColumn q v)
  · simp only [hs,ite_true]
  · simp only [F,primaryGaussRow,hs,ite_false,dite_false,mul_zero]

/-- This energy identity supplies exactly the original fixed tau and the
literal beta required by the existing second-Poisson/common-sector API. -/
theorem original_energy_source (q : Data α) (x : Frozen q) (y : Selected q)
    (seed : Id) (τ : Character) (t : ℝ) (ξ : RayCharacter)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (∑' k : O,((‖originalPolynomial q x y seed τ t ξ k‖^2:ℝ):ℂ)*
      W (‖ConcreteTraceCRT.eisEmbedding k‖^2/K)) =
      sourceGaussEnergy (commonColumns q) (outerColumn q x y seed ξ) (heightCoeff τ t) W K := by
  unfold sourceGaussEnergy gaussEnergy
  apply tsum_congr
  intro k
  rw [original_polynomial_source]

/-- The actual outer energy is now decomposed at ORIGINAL K. D has not
been erased and remains in every left/right outerColumn factor. -/
theorem original_energy_common_sectors (q : Data α) (x : Frozen q) (y : Selected q)
    (seed : Id) (τ : Character) (t : ℝ) (ξ : RayCharacter)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    (∑' k : O,((‖originalPolynomial q x y seed τ t ξ k‖^2:ℝ):ℂ)*
      W (‖ConcreteTraceCRT.eisEmbedding k‖^2/K)) =
      ∑p∈commonLabels (supportedColumns (commonColumns q)) (supportedColumns (commonColumns q)),
        ∑z∈pairSector p.1 p.2 (supportedColumns (commonColumns q))
            (supportedColumns (commonColumns q)),
          ((outerColumn q x y seed ξ z.1*heightCoeff τ t z.1)*
            star (outerColumn q x y seed ξ z.2*heightCoeff τ t z.2))*
              secondSourceKernel z.1 z.2 W K := by
  rw [original_energy_source]
  exact source_energy_common_sectors τ t (commonColumns q) (outerColumn q x y seed ξ) W K hK

/-- Exact canonical source pools and originalColumn, with all supplier
holes, old punctures and the residual seed. The two twists stay explicit;
we do not replace fixed tau by a D-dependent character for root counting. -/
theorem original_polynomial_canonical (q : Data α) (x : Frozen q) (y : Selected q)
    (seed : Id) (τ : Character) (t : ℝ) (ξ : RayCharacter) (k : O)
    (S H : Finset PrimeIdeal) (hd : q.d.1≠0 ∧ q.d.2≠0) (b : ℝ)
    (hH : q.H=punctureProduct S H)
    (hA : q.A=residualPool q.d.1 hd.1 (plainSupportPool b q.X₁ q.Y₁))
    (hB : q.B=residualPool q.d.2 hd.2 (plainSupportPool b q.X₂ q.Y₂)) :
    let Q := finiteColumns (Fintype.piFinset (sourcePools
      (fun j : RestIndex q=>q.pool j.val.val) q.d hd b q.X₁ q.X₂ q.Y₁ q.Y₂))
    let β := originalColumn S H (fun j : RestIndex q=>q.pool j.val.val) q.d hd
      (q.R*frozenProduct q x) seed (fun j : RestIndex q=>avoid q.u q.ν j.val.val)
      (fun j=>q.Wslot j.val.val) (fun j=>q.P j.val.val) q.W₁ q.W₂
      b q.X₁ q.X₂ q.Y₁ q.Y₂
    originalPolynomial q x y seed τ t ξ k =
      (if IsCoprime (frozenProduct q x) q.R then (1:ℂ) else 0)*
        gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
          (fun I : supportedColumns Q=>β I*
            (idealRowHom (primaryGenerator (frozenProduct q x)) I)^2*
            (idealRowHom (primaryGenerator (selectedProduct q y)) I)^2*
            rayCharacter ξ (primaryGenerator I)*heightCoeff τ t I) k := by
  dsimp only
  let Q := finiteColumns (Fintype.piFinset (sourcePools
    (fun j : RestIndex q=>q.pool j.val.val) q.d hd b q.X₁ q.X₂ q.Y₁ q.Y₂))
  let β := originalColumn S H (fun j : RestIndex q=>q.pool j.val.val) q.d hd
    (q.R*frozenProduct q x) seed (fun j : RestIndex q=>avoid q.u q.ν j.val.val)
    (fun j=>q.Wslot j.val.val) (fun j=>q.P j.val.val) q.W₁ q.W₂ b q.X₁ q.X₂ q.Y₁ q.Y₂
  let F : Id→ℂ := fun I=>(idealRowHom (primaryGenerator (frozenProduct q x)) I)^2*
    (idealRowHom (primaryGenerator (selectedProduct q y)) I)^2*
    rayCharacter ξ (primaryGenerator I)*heightCoeff τ t I*primaryGaussRow I k
  have hsub : Q⊆commonColumns q := by
    simpa only [Q,sourcePools,hA,hB] using remaining_columns_subset q
  have hmem (I : Id) (hn : β I≠0) : I∈Q := finite_column_mem _ _ I hn
  have hid (I : Id) : commonColumn q x seed I=
      (if IsCoprime (frozenProduct q x) q.R then (1:ℂ) else 0)*β I :=
    common_column_original q x seed I S H hd b hH hA hB
  rw [original_polynomial_source,
    source_gauss_sum (commonColumns q) (fun I=>outerColumn q x y seed ξ I*heightCoeff τ t I) k,
    source_gauss_sum Q (fun I=>β I*
      (idealRowHom (primaryGenerator (frozenProduct q x)) I)^2*
      (idealRowHom (primaryGenerator (selectedProduct q y)) I)^2*
      rayCharacter ξ (primaryGenerator I)*heightCoeff τ t I) k]
  have hsum : (∑I∈Q,β I*F I)=∑I∈commonColumns q,β I*F I := by
    apply Finset.sum_subset hsub
    intro I hI hnot
    have hz : β I=0 := by
      by_contra hn
      exact hnot (hmem I hn)
    rw [hz,zero_mul]
  unfold outerColumn
  simp_rw [hid]
  simp only [mul_assoc]
  simp only [F,mul_assoc] at hsum
  rw [←Finset.mul_sum,←hsum]

/-- Exact raw normalization, with surviving slot scales counted once. -/
theorem original_normalization (q : Data α) (x : Frozen q) (y : Selected q)
    (seed : Id) (τ : Character) (t : ℝ) (ξ : RayCharacter) (k : O)
    (hT : 0<q.X₁*q.X₂) (hP : ∀j : RestIndex q,0<q.P j.val.val) :
    ‖normalization (q.X₁*q.X₂) (fun j : RestIndex q=>q.P j.val.val)*
        originalPolynomial q x y seed τ t ξ k‖^2 =
      ‖originalPolynomial q x y seed τ t ξ k‖^2/
        ((q.X₁*q.X₂)*∏j : RestIndex q,q.P j.val.val) := by
  rw [norm_mul,mul_pow,normalization_sq _ hT _ hP]
  ring

end
end Candidate.FourthPower.MixedSupplierOriginalFrequency
