/- Copyright (c) 2026 Sil. Apache-2.0.
Exact fixed-support window completion, keeping the smaller physical
artificial-divisor pool. No mask is deleted inside an absolute value.

-/
import Candidate.Feedback.FourthPower.OuterFreshArtificialSum
import Candidate.Feedback.FourthPower.OuterFreshBlock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.Feedback.FourthPower.OuterFreshFixedWindows
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentSourceRow CenteredMomentSourceMass CenteredMomentActiveSource
open CenteredMomentLiveDomain CenteredMomentFirstSectors CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentLogDyadic CenteredMomentSecondHeightFamily
open CenteredMomentSmooth
open CenteredMomentMobiusRegroup CenteredMomentCanonicalFirst
open CenteredMomentSecondLiveBlock CenteredMomentSecondDyadicRowSupport CenteredMomentSecondEnergySplit
open MixedPrincipalPair MixedPrincipalAllocations MixedLiveNormalization
open MixedPrincipalWindow
open MixedSupplierFourthRow MixedSupplierSource MixedSupplierOriginalFrequency
open OuterFreshWindowPair OuterFreshConsumer OuterFreshBlock OuterFreshSelectedWindow
open OuterFreshNonexceptionalFamily OuterFreshStructure OuterFreshArtificialSum
open OuterFreshPairedAllocatedWindow
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq α := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- One literal window used by rawKernelPair. -/
def rawWindow (conjugate : Bool) (τ : Character) (t : ℝ)
    (S : Finset Id) (β : Id→ℂ) (G : Id) (hG : Supported G)
    (χ : RayCharacter) (A : O) (D : Id) (θ X : ℝ) (z : O) : ℂ :=
  rowPolynomial Finset.univ (sectorElement G hG.1 S)
    (fun I=>divisorCoefficient D (sectorElement G hG.1 S)
      (movingCoefficient A (sectorElement G hG.1 S)
        (fun J=>β (G*J)*heightCoeff τ t J)) χ I*
      (if conjugate then star (columnPhase logAnnulus
        (Real.log ((I.val.absNorm:ℝ)/X)) θ) else
        columnPhase logAnnulus (Real.log ((I.val.absNorm:ℝ)/X)) θ)) z

def idealTerm (conjugate : Bool) (τ : Character) (t : ℝ)
    (β : Id→ℂ) (G : Id) (χ : RayCharacter) (A : O) (D : Id)
    (θ X : ℝ) (z : O) (I : Id) : ℂ :=
  (if D∣I then (β (G*I)*heightCoeff τ t I)*idealRowHom A I*
    rayCharacter χ (primaryGenerator I) else 0)*
    (if conjugate then star (columnPhase logAnnulus (Real.log ((I.absNorm:ℝ)/X)) θ)
      else columnPhase logAnnulus (Real.log ((I.absNorm:ℝ)/X)) θ)*idealRowHom z I

theorem raw_window_ideal (conjugate : Bool) (τ : Character) (t : ℝ)
    (S : Finset Id) (β : Id→ℂ) (G : Id) (hG : Supported G)
    (χ : RayCharacter) (A : O) (D : Id) (θ X : ℝ) (z : O) :
    rawWindow conjugate τ t S β G hG χ A D θ X z=
      ∑I∈sectorPool G hG.1 S,idealTerm conjugate τ t β G χ A D θ X z I := by
  unfold rawWindow rowPolynomial
  simp only [divisorCoefficient,movingCoefficient,sectorElement_span]
  simp only [sectorElement]
  change (∑I : sectorPool G hG.1 S,idealTerm conjugate τ t β G χ A D θ X z I)=_
  exact Finset.sum_coe_sort _ _

theorem idealTerm_zero (conjugate : Bool) (τ : Character) (t : ℝ)
    (β : Id→ℂ) (G : Id) (χ : RayCharacter) (A : O) (D : Id)
    (θ X : ℝ) (z : O) (I : Id) (hzero : β (G*I)=0) :
    idealTerm conjugate τ t β G χ A D θ X z I=0 := by
  by_cases hD:D∣I <;> simp only [idealTerm,hD,ite_true,ite_false,hzero,zero_mul]

theorem sector_pool_mono (S T : Finset Id) (hST : S⊆T) (G : Id) (hG : G≠0) :
    sectorPool G hG S⊆sectorPool G hG T := by
  intro I hI
  obtain ⟨hI,hcop⟩:=Finset.mem_filter.mp hI
  have hGI: G*I∈supportedColumns S:=(mem_residualPool G hG _ I).mp hI
  have hGT:G*I∈supportedColumns T:=Finset.mem_filter.mpr
    ⟨hST (Finset.mem_filter.mp hGI).1,(Finset.mem_filter.mp hGI).2⟩
  exact Finset.mem_filter.mpr ⟨(mem_residualPool G hG _ I).mpr hGT,hcop⟩

/-- Completion is justified coefficient by coefficient before any norm.
The moving phase, ray, divisor and conjugate window remain unchanged. -/
theorem raw_window_zero_extension (conjugate : Bool) (τ : Character) (t : ℝ)
    (S T : Finset Id) (hST : S⊆T) (β : Id→ℂ)
    (hsupport : ∀I∈T,β I≠0→I∈S)
    (G : Id) (hG : Supported G) (χ : RayCharacter) (A : O) (D : Id)
    (θ X : ℝ) (z : O) :
    rawWindow conjugate τ t S β G hG χ A D θ X z=
      rawWindow conjugate τ t T β G hG χ A D θ X z := by
  rw [raw_window_ideal,raw_window_ideal]
  apply Finset.sum_subset (sector_pool_mono S T hST G hG.1)
  intro I hIT hnot
  apply idealTerm_zero
  by_contra hβ
  obtain ⟨hI,hcop⟩:=Finset.mem_filter.mp hIT
  have hGI:G*I∈supportedColumns T:=(mem_residualPool G hG.1 _ I).mp hI
  have hGS:G*I∈supportedColumns S:=Finset.mem_filter.mpr
    ⟨hsupport (G*I) (Finset.mem_filter.mp hGI).1 hβ,(Finset.mem_filter.mp hGI).2⟩
  exact hnot (Finset.mem_filter.mpr ⟨(mem_residualPool G hG.1 _ I).mpr hGS,hcop⟩)

set_option maxHeartbeats 600000 in
/-- In the actual fixed support, every outer column is supported by
commonColumn. This uses no nonzero-sum inference and no gate division. -/
theorem fixed_window (conjugate : Bool) (q : Data ι) (x : Frozen q) (y : Selected q)
    (r : Source (RestIndex q) a b) (seed : Id) (τ : Character) (t : ℝ)
    (ξ χ : RayCharacter) (A : O) (G : Id) (hG : Supported G) (D : Id)
    (θ X : ℝ) (z : O) :
    rawWindow conjugate τ t (fixedPool q x r seed) (outerColumn q x y seed ξ)
      G hG χ A D θ X z=
      rawWindow conjugate τ t (sourceColumns r) (outerColumn q x y seed ξ)
        G hG χ A D θ X z := by
  apply raw_window_zero_extension conjugate τ t _ _
    (Finset.filter_subset _ _) (outerColumn q x y seed ξ) _ G hG χ A D θ X z
  intro I hI hβ
  exact Finset.mem_filter.mpr ⟨hI,outer_supported_by_common q x y seed ξ I hβ⟩

set_option maxHeartbeats 600000 in
/-- The original residual normalization is inserted exactly once. -/
theorem fixed_window_normalized (conjugate : Bool)
    (q : Data ι) (x : Frozen q) (y : Selected q)
    (r : Source (RestIndex q) a b) (seed : Id) (τ : Character) (t : ℝ)
    (ξ χ : RayCharacter) (A : O) (G : Id) (hG : Supported G) (D : Id)
    (θ X : ℝ) (z : O) :
    normalization (r.X₁*r.X₂) r.P*
      rawWindow conjugate τ t (fixedPool q x r seed) (outerColumn q x y seed ξ)
        G hG χ A D θ X z=
      outerWindow conjugate q x y r seed τ ξ χ A G hG D t θ X z := by
  rw [fixed_window]
  rfl

/-- Exact raw physical-pair rewrite on the SMALLER fixed divisor pool.
Only the two windows are zero-extended. There is deliberately no equality
between fixedDivisors and the larger sourceColumns divisor pool. -/
theorem fixed_kernel_normalized (q : Data ι) (x : Frozen q) (y : Selected q)
    (r : Source (RestIndex q) a b) (seed : Id) (τ : Character) (t : ℝ)
    (ξ χ ρ : RayCharacter) (C E : Id) (hC : Supported C) (hE : Supported E)
    (U : Finset (CommonIndex C E)) (θ X Y : ℝ) (rows : Finset O) :
    ‖normalization (r.X₁*r.X₂) r.P‖^2*
      rawKernelPair τ t (fixedPool q x r seed) (outerColumn q x y seed ξ)
        C E hC hE U χ ρ θ X Y rows=
      ∑D∈fixedDivisors q x r seed E hE,‖(UniqueFactorizationMonoid.moebius D:ℂ)‖*
        ∑z∈rows,‖outerWindow false q x y r seed τ ξ χ (oldMoving C E U) C hC D t θ X z‖*
          ‖outerWindow true q x y r seed τ ξ (ρ⁻¹) (oldMoving C E U) E hE D t θ Y (-z)‖ := by
  change ‖normalization (r.X₁*r.X₂) r.P‖^2*
      (∑D∈fixedDivisors q x r seed E hE,‖(UniqueFactorizationMonoid.moebius D:ℂ)‖*
        ∑z∈rows,
          ‖rawWindow false τ t (fixedPool q x r seed) (outerColumn q x y seed ξ)
            C hC χ (oldMoving C E U) D θ X z‖*
          ‖rawWindow true τ t (fixedPool q x r seed) (outerColumn q x y seed ξ)
            E hE (ρ⁻¹) (oldMoving C E U) D θ Y (-z)‖)=_
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D hD
  rw [mul_left_comm,Finset.mul_sum]
  apply congrArg (fun v:ℝ=>‖(UniqueFactorizationMonoid.moebius D:ℂ)‖*v)
  apply Finset.sum_congr rfl
  intro z hz
  rw [←fixed_window_normalized false q x y r seed τ t ξ χ
      (oldMoving C E U) C hC D θ X z,
    ←fixed_window_normalized true q x y r seed τ t ξ (ρ⁻¹)
      (oldMoving C E U) E hE D θ Y (-z),norm_mul,norm_mul]
  ring

/-- The completed sharp character estimate is now attached to the literal
fixed-support window. All phases, the selected product and the original
normalization survive. No source estimate is a premise. -/
theorem fixed_window_sharp_norm (conjugate : Bool)
    (q : Data ι) (x : Frozen q) (y : Selected q)
    (r : Source (RestIndex q) a b) (ha : 0<a) (hm : Matches q x r ha)
    (seed : Id) (τ : Character) (ξ χ : RayCharacter)
    (C E : Id) (hC : Supported C) (hE : Supported E)
    (U : Finset (CommonIndex C E)) (ψ : RayCharacter→Character)
    (hψ : SharpFamily τ (frozenProduct q x) ξ C E hC hE U ψ)
    (G : Id) (hG : Supported G) (hGE:G=C ∨ G=E) (D : Id)
    (t θ X : ℝ) (z : O) :
    ‖normalization (r.X₁*r.X₂) r.P‖*
      ‖rawWindow conjugate τ t (fixedPool q x r seed) (outerColumn q x y seed ξ)
        G hG χ (oldMoving C E U) D θ X z‖≤
      ‖normalization (r.X₁*r.X₂) r.P‖*
        ‖residualWindow conjugate r ha G hG seed D (selectedProduct q y) (ψ χ) t θ X z‖ := by
  rw [←norm_mul,fixed_window_normalized,
    outer_window_sharp conjugate q x y r ha hm τ ξ χ C E hC hE U ψ hψ
      seed G D hG hGE t θ X z,norm_mul,norm_mul]
  have h := mul_le_mul_of_nonneg_right (factor_norm_le_one q x y ξ G)
    (mul_nonneg (norm_nonneg (normalization (r.X₁*r.X₂) r.P))
      (norm_nonneg (residualWindow conjugate r ha G hG seed D
        (selectedProduct q y) (ψ χ) t θ X z)))
  simpa only [norm_mul,one_mul,mul_assoc] using h

private theorem normalization_norm_pos {α : Type*} [Fintype α]
    (r : Source α a b) : 0<‖normalization (r.X₁*r.X₂) r.P‖ := by
  have he:=normalization_sq (r.X₁*r.X₂)
    (mul_pos (r.hL.trans_le r.hX₁) (r.hL.trans_le r.hX₂)) r.P
    (fun i=>zero_lt_one.trans_le (r.hP i))
  have hp:0<1/(r.X₁*r.X₂*∏i,r.P i):=one_div_pos.mpr
    (mul_pos (mul_pos (r.hL.trans_le r.hX₁) (r.hL.trans_le r.hX₂))
      (Finset.prod_pos (fun i _=>zero_lt_one.trans_le (r.hP i))))
  nlinarith [norm_nonneg (normalization (r.X₁*r.X₂) r.P)]

theorem fixed_raw_window_sharp_norm (conjugate : Bool)
    (q : Data ι) (x : Frozen q) (y : Selected q)
    (r : Source (RestIndex q) a b) (ha : 0<a) (hm : Matches q x r ha)
    (seed : Id) (τ : Character) (ξ χ : RayCharacter)
    (C E : Id) (hC : Supported C) (hE : Supported E)
    (U : Finset (CommonIndex C E)) (ψ : RayCharacter→Character)
    (hψ : SharpFamily τ (frozenProduct q x) ξ C E hC hE U ψ)
    (G : Id) (hG : Supported G) (hGE:G=C ∨ G=E) (D : Id)
    (t θ X : ℝ) (z : O) :
    ‖rawWindow conjugate τ t (fixedPool q x r seed) (outerColumn q x y seed ξ)
        G hG χ (oldMoving C E U) D θ X z‖≤
      ‖residualWindow conjugate r ha G hG seed D (selectedProduct q y) (ψ χ) t θ X z‖ :=
  (mul_le_mul_iff_of_pos_left (normalization_norm_pos r)).mp
    (fixed_window_sharp_norm conjugate q x y r ha hm seed τ ξ χ C E hC hE U ψ hψ
      G hG hGE D t θ X z)

/-- Direct attachment to the raw physical kernel, including its actual
right inverse ray. The divisor pool stays fixedPool-based on BOTH sides.
This is finite support completion and the norm-one exact phase bound only;
the prepared ArtificialSum theorem supplies the analytic residual estimate. -/
theorem fixed_raw_kernel_sharp (q : Data ι) (x : Frozen q) (y : Selected q)
    (r : Source (RestIndex q) a b) (ha : 0<a) (hm : Matches q x r ha)
    (seed : Id) (τ : Character) (ξ χ ρ : RayCharacter)
    (C E : Id) (hC : Supported C) (hE : Supported E)
    (U : Finset (CommonIndex C E)) (ψ : RayCharacter→Character)
    (hψ : SharpFamily τ (frozenProduct q x) ξ C E hC hE U ψ)
    (t θ X Y : ℝ) (rows : Finset O) :
    rawKernelPair τ t (fixedPool q x r seed) (outerColumn q x y seed ξ)
      C E hC hE U χ ρ θ X Y rows≤
      ∑D∈fixedDivisors q x r seed E hE,‖(UniqueFactorizationMonoid.moebius D:ℂ)‖*
        ∑z∈rows,
          ‖residualWindow false r ha C hC seed D (selectedProduct q y) (ψ χ) t θ X z‖*
          ‖residualWindow true r ha E hE seed D (selectedProduct q y) (ψ (ρ⁻¹)) t θ Y (-z)‖ := by
  change (∑D∈fixedDivisors q x r seed E hE,‖(UniqueFactorizationMonoid.moebius D:ℂ)‖*
    ∑z∈rows,
      ‖rawWindow false τ t (fixedPool q x r seed) (outerColumn q x y seed ξ)
        C hC χ (oldMoving C E U) D θ X z‖*
      ‖rawWindow true τ t (fixedPool q x r seed) (outerColumn q x y seed ξ)
        E hE (ρ⁻¹) (oldMoving C E U) D θ Y (-z)‖)≤_
  apply Finset.sum_le_sum
  intro D hD
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.sum_le_sum
  intro z hz
  exact mul_le_mul
    (fixed_raw_window_sharp_norm false q x y r ha hm seed τ ξ χ C E hC hE U ψ hψ
      C hC (Or.inl rfl) D t θ X z)
    (fixed_raw_window_sharp_norm true q x y r ha hm seed τ ξ (ρ⁻¹) C E hC hE U ψ hψ
      E hE (Or.inr rfl) D t θ Y (-z))
    (norm_nonneg _) (norm_nonneg _)

/-- The selected-dependent physical row set is exactly a filter of the
single fixed row set used by the analytic selected-product average. -/
theorem fixed_selected_rows (q : Data ι) (x : Frozen q) (y : Selected q)
    (τ : Character) (ξ χ₀ : RayCharacter) (Q C E : Id)
    (U : Finset (CommonIndex C E)) (R : ℝ) (n : Fin 4→ℤ) :
    dyadicRows (liveRows C E U R (OuterFreshRows.outerRows false q x y τ ξ χ₀ Q C E U R)) n=
      (dyadicRows (liveRows C E U R (sourceRows C E U R)) n).filter
        (actualKeep q x τ ξ χ₀ Q C E U R (selectedProduct q y)) := by
  ext z
  simp only [dyadicRows,liveRows,Finset.mem_filter,actualKeep,OuterFreshRows.outerRows,
    Bool.false_eq_true,ite_false]
  tauto

/-- The raw physical kernel on its actual selected-dependent partition
is bounded by exactly the fixed-row masked family consumed by ArtificialSum.
The right inverse ray and negative frequency remain literal. -/
theorem fixed_raw_kernel_masked (q : Data ι) (x : Frozen q) (y : Selected q)
    (r : Source (RestIndex q) a b) (ha : 0<a) (hm : Matches q x r ha)
    (seed : Id) (τ : Character) (ξ χ₀ χ ρ : RayCharacter) (Q : Id)
    (C E : Id) (hC : Supported C) (hE : Supported E)
    (U : Finset (CommonIndex C E)) (ψ : RayCharacter→Character)
    (hψ : SharpFamily τ (frozenProduct q x) ξ C E hC hE U ψ)
    (t θ X Y R : ℝ) (n : Fin 4→ℤ) :
    rawKernelPair τ t (fixedPool q x r seed) (outerColumn q x y seed ξ)
      C E hC hE U χ ρ θ X Y
      (dyadicRows (liveRows C E U R (OuterFreshRows.outerRows false q x y τ ξ χ₀ Q C E U R)) n)≤
      ∑D∈fixedDivisors q x r seed E hE,‖(UniqueFactorizationMonoid.moebius D:ℂ)‖*
        ∑z∈dyadicRows (liveRows C E U R (sourceRows C E U R)) n,
          if actualKeep q x τ ξ χ₀ Q C E U R (selectedProduct q y) z then
            ‖residualWindow false r ha C hC seed D (selectedProduct q y) (ψ χ) t θ X z‖*
            ‖residualWindow true r ha E hE seed D (selectedProduct q y) (ψ (ρ⁻¹)) t θ Y (-z)‖
          else 0 := by
  have he:=fixed_raw_kernel_sharp q x y r ha hm seed τ ξ χ ρ C E hC hE U ψ hψ
    t θ X Y (dyadicRows (liveRows C E U R
      (OuterFreshRows.outerRows false q x y τ ξ χ₀ Q C E U R)) n)
  simpa only [fixed_selected_rows,Finset.sum_filter] using he

end
end Candidate.Feedback.FourthPower.OuterFreshFixedWindows
