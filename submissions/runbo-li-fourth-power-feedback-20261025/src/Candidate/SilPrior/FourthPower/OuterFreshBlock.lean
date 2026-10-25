/- Copyright (c) 2026 Sil. Apache-2.0.
Actual outer exceptional physical block with dyadic old+fresh forcing count.
Original K and common heights remain explicit; no K4 transfer occurs here.

-/
import Candidate.SilPrior.FourthPower.OuterFreshWindowPair
import Candidate.SilPrior.FourthPower.MixedInnerExceptionalBlock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.OuterFreshBlock
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open CompletedGauss ConcretePrimeRowBridge RayFourExpansion CenteredExceptionalProfile
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentChildRows
open CenteredMomentGaussEnergy
open CenteredMomentSupport
open CenteredMomentSecondSourceEnergy CenteredMomentOriginalChildEnergy
open CenteredMomentFirstSectors CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentSecondHeightFamily CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalNonunit
open CenteredMomentSectorLocalization CenteredMomentWholeDivisorShell CenteredMomentMobiusRegroup
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentHeckeWindowEnergy
open CenteredMomentExceptionalWholeWindow CenteredMomentRankinRadical
open CenteredMomentCommonProfile CenteredMomentAddedZeroUniform
open CenteredMomentLattice CenteredMomentSourceRectangle CenteredMomentSourceMass
open MixedSupplierFourthRow MixedSupplierSource MixedSupplierOuterActive MixedSupplierCanonical
open MixedSupplierOriginalFrequency MixedSupplierPartition MixedSupplierReconstruction
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations MixedPrincipalBudget
open MixedLiteralAllocation MixedOriginalSource MixedLiveNormalization MixedHeightEnergy
open MixedCommonRestriction
open OuterFreshStructure OuterFreshRows
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
variable {α : Type u} [Fintype α] {a b : ℝ}
local instance {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open OuterFreshWindowPair
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondDyadicRowSupport
open CenteredMomentSecondWholeKernel CenteredMomentSupportedCorrelation
open CenteredMomentCommonSectors CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondIdealBlockBound
open MixedInnerExceptionalBlock (sourceVolume sourceVolume_pos heightBase heightBase_pos
  height_pair_le kernelScale kernelScale_pos)

/-- The row scale is the actual dyadic H, not the full source radius. -/
def dyadicCountCost (q : Data α) (y : Selected q) (Q C E : Id)
    (U : Finset (CommonIndex C E)) (Z : ℝ) (n : Fin 4→ℤ) : ℝ :=
  countCost q y Q C E U Z 1 (Real.logb Z (dyadicScale (n 1)))

theorem actual_dyadic_count (q : Data α) (x : Frozen q) (y : Selected q)
    (hy : Function.Injective y) (seed : Id) (τ : Character) (t : ℝ)
    (ξ χ : RayCharacter) (hw : selectedPositiveWeight q x y τ≠0)
    (S : Finset Id) (hS : S⊆commonColumns q)
    (C E : Id) (hC : Supported C) (hE : Supported E)
    (hCE : primeSupport C=primeSupport E) (U : Finset (CommonIndex C E))
    (Q : Id) (hQ0 : Q≠0) (hQtop : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)})
    (R Z : ℝ) (hZ : 1<Z) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4→ℤ)
    (hne : (heightCoeff τ t C*star (heightCoeff τ t E))*
      physicalBlock τ t S (outerColumn q x y seed ξ) C E hC hE U R
        (outerRows true q x y τ ξ χ Q C E U R) W K n≠0) :
    ((dyadicRows (outerRows true q x y τ ξ χ Q C E U R) n).card:ℝ)≤
      dyadicCountCost q y Q C E U Z n := by
  obtain ⟨I,J,hsector,hpair⟩ := OuterFreshPhysical.exists_pair_of_full_block τ t S
    (outerColumn q x y seed ξ) C E hC hE hCE U R
    (outerRows true q x y τ ξ χ Q C E U R) W K n hne
  have hsupport : supportedColumns S⊆supportedColumns (commonColumns q) := by
    intro I hI
    exact Finset.mem_filter.mpr ⟨hS (Finset.mem_filter.mp hI).1,(Finset.mem_filter.mp hI).2⟩
  have hp := Finset.mem_filter.mp hsector
  have hIJ := Finset.mem_product.mp hp.1
  have hsector' : (I,J)∈pairSector C E (supportedColumns (commonColumns q))
      (supportedColumns (commonColumns q)) :=
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hsupport hIJ.1,hsupport hIJ.2⟩,hp.2⟩
  let fullrows := outerRows true q x y τ ξ χ Q C E U R
  have hh := supplier_count q x y hy seed τ t ξ (ξ*χ) hw C E I J U hsector' hpair
    Q hQ0 hQtop hQ72 fixedBadMask fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _)
    (dyadicRows fullrows n) (dyadicRows_nonzero fullrows n)
    (fun z hz=>outer_rows_inducing q x y τ ξ χ Q C E U R z (dyadicRows_subset fullrows n hz))
    Z 1 (Real.logb Z (dyadicScale (n 1))) hZ (by norm_num)
    (fun z hz=>by simpa only [one_mul] using dyadicRows_power_cap fullrows n Z hZ z hz)
  exact hh

private theorem pair_scalar_mono (n N c b d p u v w : ℝ)
    (hnN : n≤N) (hb : b≤d*p) (hc : 0≤c) (hb0 : 0≤b) (hN : 0≤N)
    (hu : 0≤u) (hv : 0≤v) (hw : 0≤w) :
    n*c*b*u*v*w≤(c*d)*N*p*u*v*w := by
  have hm := mul_le_mul (mul_le_mul_of_nonneg_right hnN hc) hb hb0 (mul_nonneg hN hc)
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm hu) hv) hw
  convert hh using 1 <;> ring

/-- The same actual pair estimate, restricted BEFORE counting to the
dyadic rows. Only scalar polynomial conductor caps remain explicit;
no global-radius substitution replaces the actual dyadic row scale. -/
theorem uniform_dyadic_pair (N : ℕ) (saving Bcap a b ε δ : ℝ)
    (hs : 0≤saving) (hs4 : saving<4/5) (hBcap : 0≤Bcap)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hδ : 0<δ) (hgap : saving+2*δ<1) :
    ∃J : ℕ,∃control : Finset (ℕ×ℕ),(0,0)∈control ∧
      ∀Q : Id,Q≠0→Q≠⊤→Q≤Ideal.span {(72:O)}→∃A : ℝ,0<A ∧
      ∀(κ : Type u) [Fintype κ],∀q : Data κ,∀x : Frozen q,∀y : Selected q,
      Function.Injective y→∀s : Source (RestIndex q) a b,Matches q x s ha→
      ∀cover : OriginalEnclosure s,∀Z : ℝ,1<Z→Fintype.card (RestIndex q)≤N→
      (s.Fhole.absNorm:ℝ)≤Z^Bcap→(∏i,2*s.P i)≤Z^Bcap→
      ∀(seed : Id)(τ : Character)(ξ χ χ₁ χ₂ : RayCharacter),selectedPositiveWeight q x y τ≠0→
      ∀(C E : Id)(hC : Supported C)(hE : Supported E),primeSupport C=primeSupport E→
      seed∣C→seed∣E→∀U : Finset (CommonIndex C E),
      ∀(t radius K θ X Y : ℝ)(Φ : 𝓢(ℝ,ℂ))(n : Fin 4→ℤ),
      0<X→0<Y→
      (heightCoeff τ t C*star (heightCoeff τ t E))*
        physicalBlock τ t (sourceColumns s) (outerColumn q x y seed ξ) C E hC hE U radius
          (outerRows true q x y τ ξ χ Q C E U radius) Φ K n≠0→
      conductorBudget q x y s τ C radius≤Z^Bcap→
      conductorBudget q x y s τ E radius≤Z^Bcap→
      actualPair q x y s seed τ ξ χ₁ χ₂ C E hC hE U t θ X Y
          (dyadicRows (outerRows true q x y τ ξ χ Q C E U radius) n)≤
        A*dyadicCountCost q y Q C E U Z n*
          MixedInnerExceptionalPair.paidBudget s C E J control Z ε saving δ*
          heightCost t θ^J*heightCost t (-θ)^J*(windowMoment J)^2 := by
  obtain ⟨J,control,h00,hwindow⟩ := uniform_original_window_pair N saving Bcap a b ε δ
    hs hs4 hBcap ha hb hε hδ hgap
  obtain ⟨Cb,hCb,hbudget⟩ := uniform_pair_budget N δ hδ
  refine ⟨J,control,h00,?_⟩
  intro Q hQ0 hQtop hQ72
  obtain ⟨Cw,hCw,hwindow⟩ := hwindow Q hQ0
  refine ⟨Cw*Cb,mul_pos hCw hCb,?_⟩
  intro κ instκ q x y hy s hm cover Z hZ hι hF hP seed τ ξ χ χ₁ χ₂ hw
    C E hC hE hCE hsC hsE U t radius K θ X Y Φ n hX hY hphysical hcC hcE
  let fullrows := outerRows true q x y τ ξ χ Q C E U radius
  let rows := dyadicRows fullrows n
  have hsub : rows⊆fullrows := dyadicRows_subset fullrows n
  let Ds := MixedInnerExceptionalPair.actualDivisors s E hE
  let B := OuterFreshPhysical.combinedParameter q x y C E U
  have hsupport := (supported_mul_iff _ _).mp (selected_positive_active q x y τ hw).support
  have hf := supported_primaryGenerator_ne_zero _ hsupport.1
  have hd := supported_primaryGenerator_ne_zero _ hsupport.2
  have hA := old_moving_ne_zero C E hC U
  obtain ⟨σ₁,hσ₁,he₁,ht₁,hi₁⟩ := exists_actual_character τ ξ χ₁ (oldMoving C E U)
    (primaryGenerator (frozenProduct q x)) (primaryGenerator (selectedProduct q y)) hA hf hd
  obtain ⟨σ₂,hσ₂,he₂,ht₂,hi₂⟩ := exists_actual_character τ ξ χ₂ (oldMoving C E U)
    (primaryGenerator (frozenProduct q x)) (primaryGenerator (selectedProduct q y)) hA hf hd
  have hrows : ∀z∈rows,z≠0 := dyadicRows_nonzero fullrows n
  have hind (z : O) (hz : z∈rows) :=
    outer_rows_inducing_rays q x y τ ξ χ χ₁ χ₂ Q C E hQ72 U radius z (hsub hz)
  have hc₁ (z : O) (hz : z∈rows) (L : Id) (hL : L∈live Ds) :=
    canonical_conductor_bound q x y s τ σ₁ ξ χ (ξ*χ₁) hsupport.1 hsupport.2
      Q C E hC hE U hσ₁ C radius z (hsub hz) L ((mem_live Ds L).mp hL).1
  have hc₂ (z : O) (hz : z∈rows) (L : Id) (hL : L∈live Ds) :=
    canonical_conductor_bound q x y s τ σ₂ ξ χ (ξ*χ₂) hsupport.1 hsupport.2
      Q C E hC hE U hσ₂ E radius z (hsub hz) L ((mem_live Ds L).mp hL).1
  have hp := hwindow (RestIndex q) s cover Z hZ.le hι hF hP C E hC hE seed hsC hsE
    τ σ₁ σ₂ (ξ*χ₁) ((ξ*χ₂)⁻¹) B
    (fun I hI _ v=>by simpa only [B,OuterFreshPhysical.combinedParameter] using ht₁ I hI v)
    (fun I hI _ v=>by simpa only [B,OuterFreshPhysical.combinedParameter,inv_inv] using ht₂ I hI v)
    t θ X Y hX hY rows (live Ds) (fun L=>(UniqueFactorizationMonoid.moebius L:ℂ))
    hrows (live_squarefree Ds) (fun L _=>moebius_norm_le_one L)
    (fun z hz L hL=>(hc₁ z hz L hL).1.trans hcC)
    (fun z hz L hL=>(hc₂ z hz L hL).2.trans hcE)
    (fun z hz=>(hi₁ Q z).mpr (hind z hz).1)
    (fun z hz=>(hi₂ Q (-z)).mpr (hind z hz).2)
  simp only [inv_inv] at hp
  have hheight : ‖heightCoeff τ t C*star (heightCoeff τ t E)‖≤1 := by
    rw [norm_mul,norm_star]
    exact (mul_le_mul (CenteredMomentSourceSecondZeroEnergy.heightCoeff_norm_le_one τ t C hC.1)
      (CenteredMomentSourceSecondZeroEnergy.heightCoeff_norm_le_one τ t E hE.1)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have houter : actualPair q x y s seed τ ξ χ₁ χ₂ C E hC hE U t θ X Y rows≤
      ∑L∈live Ds,‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*∑z∈rows,
        ‖movingWindow s ha τ (ξ*χ₁) B C hC seed L t θ X z‖*
        ‖conjugateWindow s ha τ (ξ*χ₂) B E hE seed L t θ Y (-z)‖ := by
    unfold actualPair
    apply (mul_le_of_le_one_left (by positivity) hheight).trans
    rw [sum_norm_moebius_live]
    apply Finset.sum_le_sum
    intro L hL
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Finset.sum_le_sum
    intro z hz
    have hl := outer_window_norm_le false q x y s ha hm seed τ ξ χ₁
      (oldMoving C E U) C hC L t θ X z
    have hr := outer_window_norm_le true q x y s ha hm seed τ ξ χ₂
      (oldMoving C E U) E hE L t θ Y (-z)
    simp only [Bool.false_eq_true,ite_false,ite_true] at hl hr
    exact mul_le_mul hl hr (norm_nonneg _) (norm_nonneg _)
  have hcount : (rows.card:ℝ)≤dyadicCountCost q y Q C E U Z n :=
    actual_dyadic_count q x y hy seed τ t ξ χ hw
      (sourceColumns s) (source_columns_subset q x s ha hm) C E hC hE hCE U
      Q hQ0 hQtop hQ72 radius Z hZ Φ K n hphysical
  have hb' : pairBudget s hb cover C E J control Z ε saving≤
      Cb*MixedInnerExceptionalPair.paidBudget s C E J control Z ε saving δ := by
    have hh := hbudget (RestIndex q) a b s hb cover hι C E hC.1 hE.1 J control Z ε saving
      (zero_le_one.trans hZ.le) hs
    simpa only [MixedInnerExceptionalPair.paidBudget,mul_assoc,div_eq_mul_inv] using hh
  have hpaid := MixedInnerExceptionalPair.paid_budget_nonneg s C E J control Z ε saving δ
  have hcnt : 0≤dyadicCountCost q y Q C E U Z n := (Nat.cast_nonneg _).trans hcount
  have hpair := pair_budget_nonneg s hb cover C E J control Z ε saving (zero_le_one.trans hZ.le)
  have hh₁ := (heightCost_pos t θ).le
  have hh₂ := (heightCost_pos t (-θ)).le
  apply (houter.trans hp).trans
  exact pair_scalar_mono (rows.card:ℝ) (dyadicCountCost q y Q C E U Z n) Cw
    (pairBudget s hb cover C E J control Z ε saving) Cb
    (MixedInnerExceptionalPair.paidBudget s C E J control Z ε saving δ)
    (heightCost t θ^J) (heightCost t (-θ)^J) ((windowMoment J)^2)
    hcount hb' hCw.le hpair hcnt (pow_nonneg hh₁ J) (pow_nonneg hh₂ J)
    (sq_nonneg (windowMoment J))

/-- Raw windows for an arbitrary actual coefficient. Right ray inverse,
right conjugate Fourier window, and right frequency -z are literal. -/
def rawKernelPair (τ : Character) (t : ℝ) (S : Finset Id) (β : Id→ℂ)
    (C E : Id) (hC : Supported C) (hE : Supported E) (U : Finset (CommonIndex C E))
    (χ ρ : RayCharacter) (θ X Y : ℝ) (rows : Finset O) : ℝ :=
  ∑L∈divisorPool Finset.univ (fun I : sectorPool E hE.1 S=>(I:Id)),
    ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*∑z∈rows,
      ‖rowPolynomial Finset.univ (sectorElement C hC.1 S)
        (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
          (movingCoefficient (oldMoving C E U) (sectorElement C hC.1 S)
            (fun J=>β (C*J)*heightCoeff τ t J)) χ I*
          columnPhase logAnnulus (Real.log ((I.val.absNorm:ℝ)/X)) θ) z‖*
      ‖rowPolynomial Finset.univ (sectorElement E hE.1 S)
        (fun I=>divisorCoefficient L (sectorElement E hE.1 S)
          (movingCoefficient (oldMoving C E U) (sectorElement E hE.1 S)
            (fun J=>β (E*J)*heightCoeff τ t J)) (ρ⁻¹) I*
          star (columnPhase logAnnulus (Real.log ((I.val.absNorm:ℝ)/Y)) θ)) (-z)‖

/-- Coefficient-agnostic kernel specialization. There is deliberately no
old A2 inducing premise: classification is used only in the actual pair
estimate. This is the generic upstream whole_kernel_actual_second_pair. -/
theorem unweighted_kernel_bound (Φ : 𝓢(ℝ,ℂ)) (decay J : ℕ) :
    ∃B : ℝ,0≤B ∧
      ∀(τ : Character)(t : ℝ)(S : Finset Id)(β : Id→ℂ)
        (C E : Id)(hC : Supported C)(hE : Supported E),primeSupport C=primeSupport E→
      ∀(U : Finset (CommonIndex C E))(radius : ℝ)(rows : Finset O)(K : ℝ)(n : Fin 4→ℤ),
      ∀Eraw : ℝ,0≤Eraw→
      (∀χ ρ : RayCharacter,∀w : ℝ,
        rawKernelPair τ t S β C E hC hE U χ ρ w (dyadicScale (n 2)) (dyadicScale (n 3)) rows≤
          Eraw*(1+‖w‖)^J)→
      (1+kernelScale n)^decay*‖normalizedBlock τ t S β C E hC hE U radius rows Φ K n‖≤
        B*Eraw := by
  obtain ⟨B,hB,hbound⟩ := whole_kernel_actual_second_pair Φ (fun _=>logAnnulus)
    (fun _=>Real.log 4) (fun _=>Real.log_nonneg (by norm_num))
    (fun _ x hx=>logAnnulus_enclosure x hx) decay J
  refine ⟨B,hB,?_⟩
  intro τ t S β C E hC hE hCE U radius rows K n Eraw hEraw hpair
  have hcopE (I : sectorPool E hE.1 S) :
      IsCoprime (primaryGenerator C*primaryGenerator E) (sectorElement E hE.1 S I) := by
    simpa only [mul_comm] using sectorElement_coprime E C hE hC hCE.symm S I
  have he := hbound (kernelScale n) (kernelScale_pos n) rows Finset.univ Finset.univ
    (primaryGenerator C) (primaryGenerator E) (oldMoving C E U)
    (sectorElement C hC.1 S) (sectorElement E hE.1 S)
    ((supported_span_primaryGenerator_iff C).mpr hC) ((supported_span_primaryGenerator_iff E).mpr hE)
    (sectorElement_supported C hC.1 S) (sectorElement_supported E hE.1 S)
    (primaryGenerator_spec C (supported_primaryGenerator_ne_zero C hC)).2
    (primaryGenerator_spec E (supported_primaryGenerator_ne_zero E hE)).2
    (sectorElement_primary C hC.1 S) (sectorElement_primary E hE.1 S)
    (sectorElement_coprime C E hC hE hCE S) hcopE
    (retainedScalar C E U radius) (fun I=>β (C*I)*heightCoeff τ t I)
    (fun I=>β (E*I)*heightCoeff τ t I)
    (fun I : sectorPool C hC.1 S=>Real.log ((I.val.absNorm:ℝ)/dyadicScale (n 2)))
    (fun I : sectorPool E hE.1 S=>Real.log ((I.val.absNorm:ℝ)/dyadicScale (n 3)))
    (fun _=>Real.log (secondEffectiveScale C E (oldMoving C E U) K/dyadicScale (n 0)))
    (fun z=>Real.log (normValue z/dyadicScale (n 1)))
    (fun z _=>actual_retained_scalar_norm C E hC hE hCE U radius z)
    (fun z _=>logAnnulus_norm _) (fun z _=>logAnnulus_norm _) Eraw hEraw
    (by simpa only [rawKernelPair,sectorElement_span] using hpair)
  have hcop (I : sectorPool C hC.1 S) (J : sectorPool E hE.1 S) :
      IsCoprime (primaryGenerator (I:Id)) (primaryGenerator (J:Id))↔IsCoprime (I:Id) (J:Id) := by
    change IsCoprime (sectorElement C hC.1 S I) (sectorElement E hE.1 S J)↔_
    rw [←Ideal.isCoprime_span_singleton_iff,sectorElement_span,sectorElement_span]
  simpa only [normalizedBlock,kernelScale,oldMoving,sectorElement_span,idealCorrelation,
    primaryGenerator_mul,sectorElement,hcop] using he

/-- Restore raw pair normalization exactly once. The common height is
kept, so its original natural zeros remain available to the forcing count. -/
theorem raw_pair_eq (q : Data α) (x : Frozen q) (y : Selected q)
    (s : Source (RestIndex q) a b) (seed : Id) (τ : Character)
    (ξ χ ρ : RayCharacter) (C E : Id) (hC : Supported C) (hE : Supported E)
    (U : Finset (CommonIndex C E)) (t θ X Y : ℝ) (rows : Finset O) :
    ‖heightCoeff τ t C*star (heightCoeff τ t E)‖*
      rawKernelPair τ t (sourceColumns s) (outerColumn q x y seed ξ)
        C E hC hE U χ ρ θ X Y rows=
      sourceVolume s*actualPair q x y s seed τ ξ χ (ρ⁻¹) C E hC hE U t θ X Y rows := by
  have he : actualPair q x y s seed τ ξ χ (ρ⁻¹) C E hC hE U t θ X Y rows=
      ‖normalization (s.X₁*s.X₂) s.P‖^2*
        (‖heightCoeff τ t C*star (heightCoeff τ t E)‖*
          rawKernelPair τ t (sourceColumns s) (outerColumn q x y seed ξ)
            C E hC hE U χ ρ θ X Y rows) := by
    simp only [actualPair,rawKernelPair,outerWindow,MixedInnerExceptionalPair.actualDivisors,
      sectorElement_span,Bool.false_eq_true,ite_false,ite_true,norm_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro L hL
    apply Finset.sum_congr rfl
    intro z hz
    ring
  rw [he,normalization_sq (s.X₁*s.X₂)
    (mul_pos (s.hL.trans_le s.hX₁) (s.hL.trans_le s.hX₂)) s.P
    (fun i=>zero_lt_one.trans_le (s.hP i))]
  change _=sourceVolume s*((1/sourceVolume s)*_)
  field_simp [(sourceVolume_pos s).ne'] <;> ring

/-- Actual outer physical block at ORIGINAL K. Its count is the sharp
dyadic H^(1/6) times both old forcing and fresh N(D)^(-2/3). No analytic
pair, count, energy, or inducing-row assumption is supplied by the caller. -/
theorem uniform_actual_block (N : ℕ) (saving Bcap a b ε δ : ℝ)
    (hs : 0≤saving) (hs4 : saving<4/5) (hBcap : 0≤Bcap)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hδ : 0<δ) (hgap : saving+2*δ<1) :
    ∃J : ℕ,∃control : Finset (ℕ×ℕ),(0,0)∈control ∧
      ∀(Φ : 𝓢(ℝ,ℂ))(decay : ℕ),∃Ckernel : ℝ,0≤Ckernel ∧
      ∀Q : Id,Q≠0→Q≠⊤→Q≤Ideal.span {(72:O)}→∃A : ℝ,0<A ∧
      ∀(κ : Type u) [Fintype κ],∀q : Data κ,∀x : Frozen q,∀y : Selected q,
      Function.Injective y→∀s : Source (RestIndex q) a b,Matches q x s ha→
      ∀cover : OriginalEnclosure s,∀Z : ℝ,1<Z→Fintype.card (RestIndex q)≤N→
      (s.Fhole.absNorm:ℝ)≤Z^Bcap→(∏i,2*s.P i)≤Z^Bcap→
      ∀(seed : Id)(τ : Character)(ξ χ : RayCharacter),selectedPositiveWeight q x y τ≠0→
      ∀(C E : Id)(hC : Supported C)(hE : Supported E),primeSupport C=primeSupport E→
      seed∣C→seed∣E→∀U : Finset (CommonIndex C E),
      ∀(t radius K : ℝ)(n : Fin 4→ℤ),0<K→
      conductorBudget q x y s τ C radius≤Z^Bcap→conductorBudget q x y s τ E radius≤Z^Bcap→
      (1+kernelScale n)^decay*
        ‖(heightCoeff τ t C*star (heightCoeff τ t E))*
          physicalBlock τ t (sourceColumns s) (outerColumn q x y seed ξ) C E hC hE U radius
            (outerRows true q x y τ ξ χ Q C E U radius) Φ K n‖≤
        outerScalar C E K n*normalizer C E U*
          (Ckernel*(sourceVolume s*A*dyadicCountCost q y Q C E U Z n*
            MixedInnerExceptionalPair.paidBudget s C E J control Z ε saving δ*
            heightBase t^(2*J)*(windowMoment J)^2)) := by
  obtain ⟨J,control,h00,hpair⟩ := uniform_dyadic_pair N saving Bcap a b ε δ
    hs hs4 hBcap ha hb hε hδ hgap
  refine ⟨J,control,h00,?_⟩
  intro Φ decay
  obtain ⟨Ckernel,hCkernel,hkernel⟩ := unweighted_kernel_bound Φ decay (2*J)
  refine ⟨Ckernel,hCkernel,?_⟩
  intro Q hQ0 hQtop hQ72
  obtain ⟨A,hA,hpair⟩ := hpair Q hQ0 hQtop hQ72
  refine ⟨A,hA,?_⟩
  intro κ instκ q x y hy s hm cover Z hZ hι hF hP seed τ ξ χ hw
    C E hC hE hCE hsC hsE U t radius K n hK hcC hcE
  let fullrows := outerRows true q x y τ ξ χ Q C E U radius
  let rows := dyadicRows fullrows n
  let H := heightCoeff τ t C*star (heightCoeff τ t E)
  let Eraw := sourceVolume s*A*dyadicCountCost q y Q C E U Z n*
    MixedInnerExceptionalPair.paidBudget s C E J control Z ε saving δ*
    heightBase t^(2*J)*(windowMoment J)^2
  have ho : 0≤outerScalar C E K n := by unfold outerScalar; positivity
  have hn := (normalizer_pos C E hC U).le
  have hvol := (sourceVolume_pos s).le
  have hpaid := MixedInnerExceptionalPair.paid_budget_nonneg s C E J control Z ε saving δ
  have hcount0 : 0≤dyadicCountCost q y Q C E U Z n := by
    unfold dyadicCountCost countCost
    positivity
  have hheight := (heightBase_pos t).le
  have hEraw : 0≤Eraw := by dsimp only [Eraw]; positivity
  change (1+kernelScale n)^decay*
    ‖H*physicalBlock τ t (sourceColumns s) (outerColumn q x y seed ξ)
      C E hC hE U radius fullrows Φ K n‖≤
    outerScalar C E K n*normalizer C E U*(Ckernel*Eraw)
  by_cases hphysical : H*physicalBlock τ t (sourceColumns s) (outerColumn q x y seed ξ)
      C E hC hE U radius fullrows Φ K n=0
  · rw [hphysical,norm_zero,mul_zero]
    positivity
  have hH : 0<‖H‖ := norm_pos_iff.mpr (left_ne_zero_of_mul hphysical)
  have hrows : ∀z∈rows,z≠0 := dyadicRows_nonzero fullrows n
  have hp (χ₁ χ₂ : RayCharacter) (w : ℝ) :
      actualPair q x y s seed τ ξ χ₁ χ₂ C E hC hE U t w
        (dyadicScale (n 2)) (dyadicScale (n 3)) rows≤
      A*dyadicCountCost q y Q C E U Z n*
        MixedInnerExceptionalPair.paidBudget s C E J control Z ε saving δ*
        heightCost t w^J*heightCost t (-w)^J*(windowMoment J)^2 :=
    hpair κ q x y hy s hm cover Z hZ hι hF hP seed τ ξ χ χ₁ χ₂ hw
      C E hC hE hCE hsC hsE U t radius K w (dyadicScale (n 2)) (dyadicScale (n 3)) Φ n
      (dyadicScale_pos _) (dyadicScale_pos _) hphysical hcC hcE
  have hraw (χ₁ ρ : RayCharacter) (w : ℝ) :
      ‖H‖*rawKernelPair τ t (sourceColumns s) (outerColumn q x y seed ξ)
        C E hC hE U χ₁ ρ w (dyadicScale (n 2)) (dyadicScale (n 3)) rows≤
      Eraw*(1+‖w‖)^(2*J) := by
    change ‖heightCoeff τ t C*star (heightCoeff τ t E)‖*
      rawKernelPair τ t (sourceColumns s) (outerColumn q x y seed ξ)
        C E hC hE U χ₁ ρ w (dyadicScale (n 2)) (dyadicScale (n 3)) rows≤_
    rw [raw_pair_eq]
    have hh := height_pair_le t w J
    have hcoef : 0≤A*dyadicCountCost q y Q C E U Z n*
        MixedInnerExceptionalPair.paidBudget s C E J control Z ε saving δ := by positivity
    calc
      _≤sourceVolume s*(A*dyadicCountCost q y Q C E U Z n*
          MixedInnerExceptionalPair.paidBudget s C E J control Z ε saving δ*
          heightCost t w^J*heightCost t (-w)^J*(windowMoment J)^2) :=
        mul_le_mul_of_nonneg_left (hp χ₁ (ρ⁻¹) w) hvol
      _≤sourceVolume s*(A*dyadicCountCost q y Q C E U Z n*
          MixedInnerExceptionalPair.paidBudget s C E J control Z ε saving δ*
          (heightBase t^(2*J)*(1+‖w‖)^(2*J))*(windowMoment J)^2) := by
        have hh' := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hh hcoef) (sq_nonneg (windowMoment J))
        exact mul_le_mul_of_nonneg_left (by simpa only [mul_assoc] using hh') hvol
      _=_ := by dsimp only [Eraw]; ring
  have hraw' (χ₁ ρ : RayCharacter) (w : ℝ) :
      rawKernelPair τ t (sourceColumns s) (outerColumn q x y seed ξ)
        C E hC hE U χ₁ ρ w (dyadicScale (n 2)) (dyadicScale (n 3)) rows≤
      (Eraw/‖H‖)*(1+‖w‖)^(2*J) := by
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hH).mpr (by simpa only [mul_comm] using hraw χ₁ ρ w)
  have hk := hkernel τ t (sourceColumns s) (outerColumn q x y seed ξ) C E hC hE hCE
    U radius rows K n (Eraw/‖H‖) (div_nonneg hEraw hH.le) hraw'
  have hweighted : (1+kernelScale n)^decay*
      ‖H*normalizedBlock τ t (sourceColumns s) (outerColumn q x y seed ξ)
        C E hC hE U radius rows Φ K n‖≤Ckernel*Eraw := by
    calc
      _=‖H‖*((1+kernelScale n)^decay*
          ‖normalizedBlock τ t (sourceColumns s) (outerColumn q x y seed ξ)
            C E hC hE U radius rows Φ K n‖) := by rw [norm_mul]; ring
      _≤‖H‖*(Ckernel*(Eraw/‖H‖)) := mul_le_mul_of_nonneg_left hk hH.le
      _=Ckernel*Eraw := by field_simp [hH.ne'] <;> ring
  have hphys : ‖H*physicalBlock τ t (sourceColumns s) (outerColumn q x y seed ξ)
      C E hC hE U radius fullrows Φ K n‖=
      outerScalar C E K n*normalizer C E U*
        ‖H*normalizedBlock τ t (sourceColumns s) (outerColumn q x y seed ξ)
          C E hC hE U radius rows Φ K n‖ := by
    rw [physicalBlock_dyadic_rows,
      physicalBlock_eq τ t (sourceColumns s) (outerColumn q x y seed ξ)
        C E hC hE U radius rows hrows Φ K hK n]
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ho,abs_of_nonneg hn]
    ring
  rw [hphys]
  calc
    _=(outerScalar C E K n*normalizer C E U)*
        ((1+kernelScale n)^decay*
          ‖H*normalizedBlock τ t (sourceColumns s) (outerColumn q x y seed ξ)
            C E hC hE U radius rows Φ K n‖) := by ring
    _≤_ := mul_le_mul_of_nonneg_left hweighted (mul_nonneg ho hn)

end
end Candidate.SilPrior.FourthPower.OuterFreshBlock
