/- Copyright (c) 2026 Sil. Apache-2.0.
Canonical outer windows and their actual exceptional principal pair.
The source record is linked by literal input-data equalities only.
Original K, common heights, natural zeros and both cubic twists survive.

-/
import Candidate.FourthPower.OuterFreshPhysical
import Candidate.FourthPower.MixedInnerExceptionalPair

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.OuterFreshWindowPair
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open CompletedGauss ConcretePrimeRowBridge RayFourExpansion CenteredExceptionalProfile
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentChildRows
open CenteredMomentLiveDomain
open CenteredMomentGaussEnergy
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

/-- Literal compatibility with the canonical remaining-slot source.
Every field is equality of original input DATA; there is no estimate.
In particular the original residual puncture is q.R*f, not its radical. -/
structure Matches (q : Data α) (x : Frozen q)
    (s : Source (RestIndex q) a b) (ha : 0<a) : Prop where
  puncture : q.H=punctureProduct s.S s.H
  prefix_eq : q.d=s.d
  punctureR : s.R=q.R*frozenProduct q x
  pool : s.pool=fun j : RestIndex q=>q.pool j.val.val
  coefficient : s.ν=fun j : RestIndex q=>avoid q.u q.ν j.val.val
  slotProfile : s.Wslot=fun j : RestIndex q=>q.Wslot j.val.val
  slotScale : s.P=fun j : RestIndex q=>q.P j.val.val
  leftProfile : q.W₁=normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁
  rightProfile : q.W₂=normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂
  X₁ : q.X₁=s.X₁
  X₂ : q.X₂=s.X₂
  Y₁ : q.Y₁=s.Y₁
  Y₂ : q.Y₂=s.Y₂
  leftPool : q.A=residualPool s.d.1 s.hd.1 (plainSupportPool b s.X₁ s.Y₁)
  rightPool : q.B=residualPool s.d.2 s.hd.2 (plainSupportPool b s.X₂ s.Y₂)

def gate (q : Data α) (x : Frozen q) : ℂ :=
  if IsCoprime (frozenProduct q x) q.R then 1 else 0

theorem common_coefficient (q : Data α) (x : Frozen q)
    (s : Source (RestIndex q) a b) (ha : 0<a) (hm : Matches q x s ha) (seed I : Id) :
    commonColumn q x seed I=gate q x*sourceCoefficient s ha seed I := by
  have hd : q.d.1≠0 ∧ q.d.2≠0 := by simpa only [hm.prefix_eq] using s.hd
  have hA : q.A=residualPool q.d.1 hd.1 (plainSupportPool b q.X₁ q.Y₁) := by
    simpa only [hm.prefix_eq,hm.X₁,hm.Y₁] using hm.leftPool
  have hB : q.B=residualPool q.d.2 hd.2 (plainSupportPool b q.X₂ q.Y₂) := by
    simpa only [hm.prefix_eq,hm.X₂,hm.Y₂] using hm.rightPool
  have he := common_column_original q x seed I s.S s.H hd b hm.puncture hA hB
  simpa only [gate,sourceCoefficient,hm.pool,hm.coefficient,hm.slotProfile,hm.slotScale,
    hm.punctureR,hm.prefix_eq,hm.leftProfile,hm.rightProfile,hm.X₁,hm.X₂,hm.Y₁,hm.Y₂] using he

theorem source_columns_subset (q : Data α) (x : Frozen q)
    (s : Source (RestIndex q) a b) (ha : 0<a) (hm : Matches q x s ha) :
    sourceColumns s⊆commonColumns q := by
  simpa only [sourceColumns,MixedPrincipalAllocations.tuplePools,sourcePools,hm.pool,hm.leftPool,hm.rightPool]
    using remaining_columns_subset q

/-- Canonicalize BEFORE taking common parts. The original tau remains
fixed; both f,D twists stay in the coefficient and the actual gate stays
in front. This is the existing exact supplier identity, with data matched. -/
theorem canonical_polynomial (q : Data α) (x : Frozen q) (y : Selected q)
    (s : Source (RestIndex q) a b) (ha : 0<a) (hm : Matches q x s ha)
    (seed : Id) (τ : Character) (t : ℝ) (ξ : RayCharacter) (k : O) :
    originalPolynomial q x y seed τ t ξ k=
      gate q x*gaussPolynomial Finset.univ (sourceGenerator (sourceColumns s))
        (sourceGenerator_supported (sourceColumns s))
        (fun I : supportedColumns (sourceColumns s)=>sourceCoefficient s ha seed I*
          (idealRowHom (primaryGenerator (frozenProduct q x)) I)^2*
          (idealRowHom (primaryGenerator (selectedProduct q y)) I)^2*
          rayCharacter ξ (primaryGenerator I)*heightCoeff τ t I) k := by
  let F : Id→ℂ := fun I=>(idealRowHom (primaryGenerator (frozenProduct q x)) I)^2*
    (idealRowHom (primaryGenerator (selectedProduct q y)) I)^2*
    rayCharacter ξ (primaryGenerator I)*heightCoeff τ t I*primaryGaussRow I k
  have hsub : sourceColumns s⊆commonColumns q := source_columns_subset q x s ha hm
  have hmem (I : Id) (hn : sourceCoefficient s ha seed I≠0) : I∈sourceColumns s :=
    finite_column_mem _ _ I hn
  have hid (I : Id) : commonColumn q x seed I=gate q x*sourceCoefficient s ha seed I :=
    common_coefficient q x s ha hm seed I
  rw [original_polynomial_source,
    source_gauss_sum (commonColumns q) (fun I=>outerColumn q x y seed ξ I*heightCoeff τ t I) k,
    source_gauss_sum (sourceColumns s) (fun I=>sourceCoefficient s ha seed I*
      (idealRowHom (primaryGenerator (frozenProduct q x)) I)^2*
      (idealRowHom (primaryGenerator (selectedProduct q y)) I)^2*
      rayCharacter ξ (primaryGenerator I)*heightCoeff τ t I) k]
  have hsum : (∑I∈sourceColumns s,sourceCoefficient s ha seed I*F I)=
      ∑I∈commonColumns q,sourceCoefficient s ha seed I*F I := by
    apply Finset.sum_subset hsub
    intro I hI hnot
    have hz : sourceCoefficient s ha seed I=0 := by
      by_contra hn
      exact hnot (hmem I hn)
    rw [hz,zero_mul]
  unfold outerColumn
  simp_rw [hid]
  simp only [mul_assoc]
  simp only [F,mul_assoc] at hsum
  rw [←Finset.mul_sum,←hsum]

theorem canonical_source_polynomial (q : Data α) (x : Frozen q) (y : Selected q)
    (s : Source (RestIndex q) a b) (ha : 0<a) (hm : Matches q x s ha)
    (seed : Id) (τ : Character) (t : ℝ) (ξ : RayCharacter) (k : O) :
    originalPolynomial q x y seed τ t ξ k=
      gaussPolynomial Finset.univ (sourceGenerator (sourceColumns s))
        (sourceGenerator_supported (sourceColumns s))
        (fun I : supportedColumns (sourceColumns s)=>outerColumn q x y seed ξ I*
          heightCoeff τ t I) k := by
  rw [canonical_polynomial q x y s ha hm]
  simp_rw [outerColumn,common_coefficient q x s ha hm seed]
  simp only [gaussPolynomial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  ring

/-- Exact original-K energy on the CANONICAL pool. Standard common-part
and physical decomposition may now be reused without a sector reindex. -/
theorem canonical_source_energy (q : Data α) (x : Frozen q) (y : Selected q)
    (s : Source (RestIndex q) a b) (ha : 0<a) (hm : Matches q x s ha)
    (seed : Id) (τ : Character) (t : ℝ) (ξ : RayCharacter) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (∑'k : O,((‖originalPolynomial q x y seed τ t ξ k‖^2:ℝ):ℂ)*
      Φ (‖ConcreteTraceCRT.eisEmbedding k‖^2/K))=
      sourceGaussEnergy (sourceColumns s) (outerColumn q x y seed ξ) (heightCoeff τ t) Φ K := by
  unfold sourceGaussEnergy gaussEnergy
  apply tsum_congr
  intro k
  rw [canonical_source_polynomial q x y s ha hm]

/-- Literal outer second-Poisson window on the canonical source pool.
The boolean selects the actual conjugate Fourier window on the right. -/
def outerWindow (conjugate : Bool) (q : Data α) (x : Frozen q) (y : Selected q)
    (s : Source (RestIndex q) a b) (seed : Id) (τ : Character)
    (ξ χ : RayCharacter) (A₂ : O) (G : Id) (hG : Supported G) (L : Id)
    (t θ X : ℝ) (z : O) : ℂ :=
  normalization (s.X₁*s.X₂) s.P*
    rowPolynomial Finset.univ (sectorElement G hG.1 (sourceColumns s))
      (fun I=>divisorCoefficient L (sectorElement G hG.1 (sourceColumns s))
        (movingCoefficient A₂ (sectorElement G hG.1 (sourceColumns s))
          (fun J=>outerColumn q x y seed ξ (G*J)*heightCoeff τ t J)) χ I*
        (if conjugate then star (columnPhase logAnnulus
          (Real.log ((I.val.absNorm:ℝ)/X)) θ) else
          columnPhase logAnnulus (Real.log ((I.val.absNorm:ℝ)/X)) θ)) z

theorem outer_coefficient (q : Data α) (x : Frozen q) (y : Selected q)
    (s : Source (RestIndex q) a b) (ha : 0<a) (hm : Matches q x s ha)
    (seed : Id) (τ : Character) (ξ χ : RayCharacter) (A₂ : O)
    (G : Id) (hG : Supported G) (L : Id) (t : ℝ)
    (I : sectorPool G hG.1 (sourceColumns s)) :
    divisorCoefficient L (sectorElement G hG.1 (sourceColumns s))
      (movingCoefficient A₂ (sectorElement G hG.1 (sourceColumns s))
        (fun J=>outerColumn q x y seed ξ (G*J)*heightCoeff τ t J)) χ I=
      (gate q x*twist (primaryGenerator (frozenProduct q x))
        (primaryGenerator (selectedProduct q y)) ξ G)*
      divisorCoefficient L (sectorElement G hG.1 (sourceColumns s))
        (movingCoefficient (A₂*(primaryGenerator (frozenProduct q x))^2*
          (primaryGenerator (selectedProduct q y))^2)
          (sectorElement G hG.1 (sourceColumns s))
          (fun J=>sourceCoefficient s ha seed (G*J)*heightCoeff τ t J)) (ξ*χ) I := by
  simp only [divisorCoefficient,movingCoefficient,sectorElement_span]
  rw [outer_column_extract,common_coefficient q x s ha hm seed (G*I)]
  have hI := sectorPool_supported G hG.1 (sourceColumns s) I
  simp only [sectorElement,twist,rays_product,idealRowHom_argument_mul,
    idealRowHom_argument_pow (primaryGenerator (frozenProduct q x)) 2 I hI,
    idealRowHom_argument_pow (primaryGenerator (selectedProduct q y)) 2 I hI]
  split_ifs <;> ring

theorem outer_window_eq (conjugate : Bool) (q : Data α) (x : Frozen q) (y : Selected q)
    (s : Source (RestIndex q) a b) (ha : 0<a) (hm : Matches q x s ha)
    (seed : Id) (τ : Character) (ξ χ : RayCharacter) (A₂ : O)
    (G : Id) (hG : Supported G) (L : Id) (t θ X : ℝ) (z : O) :
    outerWindow conjugate q x y s seed τ ξ χ A₂ G hG L t θ X z=
      (gate q x*twist (primaryGenerator (frozenProduct q x))
        (primaryGenerator (selectedProduct q y)) ξ G)*
      (if conjugate then conjugateWindow s ha τ (ξ*χ)
        (A₂*(primaryGenerator (frozenProduct q x))^2*(primaryGenerator (selectedProduct q y))^2)
        G hG seed L t θ X z else movingWindow s ha τ (ξ*χ)
        (A₂*(primaryGenerator (frozenProduct q x))^2*(primaryGenerator (selectedProduct q y))^2)
        G hG seed L t θ X z) := by
  unfold outerWindow
  simp_rw [outer_coefficient q x y s ha hm seed τ ξ χ A₂ G hG L t]
  cases conjugate <;> simp only [Bool.false_eq_true,ite_false,ite_true,
    movingWindow,conjugateWindow,mul_assoc,rowPolynomial_factor]
  all_goals ring

theorem factor_norm_le_one (q : Data α) (x : Frozen q) (y : Selected q)
    (ξ : RayCharacter) (G : Id) :
    ‖gate q x*twist (primaryGenerator (frozenProduct q x))
      (primaryGenerator (selectedProduct q y)) ξ G‖≤1 := by
  have hg : ‖gate q x‖≤1 := by unfold gate; split_ifs <;> simp
  have hf := idealRowHom_norm (primaryGenerator (frozenProduct q x)) G
  have hd := idealRowHom_norm (primaryGenerator (selectedProduct q y)) G
  have hr : ‖rayCharacter ξ (primaryGenerator G)‖≤1 := FiniteRayExpansion.norm_char_le_one _ _
  rw [twist,norm_mul,norm_mul,norm_mul,norm_pow,norm_pow]
  have hf2 := pow_le_pow_left₀ (norm_nonneg _) hf 2
  have hd2 := pow_le_pow_left₀ (norm_nonneg _) hd 2
  have hp := mul_le_mul
    (mul_le_mul hf2 hd2 (sq_nonneg _) (by norm_num : (0:ℝ)≤1^2)) hr
    (norm_nonneg _) (by norm_num : (0:ℝ)≤1^2*1^2)
  have hh := mul_le_mul hg hp
    (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (norm_nonneg _)) zero_le_one
  simpa only [one_pow,one_mul] using hh

theorem outer_window_norm_le (conjugate : Bool) (q : Data α)
    (x : Frozen q) (y : Selected q) (s : Source (RestIndex q) a b)
    (ha : 0<a) (hm : Matches q x s ha) (seed : Id) (τ : Character)
    (ξ χ : RayCharacter) (A₂ : O) (G : Id) (hG : Supported G) (L : Id)
    (t θ X : ℝ) (z : O) :
    ‖outerWindow conjugate q x y s seed τ ξ χ A₂ G hG L t θ X z‖≤
      ‖if conjugate then conjugateWindow s ha τ (ξ*χ)
        (A₂*(primaryGenerator (frozenProduct q x))^2*(primaryGenerator (selectedProduct q y))^2)
        G hG seed L t θ X z else movingWindow s ha τ (ξ*χ)
        (A₂*(primaryGenerator (frozenProduct q x))^2*(primaryGenerator (selectedProduct q y))^2)
        G hG seed L t θ X z‖ := by
  rw [outer_window_eq conjugate q x y s ha hm,norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (factor_norm_le_one q x y ξ G)

/-- Canonical full polynomial conductor cap. The R field already equals
q.R*f; the additional f^2,D^2 remain visible. This is not a sharp width. -/
def conductorBudget (q : Data α) (x : Frozen q) (y : Selected q)
    (s : Source (RestIndex q) a b) (τ : Character) (G : Id) (R : ℝ) : ℝ :=
  4*OuterFreshPhysical.fixedConductorCost τ*s.R.absNorm*(frozenProduct q x).absNorm^2*
    (selectedProduct q y).absNorm^2*G.absNorm*MixedInnerExceptionalPair.poolNorm s*R

private theorem conductor_scalar_mono (σ B m n r g l L v f d z R : ℝ)
    (hB : 0≤B) (hm : 0≤m) (hn : 0≤n) (hr : 0≤r) (hg : 0≤g)
    (hl : 0≤l) (hL : 0≤L) (hv : 0≤v) (hz : 0≤z)
    (hs : σ≤B*m*n*(v*f^2*d^2)) (hlL : l≤L) (hvz : v*z≤4*R) :
    σ*m*n*r*g*l*z≤4*(B*m^2*n^2)*r*f^2*d^2*g*L*R := by
  have hupper : 0≤B*m*n*(v*f^2*d^2) := by positivity
  calc
    _≤(B*m*n*(v*f^2*d^2))*m*n*r*g*L*z := by gcongr
    _=(B*m^2*n^2)*r*f^2*d^2*g*L*(v*z) := by ring
    _≤(B*m^2*n^2)*r*f^2*d^2*g*L*(4*R) :=
      mul_le_mul_of_nonneg_left hvz (by positivity)
    _=_ := by ring

theorem canonical_conductor_bound (q : Data α) (x : Frozen q) (y : Selected q)
    (s : Source (RestIndex q) a b) (τ σ : Character) (ξ χ ρ : RayCharacter)
    (hf : Supported (frozenProduct q x)) (hd : Supported (selectedProduct q y))
    (Q C E : Id) (hC : Supported C) (hE : Supported E) (U : Finset (CommonIndex C E))
    (hσ : σ.modulus.absNorm≤HeckeRowClosure.rowConductorBound (childCharacter τ ρ)
      fixedBadMask 1 (OuterFreshPhysical.combinedParameter q x y C E U))
    (G : Id) (R : ℝ) (z : O) (hz : z∈outerRows true q x y τ ξ χ Q C E U R)
    (L : Id) (hL : L∈MixedInnerExceptionalPair.actualDivisors s E hE) :
    (HeckeRowClosure.rowConductorBound σ
      (fixedBadMask*idealGenerator ((s.R*G)*L)) 1 z:ℝ)≤conductorBudget q x y s τ G R ∧
    (HeckeRowClosure.rowConductorBound σ
      (fixedBadMask*idealGenerator ((s.R*G)*L)) 1 (-z):ℝ)≤conductorBudget q x y s τ G R := by
  have hs : (σ.modulus.absNorm:ℝ)≤
      ((childCharacter τ ρ).modulus.absNorm:ℝ)*(Ideal.span {fixedBadMask}).absNorm*
        (Ideal.span {(72:O)}).absNorm*normValue (OuterFreshPhysical.combinedParameter q x y C E U) := by
    have hh : (σ.modulus.absNorm:ℝ)≤(HeckeRowClosure.rowConductorBound (childCharacter τ ρ)
        fixedBadMask 1 (OuterFreshPhysical.combinedParameter q x y C E U):ℝ) := by exact_mod_cast hσ
    simpa only [HeckeRowClosure.rowConductorBound,Ideal.span_singleton_one,
      ←Ideal.one_eq_top,map_one,one_pow,one_mul,Nat.cast_mul,normValue] using hh
  rw [OuterFreshPhysical.combined_norm q x y hf hd C E U] at hs
  have hτ := OuterFreshPhysical.child_modulus_bound τ ρ
  have hnorm : 0≤normValue (oldMoving C E U) := Nat.cast_nonneg _
  have hs' : (σ.modulus.absNorm:ℝ)≤
      ((τ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm)*
        (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
        (normValue (oldMoving C E U)*(Ideal.absNorm (frozenProduct q x):ℝ)^2*
          (Ideal.absNorm (selectedProduct q y):ℝ)^2) := hs.trans (by gcongr)
  have hLn := (MixedInnerExceptionalPair.actual_divisor_norm s E hE L hL).2
  have hzold := OuterFreshPhysical.old_frequency_norm_le true q x y τ ξ χ Q C E hC U R z hz
  have hpool : 0≤MixedInnerExceptionalPair.poolNorm s := Finset.sum_nonneg (fun I _=>Nat.cast_nonneg _)
  have hnz : 0≤normValue z := Nat.cast_nonneg _
  have hbound : (HeckeRowClosure.rowConductorBound σ
      (fixedBadMask*idealGenerator ((s.R*G)*L)) 1 z:ℝ)≤conductorBudget q x y s τ G R := by
    rw [OuterFreshPhysical.full_row_conductor]
    have hh := conductor_scalar_mono (σ.modulus.absNorm:ℝ)
      ((τ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm)
      (Ideal.span {fixedBadMask}).absNorm (Ideal.span {(72:O)}).absNorm
      s.R.absNorm G.absNorm L.absNorm (MixedInnerExceptionalPair.poolNorm s)
      (normValue (oldMoving C E U)) (frozenProduct q x).absNorm
      (selectedProduct q y).absNorm (normValue z) R
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) hpool hnorm hnz hs' hLn hzold
    convert hh using 1 <;> unfold conductorBudget OuterFreshPhysical.fixedConductorCost <;> ring
  refine ⟨hbound,?_⟩
  simpa only [OuterFreshPhysical.full_row_conductor,normValue,Ideal.span_singleton_neg] using hbound

def countCost (q : Data α) (y : Selected q) (Q C E : Id)
    (U : Finset (CommonIndex C E)) (Z Cr M : ℝ) : ℝ :=
  (Ideal.absNorm (commonRadical Q Q):ℝ)^(2/3:ℝ)*
    (768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ)*
      Z^((M-4*Real.logb Z (Ideal.absNorm (oldIdeal C E U):ℝ)-
        4*Real.logb Z (Ideal.absNorm (selectedProduct q y):ℝ))/6))

/-- The complete physical pair retains commonHeight until the estimate.
The two residual windows keep the genuine inverse/right-conjugate choice
explicit in the caller's chi2, and the right frequency is exactly -z. -/
def actualPair (q : Data α) (x : Frozen q) (y : Selected q)
    (s : Source (RestIndex q) a b) (seed : Id) (τ : Character)
    (ξ χ₁ χ₂ : RayCharacter) (C E : Id) (hC : Supported C) (hE : Supported E)
    (U : Finset (CommonIndex C E)) (t θ X Y : ℝ) (rows : Finset O) : ℝ :=
  ‖heightCoeff τ t C*star (heightCoeff τ t E)‖*
    ∑L∈MixedInnerExceptionalPair.actualDivisors s E hE,
      ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*∑z∈rows,
        ‖outerWindow false q x y s seed τ ξ χ₁ (oldMoving C E U) C hC L t θ X z‖*
        ‖outerWindow true q x y s seed τ ξ χ₂ (oldMoving C E U) E hE L t θ Y (-z)‖

private theorem pair_scalar_mono (n N c b d p u v w : ℝ)
    (hnN : n≤N) (hb : b≤d*p) (hc : 0≤c) (hb0 : 0≤b) (hN : 0≤N)
    (hu : 0≤u) (hv : 0≤v) (hw : 0≤w) :
    n*c*b*u*v*w≤(c*d)*N*p*u*v*w := by
  have hm := mul_le_mul (mul_le_mul_of_nonneg_right hnN hc) hb hb0 (mul_nonneg hN hc)
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm hu) hv) hw
  convert hh using 1 <;> ring

/-- Actual outer principal pair. No energy, moment, count, valuation or
rowwise conductor premise remains. The explicit conductorBudget and hR
are scalar polynomial/mesh caps; the original physical K stays arbitrary.
The existing allocation estimate pays every common/divisor cost. -/
theorem uniform_actual_pair (N : ℕ) (saving Bcap a b ε δ : ℝ)
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
      ∀(t radius Cr M K θ X Y : ℝ)(Φ : 𝓢(ℝ,ℂ))(n : Fin 4→ℤ),
      0≤Cr→0<X→0<Y→
      4*radius/(normValue (commonFrequencyGenerator C E)*
        normValue (nonunitFrequencyGenerator C E U))≤Cr*Z^M→
      (heightCoeff τ t C*star (heightCoeff τ t E))*
        physicalBlock τ t (sourceColumns s) (outerColumn q x y seed ξ) C E hC hE U radius
          (outerRows true q x y τ ξ χ Q C E U radius) Φ K n≠0→
      conductorBudget q x y s τ C radius≤Z^Bcap→
      conductorBudget q x y s τ E radius≤Z^Bcap→
      actualPair q x y s seed τ ξ χ₁ χ₂ C E hC hE U t θ X Y
          (outerRows true q x y τ ξ χ Q C E U radius)≤
        A*countCost q y Q C E U Z Cr M*
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
    C E hC hE hCE hsC hsE U t radius Cr M K θ X Y Φ n hCr hX hY hR hphysical hcC hcE
  let rows := outerRows true q x y τ ξ χ Q C E U radius
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
  have hrows : ∀z∈rows,z≠0 := outer_rows_nonzero true q x y τ ξ χ Q C E U radius
  have hind (z : O) (hz : z∈rows) :=
    outer_rows_inducing_rays q x y τ ξ χ χ₁ χ₂ Q C E hQ72 U radius z hz
  have hc₁ (z : O) (hz : z∈rows) (L : Id) (hL : L∈live Ds) :=
    canonical_conductor_bound q x y s τ σ₁ ξ χ (ξ*χ₁) hsupport.1 hsupport.2
      Q C E hC hE U hσ₁ C radius z hz L ((mem_live Ds L).mp hL).1
  have hc₂ (z : O) (hz : z∈rows) (L : Id) (hL : L∈live Ds) :=
    canonical_conductor_bound q x y s τ σ₂ ξ χ (ξ*χ₂) hsupport.1 hsupport.2
      Q C E hC hE U hσ₂ E radius z hz L ((mem_live Ds L).mp hL).1
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
  have hcount : (rows.card:ℝ)≤countCost q y Q C E U Z Cr M :=
    OuterFreshPhysical.full_block_exceptional_count q x y hy seed τ t ξ χ hw
      (sourceColumns s) (source_columns_subset q x s ha hm) C E hC hE hCE U
      Q hQ0 hQtop hQ72 radius Z Cr M hZ hCr hR Φ K n hphysical
  have hb' : pairBudget s hb cover C E J control Z ε saving≤
      Cb*MixedInnerExceptionalPair.paidBudget s C E J control Z ε saving δ := by
    have hh := hbudget (RestIndex q) a b s hb cover hι C E hC.1 hE.1 J control Z ε saving
      (zero_le_one.trans hZ.le) hs
    simpa only [MixedInnerExceptionalPair.paidBudget,mul_assoc,div_eq_mul_inv] using hh
  have hpaid := MixedInnerExceptionalPair.paid_budget_nonneg s C E J control Z ε saving δ
  have hcnt : 0≤countCost q y Q C E U Z Cr M := (Nat.cast_nonneg _).trans hcount
  have hpair := pair_budget_nonneg s hb cover C E J control Z ε saving (zero_le_one.trans hZ.le)
  have hh₁ := (heightCost_pos t θ).le
  have hh₂ := (heightCost_pos t (-θ)).le
  apply (houter.trans hp).trans
  exact pair_scalar_mono (rows.card:ℝ) (countCost q y Q C E U Z Cr M) Cw
    (pairBudget s hb cover C E J control Z ε saving) Cb
    (MixedInnerExceptionalPair.paidBudget s C E J control Z ε saving δ)
    (heightCost t θ^J) (heightCost t (-θ)^J) ((windowMoment J)^2)
    hcount hb' hCw.le hpair hcnt (pow_nonneg hh₁ J) (pow_nonneg hh₂ J)
    (sq_nonneg (windowMoment J))

end
end Candidate.FourthPower.OuterFreshWindowPair
