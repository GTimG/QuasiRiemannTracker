/- Copyright (c) 2026 Sil. Apache-2.0.
Outer original-frequency physical witnesses and FULL combined conductors.
The actual nonzero term includes the external common height coefficient.
No source/energy estimate or hypothetical pair witness is an input.

-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.OuterFreshRows
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.WholeDivisorShell
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.PrimeScale

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.OuterFreshPhysical
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open CompletedGauss ConcretePrimeRowBridge RayFourExpansion CenteredExceptionalProfile
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentChildRows
open CenteredMomentFirstSectors CenteredMomentCommonSectors CenteredMomentSecondSourceEnergy
open CenteredMomentSecondSectorColumns CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondLiveBlock CenteredMomentSecondEnergySplit
open CenteredMomentSecondHeightFamily
open CenteredMomentSectorLocalization CenteredMomentWholeDivisorShell
open CenteredMomentMobiusRegroup CenteredMomentRankinRadical CenteredMomentFixedRay
open MixedSupplierFourthRow MixedSupplierSource MixedSupplierOuterActive
open MixedSupplierOriginalFrequency OuterFreshStructure OuterFreshRows
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]

/-- The true physical summand retains the common-factor heights outside
physicalBlock. Extracting a witness from the isolated block would lose
the original character's natural zeros at C and E. -/
theorem exists_pair_of_full_block (τ : Character) (t : ℝ)
    (S : Finset Id) (β : Id→ℂ) (C E : Id) (hC : Supported C) (hE : Supported E)
    (hCE : primeSupport C=primeSupport E) (U : Finset (CommonIndex C E))
    (R : ℝ) (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4→ℤ)
    (hne : (heightCoeff τ t C*star (heightCoeff τ t E))*
      physicalBlock τ t S β C E hC hE U R rows W K n≠0) :
    ∃I J : Id,(I,J)∈pairSector C E (supportedColumns S) (supportedColumns S) ∧
      (β I*heightCoeff τ t I)*star (β J*heightCoeff τ t J)≠0 := by
  have hheight := left_ne_zero_of_mul hne
  have hCheight : heightCoeff τ t C≠0 := left_ne_zero_of_mul hheight
  have hEheight : heightCoeff τ t E≠0 := by
    simpa only [star_ne_zero] using right_ne_zero_of_mul hheight
  have hb := right_ne_zero_of_mul hne
  unfold physicalBlock at hb
  obtain ⟨z,hz,hzsum⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
  by_cases hp : canonicalPartition C E U (nonunitFrequencyGenerator C E U*z)
  · simp only [hp,ite_true] at hzsum
    obtain ⟨I,_,hIsum⟩ := Finset.exists_ne_zero_of_sum_ne_zero hzsum
    obtain ⟨J,_,hIJ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hIsum
    have hc : IsCoprime (I:Id) (J:Id) := by
      by_contra hh
      exact hIJ (by simp only [hh,ite_false,zero_mul])
    have hpair := right_ne_zero_of_mul (left_ne_zero_of_mul hIJ)
    have hi : β (C*I)*heightCoeff τ t I≠0 := left_ne_zero_of_mul hpair
    have hj : β (E*J)*heightCoeff τ t J≠0 := by
      simpa only [star_ne_zero] using right_ne_zero_of_mul hpair
    have hi' : β (C*I)*heightCoeff τ t (C*I)≠0 := by
      rw [heightCoeff_mul]
      simpa only [mul_assoc,mul_left_comm,mul_comm] using mul_ne_zero hCheight hi
    have hj' : β (E*J)*heightCoeff τ t (E*J)≠0 := by
      rw [heightCoeff_mul]
      simpa only [mul_assoc,mul_left_comm,mul_comm] using mul_ne_zero hEheight hj
    have hI : C*I.val∈supportedColumns S :=
      (mem_residualPool C hC.1 (supportedColumns S) I.val).mp
        (Finset.mem_filter.mp I.property).1
    have hJ : E*J.val∈supportedColumns S :=
      (mem_residualPool E hE.1 (supportedColumns S) J.val).mp
        (Finset.mem_filter.mp J.property).1
    have hCJ : IsCoprime C J.val :=
      (coprime_of_same_support C E J hC.1 hE.1
        (sectorPool_supported E hE.1 S J).1 hCE).mpr
        (Finset.mem_filter.mp J.property).2
    have hparts := reconstructed_commonParts C E I J hC.1 hE.1
      (sectorPool_supported C hC.1 S I).1 (sectorPool_supported E hE.1 S J).1
      hCE (Finset.mem_filter.mp I.property).2 hCJ hc
    refine ⟨C*I,E*J,Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hI,hJ⟩,hparts⟩,?_⟩
    exact mul_ne_zero hi' (by simpa only [star_ne_zero] using hj')
  · exact False.elim (hzsum (by simp only [hp,ite_false]))

/-- The actual nonzero physical summand supplies all old/fresh forcing
gates. Only the scalar geometric radius estimate remains explicit. -/
theorem full_block_exceptional_count (q : Data α) (x : Frozen q) (y : Selected q)
    (hy : Function.Injective y) (seed : Id) (τ : Character) (t : ℝ)
    (ξ χ : RayCharacter) (hw : selectedPositiveWeight q x y τ≠0)
    (S : Finset Id) (hS : S⊆commonColumns q)
    (C E : Id) (hC : Supported C) (hE : Supported E)
    (hCE : primeSupport C=primeSupport E) (U : Finset (CommonIndex C E))
    (Q : Id) (hQ0 : Q≠0) (hQtop : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)})
    (R Z Cr M : ℝ) (hZ : 1<Z) (hCr : 0≤Cr)
    (hR : 4*R/(normValue (commonFrequencyGenerator C E)*
      normValue (nonunitFrequencyGenerator C E U))≤Cr*Z^M)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4→ℤ)
    (hne : (heightCoeff τ t C*star (heightCoeff τ t E))*
      physicalBlock τ t S (outerColumn q x y seed ξ) C E hC hE U R
        (outerRows true q x y τ ξ χ Q C E U R) W K n≠0) :
    ((outerRows true q x y τ ξ χ Q C E U R).card:ℝ)≤
      (Ideal.absNorm (commonRadical Q Q):ℝ)^(2/3:ℝ)*
        (768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card*
          Cr^(1/6:ℝ)*Z^((M-4*Real.logb Z (Ideal.absNorm (oldIdeal C E U):ℝ)-
            4*Real.logb Z (Ideal.absNorm (selectedProduct q y):ℝ))/6)) := by
  obtain ⟨I,J,hsector,hpair⟩ := exists_pair_of_full_block τ t S
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
  exact actual_exceptional_count q x y hy seed τ t ξ χ hw C E I J U hsector' hpair
    Q hQ0 hQtop hQ72 R Z Cr M hZ hCr hR

/-- A full norm cap for this actual finite pool; this is used only for
polynomial conductor admissibility, never as an analytic source estimate. -/
def poolNorm (q : Data α) : ℝ := ∑I∈commonColumns q,(I.absNorm:ℝ)

def actualDivisors (q : Data α) (G : Id) (hG : Supported G) : Finset Id :=
  divisorPool (Finset.univ : Finset ↥(sectorPool G hG.1 (commonColumns q)))
    (fun I : ↥(sectorPool G hG.1 (commonColumns q))=>
      Ideal.span {sectorElement G hG.1 (commonColumns q) I})

theorem actual_divisor_norm (q : Data α) (G : Id) (hG : Supported G)
    (L : Id) (hL : L∈actualDivisors q G hG) : L≠0 ∧ (L.absNorm:ℝ)≤poolNorm q := by
  apply divisorPool_nonzero_norm
    (Finset.univ : Finset ↥(sectorPool G hG.1 (commonColumns q)))
    (fun I : ↥(sectorPool G hG.1 (commonColumns q))=>
      Ideal.span {sectorElement G hG.1 (commonColumns q) I})
    (fun I _=>(sectorElement_supported G hG.1 (commonColumns q) I).1)
    (poolNorm q) ?_ L hL
  intro I hI
  rw [sectorElement_span]
  have hi : G*I.val∈supportedColumns (commonColumns q) :=
    (mem_residualPool G hG.1 (supportedColumns (commonColumns q)) I.val).mp
      (Finset.mem_filter.mp I.property).1
  have hcap : ((G*I.val).absNorm:ℝ)≤poolNorm q :=
    Finset.single_le_sum (fun J _=>Nat.cast_nonneg _) (Finset.mem_filter.mp hi).1
  exact (CenteredExceptionalCount.norm_le_of_dvd (Finset.mem_filter.mp hi).2.1
    (dvd_mul_left I.val G)).trans hcap

def combinedParameter (q : Data α) (x : Frozen q) (y : Selected q)
    (C E : Id) (U : Finset (CommonIndex C E)) : O :=
  oldMoving C E U*(primaryGenerator (frozenProduct q x))^2*
    (primaryGenerator (selectedProduct q y))^2

theorem combined_norm (q : Data α) (x : Frozen q) (y : Selected q)
    (hf : Supported (frozenProduct q x)) (hd : Supported (selectedProduct q y))
    (C E : Id) (U : Finset (CommonIndex C E)) :
    normValue (combinedParameter q x y C E U)=normValue (oldMoving C E U)*
      (Ideal.absNorm (frozenProduct q x):ℝ)^2*(Ideal.absNorm (selectedProduct q y):ℝ)^2 := by
  simp only [combinedParameter,normValue,←Ideal.span_singleton_mul_span_singleton,
    ←Ideal.span_singleton_pow,primary_span_supported _ hf,primary_span_supported _ hd,
    map_mul,map_pow,Nat.cast_mul,Nat.cast_pow]

/-- The Fourier geometry still uses A2*z at original K. Keeping that
factor gives a uniform bound for ALL rows, not just a chosen witness. -/
theorem old_frequency_norm_le (exceptional : Bool) (q : Data α)
    (x : Frozen q) (y : Selected q) (τ : Character) (ξ χ : RayCharacter)
    (Q C E : Id) (hC : Supported C) (U : Finset (CommonIndex C E))
    (R : ℝ) (z : O) (hz : z∈outerRows exceptional q x y τ ξ χ Q C E U R) :
    normValue (oldMoving C E U)*normValue z≤4*R := by
  have hden : 0<normValue (commonFrequencyGenerator C E)*
      normValue (nonunitFrequencyGenerator C E U) :=
    mul_pos (normValue_pos _ (commonFrequencyGenerator_ne_zero C E hC))
      (normValue_pos _ (nonunitFrequencyGenerator_ne_zero C E hC U))
  have hh := (le_div_iff₀ hden).mp
    (outer_rows_radius exceptional q x y τ ξ χ Q C E U R z hz)
  change normValue z*(normValue (commonFrequencyGenerator C E)*
    normValue (nonunitFrequencyGenerator C E U))≤4*R at hh
  rw [oldMoving,normValue_mul]
  simpa only [mul_comm] using hh

/-- One bad-mask/72 factor comes from the actual character constructor;
one comes from the final artificially masked row. Both are retained. -/
def fixedConductorCost (τ : Character) : ℝ :=
  (τ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm*
    (Ideal.span {fixedBadMask}).absNorm^2*(Ideal.span {(72:O)}).absNorm^2

/-- f^3 includes f from the original puncture q.R*f and f^2 in the
combined moving parameter. D^2 remains explicit. G is C or E. -/
def conductorBudget (q : Data α) (x : Frozen q) (y : Selected q)
    (τ : Character) (G : Id) (R : ℝ) : ℝ :=
  4*fixedConductorCost τ*q.R.absNorm*(frozenProduct q x).absNorm^3*
    (selectedProduct q y).absNorm^2*G.absNorm*poolNorm q*R

theorem full_row_conductor (σ : Character) (F G L : Id) (z : O) :
    (HeckeRowClosure.rowConductorBound σ
      (fixedBadMask*idealGenerator ((F*G)*L)) 1 z:ℝ)=
      (σ.modulus.absNorm:ℝ)*(Ideal.span {fixedBadMask}).absNorm*
        (Ideal.span {(72:O)}).absNorm*F.absNorm*G.absNorm*L.absNorm*normValue z := by
  simp only [HeckeRowClosure.rowConductorBound,←Ideal.span_singleton_mul_span_singleton,
    span_idealGenerator,Ideal.span_singleton_one,←Ideal.one_eq_top,map_one,map_mul,
    one_pow,one_mul,normValue,Nat.cast_mul]
  ring

theorem child_modulus_bound (τ : Character) (ξ : RayCharacter) :
    ((childCharacter τ ξ).modulus.absNorm:ℝ)≤
      (τ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm := by
  exact_mod_cast HeckePrimeScale.product_modulus_bound τ (primaryRayCharacter ξ)

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

/-- This hypothesis is precisely the arithmetic output of
exists_actual_character, not an analytic row/source estimate. -/
theorem presented_conductor_bound (exceptional : Bool) (q : Data α)
    (x : Frozen q) (y : Selected q) (τ σ : Character) (ξ χ ρ : RayCharacter)
    (hf : Supported (frozenProduct q x)) (hd : Supported (selectedProduct q y))
    (Q C E : Id) (hC : Supported C) (U : Finset (CommonIndex C E))
    (hσ : σ.modulus.absNorm≤HeckeRowClosure.rowConductorBound
      (childCharacter τ ρ) fixedBadMask 1 (combinedParameter q x y C E U))
    (G H : Id) (hH : Supported H) (R : ℝ) (z : O)
    (hz : z∈outerRows exceptional q x y τ ξ χ Q C E U R)
    (L : Id) (hL : L∈actualDivisors q H hH) :
    (HeckeRowClosure.rowConductorBound σ
      (fixedBadMask*idealGenerator (((q.R*frozenProduct q x)*G)*L)) 1 z:ℝ)≤
        conductorBudget q x y τ G R ∧
    (HeckeRowClosure.rowConductorBound σ
      (fixedBadMask*idealGenerator (((q.R*frozenProduct q x)*G)*L)) 1 (-z):ℝ)≤
        conductorBudget q x y τ G R := by
  have hσr : (σ.modulus.absNorm:ℝ)≤
      ((childCharacter τ ρ).modulus.absNorm:ℝ)*(Ideal.span {fixedBadMask}).absNorm*
        (Ideal.span {(72:O)}).absNorm*normValue (combinedParameter q x y C E U) := by
    have hh : (σ.modulus.absNorm:ℝ)≤(HeckeRowClosure.rowConductorBound
        (childCharacter τ ρ) fixedBadMask 1 (combinedParameter q x y C E U):ℝ) := by
      exact_mod_cast hσ
    simpa only [HeckeRowClosure.rowConductorBound,Ideal.span_singleton_one,
      ←Ideal.one_eq_top,map_one,one_pow,one_mul,Nat.cast_mul,normValue] using hh
  rw [combined_norm q x y hf hd C E U] at hσr
  have hτ := child_modulus_bound τ ρ
  have hnorm : 0≤normValue (oldMoving C E U) := Nat.cast_nonneg _
  have hσ' : (σ.modulus.absNorm:ℝ)≤
      ((τ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm)*
        (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
        (normValue (oldMoving C E U)*(Ideal.absNorm (frozenProduct q x):ℝ)^2*
          (Ideal.absNorm (selectedProduct q y):ℝ)^2) := hσr.trans (by gcongr)
  have hLn := (actual_divisor_norm q H hH L hL).2
  have hzold := old_frequency_norm_le exceptional q x y τ ξ χ Q C E hC U R z hz
  have hpool : 0≤poolNorm q := Finset.sum_nonneg (fun I _=>Nat.cast_nonneg _)
  have hnz : 0≤normValue z := Nat.cast_nonneg _
  have hbound : (HeckeRowClosure.rowConductorBound σ
      (fixedBadMask*idealGenerator (((q.R*frozenProduct q x)*G)*L)) 1 z:ℝ)≤
      conductorBudget q x y τ G R := by
    rw [full_row_conductor,map_mul,Nat.cast_mul]
    have hh := conductor_scalar_mono (σ.modulus.absNorm:ℝ)
      ((τ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm)
      (Ideal.span {fixedBadMask}).absNorm (Ideal.span {(72:O)}).absNorm
      ((q.R.absNorm:ℝ)*(frozenProduct q x).absNorm) G.absNorm L.absNorm (poolNorm q)
      (normValue (oldMoving C E U)) (frozenProduct q x).absNorm
      (selectedProduct q y).absNorm (normValue z) R
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) hpool hnorm hnz hσ' hLn hzold
    convert hh using 1 <;> unfold conductorBudget fixedConductorCost <;> ring
  refine ⟨hbound,?_⟩
  simpa only [full_row_conductor,normValue,Ideal.span_singleton_neg] using hbound

/-- The combined character is constructed, and its full polynomial
conductor bounds hold on the actual divisor pool for both signs. No
character, rowwise conductor, or exceptional-count existence is assumed. -/
theorem exists_outer_character (exceptional : Bool) (q : Data α)
    (x : Frozen q) (y : Selected q) (τ : Character) (ξ χ ρ : RayCharacter)
    (hw : selectedPositiveWeight q x y τ≠0) (Q C E : Id) (hC : Supported C)
    (U : Finset (CommonIndex C E)) (G H : Id) (hH : Supported H) (R : ℝ) :
    ∃σ : Character,
      (∀I : Id,Supported I→∀t : ℝ,heightCoeff σ t I=
        heightCoeff τ t I*idealRowHom (combinedParameter q x y C E U) I*
          rayCharacter (ξ*ρ) (primaryGenerator I)) ∧
      (∀Q' : Id,∀z : O,FixedInducingRow σ Q' fixedBadMask 1 z↔
        FixedInducingRow (childCharacter τ (ξ*ρ)) Q' fixedBadMask
          (combinedParameter q x y C E U) z) ∧
      (∀z∈outerRows exceptional q x y τ ξ χ Q C E U R,
        ∀L∈actualDivisors q H hH,
          (HeckeRowClosure.rowConductorBound σ
            (fixedBadMask*idealGenerator (((q.R*frozenProduct q x)*G)*L)) 1 z:ℝ)≤
              conductorBudget q x y τ G R ∧
          (HeckeRowClosure.rowConductorBound σ
            (fixedBadMask*idealGenerator (((q.R*frozenProduct q x)*G)*L)) 1 (-z):ℝ)≤
              conductorBudget q x y τ G R) := by
  have hs := (supported_mul_iff _ _).mp (selected_positive_active q x y τ hw).support
  obtain ⟨σ,hσ,he,ht,hi⟩ := exists_actual_character τ ξ ρ (oldMoving C E U)
    (primaryGenerator (frozenProduct q x)) (primaryGenerator (selectedProduct q y))
    (old_moving_ne_zero C E hC U) (supported_primaryGenerator_ne_zero _ hs.1)
    (supported_primaryGenerator_ne_zero _ hs.2)
  refine ⟨σ,ht,hi,?_⟩
  intro z hz L hL
  exact presented_conductor_bound exceptional q x y τ σ ξ χ (ξ*ρ) hs.1 hs.2
    Q C E hC U hσ G H hH R z hz L hL

/-- Both inputs for the existing uniform principal window-pair theorem:
actual combined height presentations, FULL masked conductors, and the
actual exceptional predicates at z and -z. These are all derived here;
the subsequent source/pool dictionary is a separate exact finite identity. -/
theorem exists_outer_pair_characters (q : Data α) (x : Frozen q) (y : Selected q)
    (τ : Character) (ξ χ χ₁ χ₂ : RayCharacter)
    (hw : selectedPositiveWeight q x y τ≠0) (Q C E : Id)
    (hQ72 : Q≤Ideal.span {(72:O)}) (hC : Supported C) (hE : Supported E)
    (U : Finset (CommonIndex C E)) (R : ℝ) :
    ∃σ₁ σ₂ : Character,
      (∀I : Id,Supported I→∀t : ℝ,heightCoeff σ₁ t I=
        heightCoeff τ t I*idealRowHom (combinedParameter q x y C E U) I*
          rayCharacter (ξ*χ₁) (primaryGenerator I)) ∧
      (∀I : Id,Supported I→∀t : ℝ,heightCoeff σ₂ t I=
        heightCoeff τ t I*idealRowHom (combinedParameter q x y C E U) I*
          rayCharacter (ξ*χ₂) (primaryGenerator I)) ∧
      (∀z∈outerRows true q x y τ ξ χ Q C E U R,
        FixedInducingRow σ₁ Q fixedBadMask 1 z ∧
        FixedInducingRow σ₂ Q fixedBadMask 1 (-z)) ∧
      (∀z∈outerRows true q x y τ ξ χ Q C E U R,
        ∀L∈actualDivisors q E hE,
          (HeckeRowClosure.rowConductorBound σ₁
            (fixedBadMask*idealGenerator (((q.R*frozenProduct q x)*C)*L)) 1 z:ℝ)≤
              conductorBudget q x y τ C R ∧
          (HeckeRowClosure.rowConductorBound σ₂
            (fixedBadMask*idealGenerator (((q.R*frozenProduct q x)*E)*L)) 1 (-z):ℝ)≤
              conductorBudget q x y τ E R) := by
  obtain ⟨σ₁,ht₁,hi₁,hc₁⟩ := exists_outer_character true q x y τ ξ χ χ₁ hw
    Q C E hC U C E hE R
  obtain ⟨σ₂,ht₂,hi₂,hc₂⟩ := exists_outer_character true q x y τ ξ χ χ₂ hw
    Q C E hC U E E hE R
  refine ⟨σ₁,σ₂,ht₁,ht₂,?_,?_⟩
  · intro z hz
    have hh := outer_rows_inducing_rays q x y τ ξ χ χ₁ χ₂ Q C E hQ72 U R z hz
    exact ⟨(hi₁ Q z).mpr hh.1,(hi₂ Q (-z)).mpr hh.2⟩
  · intro z hz L hL
    exact ⟨(hc₁ z hz L hL).1,(hc₂ z hz L hL).2⟩

end
end Candidate.FourthPower.OuterFreshPhysical
