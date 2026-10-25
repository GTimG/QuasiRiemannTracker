/- Copyright (c) 2026 Sil. Apache-2.0.
Outer retained-energy assembly at the original physical K.
All old forcing, fresh-D savings and original prefix costs survive.

-/
import Candidate.SilPrior.FourthPower.OuterFreshBlock
import Candidate.SilPrior.FourthPower.MixedInnerExceptionalLedger

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.OuterFreshAssembly
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion ConcretePrimeRowBridge CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondPhysicalLedger
open CenteredMomentSectorLocalization CenteredMomentRankinRadical
open CenteredMomentFirstCanonicalAllowance CenteredMomentSecondEnergySplit
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentLattice
open CenteredMomentSecondBlockHarmonicMass CenteredMomentSecondBlockRadicalHarmonicMass
open CenteredMomentSecondActiveCount CenteredMomentActiveSource
open CenteredMomentSecondExceptionalAggregate CenteredMomentSecondLiveBlock
open CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondLocalization
open CenteredMomentSecondActivePhysicalDictionary
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget
open QRH.Record1252270103KernelMass (pairNorm pairNorm_pos)
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedPrincipalBudget
open MixedInnerExceptionalPair MixedInnerExceptionalBlock MixedPrincipalCentered
open MixedPrincipalPoolCaps MixedOriginalTail MixedOriginalTailCaps
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

open MixedSupplierFourthRow MixedSupplierSource MixedSupplierOriginalFrequency
open MixedSupplierOuterActive OuterFreshStructure OuterFreshRows OuterFreshWindowPair
open MixedInnerExceptionalLedger
local notation "Nouter" => OuterFreshBlock.dyadicCountCost

theorem outer_coefficient_nonzero (q : Data ι) (x : Frozen q) (y : Selected q)
    (s : Source (RestIndex q) a b) (ha : 0<a) (hm : Matches q x s ha)
    (seed : Id) (ξ : RayCharacter) (I : Id)
    (hne : outerColumn q x y seed ξ I≠0) : sourceCoefficient s ha seed I≠0 := by
  have hc : commonColumn q x seed I≠0 :=
    left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hne))
  rw [common_coefficient q x s ha hm seed I] at hc
  exact right_ne_zero_of_mul hc

/-- The actual full supplier coefficient preserves original support and
seed information before any estimate of its modulus is made. -/
theorem outer_lower_seed (q : Data ι) (x : Frozen q) (y : Selected q)
    (s : Source (RestIndex q) a b) (ha : 0<a) (hm : Matches q x s ha)
    (seed : Id) (ξ : RayCharacter) (I : Id)
    (hne : outerColumn q x y seed ξ I≠0) :
    (a^2/pairNorm s.d)*sourceVolume s≤(I.absNorm:ℝ) ∧ seed∣I := by
  have hh := outer_coefficient_nonzero q x y s ha hm seed ξ I hne
  exact ⟨source_coefficient_lower s ha seed I hh,source_coefficient_seed s ha seed I hh⟩

def freshGain (q : Data ι) (y : Selected q) : ℝ :=
  1/(Ideal.absNorm (selectedProduct q y):ℝ)^(2/3:ℝ)

theorem freshGain_nonneg (q : Data ι) (y : Selected q) : 0≤freshGain q y := by
  unfold freshGain
  positivity

/-- Exact old+fresh count separation. The OLD forcing denominator remains
inside dyadicCountCost; only the additional fresh D factor is taken out. -/
theorem dyadic_count_factor (q : Data ι) (y : Selected q) (hy : Function.Injective y)
    (Q C E : Id) (U : Finset (CommonIndex C E)) (Z : ℝ) (hZ : 1<Z) (n : Fin 4→ℤ) :
    Nouter q y Q C E U Z n=
      MixedInnerExceptionalBlock.dyadicCountCost Q C E U Z n*freshGain q y := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have hd : 0<(Ideal.absNorm (selectedProduct q y):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (selected_squarefree q y hy).ne_zero)
  have hp : Z^((Real.logb Z (dyadicScale (n 1))-
      4*Real.logb Z (forcingNorm C E U)-
      4*Real.logb Z (Ideal.absNorm (selectedProduct q y):ℝ))/6)=
      Z^((Real.logb Z (dyadicScale (n 1))-4*Real.logb Z (forcingNorm C E U))/6)/
        (Ideal.absNorm (selectedProduct q y):ℝ)^(2/3:ℝ) := by
    rw [show (Real.logb Z (dyadicScale (n 1))-4*Real.logb Z (forcingNorm C E U)-
        4*Real.logb Z (Ideal.absNorm (selectedProduct q y):ℝ))/6=
        (Real.logb Z (dyadicScale (n 1))-4*Real.logb Z (forcingNorm C E U))/6-
          Real.logb Z (Ideal.absNorm (selectedProduct q y):ℝ)*(2/3) by ring,
      Real.rpow_sub hz _ _,Real.rpow_mul hz.le,
      Real.rpow_logb hz (ne_of_gt hZ) hd]
  unfold OuterFreshBlock.dyadicCountCost OuterFreshWindowPair.countCost
    MixedInnerExceptionalBlock.dyadicCountCost freshGain
  change (Ideal.absNorm (commonRadical Q Q):ℝ)^(2/3:ℝ)*
    (768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card*1^(1/6:ℝ)*
      Z^((Real.logb Z (dyadicScale (n 1))-4*Real.logb Z (forcingNorm C E U)-
        4*Real.logb Z (Ideal.absNorm (selectedProduct q y):ℝ))/6))=_
  rw [Real.one_rpow,mul_one,hp]
  ring

/-- Coefficient-agnostic old physical ledger, instantiated on the actual
outer source. Neither twist can create a new supported column. -/
theorem outer_source_common_cost (q : Data ι) (x : Frozen q) (y : Selected q)
    (s : Source (RestIndex q) a b) (ha : 0<a) (hm : Matches q x s ha)
    (τ : Character) (t : ℝ) (seed : Id) (ξ : RayCharacter)
    (C E : Id) (hC : Supported C) (hE : Supported E) (hCE : primeSupport C=primeSupport E)
    (U : Finset (CommonIndex C E)) (radius : ℝ) (rows : Finset O) (hrows : ∀z∈rows,z≠0)
    (Φ : 𝓢(ℝ,ℂ)) (K Z saving δ : ℝ) (hK : 0<K) (hZ : 1<Z)
    (hs : (2/3:ℝ)≤saving) (n : Fin 4→ℤ)
    (hne : physicalBlock τ t (sourceColumns s) (outerColumn q x y seed ξ)
      C E hC hE U radius rows Φ K n≠0) :
    centralPhysicalCost C E U K (sourceVolume s) n*
        (C.absNorm:ℝ)^δ*(E.absNorm:ℝ)^δ*min (commonSaving s C saving) (commonSaving s E saving)≤
      commonPhysicalCost s K*(C.absNorm:ℝ)^δ*(E.absNorm:ℝ)^δ := by
  have hc : 0<(C.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have he : 0<(E.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hE.1)
  have hlog : Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (E.absNorm:ℝ))/3)=
      ((C.absNorm:ℝ)*E.absNorm)^(-1/3:ℝ) := by
    rw [show -(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (E.absNorm:ℝ))/3=
      Real.logb Z ((C.absNorm:ℝ)*E.absNorm)*(-1/3) by
        rw [Real.logb_mul hc.ne' he.ne']; ring,
      Real.rpow_mul (zero_lt_one.trans hZ).le,
      Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) (mul_pos hc he)]
  have hcost := original_block_physical_cost τ t (sourceColumns s) (outerColumn q x y seed ξ)
    C E hC hE hCE U radius rows hrows Φ K n hK (sourceVolume s) (a^2/pairNorm s.d) Z
    (sourceVolume_pos s) (div_pos (sq_pos_of_pos ha) (pairNorm_pos s.hd.1 s.hd.2)) hZ
    (fun I hI=>(outer_lower_seed q x y s ha hm seed ξ I hI).1) hne
  rw [hlog] at hcost
  have hsave := common_pair_saving_norm s C E hC.1 hE.1 saving hs
  have hmin : 0≤min (commonSaving s C saving) (commonSaving s E saving) :=
    le_min (commonSaving_nonneg s C saving) (commonSaving_nonneg s E saving)
  have hfac : 0≤(sourceVolume s)^(1/3:ℝ)*K^(5/6:ℝ)*(a^2/pairNorm s.d)^(-2/3:ℝ)*
      (C.absNorm:ℝ)^δ*(E.absNorm:ℝ)^δ := by
    have hv := (sourceVolume_pos s).le
    have hd := (pairNorm_pos s.hd.1 s.hd.2).le
    positivity
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcost (Real.rpow_nonneg hc.le δ))
      (Real.rpow_nonneg he.le δ)) hmin
  calc
    _≤((sourceVolume s)^(1/3:ℝ)*K^(5/6:ℝ)*(a^2/pairNorm s.d)^(-2/3:ℝ)*
        (C.absNorm:ℝ)^δ*(E.absNorm:ℝ)^δ)*
        (((C.absNorm:ℝ)*E.absNorm)^(-1/3:ℝ)*
          min (commonSaving s C saving) (commonSaving s E saving)) := by
      convert hh using 1 <;> ring
    _≤((sourceVolume s)^(1/3:ℝ)*K^(5/6:ℝ)*(a^2/pairNorm s.d)^(-2/3:ℝ)*
        (C.absNorm:ℝ)^δ*(E.absNorm:ℝ)^δ)*(s.L/prefixNormMax s.d)^(-2/3:ℝ) :=
      mul_le_mul_of_nonneg_left hsave hfac
    _=_ := by unfold commonPhysicalCost; ring

/-- The old common-physical calculation applies to the actual outer
coefficient; its numerical forcing cost remains present until bounded by one. -/
theorem old_budget_outer_saving (q : Data ι) (x : Frozen q) (y : Selected q)
    (s : Source (RestIndex q) a b) (ha : 0<a) (hm : Matches q x s ha)
    (J : ℕ) (control : Finset (ℕ×ℕ)) (Q : Id) (τ : Character) (t : ℝ)
    (seed : Id) (ξ : RayCharacter)
    (C E : Id) (hC : Supported C) (hE : Supported E) (hCE : primeSupport C=primeSupport E)
    (U : Finset (CommonIndex C E)) (radius : ℝ) (rows : Finset O) (hrows : ∀z∈rows,z≠0)
    (Φ : 𝓢(ℝ,ℂ)) (K Z ε saving δ : ℝ) (hK : 0<K) (hZ : 1<Z)
    (hs : (2/3:ℝ)≤saving) (n : Fin 4→ℤ)
    (hne : physicalBlock τ t (sourceColumns s) (outerColumn q x y seed ξ)
      C E hC hE U radius rows Φ K n≠0) :
    (1/sourceVolume s)*outerScalar C E K n*normalizer C E U*
      (sourceVolume s*MixedInnerExceptionalBlock.dyadicCountCost Q C E U Z n*
        paidBudget s C E J control Z ε saving δ)/(1+kernelScale n)≤
      sourcePrefactor s J control Q Z ε*commonPhysicalCost s K*
        (C.absNorm:ℝ)^δ*(E.absNorm:ℝ)^δ/(Ideal.absNorm (commonRadical C E):ℝ) := by
  have hcost := outer_source_common_cost q x y s ha hm τ t seed ξ C E hC hE hCE U
    radius rows hrows Φ K Z saving δ hK hZ hs n hne
  have hp := sourcePrefactor_nonneg s J control Q Z ε
  have hphys := commonPhysicalCost_nonneg s K hK.le
  have hr : 0<(Ideal.absNorm (commonRadical C E):ℝ) := by
    rw [←common_ideal_product]
    exact common_product_pos C E hC Finset.univ
  have hf := forcing_third_ge_one C E hC U
  have hnum : 0≤sourcePrefactor s J control Q Z ε*commonPhysicalCost s K*
      (C.absNorm:ℝ)^δ*(E.absNorm:ℝ)^δ := by positivity
  rw [central_budget_exact s J control Q C E hC hE U Z ε saving δ K hZ n]
  calc
    _≤sourcePrefactor s J control Q Z ε*
        (commonPhysicalCost s K*(C.absNorm:ℝ)^δ*(E.absNorm:ℝ)^δ)/
        ((Ideal.absNorm (commonRadical C E):ℝ)*(forcingNorm C E U)^(1/3:ℝ)) := by
      apply div_le_div_of_nonneg_right _ (mul_nonneg hr.le (zero_le_one.trans hf))
      exact mul_le_mul_of_nonneg_left hcost hp
    _=(sourcePrefactor s J control Q Z ε*commonPhysicalCost s K*
        (C.absNorm:ℝ)^δ*(E.absNorm:ℝ)^δ)/
        ((Ideal.absNorm (commonRadical C E):ℝ)*(forcingNorm C E U)^(1/3:ℝ)) := by ring
    _≤_ := div_le_div_of_nonneg_left hnum hr (by nlinarith)

def outerSavedBudget (q : Data ι) (y : Selected q) (s : Source (RestIndex q) a b)
    (J : ℕ) (control : Finset (ℕ×ℕ)) (Q : Id) (Z ε K : ℝ) : ℝ :=
  sourcePrefactor s J control Q Z ε*commonPhysicalCost s K*freshGain q y

theorem outerSavedBudget_nonneg (q : Data ι) (y : Selected q)
    (s : Source (RestIndex q) a b) (J : ℕ) (control : Finset (ℕ×ℕ))
    (Q : Id) (Z ε K : ℝ) (hK : 0≤K) : 0≤outerSavedBudget q y s J control Q Z ε K :=
  mul_nonneg (mul_nonneg (sourcePrefactor_nonneg s J control Q Z ε)
    (commonPhysicalCost_nonneg s K hK)) (freshGain_nonneg q y)

/-- Full actual common-height block at ORIGINAL K. The additional D saving
survives the old physical normalization; neither K4 nor a second 1/W occurs. -/
theorem uniform_saved_actual_block (N : ℕ) (saving Bcap a b ε δ : ℝ)
    (hs : (2/3:ℝ)≤saving) (hs4 : saving<4/5) (hBcap : 0≤Bcap)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hδ : 0<δ) (hgap : saving+2*δ<1) :
    ∃J : ℕ,∃control : Finset (ℕ×ℕ),(0,0)∈control ∧
      ∀Φ : 𝓢(ℝ,ℂ),∃Ckernel : ℝ,0≤Ckernel ∧
      ∀Q : Id,Q≠0→Q≠⊤→Q≤Ideal.span {(72:O)}→∃A : ℝ,0<A ∧
      ∀(κ : Type u) [Fintype κ],∀q : Data κ,∀x : Frozen q,∀y : Selected q,
      Function.Injective y→∀s : Source (RestIndex q) a b,Matches q x s ha→
      ∀cover : OriginalEnclosure s,∀Z : ℝ,1<Z→Fintype.card (RestIndex q)≤N→
      (s.Fhole.absNorm:ℝ)≤Z^Bcap→(∏i,2*s.P i)≤Z^Bcap→
      ∀(seed : Id)(τ : Character)(ξ χ : RayCharacter),selectedPositiveWeight q x y τ≠0→
      ∀(C E : Id)(hC : Supported C)(hE : Supported E),primeSupport C=primeSupport E→
      seed∣C→seed∣E→∀U : Finset (CommonIndex C E),
      ∀(t radius K : ℝ)(n : Fin 4→ℤ),0<K→
      OuterFreshWindowPair.conductorBudget q x y s τ C radius≤Z^Bcap→
      OuterFreshWindowPair.conductorBudget q x y s τ E radius≤Z^Bcap→
      ‖(heightCoeff τ t C*star (heightCoeff τ t E))*
          physicalBlock τ t (sourceColumns s) (outerColumn q x y seed ξ) C E hC hE U radius
            (outerRows true q x y τ ξ χ Q C E U radius) Φ K n‖/sourceVolume s≤
        (Ckernel*A*heightBase t^(2*J)*(windowMoment J)^2)*
          outerSavedBudget q y s J control Q Z ε K*(C.absNorm:ℝ)^δ*(E.absNorm:ℝ)^δ/
            (Ideal.absNorm (commonRadical C E):ℝ) := by
  obtain ⟨J,control,h00,hkernel⟩ := OuterFreshBlock.uniform_actual_block N saving Bcap a b ε δ
    (by linarith) hs4 hBcap ha hb hε hδ hgap
  refine ⟨J,control,h00,?_⟩
  intro Φ
  obtain ⟨Ckernel,hCkernel,hbound⟩ := hkernel Φ 1
  refine ⟨Ckernel,hCkernel,?_⟩
  intro Q hQ0 hQt hQ72
  obtain ⟨A,hA,hblock⟩ := hbound Q hQ0 hQt hQ72
  refine ⟨A,hA,?_⟩
  intro κ instκ q x y hy s hm cover Z hZ hι hF hP seed τ ξ χ hw
    C E hC hE hCE hsC hsE U t radius K n hK hcC hcE
  let F := (heightCoeff τ t C*star (heightCoeff τ t E))*
    physicalBlock τ t (sourceColumns s) (outerColumn q x y seed ξ) C E hC hE U radius
      (outerRows true q x y τ ξ χ Q C E U radius) Φ K n
  let D := Ckernel*A*heightBase t^(2*J)*(windowMoment J)^2
  have hD : 0≤D := by
    have ht := (heightBase_pos t).le
    dsimp only [D]
    positivity
  have hsave := outerSavedBudget_nonneg q y s J control Q Z ε K hK.le
  by_cases hzero : F=0
  · change ‖F‖/_≤_
    rw [hzero,norm_zero,zero_div]
    change 0≤D*outerSavedBudget q y s J control Q Z ε K*
      (C.absNorm:ℝ)^δ*(E.absNorm:ℝ)^δ/_
    positivity
  have hb := hblock κ q x y hy s hm cover Z hZ hι hF hP seed τ ξ χ hw
    C E hC hE hCE hsC hsE U t radius K n hK hcC hcE
  have hcost := old_budget_outer_saving q x y s ha hm J control Q τ t seed ξ
    C E hC hE hCE U radius (outerRows true q x y τ ξ χ Q C E U radius)
    (outer_rows_nonzero true q x y τ ξ χ Q C E U radius) Φ K Z ε saving δ hK hZ hs n
    (right_ne_zero_of_mul hzero)
  have hv := sourceVolume_pos s
  have hk : 0<1+kernelScale n := by linarith [kernelScale_pos n]
  have hb' : ‖F‖/sourceVolume s≤
      D*((1/sourceVolume s)*outerScalar C E K n*normalizer C E U*
        (sourceVolume s*Nouter q y Q C E U Z n*paidBudget s C E J control Z ε saving δ)/
          (1+kernelScale n)) := by
    have hf : ‖F‖≤outerScalar C E K n*normalizer C E U*
        (Ckernel*(sourceVolume s*A*Nouter q y Q C E U Z n*
          paidBudget s C E J control Z ε saving δ*heightBase t^(2*J)*(windowMoment J)^2))/
          (1+kernelScale n) := by
      apply (le_div_iff₀ hk).mpr
      simpa only [pow_one,F,mul_comm,mul_left_comm,mul_assoc] using hb
    convert div_le_div_of_nonneg_right hf hv.le using 1 <;> dsimp only [D] <;> ring
  apply hb'.trans
  rw [dyadic_count_factor q y hy Q C E U Z hZ n]
  calc
    _=D*((1/sourceVolume s)*outerScalar C E K n*normalizer C E U*
        (sourceVolume s*MixedInnerExceptionalBlock.dyadicCountCost Q C E U Z n*
          paidBudget s C E J control Z ε saving δ)/(1+kernelScale n))*freshGain q y := by ring
    _≤D*(sourcePrefactor s J control Q Z ε*commonPhysicalCost s K*
        (C.absNorm:ℝ)^δ*(E.absNorm:ℝ)^δ/(Ideal.absNorm (commonRadical C E):ℝ))*freshGain q y :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcost hD) (freshGain_nonneg q y)
    _=_ := by unfold outerSavedBudget; ring

/-- Actual retained energy with the NEW combined A2*f²*D² split. The
finite labels, divisor allocations and dyadic blocks are those of the
original physical source; its common-height coefficient is unchanged. -/
def outerPartEnergy (exceptional : Bool) (q : Data ι) (x : Frozen q) (y : Selected q)
    (s : Source (RestIndex q) a b) (seed : Id) (τ : Character) (ξ χ : RayCharacter)
    (Q : Id) (t : ℝ) (Φ : 𝓢(ℝ,ℂ)) (K Tsec Z ζ Hsource : ℝ) : ℂ :=
  let S := sourceColumns s
  let β := outerColumn q x y seed ξ
  ∑p∈liveLabels τ S β,heightCoeff τ t p.val.1*star (heightCoeff τ t p.val.2)*
    ∑U : Finset (CommonIndex p.val.1 p.val.2),
      ∑n : SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ζ) Hsource,
        physicalBlock τ t (activeSource S β) β p.val.1 p.val.2
          (commonLabels_supported (activeSource S β) _ _ p.property).1
          (commonLabels_supported (activeSource S β) _ _ p.property).2 U
          (frequencyRadius Tsec Z ζ)
          (outerRows exceptional q x y τ ξ χ Q p.val.1 p.val.2 U (frequencyRadius Tsec Z ζ))
          Φ K (fun i=>(n i:ℤ))

theorem retained_energy_split (q : Data ι) (x : Frozen q) (y : Selected q)
    (s : Source (RestIndex q) a b) (seed : Id) (τ : Character) (ξ χ : RayCharacter)
    (Q : Id) (t : ℝ) (Φ : 𝓢(ℝ,ℂ)) (K Tsec Z ζ Hsource : ℝ) (hK : 0<K)
    (hH : ∀I∈sourceColumns s,outerColumn q x y seed ξ I≠0→(I.absNorm:ℝ)≤Hsource) :
    secondRetainedEnergy τ t (sourceColumns s) (outerColumn q x y seed ξ) Φ K Tsec Z ζ=
      outerPartEnergy true q x y s seed τ ξ χ Q t Φ K Tsec Z ζ Hsource+
      outerPartEnergy false q x y s seed τ ξ χ Q t Φ K Tsec Z ζ Hsource := by
  rw [original_live_blocks τ t (sourceColumns s) (outerColumn q x y seed ξ)
    Φ K Tsec Z ζ Hsource hK hH]
  unfold outerPartEnergy
  dsimp only
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [←mul_add,←Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro U hU
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  exact physical_block_outer_split q x y seed τ t ξ χ Q
    (activeSource (sourceColumns s) (outerColumn q x y seed ξ)) p.val.1 p.val.2 _ _ U
    (frequencyRadius Tsec Z ζ) Φ K (fun i=>(n i:ℤ))

/-- Triangle inequality retains the WHOLE common-height summand. Dropping
that factor here would erase the fixed C,E character zeros needed by the
fresh-prime forcing argument. -/
theorem outerPartEnergy_norm_le (exceptional : Bool) (q : Data ι) (x : Frozen q)
    (y : Selected q) (s : Source (RestIndex q) a b) (seed : Id) (τ : Character)
    (ξ χ : RayCharacter) (Q : Id) (t : ℝ) (Φ : 𝓢(ℝ,ℂ)) (K Tsec Z ζ Hsource : ℝ) :
    ‖outerPartEnergy exceptional q x y s seed τ ξ χ Q t Φ K Tsec Z ζ Hsource‖≤
      ∑p∈liveLabels τ (sourceColumns s) (outerColumn q x y seed ξ),
        ∑U : Finset (CommonIndex p.val.1 p.val.2),
          ∑n : SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ζ) Hsource,
            ‖(heightCoeff τ t p.val.1*star (heightCoeff τ t p.val.2))*
              physicalBlock τ t
                (activeSource (sourceColumns s) (outerColumn q x y seed ξ))
                (outerColumn q x y seed ξ) p.val.1 p.val.2
                (commonLabels_supported
                  (activeSource (sourceColumns s) (outerColumn q x y seed ξ)) _ _ p.property).1
                (commonLabels_supported
                  (activeSource (sourceColumns s) (outerColumn q x y seed ξ)) _ _ p.property).2 U
                (frequencyRadius Tsec Z ζ)
                (outerRows exceptional q x y τ ξ χ Q p.val.1 p.val.2 U
                  (frequencyRadius Tsec Z ζ)) Φ K (fun i=>(n i:ℤ))‖ := by
  unfold outerPartEnergy
  dsimp only
  simp only [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro U hU
  exact norm_sum_le _ _

theorem actual_outer_label_data (q : Data ι) (x : Frozen q) (y : Selected q)
    (s : Source (RestIndex q) a b) (ha : 0<a) (hb : 0≤b) (hm : Matches q x s ha)
    (seed : Id) (hseed : Squarefree seed) (ξ : RayCharacter)
    (p : ActiveLabel (sourceColumns s) (outerColumn q x y seed ξ)) :
    primeSupport p.val.1=primeSupport p.val.2 ∧ seed∣p.val.1 ∧ seed∣p.val.2 ∧
      (p.val.1.absNorm:ℝ)≤poolCap s ∧ (p.val.2.absNorm:ℝ)≤poolCap s := by
  have hmask (I : Id) (_ : I∈sourceColumns s) (hI : outerColumn q x y seed ξ I≠0) : seed∣I :=
    (outer_lower_seed q x y s ha hm seed ξ I hI).2
  have hp : p.val∈commonShell (sourceColumns s) (outerColumn q x y seed ξ)
      (Ideal.absNorm (commonRadical p.val.1 p.val.2):ℝ) := Finset.mem_filter.mpr ⟨p.property,le_rfl⟩
  have hd := active_common_data (sourceColumns s) (outerColumn q x y seed ξ)
    seed hseed hmask _ p.val hp
  have hn := commonLabel_norm_bounds (sourceColumns s) (outerColumn q x y seed ξ) (poolCap s)
    (fun I hI _=>source_column_pool_norm s hb I hI) _ _ p.property
  exact ⟨hd.2.2.1,hd.2.2.2.1,hd.2.2.2.2,hn⟩

/-- Coarse simultaneous polynomial conductor admission, including BOTH
moving products. This never replaces the sharp dyadic row count. -/
def outerFamilyConductorBudget (q : Data ι) (x : Frozen q) (y : Selected q)
    (s : Source (RestIndex q) a b) (τ : Character) (radius : ℝ) : ℝ :=
  4*OuterFreshPhysical.fixedConductorCost τ*s.R.absNorm*(frozenProduct q x).absNorm^2*
    (selectedProduct q y).absNorm^2*poolCap s*poolNorm s*radius

theorem outer_conductor_mono (q : Data ι) (x : Frozen q) (y : Selected q)
    (s : Source (RestIndex q) a b) (τ : Character) (G : Id) (radius : ℝ)
    (hr : 0≤radius) (hG : (G.absNorm:ℝ)≤poolCap s) :
    OuterFreshWindowPair.conductorBudget q x y s τ G radius≤
      outerFamilyConductorBudget q x y s τ radius := by
  have hf : 0≤OuterFreshPhysical.fixedConductorCost τ := by
    unfold OuterFreshPhysical.fixedConductorCost
    positivity
  have hp : 0≤poolNorm s := Finset.sum_nonneg (fun I _=>Nat.cast_nonneg _)
  let A : ℝ := 4*OuterFreshPhysical.fixedConductorCost τ*s.R.absNorm*
    (frozenProduct q x).absNorm^2*(selectedProduct q y).absNorm^2*poolNorm s*radius
  have hA : 0≤A := by dsimp only [A]; positivity
  calc
    _=A*(G.absNorm:ℝ) := by unfold OuterFreshWindowPair.conductorBudget A; ring
    _≤A*poolCap s := mul_le_mul_of_nonneg_left hG hA
    _=_ := by unfold outerFamilyConductorBudget A; ring

private theorem scalar_conductor_cap
    (c t r f d v p h Z ε Bτ BR BF BD Bnorm M : ℝ)
    (hz : 0<Z) (ht0 : 0≤t) (hr0 : 0≤r) (hf0 : 0≤f) (hd0 : 0≤d)
    (hv0 : 0≤v) (hp0 : 0≤p) (hh0 : 0≤h)
    (hc : c≤Z^ε) (ht : t≤Z^Bτ) (hr : r≤Z^BR) (hf : f≤Z^BF)
    (hd : d≤Z^BD) (hv : v≤Z^Bnorm) (hp : p≤(Z^Bnorm)^2) (hh : h≤Z^M) :
    c*t*r*f^2*d^2*v*p*h≤Z^ε*Z^Bτ*Z^BR*(Z^BF)^2*(Z^BD)^2*Z^Bnorm*(Z^Bnorm)^2*Z^M := by
  have hf2 := pow_le_pow_left₀ hf0 hf 2
  have hd2 := pow_le_pow_left₀ hd0 hd 2
  have h01 := mul_le_mul hc ht ht0 (Real.rpow_nonneg hz.le _)
  have h02 := mul_le_mul h01 hr hr0 (by positivity)
  have h03 := mul_le_mul h02 hf2 (sq_nonneg _) (by positivity)
  have h04 := mul_le_mul h03 hd2 (sq_nonneg _) (by positivity)
  have h05 := mul_le_mul h04 hv hv0 (by positivity)
  have h06 := mul_le_mul h05 hp hp0 (by positivity)
  exact mul_le_mul h06 hh hh0 (by positivity)

/-- The full conductor admission follows uniformly from polynomial
source scales. Moving f,D are variables with visible exponents, never
part of the eventual constant. This cap is used only for subpower losses. -/
theorem eventually_outer_family_conductor (N : ℕ)
    (b L Pexp ε Bτ BR BF BD M : ℝ) (hb : 0≤b) (hε : 0<ε) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(κ : Type u) [Fintype κ],∀q : Data κ,∀x : Frozen q,∀y : Selected q,
      ∀a : ℝ,∀s : Source (RestIndex q) a b,Fintype.card (RestIndex q)≤N→
      s.X₁≤Z^L→s.X₂≤Z^L→s.Y₁≤Z^L→s.Y₂≤Z^L→(∏i,s.P i)≤Z^Pexp→
      (s.R.absNorm:ℝ)≤Z^BR→((frozenProduct q x).absNorm:ℝ)≤Z^BF→
      ((selectedProduct q y).absNorm:ℝ)≤Z^BD→
      ∀(τ : Character)(radius : ℝ),0≤radius → (τ.modulus.absNorm:ℝ)≤Z^Bτ → radius≤Z^M →
      outerFamilyConductorBudget q x y s τ radius≤
        Z^(Bτ+BR+2*BF+2*BD+6*L+3*Pexp+M+4*ε) := by
  let Cfixed : ℝ := 4*(Ideal.span {(12:O)}).absNorm*
    (Ideal.span {fixedBadMask}).absNorm^2*(Ideal.span {(72:O)}).absNorm^2
  have hc : ∀ᶠZ : ℝ in atTop,Cfixed≤Z^ε :=
    (Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) Cfixed
  filter_upwards [eventually_source_caps N b L Pexp ε hε,hc] with Z hZ hfixed
  refine ⟨hZ.1,?_⟩
  intro κ instκ q x y a s hcard hX₁ hX₂ hY₁ hY₂ hP hR hf hd τ radius hr hτ hrad
  have hcap := (hZ.2 (RestIndex q) a s hcard hX₁ hX₂ hY₁ hY₂ hP).1
  have hpool := (pool_norm_le_square s hb).trans
    (pow_le_pow_left₀ (poolCap_nonneg s) hcap 2)
  have hpool0 : 0≤poolNorm s := Finset.sum_nonneg (fun I _=>Nat.cast_nonneg _)
  have hcap0 := poolCap_nonneg s
  have hz := zero_lt_one.trans hZ.1
  have hfixed0 : 0≤Cfixed := by dsimp only [Cfixed]; positivity
  calc
    _=Cfixed*(τ.modulus.absNorm:ℝ)*s.R.absNorm*(frozenProduct q x).absNorm^2*
        (selectedProduct q y).absNorm^2*poolCap s*poolNorm s*radius := by
      unfold outerFamilyConductorBudget OuterFreshPhysical.fixedConductorCost Cfixed
      ring
    _≤Z^ε*Z^Bτ*Z^BR*(Z^BF)^2*(Z^BD)^2*
        Z^(2*L+Pexp+ε)*(Z^(2*L+Pexp+ε))^2*Z^M := by
      exact scalar_conductor_cap Cfixed _ _ _ _ _ _ _ Z ε Bτ BR BF BD
        (2*L+Pexp+ε) M hz (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        (Nat.cast_nonneg _) hcap0 hpool0 hr hfixed hτ hR hf hd hcap hpool hrad
    _=_ := by
      simp only [pow_two]
      repeat rw [←Real.rpow_add hz]
      congr 1
      ring

/-- A generic finite summation lemma for the actual new partition.
Its local input includes the full common height; the final theorem below
discharges this input using the proved pair/count/kernel chain. -/
theorem outer_energy_radical_bound (exceptional : Bool) (q : Data ι) (x : Frozen q)
    (y : Selected q) (s : Source (RestIndex q) a b) (seed : Id) (τ : Character)
    (ξ χ : RayCharacter) (Q : Id) (t : ℝ) (Φ : 𝓢(ℝ,ℂ))
    (K Tsec Z ζ Hsource V Ebudget : ℝ) (hV : 0<V) (hE : 0≤Ebudget)
    (hblock : ∀p∈liveLabels τ (sourceColumns s) (outerColumn q x y seed ξ),
      ∀U : Finset (CommonIndex p.val.1 p.val.2),
      ∀n : SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ζ) Hsource,
        ‖(heightCoeff τ t p.val.1*star (heightCoeff τ t p.val.2))*
          physicalBlock τ t (activeSource (sourceColumns s) (outerColumn q x y seed ξ))
            (outerColumn q x y seed ξ) p.val.1 p.val.2
            (commonLabels_supported
              (activeSource (sourceColumns s) (outerColumn q x y seed ξ)) _ _ p.property).1
            (commonLabels_supported
              (activeSource (sourceColumns s) (outerColumn q x y seed ξ)) _ _ p.property).2 U
            (frequencyRadius Tsec Z ζ)
            (outerRows exceptional q x y τ ξ χ Q p.val.1 p.val.2 U (frequencyRadius Tsec Z ζ))
            Φ K (fun i=>(n i:ℤ))‖/V≤Ebudget*radicalWeight p.val.1 p.val.2) :
    ‖outerPartEnergy exceptional q x y s seed τ ξ χ Q t Φ K Tsec Z ζ Hsource‖/V≤
      Ebudget*(∑p : ActiveBlocks (sourceColumns s) (outerColumn q x y seed ξ)
        K (frequencyRadius Tsec Z ζ) Hsource,radicalWeight p.1.1.val.1 p.1.1.val.2) := by
  apply (div_le_div_of_nonneg_right
    (outerPartEnergy_norm_le exceptional q x y s seed τ ξ χ Q t Φ K Tsec Z ζ Hsource) hV.le).trans
  simp only [Finset.sum_div]
  calc
    _≤∑p∈liveLabels τ (sourceColumns s) (outerColumn q x y seed ξ),
        ∑U : Finset (CommonIndex p.val.1 p.val.2),
          ∑_n : SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ζ) Hsource,
            Ebudget*radicalWeight p.val.1 p.val.2 := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro U hU
      apply Finset.sum_le_sum
      intro n hn
      exact hblock p hp U n
    _=Ebudget*(∑p∈liveLabels τ (sourceColumns s) (outerColumn q x y seed ξ),
        ∑U : Finset (CommonIndex p.val.1 p.val.2),
          ∑_n : SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ζ) Hsource,
            radicalWeight p.val.1 p.val.2) := by simp only [Finset.mul_sum]
    _≤_ := mul_le_mul_of_nonneg_left
      (live_radical_sum_le τ (sourceColumns s) (outerColumn q x y seed ξ)
        K (frequencyRadius Tsec Z ζ) Hsource) hE

/-- Complete retained outer exceptional energy, including actual dyadic,
common-ideal and divisor summation at ORIGINAL K. All natural-zero gates
are derived from actual summands. The only bounds required of the source
are displayed structural, scale and full polynomial-conductor admissions.
There is no row-count, pair-estimate or energy-estimate premise. -/
theorem uniform_actual_outer_exceptional_part (N : ℕ)
    (saving Bcap a b ε δ Bnorm Lrad Cr εsum : ℝ)
    (hs : (2/3:ℝ)≤saving) (hs4 : saving<4/5) (hBcap : 0≤Bcap)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hδ : 0<δ) (hgap : saving+2*δ<1)
    (hBnorm : 0≤Bnorm) (hLrad : 0≤Lrad) (hCr : 0<Cr) (hεsum : 0<εsum) :
    ∃J : ℕ,∃control : Finset (ℕ×ℕ),(0,0)∈control ∧
      ∀Φ : 𝓢(ℝ,ℂ),∃Ckernel : ℝ,0≤Ckernel ∧
      ∀Q : Id,Q≠0→Q≠⊤→Q≤Ideal.span {(72:O)}→∃A Csum : ℝ,0<A ∧ 0<Csum ∧
      ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(κ : Type u) [Fintype κ],∀q : Data κ,∀x : Frozen q,∀y : Selected q,
      Function.Injective y→∀s : Source (RestIndex q) a b,Matches q x s ha→
      ∀cover : OriginalEnclosure s,Fintype.card (RestIndex q)≤N→
      (s.Fhole.absNorm:ℝ)≤Z^Bcap→(∏i,2*s.P i)≤Z^Bcap→poolCap s≤Z^Bnorm→
      ∀(seed : Id)(τ : Character)(ξ χ : RayCharacter),Squarefree seed→seed≠0→
      selectedPositiveWeight q x y τ≠0→
      ∀(t K Tsec ζ Hsource : ℝ),0<K→0≤Tsec→
      poolCap s≤Hsource→Hsource≤Z^Bnorm→
      frequencyRadius Tsec Z ζ≤Cr*Z^Lrad→
      outerFamilyConductorBudget q x y s τ (frequencyRadius Tsec Z ζ)≤Z^Bcap→
      ‖outerPartEnergy true q x y s seed τ ξ χ Q t Φ K Tsec Z ζ Hsource‖/sourceVolume s≤
        (Ckernel*A*heightBase t^(2*J)*(windowMoment J)^2)*
          outerSavedBudget q y s J control Q Z ε K*
            Z^(2*Bnorm*δ)*(Csum*Z^εsum/(seed.absNorm:ℝ)) := by
  obtain ⟨J,control,h00,hkernel⟩ := uniform_saved_actual_block N saving Bcap a b ε δ
    hs hs4 hBcap ha hb hε hδ hgap
  obtain ⟨Csum,hCsum,hsum⟩ := actual_block_radical_mass Bnorm Lrad Cr εsum
    hBnorm hLrad hCr hεsum
  refine ⟨J,control,h00,?_⟩
  intro Φ
  obtain ⟨Ckernel,hCkernel,hblock⟩ := hkernel Φ
  refine ⟨Ckernel,hCkernel,?_⟩
  intro Q hQ0 hQt hQ72
  obtain ⟨A,hA,hpoint⟩ := hblock Q hQ0 hQt hQ72
  refine ⟨A,Csum,hA,hCsum,?_⟩
  filter_upwards [hsum,eventually_gt_atTop (1:ℝ)] with Z hsum hZ
  refine ⟨hZ,?_⟩
  intro κ instκ q x y hy s hm cover hι hF hP hcap seed τ ξ χ hseed hseed0 hw
    t K Tsec ζ Hsource hK hT hpoolH hH hrad hcond
  let S := sourceColumns s
  let β := outerColumn q x y seed ξ
  let D := Ckernel*A*heightBase t^(2*J)*(windowMoment J)^2
  let Ebudget := D*outerSavedBudget q y s J control Q Z ε K*Z^(2*Bnorm*δ)
  have hD : 0≤D := by
    have ht := (heightBase_pos t).le
    dsimp only [D]
    positivity
  have hsave := outerSavedBudget_nonneg q y s J control Q Z ε K hK.le
  have hEbudget : 0≤Ebudget := by dsimp only [Ebudget]; positivity
  have hmask (I : Id) (_ : I∈S) (hI : β I≠0) : seed∣I :=
    (outer_lower_seed q x y s ha hm seed ξ I hI).2
  have hnorm (I : Id) (hI : I∈S) (_ : β I≠0) : (I.absNorm:ℝ)≤Z^Bnorm :=
    (source_column_pool_norm s hb I hI).trans hcap
  have hr0 : 0≤frequencyRadius Tsec Z ζ := by
    unfold frequencyRadius
    exact mul_nonneg hT (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
  have hlocal : ∀p∈liveLabels τ S β,∀U : Finset (CommonIndex p.val.1 p.val.2),
      ∀n : SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ζ) Hsource,
        ‖(heightCoeff τ t p.val.1*star (heightCoeff τ t p.val.2))*
          physicalBlock τ t (activeSource S β) β p.val.1 p.val.2
            (commonLabels_supported (activeSource S β) _ _ p.property).1
            (commonLabels_supported (activeSource S β) _ _ p.property).2 U
            (frequencyRadius Tsec Z ζ)
            (outerRows true q x y τ ξ χ Q p.val.1 p.val.2 U (frequencyRadius Tsec Z ζ))
            Φ K (fun i=>(n i:ℤ))‖/sourceVolume s≤Ebudget*radicalWeight p.val.1 p.val.2 := by
    intro p hp U n
    have hsupp := commonLabels_supported (activeSource S β) _ _ p.property
    have hdata := actual_outer_label_data q x y s ha hb hm seed hseed ξ p
    have hcC := (outer_conductor_mono q x y s τ p.val.1 _ hr0 hdata.2.2.2.1).trans hcond
    have hcE := (outer_conductor_mono q x y s τ p.val.2 _ hr0 hdata.2.2.2.2).trans hcond
    have hh := hpoint κ q x y hy s hm cover Z hZ hι hF hP seed τ ξ χ hw
      p.val.1 p.val.2 hsupp.1 hsupp.2 hdata.1 hdata.2.1 hdata.2.2.1 U
      t (frequencyRadius Tsec Z ζ) K (fun i=>(n i:ℤ)) hK hcC hcE
    rw [←physicalBlock_active τ t S β p.val.1 p.val.2 hsupp.1 hsupp.2 U
      (frequencyRadius Tsec Z ζ)
      (outerRows true q x y τ ξ χ Q p.val.1 p.val.2 U (frequencyRadius Tsec Z ζ))
      Φ K (fun i=>(n i:ℤ))]
    have halloc := allocation_subpowers (p.val.1.absNorm:ℝ) (p.val.2.absNorm:ℝ) Z Bnorm δ
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (zero_lt_one.trans hZ) hδ.le
      (hdata.2.2.2.1.trans hcap) (hdata.2.2.2.2.trans hcap)
    calc
      _≤D*outerSavedBudget q y s J control Q Z ε K*
          (p.val.1.absNorm:ℝ)^δ*(p.val.2.absNorm:ℝ)^δ/
            (Ideal.absNorm (commonRadical p.val.1 p.val.2):ℝ) := by
        simpa only [S,β,D] using hh
      _≤D*outerSavedBudget q y s J control Q Z ε K*Z^(2*Bnorm*δ)/
            (Ideal.absNorm (commonRadical p.val.1 p.val.2):ℝ) := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left halloc (mul_nonneg hD hsave)
      _=Ebudget*radicalWeight p.val.1 p.val.2 := by unfold Ebudget radicalWeight; ring
  exact (outer_energy_radical_bound true q x y s seed τ ξ χ Q t Φ K Tsec Z ζ Hsource
    (sourceVolume s) Ebudget (sourceVolume_pos s) hEbudget hlocal).trans
      (mul_le_mul_of_nonneg_left
        (hsum seed hseed hseed0 S β hmask hnorm K (frequencyRadius Tsec Z ζ)
          Hsource hK hrad hH) hEbudget)

end
end Candidate.SilPrior.FourthPower.OuterFreshAssembly
