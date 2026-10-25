/- Copyright (c) 2026 Sil. Apache-2.0.
Exact sharp inner-exceptional scalar ledger. Every fixed-Q, profile,
prefix, allocation and fourth-power factor remains displayed.

-/
import Candidate.SilPrior.FourthPower.MixedInnerExceptionalBlock
import Candidate.SilPrior.FourthPower.MixedPrincipalPoolCaps
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstCanonicalAllowance
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondExceptionalAggregate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.MixedInnerExceptionalLedger
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

/-- Fixed inducing modulus cost: its radical power is NOT discarded. -/
def fixedQCost (Q : Id) : ℝ :=
  (Ideal.absNorm (commonRadical Q Q):ℝ)^(2/3:ℝ)*
    (768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card)

theorem fixedQCost_nonneg (Q : Id) : 0≤fixedQCost Q := by
  unfold fixedQCost
  positivity

/-- Exactly the profile part of baseBudget; its square includes Z^(2ε). -/
def sourceProfile (s : Source ι a b) (J : ℕ) (control : Finset (ℕ×ℕ))
    (Z ε : ℝ) : ℝ :=
  (sourceControl control s.W₁*sourceControl control s.W₂)*Z^ε*
    (1+‖s.t₁‖+‖s.t₂‖)^J*fullMarkedCost s

theorem base_budget_square (s : Source ι a b) (J : ℕ)
    (control : Finset (ℕ×ℕ)) (Z ε : ℝ) :
    (baseBudget s J control Z ε)^2=
      (sourceProfile s J control Z ε)^2*sourceVolume s/(pairNorm s.d)^2 := by
  have hv : s.T*∏i,s.P i=sourceVolume s := by
    unfold sourceVolume
    rw [s.hpX]
  change (sourceProfile s J control Z ε*Real.sqrt (s.T*∏i,s.P i)/pairNorm s.d)^2=_
  rw [hv,div_pow,mul_pow,Real.sq_sqrt (sourceVolume_pos s).le]

theorem dyadic_count_exact (Q C E : Id) (hC : Supported C)
    (U : Finset (CommonIndex C E)) (Z : ℝ) (hZ : 1<Z) (n : Fin 4→ℤ) :
    dyadicCountCost Q C E U Z n=
      fixedQCost Q*(dyadicScale (n 1))^(1/6:ℝ)/(forcingNorm C E U)^(2/3:ℝ) := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have hf : 0<forcingNorm C E U := common_product_pos C E hC _
  have hp : Z^((Real.logb Z (dyadicScale (n 1))-4*Real.logb Z (forcingNorm C E U))/6)=
      (dyadicScale (n 1))^(1/6:ℝ)/(forcingNorm C E U)^(2/3:ℝ) := by
    rw [show (Real.logb Z (dyadicScale (n 1))-4*Real.logb Z (forcingNorm C E U))/6=
      Real.logb Z (dyadicScale (n 1))*(1/6)-Real.logb Z (forcingNorm C E U)*(2/3) by ring,
      Real.rpow_sub hz _ _,Real.rpow_mul hz.le,Real.rpow_mul hz.le,
      Real.rpow_logb hz (ne_of_gt hZ) (dyadicScale_pos _),
      Real.rpow_logb hz (ne_of_gt hZ) hf]
  unfold dyadicCountCost fixedQCost
  rw [hp]
  ring

def sourcePrefactor (s : Source ι a b) (J : ℕ) (control : Finset (ℕ×ℕ))
    (Q : Id) (Z ε : ℝ) : ℝ :=
  fixedQCost Q*(sourceProfile s J control Z ε)^2/(pairNorm s.d)^2

theorem sourcePrefactor_nonneg (s : Source ι a b) (J : ℕ)
    (control : Finset (ℕ×ℕ)) (Q : Id) (Z ε : ℝ) :
    0≤sourcePrefactor s J control Q Z ε :=
  div_nonneg (mul_nonneg (fixedQCost_nonneg Q) (sq_nonneg _)) (sq_nonneg _)

/-- Exact normalization of the physical block RHS. The forcing factor
survives in its denominator; allocation subpowers remain in its numerator. -/
theorem central_budget_exact (s : Source ι a b) (J : ℕ) (control : Finset (ℕ×ℕ))
    (Q C E : Id) (hC : Supported C) (hE : Supported E)
    (U : Finset (CommonIndex C E)) (Z ε α δ Kphys : ℝ) (hZ : 1<Z) (n : Fin 4→ℤ) :
    (1/sourceVolume s)*outerScalar C E Kphys n*normalizer C E U*
      (sourceVolume s*dyadicCountCost Q C E U Z n*paidBudget s C E J control Z ε α δ)/
        (1+kernelScale n)=
      sourcePrefactor s J control Q Z ε*
        (centralPhysicalCost C E U Kphys (sourceVolume s) n*
          (C.absNorm:ℝ)^δ*(E.absNorm:ℝ)^δ*min (commonSaving s C α) (commonSaving s E α))/
        ((Ideal.absNorm (commonRadical C E):ℝ)*(forcingNorm C E U)^(1/3:ℝ)) := by
  have hv := sourceVolume_pos s
  have hd := pairNorm_pos s.hd.1 s.hd.2
  have hf : 0<forcingNorm C E U := common_product_pos C E hC _
  have hr := common_product_pos C E hC Finset.univ
  have hc : 0<(C.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have he : 0<(E.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hE.1)
  have hk : 0<1+kernelScale n := by linarith [kernelScale_pos n]
  have hf13 : 0<(forcingNorm C E U)^(1/3:ℝ) := Real.rpow_pos_of_pos hf _
  have hpow : (forcingNorm C E U)^(2/3:ℝ)=
      (forcingNorm C E U)^(1/3:ℝ)*(forcingNorm C E U)^(1/3:ℝ) := by
    rw [←Real.rpow_add hf]
    congr 1
    ring
  rw [dyadic_count_exact Q C E hC U Z hZ n]
  unfold paidBudget
  rw [base_budget_square,hpow,←common_ideal_product]
  unfold sourcePrefactor centralPhysicalCost
  change (1/sourceVolume s)*outerScalar C E Kphys n*normalizer C E U*
      (sourceVolume s*(fixedQCost Q*(dyadicScale (n 1))^(1/6:ℝ)/
        ((forcingNorm C E U)^(1/3:ℝ)*(forcingNorm C E U)^(1/3:ℝ)))*
        ((C.absNorm:ℝ)^δ*(E.absNorm:ℝ)^δ*
          ((sourceProfile s J control Z ε)^2*sourceVolume s/(pairNorm s.d)^2)/
          ((C.absNorm:ℝ)*E.absNorm)*min (commonSaving s C α) (commonSaving s E α)))/
        (1+kernelScale n)=_
  change _=fixedQCost Q*(sourceProfile s J control Z ε)^2/(pairNorm s.d)^2*
    (((1/sourceVolume s)*outerScalar C E Kphys n*normalizer C E U*
      (dyadicScale (n 1))^(1/6:ℝ)/(1+kernelScale n)*
      ((sourceVolume s)^2/((C.absNorm:ℝ)*E.absNorm))*
      (Ideal.absNorm (∏P : CommonIndex C E,P.val):ℝ)/(forcingNorm C E U)^(1/3:ℝ))*
      (C.absNorm:ℝ)^δ*(E.absNorm:ℝ)^δ*min (commonSaving s C α) (commonSaving s E α))/
      ((Ideal.absNorm (∏P : CommonIndex C E,P.val):ℝ)*(forcingNorm C E U)^(1/3:ℝ))
  field_simp

/-- The numerical forcing denominator can only improve the bound. -/
theorem forcing_third_ge_one (C E : Id) (hC : Supported C)
    (U : Finset (CommonIndex C E)) : 1≤(forcingNorm C E U)^(1/3:ℝ) := by
  have hf : 0<forcingNorm C E U := common_product_pos C E hC _
  have hf1 : 1≤forcingNorm C E U := by
    unfold forcingNorm at hf ⊢
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast ne_of_gt hf)
  exact Real.one_le_rpow hf1 (by norm_num)

/-- Common normalization and all original prefix costs, before K4/W. -/
def commonPhysicalCost (s : Source ι a b) (Kphys : ℝ) : ℝ :=
  (sourceVolume s)^(1/3:ℝ)*Kphys^(5/6:ℝ)*(a^2/pairNorm s.d)^(-2/3:ℝ)*
    (s.L/prefixNormMax s.d)^(-2/3:ℝ)

theorem commonPhysicalCost_nonneg (s : Source ι a b) (Kphys : ℝ) (hK : 0≤Kphys) :
    0≤commonPhysicalCost s Kphys := by
  have hv := (sourceVolume_pos s).le
  have hd := (pairNorm_pos s.hd.1 s.hd.2).le
  have hH := (prefixNormMax_pos s.d s.hd).le
  have hL := s.hL.le
  unfold commonPhysicalCost
  positivity

theorem actual_budget_common_saving (s : Source ι a b) (ha : 0<a)
    (J : ℕ) (control : Finset (ℕ×ℕ)) (Q : Id) (η : Character) (t : ℝ) (seed : Id)
    (C E : Id) (hC : Supported C) (hE : Supported E) (hCE : primeSupport C=primeSupport E)
    (U : Finset (CommonIndex C E)) (radius : ℝ) (rows : Finset O) (hrows : ∀z∈rows,z≠0)
    (Φ : 𝓢(ℝ,ℂ)) (Kphys Z ε α δ : ℝ) (hK : 0<Kphys) (hZ : 1<Z)
    (hα : (2/3:ℝ)≤α) (n : Fin 4→ℤ)
    (hne : physicalBlock η t (sourceColumns s) (sourceCoefficient s ha seed)
      C E hC hE U radius rows Φ Kphys n≠0) :
    (1/sourceVolume s)*outerScalar C E Kphys n*normalizer C E U*
      (sourceVolume s*dyadicCountCost Q C E U Z n*paidBudget s C E J control Z ε α δ)/
        (1+kernelScale n)≤
      sourcePrefactor s J control Q Z ε*commonPhysicalCost s Kphys*
        (C.absNorm:ℝ)^δ*(E.absNorm:ℝ)^δ/(Ideal.absNorm (commonRadical C E):ℝ) := by
  have hs := actual_source_common_cost s ha η t seed C E hC hE hCE U radius rows hrows
    Φ Kphys Z α δ hK hZ hα n hne
  have hp := sourcePrefactor_nonneg s J control Q Z ε
  have hphys := commonPhysicalCost_nonneg s Kphys hK.le
  have hr : 0<(Ideal.absNorm (commonRadical C E):ℝ) := by
    rw [←common_ideal_product]
    exact common_product_pos C E hC Finset.univ
  have hf := forcing_third_ge_one C E hC U
  have hnum : 0≤sourcePrefactor s J control Q Z ε*commonPhysicalCost s Kphys*
      (C.absNorm:ℝ)^δ*(E.absNorm:ℝ)^δ := by positivity
  rw [central_budget_exact s J control Q C E hC hE U Z ε α δ Kphys hZ n]
  calc
    _≤sourcePrefactor s J control Q Z ε*
        (commonPhysicalCost s Kphys*(C.absNorm:ℝ)^δ*(E.absNorm:ℝ)^δ)/
        ((Ideal.absNorm (commonRadical C E):ℝ)*(forcingNorm C E U)^(1/3:ℝ)) := by
      apply div_le_div_of_nonneg_right _ (mul_nonneg hr.le (zero_le_one.trans hf))
      apply mul_le_mul_of_nonneg_left _ hp
      simpa only [commonPhysicalCost,mul_assoc,mul_left_comm,mul_comm] using hs
    _=(sourcePrefactor s J control Q Z ε*commonPhysicalCost s Kphys*
        (C.absNorm:ℝ)^δ*(E.absNorm:ℝ)^δ)/
        ((Ideal.absNorm (commonRadical C E):ℝ)*(forcingNorm C E U)^(1/3:ℝ)) := by ring
    _≤_ := div_le_div_of_nonneg_left hnum hr (by nlinarith)

/-- Exact fourth-power penalty together with the fixed-Q and profile
factor. PairNorm(d)^(-2), (a²/pairNorm(d))^(-2/3), and prefixNormMax(d)
are all retained separately rather than set to one. -/
def savedBudget (s : Source ι a b) (J : ℕ) (control : Finset (ℕ×ℕ))
    (Q : Id) (Z ε K W : ℝ) : ℝ :=
  sourcePrefactor s J control Q Z ε*(sourceVolume s)^(1/3:ℝ)*
    (16:ℝ)^(5/6:ℝ)*K^(5/6:ℝ)*W^(7/3:ℝ)*(a^2/pairNorm s.d)^(-2/3:ℝ)*
    (s.L/prefixNormMax s.d)^(-2/3:ℝ)

theorem savedBudget_exact (s : Source ι a b) (J : ℕ) (control : Finset (ℕ×ℕ))
    (Q : Id) (Z ε K W : ℝ) (hK : 0<K) (hW : 0<W) :
    sourcePrefactor s J control Q Z ε*commonPhysicalCost s (16*K*W^4)/W=
      savedBudget s J control Q Z ε K W := by
  unfold commonPhysicalCost savedBudget
  calc
    _=sourcePrefactor s J control Q Z ε*(sourceVolume s)^(1/3:ℝ)*
        ((16*K*W^4)^(5/6:ℝ)/W)*(a^2/pairNorm s.d)^(-2/3:ℝ)*
        (s.L/prefixNormMax s.d)^(-2/3:ℝ) := by ring
    _=_ := by rw [fourth_kernel_cost K W hK hW]; ring

theorem savedBudget_nonneg (s : Source ι a b) (J : ℕ) (control : Finset (ℕ×ℕ))
    (Q : Id) (Z ε K W : ℝ) (hK : 0<K) (hW : 0<W) :
    0≤savedBudget s J control Q Z ε K W := by
  rw [←savedBudget_exact s J control Q Z ε K W hK hW]
  exact div_nonneg (mul_nonneg (sourcePrefactor_nonneg s J control Q Z ε)
    (commonPhysicalCost_nonneg s _ (by positivity))) hW.le

/-- The full actual block estimate, including sharp common saving and
the only outside 1/W. No pair, count, Family or scalar estimate is a premise. -/
theorem uniform_saved_actual_block (N : ℕ) (α Bcap a b ε δ : ℝ)
    (hα : (2/3:ℝ)≤α) (hα4 : α<4/5) (hBcap : 0≤Bcap)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hδ : 0<δ) (hgap : α+2*δ<1) :
    ∃J : ℕ,∃control : Finset (ℕ×ℕ),(0,0)∈control ∧
      ∀Φ : 𝓢(ℝ,ℂ),∃Ckernel : ℝ,0≤Ckernel ∧
      ∀Q : Id,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} → ∃A : ℝ,0<A ∧
      ∀(ι : Type u) [Fintype ι],∀s : Source ι a b,∀cover : OriginalEnclosure s,
      ∀Z : ℝ,1<Z → Fintype.card ι≤N → (s.Fhole.absNorm:ℝ)≤Z^Bcap →
      (∏i,2*s.P i)≤Z^Bcap →
      ∀(η : Character)(χ₀ : RayCharacter)(m : O),m≠0 → goodLambda∣m → (2:O)∣m →
      ∀(C E : Id)(hC : Supported C)(hE : Supported E),primeSupport C=primeSupport E →
      ∀U : Finset (CommonIndex C E),∀seed : Id,seed∣C → seed∣E → idealCoeff η C≠0 →
      ∀(t radius K W : ℝ),0<K → 0<W →
      ∀n : Fin 4→ℤ,conductorBudget s η C E radius≤Z^Bcap →
      ‖physicalBlock η t (sourceColumns s) (sourceCoefficient s ha seed) C E hC hE U radius
          (partRows true η χ₀ Q m C E U radius) Φ (16*K*W^4) n‖/sourceVolume s/W≤
        (Ckernel*A*heightBase t^(2*J)*(windowMoment J)^2)*
          savedBudget s J control Q Z ε K W*(C.absNorm:ℝ)^δ*(E.absNorm:ℝ)^δ/
            (Ideal.absNorm (commonRadical C E):ℝ) := by
  obtain ⟨J,control,h00,hkernel⟩ := uniform_actual_block N α Bcap a b ε δ
    (by linarith) hα4 hBcap ha hb hε hδ hgap
  refine ⟨J,control,h00,?_⟩
  intro Φ
  obtain ⟨Ckernel,hCkernel,hbound⟩ := hkernel Φ 1
  refine ⟨Ckernel,hCkernel,?_⟩
  intro Q hQ0 hQt hQ72
  obtain ⟨A,hA,hblock⟩ := hbound Q hQ0 hQt hQ72
  refine ⟨A,hA,?_⟩
  intro ι instι s cover Z hZ hι hF hP η χ₀ m hm hml hm2 C E hC hE hCE U
    seed hsC hsE hη t radius K W hK hW n hcond
  let F := physicalBlock η t (sourceColumns s) (sourceCoefficient s ha seed) C E hC hE U radius
    (partRows true η χ₀ Q m C E U radius) Φ (16*K*W^4) n
  let D := Ckernel*A*heightBase t^(2*J)*(windowMoment J)^2
  have hD : 0≤D := by
    have ht := (heightBase_pos t).le
    dsimp only [D]
    positivity
  have hsaved := savedBudget_nonneg s J control Q Z ε K W hK hW
  by_cases hzero : F=0
  · change ‖F‖/_/_≤_
    rw [hzero,norm_zero,zero_div,zero_div]
    change 0≤D*savedBudget s J control Q Z ε K W*(C.absNorm:ℝ)^δ*(E.absNorm:ℝ)^δ/_
    positivity
  have hb := hblock ι s cover Z hZ hι hF hP η χ₀ m hm hml hm2 C E hC hE hCE U
    seed hsC hsE hη t radius K W hK hW n hcond
  have hs := actual_budget_common_saving s ha J control Q η t seed C E hC hE hCE U radius
    (partRows true η χ₀ Q m C E U radius)
    (fun z hz=>sourceRows_nonzero C E U radius z (Finset.mem_filter.mp hz).1)
    Φ (16*K*W^4) Z ε α δ (by positivity) hZ hα n hzero
  have hv := sourceVolume_pos s
  have hk : 0<1+kernelScale n := by linarith [kernelScale_pos n]
  have hb' : ‖F‖/sourceVolume s/W≤
      D*((1/sourceVolume s)*outerScalar C E (16*K*W^4) n*normalizer C E U*
        (sourceVolume s*dyadicCountCost Q C E U Z n*paidBudget s C E J control Z ε α δ)/
          (1+kernelScale n))/W := by
    have hf : ‖F‖≤outerScalar C E (16*K*W^4) n*normalizer C E U*
        (Ckernel*(sourceVolume s*A*dyadicCountCost Q C E U Z n*
          paidBudget s C E J control Z ε α δ*heightBase t^(2*J)*(windowMoment J)^2))/
          (1+kernelScale n) := by
      apply (le_div_iff₀ hk).mpr
      have hh := (div_le_div_iff_of_pos_right hW).mp hb
      simpa only [pow_one,F,mul_comm,mul_left_comm,mul_assoc] using hh
    convert div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_right hf hv.le) hW.le using 1 <;> dsimp only [D] <;> ring
  apply hb'.trans
  calc
    _≤D*(sourcePrefactor s J control Q Z ε*commonPhysicalCost s (16*K*W^4)*
        (C.absNorm:ℝ)^δ*(E.absNorm:ℝ)^δ/(Ideal.absNorm (commonRadical C E):ℝ))/W :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs hD) hW.le
    _=D*(sourcePrefactor s J control Q Z ε*commonPhysicalCost s (16*K*W^4)/W)*
        (C.absNorm:ℝ)^δ*(E.absNorm:ℝ)^δ/(Ideal.absNorm (commonRadical C E):ℝ) := by ring
    _=_ := by rw [savedBudget_exact s J control Q Z ε K W hK hW]

/-- The seed is a genuine mask of the original coefficient, including
tupleWeight. This proves the premise of the generic radical summation. -/
theorem source_coefficient_seed (s : Source ι a b) (ha : 0<a) (seed I : Id)
    (hI : sourceCoefficient s ha seed I≠0) : seed∣I := by
  unfold sourceCoefficient MixedHeightEnergy.originalColumn at hI
  obtain ⟨v,hv,hv0,hvI⟩ := CenteredMomentSupportedZeroEnergy.finiteColumnCoefficient_witness _ _ I hI
  rw [←hvI]
  by_contra hnot
  apply hv0
  simp only [profileCoefficient,hnot,ite_false,mul_zero]

/-- Concrete simultaneous conductor cap for the entire actual label
family. It is a scalar product of full original norms, not an energy
assumption; eventual_conductor_budget provides its scale version. -/
def familyConductorBudget (s : Source ι a b) (η : Character) (radius : ℝ) : ℝ :=
  4*fixedConductorCost η*s.R.absNorm*(poolCap s)^2*poolNorm s*radius

theorem actual_label_data (s : Source ι a b) (ha : 0<a) (hb : 0≤b)
    (seed : Id) (hseed : Squarefree seed)
    (p : ActiveLabel (sourceColumns s) (sourceCoefficient s ha seed)) :
    primeSupport p.val.1=primeSupport p.val.2 ∧ seed∣p.val.1 ∧ seed∣p.val.2 ∧
      (p.val.1.absNorm:ℝ)≤poolCap s ∧ (p.val.2.absNorm:ℝ)≤poolCap s := by
  have hm (I : Id) (_ : I∈sourceColumns s) (hI : sourceCoefficient s ha seed I≠0) : seed∣I :=
    source_coefficient_seed s ha seed I hI
  have hp : p.val∈commonShell (sourceColumns s) (sourceCoefficient s ha seed)
      (Ideal.absNorm (commonRadical p.val.1 p.val.2):ℝ) := Finset.mem_filter.mpr ⟨p.property,le_rfl⟩
  have hd := active_common_data (sourceColumns s) (sourceCoefficient s ha seed) seed hseed hm _ p.val hp
  have hn := commonLabel_norm_bounds (sourceColumns s) (sourceCoefficient s ha seed) (poolCap s)
    (fun I hI _=>source_column_pool_norm s hb I hI) _ _ p.property
  exact ⟨hd.2.2.1,hd.2.2.2.1,hd.2.2.2.2,hn⟩

theorem actual_label_conductor (s : Source ι a b) (ha : 0<a) (hb : 0≤b)
    (seed : Id) (hseed : Squarefree seed) (η : Character) (radius : ℝ) (hr : 0≤radius)
    (p : ActiveLabel (sourceColumns s) (sourceCoefficient s ha seed)) :
    conductorBudget s η p.val.1 p.val.2 radius≤familyConductorBudget s η radius := by
  have hn := actual_label_data s ha hb seed hseed p
  have hp := poolCap_nonneg s
  have hpool : 0≤poolNorm s := Finset.sum_nonneg (fun I _=>Nat.cast_nonneg _)
  have hfixed : 0≤fixedConductorCost η := by unfold fixedConductorCost; positivity
  have hpair : (p.val.1.absNorm:ℝ)*p.val.2.absNorm≤(poolCap s)^2 := by
    calc
      _≤poolCap s*poolCap s := mul_le_mul hn.2.2.2.1 hn.2.2.2.2 (Nat.cast_nonneg _) hp
      _=_ := (pow_two _).symm
  calc
    _=(4*fixedConductorCost η*s.R.absNorm*poolNorm s*radius)*
        ((p.val.1.absNorm:ℝ)*p.val.2.absNorm) := by unfold conductorBudget; ring
    _≤(4*fixedConductorCost η*s.R.absNorm*poolNorm s*radius)*(poolCap s)^2 := by
      exact mul_le_mul_of_nonneg_left hpair (by positivity)
    _=_ := by unfold familyConductorBudget; ring

/-- The simultaneous conductor admission is supplied by original source
scales. This coarse cap affects only subpowers, never the sharp count.
It includes zero coefficient columns via pool_norm_le_square. -/
theorem eventually_family_conductor (N : ℕ) (b L Pexp ε Bη BR M : ℝ)
    (hb : 0≤b) (hε : 0<ε) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(ι : Type u) [Fintype ι],∀a : ℝ,∀s : Source ι a b,
      Fintype.card ι≤N → s.X₁≤Z^L → s.X₂≤Z^L → s.Y₁≤Z^L → s.Y₂≤Z^L →
      (∏i,s.P i)≤Z^Pexp → (s.R.absNorm:ℝ)≤Z^BR →
      ∀(η : Character)(radius : ℝ),0≤radius → (η.modulus.absNorm:ℝ)≤Z^Bη → radius≤Z^M →
      familyConductorBudget s η radius≤Z^(Bη+BR+8*L+4*Pexp+M+5*ε) := by
  let Cfixed : ℝ := 4*(fixedFactor:ℝ)*(Ideal.span {fixedBadMask}).absNorm*
    (Ideal.span {(72:O)}).absNorm
  have hc : ∀ᶠZ : ℝ in atTop,Cfixed≤Z^ε :=
    (Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) Cfixed
  filter_upwards [eventually_source_caps N b L Pexp ε hε,hc] with Z hZ hfixed
  refine ⟨hZ.1,?_⟩
  intro ι instι a s hcard hX₁ hX₂ hY₁ hY₂ hP hR η radius hr hη hrad
  have hcap := (hZ.2 ι a s hcard hX₁ hX₂ hY₁ hY₂ hP).1
  have hcap2 : (poolCap s)^2≤(Z^(2*L+Pexp+ε))^2 :=
    pow_le_pow_left₀ (poolCap_nonneg s) hcap 2
  have hpool := (pool_norm_le_square s hb).trans hcap2
  have hpool0 : 0≤poolNorm s := Finset.sum_nonneg (fun I _=>Nat.cast_nonneg _)
  have hz := zero_lt_one.trans hZ.1
  calc
    _=Cfixed*(η.modulus.absNorm:ℝ)*s.R.absNorm*(poolCap s)^2*poolNorm s*radius := by
      unfold familyConductorBudget fixedConductorCost Cfixed
      ring
    _≤Z^ε*Z^Bη*Z^BR*(Z^(2*L+Pexp+ε))^2*(Z^(2*L+Pexp+ε))^2*Z^M := by gcongr
    _=_ := by
      simp only [pow_two]
      repeat rw [←Real.rpow_add hz]
      congr 1
      ring

theorem allocation_subpowers (c e Z B δ : ℝ) (hc : 0≤c) (he : 0≤e)
    (hZ : 0<Z) (hδ : 0≤δ) (hcZ : c≤Z^B) (heZ : e≤Z^B) :
    c^δ*e^δ≤Z^(2*B*δ) := by
  calc
    _≤(Z^B)^δ*(Z^B)^δ :=
      mul_le_mul (Real.rpow_le_rpow hc hcZ hδ) (Real.rpow_le_rpow he heZ hδ)
        (Real.rpow_nonneg he _) (Real.rpow_nonneg (Real.rpow_nonneg hZ.le _) _)
    _=Z^(2*B*δ) := by
      rw [←Real.rpow_mul hZ.le,←Real.rpow_add hZ]
      congr 1
      ring

/-- The actual exceptional part is now aggregated over all original
labels and dyadic blocks. The only admissibility input is the displayed
full conductor product. There is no per-block, row, count or energy
estimate among the hypotheses. Delta costs are paid by actual norm caps. -/
theorem uniform_actual_exceptional_part (N : ℕ)
    (α Bcap a b ε δ Bnorm Lrad Cr εsum : ℝ)
    (hα : (2/3:ℝ)≤α) (hα4 : α<4/5) (hBcap : 0≤Bcap)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hδ : 0<δ) (hgap : α+2*δ<1)
    (hBnorm : 0≤Bnorm) (hLrad : 0≤Lrad) (hCr : 0<Cr) (hεsum : 0<εsum) :
    ∃J : ℕ,∃control : Finset (ℕ×ℕ),(0,0)∈control ∧
      ∀Φ : 𝓢(ℝ,ℂ),∃Ckernel : ℝ,0≤Ckernel ∧
      ∀Q : Id,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} → ∃A Csum : ℝ,0<A ∧ 0<Csum ∧
      ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(ι : Type u) [Fintype ι],∀s : Source ι a b,∀cover : OriginalEnclosure s,
      Fintype.card ι≤N → (s.Fhole.absNorm:ℝ)≤Z^Bcap → (∏i,2*s.P i)≤Z^Bcap →
      poolCap s≤Z^Bnorm →
      ∀(η : Character)(χ₀ : RayCharacter)(m : O),m≠0 → goodLambda∣m → (2:O)∣m →
      ∀seed : Id,Squarefree seed → seed≠0 →
      ∀(t K W Tsec ξ Hsource : ℝ),0<K → 0<W → 0≤Tsec →
      Hsource≤Z^Bnorm →
      frequencyRadius Tsec Z ξ≤Cr*Z^Lrad →
      familyConductorBudget s η (frequencyRadius Tsec Z ξ)≤Z^Bcap →
      ‖partEnergy true η χ₀ Q m t (sourceColumns s) (sourceCoefficient s ha seed)
          Φ (16*K*W^4) Tsec Z ξ Hsource‖/sourceVolume s/W≤
        (Ckernel*A*heightBase t^(2*J)*(windowMoment J)^2)*savedBudget s J control Q Z ε K W*
          Z^(2*Bnorm*δ)*(Csum*Z^εsum/(seed.absNorm:ℝ)) := by
  obtain ⟨J,control,h00,hkernel⟩ := uniform_saved_actual_block N α Bcap a b ε δ
    hα hα4 hBcap ha hb hε hδ hgap
  obtain ⟨Csum,hCsum,hsum⟩ := source_part_radical_bound Bnorm Lrad Cr εsum
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
  intro ι instι s cover hι hF hP hcap η χ₀ m hm hml hm2 seed hseed hseed0
    t K W Tsec ξ Hsource hK hW hT hH hrad hcond
  let S := sourceColumns s
  let β := sourceCoefficient s ha seed
  let D := Ckernel*A*heightBase t^(2*J)*(windowMoment J)^2
  let Ebudget := D*savedBudget s J control Q Z ε K W*Z^(2*Bnorm*δ)
  have hD : 0≤D := by
    have ht := (heightBase_pos t).le
    dsimp only [D]
    positivity
  have hsave := savedBudget_nonneg s J control Q Z ε K W hK hW
  have hEbudget : 0≤Ebudget := by dsimp only [Ebudget]; positivity
  have hmask (I : Id) (_ : I∈S) (hI : β I≠0) : seed∣I :=
    source_coefficient_seed s ha seed I hI
  have hnorm (I : Id) (hI : I∈S) (_ : β I≠0) : (I.absNorm:ℝ)≤Z^Bnorm :=
    (source_column_pool_norm s hb I hI).trans hcap
  have hr0 : 0≤frequencyRadius Tsec Z ξ := by
    unfold frequencyRadius
    exact mul_nonneg hT (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
  rw [div_div]
  change ‖partEnergy true η χ₀ Q m t S β Φ (16*K*W^4) Tsec Z ξ Hsource‖/
    (sourceVolume s*W)≤Ebudget*(Csum*Z^εsum/(seed.absNorm:ℝ))
  apply hsum seed hseed hseed0 S β hmask hnorm true η χ₀ Q m t Φ
    (16*K*W^4) Tsec ξ Hsource (sourceVolume s*W) Ebudget (by positivity) hrad hH
    (mul_pos (sourceVolume_pos s) hW) hEbudget
  intro p hp U n
  have hsupp := commonLabels_supported (activeSource S β) _ _ p.property
  have hdata := actual_label_data s ha hb seed hseed p
  have hc := (actual_label_conductor s ha hb seed hseed η _ hr0 p).trans hcond
  have hη := (mem_liveLabels η S β p).mp hp |>.1
  have hh := hpoint ι s cover Z hZ hι hF hP η χ₀ m hm hml hm2
    p.val.1 p.val.2 hsupp.1 hsupp.2 hdata.1 U seed hdata.2.1 hdata.2.2.1 hη
    t (frequencyRadius Tsec Z ξ) K W hK hW (fun i=>(n i:ℤ)) hc
  rw [←physicalBlock_active η t S β p.val.1 p.val.2 hsupp.1 hsupp.2 U
    (frequencyRadius Tsec Z ξ)
    (partRows true η χ₀ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
    Φ (16*K*W^4) (fun i=>(n i:ℤ))]
  have halloc := allocation_subpowers (p.val.1.absNorm:ℝ) (p.val.2.absNorm:ℝ) Z Bnorm δ
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (zero_lt_one.trans hZ) hδ.le
    (hdata.2.2.2.1.trans hcap) (hdata.2.2.2.2.trans hcap)
  calc
    _≤D*savedBudget s J control Q Z ε K W*
        (p.val.1.absNorm:ℝ)^δ*(p.val.2.absNorm:ℝ)^δ/
          (Ideal.absNorm (commonRadical p.val.1 p.val.2):ℝ) := by
      simpa only [S,β,D,div_div] using hh
    _≤D*savedBudget s J control Q Z ε K W*Z^(2*Bnorm*δ)/
          (Ideal.absNorm (commonRadical p.val.1 p.val.2):ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left halloc (mul_nonneg hD hsave)
    _=Ebudget*radicalWeight p.val.1 p.val.2 := by unfold Ebudget radicalWeight; ring

end
end Candidate.SilPrior.FourthPower.MixedInnerExceptionalLedger
