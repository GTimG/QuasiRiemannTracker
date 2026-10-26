/- Copyright (c) 2026 Sil. Apache-2.0.
Actual inner exceptional physical block. The normalized pair estimate is
returned to raw volume exactly before the existing whole-kernel theorem.
K4, the physical scalar and the single outside 1/W remain explicit.

-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedInnerExceptionalPair
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondExceptionalKernel
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondPhysicalBlock
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondDyadicRowSupport
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondPhysicalLedger
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceLowerSupport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedInnerExceptionalBlock
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI.SevenEighths.CenteredMomentLogDyadic
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondExceptionalSourceFamily
open CenteredMomentSecondEnergySplit CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondHeightFamily
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization CenteredMomentSmooth
open CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSecondDyadicRowSupport CenteredMomentFixedQForcingCount
open CenteredMomentSecondPhysicalLedger CenteredMomentSourceLowerSupport
open CenteredMomentLattice CenteredMomentTwist CenteredMomentRankinRadical
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentForcing
open QRH.Record1252270103KernelMass (pairNorm pairNorm_pos)
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedPrincipalBudget
open MixedInnerExceptionalPair MixedLiveNormalization MixedPrincipalCentered
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

def sourceVolume (s : Source ι a b) : ℝ := s.X₁*s.X₂*∏i,s.P i

theorem sourceVolume_pos (s : Source ι a b) : 0<sourceVolume s := by
  exact mul_pos (mul_pos (s.hL.trans_le s.hX₁) (s.hL.trans_le s.hX₂))
    (Finset.prod_pos (fun i _=>zero_lt_one.trans_le (s.hP i)))

/-- The literal UNNORMALIZED pair required by actual_exceptional_block_bound. -/
def rawPair (s : Source ι a b) (ha : 0<a) (η : Character)
    (C E : Id) (hC : Supported C) (hE : Supported E) (U : Finset (CommonIndex C E))
    (seed : Id) (χ ξ : RayCharacter) (t θ X Y : ℝ) (rows : Finset O) : ℝ :=
  let A := commonFrequencyGenerator C E*nonunitFrequencyGenerator C E U
  ∑L∈actualDivisors s E hE,‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*∑z∈rows,
    ‖rowPolynomial Finset.univ (sectorElement C hC.1 (sourceColumns s))
      (fun I=>divisorCoefficient L (sectorElement C hC.1 (sourceColumns s))
        (movingCoefficient A (sectorElement C hC.1 (sourceColumns s))
          (fun J=>sourceCoefficient s ha seed (C*J)*heightCoeff η t J)) χ I*
        columnPhase logAnnulus (Real.log ((I.val.absNorm:ℝ)/X)) θ) z‖*
    ‖rowPolynomial Finset.univ (sectorElement E hE.1 (sourceColumns s))
      (fun I=>divisorCoefficient L (sectorElement E hE.1 (sourceColumns s))
        (movingCoefficient A (sectorElement E hE.1 (sourceColumns s))
          (fun J=>sourceCoefficient s ha seed (E*J)*heightCoeff η t J)) (ξ⁻¹) I*
        star (columnPhase logAnnulus (Real.log ((I.val.absNorm:ℝ)/Y)) θ)) (-z)‖

theorem normalized_pair_eq (s : Source ι a b) (ha : 0<a) (η : Character)
    (C E : Id) (hC : Supported C) (hE : Supported E) (U : Finset (CommonIndex C E))
    (seed : Id) (χ ξ : RayCharacter) (t θ X Y : ℝ) (rows : Finset O) :
    actualPair s ha η C E hC hE U seed χ ξ t θ X Y rows=
      ‖normalization (s.X₁*s.X₂) s.P‖^2*
        rawPair s ha η C E hC hE U seed χ ξ t θ X Y rows := by
  simp only [actualPair,rawPair,movingWindow,conjugateWindow,norm_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro L hL
  apply Finset.sum_congr rfl
  intro z hz
  ring

/-- Each of the two windows carries one normalization. Thus restoring
the raw pair costs exactly T*prod(P), not its square or square root. -/
theorem raw_pair_eq (s : Source ι a b) (ha : 0<a) (η : Character)
    (C E : Id) (hC : Supported C) (hE : Supported E) (U : Finset (CommonIndex C E))
    (seed : Id) (χ ξ : RayCharacter) (t θ X Y : ℝ) (rows : Finset O) :
    rawPair s ha η C E hC hE U seed χ ξ t θ X Y rows=
      sourceVolume s*actualPair s ha η C E hC hE U seed χ ξ t θ X Y rows := by
  rw [normalized_pair_eq,normalization_sq (s.X₁*s.X₂)
    (mul_pos (s.hL.trans_le s.hX₁) (s.hL.trans_le s.hX₂)) s.P
    (fun i=>zero_lt_one.trans_le (s.hP i))]
  change rawPair s ha η C E hC hE U seed χ ξ t θ X Y rows=
    sourceVolume s*((1/sourceVolume s)*rawPair s ha η C E hC hE U seed χ ξ t θ X Y rows)
  field_simp [(sourceVolume_pos s).ne'] <;> ring

def heightBase (t : ℝ) : ℝ := (1+‖t‖+2*Real.pi)*(1+2*Real.pi)

theorem heightBase_pos (t : ℝ) : 0<heightBase t := by unfold heightBase; positivity

theorem height_cost_le (t w : ℝ) : heightCost t w≤heightBase t*(1+‖w‖) := by
  unfold heightCost heightBase
  calc
    _≤((1+‖t‖+2*Real.pi)*(1+‖w‖))*(1+2*Real.pi) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith [mul_nonneg (show 0≤1+‖t‖ by positivity) (norm_nonneg w),Real.pi_pos]
    _=_ := by ring

theorem height_pair_le (t w : ℝ) (J : ℕ) :
    heightCost t w^J*heightCost t (-w)^J≤heightBase t^(2*J)*(1+‖w‖)^(2*J) := by
  have hbase := (heightBase_pos t).le
  have h₁ := pow_le_pow_left₀ (heightCost_pos t w).le (height_cost_le t w) J
  have h₂ := pow_le_pow_left₀ (heightCost_pos t (-w)).le (height_cost_le t (-w)) J
  simp only [norm_neg] at h₂
  calc
    _≤(heightBase t*(1+‖w‖))^J*(heightBase t*(1+‖w‖))^J :=
      mul_le_mul h₁ h₂ (pow_nonneg (heightCost_pos t (-w)).le _) (by positivity)
    _=_ := by rw [←pow_add,←two_mul,mul_pow]

def kernelScale (n : Fin 4→ℤ) : ℝ :=
  dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))

theorem kernelScale_pos (n : Fin 4→ℤ) : 0<kernelScale n :=
  div_pos (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))
    (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))

/-- The sharp fixed-Q count uses the actual dyadic row scale, with Cr=1. -/
def dyadicCountCost (Q C E : Id) (U : Finset (CommonIndex C E))
    (Z : ℝ) (n : Fin 4→ℤ) : ℝ :=
  (Ideal.absNorm (commonRadical Q Q):ℝ)^(2/3:ℝ)*
    (768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card*
      Z^((Real.logb Z (dyadicScale (n 1))-
        4*Real.logb Z (forcingNorm C E U))/6))

theorem actual_dyadic_count (η : Character) (χ₀ : RayCharacter)
    (Q : Id) (hQ0 : Q≠0) (hQtop : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)})
    (m : O) (hm : m≠0) (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (C E : Id) (hC : Supported C) (U : Finset (CommonIndex C E))
    (hη : idealCoeff η C≠0) (radius Z : ℝ) (hZ : 1<Z) (n : Fin 4→ℤ) :
    ((dyadicRows (partRows true η χ₀ Q m C E U radius) n).card:ℝ)≤
      dyadicCountCost Q C E U Z n := by
  have hc := actual_canonical_exceptional_count_fixedQ η χ₀ C E hC U Q hQ0 hQtop hQ72 hη
    m hm hml hm2 (dyadicRows (partRows true η χ₀ Q m C E U radius) n)
    (dyadicRows_nonzero _ n)
    (fun z hz=>exceptional_part_inducing η χ₀ Q m C E U radius z
      (dyadicRows_subset _ n hz))
    Z 1 (Real.logb Z (dyadicScale (n 1))) hZ (by norm_num)
    (fun z hz=>by simpa only [one_mul] using dyadicRows_power_cap _ n Z hZ z hz)
  simpa only [dyadicCountCost,forcingNorm,Real.one_rpow,mul_one] using hc

/-- Sharp actual inner block: physicalBlock_dyadic_rows removes exactly
zero frequency weights BEFORE applying the count. No global-radius
count is used. Family is constructed, and no analytic estimate is a premise. -/
theorem uniform_actual_block (N : ℕ) (α Bcap a b ε δ : ℝ)
    (hα : 0≤α) (hα4 : α<4/5) (hBcap : 0≤Bcap)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hδ : 0<δ) (hgap : α+2*δ<1) :
    ∃J : ℕ,∃control : Finset (ℕ×ℕ),(0,0)∈control ∧
      ∀(Φ : 𝓢(ℝ,ℂ))(decay : ℕ),∃Ckernel : ℝ,0≤Ckernel ∧
      ∀Q : Id,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} → ∃A : ℝ,0<A ∧
      ∀(ι : Type u) [Fintype ι],∀s : Source ι a b,∀cover : OriginalEnclosure s,
      ∀Z : ℝ,1<Z → Fintype.card ι≤N → (s.Fhole.absNorm:ℝ)≤Z^Bcap →
      (∏i,2*s.P i)≤Z^Bcap →
      ∀(η : Character)(χ₀ : RayCharacter)(m : O),m≠0 → goodLambda∣m → (2:O)∣m →
      ∀(C E : Id)(hC : Supported C)(hE : Supported E),primeSupport C=primeSupport E →
      ∀U : Finset (CommonIndex C E),∀seed : Id,seed∣C → seed∣E → idealCoeff η C≠0 →
      ∀(t radius K W : ℝ),0<K → 0<W →
      ∀n : Fin 4→ℤ,conductorBudget s η C E radius≤Z^Bcap →
      (1+kernelScale n)^decay*
        ‖physicalBlock η t (sourceColumns s) (sourceCoefficient s ha seed) C E hC hE U radius
          (partRows true η χ₀ Q m C E U radius) Φ (16*K*W^4) n‖/W≤
        outerScalar C E (16*K*W^4) n*normalizer C E U*
          (Ckernel*(sourceVolume s*A*dyadicCountCost Q C E U Z n*
            paidBudget s C E J control Z ε α δ*heightBase t^(2*J)*(windowMoment J)^2))/W := by
  obtain ⟨J,control,h00,hwindow⟩ := uniform_original_window_pair N α Bcap a b ε δ
    hα hα4 hBcap ha hb hε hδ hgap
  obtain ⟨Cb,hCb,hbudget⟩ := uniform_pair_budget N δ hδ
  refine ⟨J,control,h00,?_⟩
  intro Φ decay
  obtain ⟨Ckernel,hCkernel,hkernel⟩ := actual_exceptional_block_bound Φ decay (2*J)
  refine ⟨Ckernel,hCkernel,?_⟩
  intro Q hQ0 hQtop hQ72
  obtain ⟨Cw,hCw,hwindow⟩ := hwindow Q hQ0
  let A := Cw*Cb
  have hA : 0<A := mul_pos hCw hCb
  refine ⟨A,hA,?_⟩
  intro ι instι s cover Z hZ hι hF hP η χ₀ m hm hml hm2 C E hC hE hCE U
    seed hsC hsE hη t radius K W hK hW n hcond
  obtain ⟨τ,hf⟩ := exists_exceptional_family η C E hC hE hCE U
  let fullrows := partRows true η χ₀ Q m C E U radius
  let rows := dyadicRows fullrows n
  let Ds := actualDivisors s E hE
  let Eraw := sourceVolume s*A*dyadicCountCost Q C E U Z n*
    paidBudget s C E J control Z ε α δ*heightBase t^(2*J)*(windowMoment J)^2
  have hK4 : 0<16*K*W^4 := by positivity
  have ho : 0≤outerScalar C E (16*K*W^4) n := by unfold outerScalar; positivity
  have hn := (normalizer_pos C E hC U).le
  have hvol := (sourceVolume_pos s).le
  have hpaid := paid_budget_nonneg s C E J control Z ε α δ
  have hcard : (rows.card:ℝ)≤dyadicCountCost Q C E U Z n :=
    actual_dyadic_count η χ₀ Q hQ0 hQtop hQ72 m hm hml hm2 C E hC U hη radius Z hZ n
  have hcount : 0≤dyadicCountCost Q C E U Z n := (Nat.cast_nonneg _).trans hcard
  have hheight := (heightBase_pos t).le
  have hEraw : 0≤Eraw := by dsimp only [Eraw]; positivity
  have hsub : rows⊆fullrows := dyadicRows_subset fullrows n
  have hrows : ∀z∈rows,z≠0 := dyadicRows_nonzero fullrows n
  have hind := actual_family_both_rows η χ₀ Q hQ72 m hm hml hm2 C E hC hE U τ hf radius
  by_cases hne : physicalBlock η t (sourceColumns s) (sourceCoefficient s ha seed)
      C E hC hE U radius fullrows Φ (16*K*W^4) n=0
  · change (1+kernelScale n)^decay*
      ‖physicalBlock η t (sourceColumns s) (sourceCoefficient s ha seed)
        C E hC hE U radius fullrows Φ (16*K*W^4) n‖/W≤
        outerScalar C E (16*K*W^4) n*normalizer C E U*(Ckernel*Eraw)/W
    rw [hne,norm_zero,mul_zero,zero_div]
    positivity
  have hb' : pairBudget s hb cover C E J control Z ε α≤
      Cb*paidBudget s C E J control Z ε α δ := by
    have hh := hbudget ι a b s hb cover hι C E hC.1 hE.1 J control Z ε α
      (zero_le_one.trans hZ.le) hα
    simpa only [paidBudget,mul_assoc,div_eq_mul_inv] using hh
  have hpair (χ ξ : RayCharacter) (w : ℝ) :
      actualPair s ha η C E hC hE U seed χ ξ t w (dyadicScale (n 2)) (dyadicScale (n 3)) rows≤
        A*dyadicCountCost Q C E U Z n*paidBudget s C E J control Z ε α δ*
          heightCost t w^J*heightCost t (-w)^J*(windowMoment J)^2 := by
    have hc (z : O) (hz : z∈rows) (L : Id) (hL : L∈CenteredMomentWholeDivisorShell.live Ds) :=
      actual_conductor_bounds s ha η χ₀ Q m C E hC hE hCE U τ hf seed t radius Φ
        (16*K*W^4) hK4 n hne χ ξ z (hsub hz) L
          ((CenteredMomentWholeDivisorShell.mem_live Ds L).mp hL).1
    have hp := hwindow ι s cover Z hZ.le hι hF hP C E hC hE seed hsC hsE
      η (τ χ) (τ (ξ⁻¹)) χ ξ (commonFrequencyGenerator C E*nonunitFrequencyGenerator C E U)
      (fun I hI hcop v=>hf.height_eq χ I hI (Or.inl hcop) v)
      (fun I hI hcop v=>hf.height_eq (ξ⁻¹) I hI (Or.inr hcop) v)
      t w (dyadicScale (n 2)) (dyadicScale (n 3)) (dyadicScale_pos _) (dyadicScale_pos _)
      rows (CenteredMomentWholeDivisorShell.live Ds) (fun L=>(UniqueFactorizationMonoid.moebius L:ℂ))
      hrows (CenteredMomentWholeDivisorShell.live_squarefree Ds)
      (fun L _=>CenteredMomentWholeDivisorShell.moebius_norm_le_one L)
      (fun z hz L hL=>(hc z hz L hL).1.trans hcond)
      (fun z hz L hL=>(hc z hz L hL).2.trans hcond)
      (fun z hz=>hind.1 χ z (hsub hz)) (fun z hz=>hind.2 (ξ⁻¹) z (hsub hz))
    have hp' : actualPair s ha η C E hC hE U seed χ ξ t w
        (dyadicScale (n 2)) (dyadicScale (n 3)) rows≤
        (rows.card:ℝ)*Cw*pairBudget s hb cover C E J control Z ε α*
          heightCost t w^J*heightCost t (-w)^J*(windowMoment J)^2 := by
      unfold actualPair
      rw [CenteredMomentWholeDivisorShell.sum_norm_moebius_live]
      exact hp
    have hp₀ := pair_budget_nonneg s hb cover C E J control Z ε α (zero_le_one.trans hZ.le)
    have hh₁ := (heightCost_pos t w).le
    have hh₂ := (heightCost_pos t (-w)).le
    apply hp'.trans
    calc
      _≤dyadicCountCost Q C E U Z n*Cw*(Cb*paidBudget s C E J control Z ε α δ)*
          heightCost t w^J*heightCost t (-w)^J*(windowMoment J)^2 := by gcongr
      _=_ := by dsimp only [A]; ring
  have hraw (χ ξ : RayCharacter) (w : ℝ) :
      rawPair s ha η C E hC hE U seed χ ξ t w (dyadicScale (n 2)) (dyadicScale (n 3)) rows≤
        Eraw*(1+‖w‖)^(2*J) := by
    have hp := hpair χ ξ w
    have hh := height_pair_le t w J
    rw [raw_pair_eq]
    calc
      _≤sourceVolume s*(A*dyadicCountCost Q C E U Z n*paidBudget s C E J control Z ε α δ*
          heightCost t w^J*heightCost t (-w)^J*(windowMoment J)^2) :=
        mul_le_mul_of_nonneg_left hp hvol
      _≤sourceVolume s*(A*dyadicCountCost Q C E U Z n*paidBudget s C E J control Z ε α δ*
          (heightBase t^(2*J)*(1+‖w‖)^(2*J))*(windowMoment J)^2) := by
        have hcoef : 0≤A*dyadicCountCost Q C E U Z n*paidBudget s C E J control Z ε α δ := by positivity
        have hh' := mul_le_mul_of_nonneg_left hh hcoef
        have hh'' := mul_le_mul_of_nonneg_right hh' (sq_nonneg (windowMoment J))
        exact mul_le_mul_of_nonneg_left (by simpa only [mul_assoc] using hh'') hvol
      _=_ := by dsimp only [Eraw]; ring
  have hk := hkernel (kernelScale n) (kernelScale_pos n) η t (sourceColumns s)
    (sourceCoefficient s ha seed) C E hC hE hCE U radius rows
    (fun _=>Real.log (secondEffectiveScale C E
      (commonFrequencyGenerator C E*nonunitFrequencyGenerator C E U) (16*K*W^4)/dyadicScale (n 0)))
    (fun z=>Real.log (normValue z/dyadicScale (n 1)))
    (fun I : ↥(sectorPool C hC.1 (sourceColumns s))=>
      Real.log ((I.val.absNorm:ℝ)/dyadicScale (n 2)))
    (fun I : ↥(sectorPool E hE.1 (sourceColumns s))=>
      Real.log ((I.val.absNorm:ℝ)/dyadicScale (n 3)))
    Q m χ₀ hQ72 hml hm2
    (fun z hz=>exceptional_part_inducing η χ₀ Q m C E U radius z (hsub hz)) Eraw hEraw (by
      intro χ ξ _ _ w
      simpa only [rawPair,actualDivisors,sectorElement_span] using hraw χ ξ w)
  change (1+kernelScale n)^decay*
    ‖normalizedBlock η t (sourceColumns s) (sourceCoefficient s ha seed) C E hC hE U radius
      rows Φ (16*K*W^4) n‖≤Ckernel*Eraw at hk
  have hphys : ‖physicalBlock η t (sourceColumns s) (sourceCoefficient s ha seed)
      C E hC hE U radius fullrows Φ (16*K*W^4) n‖=
      outerScalar C E (16*K*W^4) n*normalizer C E U*
        ‖normalizedBlock η t (sourceColumns s) (sourceCoefficient s ha seed)
          C E hC hE U radius rows Φ (16*K*W^4) n‖ := by
    rw [physicalBlock_dyadic_rows,
      physicalBlock_eq η t (sourceColumns s) (sourceCoefficient s ha seed) C E hC hE U radius rows
        hrows Φ (16*K*W^4) hK4 n,
      norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ho,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hn]
  apply div_le_div_of_nonneg_right _ hW.le
  rw [hphys]
  calc
    _=(outerScalar C E (16*K*W^4) n*normalizer C E U)*
        ((1+kernelScale n)^decay*
          ‖normalizedBlock η t (sourceColumns s) (sourceCoefficient s ha seed) C E hC hE U radius
            rows Φ (16*K*W^4) n‖) := by ring
    _≤_ := mul_le_mul_of_nonneg_left hk (mul_nonneg ho hn)

/-- Scalar common saving without introducing logarithmic widths.
The original prefix is restored explicitly in common_pair_saving_norm. -/
theorem scalar_common_saving (c d x α : ℝ) (hc : 0<c) (hd : 0<d)
    (hx : 0<x) (hα : (2/3:ℝ)≤α) :
    (c*d)^(-1/3:ℝ)*min ((max 1 (x/c))^(-α)) ((max 1 (x/d))^(-α))≤x^(-2/3:ℝ) := by
  let m := min c d
  have hm : 0<m := lt_min hc hd
  have hmcd : m*m≤c*d := mul_le_mul (min_le_left _ _) (min_le_right _ _) hm.le hc.le
  have hnorm : (c*d)^(-1/3:ℝ)≤m^(-2/3:ℝ) := by
    calc
      _≤(m*m)^(-1/3:ℝ) := Real.rpow_le_rpow_of_nonpos (mul_pos hm hm) hmcd (by norm_num)
      _=_ := by rw [Real.mul_rpow hm.le hm.le,←Real.rpow_add hm]; norm_num
  have hmin : min ((max 1 (x/c))^(-α)) ((max 1 (x/d))^(-α))≤(max 1 (x/m))^(-α) := by
    rcases le_total c d with h|h
    · simpa only [m,min_eq_left h] using min_le_left ((max 1 (x/c))^(-α)) ((max 1 (x/d))^(-α))
    · simpa only [m,min_eq_right h] using min_le_right ((max 1 (x/c))^(-α)) ((max 1 (x/d))^(-α))
  have hq : 1≤max 1 (x/m) := le_max_left _ _
  have hexp : (max 1 (x/m))^(-α)≤(max 1 (x/m))^(-2/3:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hq (by linarith)
  have hxm : x≤m*max 1 (x/m) := by
    calc
      x=(x/m)*m := (div_mul_cancel₀ x hm.ne').symm
      _≤max 1 (x/m)*m := mul_le_mul_of_nonneg_right (le_max_right _ _) hm.le
      _=_ := mul_comm _ _
  have hmin0 : 0≤min ((max 1 (x/c))^(-α)) ((max 1 (x/d))^(-α)) :=
    le_min (Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _)
      (Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _)
  calc
    _≤m^(-2/3:ℝ)*(max 1 (x/m))^(-2/3:ℝ) :=
      mul_le_mul hnorm (hmin.trans hexp) hmin0 (Real.rpow_nonneg hm.le _)
    _=(m*max 1 (x/m))^(-2/3:ℝ) := (Real.mul_rpow hm.le (zero_le_one.trans hq)).symm
    _≤x^(-2/3:ℝ) := Real.rpow_le_rpow_of_nonpos hx hxm (by norm_num)

theorem common_pair_saving_norm (s : Source ι a b) (C E : Id)
    (hC : C≠0) (hE : E≠0) (α : ℝ) (hα : (2/3:ℝ)≤α) :
    ((C.absNorm:ℝ)*E.absNorm)^(-1/3:ℝ)*
      min (commonSaving s C α) (commonSaving s E α)≤
        (s.L/prefixNormMax s.d)^(-2/3:ℝ) := by
  have hc : 0<(C.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  have he : 0<(E.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hE)
  have hh := scalar_common_saving (C.absNorm:ℝ) (E.absNorm:ℝ)
    (s.L/prefixNormMax s.d) α hc he (div_pos s.hL (prefixNormMax_pos s.d s.hd)) hα
  simpa only [commonSaving,div_div] using hh

/-- Literal source support lower bound, including both original prefixes.
A nonzero tupleWeight cannot create a new column or remove its support gate. -/
theorem source_coefficient_lower (s : Source ι a b) (ha : 0<a) (seed I : Id)
    (hI : sourceCoefficient s ha seed I≠0) :
    (a^2/pairNorm s.d)*sourceVolume s≤(I.absNorm:ℝ) := by
  unfold sourceCoefficient MixedHeightEnergy.originalColumn at hI
  obtain ⟨v,hv,hv0,hvI⟩ := CenteredMomentSupportedZeroEnergy.finiteColumnCoefficient_witness _ _ I hI
  have hs₁ := (normPowerProfile_support s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁).trans s.hs₁
  have hs₂ := (normPowerProfile_support s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂).trans s.hs₂
  have hl := profile_product_lower s.R s.ν s.Wslot s.P (fun _=>(1:ℝ))
    (normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
    (normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂)
    a a s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) s.d.1 s.d.2 seed
    (fun i=>zero_lt_one.trans_le (s.hP i)) (fun _=>zero_le_one) ha.le ha.le
    (s.hL.trans_le s.hX₁) (s.hL.trans_le s.hX₂) (s.hL.trans_le s.hY₁) (s.hL.trans_le s.hY₂)
    s.hd.1 s.hd.2 rfl (s.hpY.trans s.hpX.symm)
    (fun i x hx=>(s.hW i hx).1) (fun x hx=>(hs₁ hx).1) (fun x hx=>(hs₂ hx).1)
    v (mul_ne_zero_iff.mp hv0).2
  simp only [Finset.prod_const_one,one_mul,hvI] at hl
  convert hl using 1 <;> unfold sourceVolume pairNorm <;> ring

/-- The original physical-cost theorem now has its lower column support
proved from this literal Source, rather than supplied as a hypothesis. -/
theorem actual_source_central_cost (s : Source ι a b) (ha : 0<a)
    (η : Character) (t : ℝ) (seed : Id)
    (C E : Id) (hC : Supported C) (hE : Supported E) (hCE : primeSupport C=primeSupport E)
    (U : Finset (CommonIndex C E)) (radius : ℝ) (rows : Finset O) (hrows : ∀z∈rows,z≠0)
    (Φ : 𝓢(ℝ,ℂ)) (Kphys Z : ℝ) (hK : 0<Kphys) (hZ : 1<Z) (n : Fin 4→ℤ)
    (hne : physicalBlock η t (sourceColumns s) (sourceCoefficient s ha seed)
      C E hC hE U radius rows Φ Kphys n≠0) :
    centralPhysicalCost C E U Kphys (sourceVolume s) n≤
      (sourceVolume s)^(1/3:ℝ)*Kphys^(5/6:ℝ)*(a^2/pairNorm s.d)^(-2/3:ℝ)*
        Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (E.absNorm:ℝ))/3) :=
  original_block_physical_cost η t (sourceColumns s) (sourceCoefficient s ha seed)
    C E hC hE hCE U radius rows hrows Φ Kphys n hK (sourceVolume s) (a^2/pairNorm s.d) Z
    (sourceVolume_pos s) (div_pos (sq_pos_of_pos ha) (pairNorm_pos s.hd.1 s.hd.2)) hZ
    (fun I hI=>source_coefficient_lower s ha seed I hI) hne

/-- Full common saving with allocation subpowers LEFT EXPLICITLY IN PLACE.
The source prefix loss is a^2/pairNorm(d), while the shortened ordinary
length is L/prefixNormMax(d). These are different retained quantities. -/
theorem actual_source_common_cost (s : Source ι a b) (ha : 0<a)
    (η : Character) (t : ℝ) (seed : Id)
    (C E : Id) (hC : Supported C) (hE : Supported E) (hCE : primeSupport C=primeSupport E)
    (U : Finset (CommonIndex C E)) (radius : ℝ) (rows : Finset O) (hrows : ∀z∈rows,z≠0)
    (Φ : 𝓢(ℝ,ℂ)) (Kphys Z α δ : ℝ) (hK : 0<Kphys) (hZ : 1<Z)
    (hα : (2/3:ℝ)≤α) (n : Fin 4→ℤ)
    (hne : physicalBlock η t (sourceColumns s) (sourceCoefficient s ha seed)
      C E hC hE U radius rows Φ Kphys n≠0) :
    centralPhysicalCost C E U Kphys (sourceVolume s) n*
        (C.absNorm:ℝ)^δ*(E.absNorm:ℝ)^δ*min (commonSaving s C α) (commonSaving s E α)≤
      (sourceVolume s)^(1/3:ℝ)*Kphys^(5/6:ℝ)*(a^2/pairNorm s.d)^(-2/3:ℝ)*
        (C.absNorm:ℝ)^δ*(E.absNorm:ℝ)^δ*(s.L/prefixNormMax s.d)^(-2/3:ℝ) := by
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
  have hcost := actual_source_central_cost s ha η t seed C E hC hE hCE U radius rows hrows
    Φ Kphys Z hK hZ n hne
  rw [hlog] at hcost
  have hs := common_pair_saving_norm s C E hC.1 hE.1 α hα
  have hsave : 0≤min (commonSaving s C α) (commonSaving s E α) :=
    le_min (commonSaving_nonneg s C α) (commonSaving_nonneg s E α)
  have hfactor : 0≤(sourceVolume s)^(1/3:ℝ)*Kphys^(5/6:ℝ)*(a^2/pairNorm s.d)^(-2/3:ℝ)*
      (C.absNorm:ℝ)^δ*(E.absNorm:ℝ)^δ := by
    have := (sourceVolume_pos s).le
    have := (pairNorm_pos s.hd.1 s.hd.2).le
    positivity
  calc
    _≤((sourceVolume s)^(1/3:ℝ)*Kphys^(5/6:ℝ)*(a^2/pairNorm s.d)^(-2/3:ℝ)*
        ((C.absNorm:ℝ)*E.absNorm)^(-1/3:ℝ))*
        (C.absNorm:ℝ)^δ*(E.absNorm:ℝ)^δ*min (commonSaving s C α) (commonSaving s E α) := by
      gcongr
    _=((sourceVolume s)^(1/3:ℝ)*Kphys^(5/6:ℝ)*(a^2/pairNorm s.d)^(-2/3:ℝ)*
        (C.absNorm:ℝ)^δ*(E.absNorm:ℝ)^δ)*
        (((C.absNorm:ℝ)*E.absNorm)^(-1/3:ℝ)*min (commonSaving s C α) (commonSaving s E α)) := by ring
    _≤_ := mul_le_mul_of_nonneg_left hs hfactor

/-- The inner fourth-power transfer costs precisely W^(7/3) at this
exceptional ledger. No fresh-D count or extra 1/W is inserted. -/
theorem fourth_kernel_cost (K W : ℝ) (hK : 0<K) (hW : 0<W) :
    (16*K*W^4)^(5/6:ℝ)/W=(16:ℝ)^(5/6:ℝ)*K^(5/6:ℝ)*W^(7/3:ℝ) := by
  have hw : (W^4)^(5/6:ℝ)=W^(10/3:ℝ) := by
    rw [←Real.rpow_natCast W 4,←Real.rpow_mul hW.le]
    congr 1
    norm_num
  have hratio : W^(10/3:ℝ)/W=W^(7/3:ℝ) := by
    calc
      _=W^(10/3:ℝ)/W^(1:ℝ) := by rw [Real.rpow_one]
      _=W^((10/3:ℝ)-1) := (Real.rpow_sub hW _ _).symm
      _=_ := by norm_num
  rw [Real.mul_rpow (by positivity : 0≤16*K) (by positivity : 0≤W^4),
    Real.mul_rpow (by norm_num : (0:ℝ)≤16) hK.le,hw]
  calc
    _=(16:ℝ)^(5/6:ℝ)*K^(5/6:ℝ)*(W^(10/3:ℝ)/W) := by ring
    _=_ := by rw [hratio]

end
end Candidate.FourthPower.MixedInnerExceptionalBlock
