/- Copyright (c) 2026 Sil. Apache-2.0.
Actual inner exceptional source pair: original coefficients, live Moebius
divisors, Family characters and canonical old forcing. No fresh-D count.

-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedPrincipalWindow
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedPrincipalBudget
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.WholeDivisorShell
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FixedQForcingCount

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedInnerExceptionalPair
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentSourceRow CenteredMomentSourceMass CenteredMomentFirstSectors
open CenteredMomentSecondSectorColumns CenteredMomentSecondScaled CenteredMomentChildAssembly
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondEnergySplit
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondExceptionalSourceFamily
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondHeightFamily CenteredMomentSecondLiveBlock
open CenteredMomentSecondRadicalBudget CenteredMomentSectorLocalization
open CenteredMomentWholeDivisorShell CenteredMomentFixedQForcingCount CenteredMomentForcing
open CenteredMomentMobiusRegroup CenteredMomentCommonSectors
open CenteredMomentHeckeColumnWindow CenteredMomentRowNorm
open CenteredMomentHeckeWindowEnergy CenteredMomentRankinRadical
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedPrincipalBudget
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- A deliberately coarse FULL norm bound on this actual finite pool.
It is only used for polynomial conductor admissibility. -/
def poolNorm (s : Source ι a b) : ℝ := ∑I∈sourceColumns s,(I.absNorm:ℝ)

def actualDivisors (s : Source ι a b) (G : Id) (hG : Supported G) : Finset Id :=
  divisorPool (Finset.univ : Finset ↥(sectorPool G hG.1 (sourceColumns s)))
    (fun I : ↥(sectorPool G hG.1 (sourceColumns s))=>
      Ideal.span {sectorElement G hG.1 (sourceColumns s) I})

theorem actual_divisor_norm (s : Source ι a b) (G : Id) (hG : Supported G)
    (L : Id) (hL : L∈actualDivisors s G hG) : L≠0 ∧ (L.absNorm:ℝ)≤poolNorm s := by
  apply divisorPool_nonzero_norm
    (Finset.univ : Finset ↥(sectorPool G hG.1 (sourceColumns s)))
    (fun I : ↥(sectorPool G hG.1 (sourceColumns s))=>
      Ideal.span {sectorElement G hG.1 (sourceColumns s) I})
    (fun I _=>(sectorElement_supported G hG.1 (sourceColumns s) I).1)
    (poolNorm s) ?_ L hL
  intro I hI
  rw [sectorElement_span]
  have hi : G*I.val∈supportedColumns (sourceColumns s) :=
    (mem_residualPool G hG.1 (supportedColumns (sourceColumns s)) I.val).mp
    (Finset.mem_filter.mp I.property).1
  have hcap : ((G*I.val).absNorm:ℝ)≤poolNorm s :=
    Finset.single_le_sum (fun J _=>Nat.cast_nonneg _) (Finset.mem_filter.mp hi).1
  exact (CenteredExceptionalCount.norm_le_of_dvd (Finset.mem_filter.mp hi).2.1
    (dvd_mul_left I.val G)).trans hcap

def fixedConductorCost (η : Character) : ℝ :=
  (η.modulus.absNorm:ℝ)*fixedFactor*(Ideal.span {fixedBadMask}).absNorm*
    (Ideal.span {(72:O)}).absNorm

def conductorBudget (s : Source ι a b) (η : Character) (C E : Id) (radius : ℝ) : ℝ :=
  4*fixedConductorCost η*s.R.absNorm*C.absNorm*E.absNorm*poolNorm s*radius

theorem full_row_conductor (τ : Character) (R G L : Id) (z : O) :
    (HeckeRowClosure.rowConductorBound τ
      (fixedBadMask*idealGenerator ((R*G)*L)) 1 z:ℝ)=
      (τ.modulus.absNorm:ℝ)*(Ideal.span {fixedBadMask}).absNorm*
        (Ideal.span {(72:O)}).absNorm*R.absNorm*G.absNorm*L.absNorm*normValue z := by
  simp only [HeckeRowClosure.rowConductorBound,←Ideal.span_singleton_mul_span_singleton,
    span_idealGenerator,Ideal.span_singleton_one,←Ideal.one_eq_top,map_one,map_mul,
    one_pow,one_mul,normValue,Nat.cast_mul]
  ring

/-- Conductor cap derived from the ACTUAL nonzero physical block and
actual finite divisor pool; the right sign is preserved. -/
theorem actual_conductor_bounds (s : Source ι a b) (ha : 0<a)
    (η : Character) (χ₀ : RayCharacter) (Q : Id) (m : O)
    (C E : Id) (hC : Supported C) (hE : Supported E)
    (hCE : primeSupport C=primeSupport E) (U : Finset (CommonIndex C E))
    (τ : RayCharacter→Character) (hf : Family η C E hC hE U τ)
    (seed : Id) (t radius : ℝ) (Φ : 𝓢(ℝ,ℂ)) (Kphys : ℝ) (hK : 0<Kphys)
    (n : Fin 4→ℤ)
    (hne : physicalBlock η t (sourceColumns s) (sourceCoefficient s ha seed)
      C E hC hE U radius (partRows true η χ₀ Q m C E U radius) Φ Kphys n≠0)
    (χ ξ : RayCharacter) (z : O) (hz : z∈partRows true η χ₀ Q m C E U radius)
    (L : Id) (hL : L∈actualDivisors s E hE) :
    (HeckeRowClosure.rowConductorBound (τ χ)
      (fixedBadMask*idealGenerator ((s.R*C)*L)) 1 z:ℝ)≤conductorBudget s η C E radius ∧
    (HeckeRowClosure.rowConductorBound (τ (ξ⁻¹))
      (fixedBadMask*idealGenerator ((s.R*E)*L)) 1 (-z):ℝ)≤conductorBudget s η C E radius := by
  have hzlive : z∈liveRows C E U radius (partRows true η χ₀ Q m C E U radius) := by
    rw [exceptional_part_live]
    exact hz
  have hnz := live_norm_le_four_radius C E U radius _ z hzlive
  have hnz0 : 0≤normValue z := Nat.cast_nonneg _
  have hnz0' : 0≤normValue (-z) := Nat.cast_nonneg _
  have hrad : 0≤radius := (liveRows_geometry C E U radius _ z hzlive).1.le
  have hpool : 0≤poolNorm s := Finset.sum_nonneg (fun I _=>Nat.cast_nonneg _)
  have hnz' : normValue (-z)≤4*radius := by
    simpa only [normValue,Ideal.span_singleton_neg] using hnz
  have hnL := (actual_divisor_norm s E hE L hL).2
  have hτ₁ : ((τ χ).modulus.absNorm:ℝ)≤(η.modulus.absNorm:ℝ)*fixedFactor*E.absNorm := by
    exact_mod_cast (hf.physical_conductor_bounds hCE t (sourceColumns s)
      (sourceCoefficient s ha seed) radius _ Φ Kphys hK n hne χ).2
  have hτ₂ : ((τ (ξ⁻¹)).modulus.absNorm:ℝ)≤(η.modulus.absNorm:ℝ)*fixedFactor*C.absNorm := by
    exact_mod_cast (hf.physical_conductor_bounds hCE t (sourceColumns s)
      (sourceCoefficient s ha seed) radius _ Φ Kphys hK n hne (ξ⁻¹)).1
  rw [full_row_conductor,full_row_conductor]
  constructor
  · calc
      _≤((η.modulus.absNorm:ℝ)*fixedFactor*E.absNorm)*
          (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
          s.R.absNorm*C.absNorm*poolNorm s*(4*radius) := by gcongr
      _=_ := by unfold conductorBudget fixedConductorCost; ring
  · calc
      _≤((η.modulus.absNorm:ℝ)*fixedFactor*C.absNorm)*
          (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
          s.R.absNorm*E.absNorm*poolNorm s*(4*radius) := by gcongr
      _=_ := by unfold conductorBudget fixedConductorCost; ring

/-- Only canonical OLD forcing. No selected fresh-divisor parameter is
present in this inner count. -/
def countCost (Q C E : Id) (U : Finset (CommonIndex C E)) (Z M : ℝ) : ℝ :=
  (Ideal.absNorm (commonRadical Q Q):ℝ)^(2/3:ℝ)*
    (768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card*(4:ℝ)^(1/6:ℝ)*
      Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P : CommonIndex C E=>P.val)
        (leftExponent C E) (rightExponent C E) (nonunitPartitionSet C E U)):ℝ))/6))

theorem actual_rows_count (η : Character) (χ₀ : RayCharacter)
    (Q : Id) (hQ0 : Q≠0) (hQtop : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)})
    (m : O) (hm : m≠0) (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (C E : Id) (hC : Supported C) (U : Finset (CommonIndex C E))
    (hη : idealCoeff η C≠0) (radius Z M : ℝ) (hZ : 1<Z) (hr : radius≤Z^M) :
    ((partRows true η χ₀ Q m C E U radius).card:ℝ)≤countCost Q C E U Z M := by
  unfold countCost
  apply actual_canonical_exceptional_count_fixedQ η χ₀ C E hC U Q hQ0 hQtop hQ72 hη
    m hm hml hm2 _ (exceptional_part_nonzero η χ₀ Q m C E U radius)
    (exceptional_part_inducing η χ₀ Q m C E U radius) Z 4 M hZ (by norm_num)
  intro z hz
  have hzlive : z∈liveRows C E U radius (partRows true η χ₀ Q m C E U radius) := by
    rw [exceptional_part_live]
    exact hz
  exact (live_norm_le_four_radius C E U radius _ z hzlive).trans
    (mul_le_mul_of_nonneg_left hr (by norm_num))

def paidBudget (s : Source ι a b) (C E : Id) (J : ℕ) (control : Finset (ℕ×ℕ))
    (Z ε α δ : ℝ) : ℝ :=
  (C.absNorm:ℝ)^δ*(E.absNorm:ℝ)^δ*(baseBudget s J control Z ε)^2/
    ((C.absNorm:ℝ)*E.absNorm)*min (commonSaving s C α) (commonSaving s E α)

theorem paid_budget_nonneg (s : Source ι a b) (C E : Id) (J : ℕ)
    (control : Finset (ℕ×ℕ)) (Z ε α δ : ℝ) : 0≤paidBudget s C E J control Z ε α δ := by
  have hs := le_min (commonSaving_nonneg s C α) (commonSaving_nonneg s E α)
  unfold paidBudget
  positivity

def actualPair (s : Source ι a b) (ha : 0<a) (η : Character)
    (C E : Id) (hC : Supported C) (hE : Supported E) (U : Finset (CommonIndex C E))
    (seed : Id) (χ ξ : RayCharacter) (t θ X Y : ℝ) (rows : Finset O) : ℝ :=
  ∑L∈actualDivisors s E hE,‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*∑z∈rows,
    ‖movingWindow s ha η χ (commonFrequencyGenerator C E*nonunitFrequencyGenerator C E U)
      C hC seed L t θ X z‖*
    ‖conjugateWindow s ha η (ξ⁻¹) (commonFrequencyGenerator C E*nonunitFrequencyGenerator C E U)
      E hE seed L t θ Y (-z)‖

/-- Concrete inner exceptional pair, with every analytic pair premise
discharged. K4 and 1/W remain explicit; the displayed count is canonical
old forcing only. The final physical exponent ledger is a separate step. -/
theorem uniform_actual_pair (N : ℕ) (α Bcap a b ε δ : ℝ)
    (hα : 0≤α) (hα4 : α<4/5) (hBcap : 0≤Bcap)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hδ : 0<δ) (hgap : α+2*δ<1) :
    ∃J : ℕ,∃control : Finset (ℕ×ℕ),(0,0)∈control ∧
      ∀Q : Id,Q≠0→Q≠⊤→Q≤Ideal.span {(72:O)}→∃A : ℝ,0<A ∧
      ∀(ι : Type u) [Fintype ι],∀s : Source ι a b,∀cover : OriginalEnclosure s,
      ∀Z : ℝ,1<Z→Fintype.card ι≤N→(s.Fhole.absNorm:ℝ)≤Z^Bcap→
      (∏i,2*s.P i)≤Z^Bcap→
      ∀(η : Character)(χ₀ : RayCharacter)(m : O),m≠0→goodLambda∣m→(2:O)∣m→
      ∀(C E : Id)(hC : Supported C)(hE : Supported E),primeSupport C=primeSupport E→
      ∀(U : Finset (CommonIndex C E))(τ : RayCharacter→Character),Family η C E hC hE U τ→
      ∀seed : Id,seed∣C→seed∣E→idealCoeff η C≠0→
      ∀(t radius M K W : ℝ)(Φ : 𝓢(ℝ,ℂ)),0<K → 0<W → radius≤Z^M →
      ∀n : Fin 4→ℤ,
      physicalBlock η t (sourceColumns s) (sourceCoefficient s ha seed) C E hC hE U radius
        (partRows true η χ₀ Q m C E U radius) Φ (16*K*W^4) n≠0→
      conductorBudget s η C E radius≤Z^Bcap→
      ∀(χ ξ : RayCharacter)(θ X Y : ℝ),0<X→0<Y→
      actualPair s ha η C E hC hE U seed χ ξ t θ X Y
          (partRows true η χ₀ Q m C E U radius)/W≤
        A*countCost Q C E U Z M*paidBudget s C E J control Z ε α δ*
          heightCost t θ^J*heightCost t (-θ)^J*(windowMoment J)^2/W := by
  obtain ⟨J,control,h00,hwindow⟩ := uniform_original_window_pair N α Bcap a b ε δ
    hα hα4 hBcap ha hb hε hδ hgap
  obtain ⟨Cb,hCb,hbudget⟩ := uniform_pair_budget N δ hδ
  refine ⟨J,control,h00,?_⟩
  intro Q hQ0 hQtop hQ72
  obtain ⟨Cw,hCw,hwindow⟩ := hwindow Q hQ0
  refine ⟨Cw*Cb,mul_pos hCw hCb,?_⟩
  intro ι instι s cover Z hZ hι hF hP η χ₀ m hm hml hm2 C E hC hE hCE U τ hf
    seed hsC hsE hη t radius M K W Φ hK hW hrad n hne hcond χ ξ θ X Y hX hY
  let rows := partRows true η χ₀ Q m C E U radius
  let Ds := actualDivisors s E hE
  have hind := actual_family_both_rows η χ₀ Q hQ72 m hm hml hm2 C E hC hE U τ hf radius
  have hK4 : 0<16*K*W^4 := by positivity
  have hc (z : O) (hz : z∈rows) (L : Id) (hL : L∈live Ds) :=
    actual_conductor_bounds s ha η χ₀ Q m C E hC hE hCE U τ hf seed t radius Φ
      (16*K*W^4) hK4 n hne χ ξ z hz L ((mem_live Ds L).mp hL).1
  have hp := hwindow ι s cover Z hZ.le hι hF hP C E hC hE seed hsC hsE
    η (τ χ) (τ (ξ⁻¹)) χ ξ (commonFrequencyGenerator C E*nonunitFrequencyGenerator C E U)
    (fun I hI hcop v=>hf.height_eq χ I hI (Or.inl hcop) v)
    (fun I hI hcop v=>hf.height_eq (ξ⁻¹) I hI (Or.inr hcop) v)
    t θ X Y hX hY rows (live Ds) (fun L=>(UniqueFactorizationMonoid.moebius L:ℂ))
    (exceptional_part_nonzero η χ₀ Q m C E U radius)
    (live_squarefree Ds) (fun L _=>moebius_norm_le_one L)
    (fun z hz L hL=>(hc z hz L hL).1.trans hcond)
    (fun z hz L hL=>(hc z hz L hL).2.trans hcond)
    (hind.1 χ) (hind.2 (ξ⁻¹))
  have hp' : actualPair s ha η C E hC hE U seed χ ξ t θ X Y rows≤
      (rows.card:ℝ)*Cw*pairBudget s hb cover C E J control Z ε α*
        heightCost t θ^J*heightCost t (-θ)^J*(windowMoment J)^2 := by
    unfold actualPair
    rw [sum_norm_moebius_live]
    exact hp
  have hb' : pairBudget s hb cover C E J control Z ε α≤
      Cb*paidBudget s C E J control Z ε α δ := by
    have hh := hbudget ι a b s hb cover hι C E hC.1 hE.1 J control Z ε α
      (zero_le_one.trans hZ.le) hα
    simpa only [paidBudget,mul_assoc,div_eq_mul_inv] using hh
  have hcount : (rows.card:ℝ)≤countCost Q C E U Z M :=
    actual_rows_count η χ₀ Q hQ0 hQtop hQ72 m hm hml hm2 C E hC U hη radius Z M hZ hrad
  have hpB := paid_budget_nonneg s C E J control Z ε α δ
  have hcnt : 0≤countCost Q C E U Z M := (Nat.cast_nonneg _).trans hcount
  have hp₀ := pair_budget_nonneg s hb cover C E J control Z ε α (zero_le_one.trans hZ.le)
  have hh₁ := (heightCost_pos t θ).le
  have hh₂ := (heightCost_pos t (-θ)).le
  apply div_le_div_of_nonneg_right _ hW.le
  apply hp'.trans
  calc
    _≤countCost Q C E U Z M*Cw*(Cb*paidBudget s C E J control Z ε α δ)*
        heightCost t θ^J*heightCost t (-θ)^J*(windowMoment J)^2 := by
      gcongr
    _=_ := by ring

end
end Candidate.FourthPower.MixedInnerExceptionalPair
