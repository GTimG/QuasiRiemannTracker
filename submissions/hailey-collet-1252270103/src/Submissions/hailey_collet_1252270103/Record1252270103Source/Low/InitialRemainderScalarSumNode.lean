/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual selected first-column remainder sums after pool, allocation and label
counting. The only outstanding admissions are geometric and numerical. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.InitialRemainderScalarSum
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.InitialRemainderScalarNode
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.ExceptionalInitialGeometry

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Low.InitialRemainder
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily Cycle61InitialMass Cycle61Moment CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentOriginalCommonHarmonic
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildInput CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstAnnularMajorant
open CenteredMomentSourceInputTailUniform (plainControl)
open QRH.Record1252270103Source.High.CoupledFirst
open QRH.Record1252270103Source.Admission
open QRH.Record1252270103Source.Pool
open QRH.Record1252270103Source.MarkedMainRemainder
open QRH.Record1252270103Source.ExceptionalPrice
open ConcretePrimeRowBridge CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open QRH.Record1252270103Low QRH.Record1252270103Source.InitialPhysical
open Record1252270103Finite Record1252270103StepScalar
local notation "O"=>HeckeFamily.O


def initialCann (N : ℕ) : ℝ := (2*2:ℝ)^N*(9/4)^2

theorem initialCann_pos (N : ℕ) : 0 < initialCann N := by unfold initialCann; positivity

variable (rayM : Ideal O) [NeZero rayM]
local instance : Finite (O⧸rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤H)
variable (Wslot : ℝ→ℂ) (hW : ContDiff ℝ ∞ Wslot)
variable (hsW : Function.support Wslot⊆Set.Icc (1:ℝ) 2)

/-- Uniform constants are chosen before Z, all original slot types, raw scales,
profiles, heights, nodes, selected labels and allocations. The canonical
source-face gap and the radius cap are discharged internally. -/
theorem eventual_initial_remainder_sums (N : ℕ) (ell epsMass epsZero epsCount : ℝ)
    (hell : 0<ell) (hmass : 0<epsMass) (hzero : 0≤epsZero) (hcount : 0<epsCount) :
    ∃Czero Ctail : ℝ,0<Czero ∧ 0<Ctail ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀{ι : Type}[Fintype ι][DecidableEq ι](hZ : 0<Z)(η η₀ : Character)(R₀ : Ideal O)
      (θ : ι→RayQuotient.Characters rayM H)(w v : ι→ℝ)(ht : ℝ)(p : Profiles (1/4) (9/4))
      (X₁ X₂ Y₁ Y₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂)(hY₁ : 0<Y₁)(hY₂ : 0<Y₂)
      (hprod : Y₁*Y₂=X₁*X₂),
    let s:=initialInput rayM H hH Wslot hW hsW Z hZ η η₀ R₀ θ w v ht
      p (by norm_num) X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
    ∀(K : ℚ)(n low : Source)(b width : ℝ), RealGeometry K n low b→
      0≤(n.allowance:ℝ)→0≤(n.L:ℝ)→(low.B:ℝ)≤1→width≤PhysicalLowGuard.step n→
      (globalFace (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ)).Admissible
        (length Z X₁) (length Z X₂) (∑i,w i) 1→
      b-(n.allowance:ℝ)-width≤∑i,w i→(∑i,w i)≤b→Fintype.card ι≤N→
    let a:=sourceAReal n low b
    let allowance:=(n.allowance:ℝ)
    let Cann:=initialCann N
    ∀(modifier : Tuple ι→ℂ)(R : Ideal O)(W : 𝓢(ℝ,ℂ))(ξ reserve loss saving : ℝ)(hK : 0<Z^(1:ℝ)),
      frequencyLoss Z 32 ξ+reserve+2*epsMass+loss+epsZero≤2*allowance→
    ∀(P : Finset (Ideal O))(mesh BD Bsource : ℝ)(depth : ℕ),
      FixedCellPoolData P Z a ell mesh loss BD Bsource depth→
    ∀(reflected : Bool)(bin : ℤ×(Fin 5→ℤ))(J : Type)[Fintype J]
      (column : J→FirstColumnIndex (geometryFirstSource s modifier R 1 (Z^(1:ℝ)) Z ξ hK bin)),
      Function.Injective (fun j=>(FirstFamily.firstLabel s modifier R 1 (Z^(1:ℝ)) Z ξ hK bin (column j),(column j).2.1.val))→
      (∀j,column j∈firstLiveColumns (geometryFirstSource s modifier R 1 (Z^(1:ℝ)) Z ξ hK bin) (fun _=>logAnnulus))→
      (∀j,((column j).2.1.val.absNorm:ℝ)≤Z^(4:ℝ))→
    let C:=fun j=>geometryColumnIdeal reflected s modifier R 1 (Z^(1:ℝ)) Z ξ hK bin (column j)
    let label:=fun j=>FirstFamily.firstLabel s modifier R 1 (Z^(1:ℝ)) Z ξ hK bin (column j)
    let Hmain:=fun j=>firstMainRadius reflected (Z^(1:ℝ)) (volume s) Z ξ (3*a) reserve (label j)
    let radius:=fun j=>literalFirstRadius reflected (Z^(1:ℝ)) (volume s) Z ξ reserve (label j)
    let H0:=fun j=>(geometryFirstSource s modifier R 1 (Z^(1:ℝ)) Z ξ hK bin (column j).1).H0
    let scalar:=fun j=>balancedColumnScalar reflected s modifier R 1 (Z^(1:ℝ)) Z ξ 1
      (Real.logb Z (volume s)) hK bin (fun q=>normPhase (coordinateBlock s modifier R 1 W (Z^(1:ℝ)) Z ξ q)) (column j)
    let factor:=geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin
    (∀j,0≤radius j+6*a)→(∀j,radius j+6*a≤32)→
    ∀(alloc : ∀j,actualAllocations s.pools (C j))(τ : J→Character)(t : J→ℝ),
      (∀j,frozenCoefficient (alloc j).val (C j) R s.ν s.W s.P≠0)→
    let amplitude:=fun j=>‖scalar j‖^2*
      (((bands (H0 j)).card:ℝ)*((actualAllocations s.pools (C j)).card:ℝ)^2/(P.card:ℝ)*
        ((radius j+6*a)/ell))*‖frozenCoefficient (alloc j).val (C j) R s.ν s.W s.P‖^2
    (∀j,sourceRadius (child s (C j) R (alloc j) (τ j) (t j))≤
      (Cann/((C j).absNorm:ℝ))*volume s) ∧
    ((∑j,amplitude j*(plainControl (child s (C j) R (alloc j) (τ j) (t j)) (p.profile 0) (p.profile 1))^2*
        Hmain j*(Cann/((C j).absNorm:ℝ))^(1+epsZero)*(volume s)^epsZero/
          ((column j).2.1.val.absNorm:ℝ))≤
      Czero*(SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*SchwartzMap.seminorm ℝ 0 0 (p.profile 1))^2*factor*
        Z^(-a-allowance+2*epsCount)) ∧
    ((∑j,amplitude j*(plainControl (child s (C j) R (alloc j) (τ j) (t j)) (p.profile 0) (p.profile 1))^2*
        Hmain j*(volume (child s (C j) R (alloc j) (τ j) (t j))/volume s)*Z^(-saving)/
          ((column j).2.1.val.absNorm:ℝ))≤
      Ctail*(SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*SchwartzMap.seminorm ℝ 0 0 (p.profile 1))^2*factor*
        Z^(-a-allowance-saving+2*epsCount)) := by
  obtain ⟨Cz,Ct,hCz,hCt,hbound⟩:=eventual_actual_remainder_sums N
    (initialSlotBound Wslot hW hsW) (initialCann N) ell epsMass epsZero epsCount
    (initialSlotBound_ge_one Wslot hW hsW) (initialCann_pos N) hell hmass hzero hcount
  refine ⟨Cz,Ct,hCz,hCt,?_⟩
  filter_upwards [hbound,eventual_radius_absorption N 1 (by norm_num)] with Z hz hrad
  refine ⟨hz.1,?_⟩
  intro ι _ _ hZ η η₀ R₀ θ w v ht p X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod s
    K n low b width hg he hL hB hw hadm hlo hhi hN a allowance Cann
    modifier R W ξ reserve loss saving hK herr P mesh BD Bsource depth hpool
    reflected bin J _ column hinj hlive hcap C label Hmain radius H0 scalar factor hr0 hr alloc τ t hf amplitude
  have hgap:=initial_main_amplification_gap rayM H hH Wslot hW hsW Z hZ η η₀ R₀ θ w v ht
    p X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod K n low b width hz.1 hg he hL hB hw hadm hlo hhi
  have hvol:volume s≤Z := by
    have hlog:Real.logb Z (volume s)≤1:=by linarith only [hgap,hg.a_pos,he]
    calc
      _=Z^(Real.logb Z (volume s)):=(Real.rpow_logb hZ hz.1.ne' (volume_pos s)).symm
      _≤Z^(1:ℝ):=Real.rpow_le_rpow_of_exponent_le hz.1.le hlog
      _=Z:=Real.rpow_one Z
  have hsource:sourceRadius s≤Z^(2:ℝ) := by
    have hid:=initial_source_radius_identity rayM H hH Wslot hW hsW Z hZ η η₀ R₀ θ w v ht
      p X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hprod
    calc
      _=(2:ℝ)^Fintype.card ι*(9/4)^2*volume s:=hid
      _≤(2:ℝ)^N*(9/4)^2*Z:=mul_le_mul
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hN) (sq_nonneg _))
        hvol (volume_pos s).le (by positivity)
      _≤Z^(2:ℝ):=by convert hrad.2 using 1 <;> norm_num
  have hb:=hz.2 s modifier R 1 W (p.profile 0) (p.profile 1) ξ a reserve allowance loss saving hK
    hN (fun _=>le_rfl) le_rfl le_rfl squarefree_one one_ne_zero
    (initial_plain_zero p (by norm_num) 0) (initial_plain_zero p (by norm_num) 1)
    hsource (fun x hx=>(p.support 0 hx).1) (fun x hx=>(p.support 1 hx).1)
    hg.a_pos.le he hgap herr P mesh BD Bsource depth hpool reflected bin J column hinj hlive hcap
    hr0 hr alloc τ t hf
  refine ⟨?_,by simpa only [map_one,Nat.cast_one,div_one] using hb⟩
  intro j
  have hC:C j≠0 := by
    cases reflected
    · exact (geometryFirstSource s modifier R 1 (Z^(1:ℝ)) Z ξ hK bin (column j).1).hC.1
    · exact (geometryFirstSource s modifier R 1 (Z^(1:ℝ)) Z ξ hK bin (column j).1).hD.1
  have hc:=selected_child_radius_cap s N 2 2 (9/4) hN (by norm_num) (by norm_num)
    (by norm_num) (fun _=>by norm_num [s,initialInput]) (fun _=>le_rfl) le_rfl
    (by norm_num [s,initialInput]) (by norm_num [s,initialInput]) le_rfl le_rfl
    (C j) R hC (alloc j) (τ j) (t j) (hf j)
  have hcann:(2:ℝ)^N*(9/4)^2*2^N=Cann:=by dsimp only [Cann,initialCann];rw [mul_pow];ring
  rw [hcann] at hc
  exact hc

end
end QRH.Record1252270103Source.Low.InitialRemainder
#print axioms QRH.Record1252270103Source.Low.InitialRemainder.initialCann_pos
#print axioms QRH.Record1252270103Source.Low.InitialRemainder.eventual_initial_remainder_sums
