/- Reserve-parametric adaptation by Joseph Bebel (2026). -/
/- Copyright (c) 2026 Sil. Apache-2.0.
Actual ORIGINAL first-Poisson zero and discarded terms at the restored root.
The checked normalized remainder theorems are applied, with all polynomial
caps supplied by the actual root data. No zero/tail energy bound is assumed.
This is distinct from the outer SECOND-Poisson companions of GroupedConsumer.

-/
import Candidate.Local.Qrh.PR98Improvement.RestoredRootEnergy
import Candidate.Local.Qrh.PR98Improvement.RecenteredRootSource
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedFirstRemainder
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedOriginalTailCaps

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.PR98.RestoredFirstRemainders
universe u
noncomputable section
variable [Candidate.PR98.RepairedRootParameters.Reserve]
open Candidate.FourthPower
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open ConcreteTraceCRT ConcretePrimeRowBridge CanonicalRowCompletion CompletedGauss
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentFirstLocalization
open CenteredMomentUncenteredTerminal CenteredMomentFirstSectorLocalization
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow
open MixedOriginalTail MixedOriginalTailCaps MixedOriginalNormCap
open MixedInnerExceptionalBlock
open MixedFirstPhysicalApplication MixedFirstLiveRemainders MixedFirstRemainder
open MixedFirstRebase RestoredRootSource Candidate.PR98.RestoredRootEnergy
open EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq α := Classical.decEq _

/-- The artificial selected factor1 is exactly absent on every column
that occurs in the first zero/tail sums. This uses the proved PRIMARY
generator identity, not an assumption about the separately chosen idealGenerator. -/
theorem selected_one_on_supported {ι : Type*} [Fintype ι] {a b : ℝ}
    (s : Source ι a b) (ha : 0<a) (seed I : Id) (hI : Supported I) :
    selectedCoefficient s ha seed 1 I=sourceCoefficient s ha seed I := by
  simp only [selectedCoefficient,selectedTwist,CompletedGauss.primaryGenerator_one,
    idealRowHom_one_supported I hI,one_pow,mul_one]

theorem zero_selected_one {ι : Type*} [Fintype ι] {a b : ℝ}
    (s : Source ι a b) (ha : 0<a) (seed : Id)
    (η : Character) (m A : O) (tp K : ℝ) (Ψ : 𝓢(ℝ,ℂ)) :
    zeroEnergy η m A tp (sourceColumns s) (selectedCoefficient s ha seed 1) Ψ K=
      zeroEnergy η m A tp (sourceColumns s) (sourceCoefficient s ha seed) Ψ K := by
  unfold zeroEnergy
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  rw [selected_one_on_supported s ha seed I (Finset.mem_filter.mp I.property).2,
      selected_one_on_supported s ha seed J (Finset.mem_filter.mp J.property).2]

theorem tail_selected_one {ι : Type*} [Fintype ι] {a b : ℝ}
    (s : Source ι a b) (ha : 0<a) (seed : Id)
    (η : Character) (m A : O) (tp K Z ξ : ℝ) (Ψ : 𝓢(ℝ,ℂ)) :
    CenteredMomentFirstSectorLocalization.discardedEnergy η m A tp (sourceColumns s) (selectedCoefficient s ha seed 1)
      Ψ K (sourceVolume s) Z ξ=
      CenteredMomentFirstSectorLocalization.discardedEnergy η m A tp (sourceColumns s) (sourceCoefficient s ha seed)
        Ψ K (sourceVolume s) Z ξ := by
  unfold CenteredMomentFirstSectorLocalization.discardedEnergy
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  rw [selected_one_on_supported s ha seed I (Finset.mem_filter.mp I.property).2,
      selected_one_on_supported s ha seed J (Finset.mem_filter.mp J.property).2]

/-- Exact first-sector identity for the ORIGINAL source coefficient. -/
theorem original_first_split {ι : Type*} [Fintype ι] {a b : ℝ}
    (s : Source ι a b) (ha : 0<a) (η : Character) (m A : O)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (tp K Z ξ : ℝ) (Ψ : 𝓢(ℝ,ℂ)) (hK : 0<K) :
    finiteHeckeEnergy η m A tp (sourceColumns s) (sourceCoefficient s ha 1) Ψ K=
      zeroEnergy η m A tp (sourceColumns s) (sourceCoefficient s ha 1) Ψ K+
        CenteredMomentFirstSectorLocalization.retainedEnergy η m A tp (sourceColumns s) (sourceCoefficient s ha 1)
          Ψ K (sourceVolume s) Z ξ+
        CenteredMomentFirstSectorLocalization.discardedEnergy η m A tp (sourceColumns s) (sourceCoefficient s ha 1)
          Ψ K (sourceVolume s) Z ξ :=
  finiteHeckeEnergy_sector_localized η m A tp hmLam hm2 (sourceColumns s)
    (sourceCoefficient s ha 1) Ψ K (sourceVolume s) Z ξ hK

def plainControls : Finset (ℕ×ℕ) := {(0,0)}

def profileFactor (W : ℝ → ℂ) (hW : Continuous W)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (N : ℕ) : ℝ :=
  4*(RestoredRootSource.slotBound W hW hWs)^(2*N)

theorem profileFactor_pos (W : ℝ → ℂ) (hW : Continuous W)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (N : ℕ) :
    0<profileFactor W hW hWs N := by
  have hk : 0<RestoredRootSource.slotBound W hW hWs :=
    zero_lt_one.trans_le (RestoredRootSource.slotBound_spec W hW hWs).1
  unfold profileFactor
  positivity

variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- Both stored common-height phases have norm1. Only the original
ordinary (0,0) profile control and the fixed marked bound remain. -/
theorem root_profile_sq {ι : Type u} [Fintype ι]
    (W : ℝ → ℂ) (hW : Continuous W) (hWs : Function.support W⊆Icc (1:ℝ) 2)
    (N : ℕ) (r : RestoredRootSource.Data M H ι)
    (hcard : Fintype.card ι≤N) (hWr : r.W=W) :
    (profileCap (r.source hH))^2≤
      profileFactor W hW hWs N*(r.p.control plainControls)^2 := by
  let B:=RestoredRootSource.slotBound W hW hWs
  have hB : 1≤B := (RestoredRootSource.slotBound_spec W hW hWs).1
  have hB0 : 0<B := zero_lt_one.trans_le hB
  have he : RestoredRootSource.slotBound r.W r.hW r.hWs=B := by
    cases hWr
    rfl
  have hcap : profileCap (r.source hH)=
      2*(r.p.control plainControls)*B^Fintype.card ι := by
    simp only [profileCap,RestoredRootSource.Data.source,he,
      Finset.prod_const,Finset.card_univ,Profiles.control,plainControls,supControl]
    ring
  have hp:=r.p.control_nonneg plainControls
  have hbpow:=pow_le_pow_right₀ hB hcard
  have hsq := pow_le_pow_left₀
    (show 0≤2*(r.p.control plainControls)*B^Fintype.card ι by positivity)
    (mul_le_mul_of_nonneg_left hbpow (by positivity : 0≤2*(r.p.control plainControls))) 2
  rw [hcap]
  apply hsq.trans_eq
  have hpows : (B^N)^2=B^(2*N) := by rw [←pow_mul,Nat.mul_comm]
  unfold profileFactor
  change (2*(r.p.control plainControls)*B^N)^2=4*B^(2*N)*(r.p.control plainControls)^2
  rw [mul_pow,hpows]
  ring

/-- One event supplies every numerical first-remainder input from the
actual root lengths and surviving total width. B=8 is independent of N
and of the source mesh. K=cRad*Z covers K=Z and the fixed ball-profile dilation. -/
theorem root_caps_eventually (N : ℕ) (cRad : ℝ) (hcRad : 1≤cRad) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(ι : Type u) [Fintype ι],∀r : RestoredRootSource.Data M H ι,
      Fintype.card ι≤N → r.Z=Z → (∑i,r.w i)≤3/50 →
      poolCap (r.source hH)≤Z^(8:ℝ) ∧
      sourceNormCap (r.source hH).P (9/4) (r.source hH).T (r.source hH).d≤Z^(8:ℝ) ∧
      sourceVolume (r.source hH)≤Z^(8:ℝ) ∧
      0<cRad*Z ∧ cRad*Z≤Z^(8:ℝ) ∧ (cRad*Z)⁻¹≤Z^(8:ℝ) := by
  filter_upwards [eventually_source_caps N (9/4) 3 1 1 (by norm_num),
    eventually_ge_atTop (5:ℝ),eventually_ge_atTop cRad] with Z hcaps hZ5 hcZ
  have hZ:=hcaps.1
  have hz:0<Z:=zero_lt_one.trans hZ
  refine ⟨hZ,?_⟩
  intro ι instι r hn hrZ htotal
  have hlen:=r.source_length_caps hH (by simpa only [hrZ] using hZ5)
  have hlen' : (r.source hH).X₁≤Z^(3:ℝ) ∧ (r.source hH).X₂≤Z^(3:ℝ) ∧
      (r.source hH).Y₁≤Z^(3:ℝ) ∧ (r.source hH).Y₂≤Z^(3:ℝ) := by
    simpa only [hrZ] using hlen
  have hp : (∏i,(r.source hH).P i)≤Z^(1:ℝ) := by
    change (∏i,r.Z^(r.w i))≤Z^(1:ℝ)
    rw [hrZ,←Real.rpow_sum_of_pos hz]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have hs:=hcaps.2 ι (1/4) (r.source hH) hn hlen'.1 hlen'.2.1
    hlen'.2.2.1 hlen'.2.2.2 hp
  have hvol : sourceVolume (r.source hH)≤Z^(8:ℝ) := by
    change (r.source hH).X₁*(r.source hH).X₂*(∏i,(r.source hH).P i)≤_
    have hx₂:0≤(r.source hH).X₂:=
      ((r.source hH).hL.trans_le (r.source hH).hX₂).le
    have hp₀:0≤∏i,(r.source hH).P i:=
      Finset.prod_nonneg (fun i _=>zero_le_one.trans ((r.source hH).hP i))
    calc
      _≤Z^(3:ℝ)*Z^(3:ℝ)*Z^(1:ℝ) :=
        mul_le_mul (mul_le_mul hlen'.1 hlen'.2.1 hx₂ (Real.rpow_nonneg hz.le _))
          hp hp₀ (mul_nonneg (Real.rpow_nonneg hz.le _) (Real.rpow_nonneg hz.le _))
      _=Z^(7:ℝ) := by rw [←Real.rpow_add hz,←Real.rpow_add hz];norm_num
      _≤_ := Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num)
  have hcr:0<cRad:=zero_lt_one.trans_le hcRad
  have hK1:1≤cRad*Z:=one_le_mul_of_one_le_of_one_le hcRad hZ.le
  have hKcap:cRad*Z≤Z^(8:ℝ) := by
    calc
      _≤Z*Z:=mul_le_mul_of_nonneg_right hcZ hz.le
      _=Z^(2:ℝ):=by rw [Real.rpow_two];ring
      _≤_:=Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num)
  have hinv:(cRad*Z)⁻¹≤Z^(8:ℝ) :=
    (inv_le_one_of_one_le₀ hK1).trans (Real.one_le_rpow hZ.le (by norm_num))
  refine ⟨?_,?_,hvol,mul_pos hcr hz,hKcap,hinv⟩
  · simpa only [show (2*(3:ℝ)+1+1)=8 by norm_num] using hs.1
  · simpa only [show (2*(3:ℝ)+1+1)=8 by norm_num] using hs.2

set_option maxHeartbeats 600000 in
/-- Actual first zero/tail provider for any unit-prefix source with the
original polynomial caps. The profile cost is fixed before the source;
there is no energy estimate among the inputs. -/
theorem uniform_unit_zero_tail
    (N : ℕ) (Ψ : 𝓢(ℝ,ℂ)) (cRad Cp ε ξ : ℝ)
    (hcRad : 1≤cRad) (hCp : 0<Cp) (hε : 0<ε) (hξ : 0<ξ) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(ι : Type u) [Fintype ι],∀s : Source ι (1/4) (9/4),
      Fintype.card ι≤N  →  s.d=(1,1)  →  ∀P : ℝ,0≤P  →
      (profileCap s)^2≤Cp*P^2  →  poolCap s≤Z^(8:ℝ)  →
      sourceNormCap s.P (9/4) s.T s.d≤Z^(8:ℝ)  →  sourceVolume s≤Z^(8:ℝ)  →
    ∀(η : Character)(m A : O)(tp : ℝ),
      ‖zeroEnergy η m A tp (sourceColumns s)
        (sourceCoefficient s (by norm_num) 1) Ψ (cRad*Z)‖/sourceVolume s+
      ‖CenteredMomentFirstSectorLocalization.discardedEnergy η m A tp (sourceColumns s)
        (sourceCoefficient s (by norm_num) 1) Ψ (cRad*Z)
          (sourceVolume s) Z ξ‖/sourceVolume s≤C*P^2*Z^(1+ε) := by
  obtain ⟨Cz,hCz,hzero⟩:=normalized_first_zero N (ε/16) (by positivity)
  obtain ⟨control,Ct,hCt,htail⟩:=normalized_first_tail N (9/4) 8 ξ 1 (by norm_num) hξ
  let F0:=‖paperRadialFourier Ψ 0‖
  let Ft:=control.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ
  have hF0:0≤F0:=norm_nonneg _
  have hFt:0≤Ft:=apply_nonneg _ _
  let Cz':=Cz*cRad*Cp*(1+F0)*((9/4:ℝ)^2*(2:ℝ)^N)
  let Ct':=Ct*Cp*(1+Ft)
  have hcr:0<cRad:=zero_lt_one.trans_le hcRad
  have hCz':0<Cz':=by dsimp only [Cz'];positivity
  have hCt':0<Ct':=by dsimp only [Ct'];positivity
  refine ⟨Cz'+Ct',add_pos hCz' hCt',?_⟩
  filter_upwards [eventually_ge_atTop (2:ℝ),eventually_ge_atTop cRad,htail] with Z hZ2 hcZ ht
  have hZ:1<Z:=by linarith
  have hz:0<Z:=zero_lt_one.trans hZ
  have hK:0<cRad*Z:=mul_pos hcr hz
  have hKcap:cRad*Z≤Z^(8:ℝ):=by
    calc
      _≤Z*Z:=mul_le_mul_of_nonneg_right hcZ hz.le
      _=Z^(2:ℝ):=by rw [Real.rpow_two];ring
      _≤_:=Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num)
  have hKinv:(cRad*Z)⁻¹≤Z^(8:ℝ):=
    (inv_le_one_of_one_le₀ (one_le_mul_of_one_le_of_one_le hcRad hZ.le)).trans
      (Real.one_le_rpow hZ.le (by norm_num))
  refine ⟨hZ,?_⟩
  intro ι instι s hn hunit P hP hprofile hpool hnorm hvol η m A tp
  have hnorm0:0≤sourceNormCap s.P (9/4) s.T s.d := by
    rw [source_cap_factored]
    have hp:0≤∏i,s.P i:=Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.hP i))
    have hT:=s.total_pos
    have hd:0<pairNorm s.d:=pairNorm_pos s.hd.1 s.hd.2
    positivity
  have hnormpow:(sourceNormCap s.P (9/4) s.T s.d)^(ε/16)≤Z^(ε/2) := by
    apply (Real.rpow_le_rpow hnorm0 hnorm (by positivity : 0≤ε/16)).trans_eq
    rw [←Real.rpow_mul hz.le]
    congr 1
    ring
  have hprefix : (9/4:ℝ)^2*(2:ℝ)^Fintype.card ι/pairNorm s.d≤
      (9/4:ℝ)^2*(2:ℝ)^N := by
    rw [hunit]
    simpa only [pairNorm,map_one,Nat.cast_one,mul_one,div_one] using
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hn)
        (sq_nonneg (9/4:ℝ))
  have hprefix0:0≤(9/4:ℝ)^2*(2:ℝ)^Fintype.card ι/pairNorm s.d:=
    div_nonneg (by positivity) (pairNorm_pos s.hd.1 s.hd.2).le
  have hz0:=hzero ι (1/4) (9/4) s hn (by norm_num) (by norm_num)
    1 1 η m A tp (cRad*Z) Ψ hK.le
  rw [zero_selected_one] at hz0
  have ht0:=ht.2 ι (1/4) s hn (by norm_num) (by norm_num)
    1 1 η m A tp (cRad*Z) Ψ hK hpool hvol hKcap hKinv
  rw [tail_selected_one] at ht0
  have hzpaid : ‖zeroEnergy η m A tp (sourceColumns s)
      (sourceCoefficient s (by norm_num) 1) Ψ (cRad*Z)‖/sourceVolume s≤
      Cz'*P^2*Z^(1+ε) := by
    apply hz0.trans
    calc
      _≤Cz*(cRad*Z)*(Cp*P^2)*(1+F0)*((9/4:ℝ)^2*(2:ℝ)^N)*Z^(ε/2) := by
        gcongr <;> (dsimp only [F0]; linarith)
      _=Cz'*P^2*Z^(1+ε/2) := by
        rw [Real.rpow_add hz,Real.rpow_one]
        dsimp only [Cz']
        ring
      _≤_ := by gcongr <;> linarith
  have htpaid : ‖CenteredMomentFirstSectorLocalization.discardedEnergy η m A tp (sourceColumns s)
      (sourceCoefficient s (by norm_num) 1) Ψ (cRad*Z) (sourceVolume s) Z ξ‖/
        sourceVolume s≤Ct'*P^2*Z^(1+ε) := by
    apply ht0.trans
    calc
      _≤Ct*(Cp*P^2)*(1+Ft)*Z^(-(1:ℝ)) := by
        gcongr <;> (dsimp only [Ft]; linarith)
      _=Ct'*P^2*Z^(-(1:ℝ)) := by dsimp only [Ct'];ring
      _≤_ := by gcongr <;> linarith
  exact (add_le_add hzpaid htpaid).trans_eq (by ring)

theorem uniform_root_zero_tail
    (N : ℕ) (W : ℝ → ℂ) (hW : Continuous W)
    (hWs : Function.support W⊆Icc (1:ℝ) 2)
    (Ψ : 𝓢(ℝ,ℂ)) (cRad ε ξ : ℝ) (hcRad : 1≤cRad) (hε : 0<ε) (hξ : 0<ξ) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(ι : Type u) [Fintype ι],∀r : RestoredRootSource.Data M H ι,
      Fintype.card ι≤N → r.Z=Z → r.W=W → (∑i,r.w i)≤3/50 →
    ∀(η : Character)(m A : O)(tp : ℝ),
      ‖zeroEnergy η m A tp (sourceColumns (r.source hH))
        (sourceCoefficient (r.source hH) (by norm_num) 1) Ψ (cRad*Z)‖/
          sourceVolume (r.source hH)+
      ‖CenteredMomentFirstSectorLocalization.discardedEnergy η m A tp (sourceColumns (r.source hH))
        (sourceCoefficient (r.source hH) (by norm_num) 1) Ψ (cRad*Z)
          (sourceVolume (r.source hH)) Z ξ‖/sourceVolume (r.source hH)≤
        C*(r.p.control plainControls)^2*Z^(1+ε) := by
  obtain ⟨C,hC,hbound⟩:=uniform_unit_zero_tail N Ψ cRad (profileFactor W hW hWs N)
    ε ξ hcRad (profileFactor_pos W hW hWs N) hε hξ
  refine ⟨C,hC,?_⟩
  filter_upwards [root_caps_eventually M H hH N cRad hcRad,hbound] with Z hcaps hb
  refine ⟨hb.1,?_⟩
  intro ι instι r hn hrZ hrW htotal η m A tp
  obtain ⟨hp,hnorm,hvol,_⟩:=hcaps.2 ι r hn hrZ htotal
  exact hb.2 ι (r.source hH) hn rfl (r.p.control plainControls)
    (r.p.control_nonneg plainControls) (root_profile_sq M H hH W hW hWs N r hn hrW)
    hp hnorm hvol η m A tp

/-- The repaired moving comparison source satisfies the same FIRST
remainders. Its exact common cutoff is preserved, and the all-column
pool cap, not only active coefficient support, is supplied to the tail. -/
theorem uniform_recentered_root_zero_tail
    (N : ℕ) (W : ℝ → ℂ) (hW : Continuous W)
    (hWs : Function.support W⊆Icc (1:ℝ) 2)
    (Ψ : 𝓢(ℝ,ℂ)) (cRad ε ξ : ℝ) (hcRad : 1≤cRad) (hε : 0<ε) (hξ : 0<ξ) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(ι : Type u) [Fintype ι],∀r : RestoredRootSource.Data M H ι,
      Fintype.card ι≤N → r.Z=Z → r.W=W → (∑i,r.w i)≤3/50 →
    ∀q : ℝ,∀hq : 0<q,∀hY : (r.source hH).Y₁≤q,
    ∀h₁ : q≤(r.source hH).X₁,∀h₂ : q≤(r.source hH).X₂,
    let s:=RecenteredRootSource.recenter (r.source hH) q hq hY h₁ h₂
    ∀(η : Character)(m A : O)(tp : ℝ),
      ‖zeroEnergy η m A tp (sourceColumns s)
        (sourceCoefficient s (by norm_num) 1) Ψ (cRad*Z)‖/sourceVolume s+
      ‖CenteredMomentFirstSectorLocalization.discardedEnergy η m A tp (sourceColumns s)
        (sourceCoefficient s (by norm_num) 1) Ψ (cRad*Z)
          (sourceVolume s) Z ξ‖/sourceVolume s≤C*(r.p.control plainControls)^2*Z^(1+ε) := by
  obtain ⟨C,hC,hbound⟩:=uniform_unit_zero_tail N Ψ cRad (profileFactor W hW hWs N)
    ε ξ hcRad (profileFactor_pos W hW hWs N) hε hξ
  refine ⟨C,hC,?_⟩
  filter_upwards [root_caps_eventually M H hH N cRad hcRad,hbound] with Z hcaps hb
  refine ⟨hb.1,?_⟩
  intro ι instι r hn hrZ hrW htotal q hq hY h₁ h₂ s η m A tp
  obtain ⟨hp,hnorm,hvol,_⟩:=hcaps.2 ι r hn hrZ htotal
  exact hb.2 ι s hn rfl (r.p.control plainControls)
    (r.p.control_nonneg plainControls) (root_profile_sq M H hH W hW hWs N r hn hrW)
    ((RecenteredRootSource.recenter_poolCap_le (r.source hH) q hq hY h₁ h₂).trans hp)
    hnorm hvol η m A tp

end
end Candidate.PR98.RestoredFirstRemainders
