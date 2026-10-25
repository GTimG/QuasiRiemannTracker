/- Copyright (c) 2026 Sil. Apache-2.0.
Uniform scalar/profile control of the four actual paid first coefficients.
The slot cap is explicit: Canonical alone does not bound arbitrary s.M.
No analytic energy estimate is a premise.
-/
import Candidate.SilPrior.FourthPower.MixedFirstPaidPhysical
import Candidate.SilPrior.FourthPower.MixedFirstPaidRetained
import Candidate.SilPrior.FourthPower.MixedFrozenSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.MixedFirstProfileEnvelope
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFirstAmplificationChoice QuadraticInitialBound
open CenteredMomentSecondWindowBudget CenteredMomentSecondRadicalBudget
open CenteredMomentSourceProfileMass CenteredMomentFiniteProfileExceptional
open CenteredMomentLattice CenteredMomentNaturalFixedRaySource
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalBudget MixedPrincipalPositivePart
open MixedOriginalTail MixedHeightEnvelope MixedInnerExceptionalBlock MixedInnerExceptionalLedger
open MixedFirstNonexceptionalNormalization MixedFirstExceptionalWindow
open MixedFirstFullBudget MixedFirstIntegratedWindows MixedFirstPhysicalBudget MixedFirstPaidPhysical
open MixedFirstGeometricCaps EisensteinSchwartzPoisson
open MixedFirstPaidRetained MixedFirstInactiveConductor
open CenteredMomentFirstPhysicalSource
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type u} [Fintype ι] {a b : ℝ}

def profileControl (U : Controls) : Finset (ℕ×ℕ) :=
  ({(0,0)}∪U.nonexceptionalControl)∪U.exceptionalControl

def height (t V t₁ t₂ : ℝ) : ℝ := 1+|t|+V+‖t₁‖+‖t₂‖

def heightDegree (U : Controls) : ℕ := 3*U.nonexceptionalDegree+4*U.exceptionalDegree

private def coefficientDegree (U : Controls) : Fin 4→ℕ :=
  ![0,U.nonexceptionalDegree,2*U.exceptionalDegree,0]

/-- The fixed scalars in the literal four coefficients, with all source
dimension, slot, profile and height factors factored off exactly. -/
private def fixedCoefficients (U : Controls) (c : Constants) (Q : Id) (a b : ℝ) : Fin 4→ℝ :=
  ![64*‖paperRadialFourier ballProfile 0‖*c.zero*b^2,
    4*(fixedFactor:ℝ)*c.nonexceptionalCount*c.physical*c.geometry*c.source*
      diagonalControl ballProfile*b^2*heightEnvelope 0^(2*U.nonexceptionalDegree)*
      profileMoment U.nonexceptionalDegree^2,
    c.kernel*c.exceptional*heightBase 0^(2*U.exceptionalDegree)*
      windowMoment U.exceptionalDegree^2*c.exceptionalSum*c.exceptionalCount*
      fixedQCost Q*(16:ℝ)^(5/6:ℝ)*a^(-4/3:ℝ),
    4*c.tail*U.tailControl.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile]

private theorem fixedCoefficients_nonneg (U : Controls) (c : Constants) (Q : Id)
    (a b : ℝ) (ha : 0<a) : ∀i,0≤fixedCoefficients U c Q a b i := by
  have hzero:=c.zero_pos.le
  have hn:=c.nonexceptionalCount_pos.le
  have hp:=c.physical_pos.le
  have hg:=c.geometry_pos.le
  have hs:=c.source_pos.le
  have hk:=c.kernel_nonneg
  have he:=c.exceptional_pos.le
  have hsum:=c.exceptionalSum_pos.le
  have hcount:=c.exceptionalCount_pos.le
  have ht:=c.tail_pos.le
  have hd:=diagonalControl_nonneg ballProfile
  have hQ:=fixedQCost_nonneg Q
  have hh : 0≤heightBase 0 := by unfold heightBase;positivity
  intro i
  fin_cases i <;> simp [fixedCoefficients] <;> positivity

/-- Pure real polynomial data. D=2^dimension, E=1024^dimension,
m=product of slot caps, x0/xn/xe=ordinary profile products. -/
private def scalarCoefficients (U : Controls) (k : Fin 4→ℝ)
    (D E m c0 x0 xn xe hn he : ℝ) : Fin 4→ℝ :=
  ![k 0*D^2*m^4*x0^2,
    k 1*D^3*m^2*xn^2*hn^U.nonexceptionalDegree,
    k 2*E^2*m^8*D^(4/3:ℝ)*xe^2*he^(2*U.exceptionalDegree)*c0^(-2/3:ℝ),
    k 3*m^4*x0^2/c0^4]

private theorem actual_coefficients (U : Controls) (c : Constants) (s : Source ι a b)
    (Q : Id) (c0 t V : ℝ) :
    unitCoefficients U c s Q c0 t V=
      scalarCoefficients U (fixedCoefficients U c Q a b)
        (2^Fintype.card ι) (1024^Fintype.card ι) (∏i,s.M i) c0
        (supControl s.W₁*supControl s.W₂)
        (sourceControl U.nonexceptionalControl s.W₁*sourceControl U.nonexceptionalControl s.W₂)
        (sourceControl U.exceptionalControl s.W₁*sourceControl U.exceptionalControl s.W₂)
        (sourceHeight t V (s.t₁/(2*Real.pi)) (s.t₂/(2*Real.pi)))
        (1+‖s.t₁‖+‖s.t₂‖) := by
  have hh : ((1+‖s.t₁‖+‖s.t₂‖)^U.exceptionalDegree)^2=
      (1+‖s.t₁‖+‖s.t₂‖)^(2*U.exceptionalDegree) := by
    rw [←pow_mul,Nat.mul_comm]
  funext i
  fin_cases i <;>
    simp [unitCoefficients,scalarCoefficients,fixedCoefficients,
      profileCap,profileFactor,canonicalProfile,unitOriginalFactor,
      sourceProfile,supportConstant,Real.rpow_zero,mul_one,fullMarkedCost_eq,mul_pow,hh] <;>
      ring <;> simp

private theorem scalarCoefficients_nonneg (U : Controls) (k : Fin 4→ℝ)
    (hk : ∀i,0≤k i) (D E m c0 x0 xn xe hn he : ℝ)
    (hD : 0≤D) (hE : 0≤E) (hm : 0≤m) (hc0 : 0<c0)
    (h0 : 0≤x0) (hn0 : 0≤xn) (he0 : 0≤xe) (hhn : 0≤hn) (hhe : 0≤he) :
    ∀i,0≤scalarCoefficients U k D E m c0 x0 xn xe hn he i := by
  have hk0:=hk 0
  have hk1:=hk 1
  have hk2:=hk 2
  have hk3:=hk 3
  intro i
  fin_cases i <;> simp [scalarCoefficients] <;> positivity

/-- Monotonicity uses only scalar inequalities. In particular the
negative c0 powers reverse direction and use the positive fixed floor. -/
private theorem scalarCoefficients_mono (U : Controls) (k : Fin 4→ℝ)
    (hk : ∀i,0≤k i) (D E m c0 x0 xn xe hn he Dcap Ecap Mcap cstar A H : ℝ)
    (hD : 0≤D) (hE : 0≤E) (hm : 0≤m) (hcstar : 0<cstar)
    (h0 : 0≤x0) (hn0 : 0≤xn) (he0 : 0≤xe) (hhn : 0≤hn) (hhe : 0≤he)
    (hDc : D≤Dcap) (hEc : E≤Ecap) (hmc : m≤Mcap) (hcc : cstar≤c0)
    (h0c : x0≤A) (hnc : xn≤A) (hec : xe≤A) (hhnc : hn≤H) (hhec : he≤H) :
    ∀i,scalarCoefficients U k D E m c0 x0 xn xe hn he i≤
      scalarCoefficients U k Dcap Ecap Mcap cstar A A A H H i := by
  have hDc0:=hD.trans hDc
  have hEc0:=hE.trans hEc
  have hMc0:=hm.trans hmc
  have hA:=h0.trans h0c
  have hH:=hhn.trans hhnc
  have hc0:=hcstar.trans_le hcc
  have hrpow : D^(4/3:ℝ)≤Dcap^(4/3:ℝ) := Real.rpow_le_rpow hD hDc (by norm_num)
  have hcinv : c0^(-2/3:ℝ)≤cstar^(-2/3:ℝ) :=
    Real.rpow_le_rpow_of_nonpos hcstar hcc (by norm_num)
  have hk0:=hk 0
  have hk1:=hk 1
  have hk2:=hk 2
  have hk3:=hk 3
  intro i
  fin_cases i
  · change k 0*D^2*m^4*x0^2≤k 0*Dcap^2*Mcap^4*A^2
    gcongr
  · change k 1*D^3*m^2*xn^2*hn^U.nonexceptionalDegree≤
      k 1*Dcap^3*Mcap^2*A^2*H^U.nonexceptionalDegree
    gcongr
  · change k 2*E^2*m^8*D^(4/3:ℝ)*xe^2*he^(2*U.exceptionalDegree)*c0^(-2/3:ℝ)≤
      k 2*Ecap^2*Mcap^8*Dcap^(4/3:ℝ)*A^2*H^(2*U.exceptionalDegree)*cstar^(-2/3:ℝ)
    gcongr
  · change k 3*m^4*x0^2/c0^4≤k 3*Mcap^4*A^2/cstar^4
    apply (div_le_div_of_nonneg_right (show k 3*m^4*x0^2≤k 3*Mcap^4*A^2 by gcongr)
      (pow_nonneg hc0.le 4)).trans
    exact div_le_div_of_nonneg_left (by positivity) (pow_pos hcstar 4)
      (pow_le_pow_left₀ hcstar.le hcc 4)

private theorem scalarCoefficients_scaling (U : Controls) (k : Fin 4→ℝ)
    (D E m c0 A H : ℝ) (i : Fin 4) :
    scalarCoefficients U k D E m c0 A A A H H i=
      scalarCoefficients U k D E m c0 1 1 1 1 1 i*A^2*H^(coefficientDegree U i) := by
  fin_cases i <;> simp [scalarCoefficients,coefficientDegree] <;> ring

private theorem windowMass_upper (J : ℕ) (t H : ℝ) (hH : 1≤H) (ht : 1+|t|≤H) :
    windowMass J t^2≤((1+2*Real.pi)^2)^(2*J)*profileMoment J^2*H^(2*J) := by
  have hπ : 0≤2*Real.pi := by positivity
  have henv : heightEnvelope t≤(1+2*Real.pi)^2*H := by
    have hlin : 1+‖t‖+2*Real.pi≤(1+2*Real.pi)*H := by
      rw [Real.norm_eq_abs]
      nlinarith [mul_nonneg hπ (sub_nonneg.mpr hH)]
    have hh := mul_le_mul_of_nonneg_right hlin (by positivity : 0≤1+2*Real.pi)
    convert hh using 1 <;> (try unfold heightEnvelope) <;> ring
  calc
    _=heightEnvelope t^(2*J)*profileMoment J^2 := by
      unfold windowMass
      rw [mul_pow,←pow_mul,Nat.mul_comm J 2]
    _≤((1+2*Real.pi)^2*H)^(2*J)*profileMoment J^2 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (heightEnvelope_pos t).le henv _) (sq_nonneg _)
    _=_ := by rw [mul_pow];ring

private theorem height_one_le (t V t₁ t₂ : ℝ) (hV : 0≤V) : 1≤height t V t₁ t₂ := by
  unfold height
  linarith [abs_nonneg t,norm_nonneg t₁,norm_nonneg t₂]

/-- Constants and controls precede ALL sources and height parameters.
The explicit fixed cap on s.M is indispensable: Canonical is not used
to infer it. A later source constructor obtains it from slot_profile_bound.
The reference floor cstar is also selected before any scale Z.

This is a scalar/profile theorem; no moment/source/energy premise occurs. -/
theorem uniform_profile_envelope (U : Controls) (c : Constants) (Q : Id)
    (a b cstar Kslot : ℝ) (ha : 0<a) (hcstar : 0<cstar) (hKslot : 1≤Kslot) (N : ℕ) :
    ∃C : ℝ,0<C ∧
      ∀(ι : Type u) [Fintype ι],∀s : Source ι a b,Fintype.card ι≤N→s.d=(1,1)→
      (∀i,s.M i≤Kslot)→∀c0 t V : ℝ,cstar≤c0→0≤V→
      profileEnvelope U c s Q c0 t V≤
        C*(sourceControl (profileControl U) s.W₁*sourceControl (profileControl U) s.W₂)^2*
          height t V s.t₁ s.t₂^(heightDegree U) := by
  let k:=fixedCoefficients U c Q a b
  have hk : ∀i,0≤k i := fixedCoefficients_nonneg U c Q a b ha
  let caps:=scalarCoefficients U k (2^N) (1024^N) (Kslot^N) cstar 1 1 1 1 1
  have hcaps : ∀i,0≤caps i := scalarCoefficients_nonneg U k hk
    (2^N) (1024^N) (Kslot^N) cstar 1 1 1 1 1
    (by positivity) (by positivity) (pow_nonneg (zero_le_one.trans hKslot) _) hcstar
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let cw:=((1+2*Real.pi)^2)^(2*degree U)*profileMoment (degree U)^2
  have hcw : 0≤cw := by dsimp only [cw];positivity
  let C0:=4*cw*(∑i : Fin 4,caps i)
  have hC0 : 0≤C0 := mul_nonneg (mul_nonneg (by norm_num) hcw)
    (Finset.sum_nonneg (fun i _=>hcaps i))
  refine ⟨1+C0,by positivity,?_⟩
  intro ι instι s hcard hunit hM c0 t V hfloor hV
  let A:=sourceControl (profileControl U) s.W₁*sourceControl (profileControl U) s.W₂
  let H:=height t V s.t₁ s.t₂
  have hA : 0≤A := mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hH : 1≤H := height_one_le t V s.t₁ s.t₂ hV
  have hH0:=zero_le_one.trans hH
  have hs0 : ({(0,0)} : Finset (ℕ×ℕ))⊆profileControl U := by
    intro j hj
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hj)
  have hsn : U.nonexceptionalControl⊆profileControl U := by
    intro j hj
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hj)
  have hse : U.exceptionalControl⊆profileControl U := Finset.subset_union_right
  have hcontrol (S : Finset (ℕ×ℕ)) (hS : S⊆profileControl U) :
      sourceControl S s.W₁*sourceControl S s.W₂≤A :=
    mul_le_mul (control_mono hS s.W₁) (control_mono hS s.W₂)
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hm0 : 0≤∏i,s.M i := Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.hM i))
  have hm : (∏i,s.M i)≤Kslot^N := by
    have hh := Finset.prod_le_prod₀ (fun i (_ : i∈Finset.univ)=>zero_le_one.trans (s.hM i))
      (fun i (_ : i∈Finset.univ)=>hM i)
    have hc : (∏i,s.M i)≤Kslot^Fintype.card ι := by simpa only [Finset.prod_const,Finset.card_univ] using hh
    exact hc.trans (pow_le_pow_right₀ hKslot hcard)
  have hnative : sourceHeight t V (s.t₁/(2*Real.pi)) (s.t₂/(2*Real.pi))=H := by
    have hscale (r : ℝ) : 2*Real.pi*(r/(2*Real.pi))=r := by field_simp [Real.pi_ne_zero]
    simp only [sourceHeight,H,height,hscale,Real.norm_eq_abs]
  have hex : 1+‖s.t₁‖+‖s.t₂‖≤H := by
    dsimp only [H,height]
    linarith [abs_nonneg t]
  have hmono:=scalarCoefficients_mono U k hk
    (2^Fintype.card ι) (1024^Fintype.card ι) (∏i,s.M i) c0
    (supControl s.W₁*supControl s.W₂)
    (sourceControl U.nonexceptionalControl s.W₁*sourceControl U.nonexceptionalControl s.W₂)
    (sourceControl U.exceptionalControl s.W₁*sourceControl U.exceptionalControl s.W₂)
    (sourceHeight t V (s.t₁/(2*Real.pi)) (s.t₂/(2*Real.pi))) (1+‖s.t₁‖+‖s.t₂‖)
    (2^N) (1024^N) (Kslot^N) cstar A H
    (by positivity) (by positivity) hm0 hcstar
    (mul_nonneg (supControl_nonneg _) (supControl_nonneg _))
    (mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _))
    (mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _))
    (by rw [hnative];exact hH0) (by positivity)
    (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hcard)
    (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤1024) hcard) hm hfloor
    (hcontrol _ hs0) (hcontrol _ hsn) (hcontrol _ hse) hnative.le hex
  have hdeg (i : Fin 4) : coefficientDegree U i≤U.nonexceptionalDegree+2*U.exceptionalDegree := by
    fin_cases i <;> simp [coefficientDegree] <;> omega
  have hpoint (i : Fin 4) : unitCoefficients U c s Q c0 t V i≤
      caps i*A^2*H^(U.nonexceptionalDegree+2*U.exceptionalDegree) := by
    rw [actual_coefficients U c s Q c0 t V]
    apply (hmono i).trans
    rw [scalarCoefficients_scaling]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hH (hdeg i))
      (mul_nonneg (hcaps i) (sq_nonneg A))
  have hsum : (∑i : Fin 4,unitCoefficients U c s Q c0 t V i)≤
      (∑i : Fin 4,caps i)*A^2*H^(U.nonexceptionalDegree+2*U.exceptionalDegree) := by
    simpa only [Finset.sum_mul] using Finset.sum_le_sum (fun i _=>hpoint i)
  have hwindow : windowMass (degree U) t^2≤cw*H^(2*degree U) :=
    windowMass_upper (degree U) t H hH (by dsimp only [H,height];linarith [norm_nonneg s.t₁,norm_nonneg s.t₂])
  have hsum0 : 0≤4*∑i : Fin 4,unitCoefficients U c s Q c0 t V i :=
    mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _=>
      unit_coefficients_nonneg U c s ha hunit Q c0 t V (hcstar.trans_le hfloor) hV i))
  have hh:=mul_le_mul hwindow (mul_le_mul_of_nonneg_left hsum (by norm_num : (0:ℝ)≤4))
    hsum0 (mul_nonneg hcw (pow_nonneg hH0 _))
  calc
    _≤(cw*H^(2*degree U))*(4*((∑i : Fin 4,caps i)*A^2*
        H^(U.nonexceptionalDegree+2*U.exceptionalDegree))) := hh
    _=C0*A^2*H^(heightDegree U) := by
      have he : heightDegree U=2*degree U+(U.nonexceptionalDegree+2*U.exceptionalDegree) := by
        unfold heightDegree degree
        omega
      rw [he,pow_add]
      dsimp only [C0]
      ring
    _≤(1+C0)*A^2*H^(heightDegree U) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith : C0≤1+C0) (sq_nonneg A))
        (pow_nonneg hH0 _)

/-- The exact retained prefactor and the two first-remainder profile
costs have a common control, fixed before every live source, height and
selected family. The conductor, first scale and selected mass stay
explicit; this lemma does not absorb them into a constant. -/
theorem uniform_first_costs (U : Controls) (c : Constants) (Q : Id)
    (a b cstar Kslot Cpush Ckernel ε : ℝ) (ha : 0<a) (hcstar : 0<cstar)
    (hKslot : 1≤Kslot) (hCpush : 0≤Cpush) (hCkernel : 0≤Ckernel) (N : ℕ) :
    ∃Cret Crem : ℝ,0<Cret ∧ 0<Crem ∧
      ∀(ι : Type u) [Fintype ι],∀s : Source ι a b,Fintype.card ι≤N→s.d=(1,1)→
      (∀i,s.M i≤Kslot)→∀c0 t V : ℝ,cstar≤c0→0≤V→
      let A:=sourceControl (profileControl U) s.W₁*sourceControl (profileControl U) s.W₂
      let H:=height t V s.t₁ s.t₂
      (profileCap s)^2≤Crem*A^2*H^(heightDegree U) ∧
      ∀(η : Character)(K mass : ℝ),0≤K→0≤mass→
        retainedFactor U c s η Q c0 t V K mass Cpush Ckernel ε≤
          Cret*((η.modulus.absNorm:ℝ)*K)*mass*A^2*H^(heightDegree U) := by
  obtain ⟨Cenv,hCenv,henv⟩:=uniform_profile_envelope U c Q a b cstar Kslot ha hcstar hKslot N
  let k:=(4/a^2)*fixedPresentationCost*Ckernel*Cpush*(16:ℝ)^ε*rayMass
  have hk : 0≤k := by
    have hf:=fixedPresentationCost_pos.le
    have hr:=rayMass_nonneg
    dsimp only [k]
    positivity
  let Crem:=4*(Kslot^N)^2
  have hCrem : 0<Crem := by
    have hKslot0:=zero_lt_one.trans_le hKslot
    dsimp only [Crem]
    positivity
  refine ⟨1+k*Cenv,Crem,by positivity,hCrem,?_⟩
  intro ι instι s hcard hunit hM c0 t V hfloor hV A H
  have hA : 0≤A := mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hH : 1≤H := height_one_le t V s.t₁ s.t₂ hV
  have hHpow : 1≤H^(heightDegree U) := one_le_pow₀ hH
  have hm0 : 0≤∏i,s.M i := Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.hM i))
  have hm : (∏i,s.M i)≤Kslot^N := by
    have hh := Finset.prod_le_prod₀ (fun i (_ : i∈Finset.univ)=>zero_le_one.trans (s.hM i))
      (fun i (_ : i∈Finset.univ)=>hM i)
    have hc : (∏i,s.M i)≤Kslot^Fintype.card ι := by
      simpa only [Finset.prod_const,Finset.card_univ] using hh
    exact hc.trans (pow_le_pow_right₀ hKslot hcard)
  have hs0 : ({(0,0)} : Finset (ℕ×ℕ))⊆profileControl U := by
    intro j hj
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hj)
  have hsup : supControl s.W₁*supControl s.W₂≤A :=
    mul_le_mul (control_mono hs0 s.W₁) (control_mono hs0 s.W₂)
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  constructor
  · have hp : profileCap s≤2*A*Kslot^N := by
      calc
        _=2*(supControl s.W₁*supControl s.W₂)*(∏i,s.M i) := by unfold profileCap;ring
        _≤2*A*Kslot^N := mul_le_mul
          (mul_le_mul_of_nonneg_left hsup (by norm_num)) hm hm0 (by positivity)
    calc
      _≤(2*A*Kslot^N)^2 := pow_le_pow_left₀ (profileCap_nonneg s) hp 2
      _=Crem*A^2 := by dsimp only [Crem];ring
      _≤Crem*A^2*H^(heightDegree U) := le_mul_of_one_le_right (by positivity) hHpow
  · intro η K mass hK hmass
    have henv':=henv ι s hcard hunit hM c0 t V hfloor hV
    have hnorm : 0≤(η.modulus.absNorm:ℝ) := Nat.cast_nonneg _
    calc
      _=k*((η.modulus.absNorm:ℝ)*K)*mass*profileEnvelope U c s Q c0 t V := by
        unfold retainedFactor
        dsimp only [k]
        ring
      _≤k*((η.modulus.absNorm:ℝ)*K)*mass*(Cenv*A^2*H^(heightDegree U)) :=
        mul_le_mul_of_nonneg_left henv' (by positivity)
      _=(k*Cenv)*((η.modulus.absNorm:ℝ)*K)*mass*A^2*H^(heightDegree U) := by ring
      _≤(1+k*Cenv)*((η.modulus.absNorm:ℝ)*K)*mass*A^2*H^(heightDegree U) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (by linarith : k*Cenv≤1+k*Cenv) (by positivity)) hmass)
            (sq_nonneg A)) (pow_nonneg (zero_le_one.trans hH) _)

end
end Candidate.SilPrior.FourthPower.MixedFirstProfileEnvelope
