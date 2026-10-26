import Candidate.Cycle63.Physical.InitialMass.SecondCoarseShell
import Candidate.Cycle63.Physical.InitialMass.SecondSourceControls
import Candidate.Cycle63.Physical.InitialMass.SecondCoarseCount

/- Original module: Candidate.Cycle63.Physical.InitialMass.SecondCoarseControl. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentCommonHeightEnvelope
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildSourceCaps
local notation "O" => HeckeFamily.O

/-- Fixed coefficient cost for the coarse tail. Its large size is harmless:
it is chosen before all scales, rows, allocations and heights. -/
def coarseFixedControl (N : ℕ)(Cs b bs : ℝ) : ℝ :=
  (2*(bs*bs))*(Cs^N)^2*((128*bs)^2*(128*b*Cs)^N)^2*2

lemma coarse_fixed_control_pos (N : ℕ)(Cs b bs : ℝ)
    (hCs : 1≤Cs)(hb : 1≤b)(hbs : 1≤bs) : 0<coarseFixedControl N Cs b bs := by
  unfold coarseFixedControl
  positivity

/-- Actual scale and coefficient gates imply a uniform coarse polynomial
bound; this does not assume an analytic moment estimate. -/
theorem actual_coarse_control_fixed {ι : Type*}[Fintype ι][DecidableEq ι]
    (N : ℕ)(Cs b bs cap Z B₁ B₂ : ℝ)(hCs : 1≤Cs)(hb : 1≤b)(hbs : 1≤bs)
    (hcap : 0≤cap)(hZ : 1≤Z)(hB₁ : 0≤B₁)(hB₂ : 0≤B₂)
    (s : Data ι)(hcard : Fintype.card ι≤N)(hM : ∀j,s.M j≤Cs)
    (hhi : ∀j,s.hi j≤b)(hb₁ : s.b₁≤bs)(hb₂ : s.b₂≤bs)
    (hscales : ∀second j,Cycle63.Physical.sourcePlainScales s.toSource second j≤Z^cap)
    (hP : ∀j,s.P j≤Z^cap) :
    coarseAllocationControl s B₁ B₂≤
      coarseFixedControl N Cs b bs*(B₁*B₂)^2*Z^(((N:ℝ)+2)*cap) := by
  have hz : 0<Z := lt_of_lt_of_le (by norm_num) hZ
  have hzcap : 1≤Z^cap := Real.one_le_rpow hZ hcap
  have hm0 : ∀j,0≤s.M j := fun j=>zero_le_one.trans (s.M_ge_one j)
  have hpM : (∏j,s.M j)≤Cs^N := by
    calc
      _≤∏_j : ι,Cs := Finset.prod_le_prod₀ (fun j _=>hm0 j) (fun j _=>hM j)
      _=Cs^(Fintype.card ι) := by simp
      _≤Cs^N := pow_le_pow_right₀ hCs hcard
  have hfac0 : ∀j,0≤128*max 1 (s.hi j)*s.M j := fun j=>mul_nonneg (by positivity) (hm0 j)
  have hpF : (∏j,128*max 1 (s.hi j)*s.M j)≤(128*b*Cs)^N := by
    calc
      _≤∏_j : ι,128*b*Cs := Finset.prod_le_prod₀ (fun j _=>hfac0 j) (fun j _=>by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (max_le hb (hhi j)) (by norm_num)
        · exact hM j
        · exact hm0 j
        · positivity)
      _=(128*b*Cs)^(Fintype.card ι) := by simp
      _≤_ := pow_le_pow_right₀ (by nlinarith [mul_le_mul hb hCs (by norm_num : (0:ℝ)≤1) (by linarith : 0≤b)]) hcard
  have hrow : coarseRowControl s B₁ B₂≤((128*bs)^2*(128*b*Cs)^N)*(B₁*B₂) := by
    unfold coarseRowControl
    calc
      _≤(128*bs*B₁)*(128*bs*B₂)*(128*b*Cs)^N := by
        apply mul_le_mul _ hpF (Finset.prod_nonneg (fun j _=>hfac0 j)) (by positivity)
        apply mul_le_mul
        · gcongr; exact max_le hbs hb₁
        · gcongr; exact max_le hbs hb₂
        · positivity
        · positivity
      _=_ := by ring
  have hsize (second : Bool) : coarseRowSize s second≤Z^(((N:ℝ)+2)*cap) := by
    have hp : (∏j,max 1 (s.P j))≤(Z^cap)^N := by
      calc
        _≤∏_j : ι,Z^cap := Finset.prod_le_prod₀ (fun _ _=>by positivity)
          (fun j _=>max_le hzcap (hP j))
        _=(Z^cap)^(Fintype.card ι) := by simp
        _≤_ := pow_le_pow_right₀ hzcap hcard
    unfold coarseRowSize
    calc
      _≤Z^cap*Z^cap*(Z^cap)^N := by
        apply mul_le_mul _ hp (Finset.prod_nonneg (fun _ _=>by positivity)) (by positivity)
        exact mul_le_mul (max_le hzcap (hscales second 0)) (max_le hzcap (hscales second 1))
          (by positivity) (by positivity)
      _=Z^(((N:ℝ)+2)*cap) := by
        rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_add hz,←Real.rpow_add hz]
        congr 1
        ring
  have hMprod0 : 0≤∏j,s.M j := Finset.prod_nonneg (fun j _=>hm0 j)
  have hrow0 : 0≤coarseRowControl s B₁ B₂ := by
    unfold coarseRowControl
    exact mul_nonneg (by positivity) (Finset.prod_nonneg (fun j _=>hfac0 j))
  unfold coarseAllocationControl
  calc
    _≤(2*(bs*bs))*(Cs^N)^2*(((128*bs)^2*(128*b*Cs)^N)*(B₁*B₂))^2*
        (2*Z^(((N:ℝ)+2)*cap)) := by
      apply mul_le_mul _ (by linarith [hsize false,hsize true])
        (add_nonneg (coarse_row_size_nonneg s false) (coarse_row_size_nonneg s true)) (by positivity)
      apply mul_le_mul _ (pow_le_pow_left₀ hrow0 hrow 2) (sq_nonneg _) (by positivity)
      apply mul_le_mul _ (pow_le_pow_left₀ hMprod0 hpM 2) (sq_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (max_le hbs hb₁) (max_le hbs hb₂) (by positivity) (by positivity)) (by norm_num)
    _=_ := by unfold coarseFixedControl; ring

/-- The two literal common allocations inherit the coarse bound from the
original input, uniformly in both newly introduced characters and heights. -/
theorem actual_two_common_coarse_control {ι : Type*}[Fintype ι][DecidableEq ι]
    (N : ℕ)(Cs b bs cap Z B₁ B₂ : ℝ)(hCs : 1≤Cs)(hb : 1≤b)(hbs : 1≤bs)
    (hcap : 0≤cap)(hZ : 1≤Z)(hB₁ : 0≤B₁)(hB₂ : 0≤B₂)
    (s : Input ι)(hcard : Fintype.card ι≤N)(hM : ∀j,s.M j≤Cs)
    (hupper : s.upper≤b)(hb₁ : s.b₁≤bs)(hb₂ : s.b₂≤bs)
    (hscales : ∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j≤Z^cap)
    (hP : ∀j,s.P j≤Z^cap)
    (C₁ R₁ : Ideal O)(A₁ : actualAllocations s.pools C₁)(χ₁ : Character)(t₁ : ℝ)
    (C₂ R₂ : Ideal O)(A₂ : actualAllocations (child s C₁ R₁ A₁ χ₁ t₁).pools C₂)
    (χ₂ : Character)(t₂ : ℝ) :
    coarseAllocationControl
      (commonData (withHeight (child s C₁ R₁ A₁ χ₁ t₁) χ₂ t₂) C₂ R₂ A₂) B₁ B₂≤
      coarseFixedControl N Cs b bs*(B₁*B₂)^2*Z^(((N:ℝ)+2)*cap) := by
  apply actual_coarse_control_fixed N Cs b bs cap Z B₁ B₂ hCs hb hbs hcap hZ hB₁ hB₂
  · exact (live_card_le A₂.val).trans ((live_card_le A₁.val).trans hcard)
  · intro j; exact hM j.val.val
  · intro j; exact (s.upper_ge j.val.val).trans hupper
  · exact hb₁
  · exact hb₂
  · intro second j
    have hn : (1:ℝ)≤(A₂.val (Sum.inr j)).absNorm := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
        (alloc_ne (child s C₁ R₁ A₁ χ₁ t₁) C₂ A₂ (Sum.inr j)))
    have hh := actual_child_plain_scale_le s C₁ R₁ A₁ χ₁ t₁ second j
    apply le_trans _ (hh.trans (hscales second j))
    cases second <;> fin_cases j
    · exact div_le_self (child s C₁ R₁ A₁ χ₁ t₁).X₁_pos.le hn
    · exact div_le_self (child s C₁ R₁ A₁ χ₁ t₁).X₂_pos.le hn
    · exact div_le_self (child s C₁ R₁ A₁ χ₁ t₁).Y₁_pos.le hn
    · exact div_le_self (child s C₁ R₁ A₁ χ₁ t₁).Y₂_pos.le hn
  · intro j; exact hP j.val.val

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_coarse_control_fixed

#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_two_common_coarse_control
end

/- Original module: Candidate.Cycle63.Physical.InitialMass.SecondCoarseJoint. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open LocalMoment ProbePhysical IdealMobiusDivisorSum CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open Cycle63Moment
local notation "O" => HeckeFamily.O

/-- Full residual-projector coarse energy for one injective joint selection.
The finite menu of slot types is fixed before the moving labels. -/
theorem actual_selected_coarse_shell {Index : Type}[Fintype Index]
    (Slots : Index→Type)[∀i,Fintype (Slots i)][∀i,DecidableEq (Slots i)]
    (N : ℕ)(hN : ∀i,Fintype.card (Slots i)≤N)
    (B loss ε : ℝ)(hB : 0≤B)(hloss : 0<loss)(hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{κ : Type}(left : Bool)(u₀ : O)(unit : FirstSourceLabel→O)
      (Z m e allowance control T : ℝ),2≤Z → 0≤control → 1≤T →
      ∀(key : κ→NonzeroJointSourceLabel left u₀ unit),Function.Injective key →
      ∀labels : Finset κ,
      (∀label∈labels,rawFrequencyNorm (nonzeroJointSourceRow (key label))≤Z^B) →
      (∀label∈labels,Supported (key label).val.1.1.1 ∧ (key label).val.1.1.2≠0 ∧
        Supported (key label).val.2.1.1 ∧ (key label).val.2.1.2≠0) →
      (∀label∈labels,primeSupport (key label).val.1.1.1=primeSupport (key label).val.1.1.2 ∧
        primeSupport (key label).val.2.1.1=primeSupport (key label).val.2.1.2) →
      (∀label∈labels,((Ideal.span {jointSourceRow left u₀ unit (key label).val}*
        firstSourceMissing left (key label).val.1).absNorm:ℝ)≤Z^B) →
      (∀label∈labels,((key label).val.1.1.1.absNorm:ℝ)≤Z^B ∧
        ((key label).val.1.1.2.absNorm:ℝ)≤Z^B ∧
        ((key label).val.2.1.1.absNorm:ℝ)≤Z^B ∧ ((key label).val.2.1.2.absNorm:ℝ)≤Z^B) →
      (∀label∈labels,((firstSourceMissing left (key label).val.1).absNorm:ℝ)≤Z^m) →
      ∀(index : κ→Index)(s : ∀l,Data (Slots (index l)))(z : κ→O)
        (Ds : κ→Finset (Ideal O))(B₁ B₂ : κ→ℝ),
      (∀l∈labels,0≤B₁ l ∧ 0≤B₂ l) →
      (∀l∈labels,∀x,‖(s l).W₁ x‖≤B₁ l ∧ ‖(s l).W₂ x‖≤B₂ l) →
      (∀l∈labels,coarseAllocationControl (s l) (B₁ l) (B₂ l)≤control*Z^e) →
      (∀l∈labels,(s l).toSource.allowance Z≤allowance) →
      (∀l∈labels,∀D∈Ds l,Squarefree D ∧ T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
      (∑l∈labels,∑D∈Ds l,∑a∈(s l).toSource.active D,
        retainedAllocationCost (s l) D a (z l))≤
      C*control*(2*T)^(2*ε)*Z^(m+B+loss+e+allowance) := by
  choose K hK hbound using fun i=>actual_second_coarse_shell N (hN i) ε hε
  let Kall := 1+∑i,K i
  have hKall : 0<Kall := by
    dsimp [Kall]
    have hh : 0≤∑i,K i := Finset.sum_nonneg (fun i _=>(hK i).le)
    linarith
  have hKle (i : Index) : K i≤Kall := by
    have hh := Finset.single_le_sum (fun j (_ : j∈Finset.univ)=>(hK j).le) (Finset.mem_univ i)
    dsimp [Kall]
    linarith
  obtain ⟨C,hC,hcount⟩ := actual_joint_coarse_row_count B loss hB hloss
  refine ⟨C*Kall,mul_pos hC hKall,?_⟩
  intro κ left u₀ unit Z m e allowance control T hZ hcontrol hT key hinj labels
    hrow hsupported heq hsupport hnorm hmissing index s z Ds B₁ B₂ hBs hWs hcost hallow hDs
  have hZ0 : 0<Z := by linarith
  have hc := hcount left u₀ unit Z hZ m (labels.image key)
    (by intro l hl; obtain ⟨r,hr,rfl⟩:=Finset.mem_image.mp hl; exact hrow r hr)
    (by intro l hl; obtain ⟨r,hr,rfl⟩:=Finset.mem_image.mp hl; exact hsupported r hr)
    (by intro l hl; obtain ⟨r,hr,rfl⟩:=Finset.mem_image.mp hl; exact heq r hr)
    (by intro l hl; obtain ⟨r,hr,rfl⟩:=Finset.mem_image.mp hl; exact hsupport r hr)
    (by intro l hl; obtain ⟨r,hr,rfl⟩:=Finset.mem_image.mp hl; exact hnorm r hr)
    (by intro l hl; obtain ⟨r,hr,rfl⟩:=Finset.mem_image.mp hl; exact hmissing r hr)
  rw [Finset.card_image_of_injective _ hinj] at hc
  let W := Kall*control*(2*T)^(2*ε)*Z^(e+allowance)
  have hW : 0≤W := by dsimp [W]; positivity
  have hpoint (l : κ)(hl : l∈labels) :
      (∑D∈Ds l,∑a∈(s l).toSource.active D,retainedAllocationCost (s l) D a (z l))≤W := by
    have hh := hbound (index l) (s l) (Ds l) (fun D hD=>(hDs l hl D hD).1)
      T Z hT (by linarith) (fun D hD=>(hDs l hl D hD).2.1)
      (fun D hD=>(hDs l hl D hD).2.2) (fun _ _=>z l)
      (B₁ l) (B₂ l) (hBs l hl).1 (hBs l hl).2
      (fun x=>(hWs l hl x).1) (fun x=>(hWs l hl x).2)
    apply hh.trans
    calc
      _≤(control*Z^e)*Kall*(2*T)^(2*ε)*Z^allowance := by
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul (hcost l hl) (hKle (index l)) (hK _).le (by positivity)
        · exact Real.rpow_le_rpow_of_exponent_le (by linarith) (hallow l hl)
        · positivity
        · positivity
      _=W := by
        dsimp [W]
        rw [Real.rpow_add hZ0]
        ring
  calc
    _≤∑_l∈labels,W := Finset.sum_le_sum hpoint
    _=(labels.card:ℝ)*W := by simp
    _≤(C*Z^(m+B+loss))*W := mul_le_mul_of_nonneg_right hc hW
    _=(C*Kall)*control*(2*T)^(2*ε)*Z^(m+B+loss+e+allowance) := by
      dsimp [W]
      rw [show m+B+loss+e+allowance=(m+B+loss)+(e+allowance) by ring,Real.rpow_add hZ0 (m+B+loss) (e+allowance)]
      ring

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_selected_coarse_shell
end

/- Original module: Candidate.Cycle63.Physical.InitialMass.SecondCoarseChild. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open LocalMoment ProbePhysical IdealMobiusDivisorSum CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAmplificationChildInput
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationChildSourceCaps
open Cycle63Moment
local notation "O" => HeckeFamily.O

/-- An all-height joint shell estimate from the original source's fixed
support, coefficient and scale bounds. The two common allocations and their
new heights are quantified after the constant and asymptotic threshold. -/
theorem actual_child_selected_coarse_shell {α : Type}[Fintype α][DecidableEq α]
    (N : ℕ)(hα : Fintype.card α≤N)
    (B loss ε pad Cs b bs window cap : ℝ)
    (hB : 0≤B)(hloss : 0<loss)(hε : 0<ε)(hpad : 0<pad)
    (hCs : 1≤Cs)(hb : 1≤b)(hbs : 1≤bs)(hwindow : 0≤window)(hcap : 0≤cap) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,2≤Z ∧
      ∀{κ : Type}(left : Bool)(u₀ : O)(unit : FirstSourceLabel→O)
        (m control T : ℝ),0≤control → 1≤T →
      ∀(key : κ→NonzeroJointSourceLabel left u₀ unit),Function.Injective key →
      ∀labels : Finset κ,
      (∀label∈labels,rawFrequencyNorm (nonzeroJointSourceRow (key label))≤Z^B) →
      (∀label∈labels,Supported (key label).val.1.1.1 ∧ (key label).val.1.1.2≠0 ∧
        Supported (key label).val.2.1.1 ∧ (key label).val.2.1.2≠0) →
      (∀label∈labels,primeSupport (key label).val.1.1.1=primeSupport (key label).val.1.1.2 ∧
        primeSupport (key label).val.2.1.1=primeSupport (key label).val.2.1.2) →
      (∀label∈labels,((Ideal.span {jointSourceRow left u₀ unit (key label).val}*
        firstSourceMissing left (key label).val.1).absNorm:ℝ)≤Z^B) →
      (∀label∈labels,((key label).val.1.1.1.absNorm:ℝ)≤Z^B ∧
        ((key label).val.1.1.2.absNorm:ℝ)≤Z^B ∧
        ((key label).val.2.1.1.absNorm:ℝ)≤Z^B ∧ ((key label).val.2.1.2.absNorm:ℝ)≤Z^B) →
      (∀label∈labels,((firstSourceMissing left (key label).val.1).absNorm:ℝ)≤Z^m) →
      ∀s : Input α,(∀j,s.M j≤Cs) → s.upper≤b → s.b₁≤bs → s.b₂≤bs →
      (∀j,CenteredMomentSlotRatios.logWindow (s.lo j) (s.hi j)≤window) →
      (∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j≤Z^cap) →
      (∀j,s.P j≤Z^cap) →
      ∀(C₁ R₁ : κ→Ideal O)(A₁ : ∀l,actualAllocations s.pools (C₁ l))
        (χ₁ : κ→Character)(t₁ : κ→ℝ),
      let first := fun l=>child s (C₁ l) (R₁ l) (A₁ l) (χ₁ l) (t₁ l)
      ∀(C₂ R₂ : κ→Ideal O)(A₂ : ∀l,actualAllocations (first l).pools (C₂ l))
        (χ₂ : κ→Character)(t₂ : κ→ℝ)(z : κ→O)
        (Ds : κ→Finset (Ideal O))(B₁ B₂ : ℝ),
      0≤B₁ → 0≤B₂ → (∀x,‖s.W₁ x‖≤B₁) → (∀x,‖s.W₂ x‖≤B₂) →
      (B₁*B₂)^2≤control →
      (∀l∈labels,∀D∈Ds l,Squarefree D ∧ T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
      let src := fun l=>commonData (withHeight (first l) (χ₂ l) (t₂ l)) (C₂ l) (R₂ l) (A₂ l)
      (∑l∈labels,∑D∈Ds l,∑a∈(src l).toSource.active D,
        retainedAllocationCost (src l) D a (z l))≤
      C*control*(2*T)^(2*ε)*Z^(m+B+loss+((N:ℝ)+2)*cap+pad) := by
  let Index := (S : Finset α) × Finset S
  let Slots := fun i : Index=>↥i.2
  have hN (i : Index) : Fintype.card (Slots i)≤N := by
    exact (Fintype.card_subtype_le _).trans ((Fintype.card_subtype_le _).trans hα)
  obtain ⟨C,hC,hshell⟩ := actual_selected_coarse_shell Slots N hN B loss ε hB hloss hε
  have hfixed := coarse_fixed_control_pos N Cs b bs hCs hb hbs
  refine ⟨C*coarseFixedControl N Cs b bs,mul_pos hC hfixed,?_⟩
  filter_upwards [eventual_two_common_allowance N window bs pad hwindow hbs hpad,
    eventually_ge_atTop (2:ℝ)] with Z hallow hZ
  refine ⟨hZ,?_⟩
  intro κ left u₀ unit m control T hcontrol hT key hinj labels
    hrow hsupported heq hsupport hnorm hmissing s hM hupper hb₁ hb₂ hwin hscales hP
    C₁ R₁ A₁ χ₁ t₁ first C₂ R₂ A₂ χ₂ t₂ z Ds B₁ B₂ hB₁ hB₂ hW₁ hW₂ hcontrolB hDs src
  let index := fun l=> (⟨CenteredMomentCommonProfile.liveIndices (A₁ l).val,
    CenteredMomentCommonProfile.liveIndices (A₂ l).val⟩ : Index)
  have hh := hshell left u₀ unit Z m (((N:ℝ)+2)*cap) pad
    (coarseFixedControl N Cs b bs*control) T hZ (mul_nonneg hfixed.le hcontrol) hT key hinj labels
    hrow hsupported heq hsupport hnorm hmissing index src z Ds (fun _=>B₁) (fun _=>B₂)
    (fun _ _=>⟨hB₁,hB₂⟩) (fun _ _ x=>⟨hW₁ x,hW₂ x⟩) ?_ ?_ hDs
  · convert hh using 1 <;> ring
  · intro l hl
    exact (actual_two_common_coarse_control N Cs b bs cap Z B₁ B₂ hCs hb hbs hcap
      (by linarith) hB₁ hB₂ s hα hM hupper hb₁ hb₂ hscales hP
      (C₁ l) (R₁ l) (A₁ l) (χ₁ l) (t₁ l) (C₂ l) (R₂ l) (A₂ l) (χ₂ l) (t₂ l)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcontrolB hfixed.le) (by positivity))
  · intro l hl
    have hh := hallow.2 s hα hwin hb₁ hb₂ (C₁ l) (R₁ l) (A₁ l) (χ₁ l) (t₁ l)
      (C₂ l) (R₂ l) (A₂ l) (χ₂ l) (t₂ l)
    have hp : 0≤Cycle63.Physical.plainClipAllowance Z ![(src l).b₁,(src l).b₂] := by
      unfold Cycle63.Physical.plainClipAllowance
      exact Finset.sum_nonneg (fun j _=>Real.logb_nonneg hallow.1 (le_max_left _ _))
    linarith

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_child_selected_coarse_shell
end
