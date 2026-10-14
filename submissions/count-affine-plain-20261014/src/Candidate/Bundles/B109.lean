/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B091
import Candidate.Bundles.B106
import Candidate.Bundles.B108
import OAI.NumberTheory.DirichletL.Moments.AmplificationSlotGap

/- BEGIN ORIGINAL Cycle61.Physical.HighResidualAllocation; sha256 93574321245b20bfe0d786a14235db967b7f3ea807a6378b04f9ac815d5667ed -/
section
                                           

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61HighResidual
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentEligibleEnergy
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentActiveDivisorShell Cycle61Moment
open Cycle61.Physical
local notation "O" => HeckeFamily.O
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Undo only the actual post-clipping normalizer, keeping the row itself. -/
def normalizedPositiveNorm (s : Source ι) (second : Bool) (Z : ℝ) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) (z : O) : ℝ :=
  ‖sourcePositiveRow s second D a z‖/Z^(sourcePostClip s second Z D a/2)

lemma normalizedPositiveNorm_nonneg (s : Source ι) (second : Bool) (Z : ℝ) (hZ : 0≤ Z) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) (z : O) :
    0 ≤ normalizedPositiveNorm s second Z D a z := by
  unfold normalizedPositiveNorm
  exact div_nonneg (norm_nonneg _) (Real.rpow_nonneg hZ _)

/-- The negative clipping contribution remains explicit in the squared norm. -/
lemma normalizedPositiveNorm_sq (s : Source ι) (second : Bool)
    (Z : ℝ) (hZ : 0< Z) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) (z : O) :
    (normalizedPositiveNorm s second Z D a z)^2 =
      ‖sourcePositiveRow s second D a z‖^2/Z^(sourcePostClip s second Z D a) := by
  unfold normalizedPositiveNorm
  rw [div_pow,←Real.rpow_natCast (Z^(sourcePostClip s second Z D a/2)) 2,←Real.rpow_mul hZ.le]
  congr 2
  ring

lemma normalizedPositiveNorm_sq_bound (s : Source ι) (second : Bool)
    (Z : ℝ) (hZ : 0< Z) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) (z : O) (C e : ℝ)
    (hrow : ‖sourcePositiveRow s second D a z‖^2≤ C*Z^e) :
    (normalizedPositiveNorm s second Z D a z)^2 ≤
      C*Z^(e-sourcePostClip s second Z D a) := by
  rw [normalizedPositiveNorm_sq s second Z hZ D a z,Real.rpow_sub hZ,←mul_div_assoc]
  exact div_le_div_of_nonneg_right hrow (Real.rpow_pos_of_pos hZ _).le

lemma clipped_pair_identity (s : Source ι) (v : Source κ) (secondS secondV : Bool)
    (Z : ℝ) (hZ : 1< Z) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (b : Allocation D (Finset.univ : Finset (κ ⊕ Fin 2))) (zs zv : O) :
    nonzeroClippedPairWeight s v secondS secondV Z D a b zs zv*
      normalizedPositiveNorm s secondS Z D a zs*normalizedPositiveNorm v secondV Z D b zv =
    (1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P))*
      ‖sourcePositiveRow s secondS D a zs‖*‖sourcePositiveRow v secondV D b zv‖ := by
  have hz := zero_lt_one.trans hZ
  unfold nonzeroClippedPairWeight normalizedPositiveNorm
  split_ifs with hn
  · unfold sourceClippedPairWeight
    rw [show (sourcePostClip s secondS Z D a+sourcePostClip v secondV Z D b)/2 =
      sourcePostClip s secondS Z D a/2+sourcePostClip v secondV Z D b/2 by ring,
      Real.rpow_add hz]
    field_simp
  · push Not at hn
    by_cases hs : sourcePositiveRow s secondS D a zs=0
    · simp [hs]
    · simp [hn hs]

/-- The frozen coefficients are separate from the divisor denominator. -/
def frozenControl (s : Data ι) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) : ℝ :=
  Real.sqrt (2*(max 1 s.b₁*max 1 s.b₂))*(∏ i∈frozenIndices D a,s.M i)

lemma frozenControl_nonneg (s : Data ι) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) : 0≤ frozenControl s D a := by
  unfold frozenControl
  exact mul_nonneg (Real.sqrt_nonneg _) (Finset.prod_nonneg (fun i _ => zero_le_one.trans (s.M_ge_one i)))

lemma retained_sqrt_le (s : Data ι) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) (z : O) :
    Real.sqrt (retainedAllocationCost s D a z) ≤
      frozenControl s D a/Real.sqrt (formalReductionFactor D a s.P)*
        (‖sourcePositiveRow s.toSource false D a z‖+‖sourcePositiveRow s.toSource true D a z‖) := by
  have hf : 0≤∏ i∈frozenIndices D a,s.M i :=
    Finset.prod_nonneg (fun i _ => zero_le_one.trans (s.M_ge_one i))
  have hb : 0≤2*(max 1 s.b₁*max 1 s.b₂) := by positivity
  unfold retainedAllocationCost
  rw [Real.sqrt_mul (div_nonneg (mul_nonneg hb (sq_nonneg _)) (s.reduction_pos D a).le),
    Real.sqrt_div (mul_nonneg hb (sq_nonneg _)),Real.sqrt_mul hb,Real.sqrt_sq hf]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith [norm_nonneg (sourcePositiveRow s.toSource false D a z),
      norm_nonneg (sourcePositiveRow s.toSource true D a z)]

/-- Four actual positive rectangle pairs, with both reductions and clip
normalizers retained. No first-label or residual-divisor count is taken. -/
theorem retained_pair_four_rectangles (s : Data ι) (v : Data κ)
    (Z : ℝ) (hZ : 1< Z) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (b : Allocation D (Finset.univ : Finset (κ ⊕ Fin 2))) (zs zv : O) :
    Real.sqrt (retainedAllocationCost s D a zs)*Real.sqrt (retainedAllocationCost v D b zv) ≤
      (frozenControl s D a*frozenControl v D b)*
        ∑ i : Bool, ∑ j : Bool,
          nonzeroClippedPairWeight s.toSource v.toSource i j Z D a b zs zv*
            normalizedPositiveNorm s.toSource i Z D a zs*
              normalizedPositiveNorm v.toSource j Z D b zv := by
  have hfs := frozenControl_nonneg s D a
  have hh := mul_le_mul (retained_sqrt_le s D a zs) (retained_sqrt_le v D b zv)
    (Real.sqrt_nonneg _) (by positivity : 0≤ frozenControl s D a/
      Real.sqrt (formalReductionFactor D a s.P)*
      (‖sourcePositiveRow s.toSource false D a zs‖+‖sourcePositiveRow s.toSource true D a zs‖))
  apply hh.trans_eq
  simp_rw [clipped_pair_identity _ _ _ _ Z hZ]
  rw [Real.sqrt_mul (s.reduction_pos D a).le]
  simp only [Fintype.sum_bool]
  ring

def wholeControl (s : Data ι) : ℝ :=
  Real.sqrt (2*(max 1 s.b₁*max 1 s.b₂))*(∏ i,s.M i)

omit [DecidableEq ι] in
lemma wholeControl_nonneg (s : Data ι) : 0≤ wholeControl s := by
  unfold wholeControl
  exact mul_nonneg (Real.sqrt_nonneg _) (Finset.prod_nonneg (fun i _ => zero_le_one.trans (s.M_ge_one i)))

omit [DecidableEq ι] in
/-- Fixed original slot and support bounds absorb every frozen allocation. -/
lemma wholeControl_fixed (N : ℕ) (Cs bs : ℝ) (hCs : 1≤ Cs) (hbs : 1≤ bs)
    (s : Data ι) (hcard : Fintype.card ι≤ N) (hM : ∀i,s.M i≤ Cs)
    (hb₁ : s.b₁≤ bs) (hb₂ : s.b₂≤ bs) : wholeControl s≤2*bs*Cs^N := by
  have hp : (∏i,s.M i)≤ Cs^N := by
    calc
      _ ≤ ∏_i : ι,Cs := Finset.prod_le_prod₀
        (fun i _=>zero_le_one.trans (s.M_ge_one i)) (fun i _=>hM i)
      _ = Cs^(Fintype.card ι) := by simp
      _ ≤ _ := pow_le_pow_right₀ hCs hcard
  have hr : Real.sqrt (2*(max 1 s.b₁*max 1 s.b₂))≤2*bs := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    have hh := mul_le_mul (max_le hbs hb₁) (max_le hbs hb₂)
      (zero_le_one.trans (le_max_left _ _)) (zero_le_one.trans hbs)
    nlinarith [sq_nonneg bs]
  exact mul_le_mul hr hp
    (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i))) (by positivity)

lemma frozenControl_le (s : Data ι) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) : frozenControl s D a≤ wholeControl s := by
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
    (fun i _=>zero_le_one.trans (s.M_ge_one i)) (fun i _ _=>s.M_ge_one i)

lemma pair_weight_nonneg (s : Source ι) (v : Source κ) (i j : Bool)
    (Z : ℝ) (hZ : 0≤ Z) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (b : Allocation D (Finset.univ : Finset (κ ⊕ Fin 2))) (zs zv : O) :
    0≤ nonzeroClippedPairWeight s v i j Z D a b zs zv := by
  unfold nonzeroClippedPairWeight sourceClippedPairWeight
  split_ifs
  · exact mul_nonneg (by positivity) (Real.rpow_nonneg hZ _)
  · exact le_rfl

/-- Residual dyad contraction for the actual allocation costs. Positive-row
bounds enter only after undoing the actual clipping normalizers; no claim that
the projector divides either encoded frequency is needed. -/
def RetainedPairShellBound (ι κ : Type*) [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (C ε : ℝ) : Prop :=
  ∀ (s : Data ι) (v : Data κ)
      (Ds : Finset (Ideal O)), (∀ D∈Ds,Squarefree D) →
    ∀ (zs zv : ∀ D : Ideal O,
      Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)) →
      Allocation D (Finset.univ : Finset (κ ⊕ Fin 2)) → O)
      (T Z : ℝ), 1≤ T → 1< Z →
      (∀ D∈Ds,T≤(D.absNorm:ℝ)) → (∀ D∈Ds,(D.absNorm:ℝ)<2*T) →
    ∀ E : Bool→ Bool→ℝ, (∀ i j,0≤ E i j) →
      (∀ D∈Ds,∀ a∈s.toSource.active D,∀ b∈v.toSource.active D,∀ i j,
        normalizedPositiveNorm s.toSource i Z D a (zs D a b)*
          normalizedPositiveNorm v.toSource j Z D b (zv D a b)≤ E i j) →
    (∑ D∈Ds,∑ a∈s.toSource.active D,∑ b∈v.toSource.active D,
      Real.sqrt (retainedAllocationCost s D a (zs D a b))*
        Real.sqrt (retainedAllocationCost v D b (zv D a b))) ≤
      wholeControl s*wholeControl v*(∑ i : Bool,∑ j : Bool,E i j)*C*(2*T)^(2*ε)*
        Z^((s.toSource.allowance Z+v.toSource.allowance Z+
          plainClipAllowance Z ![s.b₁,s.b₂]+plainClipAllowance Z ![v.b₁,v.b₂])/2)

theorem retained_pair_shell (N : ℕ) (hι : Fintype.card ι≤ N) (hκ : Fintype.card κ≤ N)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0< C ∧ RetainedPairShellBound ι κ C ε := by
  obtain ⟨C,hC,hbound⟩ := paired_all_clipped_active_shell N hι hκ ε hε
  refine ⟨C,hC,?_⟩
  intro s v Ds hD zs zv T Z hT hZ hlo hhi E hE hrow
  have hz := zero_lt_one.trans hZ
  let weight := fun D a b i j =>
    nonzeroClippedPairWeight s.toSource v.toSource i j Z D a b (zs D a b) (zv D a b)
  let B := C*(2*T)^(2*ε)*Z^((s.toSource.allowance Z+v.toSource.allowance Z+
    plainClipAllowance Z ![s.b₁,s.b₂]+plainClipAllowance Z ![v.b₁,v.b₂])/2)
  have hXs (i : Bool) (j : Fin 2) : 0< sourcePlainScales s.toSource i j := by
    cases i <;> fin_cases j <;> simp [sourcePlainScales,s.X₁_pos,s.X₂_pos,s.Y₁_pos,s.Y₂_pos]
  have hXv (i : Bool) (j : Fin 2) : 0< sourcePlainScales v.toSource i j := by
    cases i <;> fin_cases j <;> simp [sourcePlainScales,v.X₁_pos,v.X₂_pos,v.Y₁_pos,v.Y₂_pos]
  have hshell (i j : Bool) :
      (∑ D∈Ds,∑ a∈s.toSource.active D,∑ b∈v.toSource.active D,weight D a b i j)≤ B :=
    hbound s.toSource v.toSource i j ![s.b₁,s.b₂] ![v.b₁,v.b₂]
      (hXs i) (hXv j) s.support₁ s.support₂ v.support₁ v.support₂ Ds hD zs zv T Z hT hZ hlo hhi
  have hpoint (D : Ideal O) (hd : D∈Ds)
      (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) (ha : a∈s.toSource.active D)
      (b : Allocation D (Finset.univ : Finset (κ ⊕ Fin 2))) (hb : b∈v.toSource.active D) :
      Real.sqrt (retainedAllocationCost s D a (zs D a b))*
        Real.sqrt (retainedAllocationCost v D b (zv D a b)) ≤
      (wholeControl s*wholeControl v)*(∑ i : Bool,∑ j : Bool,weight D a b i j*E i j) := by
    apply (retained_pair_four_rectangles s v Z hZ D a b (zs D a b) (zv D a b)).trans
    apply mul_le_mul
    · exact mul_le_mul (frozenControl_le s D a) (frozenControl_le v D b)
        (frozenControl_nonneg v D b) (wholeControl_nonneg s)
    · apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (hrow D hd a ha b hb i j) (pair_weight_nonneg _ _ i j Z hz.le D a b _ _)
    · exact Finset.sum_nonneg (fun i _=>Finset.sum_nonneg (fun j _=>
        mul_nonneg (mul_nonneg (pair_weight_nonneg _ _ i j Z hz.le D a b _ _)
          (normalizedPositiveNorm_nonneg _ _ Z hz.le _ _ _))
          (normalizedPositiveNorm_nonneg _ _ Z hz.le _ _ _)))
    · exact mul_nonneg (wholeControl_nonneg s) (wholeControl_nonneg v)
  calc
    _ ≤ (wholeControl s*wholeControl v)*
        ∑ D∈Ds,∑ a∈s.toSource.active D,∑ b∈v.toSource.active D,
          ∑ i : Bool,∑ j : Bool,weight D a b i j*E i j := by
      simp only [Finset.mul_sum]
      exact Finset.sum_le_sum (fun D hd=>Finset.sum_le_sum (fun a ha=>
        Finset.sum_le_sum (fun b hb=>by simpa only [Finset.mul_sum] using hpoint D hd a ha b hb)))
    _ = (wholeControl s*wholeControl v)*
        ∑ i : Bool,∑ j : Bool,(∑ D∈Ds,∑ a∈s.toSource.active D,
          ∑ b∈v.toSource.active D,weight D a b i j)*E i j := by
      congr 1
      simp only [Fintype.sum_bool,Finset.sum_add_distrib,Finset.sum_mul]
    _ ≤ (wholeControl s*wholeControl v)*(∑ i : Bool,∑ j : Bool,B*E i j) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (wholeControl_nonneg s) (wholeControl_nonneg v))
      exact Finset.sum_le_sum (fun i _=>Finset.sum_le_sum (fun j _=>
        mul_le_mul_of_nonneg_right (hshell i j) (hE i j)))
    _ = _ := by simp only [←Finset.mul_sum]; dsimp [B]; ring

lemma RetainedPairShellBound.mono {C D ε : ℝ}
    (h : RetainedPairShellBound ι κ C ε) (hCD : C≤ D) : RetainedPairShellBound ι κ D ε := by
  intro s v Ds hD zs zv T Z hT hZ hlo hhi E hE hrow
  apply (h s v Ds hD zs zv T Z hT hZ hlo hhi E hE hrow).trans
  have hEs : 0≤∑i : Bool,∑j : Bool,E i j :=
    Finset.sum_nonneg (fun i _=>Finset.sum_nonneg (fun j _=>hE i j))
  have hbase : 0≤ wholeControl s*wholeControl v*(∑i : Bool,∑j : Bool,E i j) :=
    mul_nonneg (mul_nonneg (wholeControl_nonneg s) (wholeControl_nonneg v)) hEs
  gcongr

/-- One constant covers every pair of live subsets of the original slot type,
before moving allocations determine either subset. -/
theorem uniform_retained_pair_shell (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0< C ∧ ∀ S T : Finset ι, RetainedPairShellBound S T C ε := by
  have he (S T : Finset ι) := retained_pair_shell (Fintype.card ι)
    (show Fintype.card S≤ Fintype.card ι by simpa using Finset.card_le_univ S)
    (show Fintype.card T≤ Fintype.card ι by simpa using Finset.card_le_univ T) ε hε
  choose C hC hb using he
  let D := 1+∑S : Finset ι,∑T : Finset ι,C S T
  have hs (S : Finset ι) : 0≤∑T : Finset ι,C S T :=
    Finset.sum_nonneg (fun T _=>(hC S T).le)
  have hsum : 0≤∑S : Finset ι,∑T : Finset ι,C S T := Finset.sum_nonneg (fun S _=>hs S)
  refine ⟨D,by dsimp [D]; linarith,?_⟩
  intro S T
  apply (hb S T).mono
  have h1 := Finset.single_le_sum (fun T _=>(hC S T).le) (Finset.mem_univ T)
  have h2 := Finset.single_le_sum (fun S _=>hs S) (Finset.mem_univ S)
  dsimp [D]
  linarith

end
end OAI.SevenEighths.Cycle61HighResidual
#print axioms OAI.SevenEighths.Cycle61HighResidual.normalizedPositiveNorm_sq_bound
#print axioms OAI.SevenEighths.Cycle61HighResidual.clipped_pair_identity
#print axioms OAI.SevenEighths.Cycle61HighResidual.retained_pair_four_rectangles
#print axioms OAI.SevenEighths.Cycle61HighResidual.retained_pair_shell

#print axioms OAI.SevenEighths.Cycle61HighResidual.uniform_retained_pair_shell

#print axioms OAI.SevenEighths.Cycle61HighResidual.wholeControl_fixed

end
/- END ORIGINAL Cycle61.Physical.HighResidualAllocation -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondSourceControls; sha256 08588f8cc69fef0bc11160e329b546e501c046943aca9dca525232385a138f47 -/
section
                                              
                                        

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily Cycle61HighResidual
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonHeightEnvelope
open CenteredMomentAmplificationChildInput CenteredMomentAllocatedChildCapacity
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentEligibleEnergy CenteredMomentSlotRatios CenteredMomentActiveDivisorShell
local notation "O" => HeckeFamily.O

/-- Both common allocations only delete original slots. Their analytic
control is therefore bounded before either allocation or final height. -/
theorem actual_two_common_control_fixed {ι : Type*} [Fintype ι]
    (N : ℕ) (Cs bs : ℝ) (hCs : 1≤ Cs) (hbs : 1≤ bs)
    (s : Input ι) (hcard : Fintype.card ι≤ N) (hM : ∀i,s.M i≤ Cs)
    (hb₁ : s.b₁≤ bs) (hb₂ : s.b₂≤ bs)
    (C₁ R₁ : Ideal O) (B₁ : actualAllocations s.pools C₁) (χ₁ : Character) (t₁ : ℝ)
    (C₂ R₂ : Ideal O) (B₂ : actualAllocations (child s C₁ R₁ B₁ χ₁ t₁).pools C₂)
    (χ₂ : Character) (t₂ : ℝ) :
    wholeControl (commonData (withHeight (child s C₁ R₁ B₁ χ₁ t₁) χ₂ t₂) C₂ R₂ B₂)≤
      2*bs*Cs^N := by
  apply wholeControl_fixed N Cs bs hCs hbs
  · exact (live_card_le B₂.val).trans ((live_card_le B₁.val).trans hcard)
  · intro j
    exact hM j.val.val
  · exact hb₁
  · exact hb₂

/-- A fixed slot-window bound pays the complete residual and plain
clipping allowance. The denominator is the original logarithmic scale. -/
theorem fixed_source_allowance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (L bs : ℝ) (hL : 0≤ L) (hbs : 1≤ bs)
    (s : Data ι) (hcard : Fintype.card ι≤ N)
    (hwindow : ∀i,logWindow (s.lo i) (s.hi i)≤ L)
    (hb₁ : s.b₁≤ bs) (hb₂ : s.b₂≤ bs) (Z : ℝ) (hZ : 1< Z) :
    s.toSource.allowance Z+Cycle61.Physical.plainClipAllowance Z ![s.b₁,s.b₂]≤
      ((N:ℝ)*L+2*Real.log bs)/Real.log Z := by
  have hsum : (∑i,logWindow (s.lo i) (s.hi i))≤(N:ℝ)*L := by
    calc
      _≤∑_i : ι,L := Finset.sum_le_sum (fun i _=>hwindow i)
      _=(Fintype.card ι:ℝ)*L := by simp
      _≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hL
  have hp₁ : Real.log (max 1 s.b₁)≤ Real.log bs :=
    Real.log_le_log (by positivity) (max_le hbs hb₁)
  have hp₂ : Real.log (max 1 s.b₂)≤ Real.log bs :=
    Real.log_le_log (by positivity) (max_le hbs hb₂)
  unfold Source.allowance Cycle61.Physical.plainClipAllowance
  simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Real.logb]
  rw [←add_div,←add_div]
  apply div_le_div_of_nonneg_right _ (Real.log_pos hZ).le
  change (∑i,logWindow (s.lo i) (s.hi i))+
    (Real.log (max 1 s.b₁)+Real.log (max 1 s.b₂))≤ _
  linarith

/-- All fixed support allowances vanish uniformly before the source,
its two common allocations, and both character/height choices are known. -/
theorem eventual_two_common_allowance (N : ℕ) (L bs ε : ℝ)
    (hL : 0≤ L) (hbs : 1≤ bs) (hε : 0<ε) :
    ∀ᶠZ : ℝ in atTop,1< Z ∧
      ∀{ι : Type}[Fintype ι][DecidableEq ι](s : Input ι),
      Fintype.card ι≤ N → (∀i,logWindow (s.lo i) (s.hi i)≤ L) →
      s.b₁≤ bs → s.b₂≤ bs →
      ∀(C₁ R₁ : Ideal O)(B₁ : actualAllocations s.pools C₁)(χ₁ : Character)(t₁ : ℝ)
        (C₂ R₂ : Ideal O)(B₂ : actualAllocations (child s C₁ R₁ B₁ χ₁ t₁).pools C₂)
        (χ₂ : Character)(t₂ : ℝ),
      let src := commonData (withHeight (child s C₁ R₁ B₁ χ₁ t₁) χ₂ t₂) C₂ R₂ B₂
      src.toSource.allowance Z+Cycle61.Physical.plainClipAllowance Z ![src.b₁,src.b₂]≤ε := by
  filter_upwards [Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (((N:ℝ)*L+2*Real.log bs)/ε)),eventually_gt_atTop (1:ℝ)] with Z hz hZ
  refine ⟨hZ,?_⟩
  intro ι _ _ s hcard hwindow hb₁ hb₂ C₁ R₁ B₁ χ₁ t₁ C₂ R₂ B₂ χ₂ t₂ src
  apply (fixed_source_allowance N L bs hL hbs src
    ((live_card_le B₂.val).trans ((live_card_le B₁.val).trans hcard))
    (fun j=>hwindow j.val.val) hb₁ hb₂ Z hZ).trans
  exact (div_le_iff₀ (Real.log_pos hZ)).mpr
    (by nlinarith [(div_le_iff₀ hε).mp hz])

/-- The first common child retains exactly the original slot dictionary;
its new natural character does not change the slot coefficients. -/
theorem actual_child_matches {ι : Type*}[Fintype ι][DecidableEq ι]
    (M : Ideal O)[NeZero M](H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H)
    (s : Input ι)(η₀ : Character)(θ : ι→ RayQuotient.Characters M H)
    (w σ v : ι→ℝ)(W : ℝ→ℂ)(b Z : ℝ)
    (hm : CenteredMomentAllocatedRayDictionary.Matches M H hH s η₀ θ w σ v W b Z)
    (C R : Ideal O)(B : actualAllocations s.pools C)(χ : Character)(t : ℝ) :
    CenteredMomentAllocatedRayDictionary.Matches M H hH (child s C R B χ t) η₀
      (fun j=>θ j.val) (fun j=>w j.val) (fun j=>σ j.val) (fun j=>v j.val) W b Z := by
  exact ⟨fun j I=>hm.character j.val I,fun j x=>hm.profile j.val x,
    fun j=>hm.pool j.val,fun j=>hm.scale j.val⟩

/-- The first common allocation cannot enlarge any of the four plain
scales used by the final shell theorem. -/
theorem actual_child_plain_scale_le {ι : Type*}[Fintype ι]
    (s : Input ι)(C R : Ideal O)(B : actualAllocations s.pools C)(χ : Character)(t : ℝ)
    (second : Bool)(j : Fin 2) :
    Cycle61.Physical.sourcePlainScales (child s C R B χ t).toData.toSource second j≤
      Cycle61.Physical.sourcePlainScales s.toData.toSource second j := by
  have hnorm : (1:ℝ)≤(B.val (Sum.inr j)).absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (alloc_ne s C B (Sum.inr j)))
  cases second <;> fin_cases j
  · exact div_le_self s.X₁_pos.le hnorm
  · exact div_le_self s.X₂_pos.le hnorm
  · exact div_le_self s.Y₁_pos.le hnorm
  · exact div_le_self s.Y₂_pos.le hnorm

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_two_common_control_fixed
#print axioms OAI.SevenEighths.Cycle61InitialMass.fixed_source_allowance
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_two_common_allowance

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_child_matches
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_child_plain_scale_le

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondSourceControls -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorCoprime; sha256 02bf15d0d81a96695265e3fe245cf13041afcdeb0f88b693e6eabced827601af -/
section
                                                        
                                                               

set_option autoImplicit false
set_option maxHeartbeats 900000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAllocatedRayDictionary CenteredMomentAmplificationSlotGap
open CenteredMomentAmplificationChildInput CenteredMomentCommonAllocationSum
open HeckePrimeAnnular ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance errorCoprimeFiniteQuotient : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- The full stored prime pool has an annulus cap, including entries where
the smooth slot profile vanishes. -/
theorem actual_full_slot_norm_cap {α : Type*}[Fintype α][DecidableEq α]
    (s : Input α)(η₀ : Character)(θ : α→ RayQuotient.Characters M H)
    (w σ v : α→ℝ)(W : ℝ→ℂ)(b Z eta : ℝ)(hZ : 1≤ Z)
    (hm : Matches M H hH s η₀ θ w σ v W b Z)(hw : ∀i,w i≤ eta) :
    ∀i I,I∈s.slots i→ Prime I ∧ (I.absNorm:ℝ)≤ max 1 b*Z^eta := by
  intro i I hI
  rw [hm.pool i] at hI
  have hmem := Finset.mem_filter.mp hI
  refine ⟨hmem.2.1,?_⟩
  have hz : 0< Z := zero_lt_one.trans_le hZ
  have ha := hmem.1
  change I∈idealsUpTo ⌊max 1 b*Z^(w i)⌋₊ at ha
  have hn : (I.absNorm:ℝ)≤ max 1 b*Z^(w i) :=
    (Nat.cast_le.mpr (mem_idealsUpTo.mp ha).2).trans (Nat.floor_le (by positivity))
  exact hn.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ (hw i)) (le_max_of_le_left (by norm_num)))

/-- A genuine amplifier-prime gap separates it from all stored original
slots. No nonzero-profile restriction is used. -/
theorem actual_full_slot_coprime {α : Type*}[Fintype α][DecidableEq α]
    (s : Input α)(η₀ : Character)(θ : α→ RayQuotient.Characters M H)
    (w σ v : α→ℝ)(W : ℝ→ℂ)(b Z eta ell : ℝ)(hZ : 1≤ Z)
    (hm : Matches M H hH s η₀ θ w σ v W b Z)(hw : ∀i,w i≤ eta)
    (Q : Ideal O)(hQ : Prime Q)(hQN : Z^ell≤(Q.absNorm:ℝ))
    (hgap : max 1 b*Z^eta< Z^ell) :
    ∀i I,I∈s.slots i→ IsCoprime Q I := by
  intro i I hI
  have hc := actual_full_slot_norm_cap M H hH s η₀ θ w σ v W b Z eta hZ hm hw i I hI
  exact ((HeckeInverseAmplification.prime_coprime_iff ⟨Q,hQ⟩ I).mpr
    (amplifier_not_dvd_slot Q I hQ hc.1 Z ell eta (max 1 b) hgap hQN hc.2)).symm

/-- Common allocation deletes slots, so full-pool coprimality is inherited
by the unpruned first child used in the extracted-source formalization. -/
theorem actual_child_full_slot_coprime {α : Type*}[Fintype α][DecidableEq α]
    (s : Input α)(Q : Ideal O)(hc : ∀i I,I∈s.slots i→ IsCoprime Q I)
    (C R : Ideal O)(B : actualAllocations s.pools C)(χ : Character)(t : ℝ) :
    ∀i I,I∈(child s C R B χ t).slots i→ IsCoprime Q I := by
  intro i I hI
  exact hc i.val I hI

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_full_slot_norm_cap
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_full_slot_coprime
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_child_full_slot_coprime

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorCoprime -/

/- BEGIN ORIGINAL Cycle61.Moment.HighParameters; sha256 3c7df429716c1f3ee9e3b7ffde74271725db9865b6408724883aacbce8b2d918 -/
section
                                      

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped ContDiff
open Set Filter

def highBuffer (Rs Rp es ep : ℝ) := min (1/2000) (min (es/(32*(Rs+1))) (ep/(48*(Rp+2))))
def highKappa (es ep : ℝ) := min 1 (min (es/4) (ep/32))
def highHeight (J : ℕ) (loss d es ep : ℝ) :=
  min (loss/(2*(J+1))) (min (d*(ep/8)/32) (d*es/16))

lemma high_buffer_pos {Rs Rp es ep : ℝ} (hRs : 0≤ Rs) (hRp : 0≤ Rp)
    (hes : 0< es) (hep : 0< ep) : 0< highBuffer Rs Rp es ep := by
  dsimp [highBuffer]
  positivity

lemma high_kappa_pos {es ep : ℝ} (hes : 0< es) (hep : 0< ep) :
    0< highKappa es ep := by dsimp [highKappa]; positivity

lemma high_buffer_budgets {Rs Rp es ep : ℝ} (hRs : 0≤ Rs) (hRp : 0≤ Rp)
    (hes : 0< es) (hep : 0< ep) :
    8*highBuffer Rs Rp es ep*Rs+highKappa es ep≤ es ∧
      12*highBuffer Rs Rp es ep*(Rp+2)+8*highKappa es ep+2*(ep/8)≤ ep := by
  have hbuf : highBuffer Rs Rp es ep≤ es/(32*(Rs+1)) := (min_le_right (1/2000:ℝ) _).trans (min_le_left (es/(32*(Rs+1))) _)
  have hbuf' : highBuffer Rs Rp es ep≤ ep/(48*(Rp+2)) := (min_le_right (1/2000:ℝ) _).trans (min_le_right _ (ep/(48*(Rp+2))))
  change highBuffer Rs Rp es ep≤ es/(32*(Rs+1)) at hbuf
  change highBuffer Rs Rp es ep≤ ep/(48*(Rp+2)) at hbuf'
  have hs := (le_div_iff₀ (by positivity : 0<32*(Rs+1))).mp hbuf
  have hp := (le_div_iff₀ (by positivity : 0<48*(Rp+2))).mp hbuf'
  have hk : highKappa es ep≤ es/4 :=
    (min_le_right 1 _).trans (min_le_left _ _)
  have hk' : highKappa es ep≤ ep/32 :=
    (min_le_right 1 _).trans (min_le_right _ _)
  have he := high_buffer_pos hRs hRp hes hep
  constructor <;> nlinarith

/-- The analytic parameters exist for every positive requested loss.
The height exponent is selected after the density degree J. -/
def highParameters (W : ℝ→ℂ) (A B Rs Rp es ep lo hi bΦ Mcap Bmask margin d loss : ℝ)
    (J : ℕ) (bound : ℕ→ℝ)
    (hA : 0< A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hRs : 0≤ Rs) (hRp : 0≤ Rp) (hes : 0< es) (hep : 0< ep)
    (hbΦ : 0≤ bΦ) (hmargin : 0< margin) (hd : 0< d)
    (hsupply : Mcap+Bmask+margin≤ d) (hloss : 0< loss) (hbound : ∀k,0≤ bound k) :
    HighSourceParameters where
  Wslot := W
  A₀ := A
  B₀ := B
  hA₀ := hA
  hWs := hWs
  hW := hW
  Rwidth := Rs
  Rplain := Rp
  dmax := d
  τ := highHeight J loss d es ep
  εslot := es
  εplain := ep
  e := highBuffer Rs Rp es ep
  κ := highKappa es ep
  vplain := ep/8
  vslot := es
  σmin := lo
  σmax := hi
  bΦ := bΦ
  Mcap := Mcap
  Bmask := Bmask
  margin := margin
  d := d
  hRw := hRs
  hRp := hRp
  hdmax := hd.le
  hτ := by dsimp [highHeight]; positivity
  hεs := hes
  hεp := hep
  he := high_buffer_pos hRs hRp hes hep
  he' := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  hκ := high_kappa_pos hes hep
  hκ' := min_le_left _ _
  hvp := by positivity
  hvs := hes.le
  hslotBudget := (high_buffer_budgets hRs hRp hes hep).1
  hplainBudget := (high_buffer_budgets hRs hRp hes hep).2
  hbΦ := hbΦ
  hmargin := hmargin
  hd := hd
  hdsupply := hsupply
  hdm := le_rfl
  profileBound := bound
  hprofile := hbound

lemma high_height_losses (J : ℕ) (loss d es ep : ℝ) (hloss : 0< loss)
    (hd : 0< d) (hes : 0< es) (hep : 0< ep) :
    0< highHeight J loss d es ep ∧
      highHeight J loss d es ep*(J+1)≤ loss/2 ∧
      16*highHeight J loss d es ep≤ d*(ep/8) ∧
      8*highHeight J loss d es ep≤ d*es := by
  have ht : 0< highHeight J loss d es ep := by dsimp [highHeight]; positivity
  have hJ : 0<(2:ℝ)*(J+1) := by positivity
  have h₁ : highHeight J loss d es ep*(2*(J+1))≤ loss :=
    (le_div_iff₀ hJ).mp (min_le_left (loss/(2*(J+1))) _)
  have h₂ : highHeight J loss d es ep≤ d*(ep/8)/32 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have h₃ : highHeight J loss d es ep≤ d*es/16 :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ht,?_,?_,?_⟩ <;> nlinarith

/-- The chosen height loss pays both analytic height gates and the density
polynomial uniformly on the retained height range. The threshold is fixed
before the actual height bin and source data. -/
theorem eventually_high_truncated_heights (P : HighSourceParameters) (J : ℕ)
    (loss : ℝ) (hslot : 8*P.τ≤ P.d*P.vslot)
    (hplain : 16*P.τ≤ P.d*P.vplain) (hdensity : 2*P.τ*(J+1)≤ loss) :
    ∀ᶠ Z : ℝ in atTop,1< Z ∧ ∀i : ℕ,(i:ℝ)≤ Z^P.τ →
      (3+(3*i+2:ℕ)*Z^P.τ)^2≤(Z^P.d)^P.vslot ∧
      (3+(3*i+2:ℕ)*Z^P.τ)^4≤(Z^P.d)^P.vplain ∧
      (1+3*(i+1:ℕ)*Z^P.τ)^J≤ Z^loss := by
  filter_upwards [(tendsto_rpow_atTop P.hτ).eventually
    (eventually_ge_atTop (max (8:ℝ) (7^J))),eventually_gt_atTop (1:ℝ)] with Z hbig hZ
  refine ⟨hZ,?_⟩
  intro i hi
  let x := Z^P.τ
  have hx : 8≤ x := (le_max_left _ _).trans hbig
  have hx₁ : 1≤ x := by linarith
  have hx₀ : 0≤ x := by linarith
  have hconst : (7:ℝ)^J≤ x^2 := ((le_max_right _ _).trans hbig).trans (by nlinarith)
  have hy : (3+(3*i+2:ℕ)*x)≤ x^3 := by
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    change (i:ℝ)≤ x at hi
    have hix := mul_le_mul_of_nonneg_right hi hx₀
    have hxx : 8*x^2≤ x^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sq_nonneg x)]
    nlinarith [sq_nonneg (x-1)]
  have hd : (1+3*(i+1:ℕ)*x)≤7*x^2 := by
    simp only [Nat.cast_add,Nat.cast_one]
    change (i:ℝ)≤ x at hi
    nlinarith [mul_le_mul_of_nonneg_right hi hx₀,sq_nonneg (x-1)]
  have hz : 0< Z := zero_lt_one.trans hZ
  have hp (k : ℕ) : x^k=Z^(P.τ*(k:ℝ)) := by
    dsimp [x]
    rw [←Real.rpow_natCast,←Real.rpow_mul hz.le]
  refine ⟨?_,?_,?_⟩
  · calc
      _ ≤ (x^3)^2 := pow_le_pow_left₀ (by positivity) hy 2
      _ = Z^(P.τ*6) := by rw [←pow_mul]; norm_num; exact hp 6
      _ ≤ _ := by
        rw [←Real.rpow_mul hz.le]
        apply Real.rpow_le_rpow_of_exponent_le hZ.le
        nlinarith [P.hτ]
  · calc
      _ ≤ (x^3)^4 := pow_le_pow_left₀ (by positivity) hy 4
      _ = Z^(P.τ*12) := by rw [←pow_mul]; norm_num; exact hp 12
      _ ≤ _ := by
        rw [←Real.rpow_mul hz.le]
        apply Real.rpow_le_rpow_of_exponent_le hZ.le
        nlinarith [P.hτ]
  · calc
      _ ≤ (7*x^2)^J := pow_le_pow_left₀ (by positivity) hd J
      _ = 7^J*x^(2*J) := by rw [mul_pow,←pow_mul]
      _ ≤ x^2*x^(2*J) := mul_le_mul_of_nonneg_right hconst (pow_nonneg hx₀ _)
      _ = Z^(P.τ*(2*(J+1))) := by
        rw [←pow_add,hp]
        congr 1
        push_cast
        ring
      _ ≤ Z^loss := Real.rpow_le_rpow_of_exponent_le hZ.le (by nlinarith)

end
end OAI.SevenEighths.Cycle61Moment
#print axioms OAI.SevenEighths.Cycle61Moment.highParameters
#print axioms OAI.SevenEighths.Cycle61Moment.high_height_losses
#print axioms OAI.SevenEighths.Cycle61Moment.eventually_high_truncated_heights

end
/- END ORIGINAL Cycle61.Moment.HighParameters -/
