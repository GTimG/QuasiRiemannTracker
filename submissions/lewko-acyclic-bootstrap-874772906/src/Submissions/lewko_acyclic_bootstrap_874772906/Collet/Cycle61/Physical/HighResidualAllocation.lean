import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Moment.JointColumnExtraction

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

lemma normalizedPositiveNorm_nonneg (s : Source ι) (second : Bool) (Z : ℝ) (hZ : 0≤Z) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) (z : O) :
    0 ≤ normalizedPositiveNorm s second Z D a z := by
  unfold normalizedPositiveNorm
  exact div_nonneg (norm_nonneg _) (Real.rpow_nonneg hZ _)

/-- The negative clipping contribution remains explicit in the squared norm. -/
lemma normalizedPositiveNorm_sq (s : Source ι) (second : Bool)
    (Z : ℝ) (hZ : 0<Z) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) (z : O) :
    (normalizedPositiveNorm s second Z D a z)^2 =
      ‖sourcePositiveRow s second D a z‖^2/Z^(sourcePostClip s second Z D a) := by
  unfold normalizedPositiveNorm
  rw [div_pow,←Real.rpow_natCast (Z^(sourcePostClip s second Z D a/2)) 2,←Real.rpow_mul hZ.le]
  congr 2
  ring

lemma normalizedPositiveNorm_sq_bound (s : Source ι) (second : Bool)
    (Z : ℝ) (hZ : 0<Z) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) (z : O) (C e : ℝ)
    (hrow : ‖sourcePositiveRow s second D a z‖^2≤C*Z^e) :
    (normalizedPositiveNorm s second Z D a z)^2 ≤
      C*Z^(e-sourcePostClip s second Z D a) := by
  rw [normalizedPositiveNorm_sq s second Z hZ D a z,Real.rpow_sub hZ,←mul_div_assoc]
  exact div_le_div_of_nonneg_right hrow (Real.rpow_pos_of_pos hZ _).le

lemma clipped_pair_identity (s : Source ι) (v : Source κ) (secondS secondV : Bool)
    (Z : ℝ) (hZ : 1<Z) (D : Ideal O)
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
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) : 0≤frozenControl s D a := by
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
    (Z : ℝ) (hZ : 1<Z) (D : Ideal O)
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
    (Real.sqrt_nonneg _) (by positivity : 0≤frozenControl s D a/
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
lemma wholeControl_nonneg (s : Data ι) : 0≤wholeControl s := by
  unfold wholeControl
  exact mul_nonneg (Real.sqrt_nonneg _) (Finset.prod_nonneg (fun i _ => zero_le_one.trans (s.M_ge_one i)))

omit [DecidableEq ι] in
/-- Fixed original slot and support bounds absorb every frozen allocation. -/
lemma wholeControl_fixed (N : ℕ) (Cs bs : ℝ) (hCs : 1≤Cs) (hbs : 1≤bs)
    (s : Data ι) (hcard : Fintype.card ι≤N) (hM : ∀i,s.M i≤Cs)
    (hb₁ : s.b₁≤bs) (hb₂ : s.b₂≤bs) : wholeControl s≤2*bs*Cs^N := by
  have hp : (∏i,s.M i)≤Cs^N := by
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
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) : frozenControl s D a≤wholeControl s := by
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
    (fun i _=>zero_le_one.trans (s.M_ge_one i)) (fun i _ _=>s.M_ge_one i)

lemma pair_weight_nonneg (s : Source ι) (v : Source κ) (i j : Bool)
    (Z : ℝ) (hZ : 0≤Z) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (b : Allocation D (Finset.univ : Finset (κ ⊕ Fin 2))) (zs zv : O) :
    0≤nonzeroClippedPairWeight s v i j Z D a b zs zv := by
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
      (T Z : ℝ), 1≤T → 1<Z →
      (∀ D∈Ds,T≤(D.absNorm:ℝ)) → (∀ D∈Ds,(D.absNorm:ℝ)<2*T) →
    ∀ E : Bool→Bool→ℝ, (∀ i j,0≤E i j) →
      (∀ D∈Ds,∀ a∈s.toSource.active D,∀ b∈v.toSource.active D,∀ i j,
        normalizedPositiveNorm s.toSource i Z D a (zs D a b)*
          normalizedPositiveNorm v.toSource j Z D b (zv D a b)≤E i j) →
    (∑ D∈Ds,∑ a∈s.toSource.active D,∑ b∈v.toSource.active D,
      Real.sqrt (retainedAllocationCost s D a (zs D a b))*
        Real.sqrt (retainedAllocationCost v D b (zv D a b))) ≤
      wholeControl s*wholeControl v*(∑ i : Bool,∑ j : Bool,E i j)*C*(2*T)^(2*ε)*
        Z^((s.toSource.allowance Z+v.toSource.allowance Z+
          plainClipAllowance Z ![s.b₁,s.b₂]+plainClipAllowance Z ![v.b₁,v.b₂])/2)

theorem retained_pair_shell (N : ℕ) (hι : Fintype.card ι≤N) (hκ : Fintype.card κ≤N)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ RetainedPairShellBound ι κ C ε := by
  obtain ⟨C,hC,hbound⟩ := paired_all_clipped_active_shell N hι hκ ε hε
  refine ⟨C,hC,?_⟩
  intro s v Ds hD zs zv T Z hT hZ hlo hhi E hE hrow
  have hz := zero_lt_one.trans hZ
  let weight := fun D a b i j =>
    nonzeroClippedPairWeight s.toSource v.toSource i j Z D a b (zs D a b) (zv D a b)
  let B := C*(2*T)^(2*ε)*Z^((s.toSource.allowance Z+v.toSource.allowance Z+
    plainClipAllowance Z ![s.b₁,s.b₂]+plainClipAllowance Z ![v.b₁,v.b₂])/2)
  have hXs (i : Bool) (j : Fin 2) : 0<sourcePlainScales s.toSource i j := by
    cases i <;> fin_cases j <;> simp [sourcePlainScales,s.X₁_pos,s.X₂_pos,s.Y₁_pos,s.Y₂_pos]
  have hXv (i : Bool) (j : Fin 2) : 0<sourcePlainScales v.toSource i j := by
    cases i <;> fin_cases j <;> simp [sourcePlainScales,v.X₁_pos,v.X₂_pos,v.Y₁_pos,v.Y₂_pos]
  have hshell (i j : Bool) :
      (∑ D∈Ds,∑ a∈s.toSource.active D,∑ b∈v.toSource.active D,weight D a b i j)≤B :=
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
    (h : RetainedPairShellBound ι κ C ε) (hCD : C≤D) : RetainedPairShellBound ι κ D ε := by
  intro s v Ds hD zs zv T Z hT hZ hlo hhi E hE hrow
  apply (h s v Ds hD zs zv T Z hT hZ hlo hhi E hE hrow).trans
  have hEs : 0≤∑i : Bool,∑j : Bool,E i j :=
    Finset.sum_nonneg (fun i _=>Finset.sum_nonneg (fun j _=>hE i j))
  have hbase : 0≤wholeControl s*wholeControl v*(∑i : Bool,∑j : Bool,E i j) :=
    mul_nonneg (mul_nonneg (wholeControl_nonneg s) (wholeControl_nonneg v)) hEs
  gcongr

/-- One constant covers every pair of live subsets of the original slot type,
before moving allocations determine either subset. -/
theorem uniform_retained_pair_shell (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ S T : Finset ι, RetainedPairShellBound S T C ε := by
  have he (S T : Finset ι) := retained_pair_shell (Fintype.card ι)
    (show Fintype.card S≤Fintype.card ι by simpa using Finset.card_le_univ S)
    (show Fintype.card T≤Fintype.card ι by simpa using Finset.card_le_univ T) ε hε
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
