/- Copyright (c) 2026 Sil. Apache-2.0.
Quantitative actual selected-D averages of outer zero/tail/exceptional
terms. The nonexceptional term remains an explicit, separate quantity.

-/
import Candidate.SilPrior.FourthPower.OuterFreshCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.OuterFreshSelected
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion ConcretePrimeRowBridge
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentGaussEnergy
open CenteredMomentOriginalChildEnergy
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentSourceSecondZeroEnergy CenteredMomentSupportedTailAggregate
open EisensteinSchwartzPoisson
open MixedSupplierSplit MixedSupplierFourthRow MixedSupplierSource MixedSupplierPositive MixedSupplierOuterActive
open MixedSupplierOriginalFrequency MixedSupplierKernel
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow
open MixedOriginalNormCap MixedOriginalTail MixedInnerExceptionalBlock MixedInnerExceptionalLedger
open OuterFreshWindowPair OuterFreshAssembly OuterFreshConsumer OuterFreshCompletion OuterFreshRemainders
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
variable {ι : Type u} [Fintype ι] {a b : ℝ}

def selectedVolume (q : Data ι) : ℝ := ∏j : q.J,q.P j.val.val
def selectedMass (q : Data ι) (M : ι→ℝ) : ℝ :=
  (256:ℝ)^(Fintype.card q.J)*(∏j : q.J,M j.val.val)^2
def average (q : Data ι) (x : Frozen q) (τ : Character) (F : Selected q→ℝ) : ℝ :=
  (∑y∈activeSelected q,selectedPositiveWeight q x y τ*F y)/selectedVolume q

theorem selectedVolume_pos (q : Data ι) (hP : ∀i,0<q.P i) : 0<selectedVolume q :=
  Finset.prod_pos (fun j _=>hP j.val.val)

theorem selectedMass_nonneg (q : Data ι) (M : ι→ℝ) : 0≤selectedMass q M := by
  unfold selectedMass
  positivity

theorem positive_mass (q : Data ι) (x : Frozen q) (τ : Character) (M : ι→ℝ)
    (hM : ∀i,0≤M i) (hν : ∀i,∀I∈q.pool i,‖q.ν i I‖≤1)
    (hW : ∀i z,‖q.Wslot i z‖≤M i) (hP : ∀i,0<q.P i)
    (hpool : ∀i,∀I∈q.pool i,(I.absNorm:ℝ)≤2*q.P i) :
    (∑y∈activeSelected q,selectedPositiveWeight q x y τ)≤selectedMass q M*selectedVolume q := by
  have hw (y : Selected q) : selectedPositiveWeight q x y τ≤(∏j : q.J,M j.val.val)^2 := by
    unfold selectedPositiveWeight
    split_ifs
    · exact pow_le_pow_left₀ (norm_nonneg _) (selected_weight_norm q M hM hν hW y) 2
    · exact sq_nonneg _
  calc
    _≤∑_y∈activeSelected q,(∏j : q.J,M j.val.val)^2 := Finset.sum_le_sum (fun y _=>hw y)
    _=((activeSelected q).card:ℝ)*(∏j : q.J,M j.val.val)^2 := by
      simp only [Finset.sum_const,nsmul_eq_mul]
    _≤((256:ℝ)^(Fintype.card q.J)*selectedVolume q)*(∏j : q.J,M j.val.val)^2 :=
      mul_le_mul_of_nonneg_right (active_selected_annular_card q (fun i=>(hP i).le) hpool)
        (sq_nonneg _)
    _=_ := by unfold selectedMass;ring

private theorem average_bound (q : Data ι) (x : Frozen q) (τ : Character) (M : ι→ℝ)
    (hM : ∀i,0≤M i) (hν : ∀i,∀I∈q.pool i,‖q.ν i I‖≤1)
    (hW : ∀i z,‖q.Wslot i z‖≤M i) (hP : ∀i,0<q.P i)
    (hpool : ∀i,∀I∈q.pool i,(I.absNorm:ℝ)≤2*q.P i)
    (F : Selected q→ℝ) (E : ℝ) (hE : 0≤E)
    (hF : ∀y∈activeSelected q,selectedPositiveWeight q x y τ≠0→F y≤E) :
    average q x τ F≤selectedMass q M*E := by
  have hv := selectedVolume_pos q hP
  unfold average
  apply (div_le_iff₀ hv).mpr
  calc
    _≤∑y∈activeSelected q,selectedPositiveWeight q x y τ*E := by
      apply Finset.sum_le_sum
      intro y hy
      by_cases hw : selectedPositiveWeight q x y τ=0
      · simp only [hw,zero_mul,le_refl]
      · exact mul_le_mul_of_nonneg_left (hF y hy hw) (selected_positive_nonneg q x y τ)
    _=(∑y∈activeSelected q,selectedPositiveWeight q x y τ)*E := (Finset.sum_mul _ _ _).symm
    _≤(selectedMass q M*selectedVolume q)*E :=
      mul_le_mul_of_nonneg_right (positive_mass q x τ M hM hν hW hP hpool) hE
    _=_ := by ring

/-- The fresh-D lower bound comes from each ACTUAL nonzero selected
amplitude and its original pool, not from an invented dyadic hypothesis. -/
theorem actual_fresh_gain (q : Data ι) (hP : ∀i,0<q.P i)
    (hpool : ∀i,∀I∈q.pool i,q.P i≤(I.absNorm:ℝ) ∧ (I.absNorm:ℝ)≤2*q.P i)
    (y : Selected q) (hy : y∈activeSelected q) :
    freshGain q y≤1/(selectedVolume q)^(2/3:ℝ) := by
  have hlo := (selected_product_window q y hy q.P (fun i=>2*q.P i)
    (fun i=>(hP i).le) hpool).1
  have hv := selectedVolume_pos q hP
  have hpow := Real.rpow_le_rpow hv.le hlo (by norm_num : (0:ℝ)≤2/3)
  exact div_le_div_of_nonneg_left zero_le_one (Real.rpow_pos_of_pos hv _) hpow

/-- A nonzero frozen amplitude belongs to its literal original pool. -/
theorem active_frozen_mem (q : Data ι) (x : Frozen q) (hx : frozenWeight q x≠0)
    (i : ↥(q.Lᶜ)) : (x i).val∈q.pool i.val := by
  have hi := (Finset.prod_ne_zero_iff.mp hx) i (Finset.mem_univ i)
  by_contra hn
  exact hi (by simp only [amplitude,slotAmplitude,if_neg hn])

/-- The frozen-f norm lower bound comes from the same actual pools. -/
theorem actual_frozen_lower (q : Data ι) (x : Frozen q) (hx : frozenWeight q x≠0)
    (hP : ∀i,0<q.P i) (hpool : ∀i,∀I∈q.pool i,q.P i≤(I.absNorm:ℝ)) :
    (∏i : ↥(q.Lᶜ),q.P i.val)≤((frozenProduct q x).absNorm:ℝ) := by
  simp only [frozenProduct,map_prod,Nat.cast_prod]
  exact Finset.prod_le_prod₀ (fun i _=>(hP i.val).le)
    (fun i _=>hpool i.val (x i).val (active_frozen_mem q x hx i))

theorem frozen_weight_norm (q : Data ι) (x : Frozen q) (M : ι→ℝ)
    (hM : ∀i,0≤M i) (hν : ∀i,∀I∈q.pool i,‖q.ν i I‖≤1)
    (hW : ∀i z,‖q.Wslot i z‖≤M i) :
    ‖frozenWeight q x‖≤∏i : ↥(q.Lᶜ),M i.val := by
  rw [frozenWeight,norm_prod]
  exact Finset.prod_le_prod₀ (fun i _=>norm_nonneg _)
    (fun i _=>amplitude_norm q M hM hν hW i.val (x i))

/-- The central f normalization is EXPLICIT. The raw frozenWeight itself
does not contain N(f)^(-1/2), and this theorem never claims that it does. -/
theorem frozen_central_bound (q : Data ι) (x : Frozen q) (M : ι→ℝ)
    (hM : ∀i,0≤M i) (hν : ∀i,∀I∈q.pool i,‖q.ν i I‖≤1)
    (hW : ∀i z,‖q.Wslot i z‖≤M i) (hP : ∀i,0<q.P i)
    (hpool : ∀i,∀I∈q.pool i,q.P i≤(I.absNorm:ℝ)) :
    ‖frozenWeight q x‖^2/((frozenProduct q x).absNorm:ℝ)≤
      (∏i : ↥(q.Lᶜ),M i.val)^2/(∏i : ↥(q.Lᶜ),q.P i.val) := by
  have hv : 0<(∏i : ↥(q.Lᶜ),q.P i.val) := Finset.prod_pos (fun i _=>hP i.val)
  by_cases hx : frozenWeight q x=0
  · simp only [hx,norm_zero,zero_pow (by decide : 2≠0),zero_div]
    exact div_nonneg (sq_nonneg _) hv.le
  · have hlo := actual_frozen_lower q x hx hP hpool
    calc
      _≤‖frozenWeight q x‖^2/(∏i : ↥(q.Lᶜ),q.P i.val) :=
        div_le_div_of_nonneg_left (sq_nonneg _) hv hlo
      _≤_ := div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (frozen_weight_norm q x M hM hν hW) 2) hv.le

/-- A finite positive sum preserves inequalities; this does not assert
an analytic estimate for either energy. -/
theorem average_mono (q : Data ι) (x : Frozen q) (τ : Character)
    (hP : ∀i,0<q.P i) (F G : Selected q→ℝ)
    (hFG : ∀y∈activeSelected q,F y≤G y) : average q x τ F≤average q x τ G := by
  apply div_le_div_of_nonneg_right _ (selectedVolume_pos q hP).le
  exact Finset.sum_le_sum (fun y hy=>mul_le_mul_of_nonneg_left (hFG y hy)
    (selected_positive_nonneg q x y τ))

/-- All four actual outer terms have the SAME normalization. In
particular the nonexceptional remainder is not replaced by a hypothesis. -/
theorem average_fourCost (q : Data ι) (x : Frozen q)
    (s : Source (RestIndex q) a b) (seed : Id) (τ : Character) (ξ χ : RayCharacter)
    (Q : Id) (t K T Z ζ H : ℝ) :
    average q x τ (fun y=>fourCost q x y s seed τ ξ χ Q t K T Z ζ H/sourceVolume s)=
      average q x τ (fun y=>‖outerZero q x y s seed τ ξ t K‖/sourceVolume s)+
      average q x τ (fun y=>‖fixedPart false q x y s seed τ ξ χ Q t ballProfile K T Z ζ H‖/sourceVolume s)+
      average q x τ (fun y=>‖fixedPart true q x y s seed τ ξ χ Q t ballProfile K T Z ζ H‖/sourceVolume s)+
      average q x τ (fun y=>‖secondDiscardedEnergy τ t (sourceColumns s)
        (outerColumn q x y seed ξ) ballProfile K T Z ζ‖/sourceVolume s) := by
  simp only [average,fourCost,add_div,mul_add,Finset.sum_add_distrib]

theorem average_div (q : Data ι) (x : Frozen q) (τ : Character)
    (F : Selected q→ℝ) (V : ℝ) :
    average q x τ (fun y=>F y/V)=average q x τ F/V := by
  unfold average
  simp only [← mul_div_assoc, ← Finset.sum_div]
  ring

/-- The genuine original-K source energy reaches those four positive
averages by exact Poisson/completion identities, with no new energy input. -/
theorem actual_average_four_components (q : Data ι) (x : Frozen q)
    (s : Source (RestIndex q) a b) (seed : Id) (τ : Character) (ξ χ : RayCharacter)
    (Q : Id) (t K T Z ζ H : ℝ) (hP : ∀i,0<q.P i) (hK : 0<K)
    (hH : ∀I∈fixedPool q x s seed,(I.absNorm:ℝ)≤H) :
    average q x τ (fun y=>(sourceGaussEnergy (sourceColumns s)
      (outerColumn q x y seed ξ) (heightCoeff τ t) ballProfile K).re/sourceVolume s)≤
      average q x τ (fun y=>‖outerZero q x y s seed τ ξ t K‖/sourceVolume s)+
      average q x τ (fun y=>‖fixedPart false q x y s seed τ ξ χ Q t ballProfile K T Z ζ H‖/sourceVolume s)+
      average q x τ (fun y=>‖fixedPart true q x y s seed τ ξ χ Q t ballProfile K T Z ζ H‖/sourceVolume s)+
      average q x τ (fun y=>‖secondDiscardedEnergy τ t (sourceColumns s)
        (outerColumn q x y seed ξ) ballProfile K T Z ζ‖/sourceVolume s) := by
  rw [←average_fourCost]
  apply average_mono q x τ hP
  intro y hy
  exact div_le_div_of_nonneg_right
    (actual_four_components q x y s seed τ ξ χ Q t K T Z ζ H hK hH) (sourceVolume_pos s).le

/-- Quantitative actual diagonal average, including the original seed.
The selected averaging denominator is present exactly once. -/
theorem uniform_average_zero (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(κ : Type u) [Fintype κ],∀q : Data κ,∀x : Frozen q,
      ∀a b : ℝ,∀s : Source (RestIndex q) a b,Fintype.card (RestIndex q)≤N→
      ∀ha : 0<a,Matches q x s ha→∀M : κ→ℝ,(∀i,0≤M i)→
      (∀i,∀I∈q.pool i,‖q.ν i I‖≤1)→(∀i z,‖q.Wslot i z‖≤M i)→
      (∀i,0<q.P i)→(∀i,∀I∈q.pool i,(I.absNorm:ℝ)≤2*q.P i)→
      ∀(seed : Id)(ξ : RayCharacter)(τ : Character)(t K Y : ℝ),seed≠0→0≤K→1≤Y→
      sourceNormCap s.P b s.T s.d≤Y→
      average q x τ (fun y=>‖outerZero q x y s seed τ ξ t K‖)≤
        selectedMass q M*(K*‖paperRadialFourier ballProfile 0‖*
          (C*(profileCap s)^2*Y^(1+ε)/(seed.absNorm:ℝ))) := by
  obtain ⟨C,hC,hzero⟩ := outer_second_zero N ε hε
  refine ⟨C,hC,?_⟩
  intro κ instκ q x a b s hι ha hm M hM hν hW hP hpool seed ξ τ t K Y hseed hK hY hcap
  apply average_bound q x τ M hM hν hW hP hpool
  · have hY0 : 0<Y := zero_lt_one.trans_le hY
    have hseedN : 0≤(seed.absNorm:ℝ) := Nat.cast_nonneg _
    positivity
  · intro y hy hw
    rw [outerZero_norm q x y s seed τ ξ t K hK]
    exact mul_le_mul_of_nonneg_left
      (hzero κ q x y a b s hι ha hm seed ξ τ t Y hseed hY hcap)
      (mul_nonneg hK (norm_nonneg _))

/-- The true original-K Fourier tail averaged over the same D family.
This directly applies the arbitrary-saving theorem, not a tail premise. -/
theorem uniform_average_tail (B ζ saving : ℝ) (hB : 0≤B) (hζ : 0<ζ) :
    ∃(control : Finset (ℕ×ℕ))(C : ℝ),0<C ∧
      ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(κ : Type u) [Fintype κ],∀q : Data κ,∀x : Frozen q,
      ∀a b : ℝ,∀s : Source (RestIndex q) a b,∀ha : 0<a,0≤b→Matches q x s ha→
      ∀M : κ→ℝ,(∀i,0≤M i)→(∀i,∀I∈q.pool i,‖q.ν i I‖≤1)→
      (∀i z,‖q.Wslot i z‖≤M i)→(∀i,0<q.P i)→
      (∀i,∀I∈q.pool i,(I.absNorm:ℝ)≤2*q.P i)→
      ∀(seed : Id)(ξ : RayCharacter)(τ : Character)(t K X T : ℝ),0<K→0<X→
      poolCap s≤Z^B→sourceNormCap s.P b s.T s.d≤X→X≤Z^B→K≤Z^B→T≤Z^B→X^2/K≤T→
      average q x τ (fun y=>‖secondDiscardedEnergy τ t (sourceColumns s)
        (outerColumn q x y seed ξ) ballProfile K T Z ζ‖)≤
        selectedMass q M*(C*(profileCap s)^2*
          control.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*Z^(-saving)) := by
  obtain ⟨control,C,hC,htail⟩ := outer_tail_arbitrary_saving B ζ saving hB hζ
  refine ⟨control,C,hC,htail.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro κ instκ q x a b s ha hb hm M hM hν hW hP hpool seed ξ τ t K X T
    hK hX hmass hcap hXc hKc hTc hscale
  have h1 : 1≤Z^B := Real.one_le_rpow hZ.1.le hB
  have hk : K/16≤Z^B := (show K/16≤K by linarith).trans hKc
  have hscale' : X^2/(16*(K/16)*(1:ℝ)^4)≤T := by
    simpa only [show 16*(K/16)*(1:ℝ)^4=K by ring] using hscale
  apply average_bound q x τ M hM hν hW hP hpool
  · have hsemi : 0≤control.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile := apply_nonneg _ _
    have hZ0 : 0<Z := zero_lt_one.trans hZ.1
    positivity
  · intro y hy hw
    rw [discarded_eq_outer_tail]
    exact hZ.2 κ q x y a b s ha hb hm seed ξ τ t (K/16) 1 X T
      (by positivity) (by norm_num) hX hmass hcap hXc hk h1 (by simpa using h1) hTc hscale'

/-- Actual fresh-D exceptional average. The count gain survives after
the selected sum as selectedVolume^(-2/3), with all old forcing intact.
Only displayed structural/norm admissions remain hypotheses. -/
theorem uniform_average_exceptional (N : ℕ)
    (saving Bcap a b ε δ Bnorm Lrad Cr εsum : ℝ)
    (hs : (2/3:ℝ)≤saving) (hs4 : saving<4/5) (hBcap : 0≤Bcap)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hδ : 0<δ) (hgap : saving+2*δ<1)
    (hBnorm : 0≤Bnorm) (hLrad : 0≤Lrad) (hCr : 0<Cr) (hεsum : 0<εsum) :
    ∃J : ℕ,∃control : Finset (ℕ×ℕ),(0,0)∈control ∧
      ∀Φ : 𝓢(ℝ,ℂ),∃Ckernel : ℝ,0≤Ckernel ∧
      ∀Q : Id,Q≠0→Q≠⊤→Q≤Ideal.span {(72:O)}→∃A Csum : ℝ,0<A ∧ 0<Csum ∧
      ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(κ : Type u) [Fintype κ],∀q : Data κ,∀x : Frozen q,
      ∀s : Source (RestIndex q) a b,Matches q x s ha→∀cover : OriginalEnclosure s,
      Fintype.card (RestIndex q)≤N→(s.Fhole.absNorm:ℝ)≤Z^Bcap→
      (∏i,2*s.P i)≤Z^Bcap→poolCap s≤Z^Bnorm→
      ∀M : κ→ℝ,(∀i,0≤M i)→(∀i,∀I∈q.pool i,‖q.ν i I‖≤1)→
      (∀i z,‖q.Wslot i z‖≤M i)→(∀i,0<q.P i)→
      (∀i,∀I∈q.pool i,q.P i≤(I.absNorm:ℝ) ∧ (I.absNorm:ℝ)≤2*q.P i)→
      ∀(seed : Id)(τ : Character)(ξ χ : RayCharacter),Squarefree seed→seed≠0→
      ∀(t K T ζ H : ℝ),0<K→0≤T→poolCap s≤H→H≤Z^Bnorm→
      frequencyRadius T Z ζ≤Cr*Z^Lrad→
      (∀y∈activeSelected q,outerFamilyConductorBudget q x y s τ (frequencyRadius T Z ζ)≤Z^Bcap)→
      average q x τ (fun y=>‖fixedPart true q x y s seed τ ξ χ Q t Φ K T Z ζ H‖/sourceVolume s)≤
        selectedMass q M*
          ((Ckernel*A*heightBase t^(2*J)*(windowMoment J)^2)*
            (sourcePrefactor s J control Q Z ε*commonPhysicalCost s K)*
            Z^(2*Bnorm*δ)*(Csum*Z^εsum/(seed.absNorm:ℝ))/(selectedVolume q)^(2/3:ℝ)) := by
  obtain ⟨J,control,h00,hkernel⟩ := uniform_fixed_outer_exceptional_part N
    saving Bcap a b ε δ Bnorm Lrad Cr εsum
    hs hs4 hBcap ha hb hε hδ hgap hBnorm hLrad hCr hεsum
  refine ⟨J,control,h00,?_⟩
  intro Φ
  obtain ⟨Ckernel,hCkernel,hq⟩ := hkernel Φ
  refine ⟨Ckernel,hCkernel,?_⟩
  intro Q hQ0 hQt hQ72
  obtain ⟨A,Csum,hA,hCsum,hbase⟩ := hq Q hQ0 hQt hQ72
  refine ⟨A,Csum,hA,hCsum,hbase.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro κ instκ q x s hm cover hι hF hPs hcap M hM hν hW hP hpool seed τ ξ χ
    hseed hseed0 t K T ζ H hK hT hpoolH hH hrad hcond
  let E := (Ckernel*A*heightBase t^(2*J)*(windowMoment J)^2)*
    (sourcePrefactor s J control Q Z ε*commonPhysicalCost s K)*
    Z^(2*Bnorm*δ)*(Csum*Z^εsum/(seed.absNorm:ℝ))
  have hE : 0≤E := by
    have hsource := sourcePrefactor_nonneg s J control Q Z ε
    have hphys := commonPhysicalCost_nonneg s K hK.le
    have ht := (heightBase_pos t).le
    have hZ0 : 0<Z := zero_lt_one.trans hZ.1
    dsimp only [E]
    positivity
  apply average_bound q x τ M hM hν hW hP (fun i I hI=>(hpool i I hI).2)
  · exact div_nonneg hE (Real.rpow_nonneg (selectedVolume_pos q hP).le _)
  · intro y hy hw
    have hbnd := hZ.2 κ q x y (Finset.mem_filter.mp hy).2.1 s hm cover hι hF hPs hcap
      seed τ ξ χ hseed hseed0 hw t K T ζ H hK hT hpoolH hH hrad (hcond y hy)
    calc
      _≤E*freshGain q y := hbnd.trans_eq (by unfold outerSavedBudget;dsimp only [E];ring)
      _≤E*(1/(selectedVolume q)^(2/3:ℝ)) :=
        mul_le_mul_of_nonneg_left (actual_fresh_gain q hP hpool y hy) hE
      _=_ := by dsimp only [E];ring

end
end Candidate.SilPrior.FourthPower.OuterFreshSelected
