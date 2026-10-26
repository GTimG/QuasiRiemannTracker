/- Copyright (c) 2026 Sil. Apache-2.0.
Actual allocation sums of the second zero mode and discarded density.
Both pieces belong to the LIVE sources produced by positive Cauchy.
Full common and artificial norms remain in their denominators.
-/
import Candidate.FourthPower.MixedFirstLiveRemainders
import Candidate.FourthPower.MixedOriginalTailPower
import Candidate.FourthPower.MixedSourceAssembly

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedFirstAllocatedRemainders
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open EisensteinSchwartzPoisson
open QRH.Record1252270103KernelMass
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentCommonProfile CenteredMomentAllocationCost
open CenteredMomentSourceLiveColumn CenteredMomentCommonRawScale
open CenteredMomentSourceSecondZeroEnergy CenteredMomentAddedZeroUniform
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedOriginalNormCap MixedOriginalTail MixedOriginalSecondZero
open MixedCommonCoefficient MixedCommonRestriction MixedCommonEnergy MixedLiveNormalization
open MixedFirstLiveSource MixedFirstLiveRemainders MixedSourceAssembly
open MixedOriginalTailPower MixedPoissonLocalization
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- Restricting the marked slots does not increase the original profile
control. The ordinary profiles and both heights are unchanged. -/
theorem live_profile_cap_le (s : Source ι a b) :
    profileCap (liveSource s)≤profileCap s := by
  have hp : (∏i : liveIndices s.B,s.M i.val)≤∏i,s.M i := by
    rw [Finset.prod_coe_sort (liveIndices s.B) s.M]
    exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
      (fun i _=>zero_le_one.trans (s.hM i)) (fun i _ _=>s.hM i)
  change 2*supControl s.W₁*supControl s.W₂*(∏i : liveIndices s.B,s.M i.val)≤
    2*supControl s.W₁*supControl s.W₂*(∏i,s.M i)
  exact mul_le_mul_of_nonneg_left hp
    (mul_nonneg (mul_nonneg (by norm_num) (supControl_nonneg s.W₁)) (supControl_nonneg s.W₂))

/-- The actual counting cap decreases after extraction: ordinary
prefixes get longer and only a subset of marked slots survives. -/
theorem live_pool_cap_le (s : Source ι a b) : poolCap (liveSource s)≤poolCap s := by
  have hnorm (I : Id) (hI : I≠0) : (1:ℝ)≤I.absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hp : 1≤plainNorm s.B :=
    one_le_mul_of_one_le_of_one_le (hnorm _ (s.hB _)) (hnorm _ (s.hB _))
  have hprefix : pairNorm s.d≤pairNorm s.prefixPair := by
    rw [Source.prefixPair,extracted_pair_norm]
    exact le_mul_of_one_le_right (pairNorm_pos s.hd.1 s.hd.2).le hp
  have hV : 0≤(128*b)^2*(s.X₁+s.Y₁)*(s.X₂+s.Y₂) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (add_nonneg
      (s.hL.trans_le s.hX₁).le (s.hL.trans_le s.hY₁).le))
      (add_nonneg (s.hL.trans_le s.hX₂).le (s.hL.trans_le s.hY₂).le)
  have hdiv := div_le_div_of_nonneg_left hV (pairNorm_pos s.hd.1 s.hd.2) hprefix
  have hprod : (∏i : liveIndices s.B,256*s.P i.val)≤∏i,256*s.P i := by
    rw [Finset.prod_coe_sort (liveIndices s.B) (fun i=>256*s.P i)]
    exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
      (fun i _=>mul_nonneg (by norm_num) (zero_le_one.trans (s.hP i)))
      (fun i _ _=>by linarith [s.hP i])
  change (128*b)^2*(s.X₁+s.Y₁)*(s.X₂+s.Y₂)/pairNorm s.prefixPair*
      (∏i : liveIndices s.B,256*s.P i.val)≤
    (128*b)^2*(s.X₁+s.Y₁)*(s.X₂+s.Y₂)/pairNorm s.d*(∏i,256*s.P i)
  exact mul_le_mul hdiv hprod
    (Finset.prod_nonneg (fun i _=>mul_nonneg (by norm_num) (zero_le_one.trans (s.hP i.val))))
    (div_nonneg hV (pairNorm_pos s.hd.1 s.hd.2).le)

theorem frozen_scalar_bound (s : Source ι a b) (G : Id)
    (B : actualAllocations (tuplePools s) G) :
    ‖frozenWeight (punctureProduct s.S s.H) B.val*
      frozenCoefficient B.val G s.R s.ν s.Wslot s.P‖≤∏i,s.M i :=
  (frozen_scalar_norm_le _ _ _).trans
    (frozenCoefficient_norm B.val G s.R s.ν s.Wslot s.P s.M s.hν s.hWnorm s.hM)

/-- The actual positive-Cauchy allocation weight, shared by the four
pieces. F is merely the displayed finite summand, not a source estimate. -/
def allocationSum (s : Source ι a b) (G : Id)
    (F : actualAllocations (tuplePools s) G→ℝ) : ℝ :=
  ((actualAllocations (tuplePools s) G).card:ℝ)*
    ∑B : actualAllocations (tuplePools s) G,
      ‖frozenWeight (punctureProduct s.S s.H) B.val*
        frozenCoefficient B.val G s.R s.ν s.Wslot s.P‖^2*F B

private theorem allocation_sum_bound (s : Source ι a b) (G : Id)
    (F : actualAllocations (tuplePools s) G→ℝ) (H : ℝ) (hH : 0≤H)
    (hF : ∀B,frozenCoefficient B.val G s.R s.ν s.Wslot s.P≠0→F B≤H) :
    allocationSum s G F≤((actualAllocations (tuplePools s) G).card:ℝ)^2*(∏i,s.M i)^2*H := by
  have ht (B : actualAllocations (tuplePools s) G) :
      ‖frozenWeight (punctureProduct s.S s.H) B.val*
        frozenCoefficient B.val G s.R s.ν s.Wslot s.P‖^2*F B≤(∏i,s.M i)^2*H := by
    by_cases hf : frozenCoefficient B.val G s.R s.ν s.Wslot s.P=0
    · simp only [hf,mul_zero,norm_zero,zero_pow (by decide : 2≠0),zero_mul]
      exact mul_nonneg (sq_nonneg _) hH
    · exact (mul_le_mul_of_nonneg_left (hF B hf) (sq_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _)
          (frozen_scalar_bound s G B) 2) hH)
  calc
    _≤((actualAllocations (tuplePools s) G).card:ℝ)*
        ∑_B : actualAllocations (tuplePools s) G,(∏i,s.M i)^2*H :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun B _=>ht B)) (Nat.cast_nonneg _)
    _=_ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
      ring

def allocatedZero (s : Source ι a b) (ha : 0<a) (hb : 0≤b) (cover : OriginalEnclosure s)
    (G D : Id) (τ : Character) (t K W : ℝ) : ℝ :=
  allocationSum s G (fun B=>
    let live := allocatedLiveSource s hb cover G B
    ‖zeroDensity Finset.univ (sourceGenerator (sourceColumns live))
      (sourceGenerator_supported (sourceColumns live))
      (fun I : supportedColumns (sourceColumns live)=>sourceCoefficient live ha D I*heightCoeff τ t I)
      K W‖)

def allocatedDiscarded (s : Source ι a b) (ha : 0<a) (hb : 0≤b) (cover : OriginalEnclosure s)
    (G D : Id) (τ : Character) (t K W Tsec Z ξ : ℝ) : ℝ :=
  allocationSum s G (fun B=>
    let live := allocatedLiveSource s hb cover G B
    ‖localizedDensity Finset.univ (sourceGenerator (sourceColumns live))
      (sourceGenerator_supported (sourceColumns live))
      (fun I : supportedColumns (sourceColumns live)=>sourceCoefficient live ha D I*heightCoeff τ t I)
      K W (discardedWeight (frequencyRadius Tsec Z ξ))‖)

/-- The full allocation sum of ACTUAL live zero densities. Constants
precede profiles, heights, common ideals and all allocation choices. -/
theorem uniform_allocated_zero (N : ℕ) (ε δ : ℝ) (hε : 0<ε) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀(ι : Type u) [Fintype ι],∀a b : ℝ,∀s : Source ι a b,
      Fintype.card ι≤N→∀ha : 0<a,∀hb : 0≤b,∀cover : OriginalEnclosure s,
      ∀G D : Id,G≠0→D≠0→∀(τ : Character)(t Y K W : ℝ),1≤Y→
      (2:ℝ)^Fintype.card ι*sourceNormCap s.P b s.T s.d≤Y→0≤K→0≤W→
      allocatedZero s ha hb cover G D τ t K W≤
        (16*K*W^3)*‖paperRadialFourier ballProfile 0‖*
          (C*(G.absNorm:ℝ)^δ*(∏i,s.M i)^2*(profileCap s)^2*Y^(1+ε)/
            ((G.absNorm:ℝ)*(D.absNorm:ℝ))) := by
  obtain ⟨C0,hC0,hzero⟩ := allocated_second_zero N ε hε
  obtain ⟨Cc,hCc,hcount⟩ := genuine_count_squared (N+2) δ hδ
  refine ⟨Cc*C0,mul_pos hCc hC0,?_⟩
  intro ι instι a b s hι ha hb cover G D hG hD τ t Y K W hY hcap hK hW
  let H := (16*K*W^3)*‖paperRadialFourier ballProfile 0‖*
    (C0*(profileCap s)^2*Y^(1+ε)/((G.absNorm:ℝ)*(D.absNorm:ℝ)))
  have hY0 : 0<Y := zero_lt_one.trans_le hY
  have hH : 0≤H := by dsimp only [H];positivity
  have hh := allocation_sum_bound s G
    (fun B=>let live := allocatedLiveSource s hb cover G B
      ‖zeroDensity Finset.univ (sourceGenerator (sourceColumns live))
        (sourceGenerator_supported (sourceColumns live))
        (fun I : supportedColumns (sourceColumns live)=>sourceCoefficient live ha D I*heightCoeff τ t I)
        K W‖) H hH (by
      intro B hf
      let live := allocatedLiveSource s hb cover G B
      have hz := hzero ι a b s hι ha hb cover G D hG hD B hf τ t Y hY hcap
      have hp : profileCap live≤profileCap s :=
        live_profile_cap_le (allocationSource s hb cover G B)
      have hp2 := pow_le_pow_left₀ (profileCap_nonneg live) hp 2
      have hzero' : ‖sourceSecondZero (sourceColumns live) (sourceCoefficient live ha D) τ t‖≤
          C0*(profileCap s)^2*Y^(1+ε)/((G.absNorm:ℝ)*(D.absNorm:ℝ)) := by
        apply hz.trans
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp2 hC0.le)
            (Real.rpow_nonneg hY0.le _)) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      change ‖((16*K*W^3:ℝ):ℂ)*paperRadialFourier ballProfile 0*
        sourceSecondZero (sourceColumns live) (sourceCoefficient live ha D) τ t‖≤H
      rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity : 0≤16*K*W^3)]
      exact mul_le_mul_of_nonneg_left hzero' (by positivity))
  have hdim : Fintype.card (ι⊕Fin 2)≤N+2 := by
    simpa only [Fintype.card_sum,Fintype.card_fin] using Nat.add_le_add_right hι 2
  have hc := hcount hdim (tuplePools s) G hG
  calc
    _≤((actualAllocations (tuplePools s) G).card:ℝ)^2*(∏i,s.M i)^2*H := hh
    _≤(Cc*(G.absNorm:ℝ)^δ)*(∏i,s.M i)^2*H :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (sq_nonneg _)) hH
    _=_ := by dsimp only [H];ring

/-- Extra arbitrary-power decay pays BOTH full norms. No radical cap
or cancellation inside a row is used. -/
theorem pay_full_norms (Z B saving : ℝ) (hZ : 0<Z) (G D : Id)
    (hG : G≠0) (hD : D≠0) (hGc : (G.absNorm:ℝ)≤Z^B) (hDc : (D.absNorm:ℝ)≤Z^B) :
    Z^(-(saving+2*B))≤Z^(-saving)/((G.absNorm:ℝ)*(D.absNorm:ℝ)) := by
  have hg : 0<(G.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hG)
  have hd : 0<(D.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  apply (le_div_iff₀ (mul_pos hg hd)).mpr
  calc
    _≤Z^(-(saving+2*B))*(Z^B*Z^B) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hGc hDc hd.le (Real.rpow_nonneg hZ.le _)) (Real.rpow_nonneg hZ.le _)
    _=Z^(-saving) := by
      rw [←Real.rpow_add hZ,←Real.rpow_add hZ]
      congr 1
      ring

/-- The literal discarded-density allocation sum. Only structural
polynomial caps are hypotheses; the decay estimate is supplied by the
checked original-tail theorem at saving+2B before any live source. -/
theorem uniform_allocated_discarded (N : ℕ) (B ξ saving δ : ℝ)
    (hB : 0≤B) (hξ : 0<ξ) (hδ : 0<δ) :
    ∃(control : Finset (ℕ×ℕ))(C : ℝ),0<C ∧
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(ι : Type u) [Fintype ι],∀a b : ℝ,∀s : Source ι a b,Fintype.card ι≤N→
    ∀ha : 0<a,∀hb : 0≤b,∀cover : OriginalEnclosure s,∀G D : Id,G≠0→D≠0→
      (G.absNorm:ℝ)≤Z^B→(D.absNorm:ℝ)≤Z^B→
    ∀(τ : Character)(t K W X Tsec : ℝ),0<K→0<W→0<X→
      poolCap s≤Z^B→(2:ℝ)^Fintype.card ι*sourceNormCap s.P b s.T s.d≤X→
      X≤Z^B→K≤Z^B→W≤Z^B→W⁻¹≤Z^B→Tsec≤Z^B→X^2/(16*K*W^4)≤Tsec→
    allocatedDiscarded s ha hb cover G D τ t K W Tsec Z ξ≤
      C*(G.absNorm:ℝ)^δ*(∏i,s.M i)^2*(profileCap s)^2*
        control.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*Z^(-saving)/
          ((G.absNorm:ℝ)*(D.absNorm:ℝ)) := by
  obtain ⟨control,Ct,hCt,htail⟩ := original_tail_arbitrary_saving B ξ (saving+2*B) hB hξ
  obtain ⟨Cc,hCc,hcount⟩ := genuine_count_squared (N+2) δ hδ
  refine ⟨control,Cc*Ct,mul_pos hCc hCt,?_⟩
  filter_upwards [htail] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι instι a b s hι ha hb cover G D hG hD hGc hDc τ t K W X Tsec
    hK hW hX hpool hcap hXc hKc hWc hWic hTc hscale
  have hZ0 : 0<Z := zero_lt_one.trans hZ.1
  have hg : 0<(G.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hG)
  have hg1 : 1≤(G.absNorm:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hG)
  have hcprof : 0≤control.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile := apply_nonneg _ _
  let H := Ct*(profileCap s)^2*control.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*
    Z^(-saving)/((G.absNorm:ℝ)*(D.absNorm:ℝ))
  have hH : 0≤H := by dsimp only [H];positivity
  have hh := allocation_sum_bound s G
    (fun A=>let live := allocatedLiveSource s hb cover G A
      ‖localizedDensity Finset.univ (sourceGenerator (sourceColumns live))
        (sourceGenerator_supported (sourceColumns live))
        (fun I : supportedColumns (sourceColumns live)=>sourceCoefficient live ha D I*heightCoeff τ t I)
        K W (discardedWeight (frequencyRadius Tsec Z ξ))‖) H hH (by
      intro A hf
      let live := allocatedLiveSource s hb cover G A
      have hp : poolCap live≤Z^B :=
        (live_pool_cap_le (allocationSource s hb cover G A)).trans hpool
      have hsize : sourceNormCap live.P b live.T live.d≤X := by
        calc
          _≤(2:ℝ)^Fintype.card ι*sourceNormCap s.P b s.T s.d/(G.absNorm:ℝ) :=
            allocated_cap_shortening s hb cover G hG A hf
          _≤X/(G.absNorm:ℝ) := div_le_div_of_nonneg_right hcap hg.le
          _≤X := div_le_self hX.le hg1
      have ht := hZ.2 (liveIndices A.val) a b live ha hb D τ t K W X Tsec
        hK hW hX hp hsize hXc hKc hWc hWic hTc hscale
      have hprof : profileCap live≤profileCap s :=
        live_profile_cap_le (allocationSource s hb cover G A)
      have hp2 := pow_le_pow_left₀ (profileCap_nonneg live) hprof 2
      have hfactor : 0≤Ct*(profileCap s)^2*
          control.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile :=
        mul_nonneg (mul_nonneg hCt.le (sq_nonneg _)) hcprof
      apply ht.trans
      calc
        _≤Ct*(profileCap s)^2*control.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile*
            Z^(-(saving+2*B)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp2 hCt.le) hcprof)
            (Real.rpow_nonneg hZ0.le _)
        _≤(Ct*(profileCap s)^2*control.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile)*
            (Z^(-saving)/((G.absNorm:ℝ)*(D.absNorm:ℝ))) :=
          mul_le_mul_of_nonneg_left (pay_full_norms Z B saving hZ0 G D hG hD hGc hDc) hfactor
        _=H := by dsimp only [H];ring)
  have hdim : Fintype.card (ι⊕Fin 2)≤N+2 := by
    simpa only [Fintype.card_sum,Fintype.card_fin] using Nat.add_le_add_right hι 2
  have hc := hcount hdim (tuplePools s) G hG
  calc
    _≤((actualAllocations (tuplePools s) G).card:ℝ)^2*(∏i,s.M i)^2*H := hh
    _≤(Cc*(G.absNorm:ℝ)^δ)*(∏i,s.M i)^2*H :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (sq_nonneg _)) hH
    _=_ := by dsimp only [H];ring

end
end Candidate.FourthPower.MixedFirstAllocatedRemainders
