/- Copyright (c) 2026 Sil. Apache-2.0.
Original-K fixed-inducing contribution with the actual selected weights.
The annular lower bound is proved ONLY on active amplitudes from support;
the canonical pool is not falsely assumed to have a global lower edge.

-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.OuterFreshSelected
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.RepairedGroupedConsumer

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.RepairedGroupedExceptional
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open ConcretePrimeRowBridge CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSectorLocalization CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentLattice
open MixedSupplierSplit MixedSupplierFourthRow MixedSupplierSource MixedSupplierPositive MixedSupplierOuterActive
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow
open MixedOriginalTail MixedInnerExceptionalBlock MixedInnerExceptionalLedger
open OuterFreshWindowPair OuterFreshAssembly OuterFreshConsumer OuterFreshCompletion OuterFreshSelected
open RepairedGroupedConsumer
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ:Type*} : DecidableEq κ := Classical.decEq _
variable {ι:Type u}[Fintype ι]{a b:ℝ}

/-- An active selected amplitude has its actual annular lower edge,
even though inactive members of the original pool may be much smaller. -/
theorem active_selected_norm_lower (q:Data ι)(hP:∀i,0<q.P i)
    (hWs:∀i,Function.support (q.Wslot i)⊆Icc (1:ℝ) 2)
    (y:Selected q)(hy:y∈activeSelected q)(j:q.J) :
    q.P j.val.val≤((y j).val.absNorm:ℝ) := by
  have hweight: selectedWeight q y≠0 := (Finset.mem_filter.mp hy).2.2
  have hamp := (Finset.prod_ne_zero_iff.mp hweight) j (Finset.mem_univ j)
  have hpool := active_selected_mem q y hy j
  simp only [amplitude,slotAmplitude,if_pos hpool] at hamp
  have hs := (hWs j.val.val (right_ne_zero_of_mul hamp)).1
  simpa only [one_mul] using (le_div_iff₀ (hP j.val.val)).mp hs

theorem active_selected_volume_lower (q:Data ι)(hP:∀i,0<q.P i)
    (hWs:∀i,Function.support (q.Wslot i)⊆Icc (1:ℝ) 2)
    (y:Selected q)(hy:y∈activeSelected q) :
    selectedVolume q≤((selectedProduct q y).absNorm:ℝ) := by
  simp only [selectedVolume,selectedProduct,map_prod,Nat.cast_prod]
  exact Finset.prod_le_prod₀ (fun j _=>(hP j.val.val).le)
    (fun j _=>active_selected_norm_lower q hP hWs y hy j)

theorem active_fresh_gain (q:Data ι)(hP:∀i,0<q.P i)
    (hWs:∀i,Function.support (q.Wslot i)⊆Icc (1:ℝ) 2)
    (y:Selected q)(hy:y∈activeSelected q) :
    freshGain q y≤1/(selectedVolume q)^(2/3:ℝ) := by
  have hv:=selectedVolume_pos q hP
  have hp:=Real.rpow_le_rpow hv.le (active_selected_volume_lower q hP hWs y hy)
    (by norm_num : (0:ℝ)≤2/3)
  exact div_le_div_of_nonneg_left zero_le_one (Real.rpow_pos_of_pos hv _) hp

/-- The grouped complex norm is bounded only here, where triangle is
legitimate. Its selected denominator is the original volume, once. -/
theorem grouped_norm_le_average (q:Data ι)(x:Frozen q)(τ:Character)
    (hP:∀i,0<q.P i)(V:ℝ)(hV:0<V)(f:Selected q→ℂ) :
    ‖selectedSum q x τ f‖/(selectedVolume q*V) ≤
      average q x τ (fun y=>‖f y‖/V) := by
  have hh:=div_le_div_of_nonneg_right (selected_norm_le q x τ f)
    (mul_nonneg (selectedVolume_pos q hP).le hV.le)
  apply hh.trans_eq
  unfold average
  simp only [←mul_div_assoc,←Finset.sum_div]
  ring

private theorem average_from_active_bound (q:Data ι)(x:Frozen q)(τ:Character)(M:ι→ℝ)
    (hM:∀i,0≤M i)(hν:∀i,∀I∈q.pool i,‖q.ν i I‖≤1)
    (hW:∀i z,‖q.Wslot i z‖≤M i)(hP:∀i,0<q.P i)
    (hpool:∀i,∀I∈q.pool i,(I.absNorm:ℝ)≤2*q.P i)
    (F:Selected q→ℝ)(E:ℝ)(hE:0≤E)
    (hF:∀y∈activeSelected q,selectedPositiveWeight q x y τ≠0→F y≤E) :
    average q x τ F≤selectedMass q M*E := by
  have hv:=selectedVolume_pos q hP
  unfold average
  apply (div_le_iff₀ hv).mpr
  calc
    _≤∑y∈activeSelected q,selectedPositiveWeight q x y τ*E := by
      apply Finset.sum_le_sum
      intro y hy
      by_cases hw:selectedPositiveWeight q x y τ=0
      · simp only [hw,zero_mul,le_refl]
      · exact mul_le_mul_of_nonneg_left (hF y hy hw) (selected_positive_nonneg q x y τ)
    _=(∑y∈activeSelected q,selectedPositiveWeight q x y τ)*E := (Finset.sum_mul _ _ _).symm
    _≤(selectedMass q M*selectedVolume q)*E :=
      mul_le_mul_of_nonneg_right (positive_mass q x τ M hM hν hW hP hpool) hE
    _=_ := by ring

/-- Actual grouped exceptional contribution at ORIGINAL K. The complete
old+fresh forcing count and original common-height summation come from the
checked fixed-part theorem. Only the active annular argument above replaces
the old overly strong all-pool lower-edge interface. No energy premise.
-/
theorem uniform_grouped_exceptional (N:ℕ)
    (saving Bcap a b ε δ Bnorm Lrad Cr εsum:ℝ)
    (hs:(2/3:ℝ)≤saving)(hs4:saving<4/5)(hBcap:0≤Bcap)
    (ha:0<a)(hb:0≤b)(hε:0<ε)(hδ:0<δ)(hgap:saving+2*δ<1)
    (hBnorm:0≤Bnorm)(hLrad:0≤Lrad)(hCr:0<Cr)(hεsum:0<εsum) :
    ∃J:ℕ,∃control:Finset (ℕ×ℕ),(0,0)∈control ∧
    ∀Φ:𝓢(ℝ,ℂ),∃Ckernel:ℝ,0≤Ckernel ∧
    ∀Q:Id,Q≠0→Q≠⊤→Q≤Ideal.span {(72:O)}→∃A Csum:ℝ,0<A ∧ 0<Csum ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀(κ:Type u)[Fintype κ],∀q:Data κ,∀x:Frozen q,
    ∀s:Source (RestIndex q) a b,Matches q x s ha→∀cover:OriginalEnclosure s,
      Fintype.card (RestIndex q)≤N→(s.Fhole.absNorm:ℝ)≤Z^Bcap→
      (∏i,2*s.P i)≤Z^Bcap→poolCap s≤Z^Bnorm→
    ∀M:κ→ℝ,(∀i,0≤M i)→(∀i,∀I∈q.pool i,‖q.ν i I‖≤1)→
      (∀i z,‖q.Wslot i z‖≤M i)→(∀i,Function.support (q.Wslot i)⊆Icc (1:ℝ) 2)→
      (∀i,0<q.P i)→(∀i,∀I∈q.pool i,(I.absNorm:ℝ)≤2*q.P i)→
    ∀(seed:Id)(τ:Character)(ξ χ:RayCharacter),Squarefree seed→seed≠0→
    ∀(t K T ζ H:ℝ),0<K→0≤T→poolCap s≤H→H≤Z^Bnorm→
      frequencyRadius T Z ζ≤Cr*Z^Lrad→
      (∀y∈activeSelected q,outerFamilyConductorBudget q x y s τ (frequencyRadius T Z ζ)≤Z^Bcap)→
      ‖selectedSum q x τ (fun y=>fixedPart true q x y s seed τ ξ χ Q t Φ K T Z ζ H)‖/
        (selectedVolume q*sourceVolume s) ≤
      selectedMass q M*
        ((Ckernel*A*heightBase t^(2*J)*(windowMoment J)^2)*
          (sourcePrefactor s J control Q Z ε*commonPhysicalCost s K)*
          Z^(2*Bnorm*δ)*(Csum*Z^εsum/(seed.absNorm:ℝ))/(selectedVolume q)^(2/3:ℝ)) := by
  obtain ⟨J,control,h00,hkernel⟩:=uniform_fixed_outer_exceptional_part N
    saving Bcap a b ε δ Bnorm Lrad Cr εsum
    hs hs4 hBcap ha hb hε hδ hgap hBnorm hLrad hCr hεsum
  refine ⟨J,control,h00,?_⟩
  intro Φ
  obtain ⟨Ckernel,hCkernel,hq⟩:=hkernel Φ
  refine ⟨Ckernel,hCkernel,?_⟩
  intro Q hQ0 hQt hQ72
  obtain ⟨A,Csum,hA,hCsum,hbase⟩:=hq Q hQ0 hQt hQ72
  refine ⟨A,Csum,hA,hCsum,hbase.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro κ instκ q x s hm cover hι hF hPs hcap M hM hν hW hWs hP hpool seed τ ξ χ
    hseed hseed0 t K T ζ H hK hT hpoolH hH hrad hcond
  let E:=(Ckernel*A*heightBase t^(2*J)*(windowMoment J)^2)*
    (sourcePrefactor s J control Q Z ε*commonPhysicalCost s K)*
    Z^(2*Bnorm*δ)*(Csum*Z^εsum/(seed.absNorm:ℝ))
  have hE:0≤E := by
    have hsource:=sourcePrefactor_nonneg s J control Q Z ε
    have hphys:=commonPhysicalCost_nonneg s K hK.le
    have ht:=(heightBase_pos t).le
    have hz:=zero_lt_one.trans hZ.1
    dsimp only [E]
    positivity
  apply (grouped_norm_le_average q x τ hP (sourceVolume s) (sourceVolume_pos s) _).trans
  apply average_from_active_bound q x τ M hM hν hW hP hpool
  · exact div_nonneg hE (Real.rpow_nonneg (selectedVolume_pos q hP).le _)
  · intro y hy hw
    have he:=hZ.2 κ q x y (Finset.mem_filter.mp hy).2.1 s hm cover hι hF hPs hcap
      seed τ ξ χ hseed hseed0 hw t K T ζ H hK hT hpoolH hH hrad (hcond y hy)
    calc
      _≤E*freshGain q y := he.trans_eq (by unfold outerSavedBudget;dsimp only [E];ring)
      _≤E*(1/(selectedVolume q)^(2/3:ℝ)) :=
        mul_le_mul_of_nonneg_left (active_fresh_gain q hP hWs y hy) hE
      _=_ := by dsimp only [E];ring

end
end Candidate.FourthPower.RepairedGroupedExceptional
