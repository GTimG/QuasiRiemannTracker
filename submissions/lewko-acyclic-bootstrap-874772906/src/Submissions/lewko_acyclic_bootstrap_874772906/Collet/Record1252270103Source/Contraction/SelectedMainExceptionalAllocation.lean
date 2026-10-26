/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Adapted for the actual MAIN frozen-one constructor from the retained LOW cap/aggregate chain.
Inherited upstream notices remain required.
Actual full-pool and raw-corner support for exceptional first children. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.SelectedExceptionalInitialCapsSupport
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Pool.FixedCell
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.InitialRegularToTruncatedFamily
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Contraction.SelectedMainExceptional
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentSourceLiveColumn CenteredMomentFirstSectors CenteredMomentSecondSectorColumns
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentSectorLocalization CenteredMomentSupport
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceRow
open Cycle61InitialMass Record1252270103Second OAI.SevenEighths.Record1252270103Source
open QRH.Record1252270103Low InitialPhysical InitialTruncated
open Low.SelectedExceptionalNormalized ForcedCost Pool
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq ι:=Classical.decEq _
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _


/-- All nested exceptional allocation caps follow from the actual first
allocation, parent polynomial bounds and the one fixed-cell prime pool. -/
theorem first_child_allocation_caps {ι:Type*}[Fintype ι]
    (s:Input ι)(C R:Ideal O)(hC:C≠0)(hR:R≠0)(alloc:actualAllocations s.pools C)
    (τ:Character)(t:ℝ)(W₁ W₂:𝓢(ℝ,ℂ))(b Z a ell mesh loss Bsource:ℝ)(depth:ℕ)
    (hZ:1<Z)(hb:0≤b)(hCcap:(C.absNorm:ℝ)≤Z^(2:ℝ))(hRcap:(R.absNorm:ℝ)≤Z)
    (hW₁:s.W₁=(W₁:ℝ→ℂ))(hW₂:s.W₂=(W₂:ℝ→ℂ))(hb₁:s.b₁≤b)(hb₂:s.b₂≤b)
    (hplain:b^2*(s.X₁*s.X₂)≤Z^(2:ℝ))
    (P:Finset (Ideal O))(hpool:FixedCellPoolData P Z a ell mesh loss 12 Bsource depth)
    (hdepth:(2:ℝ)/ell≤depth)(havoid:∀p∈P,∀i I,I∈s.slots i→¬p∣I)
    (X L:Ideal O)(hX:X≠0)(hXcap:(X.absNorm:ℝ)≤Z^(2:ℝ))
    (hL:Squarefree L)(hLcap:(L.absNorm:ℝ)≤Z^(4:ℝ))
    (B:actualAllocations (child s C R alloc τ t).pools X):
    CorrectedAllocatedCaps (child s C R alloc τ t) X (R*C) B W₁ W₂ b Z 12 a 2 12 13 ell depth
      (alloc.val (Sum.inr 0)) (alloc.val (Sum.inr 1)) 1 (Collision.markedProduct alloc.val) L P := by
  have hZ0:=zero_lt_one.trans hZ
  have hA:((alloc.val (Sum.inr 0)*alloc.val (Sum.inr 1)).absNorm:ℝ)≤Z^(2:ℝ):=by
    have hd:=plain_product_dvd_tuple alloc.val
    have he:finiteTupleProduct alloc.val=C:=(Finset.mem_filter.mp alloc.property).2
    rw [he] at hd
    exact (corrected_norm_mono_of_dvd _ C hC hd).trans hCcap
  have hRC:((R*C).absNorm:ℝ)≤Z^(3:ℝ):=by
    have hh:=corrected_norm_mul_cap R C Z 1 2 hZ0 (by simpa using hRcap) hCcap
    norm_num at hh ⊢
    exact hh
  have hplainChild:b^2*((child s C R alloc τ t).X₁*(child s C R alloc τ t).X₂)≤Z^(2:ℝ):=by
    have hx₁:(child s C R alloc τ t).X₁≤s.X₁:=div_le_self s.X₁_pos.le (alloc_norm_ge_one s C alloc _)
    have hx₂:(child s C R alloc τ t).X₂≤s.X₂:=div_le_self s.X₂_pos.le (alloc_norm_ge_one s C alloc _)
    exact (mul_le_mul_of_nonneg_left
      (mul_le_mul hx₁ hx₂ (child s C R alloc τ t).X₂_pos.le s.X₁_pos.le) (sq_nonneg b)).trans hplain
  have hh:=corrected_allocated_caps_of_original (child s C R alloc τ t) X (R*C) hX B W₁ W₂
    b Z 2 2 3 2 4 a 2 ell depth (alloc.val (Sum.inr 0)) (alloc.val (Sum.inr 1)) 1
    (Collision.markedProduct alloc.val) L P hb hZ hL hW₁ hW₂ hb₁ hb₂
    (mul_ne_zero hR hC) (alloc_ne s C alloc _) (alloc_ne s C alloc _) (one_dvd _)
    hA (by simpa using (Real.one_le_rpow hZ.le (by norm_num : (0:ℝ)≤2))) hRC hXcap hLcap (Finset.card_pos.mpr hpool.nonempty) hpool.prime
    (fun p hp=>by exact_mod_cast hpool.norm_ge_sixteen p hp) hpool.norm_lower hpool.norm_upper
    (fun p hp i I hI=>havoid p hp i.val I hI)
    (by norm_num; exact hpool.card_newton) hdepth hplainChild
  norm_num at hh
  exact hh


end
end QRH.Record1252270103Source.Contraction.SelectedMainExceptional
#print axioms QRH.Record1252270103Source.Contraction.SelectedMainExceptional.first_child_allocation_caps
