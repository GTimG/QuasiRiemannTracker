/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
All finite source quantifiers around the literal first physical norm. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.HeightAnchorLong
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.GlobalInitialAssemblyShort
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.GlobalInitialAssemblyCanonical
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.GlobalInitialAssemblyPromotion
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low.HeightAnchor
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CenteredMomentFiniteProfileExceptional CenteredMomentEnergyBands
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
open CenteredMomentDetectorEnergyInitialState QuadraticInitialBound CenteredMomentPrimeSlot
open QRH.Record1252270103Source QRH.Record1252270103Source.Collision
local notation "O"=>HeckeFamily.O

theorem projected_unit_source_step
    (B lam cap B₀ lam₀ cap₀ cross K κ mesh ξ ε : ℝ) (cell : ℝ→ℝ)
    (hB0 : 0≤B) (hB1 : B≤1) (hlam : 1≤lam) (hξ : 0<ξ) (hε : 0<ε)
    (hL : lam≤lam₀) (hcrosscap : cross≤cap₀)
    (hcrossbudget : B-B₀+(lam₀-lam)*cross≤0)
    (hκlo : 7/10≤κ) (hκhi : κ≤3/4) (hκbeta : 2*HeckeZeroSupremum.beta-1≤κ)
    (hK : 6*κ≤K) (hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hm0 : 0≤mesh)
    (hmesh : mesh≤Cycle61FirstActual.comparisonMesh 1 1 (ε/2))
    (hcells : ReferenceWidthCells cross cap K cell)
    (hphysical : InitialMarkedPhysicalSupplier B lam cap cross K mesh ξ ε cell)
    (hlow : ProjectedUnitFaceSource (globalFace B₀ lam₀ cap₀) mesh ε) :
    ProjectedUnitFaceSource (globalFace B lam cap) mesh ε := by
  intro α _ _ rayM _ H hH W hW hsW bΦ hbΦ η η₀ Q hQM hQ0 hQt hQ72 R₀ hR₀
  obtain ⟨dl,Sl,Cl,hCl,hl⟩:=uniform_initial_marked_long B lam cap cross K κ mesh ξ ε cell
    hB0 hB1 hlam hξ hε hκlo hκhi hκbeta hK hbeta hm0 hmesh hcells hphysical
    α rayM H hH W hW hsW bΦ hbΦ η η₀ Q hQM hQ0 hQt hQ72 R₀ hR₀
  obtain ⟨ds,Ss,hs⟩:=uniform_initial_marked_short B lam cap cross K κ mesh ε cell
    hB1 (by linarith) hε hκlo hκhi hκbeta hK hbeta hmesh hcells
    α rayM H hH W hW hsW bΦ hbΦ η
  obtain ⟨Cs,hCs,hs⟩:=hs η₀ Q hQM hQ0 hQt hQ72 R₀ hR₀
  obtain ⟨dp,Sp,Cp,hCp,hp⟩:=hlow α rayM H hH W hW hsW bΦ hbΦ η η₀ Q hQM hQ0 hQt hQ72 R₀ hR₀
  let d:=dl+ds+dp
  let S:=Sl∪Ss∪Sp
  let C:=Cl*2^dl+Cs*2^ds+Cp*2^dp+1
  have hCl0 : 0≤Cl*2^dl:=by positivity
  have hCs0 : 0≤Cs*2^ds:=by positivity
  have hCp0 : 0≤Cp*2^dp:=by positivity
  have hC : 0<C:=by dsimp [C];linarith
  have hcl : Cl*2^dl≤C:=by dsimp [C];linarith
  have hcs : Cs*2^ds≤C:=by dsimp [C];linarith
  have hcp : Cp*2^dp≤C:=by dsimp [C];linarith
  have hSl : Sl⊆S:=fun _ h=>Finset.mem_union_left _ (Finset.mem_union_left _ h)
  have hSs : Ss⊆S:=fun _ h=>Finset.mem_union_left _ (Finset.mem_union_right _ h)
  have hSp : Sp⊆S:=fun _ h=>Finset.mem_union_right _ h
  refine ⟨d,S,C,hC,?_⟩
  filter_upwards [hl,hs,hp,eventually_gt_atTop (1:ℝ)] with Z hl hs hp hZ
  apply canonical_marked_projected rayM H hH B lam cap (by linarith) W hW hsW bΦ mesh ε Z hZ
    η η₀ Q R₀ d S C
  intro hZ' T θ w v t height hw hwm hh hv p X₁ X₂ hX₁ hX₂ hadm rows Φ hsΦ hΦ
  by_cases hwidth : (∑i,w i)≤cross
  · have hface:=inherit_lower_width (show 0≤lam by linarith) hL hcrosscap hcrossbudget
      (length_nonneg Z X₁ hZ') (length_nonneg Z X₂ hZ') (Finset.sum_nonneg (fun i _=>hw i)) hwidth hadm
    have hparent:=hp T θ w (fun _=>33/50) v t height hw hwm (fun _=>le_rfl) (fun _=>le_rfl)
      hh hv 1 le_rfl le_rfl Φ hsΦ hΦ p X₁ X₂ hX₁ hX₂ hface
    simp only [Real.rpow_one] at hparent
    let s:=initialInput rayM H hH W hW hsW Z (zero_lt_one.trans hZ') η η₀ R₀ θ w v t
      p (by norm_num) X₁ X₂ X₁ X₂ hX₁ hX₂ hX₁ hX₂ rfl
    let atoms:=Finset.univ.biUnion s.slots
    have hSlots (i : T) : s.slots i⊆atoms:=fun I hI=>Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hI⟩
    have hPrime : ∀I∈atoms,Prime I := by
      intro I hI
      obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hI
      exact (Finset.mem_filter.mp hi).2.1
    have hbound:=markedFiniteEnergy_le_projected s R₀ 1 (9/4) X₁ X₂ hX₁ hX₂ rows
      (initialKeep η (internalQ Q η₀)) Φ Z hΦ atoms hSlots hPrime
      (Cp*diagonalControl Φ*(p.control Sp)^2*(1+|t|+height)^dp*Z^(1+ε)) (hparent rows)
    exact hbound.trans (source_control_promote_standard p Φ Sp S hSp dp d (by dsimp [d];omega)
      Cp C t height Z (1+ε) hCp.le hcp hh (zero_lt_one.trans hZ').le)
  · have hcross : cross≤∑i,w i:=le_of_lt (lt_of_not_ge hwidth)
    by_cases hshort : min X₁ X₂≤Z^(49/100-K*cell (∑i,w i))
    · have hbound:=hs hZ' T θ w v t height hw hwm hh hv p X₁ X₂ hX₁ hX₂ hadm hcross hshort
        X₁ X₂ hX₁ hX₂ rfl rows Φ hsΦ hΦ
      exact hbound.trans (source_control_promote_standard p Φ Ss S hSs ds d (by dsimp [d];omega)
        Cs C t height Z (1+ε) hCs.le hcs hh (zero_lt_one.trans hZ').le)
    · have hmin : Z^(49/100-K*cell (∑i,w i))<min X₁ X₂:=lt_of_not_ge hshort
      have hbound:=hl hZ' T θ w v t height hw hwm hh hv p X₁ X₂ hX₁ hX₂ hadm hcross
        (hmin.le.trans (min_le_left _ _)) (hmin.le.trans (min_le_right _ _)) rows Φ hsΦ hΦ
      exact hbound.trans (source_control_promote_standard p Φ Sl S hSl dl d (by dsimp [d];omega)
        Cl C t height Z (1+ε) hCl.le hcl hh (zero_lt_one.trans hZ').le)

end
end QRH.Record1252270103Low.HeightAnchor
#print axioms QRH.Record1252270103Low.HeightAnchor.projected_unit_source_step
