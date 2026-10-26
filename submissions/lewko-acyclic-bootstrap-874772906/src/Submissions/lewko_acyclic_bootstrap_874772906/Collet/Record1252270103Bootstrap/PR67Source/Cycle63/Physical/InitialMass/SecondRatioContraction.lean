import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondEffectiveScalar
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open CenteredMomentSectorLocalization

def secondRatioIndex (s : SecondBlockSource) : ℤ :=
  s.dyad 0+s.dyad 1-s.dyad 2-s.dyad 3

lemma actual_second_ratio_index (s : SecondBlockSource) :
    s.ratio=dyadicScale (secondRatioIndex s) := by
  simp only [SecondBlockSource.ratio,secondRatioIndex,dyadicScale,
    zpow_sub₀ (by norm_num : (2:ℝ)≠0),zpow_add₀ (by norm_num : (2:ℝ)≠0)]
  ring

def secondRatioBins {Label : Type*}[Fintype Label] (s : Label→SecondBlockSource) : Finset ℤ :=
  Finset.univ.image (fun l=>secondRatioIndex (s l))

abbrev SecondRatioFiber {Label : Type*} (s : Label→SecondBlockSource)(r : ℤ) :=
  {l : Label // secondRatioIndex (s l)=r}

/-- Group the original weighted sum without taking absolute values of
individual first or second labels. -/
theorem actual_second_ratio_sum {Label : Type*}[Fintype Label]
    (s : Label→SecondBlockSource)(w : Label→ℂ)(W : 𝓢(ℝ,ℂ)) :
    (∑l,w l*(s l).value W)=∑r∈secondRatioBins s,
      ∑l : SecondRatioFiber s r,w l.val*(s l.val).value W := by
  classical
  rw [←Finset.sum_fiberwise_of_maps_to
    (fun l (hl : l∈(Finset.univ : Finset Label))=>
      Finset.mem_image_of_mem (fun l=>secondRatioIndex (s l)) hl)]
  refine Finset.sum_congr rfl fun r hr => ?_
  exact (Finset.sum_subtype (Finset.univ.filter (fun l=>secondRatioIndex (s l)=r))
    (fun l=>by simp) (fun l=>w l*(s l).value W))

/-- Apply the whole-kernel contraction to exact ratio fibers. Original
weights remain inside the joint balanced energy on every fiber. -/
theorem actual_second_ratio_contraction (W : 𝓢(ℝ,ℂ))(A J : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀{Label : Type*}[Fintype Label]
      (s : Label→SecondBlockSource)(w : Label→ℂ)(E : ℤ→ℝ),
      (∀r∈secondRatioBins s,0≤E r) →
      (∀r∈secondRatioBins s,∀t : ℝ,
        let src:=fun l : SecondRatioFiber s r=>s l.val
        let weight:=fun l : SecondRatioFiber s r=>w l.val
        secondBalancedEnergyPair src (secondEffectiveWeight src weight W)
          (secondGeometricBalance src (secondEffectiveWeight src weight W)) t≤E r*(1+‖t‖)^J) →
      ‖∑l,w l*(s l).value W‖≤C*∑r∈secondRatioBins s,E r/(1+dyadicScale r)^A := by
  classical
  obtain ⟨C,hC,hbound⟩:=actual_second_effective_contraction W A J
  refine ⟨C,hC,?_⟩
  intro Label _ s w E hE he
  rw [actual_second_ratio_sum]
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun r hr => ?_
  have hd : 0<dyadicScale r := by unfold dyadicScale; positivity
  have hh:=hbound (fun l : SecondRatioFiber s r=>s l.val)
    (fun l : SecondRatioFiber s r=>w l.val) (dyadicScale r) hd
    (fun l=>by rw [actual_second_ratio_index,l.property]) (E r) (hE r hr) (he r hr)
  have hpos : 0<(1+dyadicScale r)^A := by positivity
  rw [←mul_div_assoc]
  apply (le_div_iff₀ hpos).mpr
  calc
    _=(1+dyadicScale r)^A*‖∑l : SecondRatioFiber s r,w l.val*(s l.val).value W‖ := mul_comm _ _
    _≤C*E r := hh

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
