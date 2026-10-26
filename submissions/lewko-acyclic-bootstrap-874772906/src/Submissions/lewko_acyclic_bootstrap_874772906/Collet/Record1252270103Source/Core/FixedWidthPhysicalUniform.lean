/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Finite width uniformization preserves the literal physical norm and the
original anchor-before-degree quantifiers. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.FixedWidthPhysicalContract
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.GlobalInitialAssemblyCells
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.BandMonotonicity

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.FixedWidthPhysical
noncomputable section
open OAI OAI.SevenEighths QRH.Record1252270103Low
open scoped Classical BigOperators ContDiff
open Filter HeckeFamily CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyBandMonotonicity
local notation "O"=>HeckeFamily.O

/-- The grid is fixed before the original slot type and every arithmetic
anchor. Its finite choices only enlarge the fixed constants and controls. -/
theorem physical_supplier_of_finite_grid
    (B lam cap cross K mesh ξ ε δ : ℝ) (cell : ℝ→ℝ) (grid : Finset ℝ)
    (hcells : ∀s∈Set.Icc cross cap,cell s∈grid ∧ cell s-δ≤s ∧ s≤cell s)
    (hfixed : ∀b∈grid,FixedWidthMarkedPhysicalSupplier B lam cap cross K mesh ξ ε b δ) :
    Anchor.InitialMarkedPhysicalSupplier B lam cap cross K mesh ξ ε cell := by
  classical
  intro α _ _ rayM _ H hH W hW hsW bΦ hbΦ η η₀ Q hQM hQ0 hQt hQ72 R₀ hR₀
  let Grid:=↥grid
  have hb (b : Grid):=hfixed b b.property α rayM H hH W hW hsW bΦ hbΦ η
    η₀ Q hQM hQ0 hQt hQ72 R₀ hR₀
  choose degree controls C hC hbound using hb
  let d:=∑b:Grid,degree b
  let S:=Finset.univ.biUnion controls
  let Ctotal:=1+∑b:Grid,C b
  have hCtotal : 0<Ctotal := by
    have hh:=Finset.sum_nonneg (fun b (_ : b∈(Finset.univ:Finset Grid))=>(hC b).le)
    dsimp only [Ctotal]
    linarith
  refine ⟨d,S,Ctotal,hCtotal,?_⟩
  have hall : ∀ᶠZ : ℝ in atTop,∀b:Grid,_:=Filter.eventually_all.mpr hbound
  filter_upwards [hall] with Z hall
  intro hZ T θ w v t height hw hwm hheight hv p X₁ X₂ hX₁ hX₂ hadm hcross
  dsimp only
  intro hlong₁ hlong₂
  have hwcap : (∑i,w i)≤cap := by simpa [globalFace] using hadm.2.2.2.2.2.1
  obtain ⟨hcell,hlo,hhi⟩:=hcells (∑i,w i) ⟨hcross,hwcap⟩
  let b:Grid:=⟨cell (∑i,w i),hcell⟩
  have hp:=hall b hZ T θ w v t height hw hwm hheight hv p X₁ X₂ hX₁ hX₂ hadm hcross hlo hhi hlong₁ hlong₂
  have hdegree : degree b≤d :=
    Finset.single_le_sum (fun j (_ : j∈(Finset.univ:Finset Grid))=>Nat.zero_le (degree j)) (Finset.mem_univ b)
  have hcontrols : controls b⊆S := by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨b,Finset.mem_univ b,hx⟩
  have hconstant : C b≤Ctotal := by
    have hh:=Finset.single_le_sum (fun j (_ : j∈(Finset.univ:Finset Grid))=>(hC j).le) (Finset.mem_univ b)
    dsimp only [Ctotal]
    linarith
  have hcontrol:=profile_control_mono p hcontrols
  have hcontrol0:=p.control_nonneg (controls b)
  have hpower:=(pow_le_pow_right₀ (show 1≤1+|t|+height by linarith [abs_nonneg t]) hdegree)
  apply hp.trans
  gcongr

/-- Each fixed width may choose its own positive ceilings. The conclusion
retains validity for every smaller mesh and ξ; no monotonicity of physicalMass
in ξ is asserted or used. -/
theorem finite_positive_parameter_choice {P : ℝ→ℝ→ℝ→Prop} (grid : Finset ℝ)
    (h : ∀b∈grid,∃m x : ℝ,0<m ∧ 0<x ∧
      ∀mesh ξ : ℝ,0<mesh→mesh≤m→0<ξ→ξ≤x→P b mesh ξ) :
    ∃m x : ℝ,0<m ∧ 0<x ∧
      ∀mesh ξ : ℝ,0<mesh→mesh≤m→0<ξ→ξ≤x→∀b∈grid,P b mesh ξ := by
  classical
  induction grid using Finset.induction_on with
  | empty => exact ⟨1,1,by norm_num,by norm_num,by simp⟩
  | @insert a grid ha ih =>
    obtain ⟨ma,xa,hma,hxa,haP⟩:=h a (Finset.mem_insert_self _ _)
    obtain ⟨mg,xg,hmg,hxg,hgP⟩:=ih (fun b hb=>h b (Finset.mem_insert_of_mem hb))
    refine ⟨min ma mg,min xa xg,lt_min hma hmg,lt_min hxa hxg,?_⟩
    intro mesh ξ hm hm' hx hx' b hb
    rcases Finset.mem_insert.mp hb with rfl|hb
    · exact haP mesh ξ hm (hm'.trans (min_le_left _ _)) hx (hx'.trans (min_le_left _ _))
    · exact hgP mesh ξ hm (hm'.trans (min_le_right _ _)) hx (hx'.trans (min_le_right _ _)) b hb

theorem physical_supplier_of_fixed_width_ceilings
    (B lam cap cross K ε δ : ℝ) (cell : ℝ→ℝ) (grid : Finset ℝ)
    (hcells : ∀s∈Set.Icc cross cap,cell s∈grid ∧ cell s-δ≤s ∧ s≤cell s)
    (hfixed : ∀b∈grid,∃m x : ℝ,0<m ∧ 0<x ∧
      ∀mesh ξ : ℝ,0<mesh→mesh≤m→0<ξ→ξ≤x→
        FixedWidthMarkedPhysicalSupplier B lam cap cross K mesh ξ ε b δ) :
    ∃mesh ξ : ℝ,0<mesh ∧ 0<ξ ∧
      Anchor.InitialMarkedPhysicalSupplier B lam cap cross K mesh ξ ε cell := by
  obtain ⟨m,x,hm,hx,h⟩:=finite_positive_parameter_choice grid hfixed
  exact ⟨m,x,hm,hx,physical_supplier_of_finite_grid B lam cap cross K m x ε δ cell grid hcells
    (h m x hm le_rfl hx le_rfl)⟩

end
end QRH.Record1252270103Source.FixedWidthPhysical
#print axioms QRH.Record1252270103Source.FixedWidthPhysical.physical_supplier_of_finite_grid
#print axioms QRH.Record1252270103Source.FixedWidthPhysical.finite_positive_parameter_choice
#print axioms QRH.Record1252270103Source.FixedWidthPhysical.physical_supplier_of_fixed_width_ceilings
