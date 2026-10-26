/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Uniform source assembly from an earlier ordinary G and the literal marked
physical norm. The physical supplier remains the one explicit analytic leaf. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.HeightAnchorUnit
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.GlobalInitialAssemblyParentUniform
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low.HeightAnchor
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyBandMonotonicity
open QRH.Record12518109Existence QRH.Record1252270103Source QRH.Record1252270103Source.Collision
open QRH.Record1252270103Restoration

theorem physical_supplier_mono_mesh {B lam cap cross K mesh mesh' ξ ε : ℝ} {cell : ℝ→ℝ}
    (h : InitialMarkedPhysicalSupplier B lam cap cross K mesh ξ ε cell) (hm : mesh'≤mesh) :
    InitialMarkedPhysicalSupplier B lam cap cross K mesh' ξ ε cell := by
  intro α _ _ rayM _ H hH W hW hsW bΦ hbΦ η η₀ Q hQM hQ0 hQt hQ72 R₀ hR₀
  obtain ⟨degree,S,C,τ,hC,hτ,hs⟩:=h α rayM H hH W hW hsW bΦ hbΦ η
    η₀ Q hQM hQ0 hQt hQ72 R₀ hR₀
  refine ⟨degree,S,C,τ,hC,hτ,hs.mono ?_⟩
  intro Z hz hZ T θ w v t height hw hwm
  exact hz hZ T θ w v t height hw (fun i=>(hwm i).trans hm)

/-- The mesh is chosen before the ambient finite slot type. All restoration,
orientation, radial, cardinality and reference bounds are proved by the imported
source joins; no target initial energy is supplied as an assumption. -/
theorem uniform_squarefree_source_step
    (B lam cap B₀ lam₀ cap₀ cross K κ : ℝ) (cell : ℝ→ℝ)
    (hB0 : 0≤B) (hB1 : B≤1) (hB₀ : B₀≤1) (hlam : 1≤lam)
    (hL : lam≤lam₀) (hcrosscap : cross≤cap₀)
    (hcrossbudget : B-B₀+(lam₀-lam)*cross≤0)
    (hκlo : 7/10≤κ) (hκhi : κ≤3/4) (hκbeta : 2*HeckeZeroSupremum.beta-1≤κ)
    (hK : 6*κ≤K) (hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hcells : ReferenceWidthCells cross cap K cell)
    (hlow : GlobalSource B₀ lam₀ cap₀)
    (hphysical : ∀ε : ℝ,0<ε → ∃mesh ξ : ℝ,0<mesh ∧ 0<ξ ∧
      InitialMarkedPhysicalSupplier B lam cap cross K mesh ξ ε cell) :
    UniformSquarefreeUnitFaceSource B lam cap := by
  apply uniform_projected_source_lift
  intro ε hε
  obtain ⟨m₀,hm₀,h₀⟩:=hlow (ε/2) (by linarith)
  obtain ⟨mp,ξ,hmp,hξ,hp⟩:=hphysical ε hε
  let mr:=Cycle61FirstActual.comparisonMesh 1 1 (ε/2)
  have hmr : 0<mr:=Cycle61FirstActual.comparisonMesh_pos 1 1 (ε/2) (by norm_num) le_rfl (by linarith)
  let mesh:=min m₀ (min mp mr)
  have hm : 0<mesh:=lt_min hm₀ (lt_min hmp hmr)
  have hm0 : mesh≤m₀:=min_le_left _ _
  have hmp' : mesh≤mp:=(min_le_right _ _).trans (min_le_left _ _)
  have hmr' : mesh≤mr:=(min_le_right _ _).trans (min_le_right _ _)
  have hlow' : ProjectedUnitFaceSource (globalFace B₀ lam₀ cap₀) mesh ε := by
    have hh:=unit_projected_of_ordinary B₀ lam₀ cap₀ mesh (ε/2) (ε/4) hB₀
      (by linarith) (by linarith) (h₀.mono_mesh hm0)
    convert hh using 1 <;> ring
  exact ⟨mesh,hm,projected_unit_source_step B lam cap B₀ lam₀ cap₀ cross K κ mesh ξ ε cell
    hB0 hB1 hlam hξ hε hL hcrosscap hcrossbudget hκlo hκhi hκbeta hK hbeta hm.le hmr'
    hcells (physical_supplier_mono_mesh hp hmp') hlow'⟩


lemma finite_positive_height {ι : Type*} (s : Finset ι) (τ : ι→ℝ)
    (hτ : ∀i∈s,0<τ i) : ∃t : ℝ,0<t ∧ ∀i∈s,t≤τ i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | @insert a s ha ih =>
    obtain ⟨t,ht,hsmall⟩:=ih (fun i hi=>hτ i (Finset.mem_insert_of_mem hi))
    refine ⟨min (τ a) t,lt_min (hτ a (Finset.mem_insert_self _ _)) ht,?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl|hi
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hsmall i hi)

theorem fixed_width_supplier_of_fixed_subsets
    (B lam cap cross K mesh ξ ε b δ : ℝ)
    (h : FixedSubsetMarkedPhysicalSupplier B lam cap cross K mesh ξ ε b δ) :
    FixedWidthMarkedPhysicalSupplier B lam cap cross K mesh ξ ε b δ := by
  classical
  intro α _ _ rayM _ H hH W hW hsW bΦ hbΦ η η₀ Q hQM hQ0 hQt hQ72 R₀ hR₀
  have hs (T : Finset α):=h α rayM H hH W hW hsW bΦ hbΦ η
    η₀ Q hQM hQ0 hQt hQ72 R₀ hR₀ T
  choose degree controls C τ hC hτ hbound using hs
  let d:=∑T:Finset α,degree T
  let S:=Finset.univ.biUnion controls
  let Ctotal:=1+∑T:Finset α,C T
  have hCtotal : 0<Ctotal := by
    have hh:=Finset.sum_nonneg (fun T (_ : T∈(Finset.univ:Finset (Finset α)))=>(hC T).le)
    dsimp only [Ctotal]
    linarith
  obtain ⟨τ₀,hτ₀,hτmin⟩:=finite_positive_height Finset.univ τ (fun T _=>hτ T)
  refine ⟨d,S,Ctotal,τ₀,hCtotal,hτ₀,?_⟩
  have hall : ∀ᶠZ : ℝ in Filter.atTop,∀T:Finset α,_:=Filter.eventually_all.mpr hbound
  filter_upwards [hall] with Z hall
  intro hZ T θ w v t height hw hwm hheight hv hheightcap p X₁ X₂ hX₁ hX₂ hadm hcross hlo hhi
  dsimp only
  intro hlong₁ hlong₂
  have hcap : 1+|t|+height≤Z^(τ T):=hheightcap.trans
    (Real.rpow_le_rpow_of_exponent_le hZ.le (hτmin T (Finset.mem_univ T)))
  have hp:=hall T hZ θ w v t height hw hwm hheight hv hcap p X₁ X₂ hX₁ hX₂
    hadm hcross hlo hhi hlong₁ hlong₂
  have hdegree : degree T≤d :=
    Finset.single_le_sum (fun U (_ : U∈(Finset.univ:Finset (Finset α)))=>Nat.zero_le (degree U))
      (Finset.mem_univ T)
  have hcontrols : controls T⊆S := by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨T,Finset.mem_univ T,hx⟩
  have hconstant : C T≤Ctotal := by
    have hh:=Finset.single_le_sum
      (fun U (_ : U∈(Finset.univ:Finset (Finset α)))=>(hC U).le) (Finset.mem_univ T)
    dsimp only [Ctotal]
    linarith
  have hcontrol:=CenteredMomentEnergyBandMonotonicity.profile_control_mono p hcontrols
  have hcontrol0:=p.control_nonneg (controls T)
  have hpower:=(pow_le_pow_right₀ (show 1≤1+|t|+height by linarith [abs_nonneg t]) hdegree)
  apply hp.trans
  gcongr


theorem physical_supplier_of_finite_grid
    (B lam cap cross K mesh ξ ε δ : ℝ) (cell : ℝ→ℝ) (grid : Finset ℝ)
    (hcells : ∀s∈Set.Icc cross cap,cell s∈grid ∧ cell s-δ≤s ∧ s≤cell s)
    (hfixed : ∀b∈grid,FixedWidthMarkedPhysicalSupplier B lam cap cross K mesh ξ ε b δ) :
    InitialMarkedPhysicalSupplier B lam cap cross K mesh ξ ε cell := by
  classical
  intro α _ _ rayM _ H hH W hW hsW bΦ hbΦ η η₀ Q hQM hQ0 hQt hQ72 R₀ hR₀
  let Grid:=↥grid
  have hb (b : Grid):=hfixed b b.property α rayM H hH W hW hsW bΦ hbΦ η
    η₀ Q hQM hQ0 hQt hQ72 R₀ hR₀
  choose degree controls C τ hC hτ hbound using hb
  let d:=∑b:Grid,degree b
  let S:=Finset.univ.biUnion controls
  let Ctotal:=1+∑b:Grid,C b
  have hCtotal : 0<Ctotal := by
    have hh:=Finset.sum_nonneg (fun b (_ : b∈(Finset.univ:Finset Grid))=>(hC b).le)
    dsimp only [Ctotal]
    linarith
  obtain ⟨τ₀,hτ₀,hτmin⟩:=finite_positive_height Finset.univ τ (fun b _=>hτ b)
  refine ⟨d,S,Ctotal,τ₀,hCtotal,hτ₀,?_⟩
  have hall : ∀ᶠZ : ℝ in atTop,∀b:Grid,_:=Filter.eventually_all.mpr hbound
  filter_upwards [hall] with Z hall
  intro hZ T θ w v t height hw hwm hheight hv hheightcap p X₁ X₂ hX₁ hX₂ hadm hcross
  dsimp only
  intro hlong₁ hlong₂
  have hwcap : (∑i,w i)≤cap := by simpa [globalFace] using hadm.2.2.2.2.2.1
  obtain ⟨hcell,hlo,hhi⟩:=hcells (∑i,w i) ⟨hcross,hwcap⟩
  let b:Grid:=⟨cell (∑i,w i),hcell⟩
  have hcap : 1+|t|+height≤Z^(τ b):=hheightcap.trans
    (Real.rpow_le_rpow_of_exponent_le hZ.le (hτmin b (Finset.mem_univ b)))
  have hp:=hall b hZ T θ w v t height hw hwm hheight hv hcap p X₁ X₂ hX₁ hX₂ hadm hcross hlo hhi hlong₁ hlong₂
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
      InitialMarkedPhysicalSupplier B lam cap cross K mesh ξ ε cell := by
  obtain ⟨m,x,hm,hx,h⟩:=finite_positive_parameter_choice grid hfixed
  exact ⟨m,x,hm,hx,physical_supplier_of_finite_grid B lam cap cross K m x ε δ cell grid hcells
    (h m x hm le_rfl hx le_rfl)⟩

end
end QRH.Record1252270103Low.HeightAnchor
#print axioms QRH.Record1252270103Low.HeightAnchor.physical_supplier_mono_mesh
#print axioms QRH.Record1252270103Low.HeightAnchor.uniform_squarefree_source_step
#print axioms QRH.Record1252270103Low.HeightAnchor.finite_positive_height
#print axioms QRH.Record1252270103Low.HeightAnchor.fixed_width_supplier_of_fixed_subsets
#print axioms QRH.Record1252270103Low.HeightAnchor.physical_supplier_of_finite_grid
#print axioms QRH.Record1252270103Low.HeightAnchor.physical_supplier_of_fixed_width_ceilings
