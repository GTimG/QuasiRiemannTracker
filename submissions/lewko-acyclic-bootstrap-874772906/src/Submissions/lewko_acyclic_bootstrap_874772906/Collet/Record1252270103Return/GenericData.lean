/- Adapted from the accepted Cycle63/Cycle25 geometry-free detector carrier.
Original OpenAI, Hailey Collet and DaysSky attributions retained. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Return.Geometry
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Assembly.Count.Data
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle25.Assembly.SourceData
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle25.Assembly.MomentData
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle25.Assembly.Mesh
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.ParametersSlotLengths

namespace QRH.Record1252270103Return.GenericPhysical
noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters]
set_option autoImplicit false
open scoped Classical BigOperators ContDiff
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily OAI.SevenEighths.HeckeInverseAmplification OAI.SevenEighths.ProbePhysical Geometry

/-- Actual small prime-slot lengths at the new rational total. All scalar
parameters are fixed before the live character, row height and amplitude class. -/
structure DetectorData where
  N : ℕ
  length : Fin N→ℝ
  t : ℝ
  ε : ℝ
  e : ℝ
  witnessKappa : ℝ
  cost : ℝ
  momentKappa : ℝ
  t_pos : 0<t
  t_le : t≤1/100
  epsilon_pos : 0<ε
  epsilon_small : ε≤1/100000
  epsilon_count_small : ε≤1/10000000
  e_pos : 0<e
  e_small : e<1/1000
  witnessKappa_pos : 0<witnessKappa
  witnessKappa_small : witnessKappa≤1
  cost_pos : 0<cost
  momentKappa_lo : 7/10≤momentKappa
  momentKappa_hi : momentKappa≤3/4
  slots_pos : ∀j,0<length j
  slots_small : ∀j,length j≤(1/200)*t
  slots_sum : ∑j,length j=Geometry.ell
  detector_budget : 12*e*((22:ℝ)+2)+8*witnessKappa+2*cost≤ε/2

abbrev SourceData := Cycle61DetectorCount.SourceData

/-- Smallness and distinctness used by the original physical prime dictionary. -/
structure BaselineData extends DetectorData where
  t_small : t≤1/100000000
  slots_injective : Function.Injective length

def BaselineData.toMomentData (D : BaselineData) : Cycle25.Weighted.MomentData where
  N:=D.N
  ell:=D.length
  t:=D.t
  ε:=D.ε
  e:=D.e
  t_pos:=D.t_pos
  t_small:=D.t_small
  slots_injective:=D.slots_injective
  slots_bounds:=fun j=>⟨D.slots_pos j,by linarith [D.slots_small j,D.t_small]⟩
  epsilon_pos:=D.epsilon_pos
  epsilon_small:=D.epsilon_small.trans (by norm_num)
  e_pos:=D.e_pos

/-- Rescale a distinct prime-slot partition to the exact new rational total. -/
theorem exists_distinct_fine_slots {cap : ℝ} (hc : 0<cap) :
    ∃N:ℕ,∃length:Fin N→ℝ,Function.Injective length ∧
      (∀j,0<length j ∧ length j≤cap) ∧ ∑j,length j=Geometry.ell := by
  have he : 0 < ell := Geometry.ell_pos
  obtain ⟨N,hN,old,hinj,hbound,hsum⟩:=Parameters.exists_distinct_slot_lengths
    (cap/(6*Geometry.ell)) (by positivity)
  refine ⟨N,fun j=>6*Geometry.ell*old j,?_,?_,?_⟩
  · intro j k hjk
    exact hinj ((mul_right_inj' (show 6*Geometry.ell≠0 by positivity)).mp hjk)
  · intro j
    refine ⟨mul_pos (by positivity) (hbound j).1,?_⟩
    have hb:old j*(6*Geometry.ell)<cap:=
      (lt_div_iff₀ (show (0:ℝ)<6*Geometry.ell by positivity)).mp (hbound j).2
    nlinarith
  · rw [←Finset.mul_sum,hsum]
    ring

theorem exists_baseline_data_common_mesh {κ σ : ℝ} (hk : 7/10≤κ) (hk1 : κ≤3/4)
    (hσ : 0<σ) (mesh : ℝ→ℝ) (hmeshPos : ∀t,0<t→0<mesh t) :
    ∃D:BaselineData,D.momentKappa=κ ∧ 159*D.ε+609*D.t≤σ ∧
      (∀j,D.length j≤Cycle25.sourceMesh D.t/200) ∧ (∀j,D.length j≤mesh D.t/200) := by
  let ε : ℝ:=min (σ/400) (1/20000000)
  have hep : 0<ε:=lt_min (by positivity) (by norm_num)
  have heσ : ε≤σ/400:=min_le_left _ _
  have hes : ε≤1/20000000:=min_le_right _ _
  let t : ℝ:=ε/2000
  have ht : 0<t:=by positivity
  have hmesh:=Cycle25.sourceMesh_pos ht
  obtain ⟨N,length,hinj,hbound,hsum⟩:=exists_distinct_fine_slots
    (cap:=min ((1/200)*t) (min (Cycle25.sourceMesh t/200) (mesh t/200)))
      (lt_min (by positivity) (lt_min (by positivity) (by have:=hmeshPos t ht;positivity)))
  let D : BaselineData := {
    N:=N,length:=length,t:=t,ε:=ε,e:=ε/10000,
    witnessKappa:=ε/1000,cost:=ε/1000,momentKappa:=κ,
    t_pos:=ht,t_small:=by dsimp [t];linarith,
    epsilon_pos:=hep,epsilon_small:=by linarith,epsilon_count_small:=by linarith,
    e_pos:=by positivity,e_small:=by linarith,witnessKappa_pos:=by positivity,
    witnessKappa_small:=by linarith,cost_pos:=by positivity,
    momentKappa_lo:=hk,momentKappa_hi:=hk1,slots_injective:=hinj,
    slots_pos:=fun j=>(hbound j).1,
    slots_small:=fun j=>(hbound j).2.trans (min_le_left _ _),
    slots_sum:=hsum,detector_budget:=by linarith,t_le:=by dsimp [t];linarith }
  refine ⟨D,rfl,?_,?_⟩
  · dsimp [D,t];linarith
  · constructor
    · intro j;exact (hbound j).2.trans ((min_le_right _ _).trans (min_le_left _ _))
    · intro j;exact (hbound j).2.trans ((min_le_right _ _).trans (min_le_right _ _))
/-- Baseline-only specialization of the common-mesh constructor. -/
theorem exists_baseline_data_fine {κ σ : ℝ} (hk : 7/10≤κ) (hk1 : κ≤3/4)
    (hσ : 0<σ) : ∃D:BaselineData,D.momentKappa=κ ∧
      159*D.ε+609*D.t≤σ ∧ ∀j,D.length j≤Cycle25.sourceMesh D.t/200 := by
  obtain ⟨D,hκ,he,hfine,_⟩:=exists_baseline_data_common_mesh hk hk1 hσ
    Cycle25.sourceMesh (fun _ ht=>Cycle25.sourceMesh_pos ht)
  exact ⟨D,hκ,he,hfine⟩


abbrev BaselineSourceData (D : BaselineData) :=
  Cycle25ProbeFinalAssembly.WeightedSourceData D.toMomentData

def baselineSource (D : BaselineData) (F : BaselineSourceData D) : SourceData where
  S:=F.S
  exclusions:=F.exclusions
  maximal:=F.maximal
  w:=F.w
  smooth:=F.smooth
  compact:=F.compact
  support:=F.support
  positive_support:=F.positive_support
  bounded:=F.bounded
  nonzero:=F.nonzero

theorem exists_baseline_source (D : BaselineData) : Nonempty (BaselineSourceData D) :=
  Cycle25ProbeFinalAssembly.weighted_exists_source_data D.toMomentData

end
end QRH.Record1252270103Return.GenericPhysical

#print axioms QRH.Record1252270103Return.GenericPhysical.exists_baseline_data_common_mesh
#print axioms QRH.Record1252270103Return.GenericPhysical.exists_baseline_source
