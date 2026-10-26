import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Assembly.Count.Data
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Weighted.WeightedQRH.MomentData
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle25.Assembly.Mesh
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.ParametersSlotLengths
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
namespace OAI.SevenEighths.Cycle63DetectorCount
noncomputable section
open scoped Classical BigOperators

/-- Smallness and distinctness used by the original physical prime dictionary. -/
structure BaselineData extends Data where
  t_small : t≤1/100000000
  slots_injective : Function.Injective length

def BaselineData.toMomentData (D : BaselineData) : WeightedQRH.MomentData where
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
  epsilon_small:=D.epsilon_small
  e_pos:=D.e_pos

/-- Rescale a distinct prime-slot partition to the exact new rational total. -/
theorem exists_distinct_fine_slots {cap : ℝ} (hc : 0<cap) :
    ∃N:ℕ,∃length:Fin N→ℝ,Function.Injective length ∧
      (∀j,0<length j ∧ length j≤ cap) ∧ ∑j,length j=Cycle63.Arithmetic.ell := by
  have he:=Cycle63.Assembly.Count.ell_pos
  obtain ⟨N,hN,old,hinj,hbound,hsum⟩:=Parameters.exists_distinct_slot_lengths
    (cap/(6*Cycle63.Arithmetic.ell)) (by positivity)
  refine ⟨N,fun j=>6*Cycle63.Arithmetic.ell*old j,?_,?_,?_⟩
  · intro j k hjk
    exact hinj ((mul_right_inj' (show 6*Cycle63.Arithmetic.ell≠0 by positivity)).mp hjk)
  · intro j
    refine ⟨mul_pos (by positivity) (hbound j).1,?_⟩
    have hb:old j*(6*Cycle63.Arithmetic.ell)<cap:=
      (lt_div_iff₀ (show (0:ℝ)<6*Cycle63.Arithmetic.ell by positivity)).mp (hbound j).2
    nlinarith
  · rw [←Finset.mul_sum,hsum]
    ring

theorem exists_baseline_data_common_mesh {κ σ : ℝ} (hk : 7/10≤κ) (hk1 : κ≤3/4)
    (hσ : 0<σ) (mesh : ℝ→ℝ) (hmeshPos : ∀t,0<t→0< mesh t) :
    ∃D:BaselineData,D.momentKappa=κ ∧ 159*D.ε+609*D.t≤σ ∧
      (∀j,D.length j≤Cycle25.sourceMesh D.t/200) ∧ (∀j,D.length j≤ mesh D.t/200) := by
  let ε : ℝ:=min (σ/400) (1/200000)
  have hep : 0<ε:=lt_min (by positivity) (by norm_num)
  have heσ : ε≤σ/400:=min_le_left _ _
  have hes : ε≤1/200000:=min_le_right _ _
  let t : ℝ:=ε/2000
  have ht : 0<t:=by positivity
  have hmesh:=Cycle25.sourceMesh_pos ht
  obtain ⟨N,length,hinj,hbound,hsum⟩:=exists_distinct_fine_slots
    (cap:=min ((1/200)*t) (min (Cycle25.sourceMesh t/200) (mesh t/200)))
      (lt_min (by positivity) (lt_min (by positivity) (by have:=hmeshPos t ht;positivity)))
  let D : BaselineData := {
    N:=N,length:=length,t:=t,ε:=ε,e:=ε/10000,
    witnessKappa:=ε/1000,cost:=ε/1000,momentKappa:=κ,
    t_pos:=ht,t_le:=by dsimp [t];linarith,t_small:=by dsimp [t];linarith,
    epsilon_pos:=hep,epsilon_small:=by linarith,
    e_pos:=by positivity,e_small:=by linarith,witnessKappa_pos:=by positivity,
    witnessKappa_small:=by linarith,cost_pos:=by positivity,
    momentKappa_lo:=hk,momentKappa_hi:=hk1,slots_injective:=hinj,
    slots_pos:=fun j=>(hbound j).1,
    slots_small:=fun j=>(hbound j).2.trans (min_le_left _ _),
    slots_sum:=hsum,detector_budget:=by linarith }
  refine ⟨D,rfl,?_,?_⟩
  · dsimp [D,t];linarith
  · constructor
    · intro j;exact (hbound j).2.trans ((min_le_right _ _).trans (min_le_left _ _))
    · intro j;exact (hbound j).2.trans ((min_le_right _ _).trans (min_le_right _ _))

end
end OAI.SevenEighths.Cycle63DetectorCount

end Record1252270103Bootstrap.PR67
