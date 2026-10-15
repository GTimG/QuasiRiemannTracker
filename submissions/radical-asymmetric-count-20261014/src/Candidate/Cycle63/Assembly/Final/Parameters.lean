import Candidate.Cycle63.Assembly.Count.BaselineGeometry
import Candidate.Cycle63.Assembly.Transport.GeometryFacts

set_option autoImplicit false
namespace Cycle63.FinalAssembly
noncomputable section
open scoped Classical BigOperators
open OAI.SevenEighths Cycle63DetectorCount

/-- Reduce the contour spacing after the finite slot partition is fixed. -/
def withSmallerE (D : BaselineData) (e : ℝ) (he : 0<e) (hle : e≤D.e) : BaselineData :=
  { D with
    e := e
    e_pos := he
    e_small := hle.trans_lt D.e_small
    detector_budget := by
      have hd:=D.detector_budget
      nlinarith }

theorem withSmallerE_length (D : BaselineData) (e : ℝ) (he : 0<e) (hle : e≤D.e) :
    (withSmallerE D e he hle).length=D.length := rfl

def commonMesh (t : ℝ) : ℝ := min (Cycle25.sourceMesh t) t
lemma commonMesh_pos {t : ℝ} (ht : 0<t) : 0<commonMesh t :=
  lt_min (Cycle25.sourceMesh_pos ht) ht
lemma commonMesh_le {t : ℝ} : commonMesh t≤t := min_le_right _ _

def rowPadding : ℝ := 1/20000000000

structure TransportParameters (D : BaselineData) where
  t_padding : D.t≤1/40000000000
  mesh : ℝ
  mesh_pos : 0<mesh
  mesh_small : mesh≤D.t
  slots_mesh : ∀j,D.length j≤mesh/200
  e_tsmall : D.e≤D.t/10000
  rmin : ℝ
  rmin_pos : 0<rmin
  slots_lower : ∀j,(7/8:ℝ)*rmin≤D.length j
  ellMin : ℝ
  ellMin_pos : 0<ellMin
  slots_min : ∀j,ellMin≤D.length j
  phaseEpsilon : ℝ
  phaseEpsilon_pos : 0<phaseEpsilon
  phaseKappa : ℝ
  phaseKappa_pos : 0<phaseKappa
  phase_budget : 8*D.e*D.t+phaseKappa≤phaseEpsilon
  phase_gap : phaseEpsilon<rmin*mesh
  eps : ℝ
  eps_pos : 0<eps
  eps_budget : (D.N+8)*eps≤D.t/100
  sigma : ℝ
  sigma_pos : 0<sigma
  sigma_small : sigma≤D.t/8
  nu : ℝ
  nu_pos : 0<nu
  nu_eq : nu=D.t/8
  geometric_budget : sigma+8*D.e+nu≤1/20
  principal_budget : sigma+nu≤1/4000
  window_budget : sigma+D.e≤Arithmetic.theta*ellMin
  floor_budget : 26*D.e+(D.N+8)*eps+D.t+mesh*Arithmetic.ell+nu+sigma≤1/100

/-- All genuine baseline data and phase parameters are fixed before source or height. -/
theorem exists_compatible_data {κ budget : ℝ} (hk : 7/10≤κ) (hk1 : κ≤3/4)
    (hb : 0<budget) :
    ∃D : BaselineData,D.momentKappa=κ ∧ 159*D.ε+609*D.t≤budget ∧
      (∀j,D.length j≤Cycle25.sourceMesh D.t/200) ∧
      (∀j,D.length j≤commonMesh D.t/200) ∧ Nonempty (TransportParameters D) := by
  let small : ℝ := min budget (1/100000000)
  have hsmall : 0<small := lt_min hb (by norm_num)
  obtain ⟨D,hκ,hbudget,hfine,hcommon⟩ := exists_baseline_data_common_mesh hk hk1 hsmall
    commonMesh (fun _ ht=>commonMesh_pos ht)
  have hbound : 159*D.ε+609*D.t≤budget := hbudget.trans (min_le_left _ _)
  have hsum : 0<∑j,D.length j := by rw [D.slots_sum];exact Arithmetic.ell_pos
  obtain ⟨j,_,_⟩ := (Finset.sum_pos_iff_of_nonneg (fun j _=>(D.slots_pos j).le)).mp hsum
  let : Nonempty (Fin D.N) := ⟨j⟩
  obtain ⟨m,hm,hmle⟩ : ∃m : ℝ,0<m ∧ ∀j,m≤D.length j := by
    obtain ⟨i,hmle⟩ := Finite.exists_min D.length
    exact ⟨D.length i,D.slots_pos i,hmle⟩
  let mesh := commonMesh D.t
  have hmesh : 0<mesh := commonMesh_pos D.t_pos
  let phase := m*mesh/2
  have hphase : 0<phase := by positivity
  let e := min D.e (min (phase/(32*D.t)) (min (Arithmetic.theta*m/4) (D.t/10000)))
  have htheta : 0<Arithmetic.theta := by norm_num [Arithmetic.theta]
  have ht:=D.t_pos
  have hep : 0<e := lt_min D.e_pos (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have heD : e≤D.e := min_le_left _ _
  have hephase : e≤phase/(32*D.t) := (min_le_right _ _).trans (min_le_left _ _)
  have hetheta : e≤Arithmetic.theta*m/4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hesmall : e≤D.t/10000 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let D' := withSmallerE D e hep heD
  let sigma := min (Arithmetic.theta*m/4) (D.t/8)
  have hsigma : 0<sigma := lt_min (by positivity) (by positivity)
  have hsigma1 : sigma≤D.t/8 := min_le_right _ _
  have hsigmaw : sigma≤Arithmetic.theta*m/4 := min_le_left _ _
  let eps : ℝ := D.t/(100*(D.N+8))
  have heps : 0<eps := by positivity
  refine ⟨D',hκ,hbound,hfine,hcommon,⟨{
    t_padding:=by
      have hbsmall := hbudget.trans (min_le_right _ _)
      have hep0:=D.epsilon_pos
      change D.t≤1/40000000000
      linarith
    mesh:=mesh
    mesh_pos:=hmesh
    mesh_small:=commonMesh_le
    slots_mesh:=hcommon
    e_tsmall:=hesmall
    rmin:=m
    rmin_pos:=hm
    slots_lower:=fun j=>by dsimp [D',withSmallerE];nlinarith [hmle j]
    ellMin:=m
    ellMin_pos:=hm
    slots_min:=hmle
    phaseEpsilon:=phase
    phaseEpsilon_pos:=hphase
    phaseKappa:=phase/4
    phaseKappa_pos:=by positivity
    phase_budget:=by
      have ht:=D.t_pos
      have hmul: e*(32*D.t)≤phase := (le_div_iff₀ (by positivity)).mp hephase
      change 8*e*D.t+phase/4≤phase
      nlinarith
    phase_gap:=by dsimp [phase];nlinarith [mul_pos hm hmesh]
    eps:=eps
    eps_pos:=heps
    eps_budget:=by change (D.N+8:ℝ)*eps≤D.t/100;dsimp [eps];field_simp; norm_num
    sigma:=sigma
    sigma_pos:=hsigma
    sigma_small:=hsigma1
    nu:=D.t/8
    nu_pos:=by positivity
    nu_eq:=rfl
    geometric_budget:=by change sigma+8*e+D.t/8≤1/20;linarith [D.t_small]
    principal_budget:=by linarith [D.t_small]
    window_budget:=by change sigma+e≤Arithmetic.theta*m;linarith [mul_pos htheta hm]
    floor_budget:=by
      have ht:=D.t_small
      have hme:mesh≤D.t:=commonMesh_le
      have hmes:mesh*Arithmetic.ell≤D.t := by
        have hel : Arithmetic.ell≤1 := by norm_num [Arithmetic.ell]
        exact (mul_le_mul_of_nonneg_left hel hmesh.le).trans (by simpa using hme)
      have hepsmul : (D.N+8:ℝ)*eps=D.t/100 := by
        dsimp [eps];field_simp
      change 26*e+(D.N+8)*eps+D.t+mesh*Arithmetic.ell+D.t/8+sigma≤1/100
      rw [hepsmul]
      linarith }⟩⟩

theorem padding_budget (D : BaselineData) (P : TransportParameters D) :
    rowPadding+2*D.t≤Transport.rowExtension := by
  have h:=P.t_padding
  norm_num [rowPadding,Transport.rowExtension] at *
  linarith

theorem padded_row_cutoff (D : BaselineData) (P : TransportParameters D) :
    Arithmetic.h+rowPadding+2*D.t≤Arithmetic.dPlus := by
  rw [Arithmetic.dPlus_eq]
  have h:=padding_budget D P
  dsimp [Transport.rowExtension] at h
  linarith
end
end Cycle63.FinalAssembly
