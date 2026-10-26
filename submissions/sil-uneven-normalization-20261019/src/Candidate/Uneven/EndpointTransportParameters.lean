/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Target830 full pre-height slot/phase transport schedule. Predecessor attribution retained. Apache-2.0. -/
import Candidate.Uneven.EndpointData
import Candidate.Uneven.EndpointScalar
import Candidate.Cycle63.Assembly.Transport.GeometryFacts
import Candidate.Affine.Mesh

set_option autoImplicit false
namespace OAI.SevenEighths.UnevenEndpoint.Physical.Assembly
variable [config : Configuration]
noncomputable section
open scoped Classical BigOperators
open OAI.SevenEighths OAI.SevenEighths.UnevenEndpoint.Physical

/-- Reduce the contour spacing after the finite slot partition is fixed. -/
def withSmallerE (D : BaselineData) (e : ℝ) (he : 0< e) (hle : e≤ D.e) : BaselineData :=
  { D with
    e := e
    e_pos := he
    e_small := hle.trans_lt D.e_small
    detector_budget := by
      have hd:=D.detector_budget
      nlinarith }


def commonMesh (t : ℝ) : ℝ := min (min (Cycle25.sourceMesh t) t) (DetectorAffine.detectorMesh t)
lemma commonMesh_pos {t : ℝ} (ht : 0< t) : 0< commonMesh t :=
  lt_min (lt_min (Cycle25.sourceMesh_pos ht) ht) (DetectorAffine.detectorMesh_pos ht)
lemma commonMesh_le {t : ℝ} : commonMesh t≤ t := (min_le_left _ _).trans (min_le_right _ _)
lemma commonMesh_le_detector {t : ℝ} : commonMesh t≤ DetectorAffine.detectorMesh t := min_le_right _ _

def rowPadding : ℝ := upperPadding/2

structure TransportParameters (D : BaselineData) where
  t_padding : D.t≤ upperPadding/4
  mesh : ℝ
  mesh_pos : 0< mesh
  mesh_small : mesh≤ D.t
  slots_mesh : ∀j,D.length j≤ mesh/200
  e_tsmall : D.e≤ D.t/10000
  rmin : ℝ
  rmin_pos : 0< rmin
  slots_lower : ∀j,(7/8:ℝ)*rmin≤ D.length j
  ellMin : ℝ
  ellMin_pos : 0< ellMin
  slots_min : ∀j,ellMin≤ D.length j
  phaseEpsilon : ℝ
  phaseEpsilon_pos : 0< phaseEpsilon
  phaseKappa : ℝ
  phaseKappa_pos : 0< phaseKappa
  phase_budget : 8*D.e*D.t+phaseKappa≤ phaseEpsilon
  phase_gap : phaseEpsilon< rmin*mesh
  eps : ℝ
  eps_pos : 0< eps
  eps_budget : (D.N+8)*eps≤ D.t/100
  sigma : ℝ
  sigma_pos : 0< sigma
  sigma_small : sigma≤ D.t/8
  nu : ℝ
  nu_pos : 0< nu
  nu_eq : nu=D.t/8
  geometric_budget : sigma+8*D.e+nu≤1/20
  principal_budget : sigma+nu≤1/4000
  window_budget : sigma+D.e≤ OAI.SevenEighths.UnevenEndpoint.theta*ellMin
  floor_budget : 26*D.e+(D.N+8)*eps+D.t+mesh*OAI.SevenEighths.UnevenEndpoint.ell+nu+sigma≤1/100


theorem exists_compatible_data_with_mesh {κ budget : ℝ} (hk : 7/10≤κ) (hk1 : κ≤3/4)
    (hb : 0< budget) (extraMesh : ℝ → ℝ)
    (hExtra : ∀t : ℝ,0< t → 0< extraMesh t) :
    ∃D : BaselineData,D.momentKappa=κ ∧ 159*D.ε+609*D.t≤ budget ∧
      (∀j,D.length j≤ Cycle25.sourceMesh D.t/200) ∧
      (∀j,D.length j≤ commonMesh D.t/200) ∧
      (∀j,D.length j≤ extraMesh D.t/200) ∧ Nonempty (TransportParameters D) := by
  have hpad : 0 < upperPadding := by
    cases config with
    | mk stage => cases stage <;> norm_num [upperPadding]
  let small : ℝ := min budget (min (1/100000000) (100*upperPadding))
  have hsmall : 0< small := lt_min hb (lt_min (by norm_num) (by positivity))
  obtain ⟨D,hκ,hbudget,hfine,hboth⟩ := exists_baseline_data_common_mesh hk hk1 hsmall
    (fun t => min (commonMesh t) (extraMesh t))
    (fun t ht => lt_min (commonMesh_pos ht) (hExtra t ht))
  have hcommon : ∀j,D.length j≤ commonMesh D.t/200 := fun j =>
    (hboth j).trans (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
  have hextra : ∀j,D.length j≤ extraMesh D.t/200 := fun j =>
    (hboth j).trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
  have hbound : 159*D.ε+609*D.t≤ budget := hbudget.trans (min_le_left _ _)
  have hsum : 0<∑j,D.length j := by rw [D.slots_sum];exact (by have hh := parameter_gates.2.2.2.1; linarith only [hh])
  obtain ⟨j,_,_⟩ := (Finset.sum_pos_iff_of_nonneg (fun j _=>(D.slots_pos j).le)).mp hsum
  let : Nonempty (Fin D.N) := ⟨j⟩
  obtain ⟨m,hm,hmle⟩ : ∃m : ℝ,0< m ∧ ∀j,m≤ D.length j := by
    obtain ⟨i,hmle⟩ := Finite.exists_min D.length
    exact ⟨D.length i,D.slots_pos i,hmle⟩
  let mesh := min (commonMesh D.t) (extraMesh D.t)
  have hmesh : 0< mesh := lt_min (commonMesh_pos D.t_pos) (hExtra D.t D.t_pos)
  have hmeshsmall : mesh≤ D.t := (min_le_left _ _).trans commonMesh_le
  let phase := m*mesh/2
  have hphase : 0< phase := by positivity
  let e := min D.e (min (phase/(32*D.t)) (min (OAI.SevenEighths.UnevenEndpoint.theta*m/4) (D.t/10000)))
  have htheta : 0< theta := by have hh := parameter_gates.1; linarith only [hh]
  have ht:=D.t_pos
  have hep : 0< e := lt_min D.e_pos (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have heD : e≤ D.e := min_le_left _ _
  have hephase : e≤ phase/(32*D.t) := (min_le_right _ _).trans (min_le_left _ _)
  have hetheta : e≤ OAI.SevenEighths.UnevenEndpoint.theta*m/4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hesmall : e≤ D.t/10000 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let D' := withSmallerE D e hep heD
  let sigma := min (OAI.SevenEighths.UnevenEndpoint.theta*m/4) (D.t/8)
  have hsigma : 0< sigma := lt_min (by positivity) (by positivity)
  have hsigma1 : sigma≤ D.t/8 := min_le_right _ _
  have hsigmaw : sigma≤ OAI.SevenEighths.UnevenEndpoint.theta*m/4 := min_le_left _ _
  let eps : ℝ := D.t/(100*(D.N+8))
  have heps : 0< eps := by positivity
  refine ⟨D',hκ,hbound,hfine,hcommon,hextra,⟨{
    t_padding:=by
      have hbsmall : 159*D.ε+609*D.t ≤ 100*upperPadding := hbudget.trans ((min_le_right _ _).trans (min_le_right _ _))
      have hep0:=D.epsilon_pos
      change D.t≤ upperPadding/4
      linarith
    mesh:=mesh
    mesh_pos:=hmesh
    mesh_small:=hmeshsmall
    slots_mesh:=hboth
    e_tsmall:=hesmall
    rmin:=m
    rmin_pos:=hm
    slots_lower:=fun j=> by dsimp [D',withSmallerE];nlinarith [hmle j]
    ellMin:=m
    ellMin_pos:=hm
    slots_min:=hmle
    phaseEpsilon:=phase
    phaseEpsilon_pos:=hphase
    phaseKappa:=phase/4
    phaseKappa_pos:=by positivity
    phase_budget:=by
      have ht:=D.t_pos
      have hmul: e*(32*D.t)≤ phase := (le_div_iff₀ (by positivity)).mp hephase
      change 8*e*D.t+phase/4≤ phase
      nlinarith
    phase_gap:=by dsimp [phase];nlinarith [mul_pos hm hmesh]
    eps:=eps
    eps_pos:=heps
    eps_budget:=by change (D.N+8:ℝ)*eps≤ D.t/100;dsimp [eps];field_simp; norm_num
    sigma:=sigma
    sigma_pos:=hsigma
    sigma_small:=hsigma1
    nu:=D.t/8
    nu_pos:=by positivity
    nu_eq:=rfl
    geometric_budget:=by change sigma+8*e+D.t/8≤1/20;linarith [D.t_small]
    principal_budget:=by linarith [D.t_small]
    window_budget:=by change sigma+e≤ OAI.SevenEighths.UnevenEndpoint.theta*m;linarith [mul_pos htheta hm]
    floor_budget:=by
      have ht:=D.t_small
      have hme:mesh≤ D.t:=hmeshsmall
      have hmes:mesh*OAI.SevenEighths.UnevenEndpoint.ell≤ D.t := by
        have hel : OAI.SevenEighths.UnevenEndpoint.ell≤1 := by have hh := parameter_gates.2.2.2.2.1; linarith only [hh]
        exact (mul_le_mul_of_nonneg_left hel hmesh.le).trans (by simpa using hme)
      have hepsmul : (D.N+8:ℝ)*eps=D.t/100 := by
        dsimp [eps];field_simp
      change 26*e+(D.N+8)*eps+D.t+mesh*OAI.SevenEighths.UnevenEndpoint.ell+D.t/8+sigma≤1/100
      rw [hepsmul]
      linarith }⟩⟩


theorem padding_budget (D : BaselineData) (P : TransportParameters D) :
    rowPadding+2*D.t≤ upperPadding := by
  have h:=P.t_padding
  unfold rowPadding
  linarith

theorem padded_row_cutoff (D : BaselineData) (P : TransportParameters D) :
    OAI.SevenEighths.UnevenEndpoint.h+rowPadding+2*D.t≤ OAI.SevenEighths.UnevenEndpoint.dPlus := by
  change OAI.SevenEighths.UnevenEndpoint.h+rowPadding+2*D.t≤ OAI.SevenEighths.UnevenEndpoint.h+upperPadding
  have h:=padding_budget D P
  linarith
end
end OAI.SevenEighths.UnevenEndpoint.Physical.Assembly


