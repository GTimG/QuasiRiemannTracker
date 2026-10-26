/- Copyright (c) 2026 Sil, Hailey Collet and OpenAI. Apache-2.0.
Carrier definitions for detector and source data, transport heights,
and the literal normalizer. The definitions use Geometry.Parameters
without additional geometry or physical-schedule instances.
-/
import Submissions.hailey_collet_1252270103.Record1252270103Return.GenericData
import Submissions.hailey_collet_1252270103.Record1252270103Return.Transport.TransportParameters
import Submissions.hailey_collet_1252270103.Record1252270103Return.Low.Normalizer

set_option autoImplicit false
namespace Candidate.FourthPower.ReturnCarrierInterfaces
noncomputable section
open scoped Classical BigOperators ContDiff Topology
open Filter Set OAI.SevenEighths HeckeFamily ProbePhysical ProbeRaySlots
open PrincipalSignalComparison PrincipalMellinResidues ProbePrincipalResidueActual
open QRH.Record1252270103Return
open QRH.Record1252270103Return.GenericPhysical
open QRH.Record1252270103Return.GenericPhysical.Assembly

def commonMesh (t : ℝ) : ℝ := min (Cycle25.sourceMesh t) t
theorem commonMesh_pos {t : ℝ} (ht : 0<t) : 0<commonMesh t :=
  lt_min (Cycle25.sourceMesh_pos ht) ht
theorem commonMesh_le {t : ℝ} : commonMesh t≤t := min_le_right _ _

def rowPadding : ℝ := 1/20000000000

section Geometry
variable [Geometry.Parameters]

def withSmallerE (D : BaselineData) (e : ℝ) (he : 0<e) (hle : e≤D.e) : BaselineData :=
  { D with
    e := e
    e_pos := he
    e_small := hle.trans_lt D.e_small
    detector_budget := by
      have hd := D.detector_budget
      nlinarith }

theorem withSmallerE_length (D : BaselineData) (e : ℝ) (he : 0<e) (hle : e≤D.e) :
    (withSmallerE D e he hle).length=D.length := rfl

theorem exists_compatible_data_with_mesh (htheta : 0<Geometry.theta) {κ budget : ℝ} (hk : 7/10≤κ) (hk1 : κ≤3/4)
    (hb : 0< budget) (extraMesh : ℝ → ℝ)
    (hExtra : ∀t : ℝ,0< t → 0< extraMesh t) :
    ∃D : BaselineData,D.momentKappa=κ ∧ 159*D.ε+609*D.t≤ budget ∧
      (∀j,D.length j≤ Cycle25.sourceMesh D.t/200) ∧
      (∀j,D.length j≤ commonMesh D.t/200) ∧
      (∀j,D.length j≤ extraMesh D.t/200) ∧ Nonempty (TransportParameters D) := by
  let small : ℝ := min budget (1/100000000)
  have hsmall : 0< small := lt_min hb (by norm_num)
  obtain ⟨D,hκ,hbudget,hfine,hboth⟩ := exists_baseline_data_common_mesh hk hk1 hsmall
    (fun t => min (commonMesh t) (extraMesh t))
    (fun t ht => lt_min (commonMesh_pos ht) (hExtra t ht))
  have hcommon : ∀j,D.length j≤ commonMesh D.t/200 := fun j =>
    (hboth j).trans (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
  have hextra : ∀j,D.length j≤ extraMesh D.t/200 := fun j =>
    (hboth j).trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
  have hbound : 159*D.ε+609*D.t≤ budget := hbudget.trans (min_le_left _ _)
  have hsum : 0<∑j,D.length j := by rw [D.slots_sum];exact Geometry.ell_pos
  obtain ⟨j,_,_⟩ := (Finset.sum_pos_iff_of_nonneg (fun j _=>(D.slots_pos j).le)).mp hsum
  let : Nonempty (Fin D.N) := ⟨j⟩
  obtain ⟨m,hm,hmle⟩ : ∃m : ℝ,0< m ∧ ∀j,m≤ D.length j := by
    obtain ⟨i,hmle⟩ := Finite.exists_min D.length
    exact ⟨D.length i,D.slots_pos i,hmle⟩
  let mesh := min (commonMesh D.t) (extraMesh D.t)
  have hmesh : 0< mesh := lt_min (commonMesh_pos D.t_pos) (hExtra D.t D.t_pos)
  have hmeshsmall : mesh≤D.t := (min_le_left _ _).trans commonMesh_le
  let phase := m*mesh/2
  have hphase : 0< phase := by positivity
  let e := min D.e (min (phase/(32*D.t)) (min (QRH.Record1252270103Return.Geometry.theta*m/4) (D.t/10000)))
  have ht:=D.t_pos
  have hep : 0< e := lt_min D.e_pos (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have heD : e≤ D.e := min_le_left _ _
  have hephase : e≤ phase/(32*D.t) := (min_le_right _ _).trans (min_le_left _ _)
  have hetheta : e≤ QRH.Record1252270103Return.Geometry.theta*m/4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hesmall : e≤ D.t/10000 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let D' := withSmallerE D e hep heD
  let sigma := min (QRH.Record1252270103Return.Geometry.theta*m/4) (D.t/8)
  have hsigma : 0< sigma := lt_min (by positivity) (by positivity)
  have hsigma1 : sigma≤ D.t/8 := min_le_right _ _
  have hsigmaw : sigma≤ QRH.Record1252270103Return.Geometry.theta*m/4 := min_le_left _ _
  let eps : ℝ := D.t/(100*(D.N+8))
  have heps : 0< eps := by positivity
  refine ⟨D',hκ,hbound,hfine,hcommon,hextra,⟨{
    t_padding:=by
      have hbsmall := hbudget.trans (min_le_right _ _)
      have hep0:=D.epsilon_pos
      change D.t≤1/40000000000
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
    window_budget:=by change sigma+e≤ QRH.Record1252270103Return.Geometry.theta*m;linarith [mul_pos htheta hm]
    floor_budget:=by
      have ht:=D.t_small
      have hme:mesh≤ D.t:=hmeshsmall
      have hmes:mesh*QRH.Record1252270103Return.Geometry.ell≤ D.t := by
        have hel : QRH.Record1252270103Return.Geometry.ell≤1 := by linarith [Geometry.ell_lt_fifth]
        exact (mul_le_mul_of_nonneg_left hel hmesh.le).trans (by simpa using hme)
      have hepsmul : (D.N+8:ℝ)*eps=D.t/100 := by
        dsimp [eps];field_simp
      change 26*e+(D.N+8)*eps+D.t+mesh*QRH.Record1252270103Return.Geometry.ell+D.t/8+sigma≤1/200
      rw [hepsmul]
      linarith }⟩⟩


/-- The literal original normalizer, written without an inherited proof
argument from a theorem that accidentally retained old Bounds. -/
def normalizer (D : BaselineData) (F : BaselineSourceData D) (Z : ℝ) : ℂ :=
  letI : NeZero (∏P∈F.S,P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  let T := fun j=>pool (RayQuotient.identityClass F.modulus ⊤) F.S 1 2 (Z^(D.length j))
  sourceResidueConstant F.W F.W (∏P∈F.S,P)*
    (Probe.principalScalar Finset.univ Z Geometry.ell
      (slotMass T (residueWeights (fun _=>F.w) (fun j=>Z^(D.length j)))) : ℂ)

/-- The same actual inverse-normalizer estimate, using the genuine
Parameters-only low-normalizer theorem directly. No source estimate input. -/
theorem source_normalizer_bound (D : BaselineData) (F : BaselineSourceData D) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
      normalizer D F Z≠0 ∧ ‖(normalizer D F Z)⁻¹‖≤C*Z^(D.t/8) := by
  exact Record1252270103LowNormalizer.actual_ray_normalizer_inverse F.modulus ⊤ le_top F.S F.exclusions
    1 2 (by norm_num) (by norm_num) D.length (fun j=>D.slots_pos j) D.slots_sum
    (fun _=>F.w) (fun _=>F.smooth) (fun _=>F.compact) (fun _=>F.support)
    (fun _ y=>(F.bounded y).1) (fun _=>F.nonzero)
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num) F.complex_support F.complex_support
    F.real F.real F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero
    (D.t/8) (by have ht:=D.t_pos;positivity)

theorem padding_budget (D : BaselineData) (P : TransportParameters D) :
    rowPadding+2*D.t≤(1/10000000000:ℝ) := by
  have ht:=P.t_padding
  norm_num [rowPadding] at *
  linarith

theorem padded_row_cutoff (D : BaselineData) (P : TransportParameters D) :
    Geometry.h+rowPadding+2*D.t≤Geometry.dPlus := by
  have hp:=padding_budget D P
  change Geometry.h+rowPadding+2*D.t≤Geometry.h+1/10000000000
  linarith
/-- The exact six original height conditions, with no old Bounds context. -/
def HeightAdmissible (D : BaselineData) (P : TransportParameters D) (J tau : ℝ) : Prop :=
  0<tau ∧ tau<(1/200:ℝ)/2 ∧ 4*tau<(1/200:ℝ)*D.cost ∧ 2*tau≤D.t ∧
    tau*(2+4*P.eps)<D.t ∧ 2*tau*(1+J)≤D.t

end Geometry
end
end Candidate.FourthPower.ReturnCarrierInterfaces
