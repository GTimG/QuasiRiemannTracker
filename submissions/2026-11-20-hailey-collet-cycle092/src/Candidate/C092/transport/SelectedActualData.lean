/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The genuine compatible-data constructor below follows Collet's transport
parameters and Joseph Bebel's common-mesh refinement, with the original OpenAI,
Levy and Gao source attributions retained by its imports. Only the unneeded
historical CoreBounds assumption is replaced by the used theta>0 premise. -/
import Candidate.C092.transport.SelectedActual
import Candidate.C092.UpstreamPrivate.Local.Qrh.TwoSlot.AnchorExtension.Library.JointDetector.BoundaryPhysical.Transport.TransportParameters

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open Filter
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily OAI.SevenEighths.HeckeInverseAmplification
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.ProbeAssembly
namespace QRH.Cycle092.SelectedActualData

private theorem commonMesh_positive {t : ℝ} (ht : 0 < t) : 0 < commonMesh t :=
  lt_min (Cycle25.sourceMesh_pos ht) ht
private theorem commonMesh_small {t : ℝ} : commonMesh t ≤ t := min_le_right _ _

variable [Geometry.Parameters]

/-- All authentic transport parameters, including positive common savings and
window/phase/floor budgets, exist at the actual geometry. No conductor, cap or
floor-moment bound is inferred from their numerical parameter construction. -/
theorem compatible_data_with_mesh {κ budget : ℝ} (hk : 7/10≤κ) (hk1 : κ≤3/4)
    (hb : 0< budget) (htheta : 0 < Geometry.theta) (extraMesh : ℝ → ℝ)
    (hExtra : ∀t : ℝ,0< t → 0< extraMesh t) :
    ∃D : BaselineData,D.momentKappa=κ ∧ 159*D.ε+609*D.t≤ budget ∧
      (∀j,D.length j≤ Cycle25.sourceMesh D.t/200) ∧
      (∀j,D.length j≤ commonMesh D.t/200) ∧
      (∀j,D.length j≤ extraMesh D.t/200) ∧ Nonempty (TransportParameters D) := by
  let small : ℝ := min budget (1/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  have hsmall : 0< small := lt_min hb (by norm_num)
  obtain ⟨D,hκ,hbudget,hfine,hboth⟩ := exists_baseline_data_common_mesh hk hk1 hsmall
    (fun t => min (commonMesh t) (extraMesh t))
    (fun t ht => lt_min (commonMesh_positive ht) (hExtra t ht))
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
  have hmesh : 0< mesh := lt_min (commonMesh_positive D.t_pos) (hExtra D.t D.t_pos)
  have hmeshsmall : mesh≤D.t := (min_le_left _ _).trans commonMesh_small
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
      change D.t≤1/4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
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
      change 26*e+(D.N+8)*eps+D.t+mesh*QRH.Record1252270103Return.Geometry.ell+D.t/8+sigma≤1/100000
      rw [hepsmul]
      linarith }⟩⟩


/-- Source, slots and every transport parameter precede the live height and
character; every positive height then admits the actual buffered choices. -/
theorem compatible_source_with_selection {kappa budget : ℝ}
    (hk : 7/10 ≤ kappa) (hk' : kappa ≤ 3/4) (hb : 0 < budget)
    (htheta : 0 < Geometry.theta) (extraMesh : ℝ → ℝ)
    (hExtra : ∀ t : ℝ, 0 < t → 0 < extraMesh t) :
    ∃ D : BaselineData, ∃ F : BaselineSourceData D, ∃ _P : TransportParameters D,
      D.momentKappa = kappa ∧ 159*D.ε+609*D.t ≤ budget ∧
      (∀ j, D.length j ≤ Cycle25.sourceMesh D.t/200) ∧
      (∀ j, D.length j ≤ commonMesh D.t/200) ∧
      (∀ j, D.length j ≤ extraMesh D.t/200) ∧
      ∀ padding tau : ℝ, 0 < tau → ∃ n : ℕ, 0 < n ∧ ∀ᶠ Z : ℝ in atTop,
        normalizer D F Z ≠ 0 ∧ ∀ η : Character,
          ∃ idx grid : FreeRow → ℕ, selected D F padding tau n η Z idx grid := by
  obtain ⟨D, hkappa, hbudget, hfine, hcommon, hextra, ⟨P⟩⟩ :=
    compatible_data_with_mesh hk hk' hb htheta extraMesh hExtra
  obtain ⟨F⟩ := exists_baseline_source D
  exact ⟨D, F, P, hkappa, hbudget, hfine, hcommon, hextra,
    fun padding tau htau => SelectedActual.normalized_buffered_selection D F padding tau htau⟩

/-- Every raw exponent budget follows from the constructed authentic transport
record, including the large-tail inequality with saving 1. -/
theorem raw_budgets [ActualGeometry.WidenedCoreBounds]
    (D : BaselineData) (P : TransportParameters D)
    {beta : ℝ} (hbeta : Geometry.theta ≤ beta) :
    (7/8 : ℝ)+ProbeAssembly.shift-
        (Geometry.y/2-Geometry.h*(17/50-1/6)-1/50)+8*D.e+P.nu ≤ beta+ProbeAssembly.shift-P.sigma ∧
    -1+P.nu ≤ beta+ProbeAssembly.shift-P.sigma ∧
    beta+ProbeAssembly.shift-1/4000+P.nu ≤ beta+ProbeAssembly.shift-P.sigma ∧
    beta+ProbeAssembly.shift+D.e-Geometry.theta*P.ellMin ≤ beta+ProbeAssembly.shift-P.sigma := by
  have hsignal : 0 < Geometry.signal Geometry.theta := by
    rw [Geometry.signal_at_boundary]
    have hx : 0 < Geometry.x := Geometry.ell_pos.trans Geometry.ell_lt_x
    have hxy := Geometry.x_lt_y
    linarith
  have hlarge : P.sigma+P.nu ≤ 1+Geometry.signal Geometry.theta := by
    have hs := P.sigma_small
    have hn := P.nu_eq
    have ht := D.t_small
    linarith
  exact SelectedActual.raw_exponents hbeta P.geometric_budget P.principal_budget
    P.window_budget hlarge

omit [Geometry.Parameters] in
/-- Q's literal padding meets the existing canonical contour cutoff, including
the conductor-cap separation needed by the later physical estimates. -/
theorem Q_conductor_padding {h : ℝ} (hu : h ≤ Cycle090.hUpper) :
    0 < Cycle090.rowPad ∧ Cycle090.rowPad ≤ 1/(10 : ℝ)^(258 : ℕ) ∧
    h+Cycle090.rowPad ≤ (7/8 : ℝ)-1/100 ∧ h+Cycle090.rowPad < 1 := by
  have hp : Cycle090.rowPad ≤ (1/1000000000000 : ℝ) := by
    have hpow : (10 : ℝ)^(12 : ℕ) ≤ 10^(258 : ℕ) :=
      pow_le_pow_right₀ (by norm_num) (by norm_num)
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 10^(12 : ℕ)) hpow
    simpa only [Cycle090.rowPad, show (10 : ℝ)^(12 : ℕ) = 1000000000000 by norm_num] using hi
  norm_num [Cycle090.hUpper] at hu
  refine ⟨by norm_num [Cycle090.rowPad], le_rfl, ?_, ?_⟩ <;> linarith

/-- H7's actual donor cube has half of Q's numerical padding. The constructed
time budget covers that entire donor cube, not a smaller replacement pad. -/
theorem Q_donor_padding (D : BaselineData) (P : TransportParameters D) :
    D.t ≤ Cycle090.rowPad/4 ∧ Cycle090.rowPad/2+2*D.t ≤ Cycle090.rowPad := by
  have ht := P.t_padding
  have heq : Cycle090.rowPad/4 =
      (1/4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    norm_num [Cycle090.rowPad, pow_succ]
  rw [← heq] at ht
  exact ⟨ht, by linarith⟩

omit [Geometry.Parameters] in
/-- The constructor applies to every genuine Q conductor, including the
manuscript's shifted-contact value, without an old coarse-bounds instance. -/
theorem Q_compatible_source_with_selection (h : ℝ)
    (hl : Cycle090.hLower ≤ h) (hu : h ≤ Cycle090.hUpper)
    {kappa budget : ℝ} (hk : 7/10 ≤ kappa) (hk' : kappa ≤ 3/4)
    (hb : 0 < budget) (extraMesh : ℝ → ℝ)
    (hExtra : ∀ t : ℝ, 0 < t → 0 < extraMesh t) :
    let : Geometry.Parameters := ActualGeometry.parameters h hl hu
    ∃ D : BaselineData, ∃ F : BaselineSourceData D, ∃ _P : TransportParameters D,
      D.momentKappa = kappa ∧ 159*D.ε+609*D.t ≤ budget ∧
      (∀ j, D.length j ≤ Cycle25.sourceMesh D.t/200) ∧
      (∀ j, D.length j ≤ commonMesh D.t/200) ∧
      (∀ j, D.length j ≤ extraMesh D.t/200) ∧
      ∀ padding tau : ℝ, 0 < tau → ∃ n : ℕ, 0 < n ∧ ∀ᶠ Z : ℝ in atTop,
        normalizer D F Z ≠ 0 ∧ ∀ η : Character,
          ∃ idx grid : FreeRow → ℕ, selected D F padding tau n η Z idx grid := by
  let : Geometry.Parameters := ActualGeometry.parameters h hl hu
  exact compatible_source_with_selection hk hk' hb
    (by change (0 : ℝ) < Cycle090.theta; norm_num [Cycle090.theta]) extraMesh hExtra

end QRH.Cycle092.SelectedActualData
#print axioms QRH.Cycle092.SelectedActualData.compatible_data_with_mesh
#print axioms QRH.Cycle092.SelectedActualData.compatible_source_with_selection
#print axioms QRH.Cycle092.SelectedActualData.Q_compatible_source_with_selection
