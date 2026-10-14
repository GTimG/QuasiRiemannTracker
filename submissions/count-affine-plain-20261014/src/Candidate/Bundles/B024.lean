/- Cycle61 successor parameter adaptation by Zhongpai Gao, with AI assistance. Nominal θ=4374299/5000000, q=67/100; exact reserves and actual source consumers are changed by scoped ownership maps. Original notices/provenance remain intact. Full source replay and independent verification are pending. -/
/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B000
import Candidate.Bundles.B020
import Candidate.Bundles.B023
import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyMomentInput

/- BEGIN ORIGINAL Cycle61.Assembly.Count.BaselineMoments; sha256 bf2e0da76f92e8cebc6725d1d05b6efb0d63bf406a0c01eb122bc57e75f7a84c -/
section
                                              
                                         
                                           

namespace OAI.SevenEighths.Cycle61DetectorCount
noncomputable section
open scoped Classical
open Filter HeckeFamily

/-- The source window/exclusions are the genuine original physical source data.
Only the pure slot/moment contract is reused; it has no endpoint geometry. -/
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

/-- Genuine original MI/MP0 and κ-marked MP inputs on the new exact slot lengths,
from the completed parameterized κ certificate. No affine interior estimate or
improved quartic endpoint is used. -/
theorem actual_baseline_source_moments (D : BaselineData) (F : BaselineSourceData D)
    (counts : Cycle25ProbeHighRowFamily.CountParameters (baselineSource D F).modulus ⊤ D.t)
    (hβ : 51/100≤HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1≤D.momentKappa)
    (hfine : ∀j,D.length j≤Cycle25.sourceMesh D.t/200) :
    ∃J:ℝ,0≤J ∧ ∀η:Character,∃C:ℝ,0<C ∧ ∀τ:ℝ,0<τ→τ≤1→
      ∀ᶠZ:ℝ in atTop,SourceMomentBound D.toData (baselineSource D F) counts η Z τ
        (C*(1+Z^(2*τ))^J) (Z^(2*τ)) := by
  exact Cycle25ProbeFinalAssembly.weighted_actual_source_moments F D.momentKappa
    D.momentKappa_lo D.momentKappa_hi hβ hκβ counts hfine
end
end OAI.SevenEighths.Cycle61DetectorCount

end
/- END ORIGINAL Cycle61.Assembly.Count.BaselineMoments -/

/- BEGIN ORIGINAL Cycle61.Assembly.Count.ChosenHeight; sha256 54ab6dc48a51aa8353ab1b8ef4e156ff1de648fb159ca7e45409e7eedcb3c805 -/
section
                                             
                                                                    

namespace OAI.SevenEighths.Cycle61DetectorCount
noncomputable section
open scoped Classical
open Filter HeckeFamily

/-- One height exponent is chosen after the fixed polynomial degree and before
all live rows and all physical amplitude classes. -/
theorem actual_chosen_height (D : BaselineData) (F : BaselineSourceData D)
    (counts : Cycle25ProbeHighRowFamily.CountParameters (baselineSource D F).modulus ⊤ D.t)
    (hβ : 51/100≤HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1≤D.momentKappa)
    (hfine : ∀j,D.length j≤Cycle25.sourceMesh D.t/200) :
    ∃τ:ℝ,0<τ ∧ τ<(1/200:ℝ)/2 ∧ 4*τ<(1/200:ℝ)*D.cost ∧ 2*τ≤D.t ∧
      ∀η:Character,∃C:ℝ,1≤C ∧ ∀ᶠZ:ℝ in atTop,
        SourceMomentBound D.toData (baselineSource D F) counts η Z τ
          (C*Z^D.t) (Z^(2*τ)) := by
  obtain ⟨J,hJ,hbound⟩:=actual_baseline_source_moments D F counts hβ hκβ hfine
  let τ : ℝ:=min ((1/200:ℝ)*D.cost/16) (min (1/800) (D.t/(4*(J+1))))
  have ht : 0<τ:=lt_min (by have:=D.cost_pos;positivity)
    (lt_min (by norm_num) (by have:=D.t_pos;positivity))
  have hcost : τ≤(1/200:ℝ)*D.cost/16:=min_le_left _ _
  have hd : τ≤1/800:=(min_le_right _ _).trans (min_le_left _ _)
  have hsmall : τ≤D.t/(4*(J+1)):=(min_le_right _ _).trans (min_le_right _ _)
  have hb : τ*(4*(J+1))≤D.t:=(le_div_iff₀ (by positivity)).mp hsmall
  have hτJ : 0≤τ*J:=mul_nonneg ht.le hJ
  refine ⟨τ,ht,by linarith,by linarith [D.cost_pos],by nlinarith,?_⟩
  intro η
  obtain ⟨C,hC,hbound⟩:=hbound η
  refine ⟨max 1 (C*2^J),le_max_left _ _,?_⟩
  filter_upwards [hbound τ ht (by linarith),eventually_ge_atTop (1:ℝ)] with Z hm hZ
  apply hm.mono_constant (by linarith)
  apply (ProbeFinalAssembly.polynomial_height_absorption C Z τ J D.t hC.le hZ ht.le hJ
    (by nlinarith)).trans
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by linarith) _)
end
end OAI.SevenEighths.Cycle61DetectorCount

end
/- END ORIGINAL Cycle61.Assembly.Count.ChosenHeight -/

/- BEGIN ORIGINAL Cycle61.Assembly.Transport.GeometryFacts; sha256 0fe8c7b21fd62137f109f06bc7e1c11fe46e96c40a9757451ded2f1c7530a4c6 -/
section
                                

namespace Cycle61.Transport
noncomputable section

abbrev theta : ℝ := Arithmetic.theta
abbrev lx : ℝ := Arithmetic.x
abbrev ly : ℝ := Arithmetic.y
abbrev ell : ℝ := Arithmetic.ell
abbrev h : ℝ := Arithmetic.h
def b : ℝ := ly-lx
abbrev signal := Assembly.signal
def rowExtension : ℝ := 1/10000000000

theorem ell_interval : (1672 : ℝ)/10000 < ell ∧ ell < 16723/100000 := by norm_num [ell, Arithmetic.ell]
theorem h_pos : 0 < h := by norm_num [h, Arithmetic.h]
theorem extended_h_lt_one : h+rowExtension < 1 := by norm_num [h, Arithmetic.h, rowExtension]

theorem theta_lower : (874 : ℝ)/1000 < theta := by norm_num [theta, Arithmetic.theta]
theorem theta_bounds : (874 : ℝ)/1000 < theta ∧ theta < 7/8 :=
  ⟨theta_lower, Assembly.theta_lt_seven_eighths⟩
theorem h_interval : (793 : ℝ)/1000 < h ∧ h < 795/1000 := by norm_num [h, Arithmetic.h]
theorem ly_coarse : (458 : ℝ)/1000 < ly ∧ ly < 461/1000 := by norm_num [ly, Arithmetic.y]
theorem length_sum : lx+ly = 1-ell := Arithmetic.x_add_y
theorem row_endpoint : h = 1-lx+ell := Assembly.row_endpoint
theorem small_saving : (7/100 : ℝ) < ly/2-h*(17/50-1/6)-1/50 := by
  norm_num [ly, h, Arithmetic.y, Arithmetic.h]
theorem signalShift_eq : -(4+b)/6 = Assembly.signalShift := by
  exact Assembly.signalShift_eq.symm

theorem extended_row_cutoff {ζ : ℝ} (hζ : ζ ≤ 1/10000000000) :
    h+ζ ≤ Arithmetic.dPlus := by
  rw [Arithmetic.dPlus_eq]
  linarith

theorem principal_w_reserve :
    ly/20-(1+h)/1000-1/4000 = 313960284089/15000000000000 :=
  Arithmetic.principal_y_reserve

theorem principal_z_reserve :
    h/600-1/1000-1/4000 = 219737987/3000000000000 :=
  Arithmetic.principal_h_reserve

end
end Cycle61.Transport

end
/- END ORIGINAL Cycle61.Assembly.Transport.GeometryFacts -/

/- BEGIN ORIGINAL Cycle61.Assembly.Final.Parameters; sha256 c2713ff13a6109bca770aa338c7d016bdf28d069419008f52bdf78cfa338d200 -/
section
                                              
                                               

set_option autoImplicit false
namespace Cycle61.FinalAssembly
noncomputable section
open scoped Classical BigOperators
open OAI.SevenEighths Cycle61DetectorCount

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
end Cycle61.FinalAssembly

end
/- END ORIGINAL Cycle61.Assembly.Final.Parameters -/
