/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
P4's shorter-factor upper bound from the actual selected source zero band.
The original OpenAI buffered dyadic theorem and source family are unchanged. -/
import Candidate.C092.transport.ExistentialPacketBatches
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DyadicSource

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open HeckeDyadic HeckeDetectorDyadicGeometry
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.MediumWitness
namespace QRH.Cycle092.MediumReplace
variable [Geometry.Parameters]

/-- Uniform actual shorter-factor upper bound. The finite Mellin order and
constant precede the live character, buffered n, row and physical profile.
The profile budgets concern the actual retained compact log profile, including
its own height and fixed mask; they do not assert an endpoint energy. -/
theorem original_short_upper (D : BaselineData) (F : BaselineSourceData D)
    (τ : ℝ) (hτ : 0 < τ) (hheight : 4*τ < (1/200 : ℝ)*D.cost)
    (profileBound : ℕ → ℝ) (hprofile : ∀ k, 0 ≤ profileBound k) :
    ∃ order : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (η : Character) (n : ℕ),
      ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (padding d rowCap : ℝ) (idx grid : FreeRow → ℕ),
        (1/200 : ℝ) ≤ d → d ≤ 7/8 →
        ProbeAssembly.selected D F padding τ n η Z idx grid →
      ∀ u ∈ rowBand (Z^(1/100 : ℝ)) rowCap,
        (calibrationForSet F.S F.maximal).residueMonoid u.val ≠ 0 →
        rowNorm u ≤ Z^(d-D.t) →
      ∀ (label : Sum Bool (RayQuotient.Characters F.modulus ⊤))
        (W : ℝ → ℂ) (A B y σ freq : ℝ),
        0 < A → Function.support W ⊆ Icc A B → ContDiff ℝ ∞ W →
        0 ≤ y → y ≤ 22 →
        |freq|+Z^τ/2 ≤ (3*idx u+2 : ℕ)*Z^τ →
        (∀ x ∈ Icc (1-(51/100+D.e*grid u)-6*D.e-σ) (2-σ), ∀ t : ℝ,
          (1+|t|)^2*‖mellin W ((x : ℂ)+t*Complex.I)‖ ≤ profileBound 2) →
        (∀ x ∈ Icc (1-(51/100+D.e*grid u)-6*D.e-σ) (2-σ), ∀ t : ℝ,
          (1+|t|)^(order+2)*‖mellin W ((x : ℂ)+t*Complex.I)‖ ≤ profileBound (order+2)) →
        ‖polynomial (originalFamily D F η u label) false W ((Z^d)^y) σ freq‖^2 ≤
          C*(Z^d)^((2*(51/100+D.e*grid u)-1)*y+D.ε) := by
  obtain ⟨order,C,hC,hupper⟩ := source_dyadic_bounds 22 (7/8) τ D.ε D.e D.witnessKappa D.cost
    (by norm_num) (by norm_num) hτ D.epsilon_pos D.e_pos D.e_small
    D.witnessKappa_pos D.witnessKappa_small D.cost_pos.le
    (D.detector_budget.trans (by have h := D.epsilon_pos; linarith)) profileBound hprofile
  refine ⟨order,C,hC,?_⟩
  intro η n
  filter_upwards [source_ray_nonprincipal_eventually F.modulus ⊤ le_top F.S F.exclusions F.maximal η
      (1/100) (by norm_num),
    source_ray_conductor_eventually F.modulus ⊤ le_top F.S F.exclusions.prime η D.t D.t_pos,
    uniform_height_budget (1/200) τ D.cost n hτ.le D.cost_pos.le hheight,
    (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2 : ℝ)),
    eventually_gt_atTop (1 : ℝ)] with Z hnp hcond hbudget hT hZ
  refine ⟨hZ,?_⟩
  intro padding d rowCap idx grid hd hd' hsel u hu hcal hrow label W A B y σ freq
    hA hs hW hy hy' hfreq hm₂ hmn
  have hχ : ∀ j,(originalFamily D F η u j).residue ≠ 1 := hnp rowCap u hu hcal
  have hb := hsel.2.1 u
  have hmax : HeckeDetectorZeros.zeroMaximum (originalFamily D F η u) hχ
      (3*(idx u+1 : ℕ)*Z^τ) < (51/100+D.e*grid u)+2*D.e := by
    rw [←detectorMaximum_eq_nonprincipal]
    exact hb.2.2.2.2.1
  exact (hupper Z d hZ.le (by linarith) hd' hT (originalFamily D F η u) hχ
    (51/100+D.e*grid u) (idx u) hb.1 (hb.2.1.trans (by norm_num)) hmax
    label false W A B hA hs hW y σ freq (hcond u d hrow label) hy hy' hfreq
    (hbudget d hd (idx u) (hsel.1 u).2.1) hm₂ hmn).1

end QRH.Cycle092.MediumReplace
#print axioms QRH.Cycle092.MediumReplace.original_short_upper
