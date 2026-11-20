/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual canonical marked responses with the early phase collar paid explicitly.
Upstream OpenAI/Collet/Levy/Gao/Bebel attribution is retained by the imports. -/
import Candidate.C092.transport.SelectedActual
import Candidate.C092.transport.DirectPhaseBins
import Candidate.C092.transport.LowActualResponse
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeSupportedWitness

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Topology
open Filter Set
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
namespace QRH.Cycle092.MediumWitness
variable [Geometry.Parameters]

/-- A fixed pre-height payment absorbs every actual phase-bin collar. -/
def responsePayment (D : BaselineData) (Z : ℝ) : ℝ := Z^(2*D.t*Geometry.ell)

/-- Measured response of the actual physical canonical prime amplitudes,
including zero as in the original response maximum. -/
def canonicalResponse (D : BaselineData) (F : BaselineSourceData D)
    (Z : ℝ) (z : Fin D.N → ℂ) (u : FreeRow) : ℝ :=
  LowActual.response Z (responsePayment D Z) D.length
    (fun j => ‖HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length j)) (z j)‖^2)

lemma length_le_total (D : BaselineData) (j : Fin D.N) : D.length j ≤ Geometry.ell := by
  rw [←D.slots_sum]
  exact Finset.single_le_sum (fun i _ => (D.slots_pos i).le) (Finset.mem_univ j)

lemma responsePayment_pos (D : BaselineData) {Z : ℝ} (hZ : 0 < Z) : 0 < responsePayment D Z :=
  Real.rpow_pos_of_pos hZ _

/-- The payment costs at most one baseline t, so it belongs to the early
source error budget rather than changing the measured response afterward. -/
lemma responsePayment_le (D : BaselineData) {Z : ℝ} (hZ : 1 ≤ Z) : responsePayment D Z ≤ Z^D.t := by
  apply Real.rpow_le_rpow_of_exponent_le hZ
  have ht := D.t_pos
  have he := Geometry.ell_lt_fifth
  nlinarith

lemma phase_squared_paid (D : BaselineData) {Z a g w : ℝ} (hZ : 1 < Z)
    (hw : 0 ≤ w) (hwell : w ≤ Geometry.ell) (hg : g ≤ a-1/2) (Q : ℂ)
    (hQ : ‖Q‖ ≤ (Z^w)^(g+D.t)) :
    ‖Q‖^2 ≤ responsePayment D Z*Z^((2*a-1)*w) := by
  have hZp : 0 < Z := zero_lt_one.trans hZ
  have hP : 0 < Z^w := Real.rpow_pos_of_pos hZp _
  calc
    _ ≤ ((Z^w)^(g+D.t))^2 := pow_le_pow_left₀ (norm_nonneg _) hQ 2
    _ = Z^(2*(g+D.t)*w) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hP.le,←Real.rpow_mul hZp.le]
      congr 1
      ring
    _ ≤ Z^(2*D.t*Geometry.ell+(2*a-1)*w) :=
      Real.rpow_le_rpow_of_exponent_le hZ.le (by
        have h₁ := mul_le_mul_of_nonneg_right hg hw
        have h₂ := mul_le_mul_of_nonneg_left hwell D.t_pos.le
        nlinarith)
    _ = _ := by rw [Real.rpow_add hZp];rfl

/-- Actual upstream phase estimates calibrate the measured original canonical
response to the selected source-family band, uniformly in every allowed height.
The lower and next-upper detector inequalities come from the genuine selection. -/
theorem response_bounded_from_actual_selection (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (τ : ℝ) (n : ℕ) (hτ : 0 < τ)
    (hheight : 4*τ < (1/200 : ℝ)*D.cost) :
    ∀ᶠ Z : ℝ in atTop,1 < Z ∧ ∀ (d padding : ℝ),
      (1/200 : ℝ) ≤ d → d ≤ 7/8 → ∀ (η : Character) (idx grid : FreeRow → ℕ),
      ProbeAssembly.selected D F padding τ n η Z idx grid →
      ∀ (u : FreeRow),Z^(1/100 : ℝ) ≤ rowNorm u →
      (calibrationForSet F.S F.maximal).residueMonoid u.val ≠ 0 → rowNorm u ≤ Z^(d-D.t) →
      ∀ z : Fin D.N → ℂ,(∀ j,(z j).re=17/50) →
      (∀ j,|(z j).im| ≤ (3*idx u+1 : ℕ)*Z^τ) →
      0 ≤ canonicalResponse D F Z z u ∧
        canonicalResponse D F Z z u ≤ 2*((51/100 : ℝ)+D.e*grid u)-1 := by
  have hp := DirectEnergy.Source.source_prime_bins D F P τ n hτ hheight
  filter_upwards [hp,eventually_gt_atTop (1 : ℝ)] with Z hp hZ
  refine ⟨hZ,?_⟩
  intro d padding hd hd' η idx grid hselected u hulo hcal huhi z hz hzim
  have hsel := hselected
  change _ ∧ _ ∧ _ at hsel
  have hb := hsel.2.1 u
  have hi := (hsel.1 u).2.1
  let a : ℝ := 51/100+D.e*grid u
  have ha : (51/100 : ℝ) ≤ a := hb.1
  have ha' : a ≤ 1 := hb.2.1.trans (by norm_num)
  have hnext := hb.2.2.2.2.1
  have hν : 0 ≤ 2*a-1 := by linarith
  refine ⟨LowActual.response_nonneg _ _ _ _,?_⟩
  apply (LowActual.response_le_iff_amplitudes D.length _ hZ
    (responsePayment_pos D (zero_lt_one.trans hZ)) (fun j => (D.slots_pos j).le)
    (fun _ => sq_nonneg _) (fun j hj => False.elim ((D.slots_pos j).ne' hj)) hν).2
  intro j
  have hphase := hp d hd hd' η u hulo hcal huhi a (idx u) hi ha ha' hnext (z j) (hz j) (hzim j) j
  exact phase_squared_paid D hZ (D.slots_pos j).le (length_le_total D j) hphase.2.1 _ hphase.2.2.2.1

end QRH.Cycle092.MediumWitness
