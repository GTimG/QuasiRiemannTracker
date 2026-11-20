/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.DirectAll
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000
namespace QRH.Cycle092.Direct
open QRH.Cycle090 QRH.Coverage QRH.PhysicalCertificate

/-- All ten authentic E29 guards with the genuine .72 paired-source endpoint,
the original restricted native continuation, and its original comparison arm. -/
def pairedGuard {K : Type*} [Field K] (i : Fin 10) (d p g₀ g₁ : K) : K :=
  let V := 5/6-d
  let k := 1-p*(1+2*g₁)
  let U := 1-p*(1+6*g₀-4*g₁)
  let J := 3*V+2*d*k
  let T := J+d*U
  let N := (1-d)*J+V*d*U
  match i.val with
  | 0 => k
  | 1 => J
  | 2 => T-J
  | 3 => (12499/10000)*J-T
  | 4 => 2*T-3*(18/25+1/1000000)*J
  | 5 => N-(1-d*(311/400+(1-311/400)*p))*J
  | 6 => N-(1-d*(311/400+2*((1-1/1000000000000)-311/400)*p/(2+1/100000000000)))*J
  | 7 => N-(1-d*(311/400+2*(3/20-1/10000000)*p))*J
  | 8 => N-(1-2*(1757/4000)*d-2*(27/1000)*d*p)*J
  | _ => U*(-2*(1+2*g₁)*d)+(1+6*g₀-4*g₁)*J

theorem pairedGuard_cast (i : Fin 10) (d p g₀ g₁ : ℚ) :
    ((pairedGuard i d p g₀ g₁ : ℚ) : ℝ) = pairedGuard i (d : ℝ) p g₀ g₁ := by
  fin_cases i <;> push_cast [pairedGuard] <;> rfl

def pairedGuardCoefficients (k : Fin 10) (g₀ g₁ : ℚ) (box : Box) (i j : ℕ) : ℚ :=
  Physical.quadraticCoefficients
    (fun d => Physical.quadraticCoefficients (fun p => pairedGuard k d p g₀ g₁) box.vLo box.vHi j)
    box.uLo box.uHi i

theorem pairedGuard_expansion (k : Fin 10) (g₀ g₁ : ℚ) (box : Box) (x y : ℝ) :
    pairedGuard k
      ((box.uLo : ℝ)+((box.uHi : ℝ)-box.uLo)*x)
      ((box.vLo : ℝ)+((box.vHi : ℝ)-box.vLo)*y) g₀ g₁ =
    QRH.Bernstein.value 2 2 (fun i j => (pairedGuardCoefficients k g₀ g₁ box i j : ℝ)) x y := by
  norm_num [QRH.Bernstein.value,QRH.Bernstein.tensorBasis,QRH.Bernstein.basis,
    Finset.sum_range_succ,pairedGuardCoefficients,Physical.quadraticCoefficients]
  simp only [Rat.cast_add,Rat.cast_div,Rat.cast_ofNat,pairedGuard_cast]
  fin_cases k <;> norm_num [pairedGuard] <;> ring

/-- One complete original-source-admissible rectangle contains all E49 direct boxes. -/
def pairedAdmissionBox : Box := ⟨45/128,15/32,7/16,1/2⟩

def contact0 (i : Fin 2) : ℚ := if i.val=0 then 5805911/100000000 else 5805913/100000000
def contact1 (i : Fin 2) : ℚ := if i.val=0 then 3799809/50000000 else 379981/5000000

def pairedAdmissionCheck : Bool :=
  (List.finRange 2).all fun a => (List.finRange 2).all fun b =>
    (List.finRange 10).all fun k =>
      QRH.Bernstein.coefficientsCheck 2 2
        (pairedGuardCoefficients k (contact0 a) (contact1 b) pairedAdmissionBox) (1/1000)

theorem pairedAdmission_checked : pairedAdmissionCheck = true := by decide +kernel

theorem pairedBoxes_in_admission : pairedBoxes.all
    (fun box => decide (Box.Included box pairedAdmissionBox)) = true := by decide +kernel

/-- Each exact contact corner pays the complete actual guard throughout the rectangle. -/
theorem paired_corner_guard {point : Point} (hp : pairedAdmissionBox.Contains point)
    (a b : Fin 2) (k : Fin 10) :
    1/1000 ≤ pairedGuard k point.1 point.2 (contact0 a) (contact1 b) := by
  have hc := List.all_eq_true.mp
    (List.all_eq_true.mp
      (List.all_eq_true.mp pairedAdmission_checked a (List.mem_finRange a))
      b (List.mem_finRange b)) k (List.mem_finRange k)
  have hb := QRH.Bernstein.checked_boxValue_lower_bound 2 2
    (pairedGuardCoefficients k (contact0 a) (contact1 b) pairedAdmissionBox)
    (1/1000) hc (by norm_num [pairedAdmissionBox]) (by norm_num [pairedAdmissionBox])
    hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
  dsimp [QRH.Bernstein.boxValue] at hb
  rw [← pairedGuard_expansion] at hb
  have hu : (pairedAdmissionBox.uLo : ℝ) < pairedAdmissionBox.uHi := by norm_num [pairedAdmissionBox]
  have hv : (pairedAdmissionBox.vLo : ℝ) < pairedAdmissionBox.vHi := by norm_num [pairedAdmissionBox]
  norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at hb
  simpa only [Physical.reconstruct hu,Physical.reconstruct hv] using hb

noncomputable section

def contactWeight0 (g : ℝ) : ℝ := (g-5805911/100000000)/(5805913/100000000-5805911/100000000)
def contactWeight1 (g : ℝ) : ℝ := (g-3799809/50000000)/(379981/5000000-3799809/50000000)

theorem paired_guard_contact_interpolation (k : Fin 10) (d p g₀ g₁ : ℝ) :
    pairedGuard k d p g₀ g₁ =
      (1-contactWeight0 g₀)*
        ((1-contactWeight1 g₁)*pairedGuard k d p (contact0 0) (contact1 0)+
          contactWeight1 g₁*pairedGuard k d p (contact0 0) (contact1 1))+
      contactWeight0 g₀*
        ((1-contactWeight1 g₁)*pairedGuard k d p (contact0 1) (contact1 0)+
          contactWeight1 g₁*pairedGuard k d p (contact0 1) (contact1 1)) := by
  fin_cases k <;> norm_num [pairedGuard,contactWeight0,contactWeight1,contact0,contact1] <;> ring

/-- All ten actual guards hold for every real contact coefficient in the
certified enclosures, not just the four rational corners. -/
theorem paired_admission_real {point : Point} (hp : pairedAdmissionBox.Contains point)
    {g₀ g₁ : ℝ}
    (hg₀ : 5805911/100000000 ≤ g₀) (hg₀' : g₀ ≤ 5805913/100000000)
    (hg₁ : 3799809/50000000 ≤ g₁) (hg₁' : g₁ ≤ 379981/5000000) (k : Fin 10) :
    1/1000 ≤ pairedGuard k point.1 point.2 g₀ g₁ := by
  have hw0 : 0 ≤ contactWeight0 g₀ ∧ contactWeight0 g₀ ≤ 1 := by
    norm_num [contactWeight0] at *; constructor <;> linarith
  have hw1 : 0 ≤ contactWeight1 g₁ ∧ contactWeight1 g₁ ≤ 1 := by
    norm_num [contactWeight1] at *; constructor <;> linarith
  have h00 := paired_corner_guard hp 0 0 k
  have h01 := paired_corner_guard hp 0 1 k
  have h10 := paired_corner_guard hp 1 0 k
  have h11 := paired_corner_guard hp 1 1 k
  have hl : 1/1000 ≤ (1-contactWeight1 g₁)*pairedGuard k point.1 point.2 (contact0 0) (contact1 0)+
      contactWeight1 g₁*pairedGuard k point.1 point.2 (contact0 0) (contact1 1) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1-contactWeight1 g₁) (sub_nonneg.mpr h00),
      mul_nonneg hw1.1 (sub_nonneg.mpr h01)]
  have hh : 1/1000 ≤ (1-contactWeight1 g₁)*pairedGuard k point.1 point.2 (contact0 1) (contact1 0)+
      contactWeight1 g₁*pairedGuard k point.1 point.2 (contact0 1) (contact1 1) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1-contactWeight1 g₁) (sub_nonneg.mpr h10),
      mul_nonneg hw1.1 (sub_nonneg.mpr h11)]
  rw [paired_guard_contact_interpolation]
  have hl' := mul_le_mul_of_nonneg_left hl (by linarith : 0 ≤ 1-contactWeight0 g₀)
  have hh' := mul_le_mul_of_nonneg_left hh hw0.1
  nlinarith

/-- Every actual original E49 terminal satisfies the full real E29 admission. -/
theorem all_actual_E49_admitted {index : Fin 57} {leaf : DirectLeaf}
    (hm : leaf ∈ (initialAt index).directRecords) (hr : leaf.route="E49_top")
    {point : Point} (hp : leaf.box.Contains point) {g₀ g₁ : ℝ}
    (hg₀ : 5805911/100000000 ≤ g₀) (hg₀' : g₀ ≤ 5805913/100000000)
    (hg₁ : 3799809/50000000 ≤ g₁) (hg₁' : g₁ ≤ 379981/5000000) (k : Fin 10) :
    1/1000 ≤ pairedGuard k point.1 point.2 g₀ g₁ := by
  obtain ⟨_,box,hbox,hin⟩ := pairedTreeCheck_sound _ _ (actual_initial_paired_check index) hm hr
  have hh := of_decide_eq_true (List.all_eq_true.mp pairedBoxes_in_admission box hbox)
  exact paired_admission_real (Box.contains_of_included hh (Box.contains_of_included hin hp))
    hg₀ hg₀' hg₁ hg₁' k
end
end QRH.Cycle092.Direct
#print axioms QRH.Cycle092.Direct.all_actual_E49_admitted
