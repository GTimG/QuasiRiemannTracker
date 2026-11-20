/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact conversion from the genuine conductor exponent d to source radius V.
The physical kernels and lengths persist; d-V is charged, never discarded. -/
import Candidate.C092.transport.MediumReplaceSourceP4

set_option autoImplicit false
noncomputable section
open OAI OAI.SevenEighths HeckeFamily HeckeDetectorSupportedWitness
namespace QRH.Cycle092.MediumReplace.Source

def radialLength (d V length : ℝ) : ℝ := d*length/V

theorem radialLength_exact (d V length : ℝ) (hV : V ≠ 0) :
    V*radialLength d V length=d*length ∧
      radialLength d V length-length=((d-V)/V)*length := by
  constructor <;> unfold radialLength <;> field_simp <;> ring

theorem radialLength_scale (Z d V length : ℝ) (hZ : 0 < Z) (hV : V ≠ 0) :
    (Z^d)^length=(Z^V)^(radialLength d V length) := by
  rw [←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le,(radialLength_exact d V length hV).1]

/-- P4's actual witness lower exponent is identical in radial coordinates.
The kernel length becomes m_V=d*m/V, rather than silently staying m. -/
theorem P4_radial_exponent (nu y d V m error : ℝ) (hV : V ≠ 0) :
    nu*(y-d*m)+error=nu*(y-V*radialLength d V m)+error := by
  rw [(radialLength_exact d V m hV).1]

/-- The ordinary cap and the inverse cap both retain their exact conductor
collars. The ordinary length increases by at most ((d-V)/V)*(1/2+75epsilon).
The inverse length increase is at most ((d-V)/V)*(cutoff+epsilon). -/
theorem supported_radial_collars {Label : Type*} {χ : Label → Character}
    {Z d V a ε cutoff T allowance : ℝ} {i : ℕ}
    (w : SupportedWitness χ (Z^d) a ε cutoff T allowance i)
    (hV : 0 < V) (hVd : V ≤ d) :
    0 ≤ radialLength d V w.m-w.m ∧
      radialLength d V w.m-w.m ≤ ((d-V)/V)*(1/2+75*ε) ∧
      radialLength d V w.m ≤ (1/2+75*ε)+((d-V)/V)*(1/2+75*ε) ∧
      radialLength d V w.r-w.r ≤ ((d-V)/V)*(cutoff+ε) := by
  have hoff : 0 ≤ (d-V)/V := div_nonneg (sub_nonneg.mpr hVd) hV.le
  have hm := (radialLength_exact d V w.m hV.ne').2
  have hr := (radialLength_exact d V w.r hV.ne').2
  have hmb := mul_le_mul_of_nonneg_left w.plain_length_upper hoff
  have hrb := mul_le_mul_of_nonneg_left w.inverse_length_upper hoff
  refine ⟨?_,?_,?_,?_⟩
  · rw [hm];exact mul_nonneg hoff w.plain_length_lower
  · rw [hm];exact hmb
  · linarith [w.plain_length_upper]
  · rw [hr];exact hrb

/-- The complete original supported kernel, including zero, profile and signed
height, is unchanged when its physical length is expressed in V units. -/
theorem supported_plain_radial_scale {Label : Type*} {χ : Label → Character}
    {Z d V a ε cutoff T allowance : ℝ} {i : ℕ}
    (w : SupportedWitness χ (Z^d) a ε cutoff T allowance i)
    (hZ : 0 < Z) (hV : V ≠ 0) :
    QRH.Cycle092.SignedEnergy.actualPlain w =
      HeckeDyadic.polynomial (χ w.label) false HeckeDetectorDyadicProfiles.positiveAnnular
        ((Z^V)^(radialLength d V w.m)) w.zero.re (2*Real.pi*w.nu-w.zero.im) := by
  unfold QRH.Cycle092.SignedEnergy.actualPlain
  rw [radialLength_scale Z d V w.m hZ hV]

end QRH.Cycle092.MediumReplace.Source
#print axioms QRH.Cycle092.MediumReplace.Source.radialLength_exact
#print axioms QRH.Cycle092.MediumReplace.Source.supported_radial_collars
#print axioms QRH.Cycle092.MediumReplace.Source.supported_plain_radial_scale
