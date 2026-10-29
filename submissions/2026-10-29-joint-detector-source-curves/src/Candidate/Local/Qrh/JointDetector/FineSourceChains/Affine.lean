/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
/- The source gates retain Sil and OpenAI's generic source-step attribution. -/
import Candidate.Local.Qrh.JointDetector.FinePointwiseLedger

namespace Qrh.JointDetector.FineSourceChains
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open QRH.SilDensitySplit QRH.SilDensitySplit.Hybrid

/-- Endpoint positivity proves a uniform reserve for the whole affine interval. -/
theorem affine_unif {a b t : ℝ} (ht : 0 < t)
    (ha : 0 < a) (hb : 0 < a+b*t) :
    UnifPos (fun v => a+b*v) 0 t := by
  refine ⟨min a (a+b*t), lt_min ha hb, ?_⟩
  intro v hv0 hv1
  by_cases h : 0 ≤ b
  · exact (min_le_left _ _).trans (by nlinarith)
  · exact (min_le_right _ _).trans (by nlinarith)

def phi : ℝ := 999999/1000000
def amp : ℝ := 1/5
def cap : ℝ := 1/10
def density (B0 L0 L : ℝ) : ℝ :=
  FinePointwiseLedger.dens phi B0 L0 L amp 0 0

def intercepts (B0 L0 B L : ℝ) : Fin 13 → ℝ :=
  let s := cross B0 L0 B L
  let q := density B0 L0 L
  let k := AdaptivePrice.k q
  ![q-FinePointwisePrice.q0, (7/10)-q, (1/10),
    cap-s, s,
    k-q*(B-L*s)-FinePointwisePrice.amplitudeFloor*s,
    (25/24)-(B-L*s), (625/486)-(B-L*s)-3*s,
    1-B+(L-2)*s,
    (1/20)+(3/2)*(1-B)+((3/2)*L-(5/2))*s,
    1-B+(L-1)*s, (1/3)-2*s, amp]

def slopes (B0 L0 B L : ℝ) : Fin 13 → ℝ :=
  let q := density B0 L0 L
  let k := AdaptivePrice.k q
  ![0, 0, -6*amp, -6*cap*amp-1+amp, 1-amp,
    -6*amp*k+q*L-FinePointwisePrice.amplitudeFloor*(1-amp)+amp,
    -(25/4)*amp+L, -(625/81)*amp+L-3*(1-amp),
    L-2-(9/2)*amp, (3/2)*L-(5/2)-(9/2)*amp,
    L-1-4*amp, -2-3*amp, 0]

/-- These are exact rational endpoint facts, not tests at sampled widths. -/
def EndpointGates (B0 L0 B L : ℝ) : Prop :=
  ∀ i : Fin 13, 0 < intercepts B0 L0 B L i ∧
    0 < intercepts B0 L0 B L i + slopes B0 L0 B L i*(cap-cross B0 L0 B L)

theorem gates_of_endpoints {B0 L0 B L : ℝ}
    (ht : 0 < cap-cross B0 L0 B L)
    (he : 0 < densE B0 L0 L amp 0 0)
    (hc : EndpointGates B0 L0 B L) :
    FinePointwiseLedger.Gates phi B0 L0 cap B L cap amp 0 := by
  have hd (v : ℝ) : FinePointwiseLedger.dens phi B0 L0 L amp 0 v = density B0 L0 L := by
    simp [density, FinePointwiseLedger.dens, AdaptiveLedger.dens, densE]
  have hq : density B0 L0 L ∈ Set.Icc FinePointwisePrice.q0 (7/10:ℝ) := by
    have h0 := (hc 0).1
    have h1 := (hc 1).1
    simp [intercepts] at h0 h1
    exact ⟨by linarith, by linarith⟩
  have hf := FinePointwisePrice.slope_flat hq
  have hu (i : Fin 13) :
      UnifPos (fun v => intercepts B0 L0 B L i+slopes B0 L0 B L i*v)
        0 (cap-cross B0 L0 B L) := affine_unif ht (hc i).1 (hc i).2
  have h0 : UnifPos (FinePointwiseLedger.gQFloor phi B0 L0 L amp 0)
      0 (cap-cross B0 L0 B L) := by
    convert hu 0 using 1
    funext v
    simp [intercepts, slopes, FinePointwiseLedger.gQFloor, hd]
  have h1 : UnifPos (FinePointwiseLedger.gQUpper phi B0 L0 L amp 0)
      0 (cap-cross B0 L0 B L) := by
    convert hu 1 using 1
    funext v
    simp [intercepts, slopes, FinePointwiseLedger.gQUpper, hd]
  refine { phi_mem := by norm_num [phi]
           width_pos := ht
           sel_den_pos := by intros; norm_num
           dens_den_pos := by intros; simpa [densE] using he
           q_floor := h0
           q_upper := h1
           H_lower := ?_
           retained_cap := ?_
           retained_width := ?_
           high_at_q := ?_
           high_flat := ?_
           high_curved := ?_
           principal_reference := ?_
           second_reference := ?_
           second_diagonal := ?_
           reference_upper_positive := ?_
           selection_monotonicity := ?_ }
  · convert hu 2 using 1
    funext v
    simp [intercepts, slopes, gHLower, packed, sel, cap]
    <;> ring
  · convert hu 3 using 1
    funext v
    simp [intercepts, slopes, gRetainedCap, packed, sel, width]
    <;> ring
  · convert hu 4 using 1
    funext v
    simp [intercepts, slopes, gRetainedWidth, sel, width]
    <;> ring
  · convert hu 5 using 1
    funext v
    simp [intercepts, slopes, FinePointwiseLedger.gHighAtQ, hd, FinePointwiseLedger.highJ, hf, sel, width]
    <;> ring
  · convert hu 6 using 1
    funext v
    simp [intercepts, slopes, FinePointwiseLedger.gHighFlat, sel, width]
    <;> ring
  · convert hu 7 using 1
    funext v
    simp [intercepts, slopes, FinePointwiseLedger.gHighCurved, sel, width]
    <;> ring
  · convert hu 8 using 1
    funext v
    simp [intercepts, slopes, gPrincipal, sel, width]
    <;> ring
  · convert hu 9 using 1
    funext v
    simp [intercepts, slopes, gSecondRef, sel, width]
    <;> ring
  · convert hu 10 using 1
    funext v
    simp [intercepts, slopes, gSecondDiag, sel, width]
    <;> ring
  · convert hu 11 using 1
    funext v
    simp [intercepts, slopes, gRefUpper, sel, width]
    <;> ring
  · convert hu 12 using 1
    funext v
    simp [intercepts, slopes, gSelDeriv]
    <;> ring

end
end Qrh.JointDetector.FineSourceChains
