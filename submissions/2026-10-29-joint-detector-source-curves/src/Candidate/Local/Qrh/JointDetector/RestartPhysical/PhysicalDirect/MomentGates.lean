/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Restart return: h < .813, y < .473, ell < .173, row fee 1e-9.
All numerical proof obligations are re-elaborated; inherited notices follow. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Adapted for the fine-chain return: h < .810, floor reserve 1/10000.
All inherited notices follow unchanged; upstream source files are unmodified. -/
/- Repeated marks: fork of Collet's generic return module PhysicalDirect.MomentGates (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Literal retained source Batch moments at the selected cutoff. Apache-2.0.
Adapted from Gao Target830 source moment interfaces; all moment sums remain genuine. -/
/- Modified by Sil (2026-10-26): forked into QRH.SilDensitySplit.Return (namespaces and imports renamed);
re-elaborated against the widened coarse box `BoundsN` (873/1000<θ, h<806/1000, ell<171/1000) and,
where used, the physical slot cap as the `PhysicalSchedule` field `cap`. -/
import Candidate.Local.Qrh.JointDetector.RestartPhysical.Schedule
import Candidate.Local.Qrh.JointDetector.RestartPhysical.PhysicalDirect.CountParameters
import Candidate.Local.Qrh.JointDetector.RestartPhysical.PhysicalDirect.Data
import Submissions.hailey_collet_1252270103.Cycle25.Assembly.Count.SourceMomentInput
set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 200000
open scoped Classical BigOperators
open Filter Set OAI OAI.SevenEighths
open QRH.Record1252270103Return

namespace Qrh.JointDetector.RestartPhysical.Return.GenericPhysical.PhysicalDirect
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
variable [Geometry.Parameters] [Qrh.JointDetector.RestartPhysical.Return.Geometry.BoundsN] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
open QRH.Record12518109Count
open QRH.Record1252270103Return.GenericCount
open ProbePhysical ProbeHighRowFamily HeckeFamily HeckeInverseAmplification HeckeDetectorBatch HeckeDetectorRawFiber
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
def SourceMomentsAt {N : ℕ} (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (rows : Finset FreeRow) (ell : Fin N→ℝ) (W : Fin N→ℝ→ℂ)
    (Z d a ε τ dmax b slotMesh binWidth : ℝ) (i : ℕ) (z : ℂ)
    (κplain C height εm : ℝ) (counts : CountParameters M H εm) : Prop :=
  ∀q : ℝ,∀B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N)
      (Z^d) a ε (GenericCount.selectedCutoff κplain (2*a-1) (q/(2*a-1))) (Z^τ) ((Z^d)^(τ/(2*dmax))) i,
    B.rows⊆rows → B.data=sourceMomentData M H hH S hS η →
    B.reverse=sourceMomentReverse M H → B.slots=Finset.univ →
    B.widths=(fun j=>ell j/d) → B.profile=W → B.upper=(fun _=>b) → B.external=(fun _=>z) →
    B.mesh=slotMesh → B.binWidth=binWidth →
    (∀u∈B.rows,∀j,B.family u j=sourceDetectorFamily S hS η u (rayCubeFamily M H hH u) j) →
    ∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
      Cycle25DetectorRawFiber.Moments (B.fiber bin j J K hne) κplain counts.co counts.κo C height εm ∧
      Cycle25DetectorRawFiber.Moments (B.fiber bin j J K hne) scheme.naturalκ counts.ca counts.κa C height εm ∧
      ∀ w∈scheme.windows, AffineMarkedMoment (B.fiber bin j J K hne) w.face C height εm


def SourceMomentBound (D : BaselineData) (F : QRH.Record1252270103Return.GenericPhysical.SourceData)
    (counts : CountParameters F.modulus ⊤ D.t) (η : Character) (Z τ C height : ℝ) : Prop :=
  ∀ rows : Finset FreeRow, ∀ d a : ℝ, (1/200:ℝ)≤d → d≤7/8 → 51/100<a → a≤7/8 →
    (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
      (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-D.t)) →
    ∀i : ℕ, ∀z : ℂ, z.re=17/50 → |z.im|≤height →
    SourceMomentsAt F.modulus ⊤ le_top F.S F.exclusions.prime η rows D.length
      (fun _ y=>(F.w y:ℂ)) Z d a D.ε τ (7/8) 2 D.t D.t i z D.momentKappa C height D.t counts
end Qrh.JointDetector.RestartPhysical.Return.GenericPhysical.PhysicalDirect
