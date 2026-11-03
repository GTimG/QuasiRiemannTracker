/-
Historical contribution by LW56e2, Apache-2.0.
Source: https://github.com/LW56e2/quasi-riemann-improved
Commit: b83dbbd914c5751acf9bc3389cde58970437278f
Original path: lean/Transport/PhysicalHigh/MomentBound.lean
Original SHA-256: 7e5762f6a373b8c484db3e3ab701657648cb9e0ec74e4717263a6ebf7f78f60e
Tracker adaptation: import modules moved under Submissions.lw56e2_parameter_refinement;
OpenAI imports use the openai-baseline dependency; RH.Transport renamed LW56e2.Transport.
Original proof bodies and source attribution otherwise retained.
-/
import Submissions.lw56e2_parameter_refinement.Transport.PhysicalHigh.TunedData
import Submissions.lw56e2_parameter_refinement.Transport.PhysicalHigh.FixedSource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyMomentInput

namespace LW56e2.Transport.PhysicalHigh
noncomputable section
open scoped Classical
open Filter
open OAI OAI.SevenEighths
open HeckeFamily ProbeFinalAssembly ProbeHighRowFamily HeckeInverseAmplification

/-- Actual moment fields for all row subsets needed by the central partition. -/
def TunedSourceMomentBound {Δ : ℝ} {seed : Parameters.HighData Δ} (F : SourceData seed)
    {Kmin : ℕ} {allowance : ℝ} (D : TunedData Kmin allowance)
    (counts : CountParameters F.modulus ⊤ reservedLoss)
    (η : Character) (Z τ C height : ℝ) : Prop :=
  ∀rows : Finset FreeRow,(∀u∈rows,Z^(1/100:ℝ)≤rowNorm u)→
  ∀d : ℝ,(1/200:ℝ)≤d→∀a dmax slotMesh binWidth : ℝ,∀i : ℕ,∀z : ℂ,
  z.re=17/50→|z.im|≤height→
  SourceMomentsAt F.modulus ⊤ le_top F.S F.exclusions.prime η rows D.ell
    (fun _ y=>(F.w y:ℂ)) Z d a D.P.ε τ dmax 2 slotMesh binWidth i z 0
    (if 2*a-1≤5/6 then counts.cB else counts.cH)
    (if 2*a-1≤5/6 then counts.kB else counts.kH) C height reservedLoss


end
end LW56e2.Transport.PhysicalHigh
