/-
Historical contribution by LW56e2, Apache-2.0.
Source: https://github.com/LW56e2/quasi-riemann-improved
Commit: b83dbbd914c5751acf9bc3389cde58970437278f
Original path: lean/Transport/PhysicalLow/LowNominalEnergy.lean
Original SHA-256: dae19b72eab11e9982aedf9671abdd634c798e8cd79481626ed3f1c3c94a130f
Tracker adaptation: import modules moved under Submissions.lw56e2_parameter_refinement;
OpenAI imports use the openai-baseline dependency; RH.Transport renamed LW56e2.Transport.
Original proof bodies and source attribution otherwise retained.
-/
import Submissions.lw56e2_parameter_refinement.Transport.PhysicalLow.LowSelectedBound
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowCentralGeometry

/-!
Transport of OpenAI Detector/LowNominalEnergy.lean, commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb; license: upstream-config/LICENSE.
This is the actual selected inverse-row estimate at a nominal source scale.
-/

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem transport_low_selected_nominal_energy (totalWidth : ℝ) (hE0 : 0≤totalWidth) (hE1 : totalWidth≤1/5) (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤totalWidth)
    (Ck b ε : ℝ) (hCk : 0<Ck) (hε : 0<ε) (hε1 : ε≤1) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(T : Fin K→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
      (∀i P,P∈T i→(Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
    ∀(J : Finset (Fin K))(R : Finset O),
      (∀z∈R,z≠0 ∧ elementNorm z≤Ck*Z^(1-totalWidth-2*lowUnselectedLength ell J))→
    ∀X : ℝ,0<X→Z^(1+lowSelectedLength ell J-ε/2)≤X→X≤Z^(1+lowSelectedLength ell J+ε/2)→
    ∀(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→∀(Y : Fin K→ℝ)(t : ℝ)(σ : RayRing),
      (∑z∈R,‖lowSelectedInverseRow Finset.univ
        (lowSelectedWeight η (fun i=>canonicalSlotSupport (T i)) J W Y t)
        η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J) X t σ z‖^2)≤
        C*(1+‖t‖)^degree*Z^((1-totalWidth-2*lowUnselectedLength ell J)+LW56e2.Transport.Reflected.reflectedLoss totalWidth (lowUnselectedLength ell J)+507*ε) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := transport_low_selected_physical_energy totalWidth hE0 hE1 η S hS hbad K Ck ε hCk hε hε1
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [eventually_low_selected_caps ell hell b ε hε,Filter.eventually_ge_atTop Z₀] with Z hc hZ
  refine ⟨hc.1,?_⟩
  intro T hT hout hdis hnorm J R hR X hX hXlo hXhi W hW Y t σ
  have hd : 0≤lowUnselectedLength ell J := Finset.sum_nonneg (fun i _=>hell i)
  have hs : 0≤lowSelectedLength ell J := Finset.sum_nonneg (fun i _=>hell i.val)
  have hlen := lowLength_sum ell J
  have hd1 : lowUnselectedLength ell J≤totalWidth := by linarith
  have hscap : lowSelectedLength ell J≤totalWidth-lowUnselectedLength ell J := by linarith
  have hscale := lowCentralShift_scale Z X (lowSelectedLength ell J+ε/2) hc.1 hX
  rw [←hscale]
  apply he Z (lowUnselectedLength ell J) (lowSelectedLength ell J+ε/2)
    (lowCentralShift Z X (lowSelectedLength ell J+ε/2)) hZ hd hd1 (by linarith) (by linarith)
    (lowCentralShift_bound Z X (lowSelectedLength ell J) ε hc.1 hX hε.le hXlo hXhi)
    R hR T hT hout hdis J (fun i=>max 1 (b*Z^(ell i.val)))
    (fun i=>le_max_left _ _)
    (fun i P hP=>(hnorm i.val P hP).trans (le_max_right _ _)) (hc.2 J) W hW Y t σ

end SevenEighths.ProbePhysical
end

end OAI
