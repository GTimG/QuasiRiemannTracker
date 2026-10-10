import WeightedQRH.NumeratorSourceScalar
import WeightedQRH.HighRows.WeightedSourceCellGeometry

/-! The calibrated scalar bound on the literal external source rectangle. -/
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.WeightedHighFinalAssembly
open ProbeFinalAssembly ProbeHighRowFamily HeckeFamily ProbePhysical HeckeInverseAmplification

theorem weighted_source_scalar_on_rows {Δ : ℝ}
    (D : WeightedQRH.HighParameters.HighData Δ) (F : WeightedSourceData D.toMomentData) :
    ∃Cs : ℝ,0 < Cs ∧ ∀(η : Character) (rows : Finset FreeRow) (Z τ d a : ℝ) (i : ℕ),
      0 < Z → 2 < Z^τ → (51/100:ℝ) ≤ a → a ≤ 7/8 →
      (∀u∈rows,Z^(d-2*D.t) ≤ rowNorm u) →
      (∀u∈rows,rowNorm u ≤ Z^d) →
      (∀u∈rows,detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        (3*(i+1:ℕ)*Z^τ) < a+2*D.e) →
      ∀q∈WeightedQRH.FullWContour.szRectangle ((3*i+1:ℕ)*Z^τ),∀u∈rows,
        ‖frequencyWeight ((17/50:ℂ)+q.2*Complex.I) ⟨u.val,u.property.1⟩*
          WeightedQRH.Numerator.numeratorFreeRowScalar F.S F.exclusions F.maximal η u
            ((((a+16*D.e):ℝ):ℂ)+q.1*Complex.I) ((17/50:ℂ)+q.2*Complex.I)‖ ≤
          Cs*(η.modulus.absNorm:ℝ)^(2*D.eps)*(3+((3*i+1:ℕ):ℝ)*Z^τ)^(2*D.eps)*
            (Z^d)^(2*D.eps)*(Z^d)^(-(17/50:ℝ))*Z^((17/25)*D.t) := by
  obtain ⟨Cs,hCs,hbound⟩ := WeightedQRH.Numerator.source_frequency_scalar_bound
    D.e D.eps D.e_pos D.e_small D.eps_pos F.S F.exclusions F.maximal
  refine ⟨Cs,hCs,?_⟩
  intro η rows Z τ d a i hZ hB ha ha' hfreq hupper hnext q hq u hu
  have hH : ((3*i+1:ℕ):ℝ)*Z^τ ≤ ((3*i+2:ℕ):ℝ)*Z^τ := by
    push_cast
    have hp : 0 ≤ Z^τ := Real.rpow_nonneg hZ.le _
    nlinarith
  exact hbound η u (rayCubeFamily F.modulus ⊤ le_top u)
    (Z^τ) a (((3*i+1:ℕ):ℝ)*Z^τ) i hB ha (by linarith) hH (hnext u hu)
    ((((a+16*D.e):ℝ):ℂ)+q.1*Complex.I) ((17/50:ℂ)+q.2*Complex.I)
    (by simp) (by norm_num) (by simpa using hq.1)
    Z d D.t (Z^d) hZ rfl (hfreq u hu) (hupper u hu)

end SevenEighths.WeightedHighFinalAssembly
end
end OAI
