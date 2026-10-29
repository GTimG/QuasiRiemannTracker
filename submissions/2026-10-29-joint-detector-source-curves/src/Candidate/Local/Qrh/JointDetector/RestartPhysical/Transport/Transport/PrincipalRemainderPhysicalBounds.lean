/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Restart return: h < .813, y < .473, ell < .173, row fee 1e-9.
All numerical proof obligations are re-elaborated; inherited notices follow. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Adapted for the fine-chain return: h < .810, floor reserve 1/10000.
All inherited notices follow unchanged; upstream source files are unmodified. -/
/- Repeated marks: fork of Collet's generic return module Transport.Transport.PrincipalRemainderPhysicalBounds (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Ported from Cycle25.Transport weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/
/- Modified by Sil (2026-10-26): forked into QRH.SilDensitySplit.Return (namespaces and imports renamed);
re-elaborated against the widened coarse box `BoundsN` (873/1000<θ, h<806/1000, ell<171/1000) and,
where used, the physical slot cap as the `PhysicalSchedule` field `cap`. -/
import Candidate.Local.Qrh.JointDetector.RestartPhysical.TransportGeometry
import Candidate.Local.Qrh.JointDetector.RestartPhysical.Transport.Transport.PrincipalRemainderPhysical
import Candidate.Local.Qrh.JointDetector.RestartPhysical.Transport.Transport.PrincipalRemainderBounds
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PrincipalPhysicalRemainder
set_option autoImplicit false
noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [Qrh.JointDetector.RestartPhysical.Return.Geometry.BoundsN]
open scoped Classical BigOperators
open Complex MeasureTheory
namespace Qrh.JointDetector.RestartPhysical.TransportKernel.Transport.Transport.PrincipalPhysical
open OAI OAI.SevenEighths OAI.SevenEighths.ProbePrincipalPhysical
open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds
open PrincipalMellinResidues PrincipalSignalComparison ProbeMellinBoundary ProbePrincipalContours
open Qrh.JointDetector.RestartPhysical.TransportKernel.Transport.Transport.PrincipalFiniteProduct Qrh.JointDetector.RestartPhysical.TransportKernel.Transport.Transport.PrincipalContours
local notation "Id" => Ideal HeckeFamily.O

theorem physical_principal_residue_remainder {K : ℕ}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (c d B : ℝ) (hc : 0<c) (hd : c ≤ d) (hB : 0 ≤ B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (e : ℝ) (he : 0<e) (hehi : e ≤ 1/1000)
    (ha : theta <HeckeZeroSupremum.beta+e) (ha2 : HeckeZeroSupremum.beta+e ≤ 2) :
    letI : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0<C ∧ ∀slotEll : Fin K→ℝ,(∑j,slotEll j)=ell → ∀W : Fin K→ℝ→ℝ,
    (∀j x,0 ≤ W j x ∧ W j x ≤ B) → (∀j,Function.support (W j)⊆Set.Icc c d) →
    ∀T : Fin K→Finset PrimeIdeal,(∀j p,p∈T j→p.val∉S) →
    (∀P:(∀j,T j),Function.Injective (fun j=>(P j).val)) →
    ∀Z : ℝ,1 ≤ Z → (∀j,480 ≤ c*Z^(slotEll j)) → (∀j,(Ideal.absNorm η.modulus:ℝ)<c*Z^(slotEll j)) →
    ‖(∑P:(∀j,T j),(∏j,(W j ((Ideal.absNorm (P j).val.val:ℝ)/Z^(slotEll j)):ℂ))*
        principalRowIntegral η S (fun j=>primaryGenerator (P j).val.val)
          W0 W1 (Z^(lx:ℝ)) (Z^(ly:ℝ)) Z)-
      sourceResidueIntegral W0 W1 (∏p∈S,p) (η.excludePrimes S hS.prime)
        (HeckeZeroSupremum.beta+e) (Z^(lx:ℝ)) (Z^(ly:ℝ)) Z
        (globalClosedCorrection η S)
        (windowMultiplier η Finset.univ T (fun j x=>(W j x:ℂ)) (fun j=>Z^(slotEll j)))‖ ≤
      C/e*Z^(HeckeZeroSupremum.beta-(4+b)/6-1/4000) := by
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hbound⟩ := Qrh.JointDetector.RestartPhysical.TransportKernel.Transport.Transport.PrincipalRemainderBounds.source_remainders_strict_saving η S hS
    (Finset.univ : Finset (Fin K)) c d B hc hd hB W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 e he hehi ⟨ha.le,ha2⟩
  refine ⟨2*C,by positivity,?_⟩
  intro slotEll hell W hW hsupp T hT hdis Z hZ hthreshold hmod
  have hZ0 : 0<Z := by linarith [Qrh.JointDetector.RestartPhysical.TransportKernel.Transport.Transport.theta_bounds]
  have hb := hbound slotEll hell W (fun j _=>hW j) (fun j _=>hsupp j) T (fun j _ p hp=>hT j p hp)
    Z hZ (fun j _=>hthreshold j) (fun j _=>hmod j)
  dsimp only at hb
  have heq := Qrh.JointDetector.RestartPhysical.TransportKernel.Transport.Transport.PrincipalPhysical.principal_physical_pool_ordered η S hS T hT hdis
    (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/Z^(slotEll j)):ℂ)) W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 (Z^(lx:ℝ)) (Z^(ly:ℝ)) Z (HeckeZeroSupremum.beta+e) e
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0 ha (by linarith [Qrh.JointDetector.RestartPhysical.TransportKernel.Transport.Transport.theta_bounds]) (by linarith [Qrh.JointDetector.RestartPhysical.TransportKernel.Transport.Transport.theta_bounds]) he (by linarith [Qrh.JointDetector.RestartPhysical.TransportKernel.Transport.Transport.theta_bounds])
  dsimp only at heq
  have hres (F : ℂ→ℂ) :
      (HeckeReciprocal.regularizedL (fixedSourcePrincipal S hS.prime) 1)^2/6*
        verticalIntegral (HeckeZeroSupremum.beta+e) F=
      verticalIntegral (HeckeZeroSupremum.beta+e) (fun s=>fixedPrincipalResidue (∏p∈S,p)^2/6*F s) := by
    rw [verticalIntegral,verticalIntegral,integral_const_mul]
    dsimp only [fixedPrincipalResidue,fixedPrincipal,fixedSourcePrincipal]
    ring
  rw [heq]
  unfold sourceResidueIntegral windowMultiplier
  rw [hres,add_sub_cancel_right]
  have hn := (norm_add_le _ _).trans (add_le_add hb.1 hb.2)
  change _ ≤ (2*C)/e*Z^(HeckeZeroSupremum.beta-(4+b)/6-1/4000)
  apply hn.trans
  have hCe : C ≤ C/e := (le_div_iff₀ he).mpr (by nlinarith)
  have hzpow : 0 ≤ Z^(HeckeZeroSupremum.beta-(4+b)/6-1/4000) := Real.rpow_nonneg hZ0.le _
  have htwo : (2*C)/e=2*(C/e) := by ring
  rw [htwo]
  nlinarith
end Qrh.JointDetector.RestartPhysical.TransportKernel.Transport.Transport.PrincipalPhysical
end
