/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Fully selected amplitude-class packet at variable physical source cost.
Adapted from PR137 AmplitudeClass (Sil and predecessor authors, Apache-2.0).
The full original class is counted; only the selection mean masks error slots. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveWholeSlots
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.JointDetector.BoundaryPhysical.PhysicalDirect.AmplitudeClass

set_option autoImplicit false
set_option maxHeartbeats 900000
namespace Qrh.TwoSlot.AnchorContinuum.PositiveTransport
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
open QRH.Record1252270103Return
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect
open Cycle25.Weighted.Numerator Cycle25.Numerator
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical
open HeckeFamily HeckeInverseAmplification Cycle25DetectorRowCount
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
variable {line : Qrh.TwoSlot.AnchorZeroLoss.Affine.Line}
variable [Geometry.Parameters]
variable [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.CoreBounds]
variable [Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCountScheme line]

theorem amplitude_class_packet_with_cost (A : ChosenData) {cost : ℝ}
    (hcost : 0 ≤ cost) (hcostmax : cost ≤ 1/1000000000)
    (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hkbeta : 2*HeckeZeroSupremum.beta-1 ≤ A.D.momentKappa)
    (bPhi error : ℝ) (haff : 0 < error)
    (hsPhi : Function.support (CenteredMomentDetectorPlainFiberSource.radialMajorant : ℝ → ℂ) ⊆ Set.Iic bPhi)
    (di : ℕ) (control : Finset (ℕ×ℕ)) (Ci : ℝ) (hCi : 0 < Ci)
    (hinput : ∀ᶠ U : ℝ in atTop,
      affineAtFace (PositiveSource.physicalFace cost) A bPhi error U di control Ci)
    (J : Finset (Fin A.D.N)) :
    ∃ degree : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop,
      1 < U ∧ ∀ Z d : ℝ, 1 < Z → (3/4:ℝ) ≤ d → d ≤ 2*Geometry.y → U = Z^d →
      ∀ (η : Character) (x z : ℂ) (a height : ℝ), (51/100:ℝ) ≤ a → a ≤ 7/8 →
      x.re = a+16*A.D.e → z.re = 17/50 → 0 ≤ height → |z.im| ≤ height →
      ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      (∀ u ∈ rows, (rowCharacter A.F.S A.F.exclusions.prime u).residue ≠ 1) →
      (∀ P : ∀ i : J, sourcePrimePool A.F Z i.val, Function.Injective (fun i => (P i).val)) →
      (∀ i P, P ∈ sourcePrimePool A.F Z i → IsCoprime P.val η.modulus) →
      (∀ i : J, sourcePrimePool A.F Z i.val) →
      ∀ bin : BinLabel (Finset.univ : Finset (Fin A.D.N)) ((2*a-1)/2) A.D.t,
      let Q := fun (u : FreeRow) k => HeckePrimeRow.canonicalPrimeAmplitude A.F.modulus ⊤ u.val
        A.F.W 2 (Z^(A.D.length k)) z
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) A.D.t A.D.t_pos
        (fun k => A.D.length k/d) Q bin
      let main := (Finset.univ : Finset (Fin A.D.N)) \ J
      let q := weightedMean Finset.univ (fun k => A.D.length k/d)
        (maskedGain main (binValue Finset.univ ((2*a-1)/2) A.D.t bin))
      rows'.Nonempty → ∀ R Ccount : ℝ, 1 ≤ Ccount → (rows'.card : ℝ) ≤ Ccount*U^R →
      (∀ u ∈ rows', ∀ k, ‖Q u k‖ ≤ (Z^(A.D.length k))^
        (HeckePrimeAmplitudeBins.amplitude (Z^(A.D.length k)) ((2*a-1)/2) A.D.t (Q u k)+A.D.t)) →
      (∑ i : rows', ‖labelPolynomialPacket A.F.S A.F.exclusions η i.val
        (fun k : J => sourcePrimePool A.F Z k.val) (fun k => source_prime_pool_outside A.F Z k.val)
        (fun _ => A.F.W) (fun k => Z^(A.D.length k.val)) x z A.F.W (U^(Geometry.y/d))*
        (∏ k ∈ main, Q i.val k)‖) ≤
      C*Ccount*(1+height)^degree*(U^(Geometry.y/d))^(-(1/2:ℝ))*
        (∏ k : J, (Z^(A.D.length k.val))^(-(4/25:ℝ)))*
        U^(A.D.t+q*(Geometry.ell/d)-q*Selection.zeroCapacity cost d/2+
          (3*R+1+A.D.t+error+A.D.t)/4+(2*a-1)*Cycle25.sourceMesh A.D.t/4+
          (2*a-1)*(A.D.t+A.D.t)/2+A.D.t*(Geometry.ell/d)) := by
  obtain ⟨degree,C,hC,hbin⟩ := selected_source_packet_with_cost A hcost hcostmax hbeta hkbeta
    bPhi error haff hsPhi di control Ci hCi hinput J
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [hbin] with U hbin
  refine ⟨hbin.1,?_⟩
  intro Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hheight hzim
    rows hrows hrow hdis hη Pbase bin
  dsimp only
  let Q := fun (u : FreeRow) k => HeckePrimeRow.canonicalPrimeAmplitude A.F.modulus ⊤ u.val
    A.F.W 2 (Z^(A.D.length k)) z
  let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) A.D.t A.D.t_pos
    (fun k => A.D.length k/d) Q bin
  let main := (Finset.univ : Finset (Fin A.D.N)) \ J
  let q := weightedMean Finset.univ (fun k => A.D.length k/d)
    (maskedGain main (binValue Finset.univ ((2*a-1)/2) A.D.t bin))
  intro hne R Ccount hCc hcard hupper
  have hdelta : 0 ≤ 2*a-1 := by linarith
  have hdeltahi : 2*a-1 ≤ (3/4:ℝ) := by linarith
  have hU0 : 0 < U := zero_lt_one.trans hbin.1
  have hsub : rows' ⊆ rows := Finset.filter_subset _ _
  have ht := A.D.t_pos
  have hdrange : d ∈ Set.Icc (1/200:ℝ) 1 := by
    constructor <;> linarith [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.CoreBounds.ly_coarse.2]
  have hselection (j : ℕ) := class_main_selection A cost Z d
    (2*((j:ℝ)*A.D.t+A.D.t+A.D.t)) (2*a-1) hZ hdrange hdelta z rows main bin hne
  have hq0 : 0 ≤ q := (hselection 0).1
  have hqtop : q ≤ (2*a-1)/2 := (hselection 0).2.1
  have hchoices (j : ℕ) : ∃ selected : Finset (Fin A.D.N), selected ⊆ main ∧
      (∑ k ∈ selected, A.D.length k/d) ≤
        Selection.scheduledCapacity cost d (2*((j:ℝ)*A.D.t+A.D.t+A.D.t)) ∧
      ∀ u ∈ rows',
        (Z^d)^(2*q*Selection.scheduledCapacity cost d (2*((j:ℝ)*A.D.t+A.D.t+A.D.t))-
          (2*a-1)*Cycle25.sourceMesh A.D.t) ≤ ‖∏ k ∈ selected, Q u k‖^2 ∧
        ((∀ k, ‖Q u k‖ ≤ (Z^(A.D.length k))^
          (HeckePrimeAmplitudeBins.amplitude (Z^(A.D.length k)) ((2*a-1)/2) A.D.t (Q u k)+A.D.t)) →
          ‖∏ k ∈ main, Q u k‖ ≤ (Z^d)^(q*(Geometry.ell/d)+A.D.t*(Geometry.ell/d))) :=
    (hselection j).2.2
  choose selected hselectedMain hcapacity hselected using hchoices
  let Pmain (i : rows') := ∏ k ∈ main, Q i.val k
  let Pnorm (i : rows') := Pmain i/(((U^(A.D.t*(Geometry.ell/d)):ℝ)):ℂ)
  have hfull (i : rows') : ‖Pnorm i‖ ≤ U^(q*(Geometry.ell/d)) := by
    apply upper_bin_normalized (Pmain i) U (q*(Geometry.ell/d)) (A.D.t*(Geometry.ell/d)) hU0
    rw [hUZ]
    exact (hselected 0 i.val i.property).2 (hupper i.val i.property)
  have hcap (j : ℕ) (_ : j ∈ Finset.range (coefficientBoxCount A.D.t+1)) :
      (∑ k ∈ selected j, A.D.length k/d) ≤
        Selection.scheduledCapacity cost d (2*((j:ℝ)*A.D.t+A.D.t+A.D.t)) := hcapacity j
  have hlow (j : ℕ) (_ : j ∈ Finset.range (coefficientBoxCount A.D.t+1)) (i : rows') :
      U^(q*Selection.scheduledCapacity cost d (2*((j:ℝ)*A.D.t+A.D.t+A.D.t))-
        (2*a-1)*Cycle25.sourceMesh A.D.t/2) ≤ ‖∏ k ∈ selected j, Q i.val k‖ := by
    rw [hUZ]
    exact squared_selected_lower (Z^d) q _ (2*a-1) (Cycle25.sourceMesh A.D.t) _
      (by rw [←hUZ]; exact hU0) (hselected j i.val i.property).1
  have hcrude (j : ℕ) (_ : j ∈ Finset.range (coefficientBoxCount A.D.t+1)) (i : rows') :
      ‖∏ k ∈ selected j, Q i.val k‖ ≤ U := by
    rw [hUZ]
    exact selected_product_crude A Z d (2*a-1) hZ (by linarith) hdelta hdeltahi (selected j)
      (Q i.val) (hupper i.val i.property)
  have hb := hbin.2 Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hheight hzim
    rows' (fun u hu => hrows u (hsub hu)) (fun u hu => hrow u (hsub hu)) hdis hη Pbase
    selected Pnorm q R ((2*a-1)*Cycle25.sourceMesh A.D.t/2) Ccount
    hq0 hqtop hCc hcard hfull hcap hlow hcrude
  have hrestore := restore_upper_bin_loss Finset.univ
    (fun i : rows' => labelPolynomialPacket A.F.S A.F.exclusions η i.val
      (fun k : J => sourcePrimePool A.F Z k.val) (fun k => source_prime_pool_outside A.F Z k.val)
      (fun _ => A.F.W) (fun k => Z^(A.D.length k.val)) x z A.F.W (U^(Geometry.y/d)))
    Pmain U (A.D.t*(Geometry.ell/d))
    (A.D.t+q*(Geometry.ell/d)-q*Selection.zeroCapacity cost d/2+
      (3*R+1+A.D.t+error+A.D.t)/4+((2*a-1)*Cycle25.sourceMesh A.D.t/2)/2+(2*a-1)*(A.D.t+A.D.t)/2)
    (C*Ccount*(1+height)^degree*(U^(Geometry.y/d))^(-(1/2:ℝ))*
      (∏ k : J, (Z^(A.D.length k.val))^(-(4/25:ℝ)))) hU0 hb
  have he : ((2*a-1)*Cycle25.sourceMesh A.D.t/2)/2 = (2*a-1)*Cycle25.sourceMesh A.D.t/4 := by ring
  simpa only [he,Pmain] using hrestore

end
end Qrh.TwoSlot.AnchorContinuum.PositiveTransport
#print axioms Qrh.TwoSlot.AnchorContinuum.PositiveTransport.amplitude_class_packet_with_cost
