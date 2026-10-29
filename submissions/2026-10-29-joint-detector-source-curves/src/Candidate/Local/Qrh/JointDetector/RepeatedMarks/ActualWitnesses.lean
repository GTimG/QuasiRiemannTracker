/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.NoSlotMoments
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorClassBudget

namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
open scoped Classical
open Set OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification HeckeDetectorSupportedWitness
open HeckeDetectorWitnessRows HeckeDetectorClassBudget LocalMoment
local notation "O" => HeckeFamily.O

/-- The accepted detector supplies genuine supported witnesses on precisely
our finite free-core rows. Extension outside that finite set is a retraction,
not an additional zero or moment assumption. -/
theorem actual_supported_free_family
    (dmin dmax τ ε e κ η : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*η)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000)
    (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*((22:ℝ)+2)+8*κ+2*η≤ε/2) :
    ∃Z₀ : ℝ,∀Z : ℝ,Z₀≤Z → ∀d : ℝ,dmin≤d → d≤dmax →
    ∀{Label : Type}[Fintype Label](rows : Finset FreeRow),rows.Nonempty →
    ∀(family : rows→Label→Character)(hχ : ∀u j,(family u j).residue≠1),
    ∀(a : ℝ)(i : ℕ),i≤I → 51/100<a → a≤1 →
    (∀u,HeckeDetectorZeros.zeroMaximum (family u) (hχ u) (3*(i+1:ℕ)*Z^τ)<a+2*e) →
    (∀u,a≤HeckeDetectorZeros.zeroMaximum (family u) (hχ u) ((3*i:ℕ)*Z^τ)) →
    (∀u j,(family u j).modulus.absNorm≤Z^d) →
    ∀tstar : ℝ,1≤tstar → tstar≤3/2 →
    ∃χ : FreeRow→Label→Character,
    (∀u : rows,χ u.val=family u) ∧
    Nonempty (∀u : FreeRow,SupportedWitness (χ u) (Z^d) a ε tstar (Z^τ)
      ((Z^d)^(τ/(2*dmax))) i) := by
  obtain ⟨Z₀,hZ₀⟩ := actual_supported_witness_family dmin dmax τ ε e κ η I
    hdmin hdmax hτ hτzero hτheight hε he he' hκ hκ' hη hbudget
  refine ⟨Z₀,?_⟩
  intro Z hZ d hd hd' Label _ rows hne family hχ a i hi ha ha' hnext hcurrent hQ tstar ht ht'
  obtain ⟨w⟩ := hZ₀ Z hZ d hd hd' family hχ a i hi ha ha' hnext hcurrent hQ tstar ht ht'
  obtain ⟨u₀,hu₀⟩ := hne
  let retract := supportedRowRetraction rows ⟨u₀,hu₀⟩
  refine ⟨fun u=>family (retract u),?_,⟨fun u=>w (retract u)⟩⟩
  intro u
  dsimp [retract]
  rw [supportedRowRetraction_mem]

/-- Lower only the real-part demand. The literal detector polynomials,
frequencies, cutoff and full long tail stay unchanged. -/
def lower_supported_slope {Label : Type} {χ : Label→Character}
    {U a ε tstar T allowance : ℝ} {i : ℕ}
    (w : SupportedWitness χ U a ε tstar T allowance i)
    (hU : 1<U) (a₀ : ℝ) (ha₀ : a₀≤a) :
    SupportedWitness χ U a₀ ε tstar T allowance i where
  toWitness := by
    have hr0 : 0≤w.r := by
      rw [w.left_exponent hU]
      exact Real.logb_nonneg hU (one_le_pow₀ (by norm_num))
    have hm0 : 0≤w.m := w.plain_length_lower
    exact {
      label := w.label, zero := w.zero, zero_eq := w.zero_eq,
      zero_lower := ha₀.trans w.zero_lower, zero_height := w.zero_height,
      left := w.left, right := w.right, nu := w.nu, r := w.r, m := w.m,
      nu_bound := w.nu_bound, left_scale := w.left_scale, right_scale := w.right_scale,
      inverse_length_lower := w.inverse_length_lower,
      inverse_length_upper := w.inverse_length_upper,
      plain_length_lower := w.plain_length_lower,
      plain_length_upper := w.plain_length_upper,
      inverse_spike := (Real.rpow_le_rpow_of_exponent_le hU.le
        (show (2*a₀-1)*w.r-2*ε≤(2*a-1)*w.r-2*ε by nlinarith)).trans w.inverse_spike,
      plain_spike := (Real.rpow_le_rpow_of_exponent_le hU.le
        (show (2*a₀-1)*w.m-2*ε≤(2*a-1)*w.m-2*ε by nlinarith)).trans w.plain_spike }
  product_length_lower := w.product_length_lower

/-- Uniform finite zero-height and real-part bins on the actual free rows. -/
theorem finite_buffered_free_bins {Label : Type} [Fintype Label]
    (rows : Finset FreeRow) (χ : FreeRow→Label→Character)
    (hχ : ∀u : rows,∀j,(χ u.val j).residue≠1)
    (T e b : ℝ) (n : ℕ) (hT : 2<T) (he : 0<e) (hn : 0<n)
    (hwidth : (49/100:ℝ)≤(n:ℝ)*e)
    (hzero : ∀u : rows,b+e≤HeckeDetectorZeros.zeroMaximum (χ u.val) (hχ u) T) :
    ∃index : rows→Fin (n+1)×Fin (⌈1/e⌉₊+2),∀u : rows,
      let a : ℝ:=51/100+e*(index u).2.val
      b≤a ∧ a≤1 ∧
      a≤HeckeDetectorZeros.zeroMaximum (χ u.val) (hχ u) (3*((index u).1.val:ℕ)*T) ∧
      HeckeDetectorZeros.zeroMaximum (χ u.val) (hχ u)
        (3*((index u).1.val+1:ℕ)*T)<a+2*e := by
  have hex (u : rows) : ∃p : Fin (n+1)×Fin (⌈1/e⌉₊+2),
      let a : ℝ:=51/100+e*p.2.val
      b≤a ∧ a≤1 ∧
      a≤HeckeDetectorZeros.zeroMaximum (χ u.val) (hχ u) (3*(p.1.val:ℕ)*T) ∧
      HeckeDetectorZeros.zeroMaximum (χ u.val) (hχ u) (3*(p.1.val+1:ℕ)*T)<a+2*e := by
    obtain ⟨i,k,hi,hin,ha,hcurrent,hbin,hnext,_⟩ :=
      HeckeDetectorZeros.exists_actual_buffered_bin (χ u.val) (hχ u) T e hT he n hn hwidth
    have hk : (k:ℝ)≤1/e := (le_div_iff₀ he).2 (by nlinarith [ha])
    have hk' : k≤⌈1/e⌉₊ := by exact_mod_cast hk.trans (Nat.le_ceil (1/e))
    have hk'' : k<⌈1/e⌉₊+2 := by omega
    have hmono := HeckeDetectorZeros.zeroMaximum_mono (χ u.val) (hχ u)
      (show T≤3*(i:ℝ)*T by
        have hi' : (1 : ℝ) ≤ i := by exact_mod_cast hi
        nlinarith)
    refine ⟨(⟨i,by omega⟩,⟨k,hk''⟩),?_,ha,hcurrent,hnext⟩
    have hmon := (hzero u).trans hmono
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using
      (show b≤51/100+e*(k:ℝ) by linarith [hbin])
  exact ⟨fun u=>Classical.choose (hex u),fun u=>Classical.choose_spec (hex u)⟩

end
end Qrh.JointDetector.RepeatedMarks

#print axioms Qrh.JointDetector.RepeatedMarks.actual_supported_free_family
