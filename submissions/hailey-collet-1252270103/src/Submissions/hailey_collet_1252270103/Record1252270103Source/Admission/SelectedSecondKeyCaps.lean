/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual retained signed-key support caps. The original modified columns,
complete-block filter and single-reference-ray kept rows are retained. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.SelectedSecondNaturalState
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.FirstFamilyMask
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.SelectedHighCofactorCoordinates
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedSecondKeyCaps
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSectorLocalization
open CenteredMomentAmplificationChildInput CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open Cycle61Moment Cycle61InitialMass LocalMoment
open CenteredMomentOriginalCommonHarmonic
open High.GlobalPhysical SecondSectorDatum SelectedSecondNatural SelectedHighCofactorCoordinates HighScalar
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq ι:=Classical.decEq _

def coarseExponent (Afirst Asecond Brow:ℝ):ℝ :=
  max Afirst (max Asecond (max Brow (Brow+Afirst)))

/-- These are exactly the four common-ideal, row and missing-radical gates
used by the LOW and HIGH source families. -/
def KeyCaps {left:Bool}{u₀:O}{unit:FirstSourceLabel→O}
    (key:NonzeroJointSourceLabel left u₀ unit)(Z B m:ℝ):Prop :=
  ((key.val.1.1.1.absNorm:ℝ)≤Z^B ∧ (key.val.1.1.2.absNorm:ℝ)≤Z^B ∧
    (key.val.2.1.1.absNorm:ℝ)≤Z^B ∧ (key.val.2.1.2.absNorm:ℝ)≤Z^B) ∧
  ((Ideal.span {jointSourceRow left u₀ unit key.val}).absNorm:ℝ)≤Z^B ∧
  ((Ideal.span {jointSourceRow left u₀ unit key.val}*firstSourceMissing left key.val.1).absNorm:ℝ)≤Z^B ∧
  firstSourceMissing left key.val.1≠0 ∧
  ((firstSourceMissing left key.val.1).absNorm:ℝ)=Z^m

/-- Pure arithmetic payment of one actual joint row; the specialized theorem
below obtains the row bound from its literal retained frequency. -/
theorem key_caps_of_frequency {left:Bool}{u₀:O}{unit:FirstSourceLabel→O}
    (key:NonzeroJointSourceLabel left u₀ unit)(Z Afirst Asecond Brow:ℝ)(hZ:1<Z)
    (hC:Supported key.val.1.1.1)(hD:Supported key.val.1.1.2)
    (hC₁:(key.val.1.1.1.absNorm:ℝ)≤Z^Afirst)(hD₁:(key.val.1.1.2.absNorm:ℝ)≤Z^Afirst)
    (hC₂:(key.val.2.1.1.absNorm:ℝ)≤Z^Asecond)(hD₂:(key.val.2.1.2.absNorm:ℝ)≤Z^Asecond)
    (hrow:rawFrequencyNorm (nonzeroJointSourceRow key)≤Z^Brow):
    KeyCaps key Z (coarseExponent Afirst Asecond Brow)
      (Real.logb Z ((firstSourceMissing left key.val.1).absNorm:ℝ)) := by
  have hF:Afirst≤coarseExponent Afirst Asecond Brow:=le_max_left _ _
  have hS:Asecond≤coarseExponent Afirst Asecond Brow:=
    (le_max_left _ _).trans (le_max_right _ _)
  have hR:Brow≤coarseExponent Afirst Asecond Brow:=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hRF:Brow+Afirst≤coarseExponent Afirst Asecond Brow:=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have lift (a b:ℝ)(hab:a≤b):Z^a≤Z^b:=Real.rpow_le_rpow_of_exponent_le hZ.le hab
  have hrow':normValue (jointSourceRow left u₀ unit key.val)≤Z^Brow:=hrow
  have hm:=joint_missing_support_cap left u₀ unit key hC hD Z Brow Afirst
    (zero_lt_one.trans hZ) hrow' hC₁
  have hp:(0:ℝ)<(firstSourceMissing left key.val.1).absNorm:=by
    exact_mod_cast (first_missing_norm_le left key.val.1 hC hD).1
  refine ⟨⟨hC₁.trans (lift _ _ hF),hD₁.trans (lift _ _ hF),
    hC₂.trans (lift _ _ hS),hD₂.trans (lift _ _ hS)⟩,
    hrow'.trans (lift _ _ hR),hm.2.trans (lift _ _ hRF),?_,?_⟩
  · intro hz
    rw [hz,map_zero,Nat.cast_zero] at hp
    exact (lt_irrefl 0) hp
  · exact (Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hp).symm

/-- Restriction changes only rows, so the actual full-column common caps
remain available on every kept complete block. -/
theorem regular_common_caps {α Label:Type}[Fintype α][Fintype Label]
    (slots:Label→Finset α)(s:∀l,Input (slots l))(modifier:∀l,Tuple (slots l)→ℂ)
    (R seed:Label→Ideal O)(K Tsec:Label→ℝ)(Z ξ:ℝ)(W:𝓢(ℝ,ℂ))
    (hseed:∀l,Squarefree (seed l))(hz₁:∀l,(s l).W₁ 0=0)(hz₂:∀l,(s l).W₂ 0=0)
    (hK:∀l,0<K l)(χ₀:Label→RayCharacter)(Q:Ideal O)(m:O)
    (q:CompleteFamily slots s modifier R seed W K Tsec (fun _=>Z) (fun _=>ξ)):
    let d:=regularDatum slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK χ₀ Q m q
    (d.C.absNorm:ℝ)≤sourceRadius (s q.1) ∧ (d.D.absNorm:ℝ)≤sourceRadius (s q.1) := by
  have h:=modified_retained_seed_and_caps (slots q.1) (s q.1) (modifier q.1)
    (R q.1) (seed q.1) (hseed q.1) (hz₁ q.1) (hz₂ q.1) (K q.1) (Tsec q.1) Z ξ (hK q.1) q.2.val
  exact ⟨h.2.2.1,h.2.2.2⟩

/-- The threshold precedes every original source, selected first child,
complete second block and kept row. The polynomial key caps are consequences
of genuine sourceRadius caps and the actual retained MAIN radius identity. -/
theorem eventual_regular_key_caps (b err:ℝ)(N:ℕ)(hb:0<b)(herr:0<err):
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀{α Label:Type}[Fintype α][Fintype Label],
    ∀(slots:Label→Finset α)(s:∀l,Input (slots l))(modifier:∀l,Tuple (slots l)→ℂ)
      (R seed:Label→Ideal O)(K Tsec:Label→ℝ)(ξ:ℝ)(W:𝓢(ℝ,ℂ))
      (hseed:∀l,Squarefree (seed l))(hz₁:∀l,(s l).W₁ 0=0)(hz₂:∀l,(s l).W₂ 0=0)
      (hK:∀l,0<K l)(χ₀:Label→RayCharacter)(Q:Ideal O)(m:O)
      (original:Input α)(originalModifier:Tuple α→ℂ)(R₀ seed₀:Ideal O)
      (D:ℝ)(hK₀:0<Z^D)(bin:ℤ×(Fin 5→ℤ))(reflected second:Bool)
      (column:Label→FirstColumnIndex (High.CoupledFirst.geometryFirstSource original originalModifier R₀ seed₀ (Z^D) Z ξ hK₀ bin))
      (hs₀:Squarefree seed₀)(hz₀₁:original.W₁ 0=0)(hz₀₂:original.W₂ 0=0),
    let datum:=regularDatum slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK χ₀ Q m
    let first : CompleteFamily slots s modifier R seed W K Tsec (fun _=>Z) (fun _=>ξ)→FirstSourceLabel :=fun q=>FirstFamily.firstLabel original originalModifier R₀ seed₀ (Z^D) Z ξ hK₀ bin (column q.1)
    ∀(r:secondLiveRows (fun q=>(datum q).block))
      (amp reserve errv forced live small annular Afirst Asecond Brow:ℝ),
      ξ≤err→sourceRadius original≤Z^Afirst→sourceRadius (s r.val.1.1)≤Z^Asecond→
      Tsec r.val.1.1=firstMainFourierScale reflected (Z^D) (volume original) Z ξ (3*amp) reserve b N (first r.val.1)→
    let key:=FirstFamily.rawKey reflected original originalModifier R₀ seed₀ (Z^D) Z ξ hK₀ bin
      (column r.val.1.1) datum first r rfl second
    let x:=cofactorCoordinates reflected second (first r.val.1) (datum r.val.1).C (datum r.val.1).D
      (datum r.val.1).inactive Z D (Real.logb Z (volume original)) amp ξ reserve err errv forced live small annular
    x 2≤Brow→KeyCaps key Z (coarseExponent Afirst Asecond Brow) (x 1) := by
  filter_upwards [FirstFamily.eventual_literal_high_frequency b err N hb herr] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro α Label _ _ slots s modifier R seed K Tsec ξ W hseed hz₁ hz₂ hK χ₀ Q m
    original originalModifier R₀ seed₀ D hK₀ bin reflected second column hs₀ hz₀₁ hz₀₂
    datum first r amp reserve errv forced live small annular Afirst Asecond Brow hξ hsource₀ hsource₁ hT key x hq
  have hradius:(datum r.val.1).radius=frequencyRadius
      (firstMainFourierScale reflected (Z^D) (volume original) Z ξ (3*amp) reserve b N (first r.val.1)) Z ξ:=by
    change frequencyRadius (Tsec r.val.1.1) Z ξ=_
    rw [hT]
  have hf:=hZ.2 reflected second original originalModifier R₀ seed₀ D ξ hK₀ bin (column r.val.1.1)
    datum first r rfl amp reserve errv hξ hradius
  have hraw:rawFrequencyNorm (nonzeroJointSourceRow key)≤Z^(x 2):=by
    simpa [key,FirstFamily.rawKey,x,cofactorCoordinates,lostWidthCoordinates,first] using hf
  have hrow:=hraw.trans (Real.rpow_le_rpow_of_exponent_le hZ.1.le hq)
  have hfirst:=FirstFamily.label_common_bounds original originalModifier R₀ seed₀ (Z^D) Z ξ hK₀ bin hs₀ hz₀₁ hz₀₂ (column r.val.1.1)
  have hsecond:=regular_common_caps slots s modifier R seed K Tsec Z ξ W hseed hz₁ hz₂ hK χ₀ Q m r.val.1
  have hsupp:=FirstFamily.label_supported original originalModifier R₀ seed₀ (Z^D) Z ξ hK₀ bin (column r.val.1.1)
  have hkeyfirst:key.val.1=first r.val.1:=by cases second <;> rfl
  have hkeysecond:key.val.2.1=((datum r.val.1).C,(datum r.val.1).D):=by cases second <;> rfl
  have hc:Supported key.val.1.1.1:=by rw [hkeyfirst];exact hsupp.1
  have hd:Supported key.val.1.1.2:=by rw [hkeyfirst];exact hsupp.2.1
  have hc₁:(key.val.1.1.1.absNorm:ℝ)≤Z^Afirst:=by
    rw [hkeyfirst];exact hfirst.2.2.1.trans hsource₀
  have hd₁:(key.val.1.1.2.absNorm:ℝ)≤Z^Afirst:=by
    rw [hkeyfirst];exact hfirst.2.2.2.trans hsource₀
  have hc₂:(key.val.2.1.1.absNorm:ℝ)≤Z^Asecond:=by
    rw [hkeysecond];exact hsecond.1.trans hsource₁
  have hd₂:(key.val.2.1.2.absNorm:ℝ)≤Z^Asecond:=by
    rw [hkeysecond];exact hsecond.2.trans hsource₁
  have hx:x 1=Real.logb Z ((firstSourceMissing (!reflected) key.val.1).absNorm:ℝ):=by
    rw [hkeyfirst]
    simp [x,cofactorCoordinates,lostWidthCoordinates,childHighCoordinates,actualHighCoordinates]
  rw [hx]
  exact key_caps_of_frequency key Z Afirst Asecond Brow hZ.1 hc hd hc₁ hd₁ hc₂ hd₂ hrow

end
end QRH.Record1252270103Source.Admission.SelectedSecondKeyCaps
#print axioms QRH.Record1252270103Source.Admission.SelectedSecondKeyCaps.key_caps_of_frequency
#print axioms QRH.Record1252270103Source.Admission.SelectedSecondKeyCaps.regular_common_caps
#print axioms QRH.Record1252270103Source.Admission.SelectedSecondKeyCaps.eventual_regular_key_caps
