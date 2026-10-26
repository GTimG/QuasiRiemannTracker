/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal first-stage amplitudes and parent-normalized second phases. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.SelectedRegularSourceData
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.FirstAbsoluteBudgetCaps
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.SecondAbsoluteFirstCard
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.SecondAbsoluteFamilyCard
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.SecondAbsoluteEnvelope
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.SecondAbsoluteModifier
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalWeightedVolume
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.InitialPhysicalChildBounds
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.InitialPhysicalPoolTransport
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedRegularAbsolute
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic CenteredMomentSectorLocalization CenteredMomentFirstAnnularMajorant
open CenteredMomentFirstAmplificationChoice CenteredMomentCanonicalFirst
open CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondInputCapacitySource CenteredMomentSourceMass
open Cycle61Moment Cycle61InitialMass Record1252270103Second
open OAI.SevenEighths.Record1252270103Source QRH.Record1252270103Low
open High.GlobalPhysical SecondSectorDatum SelectedSecondPhase SelectedHighPaid SelectedRegularSourceData
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq ι:=Classical.decEq _
variable {α Label:Type}[Fintype α][Fintype Label]{Z:ℝ}{a:Anchor α Z}

def amplitude (F:Family a Label) (W:𝓢(ℝ,ℂ)) (P:Label→Finset (Ideal O))
    (H0 radius:Label→ℝ)(ell:ℝ)(l:Label):ℝ :=
  ‖High.CoupledFirst.balancedColumnScalar F.reflected F.s F.modifier F.R F.seed (Z^F.D) Z F.ξ F.D
    (Real.logb Z (volume F.s)) F.hK F.bin
    (fun q=>normPhase (High.CoupledFirst.coordinateBlock F.s F.modifier F.R F.seed W (Z^F.D) Z F.ξ q))
    (F.column l)‖^2 * mainExtra F.s (F.stage l).common (P l) (H0 l) (radius l) (F.amp l) ell *
    ‖frozenCoefficient (F.stage l).B.val (F.stage l).common F.R F.s.ν F.s.W F.s.P‖^2

abbrev Keep (F:Family a Label) := ∀l,BlockIndex (F.input l) (F.childModifier l) (F.mask l)
  (F.childSeed l) (F.Hmain l) (F.Tsec l) Z F.ξ→O→Prop

def datum (F:Family a Label)(keep:Keep F)(q:F.Complete):SecondInputDatum α :=
  familyDatum F.slots F.input F.childModifier F.mask F.childSeed F.childSeed_sf
    (fun _=>F.zero₁) (fun _=>F.zero₂) ballProfile F.Hmain F.Tsec (fun _=>Z) (fun _=>F.ξ) F.Hmain_pos keep q

def phase (F:Family a Label)(W:𝓢(ℝ,ℂ))(P:Label→Finset (Ideal O))
    (H0 radius:Label→ℝ)(ell:ℝ)(keep:Keep F)(q:F.Complete):ℂ :=
  familyWeight F.slots F.input F.childModifier F.mask F.childSeed ballProfile F.Hmain F.Tsec
    (fun _=>Z) (fun _=>F.ξ) (fun _=>volume F.s) (amplitude F W P H0 radius ell) keep q

def effectivePhase (F:Family a Label)(W:𝓢(ℝ,ℂ))(P:Label→Finset (Ideal O))
    (H0 radius:Label→ℝ)(ell:ℝ)(keep:Keep F)(q:F.Complete):ℂ :=
  secondEffectiveWeight (fun q=>modifiedDatumBlock (datum F keep q) (F.childModifier q.1))
    (phase F W P H0 radius ell keep) ballProfile q

theorem amplitude_nonneg (F:Family a Label)(W:𝓢(ℝ,ℂ))(P:Label→Finset (Ideal O))
    (H0 radius:Label→ℝ)(ell:ℝ)(hell:0<ell)(hrad:∀l,0≤radius l+6*F.amp l)(l:Label):
    0≤amplitude F W P H0 radius ell l := by
  dsimp only [amplitude,mainExtra]
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg
    (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (Nat.cast_nonneg _))
    (div_nonneg (hrad l) hell.le))) (sq_nonneg _)

theorem mainExtra_cap (F:Family a Label)(P:Label→Finset (Ideal O))
    (H0 radius:Label→ℝ)(ell radiusMax Da B:ℝ)(hell:0<ell)(hmax:0≤radiusMax)(hDa:0≤Da)
    (hP:∀l,(P l).Nonempty)(hH0:∀l,0<H0 l)(hrad:∀l,0≤radius l+6*F.amp l)
    (hcap:∀l,radius l+6*F.amp l≤radiusMax)
    (halloc:∀l,((actualAllocations F.s.pools (F.stage l).common).card:ℝ)^2≤Da*Z^B)(l:Label):
    mainExtra F.s (F.stage l).common (P l) (H0 l) (radius l) (F.amp l) ell≤
      (7*Da*radiusMax/ell)*Z^B := by
  have hp:(1:ℝ)≤(P l).card:=by exact_mod_cast Finset.one_le_card.mpr (hP l)
  have ha:0≤((actualAllocations F.s.pools (F.stage l).common).card:ℝ)^2:=sq_nonneg _
  have hb:(bands (H0 l)).card≤(7:ℝ):=bands_card _ (hH0 l)
  dsimp only [mainExtra]
  calc
    _≤((bands (H0 l)).card:ℝ)*((actualAllocations F.s.pools (F.stage l).common).card:ℝ)^2*
      ((radius l+6*F.amp l)/ell):=mul_le_mul_of_nonneg_right
        (div_le_self (mul_nonneg (Nat.cast_nonneg _) ha) hp) (div_nonneg (hrad l) hell.le)
    _≤7*(Da*Z^B)*(radiusMax/ell):=by
      apply mul_le_mul
      · exact mul_le_mul hb (halloc l) ha (by norm_num)
      · exact div_le_div_of_nonneg_right (hcap l) hell.le
      · exact div_nonneg (hrad l) hell.le
      · exact mul_nonneg (by norm_num) (ha.trans (halloc l))
    _=_:=by ring

def amplitudeConstant (N:ℕ)(Cs lo ap Da radiusMax ell:ℝ):ℝ :=
  (2*((geometrySupportConstant N lo ap ap)^2+1))*(7*Da*radiusMax/ell)*(Cs^N)^2

theorem amplitude_cap (F:Family a Label)(N:ℕ)(Cs lo ap Da radiusMax ell B:ℝ)
    (hCs:1≤Cs)(hlo:0<lo)(hap:0<ap)(hDa:0≤Da)(hmax:0≤radiusMax)(hell:0<ell)(hB:0≤B)
    (hN:Fintype.card α≤N)(hM:∀i,F.s.M i≤Cs)(hlower:lo≤F.s.lower)
    (hsource:sourceRadius F.s≤Z^B)(hW1:∀x,F.s.W₁ x≠0→ap≤x)(hW2:∀x,F.s.W₂ x≠0→ap≤x)
    (hV:|Real.logb Z (volume F.s)|≤B)
    (W:𝓢(ℝ,ℂ))(P:Label→Finset (Ideal O))(H0 radius:Label→ℝ)
    (hP:∀l,(P l).Nonempty)(hH0:∀l,0<H0 l)(hrad:∀l,0≤radius l+6*F.amp l)
    (hcap:∀l,radius l+6*F.amp l≤radiusMax)
    (halloc:∀l,((actualAllocations F.s.pools (F.stage l).common).card:ℝ)^2≤Da*Z^B)(l:Label):
    amplitude F W P H0 radius ell l≤amplitudeConstant N Cs lo ap Da radiusMax ell*Z^(8*B) := by
  have hs:=FirstAbsoluteBudget.canonical_scalar_sq F.reflected N lo ap hlo hap F.s F.modifier F.R F.seed W
    F.D Z F.ξ B F.hZ F.hK hB hN hlower F.seed_sf F.zero₁ F.zero₂ hsource hW1 hW2 hV F.bin (F.column l)
  have he:=mainExtra_cap F P H0 radius ell radiusMax Da B hell hmax hDa hP hH0 hrad hcap halloc l
  have hf:=pow_le_pow_left₀ (norm_nonneg _) (MarkedMainRemainder.selected_frozen_norm F.s N Cs hN hCs hM
    (F.stage l).common F.R (F.stage l).B) 2
  have hex:0≤mainExtra F.s (F.stage l).common (P l) (H0 l) (radius l) (F.amp l) ell:=by
    dsimp only [mainExtra];exact mul_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
      (Nat.cast_nonneg _)) (div_nonneg (hrad l) hell.le)
  dsimp only [amplitude]
  apply (mul_le_mul (mul_le_mul hs he hex ((sq_nonneg _).trans hs)) hf (sq_nonneg _)
    (mul_nonneg ((sq_nonneg _).trans hs) (hex.trans he))).trans_eq
  rw [show (8:ℝ)*B=7*B+B by ring,Real.rpow_add (zero_lt_one.trans F.hZ)]
  dsimp [amplitudeConstant];ring


theorem datum_common_cap (F:Family a Label)(keep:Keep F)(B:ℝ)
    (hsource:∀l,sourceRadius (F.input l)≤Z^B)(q:F.Complete):
    ((datum F keep q).C.absNorm:ℝ)≤Z^B := by
  have hh:=modified_retained_seed_and_caps (F.slots q.1) (F.input q.1) (F.childModifier q.1)
    (F.mask q.1) (F.childSeed q.1) (F.childSeed_sf q.1) F.zero₁ F.zero₂
    (F.Hmain q.1) (F.Tsec q.1) Z F.ξ (F.Hmain_pos q.1) q.2.val
  exact hh.2.2.1.trans (hsource q.1)

theorem datum_row_cap (F:Family a Label)(keep:Keep F)(q:F.Complete)(z:O)
    (hz:z∈(datum F keep q).rows):
    normValue z≤4*frequencyRadius (F.Tsec q.1) Z F.ξ := by
  have hm:=restricted_retained_rows (F.slots q.1) (F.input q.1) (F.childModifier q.1)
    (F.mask q.1) (F.childSeed q.1) (F.childSeed_sf q.1) F.zero₁ F.zero₂
    (F.Hmain q.1) (F.Tsec q.1) Z F.ξ (F.Hmain_pos q.1) q.2.val (keep q.1 q.2.val) z
  have hx:=CenteredMomentSecondLiveBlock.liveRows_geometry _ _ _ _ _ z (hm.mp hz).1
  have hC:Supported (datum F keep q).C:=(datum F keep q).hC
  have h1:=CenteredMomentSectorLocalization.normValue_ge_one _
    (commonFrequencyGenerator_ne_zero (datum F keep q).C (datum F keep q).D hC)
  have h2:=CenteredMomentSectorLocalization.normValue_ge_one _
    (CenteredMomentSecondCanonicalNonunit.nonunitFrequencyGenerator_ne_zero
      (datum F keep q).C (datum F keep q).D hC (datum F keep q).inactive)
  have hd:1≤normValue (commonFrequencyGenerator (datum F keep q).C (datum F keep q).D)*
      normValue (CenteredMomentSecondCanonicalNonunit.nonunitFrequencyGenerator
        (datum F keep q).C (datum F keep q).D (datum F keep q).inactive):=by nlinarith
  exact hx.2.2.2.trans (div_le_self (mul_nonneg (by norm_num) hx.1.le) hd)


theorem datum_row_power (F:Family a Label)(keep:Keep F)(Brows:ℝ)(hZ4:4≤Z)
    (hfreq:∀l,frequencyRadius (F.Tsec l) Z F.ξ≤Z^Brows)
    (q:F.Complete)(z:O)(hmem:z∈(datum F keep q).rows):normValue z≤Z^(Brows+1):=by
  have hz:0<Z:=zero_lt_one.trans F.hZ
  have hn:=CenteredMomentSectorLocalization.normValue_ge_one z ((datum F keep q).rows_ne z hmem)
  have hr:=datum_row_cap F keep q z hmem
  have hrad:0≤frequencyRadius (F.Tsec q.1) Z F.ξ:=by linarith
  calc
    _≤4*frequencyRadius (F.Tsec q.1) Z F.ξ:=hr
    _≤Z*Z^Brows:=mul_le_mul hZ4 (hfreq q.1) hrad (by linarith)
    _=Z^(Brows+1):=by rw [Real.rpow_add hz,Real.rpow_one];ring

theorem column_cap_irrel {ι:Type}[Fintype ι](d1 d2:DecidableEq (ι⊕Fin 2))
    (pools:(ι⊕Fin 2)→Finset (Ideal O))(Y:ℝ)
    (h:∀I∈finiteColumns (@Fintype.piFinset (ι⊕Fin 2) d1 inferInstance (fun _=>Ideal O) pools),(I.absNorm:ℝ)≤Y):
    ∀I∈finiteColumns (@Fintype.piFinset (ι⊕Fin 2) d2 inferInstance (fun _=>Ideal O) pools),(I.absNorm:ℝ)≤Y:=by
  have he:@Fintype.piFinset (ι⊕Fin 2) d2 inferInstance (fun _=>Ideal O) pools=
      @Fintype.piFinset (ι⊕Fin 2) d1 inferInstance (fun _=>Ideal O) pools:=by
    ext v; simp only [Fintype.mem_piFinset]
  simpa only [he] using h

theorem tuple_cap_irrel {ι:Type}[Fintype ι](d1 d2:DecidableEq (ι⊕Fin 2))
    (pools:(ι⊕Fin 2)→Finset (Ideal O))(f:Tuple ι→ℝ)(Y:ℝ)
    (h:∀v∈@Fintype.piFinset (ι⊕Fin 2) d1 inferInstance (fun _=>Ideal O) pools,f v≤Y):
    ∀v∈@Fintype.piFinset (ι⊕Fin 2) d2 inferInstance (fun _=>Ideal O) pools,f v≤Y:=by
  have he:@Fintype.piFinset (ι⊕Fin 2) d2 inferInstance (fun _=>Ideal O) pools=
      @Fintype.piFinset (ι⊕Fin 2) d1 inferInstance (fun _=>Ideal O) pools:=by
    ext v; simp only [Fintype.mem_piFinset]
  simpa only [he] using h

theorem child_full_pool_cap (F:Family a Label)(Bpool:ℝ)
    (hpool:∀I∈finiteColumns (Fintype.piFinset F.s.pools),(I.absNorm:ℝ)≤Z^Bpool)(l:Label):
    ∀I∈finiteColumns (Fintype.piFinset (F.input l).pools),(I.absNorm:ℝ)≤Z^Bpool:=by
  have hh:=InitialPhysical.child_full_column_cap F.s (F.stage l).common F.R (F.stage l).B
    (F.stage l).τ (F.stage l).t (Z^Bpool) (column_cap_irrel _ _ _ _ hpool)
  exact column_cap_irrel _ _ _ _ hh

theorem child_modifier_cap (F:Family a Label)(P:Label→Finset (Ideal O))(ell Bpool:ℝ)(hell:0<ell)
    (hpool:∀I∈finiteColumns (Fintype.piFinset F.s.pools),(I.absNorm:ℝ)≤Z^Bpool)
    (A1 A2 D K:Label→Ideal O)(cellA mesh loss BD:Label→ℝ)(depth:Label→ℕ)
    (hcell:∀l,Pool.FixedCellPoolData (P l) Z (cellA l) ell (mesh l) (loss l) (BD l) Bpool (depth l))
    (hmodifier:∀l,F.childModifier l=SecondRemainder.correctedModifier (P l) (A1 l) (A2 l) (D l) (K l) (fun _=>1))
    (l:Label):∀v∈Fintype.piFinset (F.input l).pools,‖F.childModifier l v‖≤2:=by
  rw [hmodifier l]
  apply tuple_cap_irrel _ _ _ _ _
  exact SecondAbsoluteEnvelope.fixed_cell_corrected_one_full_pool (F.input l) (A1 l) (A2 l) (D l) (K l)
    (P l) Z (cellA l) ell (mesh l) (loss l) (BD l) Bpool (depth l) (hcell l) hell
    (column_cap_irrel _ _ _ _ (child_full_pool_cap F Bpool hpool l))

theorem finite_family_envelope (F:Family a Label)(N:ℕ)(Cs hi ap bp ell Bpool Brows Bl Bw Cl Cw:ℝ)
    (hCs:1≤Cs)(hhi:1≤hi)(hap:0<ap)(hbp:0≤bp)(hell:0<ell)
    (hBrows:0≤Brows)(hCl:0≤Cl)(hCw:0≤Cw)(hZ4:4≤Z)
    (p:Profiles ap bp)(W:𝓢(ℝ,ℂ))(P:Label→Finset (Ideal O))(H0 radius:Label→ℝ)
    (hN:Fintype.card α≤N)(hM:∀i,F.s.M i≤Cs)(hslot:∀i,F.s.hi i≤hi)
    (he1:F.s.W₁=p.profile 0)(he2:F.s.W₂=p.profile 1)
    (hfreq:∀l,frequencyRadius (F.Tsec l) Z F.ξ≤Z^Brows)
    (hpool:∀I∈finiteColumns (Fintype.piFinset F.s.pools),(I.absNorm:ℝ)≤Z^Bpool)
    (A1 A2 D K:Label→Ideal O)(cellA mesh loss BD:Label→ℝ)(depth:Label→ℕ)
    (hcell:∀l,Pool.FixedCellPoolData (P l) Z (cellA l) ell (mesh l) (loss l) (BD l) Bpool (depth l))
    (hmodifier:∀l,F.childModifier l=SecondRemainder.correctedModifier (P l) (A1 l) (A2 l) (D l) (K l) (fun _=>1))
    (keep:Keep F)(take:F.Complete→Prop)
    (hcard:(Fintype.card {q:F.Complete // take q}:ℝ)≤Cl*Z^Bl)
    (hweighted:∀q:F.Complete,‖effectivePhase F W P H0 radius ell keep q‖*(datum F keep q).block.outside*
      (CenteredMomentExceptionalAmplitudePair.volume (datum F keep q).input.toData)^2≤Cw*Z^Bw):
    let d:=fun q:{q:F.Complete // take q}=>datum F keep q.val
    let mod:=fun q:{q:F.Complete // take q}=>F.childModifier q.val.1
    let w:=fun q:{q:F.Complete // take q}=>effectivePhase F W P H0 radius ell keep q.val
    let bound:=SecondAbsoluteEnvelope.envelopeConstant N Cs hi bp*Cl*Cw*(p.control {(0,0)})^2*
      Z^(Brows+1+Bpool+Bl+Bw)
    secondAbsoluteBudget d mod w≤bound ∧
      ∀(reflected:Bool)(t u:ℝ),modifiedSecondNormalizedSum reflected d mod w t u≤bound := by
  have hz:0<Z:=zero_lt_one.trans F.hZ
  have hrows:=datum_row_power F keep Brows hZ4 hfreq
  have hpools:=child_full_pool_cap F Bpool hpool
  have hmod:=child_modifier_cap F P ell Bpool hell hpool A1 A2 D K cellA mesh loss BD depth hcell hmodifier
  let d:=fun q:{q:F.Complete // take q}=>datum F keep q.val
  let mod:=fun q:{q:F.Complete // take q}=>F.childModifier q.val.1
  let w:=fun q:{q:F.Complete // take q}=>effectivePhase F W P H0 radius ell keep q.val
  have henv:=SecondAbsoluteEnvelope.polynomial_second_envelope N Cs hi bp ap Cl Cw Bpool
    (Brows+1) Bl Bw Z hCs hhi hbp hap hCl hCw (by linarith) F.hZ hN hcard d mod w (p.profile 0) (p.profile 1)
    (fun q i=>hM i.val) (fun q i=>hslot i.val) (fun q=>tuple_cap_irrel _ _ _ _ _ (hmod q.val.1))
    (fun _=>he1) (fun _=>he2) (p.support 0) (p.support 1) (fun q=>hrows q.val)
    (fun q=>column_cap_irrel _ _ _ _ (hpools q.val.1)) (fun q=>hweighted q.val)
  have hcontrol:(SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*SchwartzMap.seminorm ℝ 0 0 (p.profile 1))≤
      p.control {(0,0)}:=by simp [Profiles.control,sourceControl]
  have hc:0≤SecondAbsoluteEnvelope.envelopeConstant N Cs hi bp*Cl*Cw:=
    mul_nonneg (mul_nonneg (SecondAbsoluteEnvelope.envelopeConstant_nonneg N Cs hi bp) hCl) hCw
  have hbound:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hcontrol 2) hc)
    (Real.rpow_nonneg hz.le (Brows+1+Bpool+Bl+Bw))
  exact ⟨henv.1.trans hbound,fun reflected t u=>(henv.2 reflected t u).trans hbound⟩

end
end QRH.Record1252270103Source.Admission.SelectedRegularAbsolute
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularAbsolute.amplitude_nonneg
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularAbsolute.mainExtra_cap
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularAbsolute.amplitude_cap

#print axioms QRH.Record1252270103Source.Admission.SelectedRegularAbsolute.datum_common_cap
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularAbsolute.datum_row_cap

#print axioms QRH.Record1252270103Source.Admission.SelectedRegularAbsolute.finite_family_envelope

#print axioms QRH.Record1252270103Source.Admission.SelectedRegularAbsolute.datum_row_power
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularAbsolute.child_full_pool_cap
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularAbsolute.child_modifier_cap

#print axioms QRH.Record1252270103Source.Admission.SelectedRegularAbsolute.column_cap_irrel

#print axioms QRH.Record1252270103Source.Admission.SelectedRegularAbsolute.tuple_cap_irrel
