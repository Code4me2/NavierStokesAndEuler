import NavierStokes.ParticularWaveAssembly
import NavierStokes.PhysicalCurlCovariance
import NavierStokes.PhysicalResidualTZ
import NavierStokes.StateReindex
import NavierStokes.ScaledTangentTransport

/-!
# Actual reference particular waves in physical coordinates

The input is the constructed reference Volterra solve.  Curl identities
are conclusions, not compatibility assumptions on solved velocities.
-/

namespace NavierStokes.PhysicalParticularWave

open Set Filter Function ProblemStatement HarmonicCalculus
open ParticularWaveAssembly ParticularWaveBounds LinearWaveBounds WeightedClasses
open CommonCoverSolve TorusInverse CopyAngularInvariance
open scoped ContDiff Topology

noncomputable section

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

noncomputable def rawCommon (D : AssemblyData P) (j : ℤ) : WaveCoefficients ((P × ℝ) × Plane) :=
  actualCommonCoefficients D.reference D.charts D.context D.state D.carrierBlock
    D.gaussianInput D.aliasInput j D.background

noncomputable def commonPotential (D : AssemblyData P) (j : ℤ) (n : ℕ) :
    ((P × ℝ) × Plane) → ComplexVector :=
  (rawCommon D j).curlPotential D.strip D.directions n


section ActualInputs

variable (D : AssemblyData P) {j : ℤ} {α κ : ℝ}
  (C : LocalControl D.reference D.charts D.context D.state D.carrierBlock
    D.gaussianInput D.aliasInput j D.background D.copy D.strip D.directions α κ)

include C








end ActualInputs

/-! ## The actual physical changes of band and cover -/

abbrev Lift := PhysicalResidualBridge.Lift
abbrev Cylinder := PhysicalResidualBridge.Cylinder
abbrev Parameter := ℝ × Plane
abbrev WaveSpace := (Parameter × ℝ) × Plane

/-- The wave solver uses `(R,(T,Z),theta,Y)`. The physical graph theorem
uses `(R,(Z,T),Y,theta)`. This is the literal isometric reordering. -/
noncomputable def waveEquiv : Cylinder ≃ₗᵢ[ℝ] WaveSpace :=
  (PhysicalResidualTZ.swapCylinder.trans
    (StateReindex.cylinder (ParticularWaveBounds.liftAssoc Plane))).trans angleShuffle

@[simp] theorem waveEquiv_apply (x : Cylinder) :
    waveEquiv x = (((x.1.1, (x.1.2.1.2, x.1.2.1.1)), x.2), x.1.2.2) := rfl

noncomputable def nativeMap (h Q : ℝ) (i : ℕ) (z : SpaceTime) : WaveSpace :=
  waveEquiv ((PhysicalResidualBridge.commonGraph Q h i).map z)

noncomputable def ratioPower (Q Qr a : ℝ) : ℝ := Q ^ a / Qr ^ a

theorem ratioPower_pos {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr) (a : ℝ) :
    0 < ratioPower Q Qr a := div_pos (Real.rpow_pos_of_pos hQ _) (Real.rpow_pos_of_pos hQr _)

theorem ratioPower_cancel {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr) (a : ℝ) :
    ratioPower Q Qr a * Q ^ (-a) = Qr ^ (-a) := by
  unfold ratioPower
  rw [Real.rpow_neg hQ.le, Real.rpow_neg hQr.le]
  field_simp [(Real.rpow_pos_of_pos hQ a).ne', (Real.rpow_pos_of_pos hQr a).ne']

theorem ratioPower_neg_div {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr) (a : ℝ) :
    Qr ^ (-a) / Q ^ (-a) = ratioPower Q Qr a := by
  unfold ratioPower
  rw [Real.rpow_neg hQ.le, Real.rpow_neg hQr.le]
  field_simp [(Real.rpow_pos_of_pos hQ a).ne', (Real.rpow_pos_of_pos hQr a).ne']

theorem ratioPower_mul {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr) (a b : ℝ) :
    ratioPower Q Qr a * ratioPower Q Qr b = ratioPower Q Qr (a + b) := by
  unfold ratioPower
  rw [Real.rpow_add hQ, Real.rpow_add hQr]
  ring

theorem ratioPower_div {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr) (a b : ℝ) :
    ratioPower Q Qr a / ratioPower Q Qr b = ratioPower Q Qr (a - b) := by
  unfold ratioPower
  rw [Real.rpow_sub hQ, Real.rpow_sub hQr]
  field_simp [(Real.rpow_pos_of_pos hQ b).ne', (Real.rpow_pos_of_pos hQr a).ne',
    (Real.rpow_pos_of_pos hQr b).ne']

/-- A band-to-reference change, in the `(Z,T)` order used by PCC.
The slow-coordinate swap is supplied by `waveEquiv`. -/
noncomputable def chartChange (h Q Qr : ℝ) (gap : ℕ) : Lift →L[ℝ] Lift :=
  MeanChartCompatibility.chartLinear (ratioPower Q Qr (1 / 2))
    (((ratioPower Q Qr (CoordinateAlgebra.D h) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
      (ratioPower Q Qr 1 • ContinuousLinearMap.snd ℝ ℝ ℝ)).prodMap
        (coverPower gap).toContinuousLinearMap)

@[simp] theorem chartChange_apply (h Q Qr : ℝ) (gap : ℕ) (x : Lift) :
    chartChange h Q Qr gap x =
      (ratioPower Q Qr (1 / 2) * x.1,
        ((ratioPower Q Qr (CoordinateAlgebra.D h) * x.2.1.1,
          ratioPower Q Qr 1 * x.2.1.2), coverPower gap x.2.2)) := rfl

noncomputable def cylinderChange (h Q Qr : ℝ) (gap : ℕ) : Cylinder →L[ℝ] Cylinder :=
  ((chartChange h Q Qr gap).comp (ContinuousLinearMap.fst ℝ Lift ℝ)).prod
    (ContinuousLinearMap.snd ℝ Lift ℝ)

@[simp] theorem cylinderChange_apply (h Q Qr : ℝ) (gap : ℕ) (x : Cylinder) :
    cylinderChange h Q Qr gap x = (chartChange h Q Qr gap x.1, x.2) := rfl

theorem cylinderChange_graph {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr)
    (h : ℝ) (i gap : ℕ) {z : SpaceTime} (hz : 0 < z.2 0) :
    cylinderChange h Q Qr gap ((PhysicalResidualBridge.commonGraph Q h i).map z) =
      (PhysicalResidualBridge.commonGraph Qr h (i + gap)).map z := by
  rw [PhysicalResidualBridge.commonGraph_map hQ h i hz,
    PhysicalResidualBridge.commonGraph_map hQr h (i + gap) hz]
  apply Prod.ext
  · apply Prod.ext
    · simp only [cylinderChange_apply, chartChange_apply, ← mul_assoc, ratioPower_cancel hQ hQr]
    · apply Prod.ext
      · apply Prod.ext
        · simp only [cylinderChange_apply, chartChange_apply, ← mul_assoc, ratioPower_cancel hQ hQr]
        · change ratioPower Q Qr 1 * ((1 - z.1) / Q) = (1 - z.1) / Qr
          simp only [ratioPower, Real.rpow_one]
          field_simp
      · change coverPower gap ((SlotGeometry.cover ^ i) _) = (SlotGeometry.cover ^ (i + gap)) _
        rw [coverPower_apply, ← _root_.mul_apply_eq_comp, ← pow_add, Nat.add_comm gap i]
  · rfl

noncomputable def velocityWeight (h Q Qr : ℝ) : ℝ := ratioPower Q Qr (CoordinateAlgebra.A h)
noncomputable def clockWeight (h Q Qr : ℝ) : ℝ := ratioPower Q Qr (CoordinateAlgebra.A h + 1 / 2)
noncomputable def sourceWeight (h Q Qr : ℝ) : ℝ := ratioPower Q Qr (2 * CoordinateAlgebra.A h + 1 / 2)
noncomputable def pressureWeight (h Q Qr : ℝ) : ℝ := ratioPower Q Qr (2 * CoordinateAlgebra.A h)
noncomputable def normalWeight (Q Qr K Kr : ℝ) : ℝ := (Kr / K) * ratioPower Q Qr (1 / 2)

theorem clock_mul_velocity {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr) (h : ℝ) :
    clockWeight h Q Qr * velocityWeight h Q Qr = sourceWeight h Q Qr := by
  unfold clockWeight velocityWeight sourceWeight
  rw [ratioPower_mul hQ hQr]
  congr 1
  ring

/-- Both clock scaling and normal scaling are needed for the physical
pressure weight. Their frequency factors cancel exactly. -/
theorem pressure_scaling {Q Qr K Kr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr)
    (hK : K ≠ 0) (hKr : Kr ≠ 0) (h : ℝ) :
    (clockWeight h Q Qr * velocityWeight h Q Qr / normalWeight Q Qr K Kr) * (Kr / K) =
      pressureWeight h Q Qr := by
  rw [clock_mul_velocity hQ hQr]
  unfold normalWeight pressureWeight sourceWeight
  calc
    _ = ratioPower Q Qr (2 * CoordinateAlgebra.A h + 1 / 2) /
        ratioPower Q Qr (1 / 2) := by
      field_simp [hK, hKr, (ratioPower_pos hQ hQr (1 / 2)).ne']
    _ = _ := by
      rw [ratioPower_div hQ hQr]
      congr 1
      ring

theorem linear_change_direction {X E F : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (C : E →L[ℝ] F) {f : X → E} {g : X → F} {x v : X} {a b : ℝ}
    {u : E} {w : F} (ha : a ≠ 0) (hf : DifferentiableAt ℝ f x)
    (he : (fun y => C (f y)) =ᶠ[𝓝 x] g)
    (hdf : fderiv ℝ f x v = a • u) (hdg : fderiv ℝ g x v = b • w) :
    C u = (b / a) • w := by
  have hd := congrArg (fun L : X →L[ℝ] F => L v) he.fderiv_eq
  change fderiv ℝ (C ∘ f) x v = fderiv ℝ g x v at hd
  rw [fderiv_comp x C.differentiableAt hf, ContinuousLinearMap.fderiv] at hd
  simp only [ContinuousLinearMap.comp_apply, hdf, map_smul, hdg] at hd
  calc
    C u = a⁻¹ • (a • C u) := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
    _ = a⁻¹ • (b • w) := by rw [hd]
    _ = (b / a) • w := by rw [smul_smul]; congr 1; ring

theorem cylinderChange_graph_germ {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr)
    (h : ℝ) (i gap : ℕ) {z : SpaceTime} (hz : 0 < z.2 0) :
    (fun y => cylinderChange h Q Qr gap ((PhysicalResidualBridge.commonGraph Q h i).map y)) =ᶠ[𝓝 z]
      (PhysicalResidualBridge.commonGraph Qr h (i + gap)).map := by
  have hn : {y : SpaceTime | 0 < y.2 0} ∈ 𝓝 z :=
    (isOpen_lt continuous_const (PhysicalGraphBounds.coordinateProjection 0).continuous).mem_nhds hz
  exact eventually_of_mem hn (fun y hy => cylinderChange_graph hQ hQr h i gap hy)

theorem cylinderChange_radial_graph {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr)
    (h : ℝ) (i gap : ℕ) {z : SpaceTime} (hz : 0 < z.2 0) :
    let G := PhysicalResidualBridge.commonGraph Q h i
    let H := PhysicalResidualBridge.commonGraph Qr h (i + gap)
    cylinderChange h Q Qr gap (G.radial (G.map z)) =
      ratioPower Q Qr (1 / 2) • H.radial (H.map z) := by
  let G := PhysicalResidualBridge.commonGraph Q h i
  let H := PhysicalResidualBridge.commonGraph Qr h (i + gap)
  have hn : G.radialScale * z.2 0 ≠ 0 := (mul_pos (Real.rpow_pos_of_pos hQ _) hz).ne'
  have hr : H.radialScale * z.2 0 ≠ 0 := (mul_pos (Real.rpow_pos_of_pos hQr _) hz).ne'
  have he := linear_change_direction (cylinderChange h Q Qr gap)
    (Real.rpow_pos_of_pos hQ (-(1 / 2 : ℝ))).ne'
    ((G.map_smoothAt hn).differentiableAt (by simp))
    (cylinderChange_graph_germ hQ hQr h i gap hz) (G.map_radial hn) (H.map_radial hr)
  change _ = (Qr ^ (-(1 / 2 : ℝ)) / Q ^ (-(1 / 2 : ℝ))) • _ at he
  rwa [ratioPower_neg_div hQ hQr] at he

theorem cylinderChange_axial_graph {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr)
    (h : ℝ) (i gap : ℕ) {z : SpaceTime} (hz : 0 < z.2 0) :
    let G := PhysicalResidualBridge.commonGraph Q h i
    let H := PhysicalResidualBridge.commonGraph Qr h (i + gap)
    cylinderChange h Q Qr gap (G.axial (G.map z)) =
      ratioPower Q Qr (1 / 2) • H.axial (H.map z) := by
  let G := PhysicalResidualBridge.commonGraph Q h i
  let H := PhysicalResidualBridge.commonGraph Qr h (i + gap)
  have hn : G.radialScale * z.2 0 ≠ 0 := (mul_pos (Real.rpow_pos_of_pos hQ _) hz).ne'
  have hr : H.radialScale * z.2 0 ≠ 0 := (mul_pos (Real.rpow_pos_of_pos hQr _) hz).ne'
  have he := linear_change_direction (cylinderChange h Q Qr gap)
    (Real.rpow_pos_of_pos hQ (-(1 / 2 : ℝ))).ne'
    ((G.map_smoothAt hn).differentiableAt (by simp))
    (cylinderChange_graph_germ hQ hQr h i gap hz) (G.map_axial hn) (H.map_axial hr)
  change _ = (Qr ^ (-(1 / 2 : ℝ)) / Q ^ (-(1 / 2 : ℝ))) • _ at he
  rwa [ratioPower_neg_div hQ hQr] at he

theorem cylinderChange_temporal_graph {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr)
    (h : ℝ) (i gap : ℕ) {z : SpaceTime} (hz : 0 < z.2 0) :
    let G := PhysicalResidualBridge.commonGraph Q h i
    let H := PhysicalResidualBridge.commonGraph Qr h (i + gap)
    cylinderChange h Q Qr gap (G.temporal (G.map z)) =
      clockWeight h Q Qr • H.temporal (H.map z) := by
  let G := PhysicalResidualBridge.commonGraph Q h i
  let H := PhysicalResidualBridge.commonGraph Qr h (i + gap)
  have hn : G.radialScale * z.2 0 ≠ 0 := (mul_pos (Real.rpow_pos_of_pos hQ _) hz).ne'
  have hr : H.radialScale * z.2 0 ≠ 0 := (mul_pos (Real.rpow_pos_of_pos hQr _) hz).ne'
  have he := linear_change_direction (cylinderChange h Q Qr gap)
    (mul_pos (Real.rpow_pos_of_pos hQ (-CoordinateAlgebra.A h))
      (Real.rpow_pos_of_pos hQ (-(1 / 2 : ℝ)))).ne'
    ((G.map_smoothAt hn).differentiableAt (by simp))
    (cylinderChange_graph_germ hQ hQr h i gap hz) (G.map_temporal hn) (H.map_temporal hr)
  have hG : G.velocityScale * G.radialScale = Q ^ (-(CoordinateAlgebra.A h + 1 / 2)) := by
    change Q ^ (-CoordinateAlgebra.A h) * Q ^ (-(1 / 2 : ℝ)) = _
    rw [← Real.rpow_add hQ]
    congr 1
    ring
  have hH : H.velocityScale * H.radialScale = Qr ^ (-(CoordinateAlgebra.A h + 1 / 2)) := by
    change Qr ^ (-CoordinateAlgebra.A h) * Qr ^ (-(1 / 2 : ℝ)) = _
    rw [← Real.rpow_add hQr]
    congr 1
    ring
  change _ = (H.velocityScale * H.radialScale / (G.velocityScale * G.radialScale)) • _ at he
  rw [hG, hH, ratioPower_neg_div hQ hQr] at he
  exact he

theorem radial_sameRadius (G : PhysicalResidualBridge.ScaledGraph) {x y : Cylinder}
    (hxy : x.1.1 = y.1.1) : G.radial x = G.radial y := by
  simp only [PhysicalResidualBridge.ScaledGraph.radial, hxy]

theorem cylinderChange_radial {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr)
    (h : ℝ) (i gap : ℕ) {x : Cylinder} (hx : 0 < x.1.1) :
    let G := PhysicalResidualBridge.commonGraph Q h i
    let H := PhysicalResidualBridge.commonGraph Qr h (i + gap)
    cylinderChange h Q Qr gap (G.radial x) =
      ratioPower Q Qr (1 / 2) • H.radial (cylinderChange h Q Qr gap x) := by
  let G := PhysicalResidualBridge.commonGraph Q h i
  let H := PhysicalResidualBridge.commonGraph Qr h (i + gap)
  let z : SpaceTime := (0, AxisymmetricResidual.pack (Q ^ (1 / 2 : ℝ) * x.1.1) 0 0)
  have hz : 0 < z.2 0 := by
    simpa only [z, AxisymmetricResidual.pack_zero] using mul_pos (Real.rpow_pos_of_pos hQ (1 / 2)) hx
  have hn : (G.map z).1.1 = x.1.1 := by
    change Q ^ (-(1 / 2 : ℝ)) * (AxisymmetricResidual.pack (Q ^ (1 / 2 : ℝ) * x.1.1) 0 0) 0 = x.1.1
    rw [AxisymmetricResidual.pack_zero]
    rw [← mul_assoc, ← Real.rpow_add hQ, neg_add_cancel, Real.rpow_zero, one_mul]
  have hr : (H.map z).1.1 = (cylinderChange h Q Qr gap x).1.1 := by
    have he := congrArg (fun y : Cylinder => y.1.1) (cylinderChange_graph hQ hQr h i gap hz)
    change ratioPower Q Qr (1 / 2) * (G.map z).1.1 = (H.map z).1.1 at he
    rw [hn] at he
    exact he.symm
  have he := cylinderChange_radial_graph hQ hQr h i gap hz
  change cylinderChange h Q Qr gap (G.radial (G.map z)) =
    ratioPower Q Qr (1 / 2) • H.radial (H.map z) at he
  rwa [radial_sameRadius G hn, radial_sameRadius H hr] at he

theorem cylinderChange_axial {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr)
    (h : ℝ) (i gap : ℕ) (x : Cylinder) :
    let G := PhysicalResidualBridge.commonGraph Q h i
    let H := PhysicalResidualBridge.commonGraph Qr h (i + gap)
    cylinderChange h Q Qr gap (G.axial x) =
      ratioPower Q Qr (1 / 2) • H.axial (cylinderChange h Q Qr gap x) := by
  exact cylinderChange_axial_graph hQ hQr h i gap
    (z := (0, AxisymmetricResidual.pack 1 0 0)) (by simp)

theorem cylinderChange_temporal {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr)
    (h : ℝ) (i gap : ℕ) (x : Cylinder) :
    let G := PhysicalResidualBridge.commonGraph Q h i
    let H := PhysicalResidualBridge.commonGraph Qr h (i + gap)
    cylinderChange h Q Qr gap (G.temporal x) =
      clockWeight h Q Qr • H.temporal (cylinderChange h Q Qr gap x) := by
  exact cylinderChange_temporal_graph hQ hQr h i gap
    (z := (0, AxisymmetricResidual.pack 1 0 0)) (by simp)

theorem cylinderChange_angular (h Q Qr : ℝ) (gap : ℕ) (x : Cylinder) :
    cylinderChange h Q Qr gap (PhysicalResidualBridge.ScaledGraph.angular x) =
      PhysicalResidualBridge.ScaledGraph.angular (cylinderChange h Q Qr gap x) := by
  change (chartChange h Q Qr gap 0, 1) = (0, 1)
  rw [map_zero]

/-- The normal scale comes from the actual spatial chart differential
and the raw carrier phase, independently of any solved velocity. -/
theorem phaseNormal_chartChange {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr)
    (h : ℝ) (i gap : ℕ) (K Kr : ℝ) {x : Cylinder} (hx : 0 < x.1.1)
    {Φ : Cylinder → ℝ} (hΦ : DifferentiableAt ℝ Φ (cylinderChange h Q Qr gap x)) :
    let G := PhysicalResidualBridge.commonGraph Q h i
    let H := PhysicalResidualBridge.commonGraph Qr h (i + gap)
    phaseNormal PhysicalResidualBridge.ScaledGraph.radius G.radial
      PhysicalResidualBridge.ScaledGraph.angular G.axial
      (fun y => (Kr / K) * Φ (cylinderChange h Q Qr gap y)) x =
    normalWeight Q Qr K Kr • phaseNormal PhysicalResidualBridge.ScaledGraph.radius H.radial
      PhysicalResidualBridge.ScaledGraph.angular H.axial Φ (cylinderChange h Q Qr gap x) := by
  exact PhysicalCurlCovariance.phaseNormal_pull
    (Γ := cylinderChange h Q Qr gap) (x := x)
    (R := PhysicalResidualBridge.ScaledGraph.radius) (r := PhysicalResidualBridge.ScaledGraph.radius)
    (Sr := (PhysicalResidualBridge.commonGraph Q h i).radial)
    (Sθ := PhysicalResidualBridge.ScaledGraph.angular) (Sz := (PhysicalResidualBridge.commonGraph Q h i).axial)
    (Vr := (PhysicalResidualBridge.commonGraph Qr h (i + gap)).radial)
    (Vθ := PhysicalResidualBridge.ScaledGraph.angular)
    (Vz := (PhysicalResidualBridge.commonGraph Qr h (i + gap)).axial)
    (ratioPower_pos hQ hQr (1 / 2)).ne' hx.ne'
    (cylinderChange h Q Qr gap).differentiableAt
    (by simpa only [ContinuousLinearMap.fderiv] using cylinderChange_radial hQ hQr h i gap hx)
    (by simpa only [ContinuousLinearMap.fderiv] using cylinderChange_angular h Q Qr gap x)
    (by simpa only [ContinuousLinearMap.fderiv] using cylinderChange_axial hQ hQr h i gap x)
    rfl hΦ (Kr / K)


/-! ## One potential built from the actual reference solve -/

noncomputable def referenceRaw (D : AssemblyData Parameter) (j : ℤ) : WaveSpace → ComplexVector :=
  angleLift (referenceVelocity D.reference D.context D.state D.carrierBlock
    D.gaussianInput D.aliasInput j)


noncomputable def referenceFrequency (D : AssemblyData Parameter) (j : ℤ) : ℝ :=
  (j : ℝ) * D.carrierBlock.frequency D.reference.band

noncomputable def referencePhase (D : AssemblyData Parameter) (j : ℤ) : WaveSpace → ℝ :=
  (actualCarrier D.background D.carrierBlock j).phase D.reference.band

noncomputable def physicalPhase (D : AssemblyData Parameter) (h Qr : ℝ) (I : ℕ) (j : ℤ) :
    SpaceTime → ℝ := fun z => referencePhase D j (nativeMap h Qr I z)

noncomputable def physicalRaw (D : AssemblyData Parameter) (h Qr : ℝ) (I : ℕ) (j : ℤ) :
    SpaceTime → ComplexVector :=
  fun z => Qr ^ (-CoordinateAlgebra.A h) • referenceRaw D j (nativeMap h Qr I z)

/-- The native cutoff is already inside the reference common solve.
The potential is taken once, after that solve and before differentiation. -/
noncomputable def referencePotential (D : AssemblyData Parameter) (h Qr : ℝ) (I : ℕ) (j : ℤ) :
    SpaceTime → ComplexVector :=
  PhysicalCurlCovariance.referencePotential (referenceFrequency D j)
    (physicalPhase D h Qr I j) (physicalRaw D h Qr I j)





theorem nativeMap_add_angle (h Q : ℝ) (i : ℕ) (z : SpaceTime) (s : ℝ) :
    nativeMap h Q i (z + s • (0, coordinateVector 1)) =
      nativeMap h Q i z + s • (((0 : Parameter), (1 : ℝ)), (0 : Plane)) := by
  ext <;> simp [nativeMap, waveEquiv_apply, PhysicalResidualBridge.ScaledGraph.map,
    coordinateVector, smul_eq_mul]



theorem angle_translate_pack (t r theta z s : ℝ) :
    (t, AxisymmetricResidual.pack r theta z) + s • ((0 : ℝ), coordinateVector 1) =
      (t, AxisymmetricResidual.pack r (theta + s) z) := by
  apply Prod.ext
  · simp
  · ext i
    fin_cases i <;> simp [coordinateVector]


/-- These are identities of the input chart at its own reference band. -/
structure ReferenceIdentity (D : AssemblyData Parameter) : Prop where
  parameter : D.charts.parameter D.reference.band = id
  gap : D.charts.gap D.reference.band = 0
  amplitude : D.charts.amplitude D.reference.band = 1

theorem referenceRaw_eq_common (D : AssemblyData Parameter) (H : ReferenceIdentity D) (j : ℤ) :
    referenceRaw D j = (rawCommon D j).amplitude D.reference.band := by
  have hs : residualSource D.context D.state D.carrierBlock D.gaussianInput D.aliasInput j D.reference.band =
      transportSource (residualSource D.context D.state D.carrierBlock D.gaussianInput D.aliasInput j D.reference.band)
        (D.charts.parameter D.reference.band) (D.charts.gap D.reference.band)
        (D.charts.amplitude D.reference.band) := by
    rw [H.parameter, H.gap, H.amplitude]
    funext p
    simp [transportSource, coverPower]
  funext x
  have he := actualBandVelocity_eq_reference D.reference D.charts D.context D.state D.carrierBlock
    D.gaussianInput D.aliasInput j D.reference.band hs x.1.1 x.2
  rw [H.parameter, H.gap, H.amplitude] at he
  simp only [id_eq, coverPower, ContinuousLinearEquiv.refl_apply, one_smul] at he
  exact he.symm

/-- Literal input-operator matches at the reference chart. This record
contains no condition on a solved velocity, pressure, potential or curl. -/
structure ReferenceChart (D : AssemblyData Parameter) (h Qr : ℝ) (I : ℕ) : Prop where
  identity : ReferenceIdentity D
  radius : (fun x => D.background.radius D.reference.band (waveEquiv.toContinuousLinearEquiv x)) =
    PhysicalResidualBridge.ScaledGraph.radius
  radial : PhysicalCurlCovariance.reindexVector waveEquiv.toContinuousLinearEquiv
      (D.directions.radialField D.reference.band) = (PhysicalResidualBridge.commonGraph Qr h I).radial
  angular : PhysicalCurlCovariance.reindexVector waveEquiv.toContinuousLinearEquiv
      (fun _ => D.directions.angular) = PhysicalResidualBridge.ScaledGraph.angular
  axial : PhysicalCurlCovariance.reindexVector waveEquiv.toContinuousLinearEquiv
      (D.directions.axialField D.strip D.reference.band) = (PhysicalResidualBridge.commonGraph Qr h I).axial

noncomputable def referenceDomain (D : AssemblyData Parameter) : Set Cylinder :=
  waveEquiv ⁻¹' D.strip.domain

theorem referenceDomain_open (D : AssemblyData Parameter) : IsOpen (referenceDomain D) :=
  D.strip.isOpen_domain.preimage waveEquiv.continuous

noncomputable def liftPhase (D : AssemblyData Parameter) (j : ℤ) : Cylinder → ℝ :=
  fun x => referencePhase D j (waveEquiv x)

noncomputable def liftRaw (D : AssemblyData Parameter) (j : ℤ) : Cylinder → ComplexVector :=
  fun x => referenceRaw D j (waveEquiv x)

section ReferenceRealization

variable (D : AssemblyData Parameter) {h Qr : ℝ} {I : ℕ} (H : ReferenceChart D h Qr I)
  {j : ℤ} {α κ : ℝ}
  (C : LocalControl D.reference D.charts D.context D.state D.carrierBlock
    D.gaussianInput D.aliasInput j D.background D.copy D.strip D.directions α κ)

include H C

omit H in
theorem liftPhase_smooth : ContDiffOn ℝ ∞ (liftPhase D j) (referenceDomain D) :=
  (C.background.phase_smooth D.reference.band).comp waveEquiv.contDiff.contDiffOn (fun _ hx => hx)






theorem liftPotential_eq {x : Cylinder} (hx : x ∈ referenceDomain D) :
    CurlClassBounds.vectorPotential (referenceFrequency D j) PhysicalResidualBridge.ScaledGraph.radius
      (PhysicalResidualBridge.commonGraph Qr h I).radial PhysicalResidualBridge.ScaledGraph.angular
      (PhysicalResidualBridge.commonGraph Qr h I).axial (liftPhase D j) (liftRaw D j) x =
      commonPotential D j D.reference.band (waveEquiv x) := by
  have hp := ((C.background.phase_smooth D.reference.band).contDiffAt
    (D.strip.isOpen_domain.mem_nhds hx)).differentiableAt (by simp)
  have he := PhysicalCurlCovariance.vectorPotential_reindex waveEquiv.toContinuousLinearEquiv
    (referenceFrequency D j) (D.background.radius D.reference.band)
    (D.directions.radialField D.reference.band) (fun _ => D.directions.angular)
    (D.directions.axialField D.strip D.reference.band)
    ((rawCommon D j).amplitude D.reference.band) hp
  rw [H.radius, H.radial, H.angular, H.axial] at he
  unfold liftRaw
  rw [referenceRaw_eq_common D H.identity]
  exact he

theorem referencePotential_eq_common (hQr : 0 < Qr) {z : SpaceTime} (hz : 0 < z.2 0)
    (hx : nativeMap h Qr I z ∈ D.strip.domain) :
    referencePotential D h Qr I j z =
      Qr ^ (-h) • commonPotential D j D.reference.band (nativeMap h Qr I z) := by
  have hK : referenceFrequency D j ≠ 0 := C.frequency_nonzero D.reference.band
  have hp := ((liftPhase_smooth D C).contDiffAt ((referenceDomain_open D).mem_nhds hx)).differentiableAt (by simp)
  have he := PhysicalCurlCovariance.commonGraph_vectorPotential_pull hQr h I hK hK hz hp (liftRaw D j)
  simp only [div_self hK, one_mul] at he
  change referencePotential D h Qr I j z = _ at he
  rw [liftPotential_eq D H C hx] at he
  exact he



end ReferenceRealization

/-! ## Actual solves with the rescaled native clock -/

noncomputable def parameterChange (h Q Qr : ℝ) (p : Parameter) : Parameter :=
  (ratioPower Q Qr (1 / 2) * p.1,
    (ratioPower Q Qr 1 * p.2.1, ratioPower Q Qr (CoordinateAlgebra.D h) * p.2.2))


theorem waveEquiv_cylinderChange (h Q Qr : ℝ) (gap : ℕ) (x : Cylinder) :
    waveEquiv (cylinderChange h Q Qr gap x) =
      ((parameterChange h Q Qr (waveEquiv x).1.1, (waveEquiv x).1.2), coverPower gap (waveEquiv x).2) := rfl

noncomputable def referenceSource (D : AssemblyData Parameter) (j : ℤ) : Parameter × Plane → ComplexVector :=
  residualSource D.context D.state D.carrierBlock D.gaussianInput D.aliasInput j D.reference.band



/-- Continuity of the actual primitive Volterra coefficients and source,
and support inside the reference integration interval. -/
structure ReferenceODE (D : AssemblyData Parameter) (j : ℤ) (U : Set Parameter) : Prop where
  coefficient : ContinuousOn (D.reference.tangent j).linearData.coefficient (U ×ˢ univ)
  forcing : ContinuousOn (D.reference.tangent j).linearData.forcingMap (U ×ˢ univ)
  source : ContinuousOn (referenceSource D j) (U ×ˢ univ)
  cutoff : support D.reference.cutoff ⊆ univ ×ˢ Icc 0 D.reference.length

theorem normalWeight_ne {Q Qr K Kr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr)
    (hK : K ≠ 0) (hKr : Kr ≠ 0) : normalWeight Q Qr K Kr ≠ 0 :=
  mul_ne_zero (div_ne_zero hKr hK) (ratioPower_pos hQ hQr (1 / 2)).ne'





noncomputable def bandPhase (D : AssemblyData Parameter) (h Q Qr : ℝ) (gap : ℕ) (K : ℝ) (j : ℤ) :
    Cylinder → ℝ := fun x => (referenceFrequency D j / K) * liftPhase D j (cylinderChange h Q Qr gap x)





theorem normalDot_scaled (s c : ℝ) (n : Space) (a : ComplexVector) :
    normalDot (s • n) (c • a) = (s : ℂ) * (c : ℂ) * normalDot n a := by
  simp [normalDot, Complex.real_smul]
  ring

section BandRealization

variable (D : AssemblyData Parameter) {h Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr)
  (i gap : ℕ) (H : ReferenceChart D h Qr (i + gap)) {j : ℤ} {α κ : ℝ}
  (C : LocalControl D.reference D.charts D.context D.state D.carrierBlock
    D.gaussianInput D.aliasInput j D.background D.copy D.strip D.directions α κ)
  {K : ℝ} (hK : K ≠ 0) {U : Set Parameter} (hU : IsOpen U) (R : ReferenceODE D j U)

include H C R hK hQ hQr





include hU


end BandRealization

/-! ## The pressure from the same reference solve -/






theorem mode_fullTurn {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {theta : E} {phi : E → ℝ} {a : E → ℂ} {K slope : ℝ} (m : ℤ)
    (hphi : AffinePhase theta slope phi) (ha : Invariant theta a)
    (hf : K * slope = (m : ℝ)) (x : E) :
    mode K phi a (x + (2 * Real.pi) • theta) = mode K phi a x := by
  have hc : (K : ℂ) * (slope : ℂ) = (m : ℂ) := by exact_mod_cast hf
  have he : phaseFactor K * ((slope * (2 * Real.pi) : ℝ) : ℂ) =
      (m : ℂ) * (2 * Real.pi * Complex.I) := by
    unfold phaseFactor
    push_cast
    calc
      _ = ((K : ℂ) * (slope : ℂ)) * (2 * Real.pi * Complex.I) := by ring
      _ = _ := by rw [hc]
  rw [mode_translate ha hphi, he, Complex.exp_int_mul_two_pi_mul_I, one_mul]






/-! ## Finite harmonic assembly uses one potential -/




theorem spatialCurl_finset_sum {ι : Type} (S : Finset ι) (A : ι → VelocityField)
    {z : SpaceTime} (hA : ∀ i ∈ S, DifferentiableAt ℝ (A i) z) :
    SpatialCurl.spatialCurl (fun w => ∑ i ∈ S, A i w) z =
      ∑ i ∈ S, SpatialCurl.spatialCurl (A i) z := by
  have hs : ∀ i ∈ S, DifferentiableAt ℝ (fun y : Space => A i (z.1, y)) z.2 :=
    fun i hi => (hA i hi).comp z.2 ((differentiableAt_const z.1).prodMk differentiableAt_id)
  change SpatialCurl.curl (fun y : Space => ∑ i ∈ S, A i (z.1, y)) z.2 =
    ∑ i ∈ S, SpatialCurl.curl (fun y : Space => A i (z.1, y)) z.2
  simp only [SpatialCurl.curl, fderiv_fun_sum hs, map_sum]



/-! ## Axis preservation follows from vanishing of the actual source -/






/-! ## Regularity of the constructed physical fields -/


section PhysicalRegularity

variable (D : AssemblyData Parameter) {h Qr : ℝ} {I : ℕ} (H : ReferenceChart D h Qr I)
  {j : ℤ} {α κ : ℝ}
  (C : LocalControl D.reference D.charts D.context D.state D.carrierBlock
    D.gaussianInput D.aliasInput j D.background D.copy D.strip D.directions α κ)
  (hQr : 0 < Qr) {z : SpaceTime} (hz : 0 < z.2 0) (hx : nativeMap h Qr I z ∈ D.strip.domain)
  {delta : ℝ} (hdelta : 0 < delta) (chart : PolarCharts.Index)
  (hchart : z ∈ PhysicalCurlCovariance.validCylindrical delta chart)

include H C hQr hz hx hdelta hchart





end PhysicalRegularity





/-! ## Substitution of the actual target-band residual source -/







/-- Equality with the target block's literal carrier follows from the
primitive unmodulated phase identity and its shared integer angular label. -/
theorem bandPhase_eq_actualCarrier (D : AssemblyData Parameter) (h Q Qr : ℝ)
    (gap n : ℕ) (j : ℤ) (hj : j ≠ 0) (hfrequency : ∀ m, D.carrierBlock.frequency m ≠ 0)
    (hphase : ∀ p Y, D.carrierBlock.frequency n * D.carrierBlock.phase n (p, Y) =
      D.carrierBlock.frequency D.reference.band * D.carrierBlock.phase D.reference.band
        (parameterChange h Q Qr p, coverPower gap Y))
    (hangular : D.carrierBlock.angularFrequency n = D.carrierBlock.angularFrequency D.reference.band) :
    bandPhase D h Q Qr gap ((j : ℝ) * D.carrierBlock.frequency n) j =
      fun x => (actualCarrier D.background D.carrierBlock j).phase n (waveEquiv x) := by
  funext x
  have hK : (j : ℝ) * D.carrierBlock.frequency n ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hj) (hfrequency n)
  apply mul_left_cancel₀ hK
  have hn := actualCarrier_phase D.background D.carrierBlock j hfrequency n
    ((waveEquiv x).1.1, (waveEquiv x).2) (waveEquiv x).1.2
  have hr := actualCarrier_phase D.background D.carrierBlock j hfrequency D.reference.band
    (parameterChange h Q Qr (waveEquiv x).1.1, coverPower gap (waveEquiv x).2) (waveEquiv x).1.2
  change ((j : ℝ) * D.carrierBlock.frequency n) *
    (actualCarrier D.background D.carrierBlock j).phase n (waveEquiv x) = _ at hn
  change referenceFrequency D j * liftPhase D j (cylinderChange h Q Qr gap x) = _ at hr
  rw [hphase, hangular] at hn
  unfold bandPhase
  calc
    _ = referenceFrequency D j * liftPhase D j (cylinderChange h Q Qr gap x) := by
      field_simp [hfrequency n]
    _ = _ := hr.trans hn.symm

end
end NavierStokes.PhysicalParticularWave
