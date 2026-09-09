import Euler.StrongOperatorDerivative
import Euler.MetricHeatEnergy

/-! The genuine cylinder heat semigroup solves the Laplacian evolution equation. -/

noncomputable section

namespace EulerGaussianCylinderHeat

open MeasureTheory EulerLiftedGradientSpace EulerPressureSpatialRegularity EulerSpatialSobolevInverse
  EulerCylinderSobolev EulerMetricHeatEnergy EulerStrongOperatorDerivative
open scoped ENNReal NNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The real extension of a finite commuting heat product. -/
def realHeatList (directions : List LiftTangent) (t : ℝ) (f : LiftL2 period) : LiftL2 period :=
  match directions with
  | [] => f
  | a :: tail => realLineHeat period a t (realHeatList tail t f)


theorem realLineHeat_add (a : LiftTangent) (t : ℝ) (f g : LiftL2 period) :
    realLineHeat period a t (f+g) = realLineHeat period a t f + realLineHeat period a t g := by
  simp only [realLineHeat_eq_toNNReal, lineHeat_add]

theorem realLineHeat_smul (a : LiftTangent) (t c : ℝ) (f : LiftL2 period) :
    realLineHeat period a t (c • f) = c • realLineHeat period a t f := by
  simp only [realLineHeat_eq_toNNReal, lineHeat_smul]

theorem realHeatList_add (directions : List LiftTangent) (t : ℝ) (f g : LiftL2 period) :
    realHeatList period directions t (f+g) = realHeatList period directions t f + realHeatList period directions t g := by
  induction directions with
  | nil => rfl
  | cons a tail ih => simp only [realHeatList, ih, realLineHeat_add]




theorem realHeatList_eq_toNNReal (directions : List LiftTangent) (t : ℝ) (f : LiftL2 period) :
    realHeatList period directions t f = heatList period directions t.toNNReal f := by
  induction directions with
  | nil => rfl
  | cons a tail ih =>
    change realLineHeat period a t (realHeatList period tail t f) =
      lineHeat period a t.toNNReal (heatList period tail t.toNNReal f)
    rw [realLineHeat_eq_toNNReal, ih]


/-- Every strong coordinate derivative commutes with every finite heat product. -/
theorem realHeatList_strongDerivative (directions : List LiftTangent) (a : LiftTangent) (t : ℝ)
    (f g : LiftL2 period) (hD : HasDerivAt (lineOrbit period a f) g 0) :
    HasDerivAt (lineOrbit period a (realHeatList period directions t f))
      (realHeatList period directions t g) 0 := by
  induction directions with
  | nil => exact hD
  | cons b tail ih =>
    simp only [realHeatList, realLineHeat_eq_toNNReal]
    exact lineHeat_strongDerivative period b a t.toNNReal _ _ ih

/-- The finite directional heat product has the sum of its actual second derivatives as generator. -/
theorem realHeatList_generator_pos {ι : Type*} (indices : List ι) (direction : ι → LiftTangent)
    (f : LiftL2 period) (df ddf : ι → LiftL2 period)
    (hD : ∀ i ∈ indices, HasDerivAt (lineOrbit period (direction i) f) (df i) 0)
    (hDD : ∀ i ∈ indices, HasDerivAt (lineOrbit period (direction i) (df i)) (ddf i) 0)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => realHeatList period (indices.map direction) s f)
      ((1/2 : ℝ) • realHeatList period (indices.map direction) t ((indices.map ddf).sum)) t := by
  induction indices with
  | nil => simpa only [List.map_nil, List.sum_nil, realHeatList, smul_zero] using hasDerivAt_const t f
  | cons i tail ih =>
    have htailD := fun j hj => hD j (List.mem_cons_of_mem i hj)
    have htailDD := fun j hj => hDD j (List.mem_cons_of_mem i hj)
    have hinput := ih htailD htailDD
    have hfirst := realHeatList_strongDerivative period (tail.map direction) (direction i) t f (df i)
      (hD i (List.mem_cons_self ..))
    have hsecond := realHeatList_strongDerivative period (tail.map direction) (direction i) t (df i) (ddf i)
      (hDD i (List.mem_cons_self ..))
    have h := realLineHeat_varying_input period (direction i)
      (fun s => realHeatList period (tail.map direction) s f) t _ _ _ ht hinput hfirst hsecond
    have halg : realLineHeat period (direction i) t
          ((1/2 : ℝ) • realHeatList period (tail.map direction) t ((tail.map ddf).sum)) +
        (1/2 : ℝ) • realLineHeat period (direction i) t (realHeatList period (tail.map direction) t (ddf i)) =
        (1/2 : ℝ) • realHeatList period ((i::tail).map direction) t (((i::tail).map ddf).sum) := by
      rw [realLineHeat_smul, ← smul_add, ← realLineHeat_add, ← realHeatList_add]
      simp only [List.map_cons, List.sum_cons, realHeatList]
      rw [add_comm ((tail.map ddf).sum)]
    rwa [halg] at h


end EulerGaussianCylinderHeat
