import Mathlib.Probability.Distributions
import DPLib.Basic


/--
`laplaceMeasure r` is the law of `S * X`, where `X ~ Exp(r)` and `S ∈ {+1,-1}` is symmetric:
with weight `1/2` return `X`, and with weight `1/2` return `-X`.

Equivalently: a 0.5/0.5 mixture of `Exp(r)` and the pushforward of `Exp(r)` by `x ↦ -x`.
-/
noncomputable def laplaceMeasure (r : ℝ) : Measure ℝ :=
  ((1 : ℝ≥0∞) / 2) • (expMeasure r) +
  ((1 : ℝ≥0∞) / 2) • (Measure.map (fun x : ℝ => -x) (expMeasure r))


def LaplaceMechanism (ι α : Type*) (query: Query ι α ℝ) (Δ ε : ℝ) [ε > 0] : Mechanism ι α ℝ :=
  fun db =>
    let real_result := query db
    let scale := Δ / ε
    let noise ← LaplaceDistribution real_result scale.sample
    return real_result + noise


theorem laplace_mechanism_is_dp (query : Query ι α ℝ) (Δ ε : ℝ)
    (h_sensitivity : has_sensitivity query Δ) :
    is_epsilon_dp (LaplaceMechanism ι α query Δ ε) ε := by
  sorry
