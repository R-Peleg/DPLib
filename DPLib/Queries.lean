import Mathlib.Data.Fintype.Card
import Mathlib.Topology.Instances.Nat
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Finset.Card
import DPLib.Basic
variable {ι α β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α] [MeasurableSpace β]


def countMatching (criteria : α -> Bool) : Query ι α ℕ :=
  fun db => (Finset.univ.filter (fun i => criteria (db i))).card

def countEntries : Query ι α ℕ :=
  countMatching (fun _ => true)

theorem count_sensitivity_one (criteria : α → Bool) :
    has_sensitivity (countMatching criteria : Query ι α ℕ) 1 := by
  rw [has_sensitivity]
  intro db1 db2 h_neighbors
  rw [Nat.dist_eq, countMatching, countMatching]
  unfold are_neighbors hammingDist at h_neighbors
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp h_neighbors

  let S1 := (Finset.univ.filter (fun i => criteria (db1 i)))
  let S2 := (Finset.univ.filter (fun i => criteria (db2 i)))

  calc |(S1.card : ℝ) - (S2.card: ℝ)|

  _ <= 1 := by sorry
