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

-- TODO: Import from mathlib once we upgrade our version
lemma card_sub_card_eq (s t : Finset α) : t.card - s.card = (t \ s).card - (s \ t).card :=
  calc
    t.card - s.card = t.card - (s ∩ t).card - (s \ t).card := by grind
    _ = (t \ (s ∩ t)).card - (s \ t).card := by grind
    _ = (t \ s).card - (s \ t).card := by grind

theorem count_sensitivity_one (criteria : α → Bool) :
    has_sensitivity (countMatching criteria : Query ι α ℕ) 1 := by
  rw [has_sensitivity]
  intro db1 db2 h_neighbors
  rw [Nat.dist_eq, countMatching, countMatching]
  unfold are_neighbors hammingDist at h_neighbors
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp h_neighbors

  let S1 := (Finset.univ.filter (fun i => criteria (db1 i)))
  let S2 := (Finset.univ.filter (fun i => criteria (db2 i)))
  have h_diff_card : S1 \ S2 ⊆ {k} ∧ S2 \ S1 ⊆ {k} := by grind
  have h_card_diff1 : S1.card - S2.card <= 1 := by
    rw [card_sub_card_eq]
    by_cases k ∈ S1 \ S2
    · have h1: (S1 \ S2) == {k} := by grind
      grind
    · have h1: (S1 \ S2) == {} := by grind
      grind
  have h_card_diff1_R : (S1.card : ℝ) - (S2.card : ℝ) <= 1 := by
    simp
    simp at h_card_diff1
    norm_cast
  have h_card_diff2 : S2.card - S1.card <= 1 := by
    rw [card_sub_card_eq]
    by_cases k ∈ S2 \ S1
    · have h1: (S2 \ S1) == {k} := by grind
      grind
    · have h1: (S2 \ S1) == {} := by grind
      grind
  have h_card_diff2_R : (S2.card : ℝ) - (S1.card : ℝ) <= 1 := by
    simp
    simp at h_card_diff2
    norm_cast

  have h_card_abs_diff : |(S1.card : ℝ) - (S2.card: ℝ)| <= 1 := by
    by_cases h_pos : 0 ≤ (S1.card : ℝ) - (S2.card : ℝ)
    · rw [abs_eq_self.mpr h_pos]
      linarith
    · push_neg at h_pos
      apply le_of_lt at h_pos
      rw [abs_eq_neg_self.mpr h_pos]
      linarith
  grind
