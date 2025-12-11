import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.MeasureSpace

open MeasureTheory

variable {ι α β : Type*} [Fintype ι] [DecidableEq α] [MeasurableSpace β]

/--
A Database is a mapping from a finite set of indices
to a data type α (values).
-/
abbrev Database (ι α : Type*) := ι → α

/--
Hamming distance between two databases.
Defined as the number of inputs for which the outputs differ.
-/
def hammingDist (f g : Database ι α) : ℕ :=
  (Finset.univ.filter (fun i => f i ≠ g i)).card

/--
Formal neighbors defintion: Hamming distance = 1
We use the form that combines edits, addtions and removals together.
-/
def are_neighbors (f g : Database ι α) : Prop :=
  hammingDist f g = 1

/--
A Query is a deterministic function from a Database to a result type β.
-/
def Query (ι α β : Type*) := Database ι α → β

/--
A Mechanism is a function from a Database to a probability Measure over the output type β.
-/
def Mechanism (ι α β : Type*) [MeasurableSpace β] := Database ι α → ProbabilityMeasure β

/--
The formal definition of Pure ε-Differential Privacy.
-/
def is_epsilon_dp (M : Mechanism ι α β) (ε : ℝ) : Prop :=
  ∀ (d1 d2 : Database ι α) (S : Set β),
  are_neighbors d1 d2 → MeasurableSet S →
  (M d1 S) ≤ ENNReal.ofReal (Real.exp ε) * (M d2 S)

def is_item_epsilon_dp (M : Mechanism ι α β) (ε : ℝ) : Prop :=
  ∀ (d1 d2 : Database ι α) (s : β), are_neighbors d1 d2 →
  (M d1 {s}) ≤ ENNReal.ofReal (Real.exp ε) * (M d2 {s})


theorem dp_item_to_set (m : Mechanism ι α β) (ε : ℝ) (h : is_item_epsilon_dp m ε) :
is_epsilon_dp m ε := by

  sorry

theorem dp_set_to_item (m : Mechanism ι α β) (ε : ℝ) (h : is_epsilon_dp m ε) :
is_item_epsilon_dp m ε := by
  sorry

theorem dp_set_items_eq (m : Mechanism ι α β) (ε : ℝ) :
  is_epsilon_dp m ε ↔ is_item_epsilon_dp m ε := by
  constructor
  · apply dp_set_to_item
  · apply dp_item_to_set

theorem dp_mono_epsilon (m : Mechanism ι α β) (ε₁ ε₂ : ℝ) (H1 : ε₁ ≤ ε₂) (H2 : is_pure_dp) :
is_epsilon_dp m ε₁ → is_epsilon_dp m ε₂ := by
  sorry
