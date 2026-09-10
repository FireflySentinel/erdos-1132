import Erdos1132

/-! Axiom checks for both manuscripts' main theorems and corollaries. -/

/-- info: 'Erdos1132.theorem1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Erdos1132.theorem1

/-- info: 'Erdos1132.theorem2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Erdos1132.theorem2

/-- info: 'Erdos1132.positive_measure_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Erdos1132.positive_measure_lower_bound

/-- info: 'Erdos1132.no_uniform_interval_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Erdos1132.no_uniform_interval_constant
