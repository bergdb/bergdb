import Check.Steps
/-! Review probe (031-06, review-main, R7): STEP-action on a record without a step that holds
its action's put and a second operation at the same key. Run from lean/, after `lake build`:
`lake env lean <this file>`. An empty list of failures is printed: the record passes. -/
open SIS.Check in
#eval actionFailures [(.put [16] 5, false), (.put [16] 6, false)] [] [.put [16] 5] false
open SIS.Check in
#eval actionFailures [(.put [16] 5, false), (.del [16], false)] [] [.put [16] 5] false
