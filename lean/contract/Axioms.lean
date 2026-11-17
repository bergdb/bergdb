/-
The gate of bergdb 030-04, section 7.6: the axioms that the theorems rest on.
`lake env lean Axioms.lean` prints them; gate.sh checks that they are Lean's
three standard ones only.
-/
import Contract

open Contract

#print axioms inv_right
#print axioms get_right
#print axioms scan_right
#print axioms checkTx_sound
#print axioms Contract.Example.meets
