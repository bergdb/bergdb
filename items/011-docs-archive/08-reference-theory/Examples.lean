/- Executable reference examples and negative controls. See Model.lean. -/
import References.Model

namespace BergDB.References.Examples

def oldChild : Image := ⟨1, [(0, .value 7)]⟩
def newChild : Image := ⟨1, [(0, .value 7), (5, .value 9)]⟩
def parent : Image := ⟨2, [(0, .down 100), (5, .down 200)]⟩
def historicalParent : Image := ⟨3, [(0, .down 100)]⟩
def rewrittenParent : Image := ⟨2, [(0, .down 100), (5, .down 600)]⟩

def disk : Disk := fun address => List.lookup address
  [(100, oldChild), (200, newChild), (300, parent),
   (350, historicalParent), (600, newChild), (700, rewrittenParent)]

def heap : Heap := fun objectId => List.lookup objectId
  [(10, ⟨100, oldChild, []⟩),
   (20, ⟨200, newChild, []⟩),
   (30, ⟨300, parent, [(100, 10), (200, 20)]⟩),
   (35, ⟨350, historicalParent, [(100, 10)]⟩)]

/-- Both parents detach the shared child before its object is removed. -/
def evictedHeap : Heap := fun objectId => List.lookup objectId
  [(20, ⟨200, newChild, []⟩),
   (30, ⟨300, parent, [(200, 20)]⟩),
   (35, ⟨350, historicalParent, []⟩)]

def rootWarm : Ref := ⟨300, some 30⟩
def rootCold : Ref := ⟨300, none⟩

-- Two different physical images of node 1 answer different actual snapshots.
#guard oldChild.nodeId = newChild.nodeId
#guard walk disk heap 2 3 rootWarm = .value 7
#guard walk disk heap 6 3 rootWarm = .value 9
#guard walk disk emptyHeap 2 3 rootCold = .value 7
#guard walk disk emptyHeap 6 3 rootCold = .value 9

-- A shared child can become cold under both historical parents.
#guard walk disk evictedHeap 2 3 rootWarm = .value 7
#guard walk disk evictedHeap 2 3 ⟨350, some 35⟩ = .value 7
#guard walk disk heap 2 3 ⟨350, some 35⟩ = .value 7

-- An incorrect same-ID promotion installs the older image at the newer anchor.
def wrongHeap : Heap := fun objectId =>
  if objectId = 30 then some ⟨300, parent, [(100, 10), (200, 10)]⟩
  else heap objectId
#guard walk disk wrongHeap 6 3 rootWarm = .value 7
#guard walk disk wrongHeap 6 3 rootWarm ≠ diskWalk disk 6 3 300

-- A warm answer can hide an invalid cut. The cold path still needs address 100.
#guard walk (cut disk 150) heap 2 3 rootWarm = .value 7
#guard walk (cut disk 150) emptyHeap 2 3 rootCold = .missing
example : ¬ RetainedPath disk 2 150 3 300 := by
  change ¬ (150 ≤ 300 ∧ (150 ≤ 100 ∧ True))
  decide

-- At time 6 the selected old root/child addresses both survive that cut.
example : RetainedPath disk 6 150 3 300 := by
  change 150 ≤ 300 ∧ (150 ≤ 200 ∧ True)
  decide
#guard walk (cut disk 150) emptyHeap 6 3 rootCold = .value 9

-- Reclaim copies the child and rewrites the available root route before
-- cutting more aggressively. The old, expired branch remains in its history.
def rewrittenHeap : Heap := fun objectId => List.lookup objectId
  [(60, ⟨600, newChild, []⟩),
   (70, ⟨700, rewrittenParent, [(600, 60)]⟩)]
def rewrittenRoot : Ref := ⟨700, some 70⟩
example : RetainedPath disk 6 500 3 700 := by
  change 500 ≤ 700 ∧ (500 ≤ 600 ∧ True)
  decide
#guard walk disk heap 6 3 rootWarm =
  walk (cut disk 500) rewrittenHeap 6 3 rewrittenRoot
#guard query 5 (cut disk 500) rewrittenHeap 6 3 rewrittenRoot = .value 9
#guard query 5 (cut disk 500) emptyHeap 6 3 ⟨700, none⟩ = .value 9

-- The same finite time is used on retry. Moving from 2 to 6 changes the answer.
#guard query 5 disk heap 2 3 rootWarm = .expired
#guard query 5 (cut disk 500) rewrittenHeap 2 3 rewrittenRoot = .expired
#guard walk disk heap 2 3 rootWarm ≠ walk disk heap 6 3 rootWarm

-- Query-equivalent newer images still change the original latest-reference
-- rule when the writer uses a discretionary preferred cache entry.
#guard preferredReference 100 (some 200) = 200
#guard preferredReference 100 none = 100
#guard storedReference ⟨100, some 10⟩ = storedReference ⟨100, some 20⟩
#guard storedReference (detach ⟨100, some 10⟩) = 100

-- Identical bounded observations, but different globally latest addresses.
#guard observe oldWrites 100 250 = observe rewrittenWrites 100 250
#guard latestWrite oldWrites 1 ≠ latestWrite rewrittenWrites 1

#print axioms cache_invariance
#print axioms detach_preserves_read
#print axioms cut_preserves_path
#print axioms cache_cut_composition
#print axioms no_latest_from_anchor_and_tail

end BergDB.References.Examples
