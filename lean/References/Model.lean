/-
An exploratory reference model, independent of SIS's proved write algorithm.
See docs/reference-theory.md for the proposal and the limits of these proofs.

Resident object IDs model direct references, not an implementation map lookup.
This model covers immutable, exactly backed images. Dirty canonical bodies,
writer promotion, reclaim scheduling, and Java concurrency are not modeled.
-/
import Lean

namespace BergDB.References

abbrev Address := Nat
abbrev ObjectId := Nat
abbrev SnapshotTime := Nat

inductive Step where
  | value (v : Nat)
  | down (address : Address)
  deriving DecidableEq, Repr

/-- A stored image may contain routing or value changes over time. -/
structure Image where
  nodeId : Nat
  history : List (SnapshotTime × Step)
  deriving DecidableEq, Repr

/-- Histories in the examples are in chronological order. -/
def Image.at (image : Image) (time : SnapshotTime) : Option Step :=
  (image.history.reverse.find? (fun entry => entry.1 ≤ time)).map Prod.snd

/-- A physical object, including its outgoing direct references. -/
structure Body where
  address : Address
  image : Image
  links : List (Address × ObjectId)

abbrev Disk := Address → Option Image
abbrev Heap := ObjectId → Option Body

/-- The backing address survives installing/removing a resident reference. -/
structure Ref where
  anchor : Address
  resident : Option ObjectId
  deriving DecidableEq, Repr

def emptyHeap : Heap := fun _ => none

def detach (ref : Ref) : Ref := { ref with resident := none }

def fetch (disk : Disk) (heap : Heap) (ref : Ref) : Option Body :=
  match ref.resident with
  | some objectId => heap objectId
  | none => (disk ref.anchor).map (fun image => ⟨ref.anchor, image, []⟩)

/-- Exactly backed images: stronger than answering one historical query. -/
def Backed (disk : Disk) (heap : Heap) : Prop :=
  ∀ objectId body, heap objectId = some body → disk body.address = some body.image

/-- Every installed direct reference identifies the image its anchor names. -/
def LinksAligned (heap : Heap) : Prop :=
  ∀ objectId body, heap objectId = some body →
    ∀ address childId, List.lookup address body.links = some childId →
      ∃ child, heap childId = some child ∧ child.address = address

def Aligned (heap : Heap) (ref : Ref) : Prop :=
  match ref.resident with
  | none => True
  | some objectId => ∃ body, heap objectId = some body ∧ body.address = ref.anchor

inductive Result where
  | value (v : Nat)
  | absent
  | expired
  | missing
  | exhausted
  deriving DecidableEq, Repr

/-- Operational traversal: a resident hit directly dereferences the object;
only a cold reference reads the disk. No logical oracle supplies the answer. -/
def walk (disk : Disk) (heap : Heap) (time : SnapshotTime) : Nat → Ref → Result
  | 0, _ => .exhausted
  | fuel + 1, ref =>
    match fetch disk heap ref with
    | none => .missing
    | some body =>
      match body.image.at time with
      | none => .absent
      | some (.value v) => .value v
      | some (.down address) =>
        walk disk heap time fuel ⟨address, List.lookup address body.links⟩

/-- An independently defined all-cold traversal. -/
def diskWalk (disk : Disk) (time : SnapshotTime) : Nat → Address → Result
  | 0, _ => .exhausted
  | fuel + 1, address =>
    match disk address with
    | none => .missing
    | some image =>
      match image.at time with
      | none => .absent
      | some (.value v) => .value v
      | some (.down next) => diskWalk disk time fuel next

theorem fetch_image (disk : Disk) (heap : Heap) (ref : Ref)
    (backed : Backed disk heap) (aligned : Aligned heap ref) :
    (fetch disk heap ref).map (fun body => body.image) = disk ref.anchor := by
  cases hr : ref.resident with
  | none => cases hd : disk ref.anchor <;> simp [fetch, hr, hd]
  | some objectId =>
    obtain ⟨body, hb, ha⟩ := (by simpa [Aligned, hr] using aligned)
    have hd := backed objectId body hb
    simpa [fetch, hr, hb, ha] using hd.symm

theorem fetched_links_aligned (disk : Disk) (heap : Heap) (ref : Ref)
    (links : LinksAligned heap) (body : Body)
    (fetched : fetch disk heap ref = some body) (address : Address) :
    Aligned heap ⟨address, List.lookup address body.links⟩ := by
  cases hr : ref.resident with
  | none =>
    cases hd : disk ref.anchor with
    | none => simp [fetch, hr, hd] at fetched
    | some image =>
      have heq : (⟨ref.anchor, image, []⟩ : Body) = body := by
        simpa [fetch, hr, hd] using fetched
      subst body
      simp [Aligned]
  | some objectId =>
    have hb : heap objectId = some body := by simpa [fetch, hr] using fetched
    cases hl : List.lookup address body.links with
    | none => simp [Aligned]
    | some childId =>
      simpa [Aligned, hl] using links objectId body hb address childId hl

/-- Cache invariance for the exactly backed subgraph, including shared children
and several images of one logical node. -/
theorem cache_invariance (disk : Disk) (heap : Heap) (time : SnapshotTime)
    (fuel : Nat) (ref : Ref) (backed : Backed disk heap)
    (links : LinksAligned heap) (aligned : Aligned heap ref) :
    walk disk heap time fuel ref = diskWalk disk time fuel ref.anchor := by
  induction fuel generalizing ref with
  | zero => rfl
  | succ fuel ih =>
    have himage := fetch_image disk heap ref backed aligned
    cases hf : fetch disk heap ref with
    | none =>
      have hd : disk ref.anchor = none := by simpa [hf] using himage.symm
      simp [walk, diskWalk, hf, hd]
    | some body =>
      have hd : disk ref.anchor = some body.image := by
        simpa [hf] using himage.symm
      cases hs : body.image.at time with
      | none => simp [walk, diskWalk, hf, hd, hs]
      | some step =>
        cases step with
        | value v => simp [walk, diskWalk, hf, hd, hs]
        | down address =>
          simp only [walk, diskWalk, hf, hd, hs]
          exact ih ⟨address, List.lookup address body.links⟩
            (fetched_links_aligned disk heap ref links body hf address)

theorem detach_preserves_read (disk : Disk) (heap : Heap) (time : SnapshotTime)
    (fuel : Nat) (ref : Ref) (backed : Backed disk heap)
    (links : LinksAligned heap) (aligned : Aligned heap ref) :
    walk disk heap time fuel (detach ref) = walk disk heap time fuel ref := by
  rw [cache_invariance disk heap time fuel (detach ref) backed links
    (by simp [Aligned, detach])]
  rw [cache_invariance disk heap time fuel ref backed links aligned]
  rfl

/-- The serialized reference is the stable anchor, never a residency hint. -/
def storedReference (ref : Ref) : Address := ref.anchor

theorem detach_preserves_reference (ref : Ref) :
    storedReference (detach ref) = storedReference ref := rfl

def cut (disk : Disk) (firstAddress : Address) : Disk :=
  fun address => if address < firstAddress then none else disk address

/-- The actual path selected at this time stays above a proposed cut.
This checks the concrete routing choices; it is not just a cached-answer test.
It says nothing about the production algorithm establishing this property. -/
def RetainedPath (disk : Disk) (time : SnapshotTime) (firstAddress : Address) :
    Nat → Address → Prop
  | 0, _ => True
  | fuel + 1, address =>
    firstAddress ≤ address ∧
      match disk address with
      | none => True
      | some image =>
        match image.at time with
        | some (.down next) => RetainedPath disk time firstAddress fuel next
        | _ => True

theorem cut_preserves_path (disk : Disk) (time : SnapshotTime)
    (firstAddress fuel address : Nat)
    (retained : RetainedPath disk time firstAddress fuel address) :
    diskWalk (cut disk firstAddress) time fuel address =
      diskWalk disk time fuel address := by
  induction fuel generalizing address with
  | zero => rfl
  | succ fuel ih =>
    have hbound : firstAddress ≤ address := retained.1
    have hcut : cut disk firstAddress address = disk address := by
      simp [cut, Nat.not_lt.mpr hbound]
    cases hd : disk address with
    | none => simp [diskWalk, hcut, hd]
    | some image =>
      cases hs : image.at time with
      | none => simp [diskWalk, hcut, hd, hs]
      | some step =>
        cases step with
        | value v => simp [diskWalk, hcut, hd, hs]
        | down next =>
          simp only [diskWalk, hcut, hd, hs]
          exact ih next (by simpa [RetainedPath, hd, hs] using retained.2)

/-- One finite actual snapshot is retained. This model rejects expired requests
at a query boundary; it does not model a cut midway through a Java operation. -/
def query (frontier : SnapshotTime) (disk : Disk) (heap : Heap)
    (time : SnapshotTime) (fuel : Nat) (ref : Ref) : Result :=
  if time < frontier then .expired else walk disk heap time fuel ref

/-- Joint cache/cut safety for an available concrete path. Independently chosen
pre/post-cut heaps are permitted, provided each satisfies its backing contract. -/
theorem cache_cut_composition (frontier time firstAddress fuel : Nat)
    (disk : Disk) (before after : Heap) (rBefore rAfter : Ref)
    (sameAnchor : rBefore.anchor = rAfter.anchor)
    (beforeBacked : Backed disk before) (beforeLinks : LinksAligned before)
    (beforeAligned : Aligned before rBefore)
    (afterBacked : Backed (cut disk firstAddress) after)
    (afterLinks : LinksAligned after) (afterAligned : Aligned after rAfter)
    (retained : RetainedPath disk time firstAddress fuel rBefore.anchor) :
    query frontier disk before time fuel rBefore =
      query frontier (cut disk firstAddress) after time fuel rAfter := by
  by_cases expired : time < frontier
  · simp [query, expired]
  · simp only [query, expired, ↓reduceIte]
    rw [cache_invariance disk before time fuel rBefore
      beforeBacked beforeLinks beforeAligned]
    rw [cache_invariance (cut disk firstAddress) after time fuel rAfter
      afterBacked afterLinks afterAligned]
    rw [← sameAnchor]
    exact (cut_preserves_path disk time firstAddress fuel rBefore.anchor retained).symm

/-- The existing cache-preference pattern, represented only as a local example. -/
def preferredReference (anchor : Address) (preferred : Option Address) : Address :=
  preferred.getD anchor

theorem preferred_reference_is_cache_dependent :
    preferredReference 100 (some 200) ≠ preferredReference 100 none := by decide

/-- The information available in this particular proposed writer resolver. -/
structure WriterObservation where
  anchor : Address
  recentWrites : List (Nat × Address)
  deriving DecidableEq, Repr

def observe (writes : List (Nat × Address)) (anchor tailStart : Address) :
    WriterObservation :=
  ⟨anchor, writes.filter (fun entry => tailStart ≤ entry.2)⟩

def latestWrite (writes : List (Nat × Address)) (nodeId : Nat) : Option Address :=
  (writes.reverse.find? (fun entry => entry.1 == nodeId)).map Prod.snd

def oldWrites : List (Nat × Address) := [(1, 100)]
def rewrittenWrites : List (Nat × Address) := [(1, 100), (1, 200)]

/-- An anchor and a recent-write directory cannot tell these two older write
histories apart. This is a limitation of precisely this observation set, not
an impossibility theorem for every possible database architecture. -/
theorem no_latest_from_anchor_and_tail :
    ¬ ∃ resolve : WriterObservation → Option Address,
      ∀ writes, resolve (observe writes 100 250) = latestWrite writes 1 := by
  rintro ⟨resolve, correct⟩
  have hOld := correct oldWrites
  have hNew := correct rewrittenWrites
  change resolve ⟨100, []⟩ = some 100 at hOld
  change resolve ⟨100, []⟩ = some 200 at hNew
  have impossible : (some 100 : Option Address) = some 200 := hOld.symm.trans hNew
  exact (by decide : (some 100 : Option Address) ≠ some 200) impossible

end BergDB.References
