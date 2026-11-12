import SIS.Tree.KlongRoundTripBits

namespace SIS.Tree

open SIS SIS.Check

abbrev KlongParseState := List Klong × Option Time × List Nat
abbrev KlongEntryState := History BVal × Time × List Nat × Bool

def parseKlongEntry (acc : KlongParseState) (e : Entry BVal) : KlongParseState :=
  let ks := if acc.2.1 == some e.time then acc.1 else acc.1 ++ [.time e.time]
  match e.val with
  | .key c y => (ks ++ [.key c y],some e.time,acc.2.2)
  | .del [] => (ks,some e.time,acc.2.2)
  | .del cs =>
    let bits := bitsUnion acc.2.2 (bitmapMore ks cs)
    (ks ++ [.del bits],some e.time,bits)
  | _ => (ks,some e.time,acc.2.2)

def parseKlongEntries (es : History BVal) : KlongParseState :=
  es.foldl parseKlongEntry ([],none,[])

def encodeKlong (ks : List Klong) (acc : KlongEntryState) (k : Klong) : KlongEntryState :=
  match k with
  | .time t =>
    (if acc.2.2.2 then acc.1 else acc.1 ++ [⟨acc.2.1,marker⟩],t,acc.2.2.1,false)
  | .key c y => (acc.1 ++ [⟨acc.2.1,.key c y⟩],acc.2.1,acc.2.2.1,true)
  | .del bits =>
    (acc.1 ++ [⟨acc.2.1,.del (bitmapEntryCvs ks acc.2.2.1 bits)⟩],acc.2.1,bits,true)

def finishKlongEntries (acc : KlongEntryState) : History BVal :=
  if acc.2.2.2 then acc.1 else acc.1 ++ [⟨acc.2.1,marker⟩]

def encodedKlongEntry (ks : List Klong) (acc : KlongEntryState) (k : Klong) : Entry BVal :=
  match k with
  | .time t => ⟨t,marker⟩
  | .key c y => ⟨acc.2.1,.key c y⟩
  | .del bits => ⟨acc.2.1,.del (bitmapEntryCvs ks acc.2.2.1 bits)⟩

theorem klongsOf_eq_parse (es : History BVal) : klongsOf es = (parseKlongEntries es).1 := rfl

theorem entriesOf_eq_encode (ks : List Klong) :
    entriesOf ks = finishKlongEntries (ks.foldl (encodeKlong ks) ([],0,[],true)) := rfl

theorem parse_marker_entry (acc : KlongParseState) (t : Time) (v : BVal) :
    parseKlongEntry (parseKlongEntry acc ⟨t,marker⟩) ⟨t,v⟩ =
      parseKlongEntry acc ⟨t,v⟩ := by
  rcases acc with ⟨pre,ot,bits⟩
  cases v with
  | key c y => simp [parseKlongEntry,marker]
  | del cs => cases cs <;> simp [parseKlongEntry,marker]
  | rootKey y => simp [parseKlongEntry,marker]
  | skip j z => simp [parseKlongEntry,marker]
  | top z => simp [parseKlongEntry,marker]
  | data h => simp [parseKlongEntry,marker]

/-- Finishing the pending time marker commutes with the next encoded entry.
This transducer fact is independent of well-formedness. -/
theorem parse_encode_step (ks : List Klong) (acc : KlongEntryState) (k : Klong) :
    parseKlongEntries (finishKlongEntries (encodeKlong ks acc k)) =
      parseKlongEntry (parseKlongEntries (finishKlongEntries acc))
        (encodedKlongEntry ks acc k) := by
  rcases acc with ⟨es,t,bits,had⟩
  cases had <;> cases k <;>
    simp [encodeKlong,encodedKlongEntry,finishKlongEntries,parseKlongEntries,
      List.foldl_append,List.append_assoc,parse_marker_entry]

def klongEntriesState (ks : List Klong) (j : Nat) : KlongEntryState :=
  (ks.take j).foldl (encodeKlong ks) ([],0,[],true)

theorem klongEntriesState_step (ks : List Klong) (i : Nat) (k : Klong)
    (hk : ks[i]? = some k) :
    klongEntriesState ks (i+1) = encodeKlong ks (klongEntriesState ks i) k := by
  simp only [klongEntriesState,List.take_add_one,hk,Option.toList_some,
    List.foldl_append,List.foldl_cons,List.foldl_nil]

theorem parse_encode_prefix (ks : List Klong) (hw : klongsWf ks = true)
    (j : Nat) (hj : j ≤ ks.length) :
    parseKlongEntries (finishKlongEntries (klongEntriesState ks j)) =
        (ks.take j,(klongsWfState ks j).2.1,(klongsWfState ks j).2.2) ∧
      (klongEntriesState ks j).2.1 = (klongsWfState ks j).2.1.getD 0 ∧
      (klongEntriesState ks j).2.2.1 = (klongsWfState ks j).2.2 := by
  induction j with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ j ih =>
    have hj' : j < ks.length := by omega
    have hk : ks[j]? = some ks[j] := List.getElem?_eq_getElem hj'
    obtain ⟨hparse,htime,hbits⟩ := ih (by omega)
    have hs := klongsWfState_ok ks hw (j+1)
    rw [klongsWfState_succ ks j ks[j] hk] at hs
    rw [klongEntriesState_step ks j ks[j] hk,klongsWfState_succ ks j ks[j] hk,
      parse_encode_step,hparse,List.take_add_one,hk]
    cases he : ks[j] with
    | time t =>
      have hneq : (klongsWfState ks j).2.1 ≠ some t := by
        intro ht
        simp [klongsWfStep,he,ht] at hs
      simp [encodeKlong,encodedKlongEntry,klongsWfStep,parseKlongEntry,marker,
        hneq,htime,hbits]
    | key c y =>
      have hsome : (klongsWfState ks j).2.1.isSome = true := by
        simp only [klongsWfStep,he,Bool.and_eq_true] at hs
        exact hs.2
      have ht : (klongsWfState ks j).2.1 = some (klongEntriesState ks j).2.1 := by
        rw [htime]
        cases ht : (klongsWfState ks j).2.1 <;> simp_all
      simp [encodeKlong,encodedKlongEntry,klongsWfStep,parseKlongEntry,ht,hbits]
    | del bits =>
      have hsome : (klongsWfState ks j).2.1.isSome = true := by
        simp only [klongsWfStep,he,Bool.and_eq_true] at hs
        exact hs.1.1.1.1.1.2
      have ht : (klongsWfState ks j).2.1 = some (klongEntriesState ks j).2.1 := by
        rw [htime]
        cases ht : (klongsWfState ks j).2.1 <;> simp_all
      rw [he] at hk
      have hn := bitmapEntryCvs_ne_nil ks hw j bits hk
      have hb := bitmapEntryCvs_roundTrip ks hw j bits hk
      have hbits' : (klongEntriesState ks j).2.2.1 = lastBitmapOf (ks.take j) :=
        hbits.trans (klongsWfState_bitmap ks j)
      cases hc : bitmapEntryCvs ks (lastBitmapOf (ks.take j)) bits with
      | nil => exact (hn hc).elim
      | cons a cs =>
        simp only [hc] at hb
        simp [encodeKlong,encodedKlongEntry,klongsWfStep,parseKlongEntry,
          ht,hbits',klongsWfState_bitmap,hc,hb]

theorem klongsRoundTrip : KlongsRoundTrip := by
  intro ks hw
  have h := (parse_encode_prefix ks hw ks.length (Nat.le_refl _)).1
  simpa only [klongsOf_eq_parse,entriesOf_eq_encode,klongEntriesState,List.take_length]
    using congrArg Prod.fst h

end SIS.Tree
