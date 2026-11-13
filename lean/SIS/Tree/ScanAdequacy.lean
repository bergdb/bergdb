import SIS.Tree.ScanStep

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Every next-step result retains the structural chain bound, even when
called with too little fuel (in that case the reader clears the chain). -/
theorem nextGo_scanChain (p : Params) (v : View BVal) (t : Time) (req : ScanReq)
    (bound fuel : Nat) (ch : Chain) (hc : ScanChain p v t bound ch.links) :
    ScanChain p v t bound (nextGo p v t req fuel ch).2.links := by
  induction fuel generalizing ch with
  | zero => trivial
  | succ fuel ih =>
    cases hl : ch.links with
    | nil => simp [nextGo, hl, ScanChain]
    | cons link rest =>
      rcases link with ⟨x, lc⟩
      rw [hl] at hc
      obtain ⟨depth, hs, hb, hrest⟩ := hc
      cases depth with
      | zero => exact hs.elim
      | succ depth =>
        obtain ⟨n, hn, hbounds, hchildren⟩ := hs
        rw [nextGo_step p v t req fuel ch x lc rest hl n hn]
        cases hf : scanChoice n t req ch.first ch.eqMatch lc with
        | none => exact ih (scanPop p v ch rest) hrest
        | some fd =>
          have hmem := scanChoice_mem n t req ch.first ch.eqMatch lc fd hf
          simp only
          by_cases hpast : scanPast req ch fd = true
          · simp only [hpast]; trivial
          · simp only [hpast]
            cases hy : v fd.y with
            | none => trivial
            | some ny =>
              simp only
              cases hd : ny.isData with
              | true =>
                simp only [↓reduceIte]
                cases hv : valueOf v fd.y with
                | none => trivial
                | some value => exact ⟨depth+1, ⟨n, hn, hbounds, hchildren⟩, hb, hrest⟩
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte]
                have hc := (hchildren (fd.c, fd.y) hmem ny hy hd).1
                apply ih (scanPush req ch n x rest fd)
                refine ⟨depth, hc, ?_, depth+1, ⟨n, hn, hbounds, hchildren⟩, hb, hrest⟩
                simp only [List.length_cons]
                omega

/-- Starting at a child's sentinel, a nonempty sound subtree needs at most
its depth visits. It cannot exhaust one subtree and enter a sibling. -/
theorem nextGo_descent_stable (p : Params) (v : View BVal) (t : Time) (req : ScanReq)
    (depth x : Nat) (hs : ScanTree p v t depth x)
    (hne : ∃ n, knodeOf p v x = some n ∧ n.liveAt t ≠ [])
    (ch : Chain) (rest : List (NodeId × Int))
    (hl : ch.links = (x, if req.forward then cvLo else cvHi) :: rest)
    (hfirst : ch.first = false) (f g : Nat) (hf : depth ≤ f) (hg : depth ≤ g) :
    nextGo p v t req g ch = nextGo p v t req f ch := by
  induction depth generalizing x ch rest f g with
  | zero => exact hs.elim
  | succ depth ih =>
    obtain ⟨n, hn, hbounds, hchildren⟩ := hs
    obtain ⟨other, ho, hne⟩ := hne
    have he : other = n := Option.some.inj (ho.symm.trans hn)
    subst other
    cases f with
    | zero => omega
    | succ f =>
      cases g with
      | zero => omega
      | succ g =>
        rw [nextGo_step p v t req g ch x _ rest hl n hn,
          nextGo_step p v t req f ch x _ rest hl n hn]
        cases hchoice : scanChoice n t req ch.first ch.eqMatch
            (if req.forward then cvLo else cvHi) with
        | none =>
          exact (scanChoice_sentinel n t req ch.eqMatch hne hbounds
            (by simpa only [hfirst] using hchoice)).elim
        | some fd =>
          have hmem := scanChoice_mem n t req ch.first ch.eqMatch _ fd hchoice
          simp only
          by_cases hpast : scanPast req ch fd = true
          · simp only [hpast, ↓reduceIte]
          · simp only [hpast]
            cases hy : v fd.y with
            | none => rfl
            | some ny =>
              simp only
              cases hd : ny.isData with
              | true => rfl
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte]
                obtain ⟨hc, hnonempty⟩ := hchildren (fd.c, fd.y) hmem ny hy hd
                exact ih fd.y hc hnonempty (scanPush req ch n x rest fd)
                  ((x, (fd.c : Int)) :: rest) rfl rfl f g (by omega) (by omega)

/-- A sound chain first climbs at most its length, then descends at most
`bound` key nodes. Any two fuels above this sum give exactly the same result,
including the complete returned chain and touch list. -/
theorem nextGo_stable (p : Params) (v : View BVal) (t : Time) (req : ScanReq)
    (bound : Nat) (ch : Chain) (hc : ScanChain p v t bound ch.links)
    (f g : Nat) (hf : bound + ch.links.length + 1 ≤ f)
    (hg : bound + ch.links.length + 1 ≤ g) :
    nextGo p v t req g ch = nextGo p v t req f ch := by
  generalize he : ch.links = links at *
  induction links generalizing ch f g with
  | nil =>
    cases f with
    | zero => simp only [List.length_nil] at hf; omega
    | succ f =>
      cases g with
      | zero => simp only [List.length_nil] at hg; omega
      | succ g => simp only [nextGo, he]
  | cons link rest ih =>
    rcases link with ⟨x, lc⟩
    obtain ⟨depth, hs, hb, hrest⟩ := hc
    cases depth with
    | zero => exact hs.elim
    | succ depth =>
      obtain ⟨n, hn, hbounds, hchildren⟩ := hs
      cases f with
      | zero => omega
      | succ f =>
        cases g with
        | zero => omega
        | succ g =>
          rw [nextGo_step p v t req g ch x lc rest he n hn,
            nextGo_step p v t req f ch x lc rest he n hn]
          cases hchoice : scanChoice n t req ch.first ch.eqMatch lc with
          | none =>
            exact ih (scanPop p v ch rest) f g rfl hrest
              (by simp only [List.length_cons] at hf; omega)
              (by simp only [List.length_cons] at hg; omega)
          | some fd =>
            have hmem := scanChoice_mem n t req ch.first ch.eqMatch lc fd hchoice
            simp only
            by_cases hpast : scanPast req ch fd = true
            · simp only [hpast, ↓reduceIte]
            · simp only [hpast]
              cases hy : v fd.y with
              | none => rfl
              | some ny =>
                simp only
                cases hd : ny.isData with
                | true => rfl
                | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  obtain ⟨hc, hnonempty⟩ := hchildren (fd.c, fd.y) hmem ny hy hd
                  apply nextGo_descent_stable p v t req depth fd.y hc hnonempty
                    (scanPush req ch n x rest fd) ((x, (fd.c : Int)) :: rest) rfl rfl f g
                  · simp only [List.length_cons] at hf; omega
                  · simp only [List.length_cons] at hg; omega

/-- The fuel used by the reader is adequate on every structurally sound
chain; extra fuel changes no observable result or internal chain field. -/
theorem nextGo_parameter_fuel (p : Params) (v : View BVal) (t : Time) (req : ScanReq)
    (ch : Chain) (hc : ScanChain p v t p.fuel ch.links)
    (extra : Nat) :
    nextGo p v t req (2 * p.fuel + 2 + extra) ch =
      nextGo p v t req (2 * p.fuel + 2) ch := by
  have hl := scanChain_length p v t p.fuel ch.links hc
  exact nextGo_stable p v t req p.fuel ch hc _ _ (by omega) (by omega)

end SIS.Tree
