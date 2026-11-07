# 006-14 Day work, 7 November 2026

Created 2026-11-07 by Frans Lundberg. Status: open. The plan for the
coordinator's day of 2026-11-07 (coord-1107), a Saturday: the work on
release 2026.4 (020), the progress and the outcome. The way of working is
013-02's (the coordinator).


## 1. The request

Frans, 2026-11-07, 08:18: "You are today's coordinator, called coord-1107.
We will work on 2026.4 features today including DbObject. It is Saturday,
so I will only attend to the work ad hoc. And often remotely from my
phone."

Frans, 08:22: "Use up to 95% in this session. I will likely update my
subscription today or tomorrow." (Of the week's usage.)

Frans, 08:32, on 020-01, section 14, decision 2 (the shape of objects and
indexes): "I will look at it later." On 021-04: "Lone surrogates. This is
important. Study this further with a subagent at XHigh effort. Check how
this works in other languages including Rust, Python, JavaScript,
WebAssembly, C. Add to the document, make no code changes. Note that
BergDB is design for multi-langage support. So, decisions like this are
not specific to Java only."


## 2. Ground rules

* Effort: the session high while the usage level is `tight` (013-02);
  agents high, and xhigh where Frans says so (021-04's study).
* Agents at a time: at most 2 while the level is `tight`.
* Usage: up to 95% of the week (Frans, 08:22).
* Commits to `main` by the coordinator, by path, in Frans's name, with no
  AI attribution; Java changes after `BEFORE COMMIT OK`. The gate's lock:
  `/Users/f/fl/bench/006-14/gate.lock`.


## 3. The work

1. 021-04, the study of lone surrogates across languages (Rust, Python,
   JavaScript, WebAssembly, C and others) and what it means for BergDB's
   format, which other languages will read and write. Text in 021-04 only,
   no code. Agent at xhigh (Frans, 08:32).
2. 021-01 to 021-03, the morning list's fixes (Kind: Fix, Frans: none).
   Agent at high.
3. Waiting for Frans: 020-01, section 14, decision 2 (shape 1
   recommended), then decisions 3 to 8, the contract for objects (F1) and
   H1.
4. After 2026.4's work, if there is room: 019-45 and 016-02's open item 2.


## 4. If the coordinator stops

The state is in `/Users/f/fl/bench/coord/2026-11-07/state.md`; a new
session continues with `/coordinator resume` (013-02).


## 5. Progress

* 08:19. coord-1107 started; handover from coord-1106 (nothing running,
  main = origin/main 1ff6be4).
* 08:24 to 08:25. VS Code restarted; resumed.
* 08:34. Agents started: s04 on 021-04's study (xhigh), f13 on 021-01 to
  021-03 (high).
* 08:57. f13 done, BEFORE COMMIT OK (120 s): 021-01 closed (1132b1d);
  021-02 closed and 021-03 done but for a night run (aced82e).
* 08:58. java/night.sh started on aced82e, to close 021-03.
* 09:06. s04 done: 021-04's study across languages and formats, six
  options, recommendation (1), refuse everywhere (well-formed UTF-8 for
  every string), for Frans to decide.
* 09:33. Frans on 021-04: "021-04, good study. Yes, option 1, absolutely.
  Document this, ensure it is clear in the Javadoc API comments." 09:33
  agent u04 (high) makes it, and registers 021-05 (the Core's String puts)
  and 021-06 (the read side).
* 09:51. java/night.sh on aced82e: NIGHT OK (53 minutes); 021-03 closed
  (173f1c0).
* 09:52. Frans on 020-01, section 14, decision 2: "Shape 1, absolutely.
  Go slow here. I want to work out the details with you. I read
  DbObject.java yesterday. I really like the concept. Read the comments of
  it. At the very end too. The design is a limited supported set of types
  that most (approximately "all") languages will support. It is meant like
  a data storage format for objects in OO languages. Where the objects are
  crafted for this purpose, for storage. We do not support serialization
  of all types of Java objects. A real application will need to deal with
  long-term stored db objects including type evolution. We need to discuss
  thowing exceptions vs doing best-effort conversions." The details are
  worked out with Frans in the chat, one question at a time.
* 09:55. u04 done, BEFORE COMMIT OK (121 s), JAVADOC PUB OK: 021-04 and
  021-05 closed, 021-06 registered (the read side; waits for F1's spec).
* 10:04. 020-02 created: the objects' design with Frans; question 1 (a
  conversion on a get: exact or throw) for Frans to read.
* 12:15. Frans: "020-02. I would like to extend this by one more question:
  should null be supported? [...] For binson (binson.org), I chose to not
  support null values. Please analyse this in a new XHigh subagent."
  12:16 agent n02 (xhigh): question 1b in 020-02, the study in 020-03.
* 12:31. Frans, thinking out loud on question 1: best effort with feedback
  on how the conversion went, a ConversionResult, keeping the DbObject.
  The coordinator's answer: the database promises the exact DbObject; the
  conversion to a Java object is the binding's own step, with a report.
* 12:40. n02 done: question 1b in 020-02 (section 2b), the study in
  020-03; recommendation (d), no stored null: a null field is absent, and
  a put is refused where the null would not read back.
* 14:26. Frans: "About the Conversion design. Write it down. It sounds
  pretty good. No decision yet." Written as 020-02, section 2.5, option
  (D), with seven questions for the detailed design.


## 6. Outcome

Not yet.
