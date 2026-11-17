# 013-03 AI models: intelligence, time and cost

Created 2026-10-30, rewritten 2026-11-17.

A comparison of AI models by their Artificial Analysis (AA) figures:
intelligence, estimated time per task and API-equivalent cost per task.
Its purpose was to choose models for the work on BergDB.

## Use in this project

The choices made from this comparison (2026-10-30, revised 2026-11-10):

- **Claude Opus 5.5 xHigh** (57): the default, for interactive work, for
  the coordinator (013-02) and for subagents.
- **Claude Opus 5.5 Max** (59): seldom; planning, Lean proofs and hard
  programming such as concurrency.
- **Claude Opus 5.5 Medium** (48): short factual questions.
- **Claude Fable 5.2** (released 2026-11-10): Medium (56) is about as
  smart as Opus 5.5 xHigh and faster; High (62) can replace Opus 5.5 Max;
  Max (65), the highest score in the table, is slow and costly, for
  verification and second opinions rather than coding.
- **GPT-6.1 Sol Max** (55): second opinions.
- Sonnet and Haiku are not needed. Changing the effort of one model keeps
  its context, which makes effort the easiest thing to change.

Which models the sessions use now is in 013-02, section 9.

## 1. Scope and snapshot

AA Intelligence Index **v5.0.1**, retrieved on **2026-11-10**, at about
**12:55 Europe/Stockholm**. This replaces the first snapshot (v5.0,
2026-10-30). Scores are AA's displayed whole
numbers.
The work needs models scoring at least 50 and often 55 or more; scores of
**55+ are bold**. The configurations below 50 are kept
because they were explicitly discussed, including Opus Medium, Sonnet High
and the best-scoring Haiku configuration.

For Fable, Opus and Sonnet, AA labels the configurations **Default
Fallback**. Haiku is listed without that label. These are AA's tested configurations;
the table does not establish identical settings, behavior or performance
in every subscription interface.

This is a historical snapshot, not a continuously maintained leaderboard.
Each row uses one model page, identified in section 5. AA's timing
figures can change and related pages can show different snapshots of the
same model. Between the two snapshots every task time grew, by 12% to
119%, while the costs stayed the same and four scores rose by one point
(Astra Medium, Opus Max, Sonnet High, Sonnet Max). The first snapshot
read AA's comparison pages and this one its model pages, so part of the
growth in task time may be a difference between the pages and not a
change in the models; this was not checked.

## 2. Comparison

Task time is rounded to one decimal minute. Dollar figures are
API-equivalent benchmark costs, not subscription charges.

| Model | Effort | Intelligence | AA estimated time/task (min) | API-equivalent cost/task (USD) | Source |
|---|---|---:|---:|---:|---|
| GPT-6.1 Sol       | High   |     50 |  6.5 |  $0.59 | S1  |
| GPT-6.1 Sol       | xHigh  |     52 |  9.3 |  $0.76 | S2  |
| GPT-6.1 Sol       | Max    | **55** | 20.0 |  $1.27 | S3  |
| GPT-6 Astra       | Medium |     52 |  6.9 |  $2.73 | S4  |
| GPT-6 Astra       | High   | **55** |  9.8 |  $3.24 | S5  |
| GPT-6 Astra       | xHigh  | **55** | 11.3 |  $3.66 | S6  |
| GPT-6 Astra       | Max    | **57** | 23.6 |  $6.24 | S7  |
| Claude Fable 5.2  | Medium | **56** |  8.3 |  $3.80 | S8  |
| Claude Fable 5.2  | High   | **62** | 17.4 |  $9.08 | S9  |
| Claude Fable 5.2  | xHigh  | **62** | 26.3 | $14.83 | S10 |
| Claude Fable 5.2  | Max    | **65** | 44.6 | $26.54 | S11 |
| Claude Opus 5.5   | Medium |     48 |  7.1 |  $2.45 | S12 |
| Claude Opus 5.5   | High   |     52 |  9.5 |  $3.46 | S13 |
| Claude Opus 5.5   | xHigh  | **57** | 16.2 |  $6.05 | S14 |
| Claude Opus 5.5   | Max    | **59** | 25.1 | $10.04 | S15 |
| Claude Sonnet 5.5 | High   |     42 |  7.0 |  $1.64 | S16 |
| Claude Sonnet 5.5 | xHigh  |     50 | 15.0 |  $4.09 | S17 |
| Claude Sonnet 5.5 | Max    | **55** | 31.4 | $10.02 | S18 |
| Claude Haiku 5.5  | Max    |     36 | 14.8 |  $0.41 | S19 |

## 3. What the columns measure

- **Intelligence:** AA's composite Intelligence Index v5.0.1 score. It is
  neither a percentage of tasks solved nor a guarantee on a particular
  task. A score rounded to 55 does not establish equivalence between two
  models.
- **AA estimated time/task:** AA's weighted average decode-time estimate
  for Intelligence Index tasks, calculated from output-token usage and
  output speed. It excludes time to first token and overhead. It is not a
  measured wall-clock time to a verified solution.
- **API-equivalent cost/task:** AA's weighted average model cost per
  Intelligence Index task, using the applicable input, cache and output
  token prices. These are costs per benchmark attempt, not costs until a
  correct solution has been reached.

The definitions above come from AA's metric notes on its comparison
pages, read for the first snapshot. The model pages label the two figures
"Time per Intelligence Index task" and "Cost per Intelligence Index
task"; that they are defined the same way was not checked.

Time/task is the table's one speed measure; in use it works well as a
unit. The table had two more timing columns until 2026-11-10,
AA's time to first token and its end-to-end time for a 500-token answer;
they were removed then.

Tokens per second is deliberately omitted. It helps explain generation
speed, but models use different amounts of reasoning and answer text.
The timing that matters for the work is the elapsed time until an
acceptable, verified solution, including tool calls, tests, corrections and retries.
None of these AA columns directly measures that entire workflow.

## 4. How to use the comparison

For a 55+ shortlist, the table contains Sol Max, Astra High, Astra xHigh,
Astra Max, all four Fable 5.2 rows, Opus xHigh, Opus Max and Sonnet Max.
Sonnet xHigh reaches 50, and Haiku's highest score is 36. Those lower scores do not
prevent useful performance on an easier, bounded task.

In unmeasured use, Opus xHigh felt much faster than Sol Max. AA's
estimates of the end-to-end time for a 500-token answer, 133.13 seconds
versus 283.49 seconds (first snapshot; no longer a column of the table),
are consistent with that impression on AA's response workload. They do
not prove that speed ratio for complete BergDB tasks.

API-equivalent cost does not convert at a fixed rate to a subscription's
allowance, so the cost column cannot rank the cost per task under a
subscription. Within a subscription's included allowance, another task
adds no charge but consumes allowance. The useful comparison is quality,
elapsed time to an accepted solution, allowance consumed per solution and
useful work completed per month; establish any allowance advantage from
actual usage rather than from API prices alone.

## 5. Sources

All sources are Artificial Analysis model pages, retrieved on 2026-11-10.
Each row's source is the page used for all its values; a model's page
without an effort in its address is its Max configuration. Older launch
articles can use an earlier Intelligence Index; their scores are not mixed
into this v5.0.1 table.

| Source | AA model page |
|---|---|
| S1  | [GPT-6.1 Sol High](https://artificialanalysis.ai/models/gpt-6-1-sol-high) |
| S2  | [GPT-6.1 Sol xHigh](https://artificialanalysis.ai/models/gpt-6-1-sol-xhigh) |
| S3  | [GPT-6.1 Sol Max](https://artificialanalysis.ai/models/gpt-6-1-sol) |
| S4  | [GPT-6 Astra Medium](https://artificialanalysis.ai/models/gpt-6-astra-medium) |
| S5  | [GPT-6 Astra High](https://artificialanalysis.ai/models/gpt-6-astra-high) |
| S6  | [GPT-6 Astra xHigh](https://artificialanalysis.ai/models/gpt-6-astra-xhigh) |
| S7  | [GPT-6 Astra Max](https://artificialanalysis.ai/models/gpt-6-astra) |
| S8  | [Claude Fable 5.2 Medium](https://artificialanalysis.ai/models/claude-fable-5-2-medium) |
| S9  | [Claude Fable 5.2 High](https://artificialanalysis.ai/models/claude-fable-5-2-high) |
| S10 | [Claude Fable 5.2 xHigh](https://artificialanalysis.ai/models/claude-fable-5-2-xhigh) |
| S11 | [Claude Fable 5.2 Max](https://artificialanalysis.ai/models/claude-fable-5-2) |
| S12 | [Claude Opus 5.5 Medium](https://artificialanalysis.ai/models/claude-opus-5-5-medium) |
| S13 | [Claude Opus 5.5 High](https://artificialanalysis.ai/models/claude-opus-5-5-high) |
| S14 | [Claude Opus 5.5 xHigh](https://artificialanalysis.ai/models/claude-opus-5-5-xhigh) |
| S15 | [Claude Opus 5.5 Max](https://artificialanalysis.ai/models/claude-opus-5-5) |
| S16 | [Claude Sonnet 5.5 High](https://artificialanalysis.ai/models/claude-sonnet-5-5-high) |
| S17 | [Claude Sonnet 5.5 xHigh](https://artificialanalysis.ai/models/claude-sonnet-5-5-xhigh) |
| S18 | [Claude Sonnet 5.5 Max](https://artificialanalysis.ai/models/claude-sonnet-5-5) |
| S19 | [Claude Haiku 5.5 Max](https://artificialanalysis.ai/models/claude-haiku-5-5) |
