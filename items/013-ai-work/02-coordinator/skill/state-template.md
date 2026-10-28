# Coordinator state, YYYY-MM-DD

The coordinator's state, which changes by the minute (bergdb 013-02,
section 7). The record is the day's plan. Times from `date`.

* Mode: attended
  (attended | unattended until YYYY-MM-DD HH:MM | closing | closed)
* Session: coord-MMDD, ID <session ID>, process ID <pid>
* Plan: none yet (the quarter's subitem, such as 006-11)
* Previous coordinator: <name>, <its STATE_DIR>, <its mode>
* Next coordinator: none yet
* Check-ins: <job ID, cron, next run>
* Watchdog: none (<pid>, until YYYY-MM-DD HH:MM)
* Effort: xhigh (xhigh attended, max unattended; section "Effort")
* Usage: <the last line of usage.sh, with its time> (Frans's word, if he
  gave one: "tight since HH:MM")
* Agents at a time: at most N, as Frans allows
* Quiet block: none (HH:MM to HH:MM, 013-01)


## Agents

| Name or ID | Task and item | Clone | Effort | Output file | Started | Status |
|---|---|---|---|---|---|---|


## Background commands

| PID or task ID | What | Output | Started | Status |
|---|---|---|---|---|


## Waiting for Frans

None.


## Events

* HH:MM Started.
