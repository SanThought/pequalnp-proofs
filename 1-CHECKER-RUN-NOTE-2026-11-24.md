# Official checker run on a closed row, 2026-11-24 (pipeline test only)

Not a proof submission. Row L-meta-5449 was already merged upstream by another contributor; nothing was submitted from this run.

- Command: `node tools/check-lean.mjs <file> <statement> check` on a 2 GB, 2-CPU box, no swap tuning.
- File imported only narrow Mathlib modules (Data.Fintype.Basic, Tactic.Linarith, Tactic.FinCases) plus PEqualNP.Defs.
- Build of the file and Defs root: finished at t=149 s. (A full `import Mathlib` version had not finished building after 15+ minutes on the same box. One data point.)
- Verifier stage (checklemma): CheckLemma.lean reads every statement against the whole of Mathlib, so the narrow imports do not narrow this stage. It mapped about 3700 oleans, 630 MB resident, with about 10% CPU, ~240 MB/s disk reads and 45% I/O wait (page-cache thrash).
- Result: `CHECKER FAULT: the verifier could not run: spawnSync .../tools/bin/lake ETIMEDOUT`, exit 3, at 30:00 of process time. This says nothing about the proof. Total clock time from start was about 65 min because the sandbox pauses between active calls.
- Earlier, a different row (L-meta-4534) ended the same way (exit 3 ETIMEDOUT) at the verifier stage.
- Conclusion limited to this box and run: the official verifier does not finish inside the checker's 30 min step limit here. It does not show the verifier can never run on other hardware.
