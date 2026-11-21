# Security policy

rulean is a proof checker. Its main job is to reject false proofs, so a wrong accept is a security fault.

## What to report privately

- rulean accepts an export that contains a proof of a false statement.
- rulean accepts an export that the official Lean kernel rejects.
- An input makes rulean read or write a file other than its input and its report, or run code.

Use the private form at https://github.com/tamnd/rulean/security/advisories/new. Do not open a public issue for these.

## What to report in public

- A crash, a hang or a memory problem on an input. Open an issue with the input.
- rulean rejects or declines an export that the official kernel accepts. Use the "Verdict difference" form.

## What we do

- We reply to a private report in 3 days.
- We give a fix or a public advisory in 14 days for a soundness bug.
- Each soundness bug gets a CVE request, a regression test, a postmortem in the repository and a line in `SOUNDNESS.md`.
- On the day of the fix, we tell the Lean Zulip and the maintainers of the Lean Kernel Arena.

## Supported versions

Before 1.0, only the latest release gets fixes.
