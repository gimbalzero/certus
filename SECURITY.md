# Security policy

Certus is a proof checker, so **a soundness bug is a security bug**: if Certus accepts a false theorem, that is the most serious kind of issue this project can have.

## What counts
- Certus accepts an export containing a proof that Lean's kernel, or another independent checker, rejects.
- `certus deps` misses an axiom, a `sorry`, or an unsafe or partial declaration in a closure.
- Two different exports produce the same content hash (a hash collision, or an encoding ambiguity in the spec).
- The reader accepts a malformed export instead of rejecting it.
- Memory-safety problems or crashes on hostile input.

## How to report
Please report privately through GitHub: **Security → Report a vulnerability** on this repository. Include a minimal export file, or the Lean source that produces it, and the command you ran.

## What to expect
- Acknowledgement within **3 days**.
- An assessment within **14 days**.
- A fix, a release, and a public advisory crediting you (unless you'd rather not be named) within **90 days**, or sooner once a fix ships.

Everything in this policy applies to the latest release on `main`. The project is pre-1.0, and Phase 0 contains no type checker yet.
