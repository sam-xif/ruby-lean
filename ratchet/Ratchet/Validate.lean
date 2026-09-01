import Ratchet.Cert

/-!
The trusted checker: `validate : Cert → Expr → Bool`, over the **real** `Expr`.

**Stub.** This always returns `false` — no checking logic lives here right now. The
corpus (`corpus/*.json`, real desugared Ruby + a certificate + a recorded
`expect_validate`) is the target ladder to climb back up; `Ratchet/Cert.lean`'s
`Cert.lookup` (subterm-keyed claims, matched by `Expr`'s `BEq`) is the mechanism to
climb it with. See `AGENTS.md` for the design this is meant to grow back into and why
it was cleared.
-/

namespace Ratchet

def validate (_c : Cert) (_p : Expr) : Bool := false

end Ratchet
