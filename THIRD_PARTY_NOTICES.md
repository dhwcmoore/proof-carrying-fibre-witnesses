# Third-Party Notices

**Anticipated dependencies. No implementation lockfile exists yet** — Phase 0
authorises no code. The table below is the *planned* dependency set for the v0
implementation, recorded so the licence obligations are known in advance. It must
be regenerated from the actual lockfile, with upstream `LICENSE` / `NOTICE` text,
when a distributable artifact is first built (Phase 2+).

**None of this software is redistributed inside this repository** — there are no
vendored copies. Each dependency remains under its own licence; this file does not
relicense any of it.

| Component (planned) | Role | Licence |
|---|---|---|
| The Coq / Rocq Prover and its standard library (incl. the extraction realisation files `ExtrOcamlBasic`, `ExtrOcamlZBigInt`, `ExtrOcamlNatBigInt`) | Proof checking; extraction of the semantic kernel | LGPL-2.1-only |
| `zarith` | Arbitrary-precision integer arithmetic in the extracted OCaml kernel and the verifier | LGPL-2.0-only WITH OCaml-LGPL-linking-exception |
| `yojson` | JSON parsing in the verifier's non-kernel wire layer | BSD-3-Clause |
| `sha` | SHA-256 for digest binding in the verifier's non-kernel layer | ISC |

## Notes

- The OCaml LGPL linking exception (`zarith`) permits distribution of a compiled
  binary that statically links `zarith` under this project's Apache-2.0 terms,
  provided `zarith`'s own licence and notices travel with such a distribution.
- The Coq/Rocq standard library and its extraction realisation files are part of
  the extraction trusted computing base (`TRUST_BOUNDARY.md` §F.1.1); they are
  used at build time and their extracted realisations appear in the generated
  OCaml. Their LGPL-2.1 terms apply to those components, not to this project's
  own source.
- When a distributable artifact is produced (Phase 2+), this file must be
  regenerated from the actual dependency set and versions with their upstream
  `LICENSE` / `NOTICE` text included.
