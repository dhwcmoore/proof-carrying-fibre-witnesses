# Current Phase-1 nonclaims

PCFW verifies claim conditions relative to a formally specified learned
observation regime; it does not thereby verify the learned system in its entirety.
Phase 1 is **CLOSED**, with a **PARAMETRIC** release boundary. This implementation
companion supplements [NON_CLAIMS.md](NON_CLAIMS.md); current release scope is
[RELEASE_CRITERIA.md](RELEASE_CRITERIA.md).

Phase 1 does not prove:

- correctness of an arbitrary policy implementation;
- correspondence of arbitrary policy bytes to functional `Policy` or `AuditContext`;
- correctness of the learned model as a whole, its learning procedure or training data;
- correctness or truth of arbitrary external observations;
- claims beyond the formally specified learned observation regime;
- transcript faithfulness from repeatability, parsing, hashing or replay;
- discharge of theorem premises from kernel closure;
- SHA-256 injectivity, or collision resistance from digest determinism;
- semantic policy identity from manifest hash agreement;
- general executable correspondence from extraction or agreement on finite tests;
- correspondence for the retained historical native-integer demo;
- Rocq-domain validity of arbitrary raw OCaml bigint inputs;
- capture/replay correspondence, general parser/loader correctness or full Unicode conformance;
- byte-identical reproducible binaries, production-system security or certification;
- Phase-2 properties or completion of Phase 1 from a passing release gate.

`policy_binding` is supplied local equality of opaque orchestration tokens. It
neither checks a functional policy implementation nor establishes the external
policy/semantic-context association. Policy realisation and transcript
faithfulness are separate premises. Tests of literal canonical policy bytes do
not establish policy interpretation. A concrete semantic loader, closed target
registry, `SyntheticTargetV0`, `rounddiv`, positive-width concrete quantisation
and a no-clamping concrete quantiser are outside the Phase-1 release scope.

Version 0's `EXACT` branch remains unreachable. Finding no witness does not prove
fibre constancy. All mathematical and executable conclusions retain their policy,
domain, observation-binding and validation premises. The bigint structural gate,
finite differential cases and bounded ASCII byte integration strengthen evidence
within their tested boundaries; they do not supply a general correspondence
theorem, transcript/context identity from event-array bytes or F.3 faithfulness.
See [TRUST.md](TRUST.md).
