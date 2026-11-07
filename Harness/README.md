# Lean validation harness

`Harness.Main` is the package's Lake test driver. `scripts/check` only selects the
repository directory and invokes `scripts/lake test`; all validation logic is Lean.

```sh
scripts/check                         # Complete non-network gate
scripts/check --all                   # Gate, harness self-tests, and 65 HTTP checks
scripts/check --http-certified        # 30 tenant-route checks
scripts/check --http-legacy           # 35 legacy regressions
scripts/check --self-test             # Audit/parser and process-lifecycle regressions
scripts/check --generate --check      # All generator checks
scripts/check --generate              # Explicitly regenerate the checked-in artifact
scripts/check --benchmark batch       # Four native Machine-call measurements
scripts/check --benchmark s2          # Fresh schema evidence: small, mixed, 300 objects
scripts/check --benchmark s2b         # Recursive argument-layout evidence, two sizes/modes/repeats
scripts/check --benchmark prototype   # Explicit schema, real codegen, resolver/artifact reuse
```

The three schema/codegen benchmarks accept `--smoke` for smaller workloads. Logs and
new benchmark reports are written under `.lake/benchmarks`; the historical measurements
in `planning/` are preserved. Timing uses a monotonic clock, and RSS is measured by
`/usr/bin/time` (`-l` on macOS, `-v` on Linux). These are measurements, not performance
proofs. RSS accounting may require permission outside a restrictive sandbox.
On Linux, the optional RSS benchmarks require GNU `time` at `/usr/bin/time`.

## Coverage

- `Check`: builds the project, executes the Lean semantic tests, compiles generated-name
  and SDL fixtures, audits all selected tenant/plan theorems, scans escape hatches,
  and checks the expected diagnostics of all 48 rejection fixtures.
- `Audit`: masks comments and quoted literals, rejects unsupported declaration styles,
  discovers every public theorem in the restricted audited style, and requires an
  exact report inventory. Unknown dependencies, missing/duplicate reports, and malformed
  or incomplete multiline reports fail the run. Only `propext`, `Classical.choice`,
  and `Quot.sound` are allowed. This remains a source/dependency audit, not a proof
  of the compiler or a complete implementation-substitution audit.
- `Generator`: checks byte-for-byte regeneration, rejects a coordinated dispatch/metadata
  mutation specifically at the independent agreement theorem, checks a positive
  counterexample to that mutated adapter, and compiles the reordered/multiargument fixture.
- `HttpTests`: preserves both former HTTP suites, including concurrent nested-fragment
  traffic, incomplete-body disconnect recovery, tenant isolation, and exception redaction.

## Process and network boundaries

The harness targets POSIX development hosts. It uses Lean's process API, its standard
TCP sockets, and `/bin/kill` for forced cleanup. Process output is drained concurrently,
children run in owned process groups, and deadlines terminate/reap only those groups.
Compiler fixtures have a 60-second limit, aggregate proof audits 180 seconds, and the
full build 600 seconds. HTTP client processes have a 10-second limit and a 2 MiB response
bound. Servers are always cleaned up, including on assertion failure.

For cold builds or slower CI hosts, set a positive integer timeout multiplier, for
example `LEAN_GRAPHQL_TIMEOUT_SCALE=4 scripts/check --all`. It scales subprocess
deadlines; deliberate short timeout self-tests, server readiness, and latency assertions
keep their fixed bounds. Build output is buffered until completion, with a progress
message before the build starts. The default multiplier is 1; invalid values fail.

The test client independently handles HTTP content-length/chunk framing; it does not
use the server's HTTP parser or GraphQL executor. JSON assertions use Lean.Json, so
JSON parsing is shared with the server and is not an independent JSON-decoder oracle.
The limited client rejects unsupported framing; it is not a general HTTP library.
Loopback socket permission is required for the HTTP suites.

The harness is ordinary executable Lean code, not part of the proved application core.
Its self-tests cover discovery failures, multiline report handling, missing/duplicate
reports, forbidden dependencies, malformed HTTP framing, process output, and deadlines.
Lean's kernel still checks the application proofs; tests still check concrete native
behavior. Rewriting the harness does not change that distinction.
