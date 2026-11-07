# lean-graphql

```text
        o
       / \
      v   v       lean-graphql
      o   o       schemas -> graphs -> proofs
       \ /
        v
        o
```

**Proof-oriented GraphQL framework in Lean 4**

> [!NOTE]
> **An autonomous AI development experiment.** AI agents carry out implementation,
> proof development, testing, documentation, and cross-agent review under human-defined
> goals and scope. The experiment is whether that workflow can produce useful,
> independently checkable software guarantees. Evidence comes from Lean's kernel,
> explicit specifications, and reproducible tests—not an agent's confidence.

Define application rules as resolver contracts, compile queries into typed execution
graphs, and carry correctness evidence through execution, optimization, and response
encoding. The aim is to prove application properties once and preserve them as
accepted queries execute.

## A concrete guarantee

The reference application models tenants, projects, and tasks. Its authorization
judgment requires returned records to belong to the requesting tenant and to the
specified snapshot, including nested relationships. Missing or cross-tenant links,
duplicate IDs, and filtered list positions are covered. Separate fault-contract proofs
cover permitted resolver faults.

For the supported query profile, the certified path carries this evidence through
to the response bytes supplied to LeanIO. Authentication, snapshot acquisition, and
backend answers must satisfy explicit contracts for the same principal and snapshot.

Here is one link in that chain: the theorem for the deterministic in-memory runtime.
It applies to any checked nonempty selection and snapshot with the stated adapter
agreement:

```lean
import Example.Tenant.Execution
open GraphQL.Plan Example.Tenant

example (adapter : ExecutionBridge.ActualAdapter)
    (agreement : BindingAgreement Binding.independentBindings adapter)
    (request : Binding.Request) (query : IR.Checked .query selection)
    (nonempty : selection ≠ .nil) :
    Spec.AuthorizedResponse request.snapshot request.principal selection
      (Runtime.run adapter request query) :=
  Runtime.run_authorized adapter agreement request query nonempty
```

This composes existing proofs; the resolver contracts and independent authorization
semantics are developed in [the reference application](Example/Tenant/). The
[handler guarantee, `GoodReply`](Example/Tenant/CertifiedHandler.lean) composes the
optimized effectful path with authentication, acquisition, and encoding evidence.

## Run the example

The [tenant schema](Example/Tenant/Schema.lean) includes:

```graphql
type Query {
  project(id: ID!): Project
  projects: [Project!]!
}
type Project {
  id: ID!
  title: String!
  tasks: [Task!]!
}
type Task {
  id: ID!
  title: String!
  project: Project!
}
```

Build and start the certified in-memory server:

```sh
scripts/lake build
.lake/build/bin/graphql-certified 8081
```

In another terminal:

```sh
curl http://127.0.0.1:8081/graphql \
  -H 'Content-Type: application/json' \
  -H 'Authorization: Bearer tenant-1' \
  -d '{"query":"{ projects { title } }"}'
```

```json
{"data":{"projects":[{"title":"left"},{"title":"right"},{"title":"first"},{"title":"second"}]}}
```

The fixture also contains another tenant's records. Switching to `Bearer tenant-2`
returns that tenant's project instead. These fixed tokens are a demonstration policy,
not production authentication. The server binds to loopback only.

Lean 4.33.0 is pinned in `lean-toolchain`; LeanIO is pinned in `lake-manifest.json`.
`scripts/lake` uses the project-local toolchain when available, otherwise an installed
`lake` command.

## How the proof travels

```text
schema + application model + resolver contracts
                      |
                checked query
                      |
             typed execution graph
                      |
         certified optimized execution
                      |
          authorized structured response
                      |
              certified JSON bytes
```

The execution graph describes computation; a separate output plan reconstructs the
response. Typed references constrain dependencies and result types. The certified
driver requires each backend answer to carry its field postcondition, then composes
those certificates into the result guarantee.

The wire step preserves an already-established application guarantee:

```lean
import Example.Tenant.WireResponse
open Example.Tenant

example (response : {r // Spec.AuthorizedResponse snapshot principal selection r}) :
    {bytes // Wire.AuthorizedWireResponse snapshot principal selection bytes} :=
  Wire.encodeAuthorized response
```

The encoder is total and proved against independent ordered JSON and response-envelope
relations. Proofs cover escaping, integer encoding, error paths, root-null bubbling,
and UTF-8 preservation. The HTTP adapter sends these certified bytes or a closed public
failure; it does not run a separate raw resolver path.

## Verified optimization

For the recognized `projects → tasks → project` query shape with a keyed capability,
the batching transformation groups repeated `Task.project` lookups and reconstructs
their original positions. Other query shapes use the reference execution path. Under the deterministic backend meanings, a
general theorem proves complete response equality with reference execution.
For the concrete demonstration workload:

```lean
import Example.Tenant.S4bProofs
open GraphQL.Plan Example.Tenant
open Example.Tenant.S4bProofs

example : runMachine (Batch.driver adapter)
    (Batching.execute adapter request selected 2 (by decide)) =
    Runtime.run adapter request selected := whole_response
```

The batch wave makes `ceil(unique keys / batch capacity)` primitive calls. The whole
example makes **9 calls instead of 12**. These are Machine-call counts, not measured
latency or physical network-request guarantees.

With permitted nondeterministic faults, a separate proof preserves authorization and
output conformance. Deduplication can share faults between equal keys; identical fault
observations between optimized and reference executions are not claimed.
See [batching proofs](planning/s4b-status.adoc) and
[optimized fault safety](planning/s6b-status.adoc).

## Building a proved application

1. Define the application model and an independent statement of the desired behavior.
1. State resolver preconditions and postconditions, including permitted failures.
1. Prove the resolver implementations or backend producers satisfy those contracts.
1. Connect schema bindings and execution plans to that model; use the certified driver
   and encoding path to compose the result guarantee.

The tenant example supplies this chain for ownership. A separate
[list-bound example](GraphQL/Plan/ItemsExample.lean) proves that successful
`items(first: n)` execution returns no more than its accepted limit, even for arbitrary
backend answers satisfying the contract. It is a core example, not an additional field
on the tenant HTTP endpoint. New application policies still require their own proofs.

## Work in progress

This is a developer-preview framework with a narrow certified query profile.
S0–S6 are complete and independently reviewed; broader language support and generality
remain planned. Follow the [milestones and proof obligations](planning/proof-first-roadmap.adoc), [current completed milestone](planning/s6-status.adoc), and
[intended 1.0 scope and compatibility promise](RELEASE-POLICY.adoc).

The intended stable API is limited to the public declarations defined in
`GraphQL.Schema`, `GraphQL.Response`, and `GraphQL.Machine`; the remaining framework
and reference-application APIs are experimental. The package remains at `0.0.1`
until release preparation is complete. Licensed under [MIT](LICENSE).

| Coverage | Current boundary |
| --- | --- |
| Proved | Application authorization in the tenant model; execution of checked plans agrees with independent semantics; deterministic batching equivalence and Machine-call counts; permitted-fault safety; response encoding. |
| Enforced by types | Typed graph dependencies and field answers; proof-carrying backend results; matching caller and acquisition evidence in the certified handler. |
| Tested, not formally established | Source-text parser/envelope fidelity, HTTP header/body extraction, and native integration behavior. |
| External obligations | Real identity providers, snapshot acquisition, and database/backend producers must justify their declared contracts. |
| Outside the guarantee | Native runtime and network delivery correctness, liveness, cancellation, concurrency, and wall-clock performance. |

The certified profile supports the tenant fields above, one query operation, and
supported variables/defaults. It does not yet support aliases, fragments, directives,
mutations, subscriptions, Federation, or arbitrary application schemas on that path.
See [input limits and profile](planning/s5-status.adoc) and
[HTTP policy and trust boundaries](planning/s6d-status.adoc).

The repository also retains a broader legacy SDL/HTTP prototype (`graphql-demo`).
Its feature coverage does not inherit the tenant path's application proofs. Its usage,
limitations, and benchmark history are in the
[legacy prototype guide](planning/legacy-prototype-guide.txt).

## Check the evidence

The harness, runtime tests, HTTP client, generator checks, and benchmark runners are
written in Lean. Lake builds and runs the harness:

```sh
scripts/lake test                 # Build, generator checks, runtime tests, audits, rejection fixtures
scripts/lake test -- --all        # Also run process/client self-tests and both HTTP suites
```

`scripts/check` is a short shell wrapper around the same Lake test driver. Individual
suites and generator commands are also available:

```sh
scripts/check --http-certified
scripts/check --http-legacy
scripts/check --self-test
scripts/check --generate --check  # Determinism, mutation rejection, positive witness, schema fixture
scripts/check --generate          # Regenerate Example/Tenant/Generated.lean
```

| Layer | What it checks |
| --- | --- |
| Lean kernel | Theorems about application semantics, execution, optimization, and encoding. |
| Lean runtime tests | Concrete query results, coercion, faults, and effectful behavior; see [Tests/Main.lean](Tests/Main.lean) and the [tenant runner](Example/Tenant/Demo.lean). |
| Lean rejection harness | Invalid schemas, contracts, and certificates fail to compile for the expected reason. |
| Lean integration and audit harness | Starts owned servers, checks real HTTP responses, verifies generated code, and checks Lean's reported proof dependencies against the allowed set. |

The [harness guide](Harness/README.md) documents its commands, subprocess deadlines,
HTTP client, benchmark modes, and scope. It targets the project's POSIX development
environment; optional RSS benchmarks use the system `/usr/bin/time`. The TCP client
has its own HTTP framing parser, while JSON assertions use Lean.Json. Moving the
harness to Lean does not turn integration tests into proofs.

The HTTP suites launch and clean up local servers; they require loopback socket access.
At S6 closure, validation passed **696 proof-dependency reports, 48 compile-rejection
fixtures, 30 certified HTTP checks, and 35 legacy HTTP checks**, alongside native
semantic and generated-code checks. See the
[independent closure review](planning/s6cd-claude-closure.txt).
