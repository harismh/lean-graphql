# lean-graphql — 2.0 direction (historical release draft)

Historical draft: the intended release is now 1.0. See the
[current release scope and compatibility promise](../RELEASE-POLICY.adoc).
The text below preserves the earlier framing; it is not the current release announcement.

**Proof-oriented GraphQL framework in Lean 4**

> [!NOTE]
> **An autonomous AI development experiment.** AI agents carry out implementation,
> proof development, testing, documentation, and cross-agent review under human-defined
> goals and scope. The experiment is whether that workflow can produce useful,
> independently checkable software guarantees. Evidence comes from Lean's kernel,
> explicit specifications, and reproducible tests—not an agent's confidence.

Draft announcement for a developer-preview release. “2.0” is a working name for the
architectural direction, not a published semantic version. Release numbering must be
chosen before publication; this draft does not change the package version, currently
0.0.1, or create a release tag.

## Application proofs carried through to GraphQL responses

lean-graphql compiles checked queries into typed execution graphs and carries
application correctness evidence through execution, optimization, and response encoding.
The focus is on making useful properties of GraphQL programs provable.

The reference application demonstrates tenant isolation: returned project and task
records must belong to the authenticated tenant and the specified snapshot. That
property survives nested relationships, filtered lists, permitted resolver failures,
and the actual batching path. The certified HTTP adapter sends bytes backed by this
proof chain or a closed public failure.

## What this milestone delivers

- Typed execution graphs with separate output plans and checked schema bindings.
- Compositional resolver contracts and an independent tenant-authorization judgment.
- A batching transformation proved to preserve complete responses under deterministic
  backend meanings, with separate safety proofs for permitted faults.
- A proved batch-wave call count; the demonstration reduces whole-program primitive
  calls from 12 to 9. This is not a wall-clock performance claim.
- Certified effectful execution, explicit authentication and snapshot-acquisition
  obligations, and a total ordered JSON encoder connected to the actual LeanIO route.

For example, an authorized response can be encoded without losing its certificate:

```lean
import Example.Tenant.WireResponse
open Example.Tenant

example (response : {r // Spec.AuthorizedResponse snapshot principal selection r}) :
    {bytes // Wire.AuthorizedWireResponse snapshot principal selection bytes} :=
  Wire.encodeAuthorized response
```

A separate core example proves a list-length limit, demonstrating that application
contracts can express properties beyond ownership. Each new application property still
needs its own model, contracts, and proofs.

## Try it and inspect the evidence

Start with the [README](../README.md): it includes a runnable tenant query and
concise examples of authorization, encoding, and optimizer proofs. Its test guide
explains the Lean proof/runtime suites and the Lean integration harness. The build,
validation, HTTP tests, generator checks, and benchmark runners require no Python.

S6 closure passed 696 proof-dependency reports, 48 compile-rejection fixtures,
30 certified-route HTTP checks, and 35 legacy HTTP regression checks, plus native
semantic and generated-code checks. An
[independent review](s6cd-claude-closure.txt) confirmed no remaining blockers for
that milestone.

## Work in progress

This is a developer preview of the proof-oriented architecture, not a claim of broad
GraphQL compatibility or production readiness. The certified path currently covers a
restricted tenant-query profile. The broader legacy prototype is separate.

Source-text parsing and native HTTP integration are tested boundaries. External
identity, snapshot, and backend producers must justify their contracts; native runtime
and network delivery remain trusted. JSON encoding is proved against an independent
grammar; a JSON decoder round-trip and grammar injectivity are not yet proved.
There is no liveness, concurrency, or general
performance guarantee. The demo uses fixed test credentials and an in-memory store.

S0–S6 are complete. S7 plans additional language features with preservation proofs;
S8 plans broader applications, scaling, and further verified optimizations. See the
[milestones and proof obligations](proof-first-roadmap.adoc) for scope and progress.
