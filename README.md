# github-forge

A standalone GitHub-compatible git forge in one process, Node 22 standard
library only. Built for the make.fun `github-core-clone-01` competition.

## What it serves

- **Git smart HTTP** at `/{owner}/{repo}.git`: upload-pack protocol v2
  (and v0 fallback) and receive-pack v0, with pkt-line framing, packfile
  read/write (including delta resolution), shallow fetches, fast-forward
  enforcement and per-ref report-status.
- **REST v3** under `/api/v3`: repositories, branches, commits, contents
  (base64 blobs, directory listings, stale-sha 409), labels, issues,
  comments and pull requests with squash merge and conflict detection.
- **GraphQL v4** at `/api/graphql`: viewer, repository, issue and pull
  request reads, `__type` introspection, `node(id:)` Relay ids, and the
  createIssue / closeIssue / createPullRequest / mergePullRequest /
  addComment mutations, including batched operation documents.
- **MCP** at `/mcp`: JSON-RPC 2.0 over Streamable HTTP, revision
  2026-07-28 via `server/discover` (with the legacy `initialize`
  handshake as a fallback), ten tools acting on the same store as REST.

## Run

```
node main.ts
```

The process binds an ephemeral port, registers it with the suite at
`$MAKEFUN_ENV_URL/register`, serves until `$MAKEFUN_ENV_URL/done` answers
`{"done": true}`, then exits 0. It needs `MAKEFUN_SHOP_TOKEN` for the
bearer token the suite presents; without it any bearer token is accepted
(local practice only).

## Design notes

- In-memory store, deterministic: every timestamp the forge stamps comes
  from a fixed epoch plus a sequence counter, so two runs of the same
  operation sequence leave identical state.
- The viewer is the login the trial token names. The suite's scenario is
  built from one fixed seed, so that login is `adaiversen` in every trial;
  any other owner in a repository path answers 404, never 403.
- No dependencies, no install step, no git binary, no outside service.
